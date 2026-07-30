(** Preservation of security signatures along the Stc-to-Obc translation.

    First slice: the pc/clock correspondence.  [Control ck s] compiles
    the STC clock [ck] into nested [Ifte]s; generating constraints for
    the compiled statement under pc is the same as generating
    constraints for [s] under pc joined with the clock variables' types.
    Together with [clock_pc_from_assign] this reduces every per-tc case
    of the bridge to the STC constraint shapes. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import StcToObc.Translation.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecObcTyping.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From compcert Require Import common.Errors.

Module Type SECSTCOBCTRANSLATION
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import SIG   : SIGNATURE Ids SC)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Trans : TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG).
  Import SECMONADNotations.

  Section CONTROLPC.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    (** The pc accumulated by walking a clock: the pc at [Control ck s]
        entry extended with the security types of the clock variables. *)

    Fixpoint clock_pc (pc: ST) (ck: clock) : option ST :=
      match ck with
      | Cbase => Some pc
      | Con ck' x _ =>
          match clock_pc pc ck', Env.find x env with
          | Some pc', Some ty => Some (pc' ⊔ [ty])
          | _, _ => None
          end
      end.

    (** [clock_pc] is [assign_clk_type] with the seed replaced by the
        incoming pc: seeding the clock type at [b] and joining any [pc0]
        is the same as walking the clock from [pc0 ⊔ [b]]. *)

    Lemma clock_pc_from_assign:
      forall b ck ckty pc0,
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        clock_pc (pc0 ⊔ [b]) ck = Some (pc0 ⊔ ckty).
    Proof.
      intros b ck.
      induction ck as [|ck IH x bck]; intros ckty pc0 Hassign; simpl in *.
      - inversion Hassign; subst ckty. reflexivity.
      - destruct (SECCETYPING.assign_clk_type env b ck) as [ckty'|] eqn:Hck;
          simpl in Hassign; try discriminate.
        destruct (Env.find x env) as [ty|] eqn:Hx; simpl in Hassign;
          try discriminate.
        inversion Hassign; subst ckty.
        rewrite (IH ckty' pc0 eq_refl).
        f_equal.
        apply MergeFacts.merge_assoc.
    Qed.

    (** Generating constraints for a [Control]-guarded statement under
        pc is generating them for the bare statement under the
        clock-extended pc.  This is an equality of results: the [Skip]
        branches contribute no constraints and no state changes. *)

    Lemma generate_stmt_constraints_Control:
      forall memset ck s pc pc' st,
        clock_pc pc ck = Some pc' ->
        generate_stmt_constraints G env state_env rst_ty pc (Control memset ck s) st
        = generate_stmt_constraints G env state_env rst_ty pc' s st.
    Proof.
      intros memset ck.
      induction ck as [|ck IH x b]; intros s pc pc' st Hpc; simpl in Hpc.
      - inversion Hpc; subst pc'. reflexivity.
      - destruct (clock_pc pc ck) as [pcck|] eqn:Hck; try discriminate.
        destruct (Env.find x env) as [ty|] eqn:Hx; try discriminate.
        inversion Hpc; subst pc'.
        destruct b; simpl.
        + rewrite (IH (Ifte (bool_var memset x) s Skip) pc pcck st Hck).
          simpl. unfold bool_var, tovar.
          destruct (PS.mem x memset); simpl; rewrite Hx;
            unfold option_to_sec, bind, ret; simpl;
            destruct (generate_stmt_constraints G env state_env rst_ty (pcck ⊔ [ty]) s st)
              as [[c1 st1]|e]; simpl;
            try rewrite app_nil_r; reflexivity.
        + rewrite (IH (Ifte (bool_var memset x) Skip s) pc pcck st Hck).
          simpl. unfold bool_var, tovar.
          destruct (PS.mem x memset); simpl; rewrite Hx;
            unfold option_to_sec, bind, ret; simpl;
            destruct (generate_stmt_constraints G env state_env rst_ty (pcck ⊔ [ty]) s st)
              as [[c1 st1]|e]; simpl; reflexivity.
    Qed.

    (** Composition with the seed form used by the class signature
        generator: a statement guarded by clock [ck] inside a method
        whose entry pc is [pc0 ⊔ [b]] generates the constraints of the
        bare statement under [pc0 ⊔ ckty] where [ckty] is the STC clock
        type of [ck] seeded at [b]. *)

    Corollary generate_stmt_constraints_Control_assign:
      forall memset ck s b ckty pc0 st,
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ [b]) (Control memset ck s) st
        = generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ ckty) s st.
    Proof.
      intros memset ck s b ckty pc0 st Hassign.
      eapply generate_stmt_constraints_Control.
      eapply clock_pc_from_assign; eauto.
    Qed.

  End CONTROLPC.

  (** * Merge ACI helpers *)

  Lemma merge_cong_under:
    forall q c a b, c ⊔ a = c ⊔ b -> (q ⊔ c) ⊔ a = (q ⊔ c) ⊔ b.
  Proof.
    intros q c a b H.
    rewrite MergeFacts.merge_assoc, H, <- MergeFacts.merge_assoc.
    reflexivity.
  Qed.

  Lemma merge_swap:
    forall a b c, a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c).
  Proof.
    intros a b c.
    rewrite <- MergeFacts.merge_assoc.
    rewrite (MergeFacts.merge_comm a b).
    apply MergeFacts.merge_assoc.
  Qed.

  (** * Expression type correspondence

      [translate_exp] drops [Ewhen] guards (the clock is compiled by
      [Control] at the statement level).  For a well-clocked expression
      the dropped guards are exactly clock variables of the expression's
      clock, so joined with the clock type nothing is lost: the CE
      security type and the Obc security type of the translation agree
      modulo the clock type. *)

  Section EXPRCORR.
    Variable env: Env.t ident.

    Lemma translate_exp_type_correspondence:
      forall memset vars e ck b ckty ety,
        CEClo.wc_exp vars e ck ->
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        SECCETYPING.assign_exp_type env e = Some ety ->
        exists oty,
          SECOBCTYPING.assign_exp_type env (translate_exp memset e) = Some oty
          /\ ckty ⊔ ety = ckty ⊔ oty.
    Proof.
      intros memset vars e ck b ckty ety Hwc.
      revert ckty ety.
      induction Hwc as [c|x ck ty Hin|e x b' ck Hwc IH Hin|op e ck ty Hwc IH
                        |op e1 e2 ck ty Hwc1 IH1 Hwc2 IH2];
        intros ckty ety Hck Hety; simpl in Hety.
      - (* Econst *)
        inversion Hety; subst ety.
        exists []. split; [reflexivity|reflexivity].
      - (* Evar *)
        destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        exists [xty]. split; [|reflexivity].
        simpl. unfold tovar.
        destruct (PS.mem x memset); simpl; rewrite Hx; reflexivity.
      - (* Ewhen *)
        destruct (SECCETYPING.assign_exp_type env e) as [Ee|] eqn:He;
          simpl in Hety; try discriminate.
        destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        simpl in Hck.
        destruct (SECCETYPING.assign_clk_type env b ck) as [A|] eqn:HA;
          simpl in Hck; try discriminate.
        rewrite Hx in Hck. simpl in Hck.
        inversion Hck; subst ckty.
        destruct (IH A Ee eq_refl eq_refl) as (oty & Hoty & Heq).
        exists oty. split; [simpl; exact Hoty|].
        rewrite MergeFacts.merge_assoc.
        rewrite (merge_swap [xty] Ee [xty]).
        rewrite MergeFacts.merge_refl.
        rewrite <- MergeFacts.merge_assoc.
        rewrite Heq.
        rewrite MergeFacts.merge_assoc.
        rewrite (MergeFacts.merge_comm oty [xty]).
        rewrite <- MergeFacts.merge_assoc.
        reflexivity.
      - (* Eunop *)
        destruct (IH ckty ety Hck Hety) as (oty & Hoty & Heq).
        exists oty. split; [simpl; exact Hoty|exact Heq].
      - (* Ebinop *)
        destruct (SECCETYPING.assign_exp_type env e1) as [E1|] eqn:He1;
          simpl in Hety; try discriminate.
        destruct (SECCETYPING.assign_exp_type env e2) as [E2|] eqn:He2;
          simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        destruct (IH1 ckty E1 Hck eq_refl) as (O1 & HO1 & Heq1).
        destruct (IH2 ckty E2 Hck eq_refl) as (O2 & HO2 & Heq2).
        exists (O1 ⊔ O2). split.
        + simpl. rewrite HO1, HO2. reflexivity.
        + rewrite <- MergeFacts.merge_assoc.
          rewrite Heq1.
          rewrite MergeFacts.merge_assoc.
          rewrite (MergeFacts.merge_comm O1 E2).
          rewrite <- MergeFacts.merge_assoc.
          rewrite Heq2.
          rewrite MergeFacts.merge_assoc.
          rewrite (MergeFacts.merge_comm O2 O1).
          reflexivity.
    Qed.

  End EXPRCORR.

  Lemma merge_factor:
    forall p a b, (p ⊔ a) ⊔ (p ⊔ b) = p ⊔ (a ⊔ b).
  Proof.
    intros p a b.
    rewrite MergeFacts.merge_assoc.
    rewrite (merge_swap a p b).
    rewrite <- MergeFacts.merge_assoc.
    rewrite MergeFacts.merge_refl.
    reflexivity.
  Qed.

  Lemma merge_rotate:
    forall a b c, (a ⊔ b) ⊔ c = (a ⊔ c) ⊔ b.
  Proof.
    intros a b c.
    rewrite MergeFacts.merge_assoc.
    rewrite (MergeFacts.merge_comm b c).
    rewrite <- MergeFacts.merge_assoc.
    reflexivity.
  Qed.

  (** * Compiled control expressions

      [translate_cexp x ce] compiles a control expression into nested
      [Ifte]s with [Assign x] leaves.  Under the clock-extended pc every
      generated constraint targets [τ x], the state is untouched, and
      the join of all leaf sources is exactly the STC constraint source
      [(pc0 ⊔ ckty) ⊔ cety]: merge/ite conditions re-appear as pc
      extensions, and dropped [Ewhen] guards are absorbed by the clock
      type ([translate_exp_type_correspondence]). *)
  Section TCDEFCORR.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    (** [translate_cexp x ce] compiles a control expression into nested
        [Ifte]s with [Assign x] leaves.  Under the clock-extended pc every
        generated constraint targets the assigned variable, the state is
        untouched, and the join of all leaf sources is exactly the STC
        constraint source: merge/ite conditions re-appear as pc
        extensions, and dropped [Ewhen] guards are absorbed by the clock
        type ([translate_exp_type_correspondence]). *)

    Lemma translate_cexp_constraints:
      forall memset vars x ce ck b pc0 ckty cety xty cns st st',
        CEClo.wc_cexp vars ce ck ->
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        SECCETYPING.assign_cexp_type env ce = Some cety ->
        Env.find x env = Some xty ->
        generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ ckty)
          (translate_cexp memset x ce) st = OK (cns, st') ->
        st' = st
        /\ cns <> []
        /\ Forall (fun c => snd c = [xty]) cns
        /\ lhs_join cns = ([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ cety.
    Proof.
      intros memset vars x ce.
      induction ce as [y cet IHt cef IHf|e cet IHt cef IHf|le];
        intros ck b pc0 ckty cety xty cns st st' Hwc Hck Hcety Hx Hgen;
        inversion Hwc as [y' t' f' ck' Hiny Hwct Hwcf
                         |e' t' f' ck' Hwce Hwct Hwcf
                         |le' ck' Hwce]; subst.
      - (* Emerge *)
        simpl in Hcety.
        destruct (Env.find y env) as [yty|] eqn:Hy; simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cet) as [tty|] eqn:Htty;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cef) as [fty|] eqn:Hfty;
          simpl in Hcety; try discriminate.
        inversion Hcety; subst cety.
        simpl in Hgen.
        unfold bool_var, tovar in Hgen.
        assert (Hcond :
                  SECOBCTYPING.assign_exp_type env
                    (if PS.mem y memset then State y bool_type else Var y bool_type)
                  = Some [yty]).
        { destruct (PS.mem y memset); simpl; rewrite Hy; reflexivity. }
        rewrite Hcond in Hgen.
        unfold option_to_sec in Hgen.
        eapply sec_bind_inv in Hgen as (ety0 & st0 & Hety0 & Hgen).
        unfold ret in Hety0. inversion Hety0; subst ety0 st0.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        assert (Hckt : SECCETYPING.assign_clk_type env b (Con ck y true)
                       = Some (ckty ⊔ [yty])).
        { simpl. rewrite Hck. simpl. rewrite Hy. reflexivity. }
        assert (Hckf : SECCETYPING.assign_clk_type env b (Con ck y false)
                       = Some (ckty ⊔ [yty])).
        { simpl. rewrite Hck. simpl. rewrite Hy. reflexivity. }
        rewrite MergeFacts.merge_assoc in Hgen1.
        rewrite MergeFacts.merge_assoc in Hgen2.
        destruct (IHt _ b pc0 (ckty ⊔ [yty]) tty xty c1 st st1
                    Hwct Hckt eq_refl Hx Hgen1) as (Hst1 & Hne1 & Hall1 & Hjoin1).
        subst st1.
        destruct (IHf _ b pc0 (ckty ⊔ [yty]) fty xty c2 st st2
                    Hwcf Hckf eq_refl Hx Hgen2) as (Hst2 & Hne2 & Hall2 & Hjoin2).
        subst st2.
        split; [reflexivity|].
        split; [destruct c1; [congruence|discriminate]|].
        split; [apply Forall_app; split; assumption|].
        rewrite (lhs_join_app c1 c2 Hne1 Hne2).
        rewrite Hjoin1, Hjoin2.
        rewrite merge_factor.
        change (([rst_ty] ⊔ (pc0 ⊔ (ckty ⊔ [yty]))) ⊔ (tty ⊔ fty)
                = ([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ (([yty] ⊔ tty) ⊔ fty)).
        rewrite <- (MergeFacts.merge_assoc pc0 ckty [yty]).
        rewrite <- (MergeFacts.merge_assoc [rst_ty] (pc0 ⊔ ckty) [yty]).
        rewrite (MergeFacts.merge_assoc [yty] tty fty).
        rewrite <- (MergeFacts.merge_assoc ([rst_ty] ⊔ (pc0 ⊔ ckty)) [yty] (tty ⊔ fty)).
        reflexivity.
      - (* Eite *)
        simpl in Hcety.
        destruct (SECCETYPING.assign_exp_type env e) as [ety|] eqn:Hety;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cet) as [tty|] eqn:Htty;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cef) as [fty|] eqn:Hfty;
          simpl in Hcety; try discriminate.
        inversion Hcety; subst cety.
        destruct (translate_exp_type_correspondence env memset vars e ck b ckty ety
                    Hwce Hck Hety) as (oty & Hoty & Hoeq).
        simpl in Hgen.
        rewrite Hoty in Hgen.
        unfold option_to_sec in Hgen.
        eapply sec_bind_inv in Hgen as (ety0 & st0 & Hety0 & Hgen).
        unfold ret in Hety0. inversion Hety0; subst ety0 st0.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        rewrite merge_rotate in Hgen1.
        rewrite merge_rotate in Hgen2.
        destruct (IHt _ b (pc0 ⊔ oty) ckty tty xty c1 st st1
                    Hwct Hck eq_refl Hx Hgen1) as (Hst1 & Hne1 & Hall1 & Hjoin1).
        subst st1.
        destruct (IHf _ b (pc0 ⊔ oty) ckty fty xty c2 st st2
                    Hwcf Hck eq_refl Hx Hgen2) as (Hst2 & Hne2 & Hall2 & Hjoin2).
        subst st2.
        split; [reflexivity|].
        split; [destruct c1; [congruence|discriminate]|].
        split; [apply Forall_app; split; assumption|].
        rewrite (lhs_join_app c1 c2 Hne1 Hne2).
        rewrite Hjoin1, Hjoin2.
        rewrite merge_factor.
        change (([rst_ty] ⊔ ((pc0 ⊔ oty) ⊔ ckty)) ⊔ (tty ⊔ fty)
                = ([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ ((ety ⊔ tty) ⊔ fty)).
        rewrite (merge_rotate pc0 oty ckty).
        rewrite <- (MergeFacts.merge_assoc [rst_ty] (pc0 ⊔ ckty) oty).
        rewrite (MergeFacts.merge_assoc ety tty fty).
        rewrite <- (MergeFacts.merge_assoc ([rst_ty] ⊔ (pc0 ⊔ ckty)) ety (tty ⊔ fty)).
        f_equal.
        rewrite <- (MergeFacts.merge_assoc [rst_ty] pc0 ckty).
        apply merge_cong_under.
        exact (eq_sym Hoeq).
      - (* Eexp *)
        simpl in Hcety.
        destruct (translate_exp_type_correspondence env memset vars le ck b ckty cety
                    Hwce Hck Hcety) as (oty & Hoty & Hoeq).
        simpl in Hgen.
        rewrite Hoty in Hgen.
        unfold option_to_sec in Hgen.
        eapply sec_bind_inv in Hgen as (ety0 & st0 & Hety0 & Hgen).
        unfold ret in Hety0. inversion Hety0; subst ety0 st0.
        eapply sec_bind_inv in Hgen as (xty0 & st1 & Hfind & Hret).
        unfold find_env in Hfind.
        rewrite Hx in Hfind.
        unfold ret in Hfind. inversion Hfind; subst xty0 st1.
        unfold ret in Hret. inversion Hret; subst cns st'.
        split; [reflexivity|].
        split; [discriminate|].
        split; [constructor; [reflexivity|constructor]|].
        change (lhs_join [((([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ oty), [xty])]
                = ([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ cety).
        cbn [lhs_join].
        rewrite <- (MergeFacts.merge_assoc [rst_ty] pc0 ckty).
        apply merge_cong_under.
        exact (eq_sym Hoeq).
    Qed.

  End TCDEFCORR.

  (** * Per-trconstr correspondence

      For the three local trconstrs the collapsed Obc constraints are
      exactly the STC ones: [TcDef] via [translate_cexp_constraints],
      [TcNext] directly, [TcReset] as the reset dependence joined with
      the pc at the compiled call site (which, for the translated
      [Con ckr r true] clocks, is the STC reset source up to merge ACI).
      [TcCall] is semantic (preserves_on) and handled at the assembly
      level. *)

  Section TCCORR.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    Lemma translate_tcdef_constraints:
      forall memset clkvars vars x ce ck pc0 b ckty cety xty cns st st',
        CEClo.wc_cexp vars ce ck ->
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        SECCETYPING.assign_cexp_type env ce = Some cety ->
        Env.find x env = Some xty ->
        generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ [b])
          (translate_tc memset clkvars (SynStc.TcDef x ck ce)) st = OK (cns, st') ->
        st' = st
        /\ collapse cns = [((([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ cety), [xty])].
    Proof.
      intros memset clkvars vars x ce ck pc0 b ckty cety xty cns st st'
             Hwc Hck Hcety Hx Hgen.
      unfold translate_tc in Hgen.
      rewrite (generate_stmt_constraints_Control_assign
                 G env state_env rst_ty memset ck (translate_cexp memset x ce)
                 b ckty pc0 st Hck) in Hgen.
      destruct (translate_cexp_constraints G env state_env rst_ty memset vars x ce ck b
                  pc0 ckty cety xty cns st st' Hwc Hck Hcety Hx Hgen)
        as (Hst & Hne & Hall & Hjoin).
      split; [exact Hst|].
      rewrite (collapse_same_target cns [xty] Hne Hall).
      rewrite Hjoin. reflexivity.
    Qed.

    Lemma translate_tcnext_constraints:
      forall memset clkvars vars x e ck pc0 b ckty ety xty cns st st',
        CEClo.wc_exp vars e ck ->
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        SECCETYPING.assign_exp_type env e = Some ety ->
        Env.find x env = Some xty ->
        generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ [b])
          (translate_tc memset clkvars (SynStc.TcNext x ck e)) st = OK (cns, st') ->
        st' = st
        /\ cns = [((([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ ety), [xty])].
    Proof.
      intros memset clkvars vars x e ck pc0 b ckty ety xty cns st st'
             Hwc Hck Hety Hx Hgen.
      unfold translate_tc in Hgen.
      rewrite (generate_stmt_constraints_Control_assign
                 G env state_env rst_ty memset ck (AssignSt x (translate_exp memset e))
                 b ckty pc0 st Hck) in Hgen.
      destruct (translate_exp_type_correspondence env memset vars e ck b ckty ety
                  Hwc Hck Hety) as (oty & Hoty & Hoeq).
      cbn [generate_stmt_constraints] in Hgen.
      rewrite Hoty in Hgen.
      unfold option_to_sec in Hgen.
      eapply sec_bind_inv in Hgen as (ety0 & st0 & Hety0 & Hgen).
      unfold ret in Hety0. inversion Hety0; subst ety0 st0.
      eapply sec_bind_inv in Hgen as (xty0 & st1 & Hfind & Hret).
      unfold find_env in Hfind.
      rewrite Hx in Hfind.
      unfold ret in Hfind. inversion Hfind; subst xty0 st1.
      unfold ret in Hret. inversion Hret; subst cns st'.
      split; [reflexivity|].
      change ([((([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ oty), [xty])]
              = [((([rst_ty] ⊔ (pc0 ⊔ ckty)) ⊔ ety), [xty])]).
      do 2 f_equal.
      rewrite <- (MergeFacts.merge_assoc [rst_ty] pc0 ckty).
      apply merge_cong_under.
      exact (eq_sym Hoeq).
    Qed.

    Lemma translate_tcreset_constraints:
      forall memset clkvars s ck f pc0 b ckty sty cns st st',
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        Env.find s state_env = Some sty ->
        generate_stmt_constraints G env state_env rst_ty (pc0 ⊔ [b])
          (translate_tc memset clkvars (SynStc.TcReset s ck f)) st = OK (cns, st') ->
        st' = st
        /\ cns = [(([rst_ty] ⊔ (pc0 ⊔ ckty)), [sty])].
    Proof.
      intros memset clkvars s ck f pc0 b ckty sty cns st st'
             Hck Hsty Hgen.
      unfold translate_tc in Hgen.
      rewrite (generate_stmt_constraints_Control_assign
                 G env state_env rst_ty memset ck (Call [] f s reset [])
                 b ckty pc0 st Hck) in Hgen.
      cbn [generate_stmt_constraints] in Hgen.
      rewrite ident_eqb_refl in Hgen.
      eapply sec_bind_inv in Hgen as (sty0 & st1 & Hfind & Hret).
      unfold find_env in Hfind.
      rewrite Hsty in Hfind.
      unfold ret in Hfind. inversion Hfind; subst sty0 st1.
      unfold ret in Hret. inversion Hret; subst cns st'.
      split; reflexivity.
    Qed.

  End TCCORR.

End SECSTCOBCTRANSLATION.

Module SecStcObcTranslation
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import SIG   : SIGNATURE Ids SC)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Trans : TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG)
  <: SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc SemObc TypObc SIG CEIsF CEClo SECCETYPING Trans SECOBCTYPING.

Include SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc SemObc TypObc SIG CEIsF CEClo SECCETYPING Trans SECOBCTYPING.

End SecStcObcTranslation.
