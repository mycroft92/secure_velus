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
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import StcToObc.Translation.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecObcTyping.
From Velus Require Import SIF.SecObcTypingCorrectness.

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
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import LastStc  : STCISLAST Ids Op CESyn SynStc)
  (Import VarStc   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import DefStc   : STCISDEFINED Ids Op CESyn SynStc VarStc LastStc)
  (Import SystStc  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc   : STCORDERED Ids Op CESyn SynStc SystStc)
  (Import IsFStc   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc   : STCCLOCKING Ids Op CESyn SynStc LastStc VarStc DefStc SystStc OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo
                           SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc)
  (Import Trans : TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS SECOBCTYPING).
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
        rewrite (IH ckty' pc0 Logic.eq_refl).
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
        destruct (IH A Ee Logic.eq_refl Logic.eq_refl) as (oty & Hoty & Heq).
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
        destruct (IH1 ckty E1 Hck Logic.eq_refl) as (O1 & HO1 & Heq1).
        destruct (IH2 ckty E2 Hck Logic.eq_refl) as (O2 & HO2 & Heq2).
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

    (** * Argument monotonicity (TcCall obligation B)

        [translate_arg] emits either [Valid x ty] (same security type as
        the variable) or [translate_exp e], which drops [Ewhen] guards.
        The Obc argument type is therefore always a *subset* of the CE
        one: call constraints on the Obc side are weaker, which is the
        direction signature preservation needs. *)

    Lemma translate_exp_type_incl:
      forall memset e ety,
        SECCETYPING.assign_exp_type env e = Some ety ->
        exists oty,
          SECOBCTYPING.assign_exp_type env (translate_exp memset e) = Some oty
          /\ (forall z, In z oty -> In z ety).
    Proof.
      intros memset e.
      induction e as [c|x ty|e IH x b|op e IH ty|op e1 IH1 e2 IH2 ty];
        intros ety Hety; simpl in Hety.
      - (* Econst *)
        inversion Hety; subst ety.
        exists []. split; [reflexivity|intros z Hz; inversion Hz].
      - (* Evar *)
        destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        exists [xty]. split; [|auto].
        simpl. unfold tovar.
        destruct (PS.mem x memset); simpl; rewrite Hx; reflexivity.
      - (* Ewhen: the guard is dropped *)
        destruct (SECCETYPING.assign_exp_type env e) as [ee|] eqn:He;
          simpl in Hety; try discriminate.
        destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        destruct (IH ee Logic.eq_refl) as (oty & Hoty & Hincl).
        exists oty. split; [exact Hoty|].
        intros z Hz. apply in_merge_left. exact (Hincl _ Hz).
      - (* Eunop *)
        destruct (IH ety Hety) as (oty & Hoty & Hincl).
        exists oty. split; [exact Hoty|exact Hincl].
      - (* Ebinop *)
        destruct (SECCETYPING.assign_exp_type env e1) as [e1t|] eqn:H1;
          simpl in Hety; try discriminate.
        destruct (SECCETYPING.assign_exp_type env e2) as [e2t|] eqn:H2;
          simpl in Hety; try discriminate.
        inversion Hety; subst ety.
        destruct (IH1 e1t Logic.eq_refl) as (o1 & Ho1 & Hi1).
        destruct (IH2 e2t Logic.eq_refl) as (o2 & Ho2 & Hi2).
        exists (o1 ⊔ o2). split.
        + simpl. rewrite Ho1, Ho2. reflexivity.
        + intros z Hz.
          apply in_merge_inv in Hz.
          destruct Hz as [Hz|Hz].
          * apply in_merge_left. exact (Hi1 _ Hz).
          * apply in_merge_right. exact (Hi2 _ Hz).
    Qed.

    Lemma translate_arg_type_incl:
      forall memset clkvars ck e ety,
        SECCETYPING.assign_exp_type env e = Some ety ->
        exists oty,
          SECOBCTYPING.assign_exp_type env (translate_arg memset clkvars ck e) = Some oty
          /\ (forall z, In z oty -> In z ety).
    Proof.
      intros memset clkvars ck e ety Hety.
      destruct e as [c|x ty|e x b|op e ty|op e1 e2 ty];
        try (eapply translate_exp_type_incl; eauto).
      (* Evar: either Valid x ty or the compiled variable; same type *)
      simpl in Hety.
      destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hety; try discriminate.
      inversion Hety; subst ety.
      exists [xty]. split; [|auto].
      simpl.
      destruct (var_on_base_clock memset clkvars ck x); simpl.
      - rewrite Hx. reflexivity.
      - unfold tovar. destruct (PS.mem x memset); simpl; rewrite Hx; reflexivity.
    Qed.

    Lemma translate_args_type_incl:
      forall memset clkvars ck es tys otys st1 st1' st2 st2',
        SC.mmap (fun e => option_to_sec (SECCETYPING.assign_exp_type env e))
          es st1 = OK (tys, st1') ->
        SC.mmap (fun e => option_to_sec (SECOBCTYPING.assign_exp_type env e))
          (map (translate_arg memset clkvars ck) es) st2 = OK (otys, st2') ->
        Forall2 (fun ety oty => forall z, In z oty -> In z ety) tys otys.
    Proof.
      intros memset clkvars ck es.
      induction es as [|e es IH]; intros tys otys st1 st1' st2 st2' Hce Hobc.
      - simpl in Hce, Hobc.
        unfold ret in Hce, Hobc.
        inversion Hce; inversion Hobc; subst. constructor.
      - simpl in Hce, Hobc.
        eapply sec_bind_inv in Hce as (ety & sta & Hhd & Hce).
        eapply sec_bind_inv in Hce as (tys' & stb & Htl & Hret).
        unfold ret in Hret. inversion Hret; subst tys st1'.
        eapply sec_bind_inv in Hobc as (oty & stc & Hohd & Hobc).
        eapply sec_bind_inv in Hobc as (otys' & std & Hotl & Horet).
        unfold ret in Horet. inversion Horet; subst otys st2'.
        unfold option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type env e) as [ety'|] eqn:He;
          try discriminate.
        inversion Hhd; subst ety sta.
        unfold option_to_sec in Hohd.
        destruct (SECOBCTYPING.assign_exp_type env
                    (translate_arg memset clkvars ck e)) as [oty'|] eqn:Ho;
          try discriminate.
        inversion Hohd; subst oty stc.
        constructor.
        + destruct (translate_arg_type_incl memset clkvars ck e ety' He)
            as (oty'' & Ho'' & Hincl).
          rewrite Ho in Ho''. inversion Ho''; subst oty''.
          exact Hincl.
        + eapply IH; eauto.
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
                    (if PS.mem y memset then SynObc.State y bool_type else SynObc.Var y bool_type)
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
                    Hwct Hckt Logic.eq_refl Hx Hgen1) as (Hst1 & Hne1 & Hall1 & Hjoin1).
        subst st1.
        destruct (IHf _ b pc0 (ckty ⊔ [yty]) fty xty c2 st st2
                    Hwcf Hckf Logic.eq_refl Hx Hgen2) as (Hst2 & Hne2 & Hall2 & Hjoin2).
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
                    Hwct Hck Logic.eq_refl Hx Hgen1) as (Hst1 & Hne1 & Hall1 & Hjoin1).
        subst st1.
        destruct (IHf _ b (pc0 ⊔ oty) ckty fty xty c2 st st2
                    Hwcf Hck Logic.eq_refl Hx Hgen2) as (Hst2 & Hne2 & Hall2 & Hjoin2).
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
        exact (Logic.eq_sym Hoeq).
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
        exact (Logic.eq_sym Hoeq).
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
                 G env state_env rst_ty memset ck (SynObc.AssignSt x (translate_exp memset e))
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
      exact (Logic.eq_sym Hoeq).
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
                 G env state_env rst_ty memset ck (SynObc.Call [] f s reset [])
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

  (** * Per-trconstr security preservation

      With the entry pc of the step method seeded at [[clk_ty]], the pc at
      a site guarded by clock [ck] is exactly the STC clock type, so for
      the three local trconstrs the Obc constraints are (after [collapse],
      which is satisfaction-neutral) *the same constraints* the STC
      generator produces.  [preserves_on] then holds with [dlt' = dlt].

      [TcCall] is the remaining case; it is genuinely semantic (the two
      sides instantiate different callee signatures) and is treated in
      `Stc2ObcSIF_tccall.md`. *)

  Section TCPRESERV.
    Variable G1: SIG.secglobal.        (* STC signatures *)
    Variable G2: SIG.secglobal.        (* Obc signatures *)
    Variable env: Env.t ident.
    Variable reset_env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable clk_ty rst_ty: ident.

    Lemma tcdef_preserv:
      forall scope memset clkvars vars x ck ce nconst sconst st1 st1' st2 st2',
        CEClo.wc_cexp vars ce ck ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcDef x ck ce) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env state_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcDef x ck ce)) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars vars x ck ce nconst sconst st1 st1' st2 st2'
             Hwc Hstc Hobc.
      (* invert the STC generator *)
      simpl in Hstc.
      eapply sec_bind_inv in Hstc as (ckty & sta & Hck & Hstc).
      eapply sec_bind_inv in Hstc as (cety & stb & Hce & Hstc).
      eapply sec_bind_inv in Hstc as (xty & stc & Hx & Hret).
      unfold ret in Hret. inversion Hret; subst nconst st1'.
      unfold option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type env clk_ty ck) as [ckty'|] eqn:Hckopt;
        try discriminate.
      inversion Hck; subst ckty sta.
      unfold option_to_sec in Hce.
      destruct (SECCETYPING.assign_cexp_type env ce) as [cety'|] eqn:Hceopt;
        try discriminate.
      inversion Hce; subst cety stb.
      unfold SC.find_env in Hx.
      destruct (Env.find x env) as [xty'|] eqn:Hxopt; try discriminate.
      unfold ret in Hx. inversion Hx; subst xty stc.
      (* the Obc side, at entry pc [clk_ty] = [] ⊔ [clk_ty] *)
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      destruct (translate_tcdef_constraints G2 env state_env rst_ty
                  memset clkvars vars x ce ck [] clk_ty ckty' cety' xty'
                  sconst st2 st2' Hwc Hckopt Hceopt Hxopt Hobc)
        as (Hst & Hcoll).
      rewrite (MergeFacts.merge_nil2 ckty') in Hcoll.
      (* satisfaction transfers: collapse is neutral *)
      apply preserves_on_from_entailment.
      intros dlt Hsat.
      apply collapse_satisfaction.
      rewrite Hcoll. exact Hsat.
    Qed.

    Lemma tcnext_preserv:
      forall scope memset clkvars vars x ck e nconst sconst st1 st1' st2 st2',
        CEClo.wc_exp vars e ck ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcNext x ck e) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env state_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcNext x ck e)) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars vars x ck e nconst sconst st1 st1' st2 st2'
             Hwc Hstc Hobc.
      simpl in Hstc.
      eapply sec_bind_inv in Hstc as (ckty & sta & Hck & Hstc).
      eapply sec_bind_inv in Hstc as (ety & stb & He & Hstc).
      eapply sec_bind_inv in Hstc as (xty & stc & Hx & Hret).
      unfold ret in Hret. inversion Hret; subst nconst st1'.
      unfold option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type env clk_ty ck) as [ckty'|] eqn:Hckopt;
        try discriminate.
      inversion Hck; subst ckty sta.
      unfold option_to_sec in He.
      destruct (SECCETYPING.assign_exp_type env e) as [ety'|] eqn:Heopt;
        try discriminate.
      inversion He; subst ety stb.
      unfold SC.find_env in Hx.
      destruct (Env.find x env) as [xty'|] eqn:Hxopt; try discriminate.
      unfold ret in Hx. inversion Hx; subst xty stc.
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      destruct (translate_tcnext_constraints G2 env state_env rst_ty
                  memset clkvars vars x e ck [] clk_ty ckty' ety' xty'
                  sconst st2 st2' Hwc Hckopt Heopt Hxopt Hobc)
        as (Hst & Hcns).
      rewrite (MergeFacts.merge_nil2 ckty') in Hcns.
      subst sconst.
      apply preserves_on_refl.
    Qed.

    Lemma tcreset_preserv:
      forall scope memset clkvars s ck f nconst sconst st1 st1' st2 st2',
        (* the reset instance and the state instance carry the same value *)
        Env.find s reset_env = Env.find s state_env ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcReset s ck f) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env state_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcReset s ck f)) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars s ck f nconst sconst st1 st1' st2 st2'
             Heq Hstc Hobc.
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      destruct ck as [|ck0 r0 b0].
      - (* Cbase *)
        simpl in Hstc.
        eapply sec_bind_inv in Hstc as (rckty & sta & Hck & Hstc).
        eapply sec_bind_inv in Hstc as (rinst & stb & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst nconst st1'.
        unfold option_to_sec in Hck. simpl in Hck.
        inversion Hck; subst rckty sta.
        unfold SC.find_env in Hr.
        destruct (Env.find s reset_env) as [rinst'|] eqn:Hrfind; try discriminate.
        unfold ret in Hr. inversion Hr; subst rinst stb.
        destruct (translate_tcreset_constraints G2 env state_env rst_ty
                    memset clkvars s Cbase f [] clk_ty [clk_ty] rinst'
                    sconst st2 st2' Logic.eq_refl ltac:(congruence) Hobc)
          as (Hst & Hcns).
        rewrite (MergeFacts.merge_nil2 [clk_ty]) in Hcns.
        subst sconst.
        apply preserves_on_refl.
      - (* Con: both branches of the boolean *)
        destruct b0.
        + simpl in Hstc.
          eapply sec_bind_inv in Hstc as (rty & sta & Hrty & Hstc).
          eapply sec_bind_inv in Hstc as (rstckty & stb & Hck & Hstc).
          eapply sec_bind_inv in Hstc as (rinst & stc & Hr & Hret).
          unfold ret in Hret. inversion Hret; subst nconst st1'.
          unfold SC.find_env in Hrty.
          destruct (Env.find r0 env) as [rty'|] eqn:Hr0; try discriminate.
          unfold ret in Hrty. inversion Hrty; subst rty sta.
          unfold option_to_sec in Hck.
          destruct (SECCETYPING.assign_clk_type env clk_ty ck0) as [rstckty'|] eqn:Hckopt;
            try discriminate.
          inversion Hck; subst rstckty stb.
          unfold SC.find_env in Hr.
          destruct (Env.find s reset_env) as [rinst'|] eqn:Hrfind; try discriminate.
          unfold ret in Hr. inversion Hr; subst rinst stc.
          assert (Hckcon : SECCETYPING.assign_clk_type env clk_ty (Con ck0 r0 true)
                           = Some (rstckty' ⊔ [rty'])).
          { simpl. rewrite Hckopt. simpl. rewrite Hr0. reflexivity. }
          destruct (translate_tcreset_constraints G2 env state_env rst_ty
                      memset clkvars s (Con ck0 r0 true) f [] clk_ty
                      (rstckty' ⊔ [rty']) rinst'
                      sconst st2 st2' Hckcon ltac:(congruence) Hobc)
            as (Hst & Hcns).
          rewrite (MergeFacts.merge_nil2 (rstckty' ⊔ [rty'])) in Hcns.
          subst sconst.
          apply preserves_on_from_entailment.
          intros dlt Hsat.
          rewrite (MergeFacts.merge_comm rstckty' [rty']).
          exact Hsat.
        + simpl in Hstc.
          eapply sec_bind_inv in Hstc as (rckty & sta & Hck & Hstc).
          eapply sec_bind_inv in Hstc as (rinst & stb & Hr & Hret).
          unfold ret in Hret. inversion Hret; subst nconst st1'.
          unfold option_to_sec in Hck.
          destruct (SECCETYPING.assign_clk_type env clk_ty ck0) as [ckty0|] eqn:Eck;
            cbv beta in Hck; simpl in Hck; try discriminate.
          destruct (Env.find r0 env) as [rty0|] eqn:Er0;
            cbv beta in Hck; simpl in Hck; try discriminate.
          unfold ret in Hck. inversion Hck; subst rckty sta.
          assert (Hckopt : SECCETYPING.assign_clk_type env clk_ty (Con ck0 r0 false)
                           = Some (ckty0 ⊔ [rty0])).
          { simpl. rewrite Eck. simpl. rewrite Er0. reflexivity. }
          unfold SC.find_env in Hr.
          destruct (Env.find s reset_env) as [rinst'|] eqn:Hrfind; try discriminate.
          unfold ret in Hr. inversion Hr; subst rinst stb.
          destruct (translate_tcreset_constraints G2 env state_env rst_ty
                      memset clkvars s (Con ck0 r0 false) f [] clk_ty
                      (ckty0 ⊔ [rty0]) rinst'
                      sconst st2 st2' Hckopt ltac:(congruence) Hobc)
            as (Hst & Hcns).
          rewrite (MergeFacts.merge_nil2 (ckty0 ⊔ [rty0])) in Hcns.
          subst sconst.
          apply preserves_on_refl.
    Qed.


    (** ** The call case

        Both sides instantiate a callee signature at the *same* clock
        actual (the pc at the call site, which the [Control] lemma
        identifies with the STC clock type) and the *same* outputs; the
        Obc input types are included in the STC ones
        ([translate_args_type_incl]), and the reset actual is the
        instance's state type instead of the STC reset source.

        Following the NL→STC decomposition ([eqn_preserv] assumes
        [Signature_consistent] for the callee pair), the call case is
        proved from an assumed call-preservation property; establishing
        that property for *generated* signatures is the remaining
        obligation (`Stc2ObcSIF_tccall.md` §4/§5). *)

    Definition call_side_conditions
      (scope: list ident) (n1 n2: SIG.signature)
      (inptyp1 inptyp2: list SymTypes.ST) (ckty srcrst: SymTypes.ST)
      (sty: ident) (outtyp: list ident) : Prop :=
      SIG.scope_fresh scope n1
      /\ SIG.call_subst_scoped scope inptyp1 ckty srcrst outtyp
      /\ ~ In sty scope
      /\ SIG.call_subst_fresh n1 inptyp1 ckty srcrst outtyp
      /\ SIG.call_subst_fresh n2 inptyp2 ckty [sty] outtyp.

    Definition Signature_call_preserves_obc (n1 n2: SIG.signature) : Prop :=
      forall scope inptyp1 inptyp2 ckty srcrst sty outtyp
             nconst sconst st_init1 st_init2 stA stB,
        call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty srcrst sty outtyp ->
        Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) inptyp1 inptyp2 ->
        SIG.generate_constraints n1 inptyp1 ckty srcrst outtyp st_init1 = OK (nconst, stA) ->
        SIG.generate_constraints n2 inptyp2 ckty [sty] outtyp st_init2 = OK (sconst, stB) ->
        preserves_on scope nconst sconst.

    Definition Signature_consistent_obc (H1 H2: SIG.secglobal) : Prop :=
      forall f n1,
        SIG.find_signature f H1 = Some n1 ->
        exists n2,
          SIG.find_signature f H2 = Some n2
          /\ Signature_call_preserves_obc n1 n2.

    Lemma tccall_preserv:
      forall scope memset clkvars i xs ck rst f es ckty
             nconst sconst st1 st1' st2 st2',
        SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
        Signature_consistent_obc G1 G2 ->
        (forall n1 n2 inptyp1 inptyp2 outtyp srcrst sty,
            SIG.find_signature f G1 = Some n1 ->
            SIG.find_signature f G2 = Some n2 ->
            call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty srcrst sty outtyp) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcCall i xs ck rst f es) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env state_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcCall i xs ck rst f es)) st2
          = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars i xs ck rst f es ckty
             nconst sconst st1 st1' st2 st2' Hckopt Hcons Hside Hstc Hobc.
      (* compile the Control wrapper away: the Obc pc is the STC clock type *)
      unfold translate_tc in Hobc.
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      rewrite (generate_stmt_constraints_Control_assign
                 G2 env state_env rst_ty memset ck
                 (SynObc.Call xs f i step (map (translate_arg memset clkvars ck) es))
                 clk_ty ckty [] st2 Hckopt) in Hobc.
      rewrite (MergeFacts.merge_nil2 ckty) in Hobc.
      destruct xs as [|x xs'].
      - (* no outputs: both sides emit nothing *)
        simpl in Hstc. unfold ret in Hstc. inversion Hstc; subst nconst st1'.
        simpl in Hobc.
        assert (Hne : ident_eqb step reset = false).
        { apply ident_eqb_neq. intro Heq. symmetry in Heq.
          revert Heq. apply reset_not_step. }
        rewrite Hne in Hobc.
        unfold ret in Hobc. inversion Hobc; subst sconst st2'.
        apply preserves_on_nil.
      - (* a real call *)
        simpl in Hobc.
        assert (Hstep : ident_eqb step step = true) by apply ident_eqb_refl.
        rewrite Hstep in Hobc.
        destruct (SIG.find_signature f G2) as [n2|] eqn:Hf2; try discriminate.
        eapply sec_bind_inv in Hobc as (inptyp2 & stb1 & Hinp2 & Hobc).
        eapply sec_bind_inv in Hobc as (outtyp2 & stb2 & Hout2 & Hobc).
        eapply sec_bind_inv in Hobc as (sty & stb3 & Hsty & Hgen2).
        destruct rst.
        + (* reset'd call: STC uses the reset instance *)
          simpl in Hstc.
          destruct (SIG.find_signature f G1) as [n1|] eqn:Hf1; try discriminate.
          eapply sec_bind_inv in Hstc as (ckty1 & sta1 & Hck1 & Hstc).
          eapply sec_bind_inv in Hstc as (inptyp1 & sta2 & Hinp1 & Hstc).
          eapply sec_bind_inv in Hstc as (outtyp1 & sta3 & Hout1 & Hstc).
          eapply sec_bind_inv in Hstc as (rinst & sta4 & Hrinst & Hgen1).
          unfold option_to_sec in Hck1.
          rewrite Hckopt in Hck1. unfold ret in Hck1.
          inversion Hck1; subst ckty1 sta1.
          assert (Houteq : outtyp1 = outtyp2).
          { eapply (@mmap_consistent ident ident
                      (fun z => SC.find_env z env) (fun z => SC.find_env z env)
                      (x :: xs')); eauto.
            intros. eapply SC.find_env_consistent; eauto. }
          subst outtyp2.
          destruct (Hcons f n1 Hf1) as (n2' & Hf2' & Hpres).
          rewrite Hf2 in Hf2'. inversion Hf2'; subst n2'.
          eapply (Hpres scope inptyp1 inptyp2 ckty [rinst] sty outtyp1
                    nconst sconst sta4 stb3 st1' st2').
          * eapply Hside; eauto.
          * eapply translate_args_type_incl; eauto.
          * exact Hgen1.
          * exact Hgen2.
        + (* unreset call: STC uses the ambient reset type *)
          simpl in Hstc.
          destruct (SIG.find_signature f G1) as [n1|] eqn:Hf1; try discriminate.
          eapply sec_bind_inv in Hstc as (ckty1 & sta1 & Hck1 & Hstc).
          eapply sec_bind_inv in Hstc as (inptyp1 & sta2 & Hinp1 & Hstc).
          eapply sec_bind_inv in Hstc as (outtyp1 & sta3 & Hout1 & Hgen1).
          unfold option_to_sec in Hck1.
          rewrite Hckopt in Hck1. unfold ret in Hck1.
          inversion Hck1; subst ckty1 sta1.
          assert (Houteq : outtyp1 = outtyp2).
          { eapply (@mmap_consistent ident ident
                      (fun z => SC.find_env z env) (fun z => SC.find_env z env)
                      (x :: xs')); eauto.
            intros. eapply SC.find_env_consistent; eauto. }
          subst outtyp2.
          destruct (Hcons f n1 Hf1) as (n2' & Hf2' & Hpres).
          rewrite Hf2 in Hf2'. inversion Hf2'; subst n2'.
          eapply (Hpres scope inptyp1 inptyp2 ckty [rst_ty] sty outtyp1
                    nconst sconst sta3 stb3 st1' st2').
          * eapply Hside; eauto.
          * eapply translate_args_type_incl; eauto.
          * exact Hgen1.
          * exact Hgen2.
    Qed.

  End TCPRESERV.

End SECSTCOBCTRANSLATION.

Module SecStcObcTranslation
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import LastStc  : STCISLAST Ids Op CESyn SynStc)
  (Import VarStc   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import DefStc   : STCISDEFINED Ids Op CESyn SynStc VarStc LastStc)
  (Import SystStc  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc   : STCORDERED Ids Op CESyn SynStc SystStc)
  (Import IsFStc   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc   : STCCLOCKING Ids Op CESyn SynStc LastStc VarStc DefStc SystStc OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo
                           SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc)
  (Import Trans : TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS SECOBCTYPING)
  <: SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc Lat SecT SIG SIGPROOFS
       CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc SECSTCTYPING Trans
       SECOBCTYPING SECOBCTYPINGCORRECTNESS.

Include SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc Lat SecT SIG SIGPROOFS
  CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc SECSTCTYPING Trans
  SECOBCTYPING SECOBCTYPINGCORRECTNESS.

End SecStcObcTranslation.
