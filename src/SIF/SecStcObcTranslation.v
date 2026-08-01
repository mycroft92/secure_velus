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
From Velus Require Import SIF.Helpers.
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
From Coq Require Import Sorting.Permutation.
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

    (** Converse of the previous lemma: a *successful* run on
        [Control ck s] already implies that the clock's variables are
        bound, hence that the clock pc exists.  This is how the [ckty] of
        a call with no outputs is obtained, the STC generator returning
        [ret []] there without ever consulting the clock. *)

    Lemma generate_stmt_constraints_Control_inv:
      forall memset ck s pc cns st st',
        generate_stmt_constraints G env state_env rst_ty pc (Control memset ck s) st
          = OK (cns, st') ->
        exists pc',
          clock_pc pc ck = Some pc'
          /\ generate_stmt_constraints G env state_env rst_ty pc' s st = OK (cns, st').
    Proof.
      intros memset ck. induction ck as [|ck IH x b]; intros s pc cns st st' Hgen.
      - exists pc. split; [reflexivity|exact Hgen].
      - simpl in Hgen.
        destruct b.
        + destruct (IH _ _ _ _ _ Hgen) as (pcck & Hpcck & Hifte).
          simpl in Hifte.
          eapply sec_bind_inv in Hifte as (ety & sa & Hety & Hifte).
          eapply sec_bind_inv in Hifte as (c1 & sb & Hc1 & Hifte).
          eapply sec_bind_inv in Hifte as (c2 & sc & Hc2 & Hret).
          unfold ret in Hret. inversion Hret; subst cns st'.
          unfold option_to_sec in Hety.
          unfold bool_var, tovar in Hety.
          destruct (PS.mem x memset) eqn:Hmem; simpl in Hety;
            (destruct (Env.find x env) as [ty|] eqn:Hx; try discriminate;
             unfold ret in Hety; inversion Hety; subst ety sa;
             simpl in Hc2; unfold ret in Hc2; inversion Hc2; subst c2 sc;
             exists (pcck ⊔ [ty]); split;
             [simpl; now rewrite Hpcck, Hx
             |rewrite app_nil_r; exact Hc1]).
        + destruct (IH _ _ _ _ _ Hgen) as (pcck & Hpcck & Hifte).
          simpl in Hifte.
          eapply sec_bind_inv in Hifte as (ety & sa & Hety & Hifte).
          eapply sec_bind_inv in Hifte as (c1 & sb & Hc1 & Hifte).
          eapply sec_bind_inv in Hifte as (c2 & sc & Hc2 & Hret).
          unfold ret in Hret. inversion Hret; subst cns st'.
          unfold option_to_sec in Hety.
          unfold bool_var, tovar in Hety.
          destruct (PS.mem x memset) eqn:Hmem; simpl in Hety;
            (destruct (Env.find x env) as [ty|] eqn:Hx; try discriminate;
             unfold ret in Hety; inversion Hety; subst ety sa;
             simpl in Hc1; unfold ret in Hc1; inversion Hc1; subst c1 sb;
             exists (pcck ⊔ [ty]); split;
             [simpl; now rewrite Hpcck, Hx|simpl; exact Hc2]).
    Qed.

    Lemma clock_pc_assign_clk_type:
      forall ck pc pc' b,
        clock_pc pc ck = Some pc' ->
        exists ckty, SECCETYPING.assign_clk_type env b ck = Some ckty.
    Proof.
      induction ck as [|ck IH x bb]; intros pc pc' b Hpc; simpl in Hpc.
      - simpl. eauto.
      - destruct (clock_pc pc ck) as [pcck|] eqn:Hck; try discriminate.
        destruct (Env.find x env) as [ty|] eqn:Hx; try discriminate.
        destruct (IH _ _ b Hck) as (ckty & Hckty).
        simpl. rewrite Hckty. simpl. rewrite Hx.
        eexists; reflexivity.
    Qed.

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
    (** One instance environment, shared by both languages: the name
        generator mints these names once, so the STC reset instance and
        the Obc instance state are the same identifier. *)
    Variable reset_env: Env.t ident.
    Variable clk_ty rst_ty: ident.

    Lemma tcdef_preserv:
      forall scope memset clkvars vars x ck ce nconst sconst st1 st1' st2 st2',
        CEClo.wc_cexp vars ce ck ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcDef x ck ce) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
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
      destruct (translate_tcdef_constraints G2 env reset_env rst_ty
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
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
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
      destruct (translate_tcnext_constraints G2 env reset_env rst_ty
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
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcReset s ck f) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcReset s ck f)) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars s ck f nconst sconst st1 st1' st2 st2'
             Hstc Hobc.
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
        destruct (translate_tcreset_constraints G2 env reset_env rst_ty
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
          destruct (translate_tcreset_constraints G2 env reset_env rst_ty
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
          destruct (translate_tcreset_constraints G2 env reset_env rst_ty
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
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
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
                 G2 env reset_env rst_ty memset ck
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


    (** ** Closing the call obligation

        The Obc side instantiates its callee at *weaker* input types (the
        compiled arguments drop the [when] guards).  We reduce to the
        equal-actuals case that is already proved:

        - [generate_constraints_ok_change_inp] gives an Obc run at the
          STC input types;
        - [signatures_preserved_reset_underlying_calls_from_good] relates
          the two runs at those inputs (its conclusion prepends the
          reset-defining constraint, which we discard);
        - [generate_constraints_mono_inp] plus
          [constraints_src_le_satisfaction] descend from that run to the
          actual, weaker one.

        Note the completeness direction is only ever used with *equal*
        actuals, so no generalisation of it is required. *)

    Theorem signatures_preserved_obc_calls_from_good:
      forall nsig ssig,
        SIG.signature_good nsig ->
        NoDup (SIG.signature_scope nsig) ->
        SIG.signature_scoped ssig ->
        SIGPROOFS.signatures_preserved nsig ssig ->
        Signature_call_preserves_obc nsig ssig.
    Proof.
      intros nsig ssig Hgood Hnd Hssc Hpres.
      intros scope inptyp1 inptyp2 ckty srcrst sty outtyp
             nconst sconst si1 si2 stA stB Hside Hincl Hgen1 Hgen2.
      destruct Hside as (Hsf & Hcss & Hstynotin & Hfr1 & Hfr2).
      (* the Obc callee also generates at the STC input types *)
      assert (Hlen : List.length inptyp2 = List.length inptyp1).
      { symmetry. eapply Forall2_length; eauto. }
      destruct (SIGPROOFS.generate_constraints_ok_change_inp
                  ssig inptyp2 inptyp1 ckty [sty] outtyp sconst si2 stB si2
                  Hlen Hgen2)
        as (sconst1 & sB1 & Hgen2').
      (* freshness of the STC inputs w.r.t. the Obc scope, via field agreement *)
      destruct Hpres as [Hfields Hprescns].
      assert (Hscopeeq : SIG.signature_scope nsig = SIG.signature_scope ssig).
      { eapply SIG.signature_fields_agree_scope_eq; eauto. }
      destruct Hfr1 as (Hin1 & Hclk1 & Hrst1 & Hout1).
      destruct Hfr2 as (Hin2 & Hclk2 & Hrst2 & Hout2).
      assert (Hfr2' : SIG.call_subst_fresh ssig inptyp1 ckty [sty] outtyp).
      { repeat split.
        - rewrite <- Hscopeeq. exact Hin1.
        - rewrite <- Hscopeeq. exact Hclk1.
        - exact Hrst2.
        - rewrite <- Hscopeeq. exact Hout1. }
      (* equal-actuals case *)
      pose proof (SIGPROOFS.signatures_preserved_reset_underlying_calls_from_good
                    nsig ssig Hgood Hnd Hssc (conj Hfields Hprescns)
                    scope inptyp1 ckty srcrst outtyp sty
                    nconst sconst1 si1 si2 stA sB1
                    Hsf Hcss Hstynotin
                    (conj Hin1 (conj Hclk1 (conj Hrst1 Hout1)))
                    Hfr2' Hgen1 Hgen2')
        as Hpres1.
      (* descend to the weaker inputs *)
      assert (Hle : constraints_src_le sconst1 sconst).
      { eapply SIGPROOFS.generate_constraints_mono_inp;
          [exact Hincl|exact Hgen2'|exact Hgen2]. }
      intros dlt Hsat.
      destruct (Hpres1 dlt Hsat) as (dlt' & Hagree & Hsat').
      exists dlt'. split; [exact Hagree|].
      inversion Hsat' as [|c cs Hc Hcs]; subst.
      eapply constraints_src_le_satisfaction; eauto.
    Qed.




    (** The reset-underlying call theorem already *produces* the
        constraint [srcrst |- sty]; [signatures_preserved_obc_calls_from_good]
        simply discards it.  For an instance the system never resets,
        that discarded constraint is exactly what the Obc reset method
        emits for it, so keeping it lets the call block own its own
        reset-method constraint instead of leaving [sty] constrained
        from two different blocks. *)

    Definition Signature_call_preserves_obc_rst (n1 n2: SIG.signature) : Prop :=
      forall scope inptyp1 inptyp2 ckty srcrst sty outtyp
             nconst sconst st_init1 st_init2 stA stB,
        call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty srcrst sty outtyp ->
        Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) inptyp1 inptyp2 ->
        SIG.generate_constraints n1 inptyp1 ckty srcrst outtyp st_init1 = OK (nconst, stA) ->
        SIG.generate_constraints n2 inptyp2 ckty [sty] outtyp st_init2 = OK (sconst, stB) ->
        preserves_on scope nconst ((srcrst, [sty]) :: sconst).

    Theorem signatures_preserved_obc_calls_from_good_rst:
      forall nsig ssig,
        SIG.signature_good nsig ->
        NoDup (SIG.signature_scope nsig) ->
        SIG.signature_scoped ssig ->
        SIGPROOFS.signatures_preserved nsig ssig ->
        Signature_call_preserves_obc_rst nsig ssig.
    Proof.
      intros nsig ssig Hgood Hnd Hssc Hpres.
      intros scope inptyp1 inptyp2 ckty srcrst sty outtyp
             nconst sconst si1 si2 stA stB Hside Hincl Hgen1 Hgen2.
      destruct Hside as (Hsf & Hcss & Hstynotin & Hfr1 & Hfr2).
      assert (Hlen : List.length inptyp2 = List.length inptyp1).
      { symmetry. eapply Forall2_length; eauto. }
      destruct (SIGPROOFS.generate_constraints_ok_change_inp
                  ssig inptyp2 inptyp1 ckty [sty] outtyp sconst si2 stB si2
                  Hlen Hgen2)
        as (sconst1 & sB1 & Hgen2').
      destruct Hpres as [Hfields Hprescns].
      assert (Hscopeeq : SIG.signature_scope nsig = SIG.signature_scope ssig).
      { eapply SIG.signature_fields_agree_scope_eq; eauto. }
      destruct Hfr1 as (Hin1 & Hclk1 & Hrst1 & Hout1).
      destruct Hfr2 as (Hin2 & Hclk2 & Hrst2 & Hout2).
      assert (Hfr2' : SIG.call_subst_fresh ssig inptyp1 ckty [sty] outtyp).
      { repeat split.
        - rewrite <- Hscopeeq. exact Hin1.
        - rewrite <- Hscopeeq. exact Hclk1.
        - exact Hrst2.
        - rewrite <- Hscopeeq. exact Hout1. }
      pose proof (SIGPROOFS.signatures_preserved_reset_underlying_calls_from_good
                    nsig ssig Hgood Hnd Hssc (conj Hfields Hprescns)
                    scope inptyp1 ckty srcrst outtyp sty
                    nconst sconst1 si1 si2 stA sB1
                    Hsf Hcss Hstynotin
                    (conj Hin1 (conj Hclk1 (conj Hrst1 Hout1)))
                    Hfr2' Hgen1 Hgen2')
        as Hpres1.
      assert (Hle : constraints_src_le sconst1 sconst).
      { eapply SIGPROOFS.generate_constraints_mono_inp;
          [exact Hincl|exact Hgen2'|exact Hgen2]. }
      intros dlt Hsat.
      destruct (Hpres1 dlt Hsat) as (dlt' & Hagree & Hsat').
      exists dlt'. split; [exact Hagree|].
      inversion Hsat' as [|c cs Hc Hcs]; subst.
      constructor; [exact Hc|].
      eapply constraints_src_le_satisfaction; eauto.
    Qed.

    (** Dropping the head recovers the plain version. *)

    Lemma Signature_call_preserves_obc_from_rst:
      forall n1 n2,
        Signature_call_preserves_obc_rst n1 n2 ->
        Signature_call_preserves_obc n1 n2.
    Proof.
      intros n1 n2 Hrst.
      intros scope inptyp1 inptyp2 ckty srcrst sty outtyp
             nconst sconst si1 si2 stA stB Hside Hincl Hgen1 Hgen2.
      intros dlt Hsat.
      destruct (Hrst scope inptyp1 inptyp2 ckty srcrst sty outtyp
                  nconst sconst si1 si2 stA stB Hside Hincl Hgen1 Hgen2 dlt Hsat)
        as (dlt' & Hagree & Hsat').
      exists dlt'. split; [exact Hagree|].
      now inversion Hsat'.
    Qed.

    (** For an instance the system *resets*, the STC call passes the
        reset instance type and the Obc call passes the instance's state
        type — and those are the same identifier.  The two calls then
        differ only in their input actuals, so the equal-actuals
        preservation applies and no freshness side condition on that
        identifier is needed.  This is what lets the reset instance stay
        inside the shared scope, where the [TcReset] constraint also
        mentions it. *)

    Definition Signature_call_preserves_obc_eq (n1 n2: SIG.signature) : Prop :=
      forall scope inptyp1 inptyp2 ckty rstty outtyp
             nconst sconst st_init1 st_init2 stA stB,
        SIG.scope_fresh scope n1 ->
        SIG.call_subst_scoped scope inptyp1 ckty rstty outtyp ->
        SIG.call_subst_fresh n1 inptyp1 ckty rstty outtyp ->
        Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) inptyp1 inptyp2 ->
        SIG.generate_constraints n1 inptyp1 ckty rstty outtyp st_init1 = OK (nconst, stA) ->
        SIG.generate_constraints n2 inptyp2 ckty rstty outtyp st_init2 = OK (sconst, stB) ->
        preserves_on scope nconst sconst.

    Theorem signatures_preserved_obc_equal_calls_from_good:
      forall nsig ssig,
        SIG.signature_good nsig ->
        NoDup (SIG.signature_scope nsig) ->
        SIG.signature_scoped ssig ->
        SIGPROOFS.signatures_preserved nsig ssig ->
        Signature_call_preserves_obc_eq nsig ssig.
    Proof.
      intros nsig ssig Hgood Hnd Hssc Hpres.
      intros scope inptyp1 inptyp2 ckty rstty outtyp
             nconst sconst si1 si2 stA stB Hsf Hcss Hfr1 Hincl Hgen1 Hgen2.
      assert (Hlen : List.length inptyp2 = List.length inptyp1).
      { symmetry. eapply Forall2_length; eauto. }
      destruct (SIGPROOFS.generate_constraints_ok_change_inp
                  ssig inptyp2 inptyp1 ckty rstty outtyp sconst si2 stB si2
                  Hlen Hgen2)
        as (sconst1 & sB1 & Hgen2').
      pose proof (SIGPROOFS.signatures_preserved_equal_calls_from_good
                    nsig ssig Hgood Hnd Hssc Hpres
                    scope inptyp1 ckty rstty outtyp
                    nconst sconst1 si1 si2 stA sB1
                    Hsf Hcss Hfr1 Hgen1 Hgen2')
        as Hpres1.
      assert (Hle : constraints_src_le sconst1 sconst).
      { eapply SIGPROOFS.generate_constraints_mono_inp;
          [exact Hincl|exact Hgen2'|exact Hgen2]. }
      intros dlt Hsat.
      destruct (Hpres1 dlt Hsat) as (dlt' & Hagree & Hsat').
      exists dlt'. split; [exact Hagree|].
      eapply constraints_src_le_satisfaction; eauto.
    Qed.


    Definition Signature_consistent_obc_eq (H1 H2: SIG.secglobal) : Prop :=
      forall f n1,
        SIG.find_signature f H1 = Some n1 ->
        exists n2,
          SIG.find_signature f H2 = Some n2
          /\ Signature_call_preserves_obc_eq n1 n2.

    (** The [TcCall] case for an instance the system resets.  Both sides
        pass the same reset actual, so no freshness condition on it is
        required and it may live in the shared scope. *)

    Lemma tccall_reset_preserv_eq:
      forall scope memset clkvars i xs ck f es ckty
             nconst sconst st1 st1' st2 st2',
        SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
        Signature_consistent_obc_eq G1 G2 ->
        (forall n1 inptyp1 rinst outtyp,
            SIG.find_signature f G1 = Some n1 ->
            SIG.scope_fresh scope n1
            /\ SIG.call_subst_scoped scope inptyp1 ckty [rinst] outtyp
            /\ SIG.call_subst_fresh n1 inptyp1 ckty [rinst] outtyp) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcCall i xs ck true f es) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcCall i xs ck true f es)) st2
          = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope memset clkvars i xs ck f es ckty
             nconst sconst st1 st1' st2 st2' Hckopt Hcons Hside Hstc Hobc.
      unfold translate_tc in Hobc.
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      rewrite (generate_stmt_constraints_Control_assign
                 G2 env reset_env rst_ty memset ck
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
      - simpl in Hobc.
        assert (Hstep : ident_eqb step step = true) by apply ident_eqb_refl.
        rewrite Hstep in Hobc.
        destruct (SIG.find_signature f G2) as [n2|] eqn:Hf2; try discriminate.
        eapply sec_bind_inv in Hobc as (inptyp2 & stb1 & Hinp2 & Hobc).
        eapply sec_bind_inv in Hobc as (outtyp2 & stb2 & Hout2 & Hobc).
        eapply sec_bind_inv in Hobc as (sty & stb3 & Hsty & Hgen2).
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
        assert (Hrsteq : rinst = sty).
        { unfold SC.find_env in Hrinst, Hsty.
          destruct (Env.find i reset_env) as [v|]; try discriminate.
          unfold ret in Hrinst, Hsty. congruence. }
        subst sty.
        destruct (Hcons f n1 Hf1) as (n2' & Hf2' & Hpres).
        rewrite Hf2 in Hf2'. inversion Hf2'; subst n2'.
        destruct (Hside n1 inptyp1 rinst outtyp1 Logic.eq_refl) as (Hsf & Hcss & Hfr1).
        eapply (Hpres scope inptyp1 inptyp2 ckty [rinst] outtyp1
                  nconst sconst sta4 stb3 st1' st2');
          [exact Hsf|exact Hcss|exact Hfr1| |exact Hgen1|exact Hgen2].
        eapply translate_args_type_incl; eauto.
    Qed.

    (** ** From the [translate_tcs] fold to a per-trconstr concatenation

        [translate_tcs] is a *left* fold that nests [Comp] in reverse
        execution order, so the Obc constraints come out as the
        reverse-order concatenation of the per-trconstr blocks, while the
        STC generator concatenates them in order.  The two lists are
        therefore permutations of each other, and satisfaction (a
        [Forall]) does not care — see [preserves_on_Permutation]. *)

    Lemma translate_tcs_fold_right:
      forall memset clkvars tcs,
        translate_tcs memset clkvars tcs
        = fold_right (fun tc i => SynObc.Comp (translate_tc memset clkvars tc) i)
            SynObc.Skip (rev tcs).
    Proof.
      intros memset clkvars tcs.
      unfold translate_tcs.
      rewrite <- fold_left_rev_right.
      reflexivity.
    Qed.

    (** Generating constraints for a right fold of [Comp]s is the
        concatenation of the per-statement constraint blocks, with the
        state threaded left to right. *)

    Lemma generate_fold_right_Comp:
      forall memset clkvars pc tcs cns st st',
        generate_stmt_constraints G2 env reset_env rst_ty pc
          (fold_right (fun tc i => SynObc.Comp (translate_tc memset clkvars tc) i)
             SynObc.Skip tcs) st = OK (cns, st') ->
        exists blocks,
          cns = concat blocks
          /\ Forall2 (fun tc blk =>
                        exists sa sb,
                          generate_stmt_constraints G2 env reset_env rst_ty pc
                            (translate_tc memset clkvars tc) sa = OK (blk, sb))
                     tcs blocks.
    Proof.
      intros memset clkvars pc tcs.
      induction tcs as [|tc tcs IH]; intros cns st st' Hgen.
      - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
        exists nil. split; [reflexivity|constructor].
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hc1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hc2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        destruct (IH c2 st1 st2 Hc2) as (blocks & Hblocks & Hall).
        exists (c1 :: blocks). split.
        + simpl. f_equal. exact Hblocks.
        + constructor; [|exact Hall].
          exists st, st1. exact Hc1.
    Qed.

    (** ** Whole-body preservation

        The four per-trconstr results are packaged behind one predicate
        collecting the side conditions each case needs, and then lifted
        to the whole transition-constraint list. *)

    Definition tc_preserv_hyps (scope: list ident) vars (tc: SynStc.trconstr) : Prop :=
      match tc with
      | SynStc.TcDef _ ck ce => CEClo.wc_cexp vars ce ck
      | SynStc.TcNext _ ck e => CEClo.wc_exp vars e ck
      | SynStc.TcReset _ _ _ => True
      | SynStc.TcCall _ _ ck _ f _ =>
          exists ckty,
            SECCETYPING.assign_clk_type env clk_ty ck = Some ckty
            /\ (forall n1 n2 inptyp1 inptyp2 outtyp srcrst sty,
                   SIG.find_signature f G1 = Some n1 ->
                   SIG.find_signature f G2 = Some n2 ->
                   call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty srcrst sty outtyp)
      end.

    Lemma tc_preserv:
      forall scope vars memset clkvars tc nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc G1 G2 ->
        tc_preserv_hyps scope vars tc ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty tc st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars tc) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope vars memset clkvars tc nconst sconst st1 st1' st2 st2'
             Hcons Hhyps Hstc Hobc.
      destruct tc as [x ck ce|x ck e|s ck f|i xs ck rst f es]; simpl in Hhyps.
      - eapply tcdef_preserv; eauto.
      - eapply tcnext_preserv; eauto.
      - eapply tcreset_preserv; eauto.
      - destruct Hhyps as (ckty & Hckty & Hside).
        eapply tccall_preserv; eauto.
    Qed.

    (** Both call forms are needed at once: an instance the system resets
        is called with the same reset actual on both sides (equal-actuals
        preservation, its identifier inside the scope), while one it never
        resets is called with [rst_ty] on the STC side and its state type
        on the Obc side (reset-underlying preservation, its identifier a
        private extra). *)

    Definition Signature_consistent_obc_full (H1 H2: SIG.secglobal) : Prop :=
      forall f n1,
        SIG.find_signature f H1 = Some n1 ->
        exists n2,
          SIG.find_signature f H2 = Some n2
          /\ Signature_call_preserves_obc_rst n1 n2
          /\ Signature_call_preserves_obc_eq n1 n2.

    Lemma signatures_preserved_obc_full_from_good:
      forall nsig ssig,
        SIG.signature_good nsig ->
        NoDup (SIG.signature_scope nsig) ->
        SIG.signature_scoped ssig ->
        SIGPROOFS.signatures_preserved nsig ssig ->
        Signature_call_preserves_obc_rst nsig ssig
        /\ Signature_call_preserves_obc_eq nsig ssig.
    Proof.
      intros nsig ssig Hgood Hnd Hssc Hpres. split.
      - eapply signatures_preserved_obc_calls_from_good_rst; eauto.
      - eapply signatures_preserved_obc_equal_calls_from_good; eauto.
    Qed.

    (** The [TcCall] case for an instance the system never resets.  The
        Obc call passes the instance's state type where STC passes
        [rst_ty], so the block owns that identifier - and, with it, the
        reset method's constraint on it. *)

    Lemma tccall_unreset_preserv_rst:
      forall scope memset clkvars i xs ck f es ckty sty
             nconst sconst st1 st1' st2 st2',
        SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
        Env.find i reset_env = Some sty ->
        Signature_consistent_obc_full G1 G2 ->
        (forall n1 n2 inptyp1 inptyp2 outtyp,
            SIG.find_signature f G1 = Some n1 ->
            SIG.find_signature f G2 = Some n2 ->
            call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty [rst_ty] sty outtyp) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcCall i xs ck false f es) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcCall i xs ck false f es)) st2
          = OK (sconst, st2') ->
        xs <> [] ->
        preserves_on scope nconst (sconst ++ [([rst_ty], [sty])]).
    Proof.
      intros scope memset clkvars i xs ck f es ckty sty
             nconst sconst st1 st1' st2 st2' Hckopt Hsty Hcons Hside Hstc Hobc Hxs.
      unfold translate_tc in Hobc.
      rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
      rewrite (generate_stmt_constraints_Control_assign
                 G2 env reset_env rst_ty memset ck
                 (SynObc.Call xs f i step (map (translate_arg memset clkvars ck) es))
                 clk_ty ckty [] st2 Hckopt) in Hobc.
      rewrite (MergeFacts.merge_nil2 ckty) in Hobc.
      destruct xs as [|x xs']; [contradiction|].
      simpl in Hobc.
      assert (Hstep : ident_eqb step step = true) by apply ident_eqb_refl.
      rewrite Hstep in Hobc.
      destruct (SIG.find_signature f G2) as [n2|] eqn:Hf2; try discriminate.
      eapply sec_bind_inv in Hobc as (inptyp2 & stb1 & Hinp2 & Hobc).
      eapply sec_bind_inv in Hobc as (outtyp2 & stb2 & Hout2 & Hobc).
      eapply sec_bind_inv in Hobc as (sty' & stb3 & Hsty' & Hgen2).
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
      assert (Hstyeq : sty' = sty).
      { unfold SC.find_env in Hsty'. rewrite Hsty in Hsty'.
        unfold ret in Hsty'. now inversion Hsty'. }
      subst sty'.
      destruct (Hcons f n1 Hf1) as (n2' & Hf2' & Hpresrst & _).
      rewrite Hf2 in Hf2'. inversion Hf2'; subst n2'.
      eapply preserves_on_Permutation;
        [reflexivity|apply Permutation_cons_append|].
      eapply (Hpresrst scope inptyp1 inptyp2 ckty [rst_ty] sty outtyp1
                nconst sconst sta3 stb3 st1' st2').
      - eapply Hside; eauto.
      - eapply translate_args_type_incl; eauto.
      - exact Hgen1.
      - exact Hgen2.
    Qed.

    (** A call with no outputs emits nothing on either side, yet the
        instance is still in [c_objs] and the reset method still
        constrains it.  Its state type is constrained nowhere else, so
        the block covers it by naming that identifier directly. *)

    Lemma preserves_on_reset_only_extra:
      forall scope sty,
        List.In rst_ty scope ->
        ~ List.In sty scope ->
        preserves_on scope [] [([rst_ty], [sty])].
    Proof.
      intros scope sty Hrst Hsty dlt _.
      exists (overlay_scope scope dlt (fun _ => hm_ext dlt [rst_ty])).
      set (dlt' := overlay_scope scope dlt (fun _ => hm_ext dlt [rst_ty])).
      assert (Hrsteq : dlt' rst_ty = dlt rst_ty).
      { unfold dlt', overlay_scope.
        destruct (in_dec ident_eq_dec rst_ty scope); [reflexivity|contradiction]. }
      assert (Hstyeq : dlt' sty = hm_ext dlt [rst_ty]).
      { unfold dlt', overlay_scope.
        destruct (in_dec ident_eq_dec sty scope); [contradiction|reflexivity]. }
      split.
      - apply overlay_scope_agree_on.
      - constructor; [|constructor].
        unfold constraintSatisfiable, satisfiable.
        eapply Lat.order_trans with (y := dlt' sty).
        + cbn [hm_ext]. rewrite Hrsteq, Hstyeq. cbn [hm_ext].
          apply Lat.order_refl, Lat.eq_refl.
        + eapply hm_ext_list_in1. simpl. now left.
    Qed.

    (** ** Obc-exclusive names, per trconstr

        The only Obc constraint mentioning a name the STC side never sees
        is the call of an instance the system does *not* reset: there the
        STC call passes [rst_ty] while the Obc call passes the instance's
        state type.  For every other trconstr the two sides range over
        the same identifiers, so the block has no private names.

        A reset instance is *not* exclusive: the shared name generator
        gives it one identifier, used by both languages. *)

    Definition tc_obc_extras (tc: SynStc.trconstr) : option (list ident) :=
      match tc with
      | SynStc.TcCall i _ _ false _ _ =>
          match Env.find i reset_env with
          | Some sty => Some [sty]
          | None => None
          end
      | _ => Some []
      end.

    Fixpoint tcs_obc_extras (tcs: list SynStc.trconstr) : option (list (list ident)) :=
      match tcs with
      | [] => Some []
      | tc :: tcs' =>
          match tc_obc_extras tc, tcs_obc_extras tcs' with
          | Some e, Some es => Some (e :: es)
          | _, _ => None
          end
      end.

    Lemma tcs_obc_extras_Forall2:
      forall tcs es,
        tcs_obc_extras tcs = Some es ->
        Forall2 (fun tc e => tc_obc_extras tc = Some e) tcs es.
    Proof.
      induction tcs as [|tc tcs IH]; intros es Hes; simpl in Hes.
      - inversion Hes; subst. constructor.
      - destruct (tc_obc_extras tc) as [e|] eqn:He; try discriminate.
        destruct (tcs_obc_extras tcs) as [es'|] eqn:Hes'; try discriminate.
        inversion Hes; subst es.
        constructor; [exact He|now apply IH].
    Qed.

    (** Every extra is the state type of an instance the system does not
        reset, so it is bound in the shared environment. *)

    Lemma tc_obc_extras_spec:
      forall tc e ty,
        tc_obc_extras tc = Some e ->
        List.In ty e ->
        exists i, Env.find i reset_env = Some ty
                  /\ (exists xs ck f es, tc = SynStc.TcCall i xs ck false f es).
    Proof.
      intros tc e ty He Hin.
      destruct tc as [x ck ce|x ck ex|x ck f|i xs ck [|] f es];
        simpl in He; try (inversion He; subst e; inversion Hin).
      destruct (Env.find i reset_env) as [sty|] eqn:Hfind; try discriminate.
      inversion He; subst e.
      destruct Hin as [Heq|[]]. subst ty.
      exists i. split; [exact Hfind|].
      exists xs, ck, f, es. reflexivity.
    Qed.

    (** The extras of a whole body are exactly the state types of the
        instances it steps without resetting, so their distinctness
        reduces to distinctness of those instances. *)

    Fixpoint unreset_call_insts (tcs: list SynStc.trconstr) : list ident :=
      match tcs with
      | [] => []
      | SynStc.TcCall i _ _ false _ _ :: tcs' => i :: unreset_call_insts tcs'
      | _ :: tcs' => unreset_call_insts tcs'
      end.

    Lemma tcs_obc_extras_concat:
      forall tcs es,
        tcs_obc_extras tcs = Some es ->
        get_mappings (unreset_call_insts tcs) reset_env = Some (List.concat es).
    Proof.
      induction tcs as [|tc tcs IH]; intros es Hes; simpl in Hes.
      - inversion Hes; subst es. reflexivity.
      - destruct (tc_obc_extras tc) as [e|] eqn:He; try discriminate.
        destruct (tcs_obc_extras tcs) as [es'|] eqn:Hes'; try discriminate.
        inversion Hes; subst es.
        specialize (IH es' Logic.eq_refl).
        destruct tc as [x ck ce|x ck ex|x ck f|i xs ck [|] f es0];
          simpl in He; simpl.
        1,2,3: inversion He; subst e; simpl; exact IH.
        + inversion He; subst e; simpl; exact IH.
        + destruct (Env.find i reset_env) as [sty|] eqn:Hfind; try discriminate.
          inversion He; subst e.
          cbn [unreset_call_insts get_mappings List.concat].
          rewrite IH. reflexivity.
    Qed.

    Lemma tcs_obc_extras_nodup:
      forall tcs es,
        env_injective reset_env ->
        NoDup (unreset_call_insts tcs) ->
        tcs_obc_extras tcs = Some es ->
        NoDup (List.concat es).
    Proof.
      intros tcs es Hinj Hnd Hes.
      eapply get_mappings_nodup_gen; [exact Hnd|exact Hinj|].
      now apply tcs_obc_extras_concat.
    Qed.

    Lemma Signature_consistent_obc_eq_from_full:
      forall H1 H2,
        Signature_consistent_obc_full H1 H2 ->
        Signature_consistent_obc_eq H1 H2.
    Proof.
      intros H1 H2 Hfull f n1 Hf.
      destruct (Hfull f n1 Hf) as (n2 & Hf2 & _ & Heq).
      exists n2. split; assumption.
    Qed.

    (** ** Per-trconstr preservation, with the block owning its extras

        The target of a block is its own Obc constraints together with
        the reset-method constraint of any instance it owns. *)

    Definition tc_preserv_hyps_aug (scope: list ident) vars (tc: SynStc.trconstr) : Prop :=
      match tc with
      | SynStc.TcDef _ ck ce => CEClo.wc_cexp vars ce ck
      | SynStc.TcNext _ ck e => CEClo.wc_exp vars e ck
      | SynStc.TcReset _ _ _ => True
      | SynStc.TcCall _ _ ck true f _ =>
          forall ckty n1 inptyp1 rinst outtyp,
            SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
            SIG.find_signature f G1 = Some n1 ->
            SIG.scope_fresh scope n1
            /\ SIG.call_subst_scoped scope inptyp1 ckty [rinst] outtyp
            /\ SIG.call_subst_fresh n1 inptyp1 ckty [rinst] outtyp
      | SynStc.TcCall i _ ck false f _ =>
          List.In rst_ty scope
          /\ (exists sty, Env.find i reset_env = Some sty /\ ~ List.In sty scope)
          /\ (forall ckty sty n1 n2 inptyp1 inptyp2 outtyp,
                  SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
                  Env.find i reset_env = Some sty ->
                  SIG.find_signature f G1 = Some n1 ->
                  SIG.find_signature f G2 = Some n2 ->
                  call_side_conditions scope n1 n2 inptyp1 inptyp2 ckty
                    [rst_ty] sty outtyp)
      end.

    Lemma tc_preserv_aug:
      forall scope vars memset clkvars tc e nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        tc_preserv_hyps_aug scope vars tc ->
        tc_obc_extras tc = Some e ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty tc st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars tc) st2 = OK (sconst, st2') ->
        preserves_on scope nconst (sconst ++ map (fun ty => ([rst_ty], [ty])) e).
    Proof.
      intros scope vars memset clkvars tc e nconst sconst st1 st1' st2 st2'
             Hcons Hhyps Hextras Hstc Hobc.
      destruct tc as [x ck ce|x ck ex|i ck f|i xs ck [|] f es];
        simpl in Hhyps, Hextras.
      - inversion Hextras; subst e. simpl. rewrite app_nil_r.
        eapply tcdef_preserv; eauto.
      - inversion Hextras; subst e. simpl. rewrite app_nil_r.
        eapply tcnext_preserv; eauto.
      - inversion Hextras; subst e. simpl. rewrite app_nil_r.
        eapply tcreset_preserv; eauto.
      - (* a reset'd call: both sides pass the same actual, no extras *)
        inversion Hextras; subst e. simpl. rewrite app_nil_r.
        unfold translate_tc in Hobc.
        destruct (generate_stmt_constraints_Control_inv
                    G2 env reset_env rst_ty _ _ _ _ _ _ _ Hobc)
          as (pc' & Hpc' & _).
        edestruct clock_pc_assign_clk_type with (b := clk_ty)
          as (ckty & Hckty); [exact Hpc'|].
        eapply tccall_reset_preserv_eq with (ckty := ckty).
        + exact Hckty.
        + eapply Signature_consistent_obc_eq_from_full; exact Hcons.
        + intros n1 inptyp1 rinst outtyp Hf1. eapply Hhyps; eauto.
        + exact Hstc.
        + exact Hobc.
      - (* an unreset call: the block owns the instance's state type *)
        destruct Hhyps as (Hrstin & (sty & Hsty & Hstynotin) & Hside).
        rewrite Hsty in Hextras. inversion Hextras; subst e. simpl.
        assert (Hckex : exists ckty,
                   SECCETYPING.assign_clk_type env clk_ty ck = Some ckty).
        { unfold translate_tc in Hobc.
          destruct (generate_stmt_constraints_Control_inv
                      G2 env reset_env rst_ty _ _ _ _ _ _ _ Hobc)
            as (pc' & Hpc' & _).
          eapply (clock_pc_assign_clk_type env _ _ _ clk_ty); eauto. }
        destruct Hckex as (ckty & Hckty).
        destruct xs as [|x xs'].
        + (* no outputs: both generators emit nothing *)
          simpl in Hstc. unfold ret in Hstc. inversion Hstc; subst nconst st1'.
          unfold translate_tc in Hobc.
          rewrite <- (MergeFacts.merge_nil2 [clk_ty]) in Hobc.
          rewrite (generate_stmt_constraints_Control_assign
                     G2 env reset_env rst_ty memset ck
                     (SynObc.Call [] f i step (map (translate_arg memset clkvars ck) es))
                     clk_ty ckty [] st2 Hckty) in Hobc.
          rewrite (MergeFacts.merge_nil2 ckty) in Hobc.
          simpl in Hobc.
          assert (Hne : ident_eqb step reset = false).
          { apply ident_eqb_neq. intro Heq. symmetry in Heq.
            revert Heq. apply reset_not_step. }
          rewrite Hne in Hobc.
          unfold ret in Hobc. inversion Hobc; subst sconst st2'.
          simpl. now apply preserves_on_reset_only_extra.
        + eapply tccall_unreset_preserv_rst; eauto. discriminate.
    Qed.

    (** Pointwise augmentation of the Obc blocks with the reset-method
        constraints of the instances they own. *)

    Fixpoint zip_app (bs: list (list constraint)) (es: list (list ident))
      : list (list constraint) :=
      match bs, es with
      | b :: bs', e :: es' =>
          (b ++ map (fun ty => ([rst_ty], [ty])) e) :: zip_app bs' es'
      | _, _ => []
      end.

    Lemma zip_app_covers_blocks:
      forall bs es c,
        List.length bs = List.length es ->
        List.In c (List.concat bs) ->
        List.In c (List.concat (zip_app bs es)).
    Proof.
      induction bs as [|b bs IH]; intros es c Hlen Hin; simpl in *.
      - contradiction.
      - destruct es as [|e es]; [discriminate|].
        simpl in Hlen. simpl.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app.
        + left. apply in_or_app. now left.
        + right. eapply IH; eauto.
    Qed.

    Lemma zip_app_covers_extras:
      forall bs es ty,
        List.length bs = List.length es ->
        List.In ty (List.concat es) ->
        List.In ([rst_ty], [ty]) (List.concat (zip_app bs es)).
    Proof.
      induction bs as [|b bs IH]; intros es ty Hlen Hin; simpl in *.
      - destruct es; [contradiction|discriminate].
      - destruct es as [|e es]; [discriminate|].
        simpl in Hlen, Hin. simpl.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app.
        + left. apply in_or_app. right.
          apply in_map_iff. exists ty. split; [reflexivity|exact Hin].
        + right. eapply IH; eauto.
    Qed.

    Lemma zip_app_Forall2_scoped:
      forall scope bs es,
        Forall2 (fun b e => constraints_scoped (scope ++ e)
                              (b ++ map (fun ty => ([rst_ty], [ty])) e)) bs es ->
        Forall2 (fun t e => constraints_scoped (scope ++ e) t) (zip_app bs es) es.
    Proof.
      intros scope bs es Hall.
      induction Hall as [|b e bs es Hbe Hall IH]; simpl; constructor; auto.
    Qed.

    Lemma tcs_blocks_preserv_aug:
      forall scope vars memset clkvars tcs nblocks sblocks extras,
        Signature_consistent_obc_full G1 G2 ->
        Forall (tc_preserv_hyps_aug scope vars) tcs ->
        Forall2 (fun tc nblk =>
                   exists sa sb,
                     SECSTCTYPING.generate_trconstr_constraint G1 env reset_env
                       clk_ty rst_ty tc sa = OK (nblk, sb)) tcs nblocks ->
        Forall2 (fun tc sblk =>
                   exists sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (sblk, sb)) tcs sblocks ->
        Forall2 (fun tc e => tc_obc_extras tc = Some e) tcs extras ->
        Forall2 (preserves_on scope) nblocks (zip_app sblocks extras).
    Proof.
      intros scope vars memset clkvars tcs nblocks sblocks extras Hcons Hhyps Hn Hs He.
      revert nblocks sblocks extras Hn Hs He.
      induction tcs as [|tc tcs IH]; intros nblocks sblocks extras Hn Hs He.
      - inversion Hn; inversion Hs; inversion He; subst. simpl. constructor.
      - inversion Hn as [|tc1 nblk tcs1 nbs Hnb Hn']; subst.
        inversion Hs as [|tc2 sblk tcs2 sbs Hsb Hs']; subst.
        inversion He as [|tc3 e tcs3 es Hee He']; subst.
        inversion Hhyps as [|tc4 tcs4 Hh Hhyps']; subst.
        simpl. constructor.
        + destruct Hnb as (sa & sb & Hnb). destruct Hsb as (sc & sd & Hsb).
          eapply tc_preserv_aug; eauto.
        + eapply IH; eauto.
    Qed.

    (** Whole-body preservation against a target that also carries the
        reset-method constraints of every instance the body owns. *)

    Lemma tcs_preserv_aug:
      forall scope vars memset clkvars tcs extras nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        Forall (tc_preserv_hyps_aug scope vars) tcs ->
        tcs_obc_extras tcs = Some extras ->
        NoDup (List.concat extras) ->
        (forall x, List.In x (List.concat extras) -> ~ List.In x scope) ->
        Forall2 (fun tc e =>
                   forall blk sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
                     constraints_scoped (scope ++ e)
                       (blk ++ map (fun ty => ([rst_ty], [ty])) e))
                tcs extras ->
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty tcs st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tcs memset clkvars tcs) st2 = OK (sconst, st2') ->
        exists tgt,
          (forall c, List.In c sconst -> List.In c tgt)
          /\ (forall ty, List.In ty (List.concat extras) ->
                         List.In ([rst_ty], [ty]) tgt)
          /\ preserves_on scope nconst tgt.
    Proof.
      intros scope vars memset clkvars tcs extras nconst sconst st1 st1' st2 st2'
             Hcons Hhyps Hextras Hnd Hfresh Hsc Hstc Hobc.
      destruct (SECSTCTYPING.generate_trconstrs_constraints_blocks
                  G1 env reset_env clk_ty rst_ty tcs nconst st1 st1' Hstc)
        as (nblocks & Hnconst & Hnall).
      rewrite translate_tcs_fold_right in Hobc.
      destruct (generate_fold_right_Comp memset clkvars [clk_ty] (rev tcs)
                  sconst st2 st2' Hobc)
        as (sblocks & Hsconst & Hsall).
      subst nconst sconst.
      pose proof (tcs_obc_extras_Forall2 _ _ Hextras) as Hextall.
      apply Forall2_rev in Hnall.
      apply Forall2_rev in Hextall.
      apply Forall2_rev in Hsc.
      assert (Hhypsrev : Forall (tc_preserv_hyps_aug scope vars) (rev tcs))
        by (apply Forall_rev; exact Hhyps).
      assert (Hpres : Forall2 (preserves_on scope) (rev nblocks)
                        (zip_app sblocks (rev extras))).
      { eapply tcs_blocks_preserv_aug; eauto. }
      assert (Hscoped : Forall2 (fun t e => constraints_scoped (scope ++ e) t)
                          (zip_app sblocks (rev extras)) (rev extras)).
      { apply zip_app_Forall2_scoped.
        eapply (Forall2_combine _ _ _ (rev tcs) sblocks (rev extras) Hsall Hsc).
        intros tc sblk e (sa & sb & Hs) He. eapply He; eauto. }
      assert (Hndrev : NoDup (List.concat (rev extras))).
      { eapply Permutation_NoDup;
          [symmetry; apply concat_rev_Permutation|exact Hnd]. }
      assert (Hfreshrev : forall x, List.In x (List.concat (rev extras)) ->
                                    ~ List.In x scope).
      { intros x Hin. apply Hfresh.
        eapply Permutation_in; [apply concat_rev_Permutation|exact Hin]. }
      assert (Hlen : List.length sblocks = List.length (rev extras)).
      { eapply Forall2_length. eapply (Forall2_combine _ _ _ (rev tcs) sblocks (rev extras)
                                         Hsall Hextall).
        intros; exact I. }
      exists (List.concat (zip_app sblocks (rev extras))).
      repeat split.
      - intros c Hin. eapply zip_app_covers_blocks; eauto.
      - intros ty Hin. eapply zip_app_covers_extras; eauto.
        eapply Permutation_in; [symmetry; apply concat_rev_Permutation|exact Hin].
      - eapply preserves_on_Permutation;
          [apply concat_rev_Permutation|reflexivity|].
        eapply preserves_on_concat_list; eauto.
    Qed.

    (** [translate_tcs] emits the per-trconstr blocks in reverse order,
        so the Obc constraint list is a permutation of the STC one taken
        blockwise.  [extras] names, per trconstr, the identifiers that
        occur only on the Obc side (the callee instance state types);
        they must be distinct and outside the shared scope. *)

    Lemma tcs_preserv:
      forall scope vars memset clkvars tcs extras nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc G1 G2 ->
        Forall (tc_preserv_hyps scope vars) tcs ->
        NoDup (List.concat extras) ->
        (forall x, In x (List.concat extras) -> ~ In x scope) ->
        Forall2 (fun tc e =>
                   forall blk sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
                     constraints_scoped (scope ++ e) blk)
                tcs extras ->
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty tcs st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tcs memset clkvars tcs) st2 = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope vars memset clkvars tcs extras nconst sconst st1 st1' st2 st2'
             Hcons Hhyps Hnd Hfresh Hsc Hstc Hobc.
      (* decompose both sides into per-trconstr blocks *)
      destruct (SECSTCTYPING.generate_trconstrs_constraints_blocks
                  G1 env reset_env clk_ty rst_ty tcs nconst st1 st1' Hstc)
        as (nblocks & Hnconst & Hnall).
      rewrite translate_tcs_fold_right in Hobc.
      destruct (generate_fold_right_Comp memset clkvars [clk_ty] (rev tcs)
                  sconst st2 st2' Hobc)
        as (sblocks & Hsconst & Hsall).
      subst nconst sconst.
      (* the Obc blocks follow [rev tcs]; reverse the STC pairing to match *)
      apply Forall2_rev in Hnall.
      apply Forall2_rev in Hsc.
      assert (Hhypsrev : Forall (tc_preserv_hyps scope vars) (rev tcs))
        by (apply Forall_rev; exact Hhyps).
      assert (Hpres : Forall2 (preserves_on scope) (rev nblocks) sblocks).
      { eapply (Forall2_combine_with _ _ _ _ (rev tcs) (rev nblocks) sblocks
                  Hnall Hsall Hhypsrev).
        intros tc nblk sblk Hhyp (sa & sb & Hn) (sc & sd & Hs).
        eapply tc_preserv; eauto. }
      assert (Hscoped : Forall2 (fun t e => constraints_scoped (scope ++ e) t)
                          sblocks (rev extras)).
      { eapply (Forall2_combine _ _ _ (rev tcs) sblocks (rev extras) Hsall Hsc).
        intros tc sblk e (sa & sb & Hs) He.
        eapply He; eauto. }
      (* the extras are the same set, up to the same reordering *)
      assert (Hndrev : NoDup (List.concat (rev extras))).
      { eapply Permutation_NoDup;
          [symmetry; apply concat_rev_Permutation|exact Hnd]. }
      assert (Hfreshrev : forall x, In x (List.concat (rev extras)) -> ~ In x scope).
      { intros x Hin. apply Hfresh.
        eapply Permutation_in; [apply concat_rev_Permutation|exact Hin]. }
      eapply preserves_on_Permutation;
        [apply concat_rev_Permutation|reflexivity|].
      eapply preserves_on_concat_list; eauto.
    Qed.

    (** ** The reset method

        [translate_reset] initialises every memory and then resets every
        instance.  Neither statement has an STC counterpart, so its
        constraints are *discharged* rather than preserved: each one has
        the shape [rst_ty ⊑ ty], and for every such [ty] the STC side
        already carries a constraint with [rst_ty] in its source and the
        same target — the [TcNext] of that last, or the [TcReset] of that
        instance.  Both are therefore entailed under the *same*
        valuation, with no witness change. *)

    Lemma reset_constraint_entailed:
      forall dlt src ty,
        In rst_ty src ->
        constraintSatisfiable dlt (src, [ty]) ->
        constraintSatisfiable dlt ([rst_ty], [ty]).
    Proof.
      intros dlt src ty Hin Hsat.
      unfold constraintSatisfiable, satisfiable in *.
      eapply Lat.order_trans; [|exact Hsat].
      apply hm_ext_incl.
      intros z Hz. simpl in Hz. destruct Hz as [Heq|[]]. subst z. exact Hin.
    Qed.

    (** The reset-method constraints whose target is shared with the STC
        side — the memories, and the instances the system resets — are
        satisfied by *any* valuation agreeing with the source one on the
        scope.  They therefore need no witness of their own and can be
        appended to the whole-body result. *)

    Lemma reset_targets_satisfied:
      forall scope dlt dlt' nconst tys,
        listSatisfiable dlt nconst ->
        agree_on scope dlt dlt' ->
        List.In rst_ty scope ->
        Forall (fun ty =>
                  List.In ty scope
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               tys ->
        listSatisfiable dlt' (map (fun ty => ([rst_ty], [ty])) tys).
    Proof.
      intros scope dlt dlt' nconst tys Hsat Hagree Hrstin Hall.
      unfold listSatisfiable. apply Forall_map.
      eapply Forall_impl; [|exact Hall].
      intros ty (Htyin & src & Hinsrc & Hrstsrc).
      eapply constraintSatisfiable_ext with (scope := scope) (dlt1 := dlt).
      - unfold constraint_scoped, SymTypes.constraint_scope. simpl.
        intros z Hz. destruct Hz as [Heq|[Heq|[]]]; subst z; assumption.
      - exact Hagree.
      - eapply reset_constraint_entailed; [exact Hrstsrc|].
        eapply Forall_forall; [exact Hsat|exact Hinsrc].
    Qed.

    (** The reset method's memory initialisations target exactly the
        system's lasts, and each of those is defined by a [TcNext] whose
        source contains [rst_ty]. *)

    Lemma reset_mems_targets:
      forall s scope nconst st st' mtys,
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty
          s.(SynStc.s_tcs) st = OK (nconst, st') ->
        Forall2 (fun xc ty => Env.find (fst xc) env = Some ty) s.(SynStc.s_lasts) mtys ->
        (forall ty, List.In ty mtys -> List.In ty scope) ->
        Forall (fun ty =>
                  List.In ty scope
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               mtys.
    Proof.
      intros s scope nconst st st' mtys Hgen Hall Hscope.
      apply Forall_forall. intros ty Hin.
      split; [now apply Hscope|].
      destruct (Forall2_in_right _ _ _ _ Hall Hin) as (xc & Hinxc & Hfind).
      eapply SECSTCTYPING.generate_trconstrs_constraints_last_source;
        [exact Hgen| |exact Hfind].
      rewrite <- (SynStc.s_lasts_in_tcs s).
      now apply in_map with (f := fst) in Hinxc.
    Qed.

    (** Likewise the instance resets, for the instances the system
        actually resets. *)

    Lemma reset_insts_targets:
      forall s scope nconst st st' (insts: list (ident * ident)) itys,
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty
          s.(SynStc.s_tcs) st = OK (nconst, st') ->
        Forall2 (fun oc ty => Env.find (fst oc) reset_env = Some ty) insts itys ->
        (forall oc, List.In oc insts ->
                    List.In (fst oc) (map fst (resets_of s.(SynStc.s_tcs)))) ->
        (forall ty, List.In ty itys -> List.In ty scope) ->
        Forall (fun ty =>
                  List.In ty scope
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               itys.
    Proof.
      intros s scope nconst st st' insts itys Hgen Hall Hreset Hscope.
      apply Forall_forall. intros ty Hin.
      split; [now apply Hscope|].
      destruct (Forall2_in_right _ _ _ _ Hall Hin) as (oc & Hinoc & Hfind).
      eapply SECSTCTYPING.generate_trconstrs_constraints_reset_source;
        [exact Hgen|apply Hreset; exact Hinoc|exact Hfind].
    Qed.

    (** Appending the reset method's shared-target constraints to a
        preservation result is free: they hold under any valuation that
        agrees with the source one on the scope, so no witness changes. *)

    Lemma preserves_on_app_reset_shared:
      forall scope c t tys,
        List.In rst_ty scope ->
        Forall (fun ty =>
                  List.In ty scope
                  /\ exists src, List.In (src, [ty]) c /\ List.In rst_ty src)
               tys ->
        preserves_on scope c t ->
        preserves_on scope c (t ++ map (fun ty => ([rst_ty], [ty])) tys).
    Proof.
      intros scope c t tys Hrst Hall Hp.
      eapply preserves_on_app_scope_entailed; [exact Hp|].
      intros dlt dlt' Hsat Hagree.
      eapply reset_targets_satisfied; eauto.
    Qed.

    Lemma generate_reset_mems_blocks:
      forall (mems: list (ident * (const * clock))) cns st st',
        generate_stmt_constraints G2 env reset_env rst_ty []
          (reset_mems mems) st = OK (cns, st') ->
        exists tys,
          Forall2 (fun xc ty => Env.find (fst xc) env = Some ty) mems tys
          /\ cns = map (fun ty => ([rst_ty], [ty])) tys.
    Proof.
      intros mems cns st st' Hgen.
      unfold reset_mems in Hgen.
      destruct (generate_fold_left_Comp G2 env reset_env rst_ty
                  (fun xc => SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc))))
                  mems SynObc.Skip [] cns st st' Hgen)
        as (cacc & blocks & sa & Hacc & Hcns & Hall).
      simpl in Hacc. unfold ret in Hacc. inversion Hacc; subst cacc sa.
      simpl in Hcns. subst cns.
      clear Hgen Hacc.
      induction Hall as [|xc blk mems blocks Hblk Hall IH]; simpl.
      - exists []. split; [constructor|reflexivity].
      - destruct Hblk as (s1 & s2 & Hblk).
        simpl in Hblk.
        eapply sec_bind_inv in Hblk as (ety & sa & Hety & Hblk).
        eapply sec_bind_inv in Hblk as (xty & sb & Hxty & Hret).
        assert (Hfind : Env.find (fst xc) env = Some xty).
        { unfold SC.find_env in Hxty.
          destruct (Env.find (fst xc) env) as [v|] eqn:Hf; try discriminate.
          unfold ret in Hxty. congruence. }
        assert (Hety0 : ety = []).
        { unfold ret in Hety. congruence. }
        unfold ret in Hret. inversion Hret; subst blk.
        destruct IH as (tys & Htys & Hcns).
        exists (xty :: tys). split.
        + constructor; [exact Hfind|exact Htys].
        + simpl. rewrite Hcns, Hety0.
          repeat rewrite MergeFacts.merge_nil.
          reflexivity.
    Qed.

    Lemma generate_reset_insts_blocks:
      forall (insts: list (ident * ident)) cns st st',
        generate_stmt_constraints G2 env reset_env rst_ty []
          (reset_insts insts) st = OK (cns, st') ->
        exists tys,
          Forall2 (fun oc ty => Env.find (fst oc) reset_env = Some ty) insts tys
          /\ cns = map (fun ty => ([rst_ty], [ty])) tys.
    Proof.
      intros insts cns st st' Hgen.
      unfold reset_insts in Hgen.
      destruct (generate_fold_left_Comp G2 env reset_env rst_ty
                  (fun oc => SynObc.Call [] (snd oc) (fst oc) reset [])
                  insts SynObc.Skip [] cns st st' Hgen)
        as (cacc & blocks & sa & Hacc & Hcns & Hall).
      simpl in Hacc. unfold ret in Hacc. inversion Hacc; subst cacc sa.
      simpl in Hcns. subst cns.
      clear Hgen Hacc.
      induction Hall as [|oc blk insts blocks Hblk Hall IH]; simpl.
      - exists []. split; [constructor|reflexivity].
      - destruct Hblk as (s1 & s2 & Hblk).
        simpl in Hblk.
        rewrite ident_eqb_refl in Hblk.
        eapply sec_bind_inv in Hblk as (sty & sa & Hsty & Hret).
        assert (Hfind : Env.find (fst oc) reset_env = Some sty).
        { unfold SC.find_env in Hsty.
          destruct (Env.find (fst oc) reset_env) as [v|] eqn:Hf; try discriminate.
          unfold ret in Hsty. congruence. }
        unfold ret in Hret. inversion Hret; subst blk.
        destruct IH as (tys & Htys & Hcns).
        exists (sty :: tys). split.
        + constructor; [exact Hfind|exact Htys].
        + simpl. rewrite Hcns.
          repeat rewrite MergeFacts.merge_nil.
          reflexivity.
    Qed.

    Lemma generate_translate_reset_blocks:
      forall s cns st st',
        generate_stmt_constraints G2 env reset_env rst_ty []
          (translate_reset s) st = OK (cns, st') ->
        exists mtys itys,
          Forall2 (fun xc ty => Env.find (fst xc) env = Some ty) s.(SynStc.s_lasts) mtys
          /\ Forall2 (fun oc ty => Env.find (fst oc) reset_env = Some ty) s.(SynStc.s_subs) itys
          /\ cns = map (fun ty => ([rst_ty], [ty])) (mtys ++ itys).
    Proof.
      intros s cns st st' Hgen.
      unfold translate_reset in Hgen. simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      destruct (generate_reset_mems_blocks _ _ _ _ Hc1) as (mtys & Hmtys & Hm).
      destruct (generate_reset_insts_blocks _ _ _ _ Hc2) as (itys & Hitys & Hi).
      exists mtys, itys. repeat split; [exact Hmtys|exact Hitys|].
      rewrite Hm, Hi, map_app. reflexivity.
    Qed.

    (** ** Free names of a translated trconstr

        The translation invents no variables: [Control] re-reads the
        clock's variables, [translate_exp] only ever drops [Ewhen]
        guards, and the assigned names are the trconstr's own targets.
        So every name free in the translation is free or defined in the
        source, which is what the Obc scopedness theorem needs. *)

    Lemma translate_exp_free:
      forall memset e x,
        List.In x (SECOBCTYPING.exp_free (translate_exp memset e)) ->
        CEIsF.Is_free_in_exp x e.
    Proof.
      intros memset e. induction e; intros y Hin; simpl in Hin.
      - contradiction.
      - unfold tovar in Hin. destruct (PS.mem i memset); simpl in Hin;
          destruct Hin as [Heq|[]]; subst y; constructor.
      - constructor. now apply IHe.
      - constructor. now apply IHe.
      - apply in_app_iff in Hin as [Hin|Hin]; constructor;
          [left; now apply IHe1|right; now apply IHe2].
    Qed.

    Lemma translate_arg_free:
      forall memset clkvars ck e x,
        List.In x (SECOBCTYPING.exp_free (translate_arg memset clkvars ck e)) ->
        CEIsF.Is_free_in_exp x e.
    Proof.
      intros memset clkvars ck e x Hin.
      destruct e.
      - exact (translate_exp_free memset _ x Hin).
      - simpl in Hin.
        destruct (var_on_base_clock memset clkvars ck i) eqn:Hb; simpl in Hin.
        + destruct Hin as [Heq|[]]; subst x. constructor.
        + destruct (PS.mem i memset); simpl in Hin;
            destruct Hin as [Heq|[]]; subst x; constructor.
      - exact (translate_exp_free memset _ x Hin).
      - exact (translate_exp_free memset _ x Hin).
      - exact (translate_exp_free memset _ x Hin).
    Qed.

    Lemma translate_cexp_free:
      forall memset y ce x,
        List.In x (SECOBCTYPING.stmt_free (translate_cexp memset y ce)) ->
        x = y \/ CEIsF.Is_free_in_cexp x ce.
    Proof.
      intros memset y ce. induction ce; intros z Hin; simpl in Hin.
      - apply in_app_iff in Hin as [Hin|Hin].
        + right. unfold bool_var, tovar in Hin.
          destruct (PS.mem i memset); simpl in Hin;
            destruct Hin as [Heq|[]]; subst z; constructor.
        + apply in_app_iff in Hin as [Hin|Hin].
          * destruct (IHce1 _ Hin) as [Heq|Hfree]; [now left|].
            right. now apply FreeEmerge_true.
          * destruct (IHce2 _ Hin) as [Heq|Hfree]; [now left|].
            right. now apply FreeEmerge_false.
      - apply in_app_iff in Hin as [Hin|Hin].
        + right. apply FreeEite_cond.
          exact (translate_exp_free memset _ z Hin).
        + apply in_app_iff in Hin as [Hin|Hin].
          * destruct (IHce1 _ Hin) as [Heq|Hfree]; [now left|].
            right. now apply FreeEite_true.
          * destruct (IHce2 _ Hin) as [Heq|Hfree]; [now left|].
            right. now apply FreeEite_false.
      - destruct Hin as [Heq|Hin]; [now left|].
        right. constructor. exact (translate_exp_free memset _ z Hin).
    Qed.

    Lemma stmt_free_Control:
      forall memset ck s x,
        List.In x (SECOBCTYPING.stmt_free (Control memset ck s)) ->
        Is_free_in_clock x ck \/ List.In x (SECOBCTYPING.stmt_free s).
    Proof.
      intros memset ck. induction ck as [|ck IH i b]; intros s x Hin; simpl in Hin.
      - now right.
      - destruct b; simpl in Hin.
        + destruct (IH _ _ Hin) as [Hck|Hs]; [now left; right|].
          simpl in Hs. apply in_app_iff in Hs as [Hs|Hs].
          * left. unfold bool_var, tovar in Hs.
            destruct (PS.mem i memset); simpl in Hs;
              destruct Hs as [Heq|[]]; subst x; constructor.
          * rewrite app_nil_r in Hs. now right.
        + destruct (IH _ _ Hin) as [Hck|Hs]; [now left; right|].
          simpl in Hs. apply in_app_iff in Hs as [Hs|Hs].
          * left. unfold bool_var, tovar in Hs.
            destruct (PS.mem i memset); simpl in Hs;
              destruct Hs as [Heq|[]]; subst x; constructor.
          * simpl in Hs. now right.
    Qed.

    Lemma translate_tc_free:
      forall memset clkvars tc x,
        List.In x (SECOBCTYPING.stmt_free (translate_tc memset clkvars tc)) ->
        IsFStc.Is_free_in_tc x tc \/ List.In x (DefStc.defined_tc tc).
    Proof.
      intros memset clkvars tc x Hin.
      destruct tc as [y ck ce|y ck e|i ck f|i ys ck b f es]; simpl in Hin.
      - destruct (stmt_free_Control _ _ _ _ Hin) as [Hck|Hs].
        + left. constructor. now apply FreeCAexp2.
        + destruct (translate_cexp_free _ _ _ _ Hs) as [Heq|Hfree].
          * subst x. right. simpl. now left.
          * left. constructor. now apply FreeCAexp1.
      - destruct (stmt_free_Control _ _ _ _ Hin) as [Hck|Hs].
        + left. constructor. now apply freeAexp2.
        + simpl in Hs. destruct Hs as [Heq|Hs].
          * subst x. right. simpl. now left.
          * left. constructor. apply freeAexp1.
            exact (translate_exp_free memset _ x Hs).
      - destruct (stmt_free_Control _ _ _ _ Hin) as [Hck|Hs].
        + left. now constructor.
        + simpl in Hs. contradiction.
      - destruct (stmt_free_Control _ _ _ _ Hin) as [Hck|Hs].
        + left. constructor. now apply freeAexps2.
        + simpl in Hs. apply in_app_iff in Hs as [Hs|Hs].
          * right. simpl. exact Hs.
          * left. constructor. apply freeAexps1.
            apply in_flat_map in Hs as (oe & Hinoe & Hfree).
            apply in_map_iff in Hinoe as (e0 & Heq & Hine0).
            subst oe.
            apply Exists_exists. exists e0. split; [exact Hine0|].
            exact (translate_arg_free memset clkvars ck e0 x Hfree).
    Qed.

    (** ** The raw scope

        Everything the two constraint sets share: the signature scope,
        the system's locals and lasts, and the instances it resets.  The
        instances it does not reset are deliberately outside, since they
        are the per-block extras. *)

    Definition raw_scope (inp out slocals slasts rids: list ident) : list ident :=
      inp ++ out ++ slocals ++ slasts ++ rids ++ [clk_ty; rst_ty].

    Lemma rst_ty_in_raw_scope:
      forall inp out slocals slasts rids,
        List.In rst_ty (raw_scope inp out slocals slasts rids).
    Proof.
      intros. unfold raw_scope.
      repeat (apply in_or_app; right). simpl. now right; left.
    Qed.

    Lemma sig_scope_in_raw_scope:
      forall inp out slocals slasts rids x,
        List.In x (inp ++ out ++ [clk_ty; rst_ty]) ->
        List.In x (raw_scope inp out slocals slasts rids).
    Proof.
      intros inp out slocals slasts rids x Hin.
      unfold raw_scope.
      apply in_app_iff in Hin as [Hin|Hin]; [now apply in_or_app; left|].
      apply in_or_app; right.
      apply in_app_iff in Hin as [Hin|Hin]; [now apply in_or_app; left|].
      apply in_or_app; right.
      repeat (apply in_or_app; right). exact Hin.
    Qed.

    Lemma unreset_call_insts_step:
      forall tcs i,
        List.In i (unreset_call_insts tcs) ->
        Step_with_reset_in i false tcs.
    Proof.
      induction tcs as [|tc tcs IH]; intros i Hin; [inversion Hin|].
      destruct tc as [x ck ce|x ck e|x ck f|o xs ck [|] g es]; simpl in Hin.
      - right. now apply IH.
      - right. now apply IH.
      - right. now apply IH.
      - right. now apply IH.
      - destruct Hin as [Heq|Hin].
        + subst o. left. constructor.
        + right. now apply IH.
    Qed.

    (** An instance the body never resets has a state type distinct from
        every name the STC side can see: it carries the [sec_reset]
        prefix, so it is none of the [sec] names, and injectivity plus
        [reset_consistency] separate it from the reset instances. *)

    Lemma extras_fresh_raw_scope:
      forall tcs extras rids inp out slocals slasts ty,
        env_injective reset_env ->
        (forall x ty', Env.find x reset_env = Some ty' ->
                       exists n, ty' = Ids.gensym Ids.sec_reset n) ->
        (forall ty', List.In ty' (inp ++ out ++ slocals ++ slasts
                                    ++ [clk_ty; rst_ty]) ->
                     exists n, ty' = Ids.gensym Ids.sec n) ->
        get_mappings (map fst (resets_of tcs)) reset_env = Some rids ->
        reset_consistency tcs ->
        tcs_obc_extras tcs = Some extras ->
        List.In ty (List.concat extras) ->
        ~ List.In ty (raw_scope inp out slocals slasts rids).
    Proof.
      intros tcs extras rids inp out slocals slasts ty
             Hinj Hrange Hsec Hrids Hcons Hextras Hin Hscope.
      pose proof (tcs_obc_extras_concat _ _ Hextras) as Hconcat.
      destruct (get_mappings_In _ _ _ _ Hconcat Hin) as (i & Hini & Hfindi).
      destruct (Hrange _ _ Hfindi) as (n1 & Hn1).
      (* the name is a [sec_reset] gensym, so it is none of the [sec] ones *)
      assert (Hnotsec : ~ List.In ty (inp ++ out ++ slocals ++ slasts
                                        ++ [clk_ty; rst_ty])).
      { intro Hin'. destruct (Hsec _ Hin') as (n2 & Hn2).
        rewrite Hn1 in Hn2. apply gensym_injective in Hn2 as [Hpref _].
        symmetry in Hpref. exact (Ids.sec_neq_sec_reset Hpref). }
      (* and it is not one of the reset instances either *)
      assert (Hnotrid : ~ List.In ty rids).
      { intro Hinr.
        destruct (get_mappings_In _ _ _ _ Hrids Hinr) as (r & Hinr' & Hfindr).
        assert (i = r) by (eapply Hinj; eauto). subst r.
        eapply (Hcons i false); [now apply unreset_call_insts_step|].
        now apply SECSTCTYPING.resets_of_Reset_in. }
      unfold raw_scope in Hscope.
      apply in_app_iff in Hscope as [H1|Hscope].
      { apply Hnotsec, in_or_app; now left. }
      apply in_app_iff in Hscope as [H2|Hscope].
      { apply Hnotsec, in_or_app; right; apply in_or_app; now left. }
      apply in_app_iff in Hscope as [H3|Hscope].
      { apply Hnotsec, in_or_app; right; apply in_or_app; right;
          apply in_or_app; now left. }
      apply in_app_iff in Hscope as [H4|Hscope].
      { apply Hnotsec, in_or_app; right; apply in_or_app; right;
          apply in_or_app; right; apply in_or_app; now left. }
      apply in_app_iff in Hscope as [H5|Hscope].
      { exact (Hnotrid H5). }
      apply Hnotsec, in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; right. exact Hscope.
    Qed.

    (** ** Per-block target scopedness

        The Obc scopedness theorem needs the free names of the translated
        statement to have scoped types; [translate_tc_free] reduces that
        to the source trconstr's own free and defined names. *)

    Lemma translated_tc_constraints_scoped:
      forall scope memset clkvars tc e blk sa sb,
        SIG.secglobal_scoped G2 ->
        List.In clk_ty scope ->
        List.In rst_ty scope ->
        (forall x, IsFStc.Is_free_in_tc x tc \/ List.In x (DefStc.defined_tc tc) ->
                   exists ty, Env.find x env = Some ty /\ List.In ty scope) ->
        (forall o sty,
            List.In o (SECOBCTYPING.stmt_state_keys
                         (translate_tc memset clkvars tc)) ->
            Env.find o reset_env = Some sty ->
            List.In sty (scope ++ e)) ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
        constraints_scoped (scope ++ e)
          (blk ++ map (fun ty => ([rst_ty], [ty])) e).
    Proof.
      intros scope memset clkvars tc e blk sa sb
             Hglob Hclk Hrst Hnames Hstate Hgen.
      unfold constraints_scoped. apply Forall_app. split.
      - eapply SECOBCTYPING.generate_stmt_constraints_scoped_on_keys;
          [exact Hglob| | | |..|exact Hgen].
        + (* free names *)
          intros x Hin.
          destruct (translate_tc_free _ _ _ _ Hin) as [Hfree|Hdef];
            (destruct (Hnames x ltac:(auto)) as (ty & Hfind & Hty);
             exists ty; split; [exact Hfind|apply in_or_app; now left]).
        + (* the entry pc *)
          intros z Hz. simpl in Hz. destruct Hz as [Heq|[]]; subst z.
          apply in_or_app; now left.
        + apply in_or_app; now left.
        + intros o sty st0 st1 Hino Hfind.
          unfold SC.find_env in Hfind.
          destruct (Env.find o reset_env) as [v|] eqn:Hv; try discriminate.
          unfold ret in Hfind. inversion Hfind; subst v st1.
          eapply Hstate; eauto.
      - apply Forall_map. apply Forall_forall. intros ty Hty.
        unfold constraint_scoped, SymTypes.constraint_scope. simpl.
        intros z Hz. destruct Hz as [Heq|[Heq|[]]]; subst z.
        + apply in_or_app; now left.
        + apply in_or_app; now right.
    Qed.

    (** ** Shape of the translated class

        The Obc signature generator reads the step method's interface and
        the class memories; each is the STC system's own list up to
        [idty] or a type change, so the two generators compute the same
        security-type lists from the same environment. *)

    Lemma get_mappings_from_node_map_fst:
      forall A B (xs: list (ident * A)) (ys: list (ident * B)) e tys,
        map fst xs = map fst ys ->
        get_mappings_from_node xs e = Some tys ->
        get_mappings_from_node ys e = Some tys.
    Proof.
      intros A B xs ys e tys Hmap Hget.
      apply get_mappings_from_node_eq in Hget.
      rewrite Hmap in Hget.
      revert tys Hget. clear Hmap.
      induction ys as [|[y a] ys IH]; intros tys Hget; simpl in *.
      - exact Hget.
      - destruct (Env.find y e) as [ty|]; try discriminate.
        destruct (get_mappings (map fst ys) e) as [tys'|] eqn:Hys;
          try discriminate.
        inversion Hget; subst tys.
        now rewrite (IH tys' Logic.eq_refl).
    Qed.

    Lemma translated_class_step_in:
      forall s, map fst (m_in (step_method s)) = map fst s.(SynStc.s_in).
    Proof. intro s. simpl. apply map_fst_idty. Qed.

    Lemma translated_class_step_out:
      forall s, map fst (m_out (step_method s)) = map fst s.(SynStc.s_out).
    Proof. intro s. simpl. apply map_fst_idty. Qed.

    Lemma translated_class_step_vars:
      forall s, map fst (m_vars (step_method s)) = map fst s.(SynStc.s_vars).
    Proof. intro s. simpl. apply map_fst_idty. Qed.

    Lemma translated_class_mems:
      forall s, map fst (c_mems (translate_system s)) = map fst s.(SynStc.s_lasts).
    Proof. intro s. simpl. now rewrite map_map. Qed.

    Lemma translated_class_objs:
      forall s, c_objs (translate_system s) = s.(SynStc.s_subs).
    Proof. reflexivity. Qed.

    (** Every instance the class resets is one the system either resets
        (so its type is among [rids]) or only steps (so its type is a
        per-block extra).  [reset_consistency] makes the split
        exhaustive, and is applied once, to the whole list. *)

    Lemma calls_of_step_or_unreset:
      forall tcs i,
        List.In i (map fst (calls_of tcs)) ->
        Step_with_reset_in i true tcs \/ List.In i (unreset_call_insts tcs).
    Proof.
      induction tcs as [|tc tcs IH]; intros i Hin; [inversion Hin|].
      destruct tc as [x ck ce|x ck e|x ck f|o xs ck [|] g es]; simpl in Hin.
      - destruct (IH i Hin) as [H|H]; [left; now right|right; exact H].
      - destruct (IH i Hin) as [H|H]; [left; now right|right; exact H].
      - destruct (IH i Hin) as [H|H]; [left; now right|right; exact H].
      - destruct Hin as [Heq|Hin].
        + subst o. left. left. constructor.
        + destruct (IH i Hin) as [H|H]; [left; now right|right; exact H].
      - destruct Hin as [Heq|Hin].
        + subst o. right. simpl. now left.
        + destruct (IH i Hin) as [H|H];
            [left; now right|right; simpl; now right].
    Qed.

    Lemma calls_of_reset_or_unreset:
      forall tcs i,
        reset_consistency tcs ->
        List.In i (map fst (calls_of tcs)) ->
        List.In i (map fst (resets_of tcs)) \/ List.In i (unreset_call_insts tcs).
    Proof.
      intros tcs i Hcons Hin.
      destruct (calls_of_step_or_unreset _ _ Hin) as [Hstep|Hun]; [|now right].
      left. apply SECSTCTYPING.Reset_in_resets_of.
      exact (Hcons i true Hstep).
    Qed.

    Lemma unreset_call_insts_incl_calls:
      forall tcs i,
        List.In i (unreset_call_insts tcs) ->
        List.In i (map fst (calls_of tcs)).
    Proof.
      induction tcs as [|tc tcs IH]; intros i Hin; [inversion Hin|].
      destruct tc as [x ck ce|x ck e|x ck f|o xs ck [|] g es]; simpl in Hin; simpl.
      - now apply IH.
      - now apply IH.
      - now apply IH.
      - right. now apply IH.
      - destruct Hin as [Heq|Hin]; [now left|right; now apply IH].
    Qed.

    Lemma unreset_call_insts_nodup:
      forall tcs,
        NoDup (map fst (calls_of tcs)) ->
        NoDup (unreset_call_insts tcs).
    Proof.
      induction tcs as [|tc tcs IH]; intros Hnd; simpl; [constructor|].
      destruct tc as [x ck ce|x ck e|x ck f|o xs ck [|] g es]; simpl in Hnd; simpl.
      - now apply IH.
      - now apply IH.
      - now apply IH.
      - apply IH. now inversion Hnd.
      - inversion Hnd as [|? ? Hnin Hnd']; subst.
        constructor; [|now apply IH].
        intro Hin. apply Hnin. now apply unreset_call_insts_incl_calls.
    Qed.

    Lemma get_mappings_incl_Some:
      forall xs ys e tys,
        (forall x, List.In x xs -> List.In x ys) ->
        get_mappings ys e = Some tys ->
        exists txs, get_mappings xs e = Some txs.
    Proof.
      intros xs ys e tys Hincl Hys.
      apply get_mappings_Some_iff.
      apply Forall_forall. intros x Hin.
      assert (Hiny : List.In x ys) by now apply Hincl.
      destruct (get_mappings_in _ _ _ _ Hiny Hys) as (ty & Hfind & _).
      eauto.
    Qed.

    Lemma tcs_obc_extras_exists:
      forall tcs (objs: list (ident * ident)) e tys,
        (forall i, List.In i (unreset_call_insts tcs) -> List.In i (map fst objs)) ->
        get_mappings (map fst objs) e = Some tys ->
        e = reset_env ->
        exists extras, tcs_obc_extras tcs = Some extras.
    Proof.
      intros tcs objs e tys Hincl Hget Heq. subst e.
      destruct (get_mappings_incl_Some (unreset_call_insts tcs) (map fst objs)
                  reset_env tys Hincl Hget) as (txs & Htxs).
      clear Hincl Hget.
      revert txs Htxs.
      induction tcs as [|tc tcs IH]; intros txs Htxs; simpl.
      - eauto.
      - destruct tc as [x ck ce|x ck e|x ck f|o xs ck [|] g es]; simpl in Htxs.
        + destruct (IH _ Htxs) as (es' & Hes'). rewrite Hes'. eexists; reflexivity.
        + destruct (IH _ Htxs) as (es' & Hes'). rewrite Hes'. eexists; reflexivity.
        + destruct (IH _ Htxs) as (es' & Hes'). rewrite Hes'. eexists; reflexivity.
        + destruct (IH _ Htxs) as (es' & Hes'). rewrite Hes'. eexists; reflexivity.
        + cbn [tc_obc_extras].
          destruct (Env.find o reset_env) as [sty|] eqn:Ho; try discriminate.
          destruct (get_mappings (unreset_call_insts tcs) reset_env) as [t'|] eqn:Ht';
            try discriminate.
          destruct (IH _ Logic.eq_refl) as (es' & Hes').
          rewrite Hes'. eexists; reflexivity.
    Qed.

    (** ** Class-level raw preservation

        The Obc signature's raw constraints are the step method's, the
        reset method's, and then [collapse].  Every reset-method
        constraint is either backed by an STC constraint on the same
        target ([shared]) or owned by the call block of the instance it
        names (an extra). *)

    Theorem class_preserv_raw:
      forall scope vars memset clkvars tcs extras shared
             nconst craw_step craw_reset st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        List.In rst_ty scope ->
        Forall (tc_preserv_hyps_aug scope vars) tcs ->
        tcs_obc_extras tcs = Some extras ->
        NoDup (List.concat extras) ->
        (forall x, List.In x (List.concat extras) -> ~ List.In x scope) ->
        Forall2 (fun tc e =>
                   forall blk sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
                     constraints_scoped (scope ++ e)
                       (blk ++ map (fun ty => ([rst_ty], [ty])) e))
                tcs extras ->
        Forall (fun ty =>
                  List.In ty scope
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               shared ->
        (forall c, List.In c craw_reset ->
                   exists ty, c = ([rst_ty], [ty])
                              /\ (List.In ty shared
                                  \/ List.In ty (List.concat extras))) ->
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty tcs st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tcs memset clkvars tcs) st2 = OK (craw_step, st2') ->
        preserves_on scope nconst (SymTypes.collapse (craw_step ++ craw_reset)).
    Proof.
      intros scope vars memset clkvars tcs extras shared
             nconst craw_step craw_reset st1 st1' st2 st2'
             Hcons Hrstin Hhyps Hextras Hnd Hfresh Hsc Hshared Hreset Hstc Hobc.
      destruct (tcs_preserv_aug scope vars memset clkvars tcs extras
                  nconst craw_step st1 st1' st2 st2'
                  Hcons Hhyps Hextras Hnd Hfresh Hsc Hstc Hobc)
        as (tgt & Hcovstep & Hcovextra & Hpres).
      apply preserves_on_collapse.
      eapply preserves_on_incl
        with (t := tgt ++ map (fun ty => ([rst_ty], [ty])) shared).
      - intros c Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        + apply in_or_app. left. now apply Hcovstep.
        + destruct (Hreset c Hin) as (ty & Hc & [Hsh|Hex]); subst c.
          * apply in_or_app. right.
            apply in_map_iff. exists ty. split; [reflexivity|exact Hsh].
          * apply in_or_app. left. now apply Hcovextra.
      - now apply preserves_on_app_reset_shared.
    Qed.


    (** ** Class-level signature preservation

        The signature-level statement: the STC signature's constraints
        are [simplify nconst (hidden_sys_vars ...)] and the Obc class's
        are [simplify (collapse (craw_step ++ craw_reset))
        (hidden_class_vars ...)].  The two hide different name sets, and
        the bridge does not require them to agree. *)

    Corollary class_preserv_signature:
      forall sigscope rawscope vars memset clkvars tcs extras shared
             nconst craw_step craw_reset hidden_stc hidden_obc st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        List.In rst_ty rawscope ->
        Forall (tc_preserv_hyps_aug rawscope vars) tcs ->
        tcs_obc_extras tcs = Some extras ->
        NoDup (List.concat extras) ->
        (forall x, List.In x (List.concat extras) -> ~ List.In x rawscope) ->
        Forall2 (fun tc e =>
                   forall blk sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
                     constraints_scoped (rawscope ++ e)
                       (blk ++ map (fun ty => ([rst_ty], [ty])) e))
                tcs extras ->
        Forall (fun ty =>
                  List.In ty rawscope
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               shared ->
        (forall c, List.In c craw_reset ->
                   exists ty, c = ([rst_ty], [ty])
                              /\ (List.In ty shared
                                  \/ List.In ty (List.concat extras))) ->
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty tcs st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tcs memset clkvars tcs) st2 = OK (craw_step, st2') ->
        wf_constraints nconst ->
        (forall x, List.In x hidden_stc -> ~ List.In x sigscope) ->
        (forall x, List.In x sigscope -> List.In x rawscope) ->
        preserves_on sigscope
          (SymTypes.simplify nconst hidden_stc)
          (SymTypes.simplify (SymTypes.collapse (craw_step ++ craw_reset)) hidden_obc).
    Proof.
      intros. eapply preserves_on_simplify_bridge with (rawscope := rawscope); eauto.
      eapply class_preserv_raw; eauto.
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
