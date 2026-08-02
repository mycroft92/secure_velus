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
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
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
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import WD    : STCWELLDEFINED Ids Op CESyn SynStc SystStc OrdStc VarStc
                    LastStc DefStc CEIsF IsFStc)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc
       IsFStc CloStc WD SECSTCTYPING)
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

    (** The dual of [clock_pc_assign_clk_type]: if the STC side managed
        to type the clock, the Obc side can walk it, at whatever pc. *)

    Lemma clock_pc_ok:
      forall b ck ckty pc,
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        exists pc', clock_pc pc ck = Some pc'.
    Proof.
      intros b ck. induction ck as [|ck IH x bck];
        intros ckty pc Hassign; simpl in *.
      - eexists; reflexivity.
      - destruct (SECCETYPING.assign_clk_type env b ck) as [ckty'|] eqn:Hck;
          simpl in Hassign; try discriminate.
        destruct (Env.find x env) as [ty|] eqn:Hx; simpl in Hassign;
          try discriminate.
        destruct (IH ckty' pc Logic.eq_refl) as (pc' & Hpc').
        rewrite Hpc'. eexists; reflexivity.
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

    (** Existence, as opposed to containment: wherever the STC side
        typed the actuals, the Obc side types the translated ones. *)

    Lemma translate_args_type_ok:
      forall memset clkvars ck es tys st1 st1' st2,
        SC.mmap (fun e => option_to_sec (SECCETYPING.assign_exp_type env e))
          es st1 = OK (tys, st1') ->
        exists otys,
          SC.mmap (fun e => option_to_sec (SECOBCTYPING.assign_exp_type env e))
            (map (translate_arg memset clkvars ck) es) st2 = OK (otys, st2).
    Proof.
      intros memset clkvars ck es. induction es as [|e es IH];
        intros tys st1 st1' st2 Hce.
      - exists []. reflexivity.
      - simpl in Hce.
        eapply sec_bind_inv in Hce as (ety & sta & Hhd & Hce).
        eapply sec_bind_inv in Hce as (tys' & stb & Htl & _).
        assert (Hetyopt : SECCETYPING.assign_exp_type env e = Some ety).
        { unfold option_to_sec in Hhd.
          destruct (SECCETYPING.assign_exp_type env e); try discriminate.
          now inversion Hhd. }
        destruct (translate_arg_type_incl memset clkvars ck e ety Hetyopt)
          as (oty & Hoty & _).
        destruct (IH _ _ _ st2 Htl) as (otys & Hotys).
        exists (oty :: otys). simpl.
        eapply (mmap_cons_ok
                  (fun e0 => option_to_sec (SECOBCTYPING.assign_exp_type env e0))
                  (translate_arg memset clkvars ck e)
                  (map (translate_arg memset clkvars ck) es) st2 oty st2 otys st2).
        + unfold option_to_sec. rewrite Hoty. reflexivity.
        + exact Hotys.
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

    (** ** Relative totality: the Obc generator succeeds wherever the
        STC one did

        Each lemma here mirrors the corresponding constraint lemma above,
        keeping its hypotheses and replacing the *assumed*
        [generate_stmt_constraints ... = OK ...] by an [exists].  Nothing
        new is assumed about the program: an STC-side [assign_*] result
        is exactly the statement that the environment covers the names
        the translated statement looks up, and
        [translate_exp_type_correspondence] carries that across the
        expression translation. *)

    Lemma translate_cexp_constraints_ok:
      forall memset vars x ce ck b pc ckty cety xty st,
        CEClo.wc_cexp vars ce ck ->
        SECCETYPING.assign_clk_type env b ck = Some ckty ->
        SECCETYPING.assign_cexp_type env ce = Some cety ->
        Env.find x env = Some xty ->
        exists cns,
          generate_stmt_constraints G env state_env rst_ty pc
            (translate_cexp memset x ce) st = OK (cns, st).
    Proof.
      intros memset vars x ce.
      induction ce as [y cet IHt cef IHf|e cet IHt cef IHf|le];
        intros ck b pc ckty cety xty st Hwc Hck Hcety Hx;
        inversion Hwc as [y' t' f' ck' Hiny Hwct Hwcf
                         |e' t' f' ck' Hwce Hwct Hwcf
                         |le' ck' Hwce]; subst; simpl in Hcety.
      - (* Emerge: the scrutinee is a plain variable *)
        destruct (Env.find y env) as [yty|] eqn:Hy; simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cet) as [t1|] eqn:Ht;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cef) as [t2|] eqn:Hf;
          simpl in Hcety; try discriminate.
        assert (Hbv : SECOBCTYPING.assign_exp_type env (bool_var memset y)
                      = Some [yty])
          by (unfold bool_var, tovar;
              destruct (PS.mem y memset); simpl; now rewrite Hy).
        (* the two branches sit at the extended clock *)
        assert (Hckt : exists cty,
                   SECCETYPING.assign_clk_type env b (Con ck y true) = Some cty)
          by (simpl; rewrite Hck; simpl; rewrite Hy; eexists; reflexivity).
        assert (Hckf : exists cty,
                   SECCETYPING.assign_clk_type env b (Con ck y false) = Some cty)
          by (simpl; rewrite Hck; simpl; rewrite Hy; eexists; reflexivity).
        destruct Hckt as (ctyt & Hckt). destruct Hckf as (ctyf & Hckf).
        destruct (IHt (Con ck y true) b (pc ⊔ [yty]) ctyt t1 xty st
                    Hwct Hckt Logic.eq_refl Hx) as (c1 & Hc1).
        destruct (IHf (Con ck y false) b (pc ⊔ [yty]) ctyf t2 xty st
                    Hwcf Hckf Logic.eq_refl Hx) as (c2 & Hc2).
        exists (c1 ++ c2). simpl.
        unfold option_to_sec, bind, ret. rewrite Hbv. rewrite Hc1, Hc2.
        reflexivity.
      - (* Eite: the scrutinee is a translated expression *)
        destruct (SECCETYPING.assign_exp_type env e) as [ety|] eqn:He;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cet) as [t1|] eqn:Ht;
          simpl in Hcety; try discriminate.
        destruct (SECCETYPING.assign_cexp_type env cef) as [t2|] eqn:Hf;
          simpl in Hcety; try discriminate.
        destruct (translate_exp_type_correspondence env memset vars e ck b ckty ety
                    Hwce Hck He) as (oty & Hoty & _).
        destruct (IHt ck b (pc ⊔ oty) ckty t1 xty st
                    Hwct Hck Logic.eq_refl Hx) as (c1 & Hc1).
        destruct (IHf ck b (pc ⊔ oty) ckty t2 xty st
                    Hwcf Hck Logic.eq_refl Hx) as (c2 & Hc2).
        exists (c1 ++ c2). simpl.
        unfold option_to_sec, bind, ret. rewrite Hoty. rewrite Hc1, Hc2.
        reflexivity.
      - (* Eexp: a single assignment *)
        destruct (translate_exp_type_correspondence env memset vars le ck b ckty cety
                    Hwce Hck Hcety) as (oty & Hoty & _).
        eexists. simpl.
        unfold option_to_sec, find_env, bind, ret.
        rewrite Hoty, Hx. reflexivity.
    Qed.

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

    (** The call rules and the per-trconstr correspondence that used
        them live in [SIGNATURE_PROOFS] and in [tc_preserv_aug]
        respectively.  An earlier, weaker set -- [call_side_conditions],
        [Signature_call_preserves_obc], [Signature_consistent_obc],
        [tccall_preserv], [signatures_preserved_obc_calls_from_good],
        [tc_preserv_hyps] and [tc_preserv] -- was superseded and has been
        removed; see the git history if a discarded head constraint is
        ever wanted back. *)





    (** The reset-underlying call theorem *produces* the constraint
        [srcrst |- sty].  For an instance the system never resets, that
        constraint is exactly what the Obc reset method emits for it, so
        keeping it lets the call block own its own reset-method
        constraint instead of leaving [sty] constrained from two
        different blocks.  That is why the rule below keeps the head
        rather than dropping it. *)

    (** The shared rule (SIGPROOFS): identical on both bridges. *)
    Definition Signature_call_preserves_obc_rst (n1 n2: SIG.signature) : Prop :=
      SIGPROOFS.call_preserves_rst n1 n2.

    Theorem signatures_preserved_obc_calls_from_good_rst:
      forall stcsig obcsig,
        SIG.signature_good stcsig ->
        NoDup (SIG.signature_scope stcsig) ->
        SIG.signature_scoped obcsig ->
        SIGPROOFS.signatures_preserved stcsig obcsig ->
        Signature_call_preserves_obc_rst stcsig obcsig.
    Proof.
      exact SIGPROOFS.call_preserves_rst_from_good.
    Qed.

    (** Dropping the head recovers the plain version. *)

    (** For an instance the system *resets*, the STC call passes the
        reset instance type and the Obc call passes the instance's state
        type — and those are the same identifier.  The two calls then
        differ only in their input actuals, so the equal-actuals
        preservation applies and no freshness side condition on that
        identifier is needed.  This is what lets the reset instance stay
        inside the shared scope, where the [TcReset] constraint also
        mentions it. *)

    (** The shared rule (SIGPROOFS): identical on both bridges. *)
    Definition Signature_call_preserves_obc_eq (n1 n2: SIG.signature) : Prop :=
      SIGPROOFS.call_preserves_eq n1 n2.

    Theorem signatures_preserved_obc_equal_calls_from_good:
      forall stcsig obcsig,
        SIG.signature_good stcsig ->
        NoDup (SIG.signature_scope stcsig) ->
        SIG.signature_scoped obcsig ->
        SIGPROOFS.signatures_preserved stcsig obcsig ->
        Signature_call_preserves_obc_eq stcsig obcsig.
    Proof.
      exact SIGPROOFS.call_preserves_eq_from_good.
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
      forall scope vars P memset clkvars i xs ck f es ckty
             nconst sconst st1 st1' st2 st2',
        SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
        Signature_consistent_obc_eq G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        wc_env vars ->
        CloStc.wc_trconstr P vars (SynStc.TcCall i xs ck true f es) ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        (forall rinst, Env.find i reset_env = Some rinst -> List.In rinst scope) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcCall i xs ck true f es) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcCall i xs ck true f es)) st2
          = OK (sconst, st2') ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope vars P memset clkvars i xs ck f es ckty
             nconst sconst st1 st1' st2 st2'
             Hckopt Hcons Hscopefresh Hwcenv Hwc Hvars Hclkin Hresetscope Hstc Hobc.
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
        (* the call side conditions, derived from the actual actuals *)
        assert (Hsf : SIG.scope_fresh scope n1) by (eapply Hscopefresh; eauto).
        assert (Hrinsteq : Env.find i reset_env = Some rinst).
        { unfold SC.find_env in Hrinst.
          destruct (Env.find i reset_env) as [v|] eqn:Hv; try discriminate.
          unfold ret in Hrinst. congruence. }
        inversion Hwc as [| | |i2 xs2 ck2 rst2 f2 es2 sy P' sub
                              Hfindnode Hinputs Houtputs]; subst.
        assert (Hckscope : st_scoped scope ckty).
        { eapply (SECCETYPING.assign_clk_type_scoped env clk_ty scope ck ckty);
            [exact Hclkin| |exact Hckopt].
          intros z Hz.
          eapply Hvars.
          eapply (SECSTCTYPING.wc_tc_clock_free_in_vars P vars i (x :: xs') ck true f es);
            eauto. }
        assert (HinpScope : Forall (st_scoped scope) inptyp1).
        { eapply (SECSTCTYPING.mmap_assign_exp_type_scoped env scope es inptyp1);
            [|exact Hinp1].
          eapply (SECSTCTYPING.wc_call_args_scoped env vars scope sub ck
                    (SynStc.s_in sy) es); eauto. }
        assert (HoutScope : Forall (fun z => List.In z scope) outtyp1).
        { eapply (SC.mmap_find_env_scoped env scope (x :: xs') outtyp1);
            [|exact Hout1].
          intros y Hy.
          eapply (SECSTCTYPING.wc_call_outs_scoped env vars scope sub ck
                    (SynStc.s_out sy) (x :: xs')); eauto. }
        assert (Hcss : SIG.call_subst_scoped scope inptyp1 ckty [rinst] outtyp1).
        { split.
          - unfold SIG.call_actuals_scoped.
            split; [exact HinpScope|].
            split; [exact Hckscope|assumption].
          - apply st_scoped_singleton. exact (Hresetscope rinst Hrinsteq). }
        assert (Hfr1 : SIG.call_subst_fresh n1 inptyp1 ckty [rinst] outtyp1).
        { eapply (SIG.call_subst_fresh_from_scope_fresh scope n1 inptyp1 ckty
                    [rinst] outtyp1).
          - exact Hsf.
          - exact HinpScope.
          - exact Hckscope.
          - apply st_scoped_singleton. exact (Hresetscope rinst Hrinsteq).
          - exact HoutScope. }
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


    (** Both call forms are needed at once: an instance the system resets
        is called with the same reset actual on both sides (equal-actuals
        preservation, its identifier inside the scope), while one it never
        resets is called with [rst_ty] on the STC side and its state type
        on the Obc side (reset-underlying preservation, its identifier a
        private extra). *)

    (** Mirrors the NLustre-to-STC [Signature_head_consistent]: the two
        callee signatures agree on name and interface, and both call
        forms preserve.  The interface agreement is what supplies the
        callee-side freshness conditions, its scope being the same list
        as the source signature's. *)

    (** Grouped exactly as NLustre's [Signature_call_preserves]: the
        equal-call clause first, the reset-call clause second. *)

    Definition Signature_call_preserves_obc_full (n1 n2: SIG.signature) : Prop :=
      Signature_call_preserves_obc_eq n1 n2
      /\ Signature_call_preserves_obc_rst n1 n2.

    Definition Signature_head_consistent_obc (n1 n2: SIG.signature) : Prop :=
      n1.(s_name) = n2.(s_name)
      /\ SIG.signature_fields_agree n1 n2
      /\ Signature_call_preserves_obc_full n1 n2.

    Definition Signature_consistent_obc_full (H1 H2: SIG.secglobal) : Prop :=
      forall f n1,
        SIG.find_signature f H1 = Some n1 ->
        exists n2,
          SIG.find_signature f H2 = Some n2
          /\ Signature_head_consistent_obc n1 n2.

    Lemma signatures_preserved_obc_full_from_good:
      forall stcsig obcsig,
        stcsig.(s_name) = obcsig.(s_name) ->
        SIG.signature_good stcsig ->
        NoDup (SIG.signature_scope stcsig) ->
        SIG.signature_scoped obcsig ->
        SIGPROOFS.signatures_preserved stcsig obcsig ->
        Signature_head_consistent_obc stcsig obcsig.
    Proof.
      intros stcsig obcsig Hname Hgood Hnd Hssc Hpres.
      split; [exact Hname|].
      split; [exact (proj1 Hpres)|].
      split.
      - eapply signatures_preserved_obc_equal_calls_from_good; eauto.
      - eapply signatures_preserved_obc_calls_from_good_rst; eauto.
    Qed.

    (** The [TcCall] case for an instance the system never resets.  The
        Obc call passes the instance's state type where STC passes
        [rst_ty], so the block owns that identifier - and, with it, the
        reset method's constraint on it. *)

    Lemma tccall_unreset_preserv_rst:
      forall scope vars P memset clkvars i xs ck f es ckty sty
             nconst sconst st1 st1' st2 st2',
        SECCETYPING.assign_clk_type env clk_ty ck = Some ckty ->
        Env.find i reset_env = Some sty ->
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        secglobal_scope_sec G2 ->
        wc_env vars ->
        CloStc.wc_trconstr P vars (SynStc.TcCall i xs ck false f es) ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        List.In rst_ty scope ->
        ~ List.In sty scope ->
        (exists n, sty = Ids.gensym Ids.sec_reset n) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcCall i xs ck false f es) st1 = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars (SynStc.TcCall i xs ck false f es)) st2
          = OK (sconst, st2') ->
        xs <> [] ->
        preserves_on scope nconst (sconst ++ [([rst_ty], [sty])]).
    Proof.
      intros scope vars P memset clkvars i xs ck f es ckty sty
             nconst sconst st1 st1' st2 st2'
             Hckopt Hsty Hcons Hscopefresh Hg2sec Hwcenv Hwc Hvars
             Hclkin Hrstin Hstynotin Hstysec Hstc Hobc Hxs.
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
      destruct (Hcons f n1 Hf1) as (n2' & Hf2' & _ & Hfields & _ & Hpresrst).
      rewrite Hf2 in Hf2'. inversion Hf2'; subst n2'.
      (* the call side conditions, from the real actuals *)
      assert (Hsf : SIG.scope_fresh scope n1) by (eapply Hscopefresh; eauto).
      inversion Hwc as [| | |i2 xs2 ck2 rst2 f2 es2 sy P' sub
                            Hfindnode Hinputs Houtputs]; subst.
      assert (Hckscope : st_scoped scope ckty).
      { eapply (SECCETYPING.assign_clk_type_scoped env clk_ty scope ck ckty);
          [exact Hclkin| |exact Hckopt].
        intros z Hz. eapply Hvars.
        eapply (SECSTCTYPING.wc_tc_clock_free_in_vars P vars i (x :: xs') ck false f es);
          eauto. }
      assert (HinpScope : Forall (st_scoped scope) inptyp1).
      { eapply (SECSTCTYPING.mmap_assign_exp_type_scoped env scope es inptyp1);
          [|exact Hinp1].
        eapply (SECSTCTYPING.wc_call_args_scoped env vars scope sub ck
                  (SynStc.s_in sy) es); eauto. }
      assert (HoutScope : Forall (fun z => List.In z scope) outtyp1).
      { eapply (SC.mmap_find_env_scoped env scope (x :: xs') outtyp1);
          [|exact Hout1].
        intros y Hy.
        eapply (SECSTCTYPING.wc_call_outs_scoped env vars scope sub ck
                  (SynStc.s_out sy) (x :: xs')); eauto. }
      assert (Hincl2 : Forall2 (fun t1 t2 => forall z, List.In z t2 -> List.In z t1)
                         inptyp1 inptyp2)
        by (eapply translate_args_type_incl; eauto).
      assert (HinpScope2 : Forall (st_scoped scope) inptyp2).
      { clear -HinpScope Hincl2.
        induction Hincl2 as [|t1 t2 l1 l2 Ht Hall IH];
          [constructor|].
        inversion HinpScope as [|? ? Ht1 Hrest]; subst.
        constructor; [|now apply IH].
        intros z Hz. apply Ht1. now apply Ht. }
      assert (Hcss : SIG.call_subst_scoped scope inptyp1 ckty [rst_ty] outtyp1).
      { split.
        - unfold SIG.call_actuals_scoped.
          split; [exact HinpScope|]. split; [exact Hckscope|assumption].
        - apply st_scoped_singleton. exact Hrstin. }
      assert (Hfr1 : SIG.call_subst_fresh n1 inptyp1 ckty [rst_ty] outtyp1).
      { eapply (SIG.call_subst_fresh_from_scope_fresh scope n1 inptyp1 ckty
                  [rst_ty] outtyp1); auto.
        apply st_scoped_singleton. exact Hrstin. }
      assert (Hsf2 : SIG.scope_fresh scope n2)
        by (eapply SIG.scope_fresh_fields_agree; eauto).
      assert (Hfr2 : SIG.call_subst_fresh n2 inptyp2 ckty [sty] outtyp1).
      { eapply (SIG.call_subst_fresh_reset_from_scope_fresh scope n2 inptyp2
                  ckty sty outtyp1); auto.
        eapply Hg2sec; eauto. }
      eapply preserves_on_Permutation;
        [reflexivity|apply Permutation_cons_append|].
      eapply (Hpresrst scope inptyp1 inptyp2 ckty [rst_ty] sty outtyp1
                nconst sconst sta3 stb3 st1' st2').
      - exact Hsf.
      - exact Hcss.
      - exact Hstynotin.
      - exact Hfr1.
      - exact (proj1 (proj2 (proj2 Hfr2))).
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

    Lemma Signature_consistent_obc_eq_from_full:
      forall H1 H2,
        Signature_consistent_obc_full H1 H2 ->
        Signature_consistent_obc_eq H1 H2.
    Proof.
      intros H1 H2 Hfull f n1 Hf.
      destruct (Hfull f n1 Hf) as (n2 & Hf2 & _ & _ & Heq & _).
      exists n2. split; assumption.
    Qed.

    (** ** Per-trconstr preservation, with the block owning its extras

        The target of a block is its own Obc constraints together with
        the reset-method constraint of any instance it owns.  No
        per-trconstr predicate is assumed: the call side conditions are
        derived in-proof from the same facts the NLustre-Stc bridge
        takes. *)

    Lemma tc_preserv_aug:
      forall scope vars P memset clkvars tc e nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        wc_env vars ->
        CloStc.wc_trconstr P vars tc ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        (forall i rinst,
            ((exists ck g, tc = SynStc.TcReset i ck g)
             \/ (exists ys ck g es, tc = SynStc.TcCall i ys ck true g es)) ->
            Env.find i reset_env = Some rinst -> List.In rinst scope) ->
        secglobal_scope_sec G2 ->
        List.In rst_ty scope ->
        (forall x sty, Env.find x reset_env = Some sty ->
                       exists n, sty = Ids.gensym Ids.sec_reset n) ->
        tc_obc_extras tc = Some e ->
        (forall ty, List.In ty e -> ~ List.In ty scope) ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty tc st1
          = OK (nconst, st1') ->
        generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
          (translate_tc memset clkvars tc) st2 = OK (sconst, st2') ->
        preserves_on scope nconst (sconst ++ map (fun ty => ([rst_ty], [ty])) e).
    Proof.
      intros scope vars P memset clkvars tc e nconst sconst st1 st1' st2 st2'
             Hcons Hscopefresh Hwcenv Hwc Hvars Hclkin Hresetscope
             Hg2sec Hrstin Hrange Hextras Hefresh Hstc Hobc.
      destruct tc as [x ck ce|x ck ex|i ck f|i xs ck [|] f es];
        simpl in Hextras.
      - inversion Hextras; subst e. simpl. rewrite app_nil_r.
        inversion Hwc; subst.
        eapply tcdef_preserv; eauto.
      - inversion Hextras; subst e. simpl. rewrite app_nil_r.
        inversion Hwc; subst.
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
        eapply (tccall_reset_preserv_eq scope vars P memset clkvars _ _ _ _ _ ckty).
        + exact Hckty.
        + eapply Signature_consistent_obc_eq_from_full; exact Hcons.
        + exact Hscopefresh.
        + exact Hwcenv.
        + exact Hwc.
        + exact Hvars.
        + exact Hclkin.
        + intros rinst Hr. eapply Hresetscope; [right; eauto|exact Hr].
        + exact Hstc.
        + exact Hobc.
      - (* an unreset call: the block owns the instance's state type *)
        simpl in Hextras.
        destruct (Env.find i reset_env) as [sty|] eqn:Hsty; [|discriminate].
        inversion Hextras; subst e. simpl.
        assert (Hstynotin : ~ List.In sty scope) by (apply Hefresh; now left).
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
        + eapply (tccall_unreset_preserv_rst scope vars P memset clkvars i
                    (x :: xs') ck f es ckty sty); eauto.
          discriminate.
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
      forall scope vars P memset clkvars tcs nblocks sblocks extras,
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) tcs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        (forall tc i rinst,
            List.In tc tcs ->
            ((exists ck g, tc = SynStc.TcReset i ck g)
             \/ (exists ys ck g es, tc = SynStc.TcCall i ys ck true g es)) ->
            Env.find i reset_env = Some rinst -> List.In rinst scope) ->
        secglobal_scope_sec G2 ->
        List.In rst_ty scope ->
        (forall x sty, Env.find x reset_env = Some sty ->
                       exists n, sty = Ids.gensym Ids.sec_reset n) ->

        Forall2 (fun tc nblk =>
                   exists sa sb,
                     SECSTCTYPING.generate_trconstr_constraint G1 env reset_env
                       clk_ty rst_ty tc sa = OK (nblk, sb)) tcs nblocks ->
        Forall2 (fun tc sblk =>
                   exists sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (sblk, sb)) tcs sblocks ->
        Forall2 (fun tc e => tc_obc_extras tc = Some e) tcs extras ->
        (forall e ty, List.In e extras -> List.In ty e -> ~ List.In ty scope) ->
        Forall2 (preserves_on scope) nblocks (zip_app sblocks extras).
    Proof.
      intros scope vars P memset clkvars tcs nblocks sblocks extras
             Hcons Hscopefresh Hwcenv Hwctcs Hvars Hclkin Hresetscope
             Hg2sec Hrstin Hrange Hn Hs He Hefresh.
      revert nblocks sblocks extras Hn Hs He Hefresh.
      revert Hwctcs Hresetscope.
      induction tcs as [|tc tcs IH];
        intros Hwctcs Hresetscope nblocks sblocks extras Hn Hs He Hefresh.
      - inversion Hn; inversion Hs; inversion He; subst. simpl. constructor.
      - inversion Hn as [|tc1 nblk tcs1 nbs Hnb Hn']; subst.
        inversion Hs as [|tc2 sblk tcs2 sbs Hsb Hs']; subst.
        inversion He as [|tc3 e tcs3 es Hee He']; subst.
        simpl. constructor.
        + destruct Hnb as (sa & sb & Hnb). destruct Hsb as (sc & sd & Hsb).
          inversion Hwctcs as [|tc5 tcs5 Hwctc Hwcrest]; subst.
          eapply (tc_preserv_aug scope vars P); eauto.
          * intros i rinst Hshape Hfind.
            eapply Hresetscope; [now left|exact Hshape|exact Hfind].
          * intros ty Hty. eapply Hefresh; [now left|exact Hty].
        + inversion Hwctcs; subst.
          eapply IH; eauto.
          * intros tc5 i rinst Hin5 Hshape Hfind.
            eapply Hresetscope; [right; exact Hin5|exact Hshape|exact Hfind].
          * intros e5 ty He5 Hty. eapply Hefresh; [right; exact He5|exact Hty].
    Qed.

    (** Whole-body preservation against a target that also carries the
        reset-method constraints of every instance the body owns. *)

    Lemma tcs_preserv_aug:
      forall scope vars P memset clkvars tcs extras nconst sconst st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) tcs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        (forall tc i rinst,
            List.In tc tcs ->
            ((exists ck g, tc = SynStc.TcReset i ck g)
             \/ (exists ys ck g es, tc = SynStc.TcCall i ys ck true g es)) ->
            Env.find i reset_env = Some rinst -> List.In rinst scope) ->
        secglobal_scope_sec G2 ->
        List.In rst_ty scope ->
        (forall x sty, Env.find x reset_env = Some sty ->
                       exists n, sty = Ids.gensym Ids.sec_reset n) ->

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
      intros scope vars P memset clkvars tcs extras nconst sconst st1 st1' st2 st2'
             Hcons Hscopefresh Hwcenv Hwctcs Hvars Hclkin Hresetscope
             Hg2sec Hrstin Hrange Hextras Hnd Hfresh Hsc Hstc Hobc.
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
      assert (Hpres : Forall2 (preserves_on scope) (rev nblocks)
                        (zip_app sblocks (rev extras))).
      { assert (Hwcrev : Forall (CloStc.wc_trconstr P vars) (rev tcs))
          by (apply Forall_rev; exact Hwctcs).
        assert (Hresetrev :
                  forall tc5 i rinst,
                    List.In tc5 (rev tcs) ->
                    ((exists ck g, tc5 = SynStc.TcReset i ck g)
                     \/ (exists ys ck g es, tc5 = SynStc.TcCall i ys ck true g es)) ->
                    Env.find i reset_env = Some rinst -> List.In rinst scope).
        { intros tc5 i rinst Hin5 Hshape Hfind.
          rewrite <- in_rev in Hin5.
          eapply Hresetscope; eauto. }
        eapply (tcs_blocks_preserv_aug scope vars P memset clkvars (rev tcs)
                  (rev nblocks) sblocks (rev extras)); eauto.
        intros e5 ty He5 Hty. apply Hfresh.
        rewrite <- in_rev in He5.
        apply in_concat. exists e5. split; assumption. }
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

    (** Likewise the instance resets, for the instances the system
        actually resets. *)

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

    (** ** Targets of a translated trconstr

        [Control] only adds [Skip] branches, so it leaves the targets
        alone up to membership; a translated trconstr then writes exactly
        the security types of the names the source defines.  This is what
        shows every hidden class variable has a defining constraint,
        which [simplify_scoped] requires. *)

    Lemma stmt_targets_Control_inv:
      forall memset ck s tys,
        SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
          (Control memset ck s) = Some tys ->
        exists t,
          SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env s = Some t
          /\ (forall d, List.In d tys <-> List.In d t).
    Proof.
      intros memset ck. induction ck as [|ck IH x b]; intros s tys Htys.
      - exists tys. split; [exact Htys|tauto].
      - destruct b; simpl in Htys;
          destruct (IH _ _ Htys) as (t & Ht & Hiff); simpl in Ht;
          destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env s)
            as [t0|] eqn:Hs; try discriminate;
          inversion Ht; subst t; exists t0; split; try reflexivity.
      + intros d. rewrite Hiff, app_nil_r. tauto.
      + intros d. rewrite Hiff. simpl. tauto.
    Qed.

    Lemma stmt_targets_translate_cexp:
      forall memset x ce tys ty,
        SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
          (translate_cexp memset x ce) = Some tys ->
        Env.find x env = Some ty ->
        List.In ty tys.
    Proof.
      intros memset x ce. induction ce; intros tys ty Htys Hfind; simpl in Htys.
      - destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                    (translate_cexp memset x ce1)) as [t1|] eqn:H1;
          try discriminate.
        destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                    (translate_cexp memset x ce2)) as [t2|] eqn:H2;
          try discriminate.
        inversion Htys; subst tys.
        apply in_or_app; left. eapply IHce1; eauto.
      - destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                    (translate_cexp memset x ce1)) as [t1|] eqn:H1;
          try discriminate.
        destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                    (translate_cexp memset x ce2)) as [t2|] eqn:H2;
          try discriminate.
        inversion Htys; subst tys.
        apply in_or_app; left. eapply IHce1; eauto.
      - rewrite Hfind in Htys. inversion Htys; subst tys. now left.
    Qed.

    (** A translated trconstr writes the security type of every variable
        the source defines. *)

    Lemma stmt_targets_translate_tc_variables:
      forall memset clkvars tc tys x ty,
        SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
          (translate_tc memset clkvars tc) = Some tys ->
        List.In x (variables_tc tc) ->
        Env.find x env = Some ty ->
        List.In ty tys.
    Proof.
      intros memset clkvars tc tys x ty Htys Hin Hfind.
      destruct tc as [y ck ce|y ck e|i ck g|i ys ck b g es]; simpl in Hin.
      - destruct Hin as [Heq|[]]; subst y.
        unfold translate_tc in Htys.
        destruct (stmt_targets_Control_inv _ _ _ _ Htys) as (t & Ht & Hiff).
        apply Hiff. eapply stmt_targets_translate_cexp; eauto.
      - inversion Hin.
      - inversion Hin.
      - unfold translate_tc in Htys.
        destruct (stmt_targets_Control_inv _ _ _ _ Htys) as (t & Ht & Hiff).
        apply Hiff.
        destruct ys as [|y ys']; [inversion Hin|].
        simpl in Ht. rewrite ident_eqb_refl in Ht.
        destruct (get_mappings_in _ _ _ _ Hin Ht) as (ty0 & Hty0 & Hinty).
        rewrite Hfind in Hty0. inversion Hty0; subst ty0. exact Hinty.
    Qed.

    (** Lifting the per-trconstr fact over the body's fold: the targets of
        every translated trconstr, and of the accumulator, all land in the
        targets of the whole body. *)

    Lemma stmt_targets_fold_inv:
      forall memset clkvars tcs acc tys,
        SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
          (fold_left (fun i tc => SynObc.Comp (translate_tc memset clkvars tc) i)
             tcs acc) = Some tys ->
        exists accty,
          SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env acc = Some accty
          /\ (forall d, List.In d accty -> List.In d tys)
          /\ (forall tc, List.In tc tcs ->
                        exists t,
                          SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                            (translate_tc memset clkvars tc) = Some t
                          /\ forall d, List.In d t -> List.In d tys).
    Proof.
      intros memset clkvars tcs. induction tcs as [|tc tcs IH]; intros acc tys Hfold.
      - simpl in Hfold. exists tys. repeat split; auto.
        intros tc Hin. inversion Hin.
      - simpl in Hfold.
        destruct (IH _ _ Hfold) as (accty1 & Hacc1 & Hmono1 & Hall1).
        simpl in Hacc1.
        destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env
                    (translate_tc memset clkvars tc)) as [t|] eqn:Ht;
          try discriminate.
        destruct (SECOBCTYPINGCORRECTNESS.stmt_targets env reset_env acc)
          as [a|] eqn:Ha; try discriminate.
        inversion Hacc1; subst accty1.
        exists a. repeat split.
        + intros d Hd. apply Hmono1. apply in_or_app. now right.
        + intros tc5 Hin5.
          destruct Hin5 as [Heq|Hin5].
          * subst tc5. exists t. split; [exact Ht|].
            intros d Hd. apply Hmono1. apply in_or_app. now left.
          * destruct (Hall1 tc5 Hin5) as (t5 & Ht5 & Hmono5).
            exists t5. split; assumption.
    Qed.

    (** ** The translated class is well defined

        Each clause of [class_well_defined] holds for [translate_system]:
        the reset body assigns every memory and resets every object, and
        the step body assigns every variable the system defines. *)

    Lemma stmt_writes_reset_mems_fold:
      forall (mems: list (ident * (const * clock))) acc,
        (forall d, List.In d (SECOBCTYPING.stmt_writes acc) ->
                   List.In d (SECOBCTYPING.stmt_writes
                     (fold_left (fun s xc => SynObc.Comp s
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                        mems acc)))
        /\ (forall x, List.In x (map fst mems) ->
                     List.In x (SECOBCTYPING.stmt_writes
                       (fold_left (fun s xc => SynObc.Comp s
                          (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                          mems acc))).
    Proof.
      induction mems as [|xc mems IH]; intros acc; simpl.
      - split; [auto|contradiction].
      - destruct (IH (SynObc.Comp acc
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc))))))
          as (Hmono & Hall).
        split.
        + intros d Hd. apply Hmono. simpl. apply in_or_app; now left.
        + intros x Hx. destruct Hx as [Heq|Hx].
          * subst x. apply Hmono. simpl. apply in_or_app; right. now left.
          * now apply Hall.
    Qed.

    Lemma stmt_reset_insts_reset_insts_fold:
      forall (objs: list (ident * ident)) acc,
        (forall d, List.In d (SECOBCTYPING.stmt_reset_insts acc) ->
                   List.In d (SECOBCTYPING.stmt_reset_insts
                     (fold_left (fun s xf => SynObc.Comp s
                        (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc)))
        /\ (forall o, List.In o (map fst objs) ->
                     List.In o (SECOBCTYPING.stmt_reset_insts
                       (fold_left (fun s xf => SynObc.Comp s
                          (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc))).
    Proof.
      induction objs as [|xf objs IH]; intros acc; simpl.
      - split; [auto|contradiction].
      - destruct (IH (SynObc.Comp acc
                        (SynObc.Call [] (snd xf) (fst xf) reset [])))
          as (Hmono & Hall).
        split.
        + intros d Hd. apply Hmono. simpl. apply in_or_app; now left.
        + intros o Ho. destruct Ho as [Heq|Ho].
          * subst o. apply Hmono. simpl. apply in_or_app; right.
            rewrite ident_eqb_refl. now left.
          * now apply Hall.
    Qed.

    Lemma stmt_writes_Control:
      forall memset ck s d,
        List.In d (SECOBCTYPING.stmt_writes s) ->
        List.In d (SECOBCTYPING.stmt_writes (Control memset ck s)).
    Proof.
      intros memset ck. induction ck as [|ck IH x b]; intros s d Hd.
      - exact Hd.
      - destruct b; apply IH; cbn [SECOBCTYPING.stmt_writes];
          apply in_or_app.
        + now left.
        + now right.
    Qed.

    Lemma stmt_writes_translate_cexp:
      forall memset x ce,
        List.In x (SECOBCTYPING.stmt_writes (translate_cexp memset x ce)).
    Proof.
      intros memset x ce. induction ce; simpl.
      - apply in_or_app; now left.
      - apply in_or_app; now left.
      - now left.
    Qed.

    Lemma stmt_writes_translate_tc:
      forall memset clkvars tc x,
        List.In x (variables_tc tc) ->
        List.In x (SECOBCTYPING.stmt_writes (translate_tc memset clkvars tc)).
    Proof.
      intros memset clkvars tc x Hin.
      destruct tc as [y ck ce|y ck e|i ck g|i ys ck b g es]; simpl in Hin.
      - destruct Hin as [Heq|[]]; subst y.
        apply stmt_writes_Control. apply stmt_writes_translate_cexp.
      - inversion Hin.
      - inversion Hin.
      - apply stmt_writes_Control.
        destruct ys as [|y ys']; [inversion Hin|].
        simpl. rewrite ident_eqb_refl. exact Hin.
    Qed.

    (** The converses.  A translated body writes *only* the names the
        system defines -- its variables and its lasts -- which is what
        lets a constraint target be traced back to an output.  The
        forward lemmas above give containment the other way; both halves
        are needed, one for "every output is a target" and one for "every
        target is an output". *)

    Lemma stmt_writes_Control_inv:
      forall memset ck s d,
        List.In d (SECOBCTYPING.stmt_writes (Control memset ck s)) ->
        List.In d (SECOBCTYPING.stmt_writes s).
    Proof.
      intros memset ck. induction ck as [|ck IH x b]; intros s d Hd.
      - exact Hd.
      - destruct b; apply IH in Hd; cbn [SECOBCTYPING.stmt_writes] in Hd;
          apply in_app_iff in Hd as [Hd|Hd];
          solve [exact Hd | contradiction].
    Qed.

    Lemma stmt_writes_translate_cexp_inv:
      forall memset x ce d,
        List.In d (SECOBCTYPING.stmt_writes (translate_cexp memset x ce)) ->
        d = x.
    Proof.
      intros memset x ce. induction ce as [y t IHt f IHf|e t IHt f IHf|le];
        intros d Hd; simpl in Hd.
      - apply in_app_iff in Hd as [Hd|Hd]; [now apply IHt|now apply IHf].
      - apply in_app_iff in Hd as [Hd|Hd]; [now apply IHt|now apply IHf].
      - destruct Hd as [Heq|[]]. now symmetry.
    Qed.

    Lemma stmt_writes_translate_tc_inv:
      forall memset clkvars tc d,
        List.In d (SECOBCTYPING.stmt_writes (translate_tc memset clkvars tc)) ->
        List.In d (variables_tc tc) \/ List.In d (lasts_of [tc]).
    Proof.
      intros memset clkvars tc d Hd.
      destruct tc as [y ck ce|y ck e|i ck g|i ys ck b g es];
        unfold translate_tc in Hd; apply stmt_writes_Control_inv in Hd.
      - left. apply stmt_writes_translate_cexp_inv in Hd. subst d. now left.
      - right. cbn [SECOBCTYPING.stmt_writes] in Hd.
        destruct Hd as [Heq|[]]. subst d. now left.
      - cbn [SECOBCTYPING.stmt_writes] in Hd.
        destruct (ident_eqb reset step); contradiction.
      - left. cbn [SECOBCTYPING.stmt_writes] in Hd.
        rewrite ident_eqb_refl in Hd. exact Hd.
    Qed.

    Lemma stmt_writes_translate_tcs_fold_inv:
      forall memset clkvars tcs acc d,
        List.In d (SECOBCTYPING.stmt_writes
                     (fold_left (fun i tc =>
                        SynObc.Comp (translate_tc memset clkvars tc) i) tcs acc)) ->
        List.In d (SECOBCTYPING.stmt_writes acc)
        \/ List.In d (variables tcs) \/ List.In d (lasts_of tcs).
    Proof.
      induction tcs as [|tc tcs IH]; intros acc d Hd; simpl in Hd |- *.
      - now left.
      - destruct (IH _ _ Hd) as [Hin|[Hin|Hin]].
        + cbn [SECOBCTYPING.stmt_writes] in Hin.
          apply in_app_iff in Hin as [Hin|Hin].
          * destruct (stmt_writes_translate_tc_inv memset clkvars tc d Hin)
              as [Hv|Hl].
            -- right; left. apply in_or_app; now left.
            -- right; right.
               destruct tc as [|y ck e| |]; simpl in Hl |- *;
                 solve [contradiction | destruct Hl as [Heq|[]]; now left].
          * now left.
        + right; left. apply in_or_app; now right.
        + right; right. destruct tc as [|y ck e| |]; simpl; auto.
    Qed.

    Lemma stmt_writes_translate_tcs_fold:
      forall memset clkvars tcs acc,
        (forall d, List.In d (SECOBCTYPING.stmt_writes acc) ->
                   List.In d (SECOBCTYPING.stmt_writes
                     (fold_left (fun i tc =>
                        SynObc.Comp (translate_tc memset clkvars tc) i) tcs acc)))
        /\ (forall x, List.In x (variables tcs) ->
                     List.In x (SECOBCTYPING.stmt_writes
                       (fold_left (fun i tc =>
                          SynObc.Comp (translate_tc memset clkvars tc) i) tcs acc))).
    Proof.
      induction tcs as [|tc tcs IH]; intros acc; simpl.
      - split; [auto|contradiction].
      - destruct (IH (SynObc.Comp (translate_tc memset clkvars tc) acc))
          as (Hmono & Hall).
        split.
        + intros d Hd. apply Hmono. simpl. apply in_or_app; now right.
        + intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
          * apply Hmono. simpl. apply in_or_app; left.
            now apply stmt_writes_translate_tc.
          * now apply Hall.
    Qed.

    (** The reset body reads nothing but the memories it assigns, and the
        only instances it touches are the objects it resets. *)

    (** Converses for the reset body, matching the ones for the step
        body: the memory loop writes only memories and resets nothing,
        the instance loop resets only objects and writes nothing. *)

    Lemma stmt_writes_reset_mems_fold_inv:
      forall (mems: list (ident * (const * clock))) acc d,
        List.In d (SECOBCTYPING.stmt_writes
                     (fold_left (fun s xc => SynObc.Comp s
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                        mems acc)) ->
        List.In d (SECOBCTYPING.stmt_writes acc) \/ List.In d (map fst mems).
    Proof.
      induction mems as [|xc mems IH]; intros acc d Hd; simpl in Hd |- *.
      - now left.
      - destruct (IH _ _ Hd) as [Hin|Hin]; [|now right; right].
        cbn [SECOBCTYPING.stmt_writes] in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [now left|].
        cbn [SECOBCTYPING.stmt_writes] in Hin.
        destruct Hin as [Heq|[]]. right. now left.
    Qed.

    Lemma stmt_reset_insts_reset_mems_fold_inv:
      forall (mems: list (ident * (const * clock))) acc o,
        List.In o (SECOBCTYPING.stmt_reset_insts
                     (fold_left (fun s xc => SynObc.Comp s
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                        mems acc)) ->
        List.In o (SECOBCTYPING.stmt_reset_insts acc).
    Proof.
      induction mems as [|xc mems IH]; intros acc o Ho; simpl in Ho |- *;
        [exact Ho|].
      apply IH in Ho. cbn [SECOBCTYPING.stmt_reset_insts] in Ho.
      apply in_app_iff in Ho as [Ho|Ho]; [exact Ho|].
      cbn [SECOBCTYPING.stmt_reset_insts] in Ho. contradiction.
    Qed.

    Lemma stmt_reset_insts_reset_insts_fold_inv:
      forall (objs: list (ident * ident)) acc o,
        List.In o (SECOBCTYPING.stmt_reset_insts
                     (fold_left (fun s xf => SynObc.Comp s
                        (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc)) ->
        List.In o (SECOBCTYPING.stmt_reset_insts acc) \/ List.In o (map fst objs).
    Proof.
      induction objs as [|xf objs IH]; intros acc o Ho; simpl in Ho |- *.
      - now left.
      - destruct (IH _ _ Ho) as [Hin|Hin]; [|now right; right].
        cbn [SECOBCTYPING.stmt_reset_insts] in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [now left|].
        cbn [SECOBCTYPING.stmt_reset_insts] in Hin.
        rewrite ident_eqb_refl in Hin.
        destruct Hin as [Heq|[]]. right. now left.
    Qed.

    Lemma stmt_writes_reset_insts_fold_inv:
      forall (objs: list (ident * ident)) acc d,
        List.In d (SECOBCTYPING.stmt_writes
                     (fold_left (fun s xf => SynObc.Comp s
                        (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc)) ->
        List.In d (SECOBCTYPING.stmt_writes acc).
    Proof.
      induction objs as [|xf objs IH]; intros acc d Hd; simpl in Hd |- *;
        [exact Hd|].
      apply IH in Hd. cbn [SECOBCTYPING.stmt_writes] in Hd.
      apply in_app_iff in Hd as [Hd|Hd]; [exact Hd|].
      cbn [SECOBCTYPING.stmt_writes] in Hd.
      destruct (ident_eqb reset step); contradiction.
    Qed.

    Lemma stmt_free_reset_mems_fold:
      forall (mems: list (ident * (const * clock))) acc x,
        List.In x (SECOBCTYPING.stmt_free
                     (fold_left (fun s xc => SynObc.Comp s
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                        mems acc)) ->
        List.In x (SECOBCTYPING.stmt_free acc) \/ List.In x (map fst mems).
    Proof.
      induction mems as [|xc mems IH]; intros acc x Hx; simpl in Hx |- *.
      - now left.
      - destruct (IH _ _ Hx) as [Hin|Hin]; [|now right; right].
        cbn [SECOBCTYPING.stmt_free] in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [now left|].
        cbn [SECOBCTYPING.stmt_free SECOBCTYPING.exp_free] in Hin.
        destruct Hin as [Heq|[]]. right. now left.
    Qed.

    Lemma stmt_free_reset_insts_fold:
      forall (objs: list (ident * ident)) acc x,
        List.In x (SECOBCTYPING.stmt_free
                     (fold_left (fun s xf => SynObc.Comp s
                        (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc)) ->
        List.In x (SECOBCTYPING.stmt_free acc).
    Proof.
      induction objs as [|xf objs IH]; intros acc x Hx; simpl in Hx |- *.
      - exact Hx.
      - specialize (IH _ _ Hx).
        cbn [SECOBCTYPING.stmt_free] in IH.
        apply in_app_iff in IH as [Hin|Hin]; [exact Hin|].
        cbn [SECOBCTYPING.stmt_free] in Hin. contradiction.
    Qed.

    Lemma stmt_state_keys_reset_mems_fold:
      forall (mems: list (ident * (const * clock))) acc o,
        List.In o (SECOBCTYPING.stmt_state_keys
                     (fold_left (fun s xc => SynObc.Comp s
                        (SynObc.AssignSt (fst xc) (SynObc.Const (fst (snd xc)))))
                        mems acc)) ->
        List.In o (SECOBCTYPING.stmt_state_keys acc).
    Proof.
      induction mems as [|xc mems IH]; intros acc o Ho; simpl in Ho |- *.
      - exact Ho.
      - specialize (IH _ _ Ho).
        cbn [SECOBCTYPING.stmt_state_keys] in IH.
        apply in_app_iff in IH as [Hin|Hin]; [exact Hin|].
        cbn [SECOBCTYPING.stmt_state_keys] in Hin. contradiction.
    Qed.

    Lemma stmt_state_keys_reset_insts_fold:
      forall (objs: list (ident * ident)) acc o,
        List.In o (SECOBCTYPING.stmt_state_keys
                     (fold_left (fun s xf => SynObc.Comp s
                        (SynObc.Call [] (snd xf) (fst xf) reset [])) objs acc)) ->
        List.In o (SECOBCTYPING.stmt_state_keys acc) \/ List.In o (map fst objs).
    Proof.
      induction objs as [|xf objs IH]; intros acc o Ho; simpl in Ho |- *.
      - now left.
      - destruct (IH _ _ Ho) as [Hin|Hin]; [|now right; right].
        cbn [SECOBCTYPING.stmt_state_keys] in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [now left|].
        cbn [SECOBCTYPING.stmt_state_keys] in Hin.
        destruct Hin as [Heq|[]]. right. now left.
    Qed.

    (** The only instances the step body touches are those the source
        trconstrs name. *)

    Lemma stmt_state_keys_Control:
      forall memset ck s o,
        List.In o (SECOBCTYPING.stmt_state_keys (Control memset ck s)) ->
        List.In o (SECOBCTYPING.stmt_state_keys s).
    Proof.
      intros memset ck. induction ck as [|ck IH x b]; intros s o Ho.
      - exact Ho.
      - destruct b; specialize (IH _ _ Ho);
          cbn [SECOBCTYPING.stmt_state_keys] in IH;
          apply in_app_iff in IH as [Hin|Hin]; auto;
          cbn [SECOBCTYPING.stmt_state_keys] in Hin; try contradiction.
    Qed.

    Lemma stmt_state_keys_translate_cexp:
      forall memset x ce o,
        List.In o (SECOBCTYPING.stmt_state_keys (translate_cexp memset x ce)) ->
        False.
    Proof.
      intros memset x ce. induction ce; intros o Ho;
        cbn [translate_cexp SECOBCTYPING.stmt_state_keys] in Ho.
      - apply in_app_iff in Ho as [Ho|Ho]; [eapply IHce1|eapply IHce2]; eauto.
      - apply in_app_iff in Ho as [Ho|Ho]; [eapply IHce1|eapply IHce2]; eauto.
      - contradiction.
    Qed.

    Lemma stmt_state_keys_translate_tc:
      forall memset clkvars tc o,
        List.In o (SECOBCTYPING.stmt_state_keys
                     (translate_tc memset clkvars tc)) ->
        (exists ck g, tc = SynStc.TcReset o ck g)
        \/ (exists ys ck b g es, tc = SynStc.TcCall o ys ck b g es).
    Proof.
      intros memset clkvars tc o Ho.
      destruct tc as [y ck ce|y ck e|i ck g|i ys ck b g es];
        unfold translate_tc in Ho; apply stmt_state_keys_Control in Ho.
      - exfalso. eapply stmt_state_keys_translate_cexp; eauto.
      - cbn [SECOBCTYPING.stmt_state_keys] in Ho. contradiction.
      - cbn [SECOBCTYPING.stmt_state_keys] in Ho.
        destruct Ho as [Heq|[]]. subst i. left. eauto.
      - cbn [SECOBCTYPING.stmt_state_keys] in Ho.
        destruct Ho as [Heq|[]]. subst i. right. eauto 10.
    Qed.

    (** A reset call is a call, so the instances a body resets are among
        the instances it touches.  This is what lets the step body's
        reset instances be classified by
        [stmt_state_keys_translate_tcs_fold] rather than by a fold lemma
        of their own. *)

    Lemma stmt_reset_insts_state_keys:
      forall st o,
        List.In o (SECOBCTYPING.stmt_reset_insts st) ->
        List.In o (SECOBCTYPING.stmt_state_keys st).
    Proof.
      induction st as [x e|x e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls q m es|];
        intros o Ho; simpl in Ho |- *; try contradiction.
      - apply in_app_iff in Ho as [Ho|Ho]; apply in_or_app;
          [left; now apply IH1|right; now apply IH2].
      - apply in_app_iff in Ho as [Ho|Ho]; apply in_or_app;
          [left; now apply IH1|right; now apply IH2].
      - destruct ys as [|y ys']; [|contradiction].
        destruct (ident_eqb m Ids.reset); [exact Ho|contradiction].
    Qed.

    Lemma stmt_state_keys_translate_tcs_fold:
      forall memset clkvars tcs acc o,
        List.In o (SECOBCTYPING.stmt_state_keys
                     (fold_left (fun i tc =>
                        SynObc.Comp (translate_tc memset clkvars tc) i) tcs acc)) ->
        List.In o (SECOBCTYPING.stmt_state_keys acc)
        \/ exists tc, List.In tc tcs
                     /\ ((exists ck g, tc = SynStc.TcReset o ck g)
                         \/ (exists ys ck b g es, tc = SynStc.TcCall o ys ck b g es)).
    Proof.
      induction tcs as [|tc tcs IH]; intros acc o Ho; simpl in Ho |- *.
      - now left.
      - destruct (IH _ _ Ho) as [Hin|(tc5 & Hin5 & Hshape)].
        + cbn [SECOBCTYPING.stmt_state_keys] in Hin.
          apply in_app_iff in Hin as [Hin|Hin].
          * right. exists tc. split; [now left|].
            now apply stmt_state_keys_translate_tc in Hin.
          * now left.
        + right. exists tc5. split; [now right|exact Hshape].
    Qed.

    (** ** Free names of the step body

        [translate_tc_free] sends a name free in a translated trconstr
        back to a name the source constraint reads or defines.  The
        names it defines are the system's own variables and lasts; the
        names it reads are declared because the system is well clocked.
        The expression-level halves of that are already available as
        [SECCETYPING.wc_{clock,exp,cexp}_free_in_vars]; the trconstr
        level is the STC counterpart of [wc_call_clock_free_in_vars],
        whose call case reappears here verbatim. *)

    Lemma wc_trconstr_free_in_vars:
      forall P vars x tc,
        wc_env vars ->
        wc_trconstr P vars tc ->
        IsFStc.Is_free_in_tc x tc ->
        InMembers x vars.
    Proof.
      intros P vars x tc Henv Hwc Hfree.
      inversion Hwc as [y ck ce Hinv Hwce
                       |y ck e Hinv Hwce
                       |i ck g Hwck
                       |i ys ck rst g es sy P' sub Hfind Hargs Houts];
        subst; inv Hfree.
      - (* TcDef *)
        match goal with H: Is_free_in_caexp _ _ _ |- _ => inv H end.
        + eapply SECCETYPING.wc_cexp_free_in_vars; eauto.
        + assert (wc_clock vars ck) by (eapply wc_env_var; eauto).
          eapply SECCETYPING.wc_clock_free_in_vars; eauto.
      - (* TcNext *)
        match goal with H: Is_free_in_aexp _ _ _ |- _ => inv H end.
        + eapply SECCETYPING.wc_exp_free_in_vars; eauto.
        + assert (wc_clock vars ck) by (eapply wc_env_var; eauto).
          eapply SECCETYPING.wc_clock_free_in_vars; eauto.
      - (* TcReset *)
        eapply SECCETYPING.wc_clock_free_in_vars; eauto.
      - (* TcCall *)
        match goal with H: Is_free_in_aexps _ _ _ |- _ => inv H end.
        + (* free in an argument *)
          match goal with
          | H: Exists _ _ |- _ => apply Exists_exists in H as (e & Hine & Hfe)
          end.
          destruct (Forall2_in_right _ _ _ _ Hargs Hine) as (p & _ & Hp).
          destruct p as (z & zt & zck).
          destruct Hp as (_ & lck & Hwce & _).
          eapply SECCETYPING.wc_exp_free_in_vars; eauto.
        + (* free in the call's clock, as in [wc_call_clock_free_in_vars] *)
          destruct (SynStc.s_in sy) as [|(z & zt & zck) ins] eqn:Hinps.
          { pose proof (SynStc.s_ingt0 sy) as Hgt0. rewrite Hinps in Hgt0.
            simpl in Hgt0. inversion Hgt0. }
          inversion Hargs as [|? ? ? ? Hhead Htail]; subst.
          destruct Hhead as (_ & lck & Hexp & Hinst).
          assert (Hfree' : Is_free_in_clock x lck)
            by (eapply instck_free_bck; eauto).
          assert (Hwc_lck : wc_clock vars lck)
            by (eapply wc_clock_exp; eauto).
          eapply SECCETYPING.wc_clock_free_in_vars; eauto.
    Qed.

    Lemma stmt_free_translate_tcs_fold:
      forall memset clkvars tcs acc x,
        List.In x (SECOBCTYPING.stmt_free
                     (fold_left (fun i tc =>
                        SynObc.Comp (translate_tc memset clkvars tc) i) tcs acc)) ->
        List.In x (SECOBCTYPING.stmt_free acc)
        \/ exists tc, List.In tc tcs
                     /\ (IsFStc.Is_free_in_tc x tc
                         \/ List.In x (DefStc.defined_tc tc)).
    Proof.
      induction tcs as [|tc tcs IH]; intros acc x Hx; simpl in Hx |- *.
      - now left.
      - destruct (IH _ _ Hx) as [Hin|(tc' & Hin' & Hsrc)].
        + cbn [SECOBCTYPING.stmt_free] in Hin.
          apply in_app_iff in Hin as [Hin|Hin].
          * right. exists tc. split; [now left|].
            now apply translate_tc_free in Hin.
          * now left.
        + right. exists tc'. split; [now right|exact Hsrc].
    Qed.

    (** ** [translate_system] produces a well-defined class

        The class's fields and its two method bodies read off the source
        system; naming them once keeps the assembly below readable. *)

    Lemma translate_system_mems:
      forall s,
        (translate_system s).(c_mems)
        = map (fun xc => (fst xc, type_const (fst (snd xc)))) (SynStc.s_lasts s).
    Proof. reflexivity. Qed.

    Lemma translate_system_objs:
      forall s, (translate_system s).(c_objs) = SynStc.s_subs s.
    Proof. reflexivity. Qed.

    Lemma step_method_vars:
      forall s, (step_method s).(m_vars) = idty (SynStc.s_vars s).
    Proof. reflexivity. Qed.

    Lemma step_method_ins:
      forall s, (step_method s).(m_in) = idty (SynStc.s_in s).
    Proof. reflexivity. Qed.

    Lemma step_method_outs:
      forall s, (step_method s).(m_out) = idty (SynStc.s_out s).
    Proof. reflexivity. Qed.

    Lemma step_method_body:
      forall s,
      exists memset clkvars,
        (step_method s).(m_body) = translate_tcs memset clkvars (SynStc.s_tcs s).
    Proof. intro s. do 2 eexists; reflexivity. Qed.

    Lemma reset_method_body:
      forall s,
        (reset_method s).(m_body)
        = SynObc.Comp (reset_mems (SynStc.s_lasts s)) (reset_insts (SynStc.s_subs s)).
    Proof. reflexivity. Qed.

    (** Every clause of [class_well_defined] holds for a translated
        system.  The fold lemmas above give the syntactic ones;
        [s_vars_out_in_tcs], [s_lasts_in_tcs], [s_subs_calls_of] and
        [s_reset_incl] connect the source targets to the class's own
        names; and [wc_system] is what places the step body's reads
        inside the interface -- the single non-syntactic ingredient,
        exactly as [wc_node] is for [node_preserv_scoped]. *)

    (** A translated class writes its outputs too.  [class_well_defined]
        does not record this -- scopedness only needs the *hidden* names
        to be defined -- but call generation does: an output that is
        never a target cannot be read back by the closing [mmap findST].
        It is not a property of an arbitrary class, so it is proved here,
        for translated systems, off the same record invariant the locals
        clause uses.  [s_vars_out_in_tcs] covers both halves; the locals
        bullet below takes the left one and this takes the right. *)

    Lemma translate_step_writes_outs:
      forall s x,
        InMembers x (step_method s).(m_out) ->
        List.In x (SECOBCTYPING.stmt_writes (step_method s).(m_body)).
    Proof.
      intros s x Hx.
      pose proof (SynStc.s_vars_out_in_tcs s) as Hvo.
      rewrite step_method_outs in Hx.
      apply fst_InMembers in Hx. rewrite map_fst_idty in Hx.
      destruct (step_method_body s) as (memset & clkvars & Hb). rewrite Hb.
      unfold translate_tcs.
      apply (proj2 (stmt_writes_translate_tcs_fold
                      memset clkvars (SynStc.s_tcs s) SynObc.Skip)).
      eapply Permutation_in; [apply Hvo|].
      apply in_or_app; now right.
    Qed.

    (** [get_mappings_from_node] reads only the keys, so retyping the
        interface -- which is all [idty] and the [c_mems] map do -- leaves
        it unchanged. *)

    Lemma get_mappings_from_node_idty:
      forall (xs: list (ident * (type * clock))) e,
        get_mappings_from_node (idty xs) e = get_mappings_from_node xs e.
    Proof.
      induction xs as [|(x, (t, c)) xs IH]; intros e; simpl; [reflexivity|].
      now rewrite IH.
    Qed.

    Lemma get_mappings_from_node_mems:
      forall (xs: list (ident * (const * clock))) e,
        get_mappings_from_node
          (map (fun xc => (fst xc, type_const (fst (snd xc)))) xs) e
        = get_mappings_from_node xs e.
    Proof.
      induction xs as [|(x, (c, ck)) xs IH]; intros e; simpl; [reflexivity|].
      now rewrite IH.
    Qed.

    (** The Obc hidden set avoids the signature scope.  The locals and
        the memories go through the STC lemma -- they are literally the
        same lists, and the STC hidden set contains them whatever its
        reset instances are -- while the state instances are excluded by
        prefix, being [sec_reset] gensyms where the scope holds [sec]
        ones.  The STC key list is built from the Obc one: every reset
        instance is a sub, so the instance environment covers it. *)

    Lemma translate_class_hidden_disjoint:
      forall s e aux_names clk_id rst_id clk_type rst_type
             inp out locals lasts state_env stids ty,
        NAMEGEN.naming_env_props e aux_names ->
        get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id e = Some clk_type ->
        Env.find rst_id e = Some rst_type ->
        get_mappings_from_node (SynStc.s_in s) e = Some inp ->
        get_mappings_from_node (SynStc.s_out s) e = Some out ->
        get_mappings_from_node (SynStc.s_vars s) e = Some locals ->
        get_mappings_from_node (SynStc.s_lasts s) e = Some lasts ->
        get_node_inst s.(SynStc.s_name) aux_names = Some state_env ->
        get_mappings (map fst (SynStc.s_subs s)) state_env = Some stids ->
        List.In ty (SECOBCTYPING.hidden_class_vars locals lasts stids) ->
        ~ List.In ty (inp ++ out ++ [clk_type; rst_type]).
    Proof.
      intros s e aux_names clk_id rst_id clk_type rst_type
             inp out locals lasts state_env stids ty
             Hprops Haux Hclk Hrst Hinp Hout Hlocals Hlasts Hsenv Hstids Hty.
      destruct Hprops as ((Hinj & Hsec) & (Hauxsec & Hinstp & _)).
      destruct (Hinstp _ _ Hsenv) as (_ & Hrstrange).
      assert (Hauxsec' : exists i j, clk_id = Ids.gensym Ids.sec i
                                     /\ rst_id = Ids.gensym Ids.sec j)
        by (eapply Hauxsec; eauto).
      (* the STC key list: the reset instances are among the subs *)
      assert (Hrids : exists rids,
                 get_mappings (map fst (resets_of s.(SynStc.s_tcs)))
                   state_env = Some rids).
      { apply (proj2 (get_mappings_Some_iff _ _)).
        rewrite Forall_forall. intros x Hx.
        pose proof (proj1 (get_mappings_Some_iff _ _)
                      (ex_intro _ stids Hstids)) as Hall.
        rewrite Forall_forall in Hall. apply Hall.
        apply in_map_iff in Hx as ((y & f) & Hyf & Hin). simpl in Hyf. subst y.
        apply in_map_iff. exists (x, f). split; [reflexivity|].
        eapply Permutation_in; [symmetry; apply (SynStc.s_subs_calls_of s)|].
        apply (SynStc.s_reset_incl s). exact Hin. }
      destruct Hrids as (rids & Hrids).
      unfold SECOBCTYPING.hidden_class_vars in Hty. rewrite nodup_In in Hty.
      apply in_app_iff in Hty as [Hty|Hty].
      - eapply (SECSTCTYPINGCORRECTNESS.generated_sys_hidden_disjoint
                  s e aux_names clk_id rst_id clk_type rst_type inp out
                  locals lasts state_env rids ty Hinj Hsec Hauxsec'
                  Haux Hclk Hrst Hinp Hout Hlocals Hlasts Hrids Hrstrange).
        unfold SECSTCTYPING.hidden_sys_vars. rewrite nodup_In.
        apply in_or_app; now left.
      - apply in_app_iff in Hty as [Hty|Hty].
        + eapply (SECSTCTYPINGCORRECTNESS.generated_sys_hidden_disjoint
                    s e aux_names clk_id rst_id clk_type rst_type inp out
                    locals lasts state_env rids ty Hinj Hsec Hauxsec'
                    Haux Hclk Hrst Hinp Hout Hlocals Hlasts Hrids Hrstrange).
          unfold SECSTCTYPING.hidden_sys_vars. rewrite nodup_In.
          apply in_or_app; right. apply in_or_app; now left.
        + (* a state instance: a [sec_reset] gensym, the scope is [sec] *)
          intro Hvis.
          destruct (get_mappings_In _ _ _ _ Hstids Hty) as (o & _ & Hfo).
          eapply (SIG.sec_reset_not_in_signature_scope
                    {| s_name := s.(SynStc.s_name); s_in := inp; s_out := out;
                       s_reset := rst_type; s_clk := clk_type;
                       s_constraints := [] |} ty).
          * intros t Ht. unfold SIG.signature_scope in Ht. cbn in Ht.
            apply in_app_iff in Ht as [Ht|Ht].
            -- destruct (get_mappings_In _ _ _ _
                           (get_mappings_from_node_eq _ _ _ _ Hinp) Ht)
                 as (z & _ & Hfz). eapply Hsec; exact Hfz.
            -- apply in_app_iff in Ht as [Ht|Ht].
               ++ destruct (get_mappings_In _ _ _ _
                              (get_mappings_from_node_eq _ _ _ _ Hout) Ht)
                    as (z & _ & Hfz). eapply Hsec; exact Hfz.
               ++ destruct Ht as [Heq|[Heq|[]]]; subst t;
                    [eapply Hsec; exact Hclk|eapply Hsec; exact Hrst].
          * exact (Hrstrange _ _ Hfo).
          * unfold SIG.signature_scope. cbn. exact Hvis.
    Qed.

    (** The outputs of a translated class are distinct: they are images
        of distinct source names under an injective environment. *)

    Lemma translate_class_out_nodup:
      forall s out,
        env_injective env ->
        get_mappings_from_node (SynStc.s_out s) env = Some out ->
        NoDup out.
    Proof.
      intros s out Hinj Hout.
      eapply get_mappings_nodup_gen;
        [|exact Hinj|exact (get_mappings_from_node_eq _ _ _ _ Hout)].
      pose proof (SynStc.s_nodup s) as Hnd.
      apply NoDup_app_r, NoDup_app_r in Hnd.
      eapply NoDup_app_l; exact Hnd.
    Qed.

    (** Every output of a translated class is a target of its generated
        constraints: the step method writes it, so its type is among the
        statement targets, and it is not hidden, so [simplify] keeps
        it. *)

    Lemma translate_class_out_is_target:
      forall P s aux_names obcsig ty,
        NAMEGEN.naming_env_props env aux_names ->
        SIG.secglobal_scoped G2 ->
        CloStc.wc_system P s ->
        SECOBCTYPING.generate_class_signature G2 (translate_system s) env
          aux_names = OK obcsig ->
        List.In ty obcsig.(s_out) ->
        List.In [ty] (map snd obcsig.(s_constraints)).
    Proof.
      intros P s aux_names obcsig ty Hprops Hglob Hwc Hsig Hty.
      pose proof Hsig as Hsig0.
      edestruct SECOBCTYPINGCORRECTNESS.generate_class_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & stepm & resetm
           & inp & out & locals & lasts & state_env & stids
           & craw_step & craw_reset & st_state & st_step & st_raw
           & Haux & Hclk & Hrst & Hstepm & Hresetm & Hinp & Hout
           & Hlocals & Hlasts & Hsenv & Hstids & Hstepc & Hresetc & Hsigdef);
        [exact Hsig0|].
      rewrite exists_step_method in Hstepm. inversion Hstepm; subst stepm.
      rewrite exists_reset_method in Hresetm. inversion Hresetm; subst resetm.
      simpl in Haux, Hsenv, Hstids, Hlasts.
      rewrite step_method_ins, get_mappings_from_node_idty in Hinp.
      rewrite step_method_vars, get_mappings_from_node_idty in Hlocals.
      rewrite get_mappings_from_node_mems in Hlasts.
      pose proof Hout as Hout0.
      rewrite step_method_outs, get_mappings_from_node_idty in Hout0.
      pose proof (fun t => translate_class_hidden_disjoint
                    s env aux_names clk_id rst_id clk_type rst_type inp out
                    locals lasts state_env stids t
                    Hprops Haux Hclk Hrst Hinp Hout0 Hlocals Hlasts Hsenv Hstids)
        as Hdisj.
      subst obcsig. cbn in Hty |- *.
      (* the source name behind this output type *)
      destruct (get_mappings_In _ _ _ _
                  (get_mappings_from_node_eq _ _ _ _ Hout) Hty)
        as (x & Hxin & Hfx).
      (* the step method writes it *)
      assert (Hwr : List.In x (SECOBCTYPING.stmt_writes
                                 (step_method s).(m_body))).
      { apply translate_step_writes_outs. now apply fst_InMembers. }
      (* so its type is a statement target *)
      destruct (SECOBCTYPINGCORRECTNESS.generate_stmt_constraints_targets
                  G2 env state_env rst_type _ _ _ _ _ Hstepc)
        as (step_tys & Hstept & _).
      destruct (SECOBCTYPINGCORRECTNESS.generate_stmt_constraints_targets
                  G2 env state_env rst_type _ _ _ _ _ Hresetc)
        as (reset_tys & Hresett & _).
      assert (Hintys : List.In ty step_tys)
        by (eapply SECOBCTYPINGCORRECTNESS.stmt_writes_targets;
            [exact Hstept|exact Hwr|exact Hfx]).
      (* hence a raw target *)
      assert (Hraw : List.In [ty] (map snd (SymTypes.collapse
                                              (craw_step ++ craw_reset)))).
      { apply (SECOBCTYPINGCORRECTNESS.generated_class_raw_target_in
                 G2 env state_env rst_type _ _ _ _ _ _ _ _ _ _ _ _ _
                 Hstepc Hresetc Hstept Hresett).
        apply in_map_iff. exists ty. split; [reflexivity|].
        apply in_or_app; now left. }
      (* and it survives simplification, not being hidden *)
      apply SymTypes.simplify_preserves_other_rhs; [|exact Hraw].
      intros d Hd Heq. subst d.
      eapply Hdisj; [exact Hd|].
      apply in_or_app; right. apply in_or_app; now left.
    Qed.

    (** ** Per-trconstr relative totality (non-call cases)

        Where the STC generator succeeded, so does the Obc one.  Its
        inversion hands over exactly what the translated statement needs:
        a clock type (so [Control] reduces), an expression type, and the
        target's entry in the environment. *)

    Lemma translate_tcdef_constraints_ok:
      forall memset clkvars vars x ck ce pc nconst st1 st1' st2,
        CEClo.wc_cexp vars ce ck ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcDef x ck ce) st1 = OK (nconst, st1') ->
        exists cns,
          generate_stmt_constraints G2 env reset_env rst_ty pc
            (translate_tc memset clkvars (SynStc.TcDef x ck ce)) st2
          = OK (cns, st2).
    Proof.
      intros memset clkvars vars x ck ce pc nconst st1 st1' st2 Hwc Hstc.
      simpl in Hstc.
      eapply sec_bind_inv in Hstc as (ckty & sa & Hck & Hstc).
      eapply sec_bind_inv in Hstc as (cety & sb & Hce & Hstc).
      eapply sec_bind_inv in Hstc as (xty & sc & Hx & _).
      assert (Hckopt : SECCETYPING.assign_clk_type env clk_ty ck = Some ckty).
      { unfold option_to_sec in Hck.
        destruct (SECCETYPING.assign_clk_type env clk_ty ck); try discriminate.
        now inversion Hck. }
      assert (Hceopt : SECCETYPING.assign_cexp_type env ce = Some cety).
      { unfold option_to_sec in Hce.
        destruct (SECCETYPING.assign_cexp_type env ce); try discriminate.
        now inversion Hce. }
      assert (Hxopt : Env.find x env = Some xty).
      { unfold find_env in Hx.
        destruct (Env.find x env); try discriminate. now inversion Hx. }
      unfold translate_tc.
      destruct (clock_pc_ok env clk_ty ck ckty pc Hckopt) as (pc' & Hpc').
      rewrite (generate_stmt_constraints_Control G2 env reset_env rst_ty
                 memset ck _ pc pc' st2 Hpc').
      eapply (translate_cexp_constraints_ok G2 env reset_env rst_ty
                memset vars x ce ck clk_ty pc' ckty cety xty st2);
        eassumption.
    Qed.

    Lemma translate_tcnext_constraints_ok:
      forall memset clkvars vars x ck e pc nconst st1 st1' st2,
        CEClo.wc_exp vars e ck ->
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcNext x ck e) st1 = OK (nconst, st1') ->
        exists cns,
          generate_stmt_constraints G2 env reset_env rst_ty pc
            (translate_tc memset clkvars (SynStc.TcNext x ck e)) st2
          = OK (cns, st2).
    Proof.
      intros memset clkvars vars x ck e pc nconst st1 st1' st2 Hwc Hstc.
      simpl in Hstc.
      eapply sec_bind_inv in Hstc as (ckty & sa & Hck & Hstc).
      eapply sec_bind_inv in Hstc as (ety & sb & He & Hstc).
      eapply sec_bind_inv in Hstc as (xty & sc & Hx & _).
      assert (Hckopt : SECCETYPING.assign_clk_type env clk_ty ck = Some ckty).
      { unfold option_to_sec in Hck.
        destruct (SECCETYPING.assign_clk_type env clk_ty ck); try discriminate.
        now inversion Hck. }
      assert (Heopt : SECCETYPING.assign_exp_type env e = Some ety).
      { unfold option_to_sec in He.
        destruct (SECCETYPING.assign_exp_type env e); try discriminate.
        now inversion He. }
      assert (Hxopt : Env.find x env = Some xty).
      { unfold find_env in Hx.
        destruct (Env.find x env); try discriminate. now inversion Hx. }
      unfold translate_tc.
      destruct (clock_pc_ok env clk_ty ck ckty pc Hckopt) as (pc' & Hpc').
      rewrite (generate_stmt_constraints_Control G2 env reset_env rst_ty
                 memset ck _ pc pc' st2 Hpc').
      destruct (translate_exp_type_correspondence env memset vars e ck clk_ty
                  ckty ety Hwc Hckopt Heopt) as (oty & Hoty & _).
      eexists. simpl.
      unfold option_to_sec, find_env, bind, ret.
      rewrite Hoty, Hxopt. reflexivity.
    Qed.

    Lemma translate_tcreset_constraints_ok:
      forall memset clkvars i ck f pc nconst st1 st1' st2,
        SECSTCTYPING.generate_trconstr_constraint G1 env reset_env clk_ty rst_ty
          (SynStc.TcReset i ck f) st1 = OK (nconst, st1') ->
        exists cns,
          generate_stmt_constraints G2 env reset_env rst_ty pc
            (translate_tc memset clkvars (SynStc.TcReset i ck f)) st2
          = OK (cns, st2).
    Proof.
      intros memset clkvars i ck f pc nconst st1 st1' st2 Hstc.
      (* the STC generator has two shapes for a reset; both hand over a
         clock type for the whole clock and the instance's entry *)
      assert (Hdata : (exists ckty,
                          SECCETYPING.assign_clk_type env clk_ty ck = Some ckty)
                      /\ (exists sty, Env.find i reset_env = Some sty)).
      { destruct ck as [|ckr r [|]];
          cbn [SECSTCTYPING.generate_trconstr_constraint] in Hstc.
        - eapply sec_bind_inv in Hstc as (ckty & sa & Hck & Hstc).
          eapply sec_bind_inv in Hstc as (sty & sb & Hs & _).
          split.
          + eexists. reflexivity.
          + exists sty. unfold find_env in Hs.
            destruct (Env.find i reset_env); try discriminate.
            now inversion Hs.
        - eapply sec_bind_inv in Hstc as (rty & sa & Hr & Hstc).
          eapply sec_bind_inv in Hstc as (rckty & sb & Hck & Hstc).
          eapply sec_bind_inv in Hstc as (sty & sc & Hs & _).
          assert (Hropt : Env.find r env = Some rty).
          { unfold find_env in Hr.
            destruct (Env.find r env); try discriminate. now inversion Hr. }
          assert (Hckopt : SECCETYPING.assign_clk_type env clk_ty ckr
                           = Some rckty).
          { unfold option_to_sec in Hck.
            destruct (SECCETYPING.assign_clk_type env clk_ty ckr);
              try discriminate. now inversion Hck. }
          split.
          + eexists. simpl. rewrite Hckopt. simpl. rewrite Hropt. reflexivity.
          + exists sty. unfold find_env in Hs.
            destruct (Env.find i reset_env); try discriminate.
            now inversion Hs.
        - eapply sec_bind_inv in Hstc as (ckty & sa & Hck & Hstc).
          eapply sec_bind_inv in Hstc as (sty & sb & Hs & _).
          split.
          + exists ckty. unfold option_to_sec in Hck.
            destruct (SECCETYPING.assign_clk_type env clk_ty (Con ckr r false));
              try discriminate. now inversion Hck.
          + exists sty. unfold find_env in Hs.
            destruct (Env.find i reset_env); try discriminate.
            now inversion Hs. }
      destruct Hdata as ((ckty & Hckopt) & (sty & Hsty)).
      unfold translate_tc.
      destruct (clock_pc_ok env clk_ty ck ckty pc Hckopt) as (pc' & Hpc').
      rewrite (generate_stmt_constraints_Control G2 env reset_env rst_ty
                 memset ck _ pc pc' st2 Hpc').
      eexists. simpl. rewrite ident_eqb_refl.
      unfold find_env, bind, ret. rewrite Hsty. reflexivity.
    Qed.

    Lemma translate_system_well_defined:
      forall P s,
        wc_system P s ->
        SECOBCTYPING.class_well_defined (translate_system s).
    Proof.
      intros P s Hwc stepm resetm Hstep Hreset.
      rewrite exists_step_method in Hstep; inv Hstep.
      rewrite exists_reset_method in Hreset; inv Hreset.
      destruct Hwc as (_ & _ & Henv & Htcs).
      pose proof (SynStc.s_vars_out_in_tcs s) as Hvo.
      pose proof (SynStc.s_lasts_in_tcs s) as Hls.
      pose proof (SynStc.s_subs_calls_of s) as Hsubs.
      pose proof (SynStc.s_reset_incl s) as Hrincl.
      repeat split.
      - (* the step body assigns every local *)
        intros x Hx.
        rewrite step_method_vars in Hx.
        apply fst_InMembers in Hx. rewrite map_fst_idty in Hx.
        destruct (step_method_body s) as (memset & clkvars & Hb). rewrite Hb.
        unfold translate_tcs.
        apply (proj2 (stmt_writes_translate_tcs_fold
                        memset clkvars (SynStc.s_tcs s) SynObc.Skip)).
        eapply Permutation_in; [apply Hvo|].
        apply in_or_app; now left.
      - (* the reset body assigns every memory *)
        intros x Hx.
        rewrite translate_system_mems in Hx.
        apply fst_InMembers in Hx. rewrite map_map in Hx. simpl in Hx.
        rewrite reset_method_body.
        cbn [SECOBCTYPING.stmt_writes]. apply in_or_app; left.
        unfold reset_mems.
        apply (proj2 (stmt_writes_reset_mems_fold
                        (SynStc.s_lasts s) SynObc.Skip)).
        exact Hx.
      - (* the reset body resets every object *)
        intros o Ho.
        rewrite translate_system_objs in Ho. apply fst_InMembers in Ho.
        rewrite reset_method_body.
        cbn [SECOBCTYPING.stmt_reset_insts]. apply in_or_app; right.
        unfold reset_insts.
        apply (proj2 (stmt_reset_insts_reset_insts_fold
                        (SynStc.s_subs s) SynObc.Skip)).
        exact Ho.
      - (* the step body reads only interface names *)
        intros x Hx.
        assert (Hint: SECOBCTYPING.class_interface
                        (translate_system s) (step_method s)
                = map fst (SynStc.s_in s) ++ map fst (SynStc.s_vars s)
                  ++ map fst (SynStc.s_out s) ++ map fst (SynStc.s_lasts s)).
        { unfold SECOBCTYPING.class_interface.
          rewrite step_method_ins, step_method_vars, step_method_outs,
            translate_system_mems, 3 map_fst_idty, map_map.
          reflexivity. }
        rewrite Hint.
        destruct (step_method_body s) as (memset & clkvars & Hb). rewrite Hb in Hx.
        unfold translate_tcs in Hx.
        apply stmt_free_translate_tcs_fold in Hx
          as [Hx|(tc & Htc & [Hfree|Hdef])].
        + cbn in Hx. contradiction.
        + (* a name the constraint reads: declared, since [s] is well clocked *)
          eapply Forall_forall in Htcs; eauto.
          eapply wc_trconstr_free_in_vars in Htcs; eauto.
          apply InMembers_app in Htcs as [Hin|Hin];
            rewrite InMembers_idck in Hin; apply fst_InMembers in Hin;
            [rewrite 2 map_app in Hin|];
            repeat rewrite in_app_iff in *; tauto.
        + (* a name the constraint defines: a variable, an output or a last *)
          assert (Hd : In x (DefStc.defined (SynStc.s_tcs s)))
            by (unfold DefStc.defined; apply in_flat_map; eauto).
          assert (Hd' : In x (SynStc.variables (SynStc.s_tcs s)
                              ++ SynStc.lasts_of (SynStc.s_tcs s)))
            by (eapply Permutation_in; [apply (DefStc.s_defined s)|exact Hd]).
          apply in_app_iff in Hd' as [Hd'|Hd'].
          * assert (In x (map fst (SynStc.s_vars s)
                          ++ map fst (SynStc.s_out s)))
              by (eapply Permutation_in; [apply (Permutation_sym Hvo)|exact Hd']).
            repeat rewrite in_app_iff in *; tauto.
          * assert (In x (map fst (SynStc.s_lasts s)))
              by (eapply Permutation_in; [apply (Permutation_sym Hls)|exact Hd']).
            repeat rewrite in_app_iff in *; tauto.
      - (* the reset body reads only memories *)
        intros x Hx.
        rewrite reset_method_body in Hx.
        cbn [SECOBCTYPING.stmt_free] in Hx.
        apply in_app_iff in Hx as [Hx|Hx].
        + unfold reset_mems in Hx.
          apply stmt_free_reset_mems_fold in Hx as [Hx|Hx];
            [cbn in Hx; contradiction|].
          rewrite translate_system_mems. apply fst_InMembers.
          rewrite map_map. simpl. exact Hx.
        + unfold reset_insts in Hx.
          apply stmt_free_reset_insts_fold in Hx. cbn in Hx. contradiction.
      - (* the step body touches only the class's own objects *)
        intros o Ho.
        destruct (step_method_body s) as (memset & clkvars & Hb). rewrite Hb in Ho.
        unfold translate_tcs in Ho.
        apply stmt_state_keys_translate_tcs_fold in Ho
          as [Ho|(tc & Htc & Hshape)]; [cbn in Ho; contradiction|].
        rewrite translate_system_objs. apply fst_InMembers.
        assert (Hcall : exists g, In (o, g) (SynStc.calls_of (SynStc.s_tcs s))).
        { destruct Hshape as [(ck & g & Heq)|(ys & ck & b & g & es & Heq)];
            subst tc.
          - exists g. apply Hrincl. eapply SECSTCTYPING.In_resets_of; eauto.
          - exists g. eapply SECSTCTYPING.In_calls_of; eauto. }
        destruct Hcall as (g & Hcall).
        assert (Hin : In (o, g) (SynStc.s_subs s))
          by (eapply Permutation_in; [apply (Permutation_sym Hsubs)|exact Hcall]).
        now apply (in_map fst) in Hin.
      - (* the reset body touches only the class's own objects *)
        intros o Ho.
        rewrite reset_method_body in Ho.
        cbn [SECOBCTYPING.stmt_state_keys] in Ho.
        apply in_app_iff in Ho as [Ho|Ho].
        + unfold reset_mems in Ho.
          apply stmt_state_keys_reset_mems_fold in Ho. cbn in Ho. contradiction.
        + unfold reset_insts in Ho.
          apply stmt_state_keys_reset_insts_fold in Ho as [Ho|Ho];
            [cbn in Ho; contradiction|].
          rewrite translate_system_objs. now apply fst_InMembers.
    Qed.

    (** And conversely.  Every case but the outputs closes by
        contradiction with "the target is not hidden": a variable, a
        memory or an instance would all have been eliminated. *)

    Lemma translate_class_target_is_out:
      forall P s aux_names obcsig rhs,
        NAMEGEN.naming_env_props env aux_names ->
        SIG.secglobal_scoped G2 ->
        CloStc.wc_system P s ->
        SECOBCTYPING.generate_class_signature G2 (translate_system s) env
          aux_names = OK obcsig ->
        List.In rhs (map snd obcsig.(s_constraints)) ->
        List.In rhs (map (fun ty => [ty]) obcsig.(s_out)).
    Proof.
      intros P s aux_names obcsig rhs Hprops Hglob Hwc Hsig Hin.
      pose proof Hsig as Hsig0.
      edestruct SECOBCTYPINGCORRECTNESS.generate_class_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & stepm & resetm
           & inp & out & locals & lasts & state_env & stids
           & craw_step & craw_reset & st_state & st_step & st_raw
           & Haux & Hclk & Hrst & Hstepm & Hresetm & Hinp & Hout
           & Hlocals & Hlasts & Hsenv & Hstids & Hstepc & Hresetc & Hsigdef);
        [exact Hsig0|].
      rewrite exists_step_method in Hstepm. inversion Hstepm; subst stepm.
      rewrite exists_reset_method in Hresetm. inversion Hresetm; subst resetm.
      simpl in Haux, Hsenv, Hstids, Hlasts.
      rewrite step_method_ins, get_mappings_from_node_idty in Hinp.
      rewrite step_method_vars, get_mappings_from_node_idty in Hlocals.
      rewrite get_mappings_from_node_mems in Hlasts.
      pose proof Hout as Hout0.
      rewrite step_method_outs, get_mappings_from_node_idty in Hout0.
      pose proof (fun t => translate_class_hidden_disjoint
                    s env aux_names clk_id rst_id clk_type rst_type inp out
                    locals lasts state_env stids t
                    Hprops Haux Hclk Hrst Hinp Hout0 Hlocals Hlasts Hsenv Hstids)
        as Hdisj.
      assert (Hscoped : SIG.signature_scoped obcsig).
      { eapply SECOBCTYPINGCORRECTNESS.generate_class_signature_scoped;
          [exact Hglob|eapply translate_system_well_defined; exact Hwc
          |exact Hsig]. }
      destruct (SECOBCTYPINGCORRECTNESS.generate_stmt_constraints_targets
                  G2 env state_env rst_type _ _ _ _ _ Hstepc)
        as (step_tys & Hstept & _).
      destruct (SECOBCTYPINGCORRECTNESS.generate_stmt_constraints_targets
                  G2 env state_env rst_type _ _ _ _ _ Hresetc)
        as (reset_tys & Hresett & _).
      pose proof (fun r => SECOBCTYPINGCORRECTNESS.generated_class_raw_target_in
                    G2 env state_env rst_type _ _ _ _ _ _ _ _ _ _ _ _ r
                    Hstepc Hresetc Hstept Hresett) as Hrawin.
      (* every raw target is an output or a hidden name *)
      assert (Hcls : forall t, List.In t (step_tys ++ reset_tys) ->
                     List.In t out
                     \/ List.In t (SECOBCTYPING.hidden_class_vars
                                     locals lasts stids)).
      { intros t Ht.
        unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
        apply in_app_iff in Ht as [Ht|Ht].
        - destruct (SECOBCTYPINGCORRECTNESS.stmt_targets_source
                      env state_env _ _ _ Hstept Ht)
            as [(x & Hx & Hfx)|(o & Ho & Hfo)].
          + destruct (step_method_body s) as (memset & clkvars & Hb).
            rewrite Hb in Hx. unfold translate_tcs in Hx.
            destruct (stmt_writes_translate_tcs_fold_inv
                        memset clkvars (SynStc.s_tcs s) SynObc.Skip x Hx)
              as [Hsk|[Hv|Hl]].
            * simpl in Hsk. contradiction.
            * eapply Permutation_in in Hv;
                [|symmetry; apply (SynStc.s_vars_out_in_tcs s)].
              apply in_app_iff in Hv as [Hv|Hv].
              -- right. apply in_or_app; left.
                 destruct (get_mappings_in _ _ _ _ Hv
                             (get_mappings_from_node_eq _ _ _ _ Hlocals))
                   as (t' & Hf' & Hin').
                 rewrite Hfx in Hf'. inversion Hf'; subst t'. exact Hin'.
              -- left.
                 destruct (get_mappings_in _ _ _ _ Hv
                             (get_mappings_from_node_eq _ _ _ _ Hout0))
                   as (t' & Hf' & Hin').
                 rewrite Hfx in Hf'. inversion Hf'; subst t'. exact Hin'.
            * right. apply in_or_app; right. apply in_or_app; left.
              eapply Permutation_in in Hl;
                [|symmetry; apply (SynStc.s_lasts_in_tcs s)].
              destruct (get_mappings_in _ _ _ _ Hl
                          (get_mappings_from_node_eq _ _ _ _ Hlasts))
                as (t' & Hf' & Hin').
              rewrite Hfx in Hf'. inversion Hf'; subst t'. exact Hin'.
          + right. apply in_or_app; right. apply in_or_app; right.
            apply stmt_reset_insts_state_keys in Ho.
            destruct (step_method_body s) as (memset & clkvars & Hb).
            rewrite Hb in Ho. unfold translate_tcs in Ho.
            destruct (stmt_state_keys_translate_tcs_fold
                        memset clkvars (SynStc.s_tcs s) SynObc.Skip o Ho)
              as [Hsk|(tc & Htc & Hcase)]; [simpl in Hsk; contradiction|].
            assert (Hsub : List.In o (map fst (SynStc.s_subs s))).
            { destruct Hcase as [(ck & g & Heq)|(ys & ck & b & g & es & Heq)];
                subst tc; apply in_map_iff; exists (o, g);
                (split; [reflexivity|]);
                eapply Permutation_in;
                [symmetry; apply (SynStc.s_subs_calls_of s)
                |apply (SynStc.s_reset_incl s);
                 eapply SECSTCTYPING.In_resets_of; exact Htc
                |symmetry; apply (SynStc.s_subs_calls_of s)
                |eapply SECSTCTYPING.In_calls_of; exact Htc]. }
            destruct (get_mappings_in _ _ _ _ Hsub Hstids) as (t' & Hf' & Hin').
            rewrite Hfo in Hf'. inversion Hf'; subst t'. exact Hin'.
        - right.
          destruct (SECOBCTYPINGCORRECTNESS.stmt_targets_source
                      env state_env _ _ _ Hresett Ht)
            as [(x & Hx & Hfx)|(o & Ho & Hfo)].
          + rewrite reset_method_body in Hx.
            cbn [SECOBCTYPING.stmt_writes] in Hx.
            apply in_app_iff in Hx as [Hx|Hx].
            * unfold reset_mems in Hx.
              destruct (stmt_writes_reset_mems_fold_inv _ SynObc.Skip x Hx)
                as [Hsk|Hm]; [simpl in Hsk; contradiction|].
              apply in_or_app; right. apply in_or_app; left.
              destruct (get_mappings_in _ _ _ _ Hm
                          (get_mappings_from_node_eq _ _ _ _ Hlasts))
                as (t' & Hf' & Hin').
              rewrite Hfx in Hf'. inversion Hf'; subst t'. exact Hin'.
            * unfold reset_insts in Hx.
              apply stmt_writes_reset_insts_fold_inv in Hx.
              simpl in Hx. contradiction.
          + rewrite reset_method_body in Ho.
            cbn [SECOBCTYPING.stmt_reset_insts] in Ho.
            apply in_app_iff in Ho as [Ho|Ho].
            * unfold reset_mems in Ho.
              apply stmt_reset_insts_reset_mems_fold_inv in Ho.
              simpl in Ho. contradiction.
            * unfold reset_insts in Ho.
              destruct (stmt_reset_insts_reset_insts_fold_inv
                          _ SynObc.Skip o Ho)
                as [Hsk|Hb]; [simpl in Hsk; contradiction|].
              apply in_or_app; right. apply in_or_app; right.
              destruct (get_mappings_in _ _ _ _ Hb Hstids)
                as (t' & Hf' & Hin').
              rewrite Hfo in Hf'. inversion Hf'; subst t'. exact Hin'. }
      subst obcsig. cbn in Hin |- *.
      pose proof (SymTypes.simplify_rhs_in _ _ _ Hin) as Hinc.
      apply (proj1 (Hrawin _)) in Hinc.
      apply in_map_iff in Hinc as (ty & Hty & Hinty). subst rhs.
      assert (Hnothid : ~ List.In ty (SECOBCTYPING.hidden_class_vars
                                        locals lasts stids)).
      { intro Hhid.
        destruct (SymTypes.findST_of_rhs_in _ _ Hin) as (stc & Hfind).
        apply SymTypes.find_correct in Hfind.
        unfold SIG.signature_scoped in Hscoped. cbn in Hscoped.
        eapply Forall_forall in Hscoped; [|exact Hfind].
        eapply Hdisj; [exact Hhid|].
        eapply constraint_scoped_rhs; [exact Hscoped|now left]. }
      apply in_map_iff. exists ty. split; [reflexivity|].
      destruct (Hcls ty Hinty) as [Hgood|Hbad]; [exact Hgood|contradiction].
    Qed.

    (** ** The generated class signature's targets are its outputs

        The two halves, closed by [NoDup_Permutation].  This is the Obc
        reading of what [generate_sys_signature_good] proves on the STC
        side, and it is what [generate_constraints_ok_from_good] needs of
        a callee signature. *)

    Theorem generate_class_signature_targets_out:
      forall P s aux_names obcsig,
        NAMEGEN.naming_env_props env aux_names ->
        SIG.secglobal_scoped G2 ->
        CloStc.wc_system P s ->
        SECOBCTYPING.generate_class_signature G2 (translate_system s) env
          aux_names = OK obcsig ->
        SIGPROOFS.signature_targets_out obcsig.
    Proof.
      intros P s aux_names obcsig Hprops Hglob Hwc Hsig.
      pose proof Hsig as Hsig0.
      edestruct SECOBCTYPINGCORRECTNESS.generate_class_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & stepm & resetm
           & inp & out & locals & lasts & state_env & stids
           & craw_step & craw_reset & st_state & st_step & st_raw
           & Haux & Hclk & Hrst & Hstepm & Hresetm & Hinp & Hout
           & Hlocals & Hlasts & Hsenv & Hstids & Hstepc & Hresetc & Hsigdef);
        [exact Hsig0|].
      rewrite exists_step_method in Hstepm. inversion Hstepm; subst stepm.
      rewrite step_method_outs, get_mappings_from_node_idty in Hout.
      assert (Hnd1 : NoDup (map snd obcsig.(s_constraints))).
      { rewrite Hsigdef. cbn.
        apply SECOBCTYPINGCORRECTNESS.generated_class_targets_nodup. }
      assert (Hnd2 : NoDup obcsig.(s_out)).
      { rewrite Hsigdef. cbn.
        eapply translate_class_out_nodup;
          [exact (proj1 (proj1 Hprops))|exact Hout]. }
      unfold SIGPROOFS.signature_targets_out.
      apply NoDup_Permutation;
        [exact Hnd1|apply SIG.nodup_singleton_map; exact Hnd2|].
      intro rhs. split.
      - intro Hin. eapply translate_class_target_is_out; eauto.
      - intro Hin. apply in_map_iff in Hin as (ty & Heq & Hty). subst rhs.
        eapply translate_class_out_is_target; eauto.
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

    Lemma clk_ty_in_raw_scope:
      forall inp out slocals slasts rids,
        List.In clk_ty (raw_scope inp out slocals slasts rids).
    Proof.
      intros. unfold raw_scope.
      repeat (apply in_or_app; right). simpl. now left.
    Qed.

    (** A reset instance's type is inside the raw scope by construction:
        the scope contains [rids], which is exactly the image of the
        reset instances.  [reset_consistency] brings a reset'd call under
        the same umbrella. *)

    Lemma reset_inst_in_raw_scope:
      forall tcs rids inp out slocals slasts tc i rinst,
        reset_consistency tcs ->
        get_mappings (map fst (resets_of tcs)) reset_env = Some rids ->
        List.In tc tcs ->
        ((exists ck g, tc = SynStc.TcReset i ck g)
         \/ (exists ys ck g es, tc = SynStc.TcCall i ys ck true g es)) ->
        Env.find i reset_env = Some rinst ->
        List.In rinst (raw_scope inp out slocals slasts rids).
    Proof.
      intros tcs rids inp out slocals slasts tc i rinst
             Hcons Hrids Hin Hshape Hfind.
      assert (Hinres : List.In i (map fst (resets_of tcs))).
      { destruct Hshape as [(ck & g & Heq)|(ys & ck & g & es & Heq)]; subst tc.
        - apply SECSTCTYPING.Reset_in_resets_of.
          apply Exists_exists. exists (SynStc.TcReset i ck g).
          split; [exact Hin|constructor].
        - apply SECSTCTYPING.Reset_in_resets_of.
          eapply (Hcons i true).
          apply Exists_exists. exists (SynStc.TcCall i ys ck true g es).
          split; [exact Hin|constructor]. }
      destruct (get_mappings_in _ _ _ _ Hinres Hrids) as (ty & Hty & Hinty).
      rewrite Hfind in Hty. inversion Hty; subst ty.
      unfold raw_scope.
      apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; now left.
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

    (** ** Feeding the per-block scopedness hypothesis

        [translate_tc_constraints_scoped] asks for two things about each
        trconstr: that every name it mentions has a type in the raw
        scope, and that every instance the translation touches has its
        type in the scope or in that block's own extras.  Both follow
        from the system's well-clockedness and its record invariants. *)

    Lemma sys_vars_env_scoped_from_mappings:
      forall s inp out slocals slasts rids,
        get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
        get_mappings_from_node s.(SynStc.s_out) env = Some out ->
        get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
        get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
        SECSTCTYPING.vars_env_scoped env
          (idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
           ++ idck s.(SynStc.s_lasts))
          (raw_scope inp out slocals slasts rids).
    Proof.
      intros s inp out slocals slasts rids Hinp Hout Hslocals Hslasts x Hmem.
      unfold raw_scope.
      apply InMembers_app in Hmem as [Hmem|Hmem]; rewrite InMembers_idck in Hmem.
      - apply InMembers_app in Hmem as [Hin|Hmem].
        + destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp)
            as (ty & Hfind & Hscope).
          exists ty. split; [exact Hfind|]. apply in_or_app; now left.
        + apply InMembers_app in Hmem as [Hin|Hin].
          * destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hslocals)
              as (ty & Hfind & Hscope).
            exists ty. split; [exact Hfind|].
            apply in_or_app; right. apply in_or_app; right.
            apply in_or_app; now left.
          * destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout)
              as (ty & Hfind & Hscope).
            exists ty. split; [exact Hfind|].
            apply in_or_app; right. apply in_or_app; now left.
      - destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hmem Hslasts)
          as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; now left.
    Qed.

    (** A name a constraint reads is declared because the system is well
        clocked; a name it defines is one of the system's own variables,
        outputs or lasts.  Either way it is in [vars], so the mappings
        give it a type in the raw scope. *)

    Lemma tc_names_env_scoped:
      forall s P vars scope tc x,
        vars = idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
               ++ idck s.(SynStc.s_lasts) ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) s.(SynStc.s_tcs) ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In tc s.(SynStc.s_tcs) ->
        (IsFStc.Is_free_in_tc x tc \/ List.In x (DefStc.defined_tc tc)) ->
        exists ty, Env.find x env = Some ty /\ List.In ty scope.
    Proof.
      intros s P vars scope tc x Hvars Henv Htcs Hscoped Htc Hx.
      apply Hscoped.
      destruct Hx as [Hfree|Hdef].
      - eapply Forall_forall in Htcs; [|exact Htc].
        eapply wc_trconstr_free_in_vars; eauto.
      - subst vars.
        assert (Hd : List.In x (DefStc.defined s.(SynStc.s_tcs)))
          by (unfold DefStc.defined; apply in_flat_map; eauto).
        assert (Hd' : List.In x (SynStc.variables s.(SynStc.s_tcs)
                                 ++ SynStc.lasts_of s.(SynStc.s_tcs)))
          by (eapply Permutation_in; [apply (DefStc.s_defined s)|exact Hd]).
        apply InMembers_app.
        apply in_app_iff in Hd' as [Hd'|Hd'].
        + left. rewrite InMembers_idck.
          assert (List.In x (map fst s.(SynStc.s_vars)
                             ++ map fst s.(SynStc.s_out)))
            by (eapply Permutation_in;
                [apply (Permutation_sym (SynStc.s_vars_out_in_tcs s))|exact Hd']).
          apply fst_InMembers. rewrite 2 map_app.
          repeat rewrite in_app_iff in *. tauto.
        + right. rewrite InMembers_idck. apply fst_InMembers.
          eapply Permutation_in;
            [apply (Permutation_sym (SynStc.s_lasts_in_tcs s))|exact Hd'].
    Qed.

    (** The instances a translated trconstr touches: reset by the system,
        hence typed inside the raw scope, or only stepped, hence the sole
        member of that block's extras. *)

    Lemma tc_state_keys_in_scope_or_extras:
      forall tcs rids inp out slocals slasts tc e o sty memset clkvars,
        reset_consistency tcs ->
        get_mappings (map fst (resets_of tcs)) reset_env = Some rids ->
        List.In tc tcs ->
        tc_obc_extras tc = Some e ->
        List.In o (SECOBCTYPING.stmt_state_keys (translate_tc memset clkvars tc)) ->
        Env.find o reset_env = Some sty ->
        List.In sty (raw_scope inp out slocals slasts rids ++ e).
    Proof.
      intros tcs rids inp out slocals slasts tc e o sty memset clkvars
             Hcons Hrids Htc He Ho Hfind.
      apply stmt_state_keys_translate_tc in Ho.
      destruct Ho as [(ck & g & Heq)|(ys & ck & b & g & es & Heq)]; subst tc.
      - apply in_or_app; left.
        eapply reset_inst_in_raw_scope
          with (tcs := tcs) (tc := SynStc.TcReset o ck g) (i := o);
          [exact Hcons|exact Hrids|exact Htc| |exact Hfind].
        left. exists ck, g. reflexivity.
      - destruct b.
        + apply in_or_app; left.
          eapply reset_inst_in_raw_scope
            with (tcs := tcs) (tc := SynStc.TcCall o ys ck true g es) (i := o);
            [exact Hcons|exact Hrids|exact Htc| |exact Hfind].
          right. exists ys, ck, g, es. reflexivity.
        + (* an unreset call owns its instance's type as its extra *)
          apply in_or_app; right.
          cbn [tc_obc_extras] in He. rewrite Hfind in He.
          inversion He; subst e. now left.
    Qed.

    (** Lifting per-block scopedness to the whole constraint list. *)

    Lemma translated_tcs_constraints_scoped:
      forall s P vars inp out slocals slasts rids extras memset clkvars,
        SIG.secglobal_scoped G2 ->
        vars = idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
               ++ idck s.(SynStc.s_lasts) ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) s.(SynStc.s_tcs) ->
        get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
        get_mappings_from_node s.(SynStc.s_out) env = Some out ->
        get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
        get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
        reset_consistency s.(SynStc.s_tcs) ->
        get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
        tcs_obc_extras s.(SynStc.s_tcs) = Some extras ->
        Forall2 (fun tc e =>
                   forall blk sa sb,
                     generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
                       (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
                     constraints_scoped
                       (raw_scope inp out slocals slasts rids ++ e)
                       (blk ++ map (fun ty => ([rst_ty], [ty])) e))
                s.(SynStc.s_tcs) extras.
    Proof.
      intros s P vars inp out slocals slasts rids extras memset clkvars
             Hglob Hvars Hwcenv Hwctcs Hinp Hout Hslocals Hslasts
             Hcons Hrids Hextras.
      eapply Forall2_impl_In; [|exact (tcs_obc_extras_Forall2 _ _ Hextras)].
      intros tc e Htc He Hextc blk sa sb Hgen.
      eapply translated_tc_constraints_scoped;
        [exact Hglob|apply clk_ty_in_raw_scope|apply rst_ty_in_raw_scope| | |exact Hgen].
      - intros x Hx.
        eapply tc_names_env_scoped with (s := s) (P := P) (vars := vars); eauto.
        subst vars. eapply sys_vars_env_scoped_from_mappings; eauto.
      - intros o sty Ho Hfind.
        eapply tc_state_keys_in_scope_or_extras; eauto.
    Qed.

    (** ** The reset method's constraints

        [translate_reset] emits one [rst_ty ==> ty] constraint per memory
        and per object.  Taking [slasts ++ rids] as the shared targets,
        every one of them is either shared or a per-block extra: a
        memory's type is backed by the [TcNext] that defines it, a reset
        object's by the [TcReset] that resets it, and an object the
        system only steps is exactly what [tcs_obc_extras] collects.
        These are the two reset-body hypotheses of
        [class_preserv_signature]. *)

    Lemma reset_shared_targets:
      forall s inp out slocals slasts rids nconst st st',
        get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
        get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
        SECSTCTYPING.generate_trconstrs_constraints G1 env reset_env clk_ty rst_ty
          s.(SynStc.s_tcs) st = OK (nconst, st') ->
        Forall (fun ty =>
                  List.In ty (raw_scope inp out slocals slasts rids)
                  /\ exists src, List.In (src, [ty]) nconst /\ List.In rst_ty src)
               (slasts ++ rids).
    Proof.
      intros s inp out slocals slasts rids nconst st st' Hslasts Hrids Hgen.
      apply get_mappings_from_node_eq in Hslasts.
      apply Forall_forall. intros ty Hin.
      apply in_app_iff in Hin as [Hin|Hin]; split.
      - (* a memory's type lies in the [slasts] slot of the raw scope *)
        unfold raw_scope.
        apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; now left.
      - destruct (get_mappings_In _ _ _ _ Hslasts Hin) as (x & Hinx & Hfind).
        eapply SECSTCTYPING.generate_trconstrs_constraints_last_source;
          [exact Hgen| |exact Hfind].
        now rewrite <- (SynStc.s_lasts_in_tcs s).
      - (* a reset instance's type lies in the [rids] slot *)
        unfold raw_scope.
        apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; now left.
      - destruct (get_mappings_In _ _ _ _ Hrids Hin) as (o & Hino & Hfind).
        eapply SECSTCTYPING.generate_trconstrs_constraints_reset_source;
          [exact Hgen|exact Hino|exact Hfind].
    Qed.

    Lemma reset_body_constraints_classified:
      forall s slasts rids extras craw_reset st st',
        reset_consistency s.(SynStc.s_tcs) ->
        get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
        get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
        tcs_obc_extras s.(SynStc.s_tcs) = Some extras ->
        generate_stmt_constraints G2 env reset_env rst_ty []
          (translate_reset s) st = OK (craw_reset, st') ->
        forall c, List.In c craw_reset ->
                  exists ty, c = ([rst_ty], [ty])
                             /\ (List.In ty (slasts ++ rids)
                                 \/ List.In ty (List.concat extras)).
    Proof.
      intros s slasts rids extras craw_reset st st'
             Hcons Hslasts Hrids Hextras Hgen c Hc.
      destruct (generate_translate_reset_blocks _ _ _ _ Hgen)
        as (mtys & itys & Hmtys & Hitys & Hcns).
      subst craw_reset.
      apply in_map_iff in Hc as (ty & Heq & Hty).
      exists ty. split; [now symmetry|].
      apply get_mappings_from_node_eq in Hslasts.
      apply in_app_iff in Hty as [Hty|Hty].
      - (* a memory initialisation *)
        left. apply in_or_app; left.
        destruct (Forall2_in_right _ _ _ _ Hmtys Hty) as (xc & Hinxc & Hfind).
        assert (Hinx : List.In (fst xc) (map fst s.(SynStc.s_lasts)))
          by now apply in_map.
        destruct (get_mappings_in _ _ _ _ Hinx Hslasts) as (ty' & Hty' & Hinty').
        rewrite Hfind in Hty'. inversion Hty'; subst ty'. exact Hinty'.
      - (* an instance reset: shared when the system resets it too *)
        destruct (Forall2_in_right _ _ _ _ Hitys Hty) as (oc & Hinoc & Hfind).
        assert (Hincalls : List.In (fst oc) (map fst (calls_of s.(SynStc.s_tcs)))).
        { apply in_map. eapply Permutation_in;
            [apply (SynStc.s_subs_calls_of s)|exact Hinoc]. }
        destruct (calls_of_reset_or_unreset _ _ Hcons Hincalls) as [Hres|Hun].
        + left. apply in_or_app; right.
          destruct (get_mappings_in _ _ _ _ Hres Hrids) as (ty' & Hty' & Hinty').
          rewrite Hfind in Hty'. inversion Hty'; subst ty'. exact Hinty'.
        + right.
          pose proof (tcs_obc_extras_concat _ _ Hextras) as Hconc.
          destruct (get_mappings_in _ _ _ _ Hun Hconc) as (ty' & Hty' & Hinty').
          rewrite Hfind in Hty'. inversion Hty'; subst ty'. exact Hinty'.
    Qed.

    (** ** Interface agreement

        Both generators read the same environment and the same auxiliary
        names, and the translated class's step method carries the
        system's own interface up to [idty].  So the two signatures agree
        on name, inputs, outputs, clock and reset. *)

    Lemma generated_signature_fields_agree:
      forall s aux stcsig obcsig,
        SECSTCTYPING.generate_sys_signature G1 s env aux = OK stcsig ->
        SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux = OK obcsig ->
        stcsig.(s_name) = obcsig.(s_name)
        /\ SIG.signature_fields_agree stcsig obcsig.
    Proof.
      intros s aux stcsig obcsig Hnsig Hssig.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
           & renv & rids & st_reset & sconst & st_s
           & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
           & Hrenv & Hrids & Hsconst & Hnsigdef); [exact Hnsig|].
      edestruct SECOBCTYPINGCORRECTNESS.generate_class_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & stepm & resetm
           & inp' & out' & locals' & lasts' & senv & stids
           & craw_step & craw_reset & st_state & st_step & st_raw
           & Haux' & Hclk' & Hrst' & Hstepm & Hresetm & Hinp' & Hout'
           & Hlocals' & Hlasts' & Hsenv & Hstids & Hstepc & Hresetc & Hssigdef);
        [exact Hssig|].
      simpl in Haux'.
      rewrite Haux in Haux'. inversion Haux'; subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'; subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'; subst rst_type'.
      pose proof (exists_step_method s) as Hex.
      rewrite Hstepm in Hex. inversion Hex; subst stepm.
      assert (Hinpeq : inp' = inp).
      { assert (Hmap : get_mappings_from_node (m_in (step_method s)) env = Some inp).
        { eapply get_mappings_from_node_map_fst; [|exact Hinp].
          symmetry. apply translated_class_step_in. }
        rewrite Hmap in Hinp'. now inversion Hinp'. }
      assert (Houteq : out' = out).
      { assert (Hmap : get_mappings_from_node (m_out (step_method s)) env = Some out).
        { eapply get_mappings_from_node_map_fst; [|exact Hout].
          symmetry. apply translated_class_step_out. }
        rewrite Hmap in Hout'. now inversion Hout'. }
      subst inp' out' stcsig obcsig. simpl.
      repeat split; reflexivity.
    Qed.

    (** ** Lockstep over the program

        Signature environments grow in step: extending both with a
        head-consistent pair preserves consistency, since the two
        signatures share a name and so are found together. *)

    Theorem Signature_consistent_obc_full_cons:
      forall H1 H2 stcsig obcsig,
        Signature_consistent_obc_full H1 H2 ->
        Signature_head_consistent_obc stcsig obcsig ->
        Signature_consistent_obc_full (stcsig :: H1) (obcsig :: H2).
    Proof.
      intros H1 H2 stcsig obcsig Hcons Hhead f n1 Hfind.
      simpl in Hfind.
      destruct (ident_eqb stcsig.(s_name) f) eqn:Hname.
      - destruct Hhead as (Hsgname & Hhead).
        apply ident_eqb_eq in Hname. inversion Hfind; subst n1.
        exists obcsig. simpl. rewrite <- Hsgname, Hname, ident_eqb_refl.
        split; [reflexivity|].
        split; [exact Hsgname|exact Hhead].
      - apply ident_eqb_neq in Hname.
        destruct Hhead as (Hsgname & Hhead).
        specialize (Hcons f n1 Hfind) as (n2 & Hfind2 & Hhead2).
        assert (Hneqb : ident_eqb obcsig.(s_name) f = false).
        { apply ident_eqb_neq. rewrite <- Hsgname. exact Hname. }
        exists n2. simpl. rewrite Hneqb. auto.
    Qed.

    (** One translation step: a generated signature pair that is
        head-consistent extends a consistent pair of environments. *)

    Theorem generated_signature_consistent_step:
      forall H1 H2 s aux stcsig obcsig,
        Signature_consistent_obc_full H1 H2 ->
        SECSTCTYPING.generate_sys_signature G1 s env aux = OK stcsig ->
        SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux = OK obcsig ->
        Signature_head_consistent_obc stcsig obcsig ->
        Signature_consistent_obc_full (stcsig :: H1) (obcsig :: H2).
    Proof.
      intros. eapply Signature_consistent_obc_full_cons; eauto.
    Qed.

    (** ** Class-level raw preservation

        The Obc signature's raw constraints are the step method's, the
        reset method's, and then [collapse].  Every reset-method
        constraint is either backed by an STC constraint on the same
        target ([shared]) or owned by the call block of the instance it
        names (an extra). *)

    Theorem class_preserv_raw:
      forall scope vars P memset clkvars tcs extras shared
             nconst craw_step craw_reset st1 st1' st2 st2',
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) tcs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        List.In clk_ty scope ->
        (forall tc i rinst,
            List.In tc tcs ->
            ((exists ck g, tc = SynStc.TcReset i ck g)
             \/ (exists ys ck g es, tc = SynStc.TcCall i ys ck true g es)) ->
            Env.find i reset_env = Some rinst -> List.In rinst scope) ->
        secglobal_scope_sec G2 ->
        List.In rst_ty scope ->
        (forall x sty, Env.find x reset_env = Some sty ->
                       exists n, sty = Ids.gensym Ids.sec_reset n) ->

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
      intros scope vars P memset clkvars tcs extras shared
             nconst craw_step craw_reset st1 st1' st2 st2'
             Hcons Hscopefresh Hwcenv Hwctcs Hvars Hclkin Hresetscope
             Hg2sec Hrstin Hrange Hextras Hnd Hfresh Hsc Hshared Hreset Hstc Hobc.
      destruct (tcs_preserv_aug scope vars P memset clkvars tcs extras
                  nconst craw_step st1 st1' st2 st2'
                  Hcons Hscopefresh Hwcenv Hwctcs Hvars Hclkin Hresetscope
                  Hg2sec Hrstin Hrange Hextras Hnd Hfresh Hsc Hstc Hobc)
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
      forall sigscope inp out slocals slasts rids vars P memset clkvars
             tcs extras shared
             nconst craw_step craw_reset hidden_stc hidden_obc st1 st1' st2 st2',
        let rawscope := raw_scope inp out slocals slasts rids in
        Signature_consistent_obc_full G1 G2 ->
        SIG.secglobal_scope_fresh rawscope G1 ->
        wc_env vars ->
        Forall (CloStc.wc_trconstr P vars) tcs ->
        SECSTCTYPING.vars_env_scoped env vars rawscope ->
        reset_consistency tcs ->
        get_mappings (map fst (resets_of tcs)) reset_env = Some rids ->
        secglobal_scope_sec G2 ->
        (forall x sty, Env.find x reset_env = Some sty ->
                       exists n, sty = Ids.gensym Ids.sec_reset n) ->
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
      intros.
      eapply preserves_on_simplify_bridge with (rawscope := rawscope); eauto.
      eapply class_preserv_raw; eauto.
      all: first [ apply clk_ty_in_raw_scope
                 | apply rst_ty_in_raw_scope
                 | (intros tc i rinst Hin Hshape Hfind;
                    eapply reset_inst_in_raw_scope; eauto) ].
    Qed.

  End TCPRESERV.

  (** ** Signature preservation for one translated system

      The Stc-to-Obc counterpart of NLustre's
      [generated_signatures_preserved_from_simplify_bridge_scoped]: both
      generators are inverted, their components matched through the
      translation, and the raw scope handed to [class_preserv_signature].
      The hypotheses are the same ones NLustre takes, with [wc_system]
      for [wc_node] and the two Stc-side side conditions in place of
      their node counterparts. *)

  Theorem generated_signatures_preserved_obc:
    forall P (s: SynStc.system) (G1 G2: SIG.secglobal)
           (env: Env.t ident) (aux_names: list node_aux_names)
           (stcsig obcsig: SIG.signature),
      Signature_consistent_obc_full G1 G2 ->
      SECSTCTYPINGCORRECTNESS.sys_scope_fresh_in_env s env aux_names G1 ->
      SIG.secglobal_scope_sec G2 ->
      SIG.secglobal_scoped G2 ->
      NAMEGEN.naming_env_props env aux_names ->
      CloStc.wc_system P s ->
      (** as for [generate_sys_signature_good]: a doubly-reset instance
          would give two constraints the same target *)
      WD.Is_well_sch (map fst s.(SynStc.s_in))
                     (ps_from_list (map fst s.(SynStc.s_lasts)))
                     s.(SynStc.s_tcs) ->
      SECSTCTYPING.generate_sys_signature G1 s env aux_names = OK stcsig ->
      SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux_names
        = OK obcsig ->
      SECSTCTYPINGCORRECTNESS.generated_sys_simplify_ready env aux_names ->
      signatures_preserved stcsig obcsig.
  Proof.
    intros P s G1 G2 env aux_names stcsig obcsig
           Hcons Hfreshenv Hg2sec Hg2scoped
           ((Hinjp & Hsecp) & (Hauxsecp & Hinstp & Hdistp))
           Hwc Hsch Hstcsig Hobcsig Hready.
    (* both generators, inverted *)
    edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
        (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
         & reset_env & rids & st_reset & sconst & st_s
         & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
         & Hrenv & Hrids & Hsconst & Hstcdef); [exact Hstcsig|].
    edestruct SECOBCTYPINGCORRECTNESS.generate_class_signature_inv as
        (clk_id' & rst_id' & clk_type' & rst_type' & stepm & resetm
         & inp' & out' & locals' & lasts' & state_env & stids
         & craw_step & craw_reset & st_state & st_step & st_raw
         & Haux' & Hclk' & Hrst' & Hstepm & Hresetm & Hinp' & Hout'
         & Hlocals' & Hlasts' & Hsenv & Hstids & Hstepc & Hresetc & Hobcdef);
      [exact Hobcsig|].
    (* the class's name, auxiliaries and instance environment are the system's *)
    simpl in Haux', Hsenv.
    rewrite Haux in Haux'. inversion Haux'; subst clk_id' rst_id'.
    rewrite Hclk in Hclk'. inversion Hclk'; subst clk_type'.
    rewrite Hrst in Hrst'. inversion Hrst'; subst rst_type'.
    rewrite Hrenv in Hsenv. inversion Hsenv; subst state_env.
    pose proof (exists_step_method s) as Hexs.
    rewrite Hstepm in Hexs. inversion Hexs; subst stepm.
    pose proof (exists_reset_method s) as Hexr.
    rewrite Hresetm in Hexr. inversion Hexr; subst resetm.
    rewrite translate_system_objs in Hstids.
    (* the two generators read the same interface lists *)
    assert (Hinpeq : inp' = inp).
    { assert (Hmap : get_mappings_from_node (m_in (step_method s)) env = Some inp)
        by (eapply get_mappings_from_node_map_fst;
            [symmetry; apply translated_class_step_in|exact Hinp]).
      rewrite Hmap in Hinp'. now inversion Hinp'. }
    assert (Houteq : out' = out).
    { assert (Hmap : get_mappings_from_node (m_out (step_method s)) env = Some out)
        by (eapply get_mappings_from_node_map_fst;
            [symmetry; apply translated_class_step_out|exact Hout]).
      rewrite Hmap in Hout'. now inversion Hout'. }
    subst inp' out'.
    (* the instance environment is injective and made of sec_reset names *)
    destruct (Hinstp _ _ Hrenv)
      as (Hinstinj & Hinstrange).
    (* everything the two signatures share is a sec name *)
    assert (Hsec : forall ty,
               List.In ty (inp ++ out ++ slocals ++ slasts
                             ++ [clk_type; rst_type]) ->
               exists n, ty = Ids.gensym Ids.sec n).
    { intros ty Hin.
      assert (Hfind : exists x, Env.find x env = Some ty).
      { repeat (apply in_app_iff in Hin as [Hin|Hin]);
          [ apply get_mappings_from_node_eq in Hinp
          | apply get_mappings_from_node_eq in Hout
          | apply get_mappings_from_node_eq in Hslocals
          | apply get_mappings_from_node_eq in Hslasts
          | ].
        1-4: match goal with
             | H: get_mappings _ _ = Some _ |- _ =>
                 destruct (get_mappings_In _ _ _ _ H Hin) as (x & _ & Hf);
                 now exists x
             end.
        destruct Hin as [Heq|[Heq|[]]]; subst ty; eauto. }
      destruct Hfind as (x & Hfind).
      eapply Hsecp; eauto. }
    (* the per-block extras exist, are distinct, and avoid the raw scope *)
    destruct (tcs_obc_extras_exists reset_env s.(SynStc.s_tcs) s.(SynStc.s_subs)
                reset_env stids) as (extras & Hextras).
    { intros i Hin.
      eapply Permutation_in;
        [apply Permutation_map, (Permutation_sym (SynStc.s_subs_calls_of s))|].
      now apply unreset_call_insts_incl_calls. }
    { exact Hstids. }
    { reflexivity. }
    assert (Hndcalls : NoDup (map fst (calls_of s.(SynStc.s_tcs)))).
    { eapply Permutation_NoDup;
        [apply Permutation_map, (SynStc.s_subs_calls_of s)
        |apply fst_NoDupMembers, (SynStc.s_nodup_subs s)]. }
    assert (Hndextras : NoDup (List.concat extras)).
    { eapply get_mappings_nodup_gen;
        [apply unreset_call_insts_nodup; exact Hndcalls
        |exact Hinstinj
        |apply tcs_obc_extras_concat; exact Hextras]. }
    (* now the two halves of [signatures_preserved] *)
    split.
    - destruct (generated_signature_fields_agree G1 G2 env s aux_names
                  stcsig obcsig Hstcsig Hobcsig) as (_ & Hagree).
      exact Hagree.
    - subst stcsig obcsig. unfold SIG.signature_scope; simpl.
      destruct Hwc as (_ & _ & Hwcenv & Hwctcs).
      pose proof (SynStc.s_reset_consistency s) as Hrcons.
      destruct (step_method_body s) as (memset & clkvars & Hbody).
      rewrite Hbody in Hstepc.
      (* every side condition of [class_preserv_signature], up front *)
      assert (Hfresh : SIG.secglobal_scope_fresh
                         (raw_scope clk_type rst_type inp out slocals slasts rids)
                         G1).
      { unfold raw_scope. eapply Hfreshenv; eauto. }
      assert (Hvarscoped :
                SECSTCTYPING.vars_env_scoped env
                  (idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
                   ++ idck s.(SynStc.s_lasts))
                  (raw_scope clk_type rst_type inp out slocals slasts rids)).
      { eapply sys_vars_env_scoped_from_mappings; eauto. }
      assert (Hextrafresh :
                forall x, List.In x (List.concat extras) ->
                          ~ List.In x (raw_scope clk_type rst_type inp out
                                         slocals slasts rids)).
      { intros ty Hin. eapply extras_fresh_raw_scope; eauto. }
      assert (Hblockscoped :
                Forall2 (fun tc e =>
                           forall blk sa sb,
                             generate_stmt_constraints G2 env reset_env rst_type
                               [clk_type] (translate_tc memset clkvars tc) sa
                             = OK (blk, sb) ->
                             constraints_scoped
                               (raw_scope clk_type rst_type inp out slocals
                                  slasts rids ++ e)
                               (blk ++ map (fun ty => ([rst_type], [ty])) e))
                        s.(SynStc.s_tcs) extras).
      { eapply translated_tcs_constraints_scoped; eauto. }
      assert (Hsharedok :
                Forall (fun ty =>
                          List.In ty (raw_scope clk_type rst_type inp out
                                        slocals slasts rids)
                          /\ exists src, List.In (src, [ty]) sconst
                                         /\ List.In rst_type src)
                       (slasts ++ rids)).
      { eapply reset_shared_targets; eauto. }
      assert (Hresetok :
                forall c, List.In c craw_reset ->
                          exists ty, c = ([rst_type], [ty])
                                     /\ (List.In ty (slasts ++ rids)
                                         \/ List.In ty (List.concat extras))).
      { eapply reset_body_constraints_classified; eauto. }
      (* both halves come from [generated_sys_simplify_ready], as in NLustre *)
      assert (Hndrst : NoDup (map fst (resets_of s.(SynStc.s_tcs))))
        by (eapply SECSTCTYPINGCORRECTNESS.Is_well_sch_resets_nodup; exact Hsch).
      edestruct Hready as (Hwf & Hdisjready); eauto.
      assert (Hdisj :
                forall x, List.In x (SECSTCTYPING.hidden_sys_vars slocals slasts rids) ->
                          ~ List.In x (inp ++ out ++ [clk_type; rst_type])).
      { intros ty Hin. exact (Hdisjready ty Hin). }
      eapply class_preserv_signature
        with (sigscope := inp ++ out ++ [clk_type; rst_type])
             (inp := inp) (out := out) (slocals := slocals) (slasts := slasts)
             (rids := rids) (extras := extras)
             (shared := slasts ++ rids)
             (vars := idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars)
                            ++ s.(SynStc.s_out)) ++ idck s.(SynStc.s_lasts))
             (P := P) (tcs := s.(SynStc.s_tcs))
             (memset := memset) (clkvars := clkvars)
             (craw_reset := craw_reset)
             (st1 := st_reset) (st1' := st_s)
             (st2 := st_state) (st2' := st_step);
        eauto using sig_scope_in_raw_scope.
  Qed.

  (** ** Lockstep over the whole program

      The Stc-to-Obc counterpart of NLustre's
      [generate_all_signatures_consistent'_abstract].  Both generators
      walk the same program, the accumulators grow together, and one
      head-consistent pair per system keeps every lookup aligned. *)

  Definition generated_signature_step_consistent_obc
    (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
    forall G1 G2 s stcsig obcsig,
      Signature_consistent_obc_full G1 G2 ->
      SECSTCTYPING.generate_sys_signature G1 s env aux_names = OK stcsig ->
      SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux_names
        = OK obcsig ->
      Signature_head_consistent_obc stcsig obcsig.

  Lemma Signature_consistent_obc_full_nil:
    Signature_consistent_obc_full nil nil.
  Proof.
    intros f n1 Hfind. simpl in Hfind. discriminate.
  Qed.

  (** One head-consistent pair per system, from the preservation bridge
      plus the two signature-shape facts each layer proves about its own
      generator. *)

  Theorem generated_signature_step_consistent_obc_from_bridges:
    forall env aux_names,
      (forall G1 G2 s stcsig obcsig,
          Signature_consistent_obc_full G1 G2 ->
          SECSTCTYPING.generate_sys_signature G1 s env aux_names = OK stcsig ->
          SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux_names
            = OK obcsig ->
          signatures_preserved stcsig obcsig) ->
      (forall G1 s stcsig,
          SECSTCTYPING.generate_sys_signature G1 s env aux_names = OK stcsig ->
          SIG.signature_good stcsig /\ NoDup (SIG.signature_scope stcsig)) ->
      (forall G2 s obcsig,
          SECOBCTYPING.generate_class_signature G2 (translate_system s) env aux_names
            = OK obcsig ->
          SIG.signature_scoped obcsig) ->
      generated_signature_step_consistent_obc env aux_names.
  Proof.
    intros env aux_names Hpres Hgood Hscoped
           G1 G2 s stcsig obcsig Hcons Hstcsig Hobcsig.
    assert (Hagree : stcsig.(s_name) = obcsig.(s_name)
                     /\ SIG.signature_fields_agree stcsig obcsig)
      by (eapply generated_signature_fields_agree; eauto).
    destruct (Hgood G1 s stcsig Hstcsig) as (Hsiggood & Hsignd).
    eapply signatures_preserved_obc_full_from_good;
      [apply (proj1 Hagree)|exact Hsiggood|exact Hsignd| |].
    - eapply Hscoped; eauto.
    - eapply Hpres; eauto.
  Qed.

  Theorem generate_all_signatures_consistent_obc'_abstract:
    forall systems acc1 acc2 env aux_names G1 G2,
      Signature_consistent_obc_full acc1 acc2 ->
      generated_signature_step_consistent_obc env aux_names ->
      SECSTCTYPING.generate_all_sys_signatures' acc1 systems env aux_names = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures' acc2 (translate systems)
        env aux_names = OK G2 ->
      Signature_consistent_obc_full G1 G2.
  Proof.
    induction systems as [|s systems IH];
      intros acc1 acc2 env aux_names G1 G2 Hcons Hstep Hstc Hobc.
    - simpl in Hstc, Hobc. inversion Hstc; inversion Hobc; subst. exact Hcons.
    - simpl in Hstc, Hobc.
      destruct (SECSTCTYPING.generate_sys_signature acc1 s env aux_names)
        as [stcsig|] eqn:Hstcsig; try discriminate.
      destruct (SECOBCTYPING.generate_class_signature acc2 (translate_system s)
                  env aux_names) as [obcsig|] eqn:Hobcsig;
        simpl in Hstc, Hobc; try discriminate.
      destruct (SECSTCTYPING.generate_all_sys_signatures' (stcsig :: acc1)
                  systems env aux_names) as [G1'|] eqn:Hstc';
        simpl in Hstc; try discriminate.
      destruct (SECOBCTYPING.generate_all_class_signatures' (obcsig :: acc2)
                  (translate systems) env aux_names) as [G2'|] eqn:Hobc';
        simpl in Hobc; try discriminate.
      inversion Hstc; subst; clear Hstc.
      inversion Hobc; subst; clear Hobc.
      eapply IH with (acc1 := stcsig :: acc1) (acc2 := obcsig :: acc2); eauto.
      eapply generated_signature_consistent_step; eauto.
  Qed.

  Corollary generate_all_signatures_consistent_obc_abstract:
    forall systems env aux_names G1 G2,
      generated_signature_step_consistent_obc env aux_names ->
      SECSTCTYPING.generate_all_sys_signatures systems env aux_names = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures (translate systems)
        env aux_names = OK G2 ->
      Signature_consistent_obc_full G1 G2.
  Proof.
    intros systems env aux_names G1 G2 Hstep Hstc Hobc.
    unfold SECSTCTYPING.generate_all_sys_signatures in Hstc.
    unfold SECOBCTYPING.generate_all_class_signatures in Hobc.
    eapply generate_all_signatures_consistent_obc'_abstract
      with (acc1 := @nil SIG.signature) (acc2 := @nil SIG.signature); eauto.
    apply Signature_consistent_obc_full_nil.
  Qed.

  (** This is the main lockstep induction for the translation layer.  It
      runs the STC and Obc signature generators over the same
      node-scoped environment, proves that each fresh signature pair is
      individually well formed, and extends the accumulator with a
      [Signature_head_consistent_obc] pair.  Nothing about the
      accumulators is assumed: consistency, scopedness and the freshness
      bound are carried as invariants and re-established at each step,
      which is why there is no per-step predicate to supply.

      The naming run itself does not appear.  All the induction needs
      from it is [scoped_envs_windowed]: each system's environment, and
      the state window that environment's names occupy, with consecutive
      windows abutting.  Producing that from the NLustre naming pass is
      somebody else's job, which is what keeps this layer free of
      NLustre nodes. *)

  Theorem generate_all_signatures_consistent_obc_scoped':
    forall systems acc1 acc2 envs aux_names st G1 G2,
      SECSTCTYPINGCORRECTNESS.scoped_envs_windowed envs st systems ->
      NAMEGEN.aux_naming_props aux_names ->
      CloStc.wc_program systems ->
      WD.Well_scheduled systems ->
      Signature_consistent_obc_full acc1 acc2 ->
      SIG.secglobal_scoped acc1 ->
      SIG.secglobal_scoped acc2 ->
      SIG.secglobal_scope_sec acc1 ->
      SIG.secglobal_scope_sec acc2 ->
      SIG.secglobal_scope_bounded_above acc1 st ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env' acc1 systems envs
        aux_names = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env' acc2
        (translate systems) envs aux_names = OK G2 ->
      Signature_consistent_obc_full G1 G2
      /\ SIG.secglobal_scoped G2
      /\ SIG.secglobal_scope_sec G2.
  Proof.
    induction systems as [|s systems IH];
      intros acc1 acc2 envs aux_names st G1 G2
             Hwindow Haux Hwc Hsch Hcons Hacc1scoped Hacc2scoped
             Hacc1sec Hacc2sec Hbound Hstc Hobc.
    - simpl in Hstc, Hobc. inversion Hstc; inversion Hobc; subst.
      repeat split; assumption.
    - inversion Hwindow as [|st0 st' s0 systems0 local_env
                             Hfindlocal Henvprops Hwin Htail];
        subst st0 s0 systems0.
      inversion Hwc as [|s' systems'' Hwc_tail Hwc_head]; subst s' systems''.
      inversion Hsch as [|s' systems'' Hsch_head Hsch_tail]; subst s' systems''.
      simpl in Hstc, Hobc.
      destruct (SECSTCTYPING.generate_sys_signature_scoped_env acc1 s envs aux_names)
        as [stcsig|] eqn:Hstcsig; try discriminate.
      destruct (SECOBCTYPING.generate_class_signature_scoped_env acc2
                  (translate_system s) envs aux_names) as [obcsig|] eqn:Hobcsig;
        simpl in Hstc, Hobc; try discriminate.
      destruct (SECSTCTYPING.generate_all_sys_signatures_scoped_env'
                  (stcsig :: acc1) systems envs aux_names) as [G1'|] eqn:Hstc';
        simpl in Hstc; try discriminate.
      destruct (SECOBCTYPING.generate_all_class_signatures_scoped_env'
                  (obcsig :: acc2) (translate systems) envs aux_names)
        as [G2'|] eqn:Hobc'; simpl in Hobc; try discriminate.
      inversion Hstc; subst G1'; clear Hstc.
      inversion Hobc; subst G2'; clear Hobc.
      (* both scoped generators read this system's environment *)
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hstcsig.
      rewrite Hfindlocal in Hstcsig.
      unfold SECOBCTYPING.generate_class_signature_scoped_env in Hobcsig.
      assert (Hfindlocal_cls :
                find_node_env (translate_system s).(c_name) envs = Some local_env)
        by (simpl; exact Hfindlocal).
      rewrite Hfindlocal_cls in Hobcsig.
      assert (Hprops : NAMEGEN.naming_env_props local_env aux_names)
        by exact (conj Henvprops Haux).
      assert (Henvinj : env_injective local_env) by exact (proj1 Henvprops).
      assert (Hready : SECSTCTYPINGCORRECTNESS.generated_sys_simplify_ready
                         local_env aux_names).
      { eapply SECSTCTYPINGCORRECTNESS.generated_sys_simplify_ready_from_naming_props;
          exact Hprops. }
      (* the two signatures, each scoped in its own layer *)
      assert (Hstcscoped : SIG.signature_scoped stcsig).
      { eapply SECSTCTYPING.generate_sys_signature_scoped
          with (P := systems) (s := s) (env := local_env);
          [exact Hacc1scoped|exact Henvinj|exact Hwc_head|exact Hstcsig]. }
      assert (Hobcscoped : SIG.signature_scoped obcsig).
      { eapply SECOBCTYPINGCORRECTNESS.generate_class_signature_scoped;
          [exact Hacc2scoped| |exact Hobcsig].
        eapply translate_system_well_defined; eauto. }
      assert (Hstcgood : SIG.signature_good stcsig).
      { eapply SECSTCTYPINGCORRECTNESS.generate_sys_signature_good
          with (P := systems) (s := s) (env := local_env);
          [exact Hprops|exact Hacc1scoped|exact Hwc_head
          |eapply SECSTCTYPINGCORRECTNESS.Is_well_sch_resets_nodup;
           exact Hsch_head
          |exact Hstcsig]. }
      assert (Hstcnd : NoDup (SIG.signature_scope stcsig)).
      { eapply SECSTCTYPINGCORRECTNESS.generate_sys_signature_scope_nodup;
          [exact Hprops|exact Hstcsig]. }
      (* freshness of this system's scope against the accumulator *)
      assert (Hfreshenv : SECSTCTYPINGCORRECTNESS.sys_scope_fresh_in_env
                            s local_env aux_names acc1).
      { eapply SECSTCTYPINGCORRECTNESS.sys_scope_fresh_in_env_from_bounds
          with (st := st).
        - intros ie x ty Hinst Hfind.
          exact (proj2 (proj1 (proj2 Haux) _ _ Hinst) _ _ Hfind).
        - eapply SECSTCTYPINGCORRECTNESS.env_sec_lower_bounded_from_window;
            exact Hwin.
        - exact Hbound.
        - exact Hacc1sec. }
      assert (Hpres : signatures_preserved stcsig obcsig).
      { eapply generated_signatures_preserved_obc with (P := systems); eauto. }
      assert (Hhead : Signature_head_consistent_obc stcsig obcsig).
      { assert (Hagree : stcsig.(s_name) = obcsig.(s_name)
                         /\ SIG.signature_fields_agree stcsig obcsig)
          by (eapply generated_signature_fields_agree; eauto).
        eapply signatures_preserved_obc_full_from_good;
          [exact (proj1 Hagree)|exact Hstcgood|exact Hstcnd
          |exact Hobcscoped|exact Hpres]. }
      (* re-establish every accumulator invariant *)
      assert (Hcons' : Signature_consistent_obc_full (stcsig :: acc1)
                         (obcsig :: acc2))
        by (eapply Signature_consistent_obc_full_cons; eauto).
      assert (Hacc1scoped' : SIG.secglobal_scoped (stcsig :: acc1))
        by (eapply SIG.secglobal_scoped_cons; eauto).
      assert (Hacc2scoped' : SIG.secglobal_scoped (obcsig :: acc2))
        by (eapply SIG.secglobal_scoped_cons; eauto).
      assert (Hstcsec : SIG.signature_scope_sec stcsig).
      { eapply SECSTCTYPINGCORRECTNESS.generated_sys_signature_scope_sec_from_env_props;
          [exact Henvprops|exact Hstcsig]. }
      assert (Hacc1sec' : SIG.secglobal_scope_sec (stcsig :: acc1))
        by (eapply SIG.secglobal_scope_sec_cons; eauto).
      assert (Hacc2sec' : SIG.secglobal_scope_sec (obcsig :: acc2)).
      { eapply SIG.secglobal_scope_sec_cons; [|exact Hacc2sec].
        intros ty Hin.
        rewrite <- (SIG.signature_fields_agree_scope_eq stcsig obcsig
                      (proj1 (proj2 Hhead))) in Hin.
        exact (Hstcsec ty Hin). }
      assert (Hbound' : SIG.secglobal_scope_bounded_above (stcsig :: acc1) st').
      { eapply SIG.secglobal_scope_bounded_above_cons.
        - eapply SECSTCTYPINGCORRECTNESS.generated_sys_signature_scope_bounded_from_window;
            [exact Hwin|exact Hstcsig].
        - eapply SIG.secglobal_scope_bounded_above_monotone;
            [exact Hbound|exact (proj2 Hwin)]. }
      eapply IH with (acc1 := stcsig :: acc1) (acc2 := obcsig :: acc2)
                     (envs := envs) (aux_names := aux_names) (st := st');
        eauto.
  Qed.

  Corollary generate_all_signatures_consistent_obc_scoped:
    forall systems envs aux_names G1 G2,
      SECSTCTYPINGCORRECTNESS.scoped_envs_windowed envs NAMEGEN.init_state systems ->
      NAMEGEN.aux_naming_props aux_names ->
      CloStc.wc_program systems ->
      WD.Well_scheduled systems ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env systems envs aux_names
        = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env (translate systems)
        envs aux_names = OK G2 ->
      Signature_consistent_obc_full G1 G2
      /\ SIG.secglobal_scoped G2
      /\ SIG.secglobal_scope_sec G2.
  Proof.
    intros systems envs aux_names G1 G2 Hwindow Haux Hwc Hsch Hstc Hobc.
    unfold SECSTCTYPING.generate_all_sys_signatures_scoped_env in Hstc.
    unfold SECOBCTYPING.generate_all_class_signatures_scoped_env in Hobc.
    eapply generate_all_signatures_consistent_obc_scoped'
      with (acc1 := nil) (acc2 := nil) (st := NAMEGEN.init_state).
    - exact Hwindow.
    - exact Haux.
    - exact Hwc.
    - exact Hsch.
    - apply Signature_consistent_obc_full_nil.
    - apply SIG.secglobal_scoped_nil.
    - apply SIG.secglobal_scoped_nil.
    - apply SIG.secglobal_scope_sec_nil.
    - apply SIG.secglobal_scope_sec_nil.
    - apply SIG.secglobal_scope_bounded_above_nil.
    - exact Hstc.
    - exact Hobc.
  Qed.

  Corollary generate_all_signatures_consistent_obc:
    forall systems envs aux_names G1 G2,
      SECSTCTYPINGCORRECTNESS.scoped_envs_windowed envs NAMEGEN.init_state systems ->
      NAMEGEN.aux_naming_props aux_names ->
      CloStc.wc_program systems ->
      WD.Well_scheduled systems ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env systems envs aux_names
        = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env (translate systems)
        envs aux_names = OK G2 ->
      Signature_consistent_obc_full G1 G2.
  Proof.
    intros systems envs aux_names G1 G2 Hwindow Haux Hwc Hsch Hstc Hobc.
    destruct (generate_all_signatures_consistent_obc_scoped
                systems envs aux_names G1 G2
                Hwindow Haux Hwc Hsch Hstc Hobc) as [Hcons _].
    exact Hcons.
  Qed.

  (** This is the public lookup theorem exported by the translation
      layer, the Stc-to-Obc counterpart of NLustre's
      [generated_program_signatures_preserved_global].  Every STC
      signature lookup has a matching Obc class signature lookup with
      the same visible fields and the call-preservation facts needed
      later.  Note that no NLustre node appears: the naming data enters
      only through [scoped_envs_windowed] and [aux_naming_props]. *)

  Corollary generated_program_signatures_preserved_obc_global:
    forall systems (G1 G2: SIG.secglobal)
           (envs: node_scoped_env) (aux_names: list node_aux_names),
      SECSTCTYPINGCORRECTNESS.scoped_envs_windowed envs NAMEGEN.init_state systems ->
      NAMEGEN.aux_naming_props aux_names ->
      CloStc.wc_program systems ->
      WD.Well_scheduled systems ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env systems envs aux_names
        = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env (translate systems)
        envs aux_names = OK G2 ->
      forall f stcsig,
        SIG.find_signature f G1 = Some stcsig ->
        exists obcsig,
          SIG.find_signature f G2 = Some obcsig
          /\ Signature_head_consistent_obc stcsig obcsig.
  Proof.
    intros systems G1 G2 envs aux_names
           Hwindow Haux Hwc Hsch Hstc Hobc f stcsig Hfindsig.
    pose proof (generate_all_signatures_consistent_obc
                  systems envs aux_names G1 G2
                  Hwindow Haux Hwc Hsch Hstc Hobc) as Hcons.
    destruct (Hcons f stcsig Hfindsig) as (obcsig & Hfindobc & Hhead).
    exists obcsig. split; assumption.
  Qed.

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
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import WD    : STCWELLDEFINED Ids Op CESyn SynStc SystStc OrdStc VarStc
                    LastStc DefStc CEIsF IsFStc)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc
       IsFStc CloStc WD SECSTCTYPING)
  (Import Trans : TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS SECOBCTYPING)
  <: SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc Lat SecT SIG SIGPROOFS
       CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc SECSTCTYPING
       SynNL NAMEGEN WD SECSTCTYPINGCORRECTNESS Trans
       SECOBCTYPING SECOBCTYPINGCORRECTNESS.

Include SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc Lat SecT SIG SIGPROOFS
  CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc IsFStc CloStc SECSTCTYPING
  SynNL NAMEGEN WD SECSTCTYPINGCORRECTNESS Trans
  SECOBCTYPING SECOBCTYPINGCORRECTNESS.

End SecStcObcTranslation.
