(** Leg U: unnesting preserves generated constraints.

    This is the pass the refinement types were built for.  [unnest_exp] on a
    nested call mints one variable per result with [idents_for_anns'], returns
    an [Evar] for each, and emits the call as its own equation.
    [assign_lexp_type] on the same expression mints one security name per
    result with [fresh_idents], returns a variable-shaped type for each, and
    *carries* that equation's constraints.

    So the theorem is that the carried constraints are the constraints of the
    equations unnesting emits, and the minted security names are the variables
    unnesting adds.  Nothing in the transcription leg states this, and nothing
    in it can: [to_lexp] rejects [Eapp], so by then there are no nested calls
    left and the carried component is empty everywhere.

    The two allocators cannot produce the same names -- unnesting mints
    [gensym norm1 _] and the security monad [gensym sec _] -- so the two sides
    are related by a bijection rather than by equality.  Both mint one name per
    annotation in the same order, so within a node the bijection is positional,
    and [preserves_on] absorbs it: the witness valuation is free to differ off
    the visible scope, which is exactly where the renamed names live. *)

From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Lia.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.
Module SecLusUnnestingBase
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import Lat     : Lattice)
  (Import SecT    : SECTYPES Lat)
  (Import SLT     : SECLUSTYPES Lat SecT)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX Ids Op)
  (Import LClo    : LCLOCKING Ids Op LSyn)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import UNN     : UNNESTING Ids Op OpAux LSyn).

  Import SECMONADNotations.
  Import UNN.Fresh.Tactics.

  (** * The security side of a call expression

      The analogue of [generate_lcall_constraint_inv], one level down: what
      [assign_lexp_type] does to an [Eapp].  Every Leg U proof about a nested
      call starts here.

      The result is [length anns] types, all carrying the *same* constraint
      list -- the instantiated call block joined with whatever the arguments
      and the reset were carrying.  That shared list is what the emitted
      equation has to generate. *)

  (** * Clocks, and the types assigned to them

      [assign_clk_type] walks a clock from [Cbase] outwards, joining the
      security name of each sampling variable onto what it has so far.  So it
      is monotone along the [Con] chain: the type of a clock contains the type
      of every clock that clock refines.

      Two things rest on this.  A call instantiates all of its formals from
      one base clock, so the call's own ambient sits below the ambient of
      every one of its results; and a well-clocked expression reads each
      variable at a clock its own clock refines, so the expression's clock
      type dominates the clock type of everything it mentions. *)

  Inductive clock_prefix : clock -> clock -> Prop :=
  | clock_prefix_refl :
      forall ck, clock_prefix ck ck
  | clock_prefix_con :
      forall ck ck' x b,
        clock_prefix ck ck' -> clock_prefix ck (Con ck' x b).

  Lemma clock_prefix_trans :
    forall ck1 ck2 ck3,
      clock_prefix ck1 ck2 -> clock_prefix ck2 ck3 -> clock_prefix ck1 ck3.
  Proof.
    intros ck1 ck2 ck3 H12 H23. revert ck1 H12.
    induction H23 as [ck|ck ck' x b H IH]; intros ck1 H12.
    - exact H12.
    - apply clock_prefix_con. exact (IH ck1 H12).
  Qed.

  Lemma clock_prefix_con_inv :
    forall ck ck' x b,
      clock_prefix (Con ck x b) ck' -> clock_prefix ck ck'.
  Proof.
    intros ck ck' x b H.
    apply clock_prefix_trans with (ck2 := Con ck x b);
      [apply clock_prefix_con, clock_prefix_refl|exact H].
  Qed.

  (** A clock's type is defined exactly when every clock it refines has one. *)
  Lemma assign_clk_type_prefix_defined :
    forall env base_ty ck ck' ckty',
      clock_prefix ck ck' ->
      assign_clk_type env base_ty ck' = Some ckty' ->
      exists ckty, assign_clk_type env base_ty ck = Some ckty.
  Proof.
    intros env base_ty ck ck' ckty' Hpre. revert ckty'.
    induction Hpre as [ck0|ck0 ck1 x b Hpre IH]; intros ckty' H.
    - exists ckty'. exact H.
    - simpl in H.
      destruct (assign_clk_type env base_ty ck1) as [c1|] eqn:Ec1;
        [|discriminate H].
      exact (IH c1 (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some c1))).
  Qed.

  Lemma assign_clk_type_prefix_incl :
    forall env base_ty ck ck' ckty ckty',
      clock_prefix ck ck' ->
      assign_clk_type env base_ty ck  = Some ckty ->
      assign_clk_type env base_ty ck' = Some ckty' ->
      incl ckty ckty'.
  Proof.
    intros env base_ty ck ck' ckty ckty' Hpre. revert ckty ckty'.
    induction Hpre as [ck0|ck0 ck1 x b Hpre IH]; intros ckty ckty' H1 H2.
    - rewrite H1 in H2. inversion H2; subst. apply incl_refl.
    - simpl in H2.
      destruct (assign_clk_type env base_ty ck1) as [c1|] eqn:Ec1;
        [|discriminate H2].
      destruct (Env.find x env) as [xt|] eqn:Ex; [|discriminate H2].
      simpl in H2. inversion H2; subst ckty'.
      intros y Hy.
      apply in_merge_left.
      exact
        (IH ckty c1 H1
           (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some c1)) y Hy).
  Qed.

  Lemma option_Some_inj :
    forall (A : Type) (x y : A), Some x = Some y -> x = y.
  Proof. intros A x y H. injection H. auto. Qed.

  (** Every variable a well-clocked CoreExpr expression mentions is read at
      a clock its own clock refines -- with one exception, the sampling
      variable a [merge] introduces, whose branches sit one [Con] deeper.
      That variable is carried by the expression's *type*, because
      [assign_cexp_type] joins it in.  So the two together --- the clock's
      type and the expression's --- dominate the clock type of everything
      mentioned, and that pair is exactly the shape of a generated
      constraint source, [ambient(ck) ⊔ type(e)]. *)

  Lemma assign_exp_type_clock_closed :
    forall env base_ty vars,
      env_injective env ->
      NoDupMembers vars ->
      forall e ck ety ckty,
        CEClo.wc_exp vars e ck ->
        assign_exp_type env e = Some ety ->
        assign_clk_type env base_ty ck = Some ckty ->
        forall v b ckv ckvty,
          Env.find v env = Some b ->
          In b ety ->
          In (v, ckv) vars ->
          assign_clk_type env base_ty ckv = Some ckvty ->
          incl ckvty (merge ckty ety).
  Proof.
    intros env base_ty vars Hinj Hnd e ck ety ckty Hwc. revert ety ckty.
    induction Hwc as
      [c|x ck0 ty Hin|e0 x b0 ck0 Hwc IH Hin
      |op e0 ck0 ty Hwc IH|op e1 e2 ck0 ty Hwc1 IH1 Hwc2 IH2];
      intros ety ckty Hety Hckty v b ckv ckvty Hfv Hb Hinv Hckv.
    - (** a constant mentions nothing *)
      simpl in Hety. inversion Hety; subst ety. inversion Hb.
    - (** a variable is read at its own clock *)
      simpl in Hety.
      destruct (Env.find x env) as [bx|] eqn:Ex; [|discriminate Hety].
      simpl in Hety. inversion Hety; subst ety.
      destruct Hb as [Hb|[]]. subst bx.
      assert (v = x) as ? by (exact (Hinj v x b b Hfv Ex (@Coq.Init.Logic.eq_refl ident b))); subst v.
      assert (ckv = ck0) as ?
          by (exact (NoDupMembers_det x ckv ck0 vars Hnd Hinv Hin)); subst ckv.
      rewrite Hckv in Hckty. inversion Hckty; subst ckty.
      intros z Hz. apply in_merge_left. exact Hz.
    - (** a sampled expression: the sampling variable is at the shallower
          clock, and everything below it at that clock too *)
      simpl in Hety.
      destruct (assign_exp_type env e0) as [ety0|] eqn:Ee0;
        [|discriminate Hety].
      destruct (Env.find x env) as [bx|] eqn:Ex; [|discriminate Hety].
      simpl in Hety. inversion Hety; subst ety.
      simpl in Hckty.
      destruct (assign_clk_type env base_ty ck0) as [c0|] eqn:Ec0;
        [|discriminate Hckty].
      rewrite Ex in Hckty. simpl in Hckty. inversion Hckty; subst ckty.
      apply in_merge_inv in Hb as [Hb|Hb].
      + intros z Hz.
        assert (In z (merge c0 ety0)) as Hz0
            by (exact (IH ety0 c0 (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some ety0)) (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some c0))
                     v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left, in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_left. exact Hz0.
      + destruct Hb as [Hb|[]]. subst bx.
        assert (v = x) as ? by (exact (Hinj v x b b Hfv Ex (@Coq.Init.Logic.eq_refl ident b))); subst v.
        assert (ckv = ck0) as ?
            by (exact (NoDupMembers_det x ckv ck0 vars Hnd Hinv Hin));
          subst ckv.
        rewrite Hckv in Ec0. inversion Ec0; subst c0.
        intros z Hz. apply in_merge_left, in_merge_left. exact Hz.
    - (** a unary operator mentions what its operand does *)
      simpl in Hety.
      exact (IH ety ckty Hety Hckty v b ckv ckvty Hfv Hb Hinv Hckv).
    - (** a binary operator, on one clock *)
      simpl in Hety.
      destruct (assign_exp_type env e1) as [e1ty|] eqn:Ee1;
        [|discriminate Hety].
      destruct (assign_exp_type env e2) as [e2ty|] eqn:Ee2;
        [|discriminate Hety].
      simpl in Hety. inversion Hety; subst ety.
      apply in_merge_inv in Hb as [Hb|Hb]; intros z Hz.
      + assert (In z (merge ckty e1ty)) as Hz0
            by (exact
                  (IH1 e1ty ckty (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some e1ty)) Hckty
                     v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_left. exact Hz0.
      + assert (In z (merge ckty e2ty)) as Hz0
            by (exact
                  (IH2 e2ty ckty (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some e2ty)) Hckty
                     v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_right. exact Hz0.
  Qed.

  (** The same closure for a clock's own type: a well-clocked clock samples
      on variables that are themselves declared on the clocks it refines, so
      its type already contains theirs.  The base name is the one thing in a
      clock type that is not a program variable's, which is what
      [base_not_var] says. *)

  Lemma assign_clk_type_clock_closed :
    forall env base_ty vars,
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv b, In (v, ckv) vars ->
                       Env.find v env = Some b -> b <> base_ty) ->
      forall ck ckty,
        wc_clock vars ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        forall v b ckv ckvty,
          Env.find v env = Some b ->
          In b ckty ->
          In (v, ckv) vars ->
          assign_clk_type env base_ty ckv = Some ckvty ->
          incl ckvty ckty.
  Proof.
    intros env base_ty vars Hinj Hnd Hbase ck ckty Hwc. revert ckty.
    induction Hwc as [|ck0 y b0 Hwc IH Hin];
      intros ckty Hckty v b ckv ckvty Hfv Hb Hinv Hckv.
    - (** the base clock mentions only the base name *)
      simpl in Hckty. apply option_Some_inj in Hckty. subst ckty.
      destruct Hb as [Hb|[]].
      exfalso. exact (Hbase v ckv b Hinv Hfv (@Coq.Init.Logic.eq_sym _ _ _ Hb)).
    - (** one more sampling variable, declared on the clock below it *)
      cbn -[SymTypes.merge] in Hckty.
      destruct (assign_clk_type env base_ty ck0) as [c0|] eqn:Ec0;
        [|discriminate Hckty].
      destruct (Env.find y env) as [by0|] eqn:Ey; [|discriminate Hckty].
      cbn -[SymTypes.merge] in Hckty.
      apply option_Some_inj in Hckty. subst ckty.
      apply in_merge_inv in Hb as [Hb|Hb].
      + intros z Hz. apply in_merge_left.
        exact
          (IH c0
             (@Coq.Init.Logic.eq_refl (option SymTypes.ST) (Some c0))
             v b ckv ckvty Hfv Hb Hinv Hckv z Hz).
      + destruct Hb as [Hb|[]]. subst by0.
        assert (v = y) as ?
            by (exact (Hinj v y b b Hfv Ey (@Coq.Init.Logic.eq_refl ident b)));
          subst v.
        assert (ckv = ck0) as ?
            by (exact (NoDupMembers_det y ckv ck0 vars Hnd Hinv Hin));
          subst ckv.
        rewrite Hckv in Ec0. apply option_Some_inj in Ec0. subst c0.
        intros z Hz. apply in_merge_left. exact Hz.
  Qed.

  Lemma assign_cexp_type_clock_closed :
    forall env base_ty vars,
      env_injective env ->
      NoDupMembers vars ->
      forall ce ck ety ckty,
        CEClo.wc_cexp vars ce ck ->
        assign_cexp_type env ce = Some ety ->
        assign_clk_type env base_ty ck = Some ckty ->
        forall v b ckv ckvty,
          Env.find v env = Some b ->
          In b ety ->
          In (v, ckv) vars ->
          assign_clk_type env base_ty ckv = Some ckvty ->
          incl ckvty (merge ckty ety).
  Proof.
    intros env base_ty vars Hinj Hnd ce ck ety ckty Hwc. revert ety ckty.
    induction Hwc as
      [x t f ck0 Hin Hwct IHt Hwcf IHf
      |e0 t f ck0 Hwce Hwct IHt Hwcf IHf
      |e0 ck0 Hwce];
      intros ety ckty Hety Hckty v b ckv ckvty Hfv Hb Hinv Hckv.
    - (** the sampling variable is at the shallower clock, and the type
          carries it, so the branches' extra [Con] is paid for *)
      cbn -[SymTypes.merge] in Hety.
      destruct (Env.find x env) as [bx|] eqn:Ex; [|discriminate Hety].
      destruct (assign_cexp_type env t) as [c1ty|] eqn:Et;
        [|discriminate Hety].
      destruct (assign_cexp_type env f) as [c2ty|] eqn:Ef;
        [|discriminate Hety].
      cbn -[SymTypes.merge] in Hety. apply option_Some_inj in Hety. subst ety.
      assert (assign_clk_type env base_ty (Con ck0 x true)
              = Some (merge ckty [bx])) as Ect.
      { simpl. rewrite Hckty, Ex. reflexivity. }
      assert (assign_clk_type env base_ty (Con ck0 x false)
              = Some (merge ckty [bx])) as Ecf.
      { simpl. rewrite Hckty, Ex. reflexivity. }
      apply in_merge_inv in Hb as [Hb|Hb].
      + apply in_merge_inv in Hb as [Hb|Hb].
        * (** the sampling variable itself *)
          destruct Hb as [Hb|[]]. subst bx.
          assert (v = x) as ?
              by (exact (Hinj v x b b Hfv Ex (@Coq.Init.Logic.eq_refl ident b)));
            subst v.
          assert (ckv = ck0) as ?
              by (exact (NoDupMembers_det x ckv ck0 vars Hnd Hinv Hin));
            subst ckv.
          rewrite Hckv in Hckty. inversion Hckty; subst ckty.
          intros z Hz. apply in_merge_left. exact Hz.
        * (** the true branch, one [Con] deeper *)
          intros z Hz.
          assert (In z (merge (merge ckty [bx]) c1ty)) as Hz0
              by (exact
                    (IHt c1ty (merge ckty [bx])
                       (@Coq.Init.Logic.eq_refl (option SymTypes.ST)
                          (Some c1ty))
                       Ect v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
          apply in_merge_inv in Hz0 as [Hz0|Hz0].
          -- apply in_merge_inv in Hz0 as [Hz0|Hz0].
             ++ apply in_merge_left. exact Hz0.
             ++ apply in_merge_right, in_merge_left, in_merge_left.
                exact Hz0.
          -- apply in_merge_right, in_merge_left, in_merge_right. exact Hz0.
      + (** the false branch *)
        intros z Hz.
        assert (In z (merge (merge ckty [bx]) c2ty)) as Hz0
            by (exact
                  (IHf c2ty (merge ckty [bx])
                     (@Coq.Init.Logic.eq_refl (option SymTypes.ST)
                        (Some c2ty))
                     Ecf v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_inv in Hz0 as [Hz0|Hz0].
          -- apply in_merge_left. exact Hz0.
          -- apply in_merge_right, in_merge_left, in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_right. exact Hz0.
    - (** a conditional: scrutinee and branches all on one clock *)
      cbn -[SymTypes.merge] in Hety.
      destruct (assign_exp_type env e0) as [ety0|] eqn:Ee0;
        [|discriminate Hety].
      destruct (assign_cexp_type env t) as [c1ty|] eqn:Et;
        [|discriminate Hety].
      destruct (assign_cexp_type env f) as [c2ty|] eqn:Ef;
        [|discriminate Hety].
      cbn -[SymTypes.merge] in Hety. apply option_Some_inj in Hety. subst ety.
      apply in_merge_inv in Hb as [Hb|Hb]; [apply in_merge_inv in Hb as [Hb|Hb]|];
        intros z Hz.
      + assert (In z (merge ckty ety0)) as Hz0
            by (exact
                  (assign_exp_type_clock_closed
                     env base_ty vars Hinj Hnd e0 ck0 ety0 ckty
                     Hwce Ee0 Hckty v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_left, in_merge_left. exact Hz0.
      + assert (In z (merge ckty c1ty)) as Hz0
            by (exact
                  (IHt c1ty ckty
                     (@Coq.Init.Logic.eq_refl (option SymTypes.ST)
                        (Some c1ty))
                     Hckty v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_left, in_merge_right. exact Hz0.
      + assert (In z (merge ckty c2ty)) as Hz0
            by (exact
                  (IHf c2ty ckty
                     (@Coq.Init.Logic.eq_refl (option SymTypes.ST)
                        (Some c2ty))
                     Hckty v b ckv ckvty Hfv Hb Hinv Hckv z Hz)).
        apply in_merge_inv in Hz0 as [Hz0|Hz0].
        * apply in_merge_left. exact Hz0.
        * apply in_merge_right, in_merge_right. exact Hz0.
    - (** a plain expression *)
      cbn -[SymTypes.merge] in Hety.
      exact
        (assign_exp_type_clock_closed
           env base_ty vars Hinj Hnd e0 ck0 ety ckty
           Hwce Hety Hckty v b ckv ckvty Hfv Hb Hinv Hckv).
  Qed.

  Lemma assign_lexp_Eapp_inv :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      exists sg argts rstty ckty outs cs sta stb stc,
        assign_lexps G env base_ty rst_ty es st = OK (argts, sta)
        /\ assign_clk_type env base_ty (find_base_clock (LSyn.clocksof es))
           = Some ckty
        /\ (match er with
            | None => rstty = lvar rst_ty /\ stb = sta
            | Some e1 =>
                exists t1 a1 rck stm,
                  assign_lexp_type G env base_ty rst_ty e1 sta = OK (t1, stm)
                  /\ single t1 stm = OK (a1, stb)
                  /\ assign_clk_type env base_ty (hd Cbase (LSyn.clockof e1))
                     = Some rck
                  /\ rstty = ljoin (lvar rst_ty) (ljoin a1 (rck, []))
            end)
        /\ find_signature f G = Some sg
        /\ fresh_idents (List.length anns) stb = OK (outs, stc)
        /\ generate_constraints sg (List.map fst argts) ckty (fst rstty) outs stc
           = OK (cs, st')
        /\ ts = List.map
                  (fun o => (([o] : ST),
                             cmerge cs (cmerge (carried argts) (snd rstty))))
                  outs.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (argts & sta & Hargs & H).
    eapply sec_bind_inv in H as (rstty & stb & Hrst & H).
    eapply sec_bind_inv in H as (ckty & stk & Hck & H).
    apply option_to_sec_inv in Hck as [Hck ?]; subst stk.
    destruct (find_signature f G) as [sg|] eqn:Esg; [|discriminate].
    eapply sec_bind_inv in H as (outs & stc & Houts & H).
    eapply sec_bind_inv in H as (cs & std & Hcs & Hret).
    unfold ret in Hret. inv Hret.
    exists sg, argts, rstty, ckty, outs, cs, sta, stb, stc.
    repeat split; auto.
    destruct er as [e1|].
    - eapply sec_bind_inv in Hrst as (t1 & stm & Ht1 & Hrst).
      eapply sec_bind_inv in Hrst as (a1 & stn & Ha1 & Hrst).
      eapply sec_bind_inv in Hrst as (rck & stp & Hrck & Hret').
      apply option_to_sec_inv in Hrck as [Hrck ?]; subst stp.
      unfold ret in Hret'. inv Hret'.
      exists t1, a1, rck, stm. auto.
    - unfold ret in Hrst. inv Hrst. auto.
  Qed.

  (** * The unnesting side of a call expression

      The mirror of the previous lemma.  [unnest_exp] on an [Eapp] unnests the
      arguments, the no-op arguments and the reset, takes one identifier per
      result annotation, returns an [Evar] for each, and emits the call as an
      equation in front of everything the sub-unnestings emitted.

      [idents_for_anns'] does not always mint: when the annotation already
      carries a name it *reuses* it.  So the correspondence with
      [fresh_idents (length anns)] is not mint-for-mint.  It does not need to
      be -- both lists have length [length anns]
      ([idents_for_anns'_length]), so the bijection is positional over the
      call's results, and whether a result's variable is new or reused only
      changes which side of the bijection was already named. *)

  Lemma unnest_exp_Eapp_inv :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists es1 eqs1 st1 es2 eqs2 st2 er' eqs3 st3 xs,
        unnest_exps G es st = ((es1, eqs1), st1)
        /\ unnest_noops_exps (find_node_incks G f) es1 st1 = ((es2, eqs2), st2)
        /\ unnest_reset (unnest_exp G true) er st2 = ((er', eqs3), st3)
        /\ idents_for_anns' anns st3 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (List.map fst xs, [Eapp f es2 er' (List.map snd xs)])
                 :: eqs1 ++ eqs2 ++ eqs3.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    unfold unnest_exps. apply bind2_spec.
    do 3 eexists. split; [eassumption|apply ret_spec].
  Qed.

  (** The two lists of results have the same length, which is what makes the
      bijection between a call's minted security names and its variables
      positional. *)

  Lemma fresh_idents_length :
    forall n outs st st',
      fresh_idents n st = OK (outs, st') ->
      List.length outs = n.
  Proof.
    induction n as [|n IH]; intros outs st st' H; simpl in H.
    - unfold ret in H. inv H. reflexivity.
    - eapply sec_bind_inv in H as (x & st1 & Hx & H).
      eapply sec_bind_inv in H as (xs & st2 & Hxs & Hret).
      unfold ret in Hret. inv Hret. simpl. f_equal. eapply IH; eauto.
  Qed.

  Lemma assign_lexp_Eapp_length :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      List.length ts = List.length anns.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & Hargs & Hck & Hrst & Esg & Houts & Hcs & Hts).
    subst ts. rewrite map_length.
    eapply fresh_idents_length; eauto.
  Qed.

  (** * Why the carried component is empty after unnesting

      The results of an unnested expression are variables, and a variable
      carries nothing: [assign_lexp_type] on an [Evar] is [lvar] of its
      security name, whose constraint component is [[]].  Everything the
      expression was carrying has become an equation.

      That is the bridge between this leg and the transcription leg, and it is
      why [to_lexps_assign_rev] could conclude the argument types come back as
      [map (fun t => (t, [])) tys] there: by the time transcription runs, both
      passes have already turned every carried constraint into an equation. *)

  Lemma assign_lexp_Evar_inv :
    forall G env base_ty rst_ty x a t st st',
      assign_lexp_type G env base_ty rst_ty (Evar x a) st = OK (t, st') ->
      exists xt,
        Env.find x env = Some xt
        /\ t = [(([xt] : ST), [])]
        /\ st' = st.
  Proof.
    intros G env base_ty rst_ty x a t st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (xt & st1 & Hx & Hret).
    apply find_env_inv in Hx as [Hx Hst]; subst st1.
    unfold ret in Hret. inv Hret.
    exists xt. repeat split; auto.
  Qed.

  Corollary unnested_call_results_carry_nothing :
    forall G env base_ty rst_ty G' is_control f es er anns es' eqs st st',
      unnest_exp G' is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      Forall (fun e' =>
                forall t sst sst',
                  assign_lexp_type G env base_ty rst_ty e' sst = OK (t, sst') ->
                  Forall (fun p => snd p = []) t)
             es'.
  Proof.
    intros G env base_ty rst_ty G' is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & _ & _ & Hes' & _).
    subst es'.
    apply Forall_map, Forall_forall. intros [id an] _ t sst sst' Ht.
    eapply assign_lexp_Evar_inv in Ht as (xt & _ & Ht & _). subst t.
    now repeat constructor.
  Qed.

  (** * Base cases

      On a constant or a variable unnesting does nothing and emits nothing,
      and the security typer returns a type carrying nothing.  Those are the
      two ends of the induction meeting trivially. *)

  Lemma unnest_exp_Econst :
    forall G is_control c st,
      unnest_exp G is_control (Econst c) st = (([Econst c], []), st).
  Proof. intros. simpl. apply ret_spec. Qed.

  Lemma unnest_exp_Evar :
    forall G is_control x a st,
      unnest_exp G is_control (Evar x a) st = (([Evar x a], []), st).
  Proof. intros. simpl. apply ret_spec. Qed.

  (** * A call carries exactly what its emitted equation generates

      Every result of a call carries the same list, so merging them all
      collapses back to that one list -- [cmerge] is idempotent.  Which means
      the call's total carried constraints are the instantiated block joined
      with what the arguments and the reset carried, and that is, term for
      term, what [generate_lcall_constraint] produces for the equation
      unnesting emits. *)

  Lemma carried_uniform :
    forall (held : list SymTypes.constraint) outs,
      carried (List.map (fun o => (([o] : ST), held)) outs)
      = match outs with [] => [] | _ => held end.
  Proof.
    intros held outs. induction outs as [|o os IH]; [reflexivity|].
    simpl in *. rewrite IH. destruct os.
    - apply cmerge_nil.
    - apply cmerge_refl.
  Qed.

  Corollary assign_lexp_Eapp_carried :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      anns <> [] ->
      exists sg (argts : list LST) (rstty : LST) (ckty : ST)
             (cs : list SymTypes.constraint),
        find_signature f G = Some sg
        /\ assign_clk_type env base_ty (find_base_clock (LSyn.clocksof es))
           = Some ckty
        /\ carried ts = cmerge cs (cmerge (carried argts) (snd rstty)).
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H Hne.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & Hargs & Hck & Hrst & Esg & Houts & Hcs & Hts).
    exists sg, argts, rstty, ckty, cs.
    split; [exact Esg|]. split; [exact Hck|].
    subst ts. rewrite carried_uniform.
    destruct outs as [|o os] eqn:Eouts.
    - exfalso. apply Hne.
      apply fresh_idents_length in Houts. simpl in Houts.
      destruct anns; [reflexivity|discriminate].
    - reflexivity.
  Qed.

  (** * Argument lists

      The induction decomposes an argument list on both sides at once, so it
      needs [carried] to distribute over the concatenation [assign_lexps]
      builds.  It does: [carried] is a [cmerge] fold, and [cmerge] is
      associative with [[]] as unit. *)

  Lemma carried_app :
    forall ts us,
      carried (ts ++ us) = cmerge (carried ts) (carried us).
  Proof.
    induction ts as [|t ts IH]; intros us; simpl.
    - now rewrite cmerge_nil2.
    - rewrite IH. now rewrite cmerge_assoc.
  Qed.

  (** So an argument list carries the merge of what its expressions carry,
      which is the shape the [Eapp] case needs of its [carried argts]. *)

  Lemma assign_lexps_carried_cons :
    forall G env base_ty rst_ty e es ts st st',
      assign_lexps G env base_ty rst_ty (e :: es) st = OK (ts, st') ->
      exists t r sta,
        assign_lexp_type G env base_ty rst_ty e st = OK (t, sta)
        /\ assign_lexps G env base_ty rst_ty es sta = OK (r, st')
        /\ ts = t ++ r
        /\ carried ts = cmerge (carried t) (carried r).
  Proof.
    intros G env base_ty rst_ty e es ts st st' H.
    rewrite assign_lexps_cons in H.
    eapply sec_bind_inv in H as (t & sta & Ht & H).
    eapply sec_bind_inv in H as (r & stb & Hr & Hret).
    unfold ret in Hret. inv Hret.
    exists t, r, sta. repeat split; auto. apply carried_app.
  Qed.

  Lemma assign_lexps_carried_nil :
    forall G env base_ty rst_ty ts st st',
      assign_lexps G env base_ty rst_ty [] st = OK (ts, st') ->
      ts = [] /\ carried ts = [] /\ st' = st.
  Proof.
    intros G env base_ty rst_ty ts st st' H.
    rewrite assign_lexps_nil in H. unfold ret in H. inv H.
    repeat split; reflexivity.
  Qed.

  (** * The delay, on the unnesting side

      [Efby] lifts exactly as [Eapp] does -- one identifier per annotation, an
      [Evar] returned for each, and one emitted equation per result.  The
      difference is what the emitted equations are: a [fby] each, rather than
      a single call.  This is also the case the initialisation leg picks up,
      since those [fby]s are what [fby_equation] then looks at. *)

  Lemma unnest_exp_Efby_inv :
    forall G is_control e0s es anns es' eqs st st',
      unnest_exp G is_control (Efby e0s es anns) st = ((es', eqs), st') ->
      exists e0s' eqs1 st1 es'' eqs2 st2 xs,
        unnest_exps G e0s st = ((e0s', eqs1), st1)
        /\ unnest_exps G es st1 = ((es'', eqs2), st2)
        /\ idents_for_anns anns st2 = (xs, st')
        /\ es' = List.map (fun '(x, ann) => Evar x ann) xs
        /\ eqs = (List.map (fun '((x, _), fby) => ([x], [fby]))
                    (combine xs (unnest_fby e0s' es'' anns)))
                 ++ eqs1 ++ eqs2.
  Proof.
    intros G is_control e0s es anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    all: unfold unnest_exps; apply bind2_spec;
         repeat esplit; eauto using ret_spec.
  Qed.

  (** * The remaining lifting cases

      [Earrow] lifts exactly as [Efby].  [Emerge] and [Eite] lift only when
      [is_control] is false; their branches are unnested at [is_control =
      true], where nothing lifts, so the induction has to run at both flags.
      [unnest_controls] is a local [let] with no global counterpart, so these
      are stated directly over [map_bind2 (unnest_exp G true)]. *)

  Lemma unnest_exp_Earrow_inv :
    forall G is_control e0s es anns es' eqs st st',
      unnest_exp G is_control (Earrow e0s es anns) st = ((es', eqs), st') ->
      exists e0s' eqs1 st1 es'' eqs2 st2 xs,
        unnest_exps G e0s st = ((e0s', eqs1), st1)
        /\ unnest_exps G es st1 = ((es'', eqs2), st2)
        /\ idents_for_anns anns st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e]) (unnest_arrow e0s' es'' anns)))
                 ++ eqs1 ++ eqs2.
  Proof.
    intros G is_control e0s es anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    all: unfold unnest_exps; apply bind2_spec;
         repeat esplit; eauto using ret_spec.
  Qed.

  Lemma unnest_exp_Emerge_inv :
    forall G ckid es1 es2 tys cl es' eqs st st',
      unnest_exp G false (Emerge ckid es1 es2 (tys, cl)) st = ((es', eqs), st') ->
      exists es1' eqs1 st1 es2' eqs2 st2 xs,
        map_bind2 (unnest_exp G true) es1 st = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st2)
        /\ idents_for_anns (List.map (fun ty => (ty, cl)) tys) st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e])
                       (unnest_merge ckid (List.concat es1') (List.concat es2')
                          tys cl)))
                 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G ckid es1 es2 tys cl es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Eite_inv :
    forall G e es1 es2 tys ck es' eqs st st',
      unnest_exp G false (Eite e es1 es2 (tys, ck)) st = ((es', eqs), st') ->
      exists e' eqs0 st0 es1' eqs1 st1 es2' eqs2 st2 xs,
        unnest_exp G false e st = ((e', eqs0), st0)
        /\ map_bind2 (unnest_exp G true) es1 st0 = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st2)
        /\ idents_for_anns (List.map (fun ty => (ty, ck)) tys) st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e])
                       (unnest_ite (hd_default e') (List.concat es1')
                          (List.concat es2') tys ck)))
                 ++ eqs0 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G e es1 es2 tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
  Qed.

  (** * The reset of an unnested call is always a variable

      [unnest_reset] has two branches: it keeps the head when it is already an
      [Evar], and otherwise mints a variable and emits an equation binding it.
      Either way what comes back is a variable, which is what lets the emitted
      call equation be inverted with [generate_lcall_constraint_inv] -- the
      Lustre generator only accepts a reset that is an [Evar]. *)

  Lemma unnest_reset_shape :
    forall k er er' eqs st st',
      unnest_reset k er st = ((er', eqs), st') ->
      er' = None \/ exists v an, er' = Some (Evar v an).
  Proof.
    intros k er er' eqs st st' H.
    unnest_reset_spec.
    - right. do 2 eexists. reflexivity.
    - right. do 2 eexists. reflexivity.
    - left. reflexivity.
  Qed.

  Corollary unnest_exp_Eapp_reset_is_var :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists es2 er' xs,
        (er' = None \/ exists v an, er' = Some (Evar v an))
        /\ In (List.map fst xs, [Eapp f es2 er' (List.map snd xs)]) eqs.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & Hrst & _ & _ & Heqs).
    exists es2, er', xs. split.
    - eapply unnest_reset_shape; eauto.
    - subst eqs. now left.
  Qed.

  (** * What the call case reduces to

      Both sides instantiate the *same* callee: the source expression looks [f]
      up to build what it carries, and the equation unnesting emits looks [f]
      up to build what it generates.  So the two constraint sets have the same
      shape -- an instantiated block merged with what the arguments and the
      reset carry -- and differ only in the arguments, which the induction
      relates, and in the result names, which
      [subst_constraints_out_map] relates.

      Nothing structural is left in this case. *)

  Lemma Eapp_and_emitted_shape :
    forall GL GN env base_ty rst_ty cenv f es er anns ts sst sst'
           x xs es'' er'' anns'' ce xst xst',
      assign_lexp_type GL env base_ty rst_ty (Eapp f es er anns) sst
        = OK (ts, sst') ->
      (er'' = None \/ exists v an, er'' = Some (Evar v an)) ->
      generate_leqn_constraint GN env base_ty rst_ty cenv
        (x :: xs, [Eapp f es'' er'' anns'']) xst = OK (ce, xst') ->
      anns <> [] ->
      exists sgL sgN,
        find_signature f GL = Some sgL
        /\ find_signature f GN = Some sgN
        /\ (exists (argts : list LST) (rstty : LST) (cs : list SymTypes.constraint),
              carried ts = cmerge cs (cmerge (carried argts) (snd rstty)))
        /\ (exists (argts' : list LST) (rstty' : LST) (ckty' : ST)
                   (outs' : list ident) (cs0 : list SymTypes.constraint) sti stf,
              generate_constraints sgN (List.map fst argts') ckty' (fst rstty')
                outs' sti = OK (cs0, stf)
              /\ ce = cmerge cs0 (cmerge (carried argts') (snd rstty'))).
  Proof.
    intros GL GN env base_ty rst_ty cenv f es er anns ts sst sst'
           x xs es'' er'' anns'' ce xst xst' Hsrc Hshape Htgt Hne.
    (* the source side *)
    pose proof Hsrc as Hsrc0.
    eapply assign_lexp_Eapp_inv in Hsrc0
      as (sgL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EsgL & _ & _ & _).
    eapply assign_lexp_Eapp_carried in Hsrc
      as (sgL' & argts & rstty & ckty & cs & EsgL' & _ & Hcar); [|exact Hne].
    rewrite EsgL in EsgL'. inversion EsgL'; subst sgL'.
    (* the target side: the emitted equation, whose reset is a variable *)
    destruct Hshape as [Hnone|(v & an & Hsome)]; subst er''.
    - rewrite gen_leqn_Eapp in Htgt.
      eapply generate_lcall_constraint_inv in Htgt
        as (sgN & ckt & argt & outt & sti & cs0 & EsgN & _ & _ & _ & Hgc & Hce).
      exists sgL, sgN. repeat split; auto.
      + exists argts, rstty, cs. exact Hcar.
      + exists argt, (lvar rst_ty), ckt, outt, cs0, sti, xst'.
        split; [exact Hgc|exact Hce].
    - destruct an as [ty [ckr nm]].
      rewrite gen_leqn_Eapp_reset in Htgt.
      eapply sec_bind_inv in Htgt as (rty & sta & Hrty & Htgt).
      eapply sec_bind_inv in Htgt as (rstck & stb & Hrstck & Htgt).
      eapply generate_lcall_constraint_inv in Htgt
        as (sgN & ckt & argt & outt & sti & cs0 & EsgN & _ & _ & _ & Hgc & Hce).
      exists sgL, sgN. repeat split; auto.
      + exists argts, rstty, cs. exact Hcar.
      + exists argt, (ljoin (lvar rst_ty) (merge [rty] rstck, [])), ckt, outt,
               cs0, sti, xst'.
        split; [exact Hgc|exact Hce].
  Qed.

  (** * The cases where nothing is introduced

      [Eunop], [Ebinop] and [Ewhen] do not lift: unnesting rebuilds the
      expression and emits exactly what its sub-expressions emitted, and the
      typer carries exactly what its sub-expressions carried.  Nothing is
      minted on either side, so these cases of the induction are inherited
      rather than argued -- the renaming stays empty through them. *)

  Lemma unnest_exp_Eunop_inv :
    forall G is_control op e1 an es' eqs st st',
      unnest_exp G is_control (Eunop op e1 an) st = ((es', eqs), st') ->
      exists e1' st1,
        unnest_exp G false e1 st = ((e1', eqs), st1)
        /\ st' = st1
        /\ es' = [Eunop op (hd_default e1') an].
  Proof.
    intros G is_control op e1 an es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Ebinop_inv :
    forall G is_control op e1 e2 an es' eqs st st',
      unnest_exp G is_control (Ebinop op e1 e2 an) st = ((es', eqs), st') ->
      exists e1' eqs1 st1 e2' eqs2,
        unnest_exp G false e1 st = ((e1', eqs1), st1)
        /\ unnest_exp G false e2 st1 = ((e2', eqs2), st')
        /\ eqs = eqs1 ++ eqs2
        /\ es' = [Ebinop op (hd_default e1') (hd_default e2') an].
  Proof.
    intros G is_control op e1 e2 an es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Ewhen_inv :
    forall G is_control es ckid b tys ck es' eqs st st',
      unnest_exp G is_control (Ewhen es ckid b (tys, ck)) st
        = ((es', eqs), st') ->
      exists es1,
        unnest_exps G es st = ((es1, eqs), st')
        /\ es' = unnest_when ckid b es1 tys ck.
  Proof.
    intros G is_control es ckid b tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    unfold unnest_exps. apply bind2_spec.
    repeat esplit; eauto using ret_spec.
  Qed.

  (** And the typer's side of the same three: the unary case is literally its
      operand's, and the other two carry the merge of their operands'. *)

  Lemma assign_lexp_Eunop_inv :
    forall G env base_ty rst_ty op e1 an ts st st',
      assign_lexp_type G env base_ty rst_ty (Eunop op e1 an) st = OK (ts, st') ->
      assign_lexp_type G env base_ty rst_ty e1 st = OK (ts, st').
  Proof. intros. exact H. Qed.

  Lemma assign_lexp_Ewhen_carried :
    forall G env base_ty rst_ty es x b tys ck ts st st',
      assign_lexp_type G env base_ty rst_ty (Ewhen es x b (tys, ck)) st
        = OK (ts, st') ->
      exists us g,
        assign_lexps G env base_ty rst_ty es st = OK (us, st')
        /\ Env.find x env = Some g
        /\ ts = List.map (fun t => ljoin t (lvar g)) us.
  Proof.
    intros G env base_ty rst_ty es x b tys ck ts st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (us & sta & Hus & H).
    eapply sec_bind_inv in H as (g & stb & Hg & Hret).
    apply find_env_inv in Hg as [Hg Hst]; subst stb.
    unfold ret in Hret. inv Hret.
    exists us, g. repeat split; auto.
  Qed.

  (** * The renaming, constructed

      For a call the two sides' residual types are both lists of singletons:
      the typer gives each result the singleton of its minted name, unnesting
      gives each result an [Evar] on the variable it took.  So the renaming is
      the pairing of those two lists, and both have length [length anns].

      Nothing more is needed of it than that pairing.
      [subst_constraints_out_map] renames occurrences of the first list by the
      second *inside the left-hand sides as well as at the targets*
      ([subst_ident_constraint] rewrites [ty] and [x'] together), so putting a
      defining constraint into the set renames the type inside it too.  That is
      why the induction does not have to carry a separate claim about types:
      a type only ever appears inside a constraint, and the renaming reaches
      it there. *)

  Lemma assign_lexp_Eapp_result_types :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st
        = OK (ts, st') ->
      exists outs,
        List.length outs = List.length anns
        /\ List.map fst ts = List.map (fun o => ([o] : ST)) outs.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & _ & _ & _ & _ & Houts & _ & Hts).
    exists outs. split.
    - eapply fresh_idents_length; eauto.
    - subst ts. now rewrite !map_map.
  Qed.

  Lemma unnest_exp_Eapp_result_vars :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists xs,
        List.length xs = List.length anns
        /\ es' = List.map (fun '(id, an) => Evar id an) xs.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & _ & Hxs & Hes' & _).
    exists xs. split; [|exact Hes'].
    eapply idents_for_anns'_length; eauto.
  Qed.

  (** The two lists to be paired, with the pairing's defining property: they
      are the same length, so [subst_constraints_out_map] can consume them. *)

  Corollary Eapp_renaming_lists :
    forall G env base_ty rst_ty G' is_control f es er anns
           ts st st' es' eqs sst sst',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st
        = OK (ts, st') ->
      unnest_exp G' is_control (Eapp f es er anns) sst = ((es', eqs), sst') ->
      exists outs xs,
        List.map fst ts = List.map (fun o => ([o] : ST)) outs
        /\ es' = List.map (fun '(id, an) => Evar id an) xs
        /\ List.length outs = List.length (List.map fst xs).
  Proof.
    intros G env base_ty rst_ty G' is_control f es er anns
           ts st st' es' eqs sst sst' Hsrc Htgt.
    eapply assign_lexp_Eapp_result_types in Hsrc as (outs & Hlo & Hts).
    eapply unnest_exp_Eapp_result_vars in Htgt as (xs & Hlx & Hes').
    exists outs, xs. repeat split; auto.
    rewrite map_length. congruence.
  Qed.

  (** * Renaming a type

      [subst_constraints_out_map] reaches types that sit inside constraints,
      but the induction also meets a type on its own: a call's actual argument
      types are handed to [generate_constraints], which substitutes them for
      the callee's formals.  So the renaming has to apply to a bare [ST] too.

      That is not a new substitution.  [SIG.subst_ident_in_type] is the
      primitive -- the one [subst_ident_constraint] is built from -- and the
      list-wise version is its fold, shaped exactly like
      [subst_constraints_inp_map]. *)

  Fixpoint subst_idents_in_type (ty : ST) (xs vs : list ident) : ST :=
    match xs, vs with
    | x :: xs', v :: vs' =>
        subst_idents_in_type (SIG.subst_ident_in_type ty x [v]) xs' vs'
    | _, _ => ty
    end.

  Lemma subst_ident_in_type_notin :
    forall ty x v, ~ In x ty -> SIG.subst_ident_in_type ty x v = ty.
  Proof.
    intros ty x v Hnin. unfold SIG.subst_ident_in_type.
    destruct (SymTypes.my_set_mem x ty) eqn:Em; [|reflexivity].
    exfalso. apply Hnin. now apply SymTypes.my_set_mem_correct.
  Qed.

  (** What the cases that mint nothing need: a type mentioning none of the
      renamed names is left alone, so the renaming really is the identity
      through [Eunop], [Ebinop], [Ewhen] and the base cases. *)

  Lemma subst_idents_in_type_notin :
    forall xs vs ty,
      (forall x, In x xs -> ~ In x ty) ->
      subst_idents_in_type ty xs vs = ty.
  Proof.
    induction xs as [|x xs IH]; intros vs ty Hnin; simpl.
    - reflexivity.
    - destruct vs as [|v vs]; [reflexivity|].
      rewrite subst_ident_in_type_notin by (apply Hnin; now left).
      apply IH. intros y Hy. apply Hnin. now right.
  Qed.

  Corollary subst_idents_in_type_nil :
    forall ty vs, subst_idents_in_type ty [] vs = ty.
  Proof. reflexivity. Qed.

  (** * Composing renamings

      A constructor that combines sub-expressions inherits their renamings, so
      the induction has to concatenate them.  Both levels compose the way the
      folds are written -- renaming by [xs1 ++ xs2] is renaming by [xs1] and
      then by [xs2] -- and at the constraint level the composition is exactly
      the monadic sequencing the fixpoint already performs. *)

  Lemma subst_idents_in_type_app :
    forall xs1 vs1 xs2 vs2 ty,
      List.length xs1 = List.length vs1 ->
      subst_idents_in_type ty (xs1 ++ xs2) (vs1 ++ vs2)
      = subst_idents_in_type (subst_idents_in_type ty xs1 vs1) xs2 vs2.
  Proof.
    induction xs1 as [|x xs1 IH]; intros vs1 xs2 vs2 ty Hlen.
    - destruct vs1; [reflexivity|simpl in Hlen; discriminate].
    - destruct vs1 as [|v vs1]; [simpl in Hlen; discriminate|].
      simpl. apply IH. simpl in Hlen. congruence.
  Qed.

  Lemma subst_constraints_out_map_app :
    forall xs1 vs1 xs2 vs2 cs cs1 cs2 st st1 st2,
      subst_constraints_out_map cs xs1 vs1 st = OK (cs1, st1) ->
      subst_constraints_out_map cs1 xs2 vs2 st1 = OK (cs2, st2) ->
      subst_constraints_out_map cs (xs1 ++ xs2) (vs1 ++ vs2) st = OK (cs2, st2).
  Proof.
    induction xs1 as [|x xs1 IH]; intros vs1 xs2 vs2 cs cs1 cs2 st st1 st2 H1 H2.
    - destruct vs1 as [|v vs1]; simpl in H1; [|discriminate].
      unfold ret in H1. inv H1. exact H2.
    - destruct vs1 as [|v vs1]; simpl in H1; [discriminate|].
      simpl.
      destruct (SymTypes.findST cs v) eqn:Ef; [discriminate|].
      eapply sec_bind_inv in H1 as (cs' & sta & Hhd & Htl).
      eapply sec_bind_ok; [exact Hhd|].
      eapply IH; eauto.
  Qed.

  (** And the degenerate case the non-lifting constructors land in: renaming by
      nothing is the identity, at both levels. *)

  Lemma subst_constraints_out_map_nil :
    forall cs st, subst_constraints_out_map cs [] [] st = OK (cs, st).
  Proof. intros. reflexivity. Qed.

  (** * Domination

      The relation between a source type and the target type that replaces it
      is not equality and not a renaming: the target is a name the emitted
      equation constrains to sit *above* the source's type.  That is
      [SecTypes.satisfiable] -- [hm_ext dlt s0 ⊑ hm_ext dlt s1] -- so no new
      notion is needed, only its arithmetic.

      These are the steps the induction takes: a target name dominates the
      operands it was built from, and domination composes along a chain of
      sub-expressions. *)

  Lemma satisfiable_refl :
    forall dlt s, satisfiable dlt s s.
  Proof. intros dlt s. unfold satisfiable. apply Lat.order_refl, Lat.eq_refl. Qed.

  Lemma satisfiable_trans :
    forall dlt a b c,
      satisfiable dlt a b -> satisfiable dlt b c -> satisfiable dlt a c.
  Proof.
    intros dlt a b c Hab Hbc. unfold satisfiable in *.
    eapply Lat.order_trans; eauto.
  Qed.

  (** A merge dominates each of its sides, and is dominated by anything that
      dominates both -- which is how a defining constraint of the form
      [ambient ⊔ t ⊑ b] is taken apart and put back together. *)

  Lemma satisfiable_merge_l :
    forall dlt a b, satisfiable dlt a (merge a b).
  Proof.
    intros dlt a b. unfold satisfiable.
    rewrite hm_ext_merge_eq. apply Lat.join_bound1.
  Qed.

  Lemma satisfiable_merge_r :
    forall dlt a b, satisfiable dlt b (merge a b).
  Proof.
    intros dlt a b. unfold satisfiable.
    rewrite hm_ext_merge_eq. apply Lat.join_bound2.
  Qed.

  Lemma satisfiable_merge_intro :
    forall dlt a b c,
      satisfiable dlt a c -> satisfiable dlt b c -> satisfiable dlt (merge a b) c.
  Proof.
    intros dlt a b c Ha Hb. unfold satisfiable in *.
    rewrite hm_ext_merge_eq. now apply Lat.join_least_upper_bound.
  Qed.

  Lemma satisfiable_merge_mono :
    forall dlt c a b,
      satisfiable dlt a b -> satisfiable dlt (merge c a) (merge c b).
  Proof.
    intros dlt c a b H. apply satisfiable_merge_intro.
    - apply satisfiable_merge_l.
    - eapply satisfiable_trans; [exact H|apply satisfiable_merge_r].
  Qed.

  (** So a name constrained above a merge dominates each side of it -- the step
      that carries a source operand's type up to the variable unnesting
      created for the whole expression. *)

  Corollary satisfiable_through_merge_l :
    forall dlt a b c, satisfiable dlt (merge a b) c -> satisfiable dlt a c.
  Proof.
    intros dlt a b c H. eapply satisfiable_trans; [apply satisfiable_merge_l|exact H].
  Qed.

  Corollary satisfiable_through_merge_r :
    forall dlt a b c, satisfiable dlt (merge a b) c -> satisfiable dlt b c.
  Proof.
    intros dlt a b c H. eapply satisfiable_trans; [apply satisfiable_merge_r|exact H].
  Qed.

  (** And the form a defining constraint arrives in: [constraintSatisfiable]
      on [(lhs, [b])] is exactly domination of [b] over [lhs]. *)

  Lemma constraint_is_domination :
    forall dlt lhs b,
      constraintSatisfiable dlt (lhs, [b]) <-> satisfiable dlt lhs [b].
  Proof. intros. split; intro H; exact H. Qed.

  (** * How carried constraints propagate

      Every constructor but the call builds its result types with [ljoin],
      [ljoin_list] or [lvar], and none of those creates a constraint -- they
      merge what their operands were already carrying.  So a constructor's
      carried set is the merge of its operands' carried sets, and an
      expression carries something exactly when a call occurs inside it.

      That is the precise form of the observation that opened this leg: the
      refinement component is empty until a nested call puts something in it,
      and [to_lexps_assign_rev] saw it empty on the transcription leg because
      by then the calls had all been lifted out. *)

  Lemma carried_ljoin :
    forall a b, carried [ljoin a b] = cmerge (snd a) (snd b).
  Proof.
    intros a b. simpl. unfold ljoin. simpl. apply cmerge_nil.
  Qed.

  Lemma ljoin_list_carried :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') ->
      carried rs = cmerge (carried ts) (carried us).
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us as [|u us]; simpl in H; [|discriminate].
      unfold ret in H. inv H. reflexivity.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sta & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl. rewrite (IH _ _ _ _ Hr). unfold ljoin. simpl.
      rewrite <- !cmerge_assoc. f_equal.
      rewrite !cmerge_assoc. f_equal. apply cmerge_comm.
  Qed.

  (** A variable and a constant carry nothing, so the leaves contribute
      nothing and the whole propagation bottoms out. *)

  Lemma carried_lvar : forall d, carried [lvar d] = [].
  Proof. reflexivity. Qed.

  Lemma carried_lbot : carried [lbot] = [].
  Proof. reflexivity. Qed.


  (** * The clock environment survives the pass

      [generate_leqns_constraints] does not read the equations alone: through
      [eqn_clock_type] it looks every defined variable up in the node's
      [lnode_clock_env] to recover the clock it is defined on.  So comparing
      the two generators equation by equation is only meaningful once the two
      environments are known to answer the same way.

      Unnesting leaves [n_in] and [n_out] untouched and only *appends* to
      [n_vars].  Extension by itself would not be enough -- [Env.adds'] lets a
      later binding shadow an earlier one, so an appended name colliding with
      a declared one would silently change the answer -- but the target node
      carries its own [n_nodup], and that is exactly the statement that the
      appended names are fresh for the declared ones.  Freshness is therefore
      not assumed here; it is read off the node the pass returns. *)

  Lemma Env_find_adds'_app_notin {A : Type} :
    forall (xs ys : list (ident * A)) (m : Env.t A) x,
      ~ InMembers x ys ->
      Env.find x (Env.adds' (xs ++ ys) m) = Env.find x (Env.adds' xs m).
  Proof.
    intros * Hnin. rewrite <- Env.adds'_app. now apply Env.gsso'.
  Qed.

  (** The disjointness, stated on the shape of the pass rather than on its
      code: any node whose inputs and outputs are the source's and whose
      locals extend the source's has its extension fresh for the source. *)

  Lemma unnested_locals_fresh :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        ~ InMembers x nvars.
  Proof.
    intros n n' nvars Hin Hout Hvars x Hx.
    pose proof (n_nodup n') as Hnd.
    rewrite Hin, Hout, Hvars in Hnd.
    assert (Permutation (n_in n ++ (n_vars n ++ nvars) ++ n_out n
                           ++ anon_in_eqs (n_eqs n'))
                        ((n_in n ++ n_vars n ++ n_out n)
                           ++ nvars ++ anon_in_eqs (n_eqs n'))) as Hp.
    { repeat rewrite <- app_assoc.
      apply Permutation_app_head, Permutation_app_head, Permutation_swap. }
    rewrite Hp in Hnd.
    eapply NoDupMembers_app_InMembers in Hnd; [|exact Hx].
    intros Hn; apply Hnd, InMembers_app; auto.
  Qed.

  (** Hence the two generators read the same clocks. *)

  Lemma lnode_clock_env_extended :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        Env.find x (lnode_clock_env n') = Env.find x (lnode_clock_env n).
  Proof.
    intros n n' nvars Hin Hout Hvars x Hx.
    unfold lnode_clock_env. rewrite Hin, Hout, Hvars.
    apply Env_find_adds'_app_notin.
    eapply unnested_locals_fresh; eauto.
  Qed.

  (** What the equation level actually consumes: [find_clock], and through it
      [eqn_clock_type], cannot tell the two environments apart. *)

  Corollary find_clock_extended :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        find_clock (lnode_clock_env n') x = find_clock (lnode_clock_env n) x.
  Proof.
    intros. unfold find_clock.
    erewrite lnode_clock_env_extended; eauto.
  Qed.


  (** * The expression-level statement

      One valuation goes in, one comes out.  [dlt] satisfies what the source
      expression *carries* -- the constraints its nested calls impose on the
      fresh names the security monad minted for them.  [dlt'] satisfies what
      unnesting *emitted* -- the constraints generated for the equations the
      pass lifted out.  The two differ only off [scope]: on every security
      name the source node can see they are the same valuation, which is what
      makes this composable with the rest of the node.

      The third conjunct is the part that took the longest to get right.  It
      is not "the two sides give the expression the same type": in four of the
      five lifting cases the pass replaces a compound expression by a variable
      whose defining equation carries an ambient (the reset level joined with
      the clock the variable is defined on), so the target type is the source
      type *raised by that ambient*.  Domination in this direction --
      target below source-plus-ambient -- is exactly what the enclosing
      equation needs, because the enclosing equation sits under the same
      ambient and so absorbs it.

      [amb] is a parameter rather than a computed term: which ambient a lifted
      equation sits under is a fact about clocks, and is discharged where the
      clocks are known, not here. *)

  (** * A one-element list, and what the typer does with it

      Stated at module level rather than inside the preservation section:
      these are facts about the generator, not about the pass. *)

  Lemma assign_lexps_single :
    forall G env base_ty rst_ty e ts st st',
      assign_lexps G env base_ty rst_ty [e] st = OK (ts, st') ->
      assign_lexp_type G env base_ty rst_ty e st = OK (ts, st').
  Proof.
    intros G env base_ty rst_ty e ts st st' H.
    apply assign_lexps_carried_cons in H as (t & r & sta & Ht & Hr & Hts & _).
    apply assign_lexps_carried_nil in Hr as (Hr & _ & ?); subst.
    now rewrite app_nil_r.
  Qed.

  Lemma assign_lexps_single_intro :
    forall G env base_ty rst_ty e ts st st',
      assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
      assign_lexps G env base_ty rst_ty [e] st = OK (ts, st').
  Proof.
    intros G env base_ty rst_ty e ts st st' H.
    rewrite assign_lexps_cons.
    eapply sec_bind_ok; [exact H|].
    eapply sec_bind_ok with (y := ([] : list LST));
      [rewrite assign_lexps_nil; reflexivity|].
    unfold ret. now rewrite app_nil_r.
  Qed.

  Lemma fst_ljoin : forall a b, fst (ljoin a b) = merge (fst a) (fst b).
  Proof. reflexivity. Qed.

  Lemma snd_ljoin : forall a b, snd (ljoin a b) = cmerge (snd a) (snd b).
  Proof. reflexivity. Qed.

  Lemma snd_lvar : forall d, snd (lvar d) = [].
  Proof. reflexivity. Qed.

  Lemma fst_lvar : forall d, fst (lvar d) = [d].
  Proof. reflexivity. Qed.

  Lemma single_inv :
    forall (ts : list LST) t st st',
      single ts st = OK (t, st') -> ts = [t] /\ st' = st.
  Proof.
    intros ts t st st' H. unfold single in H.
    destruct ts as [|t0 [|]]; try discriminate.
    unfold ret in H. inv H. auto.
  Qed.

  (** * What the typer does to an already-unnested expression

      Unnesting returns normalized expressions, and a normalized expression
      contains no call.  The call case is the *only* place the security
      generator touches its state, so on the pass's output the generator is
      state-pure, and a normalized expression is given exactly one flow.

      Both facts are about what the generator does on the target side, and
      both are what let the target's types be read off in whatever order a
      constructor happens to visit its operands -- [unnest_merge] interleaves
      the two branches, where [assign_lexps] would take one branch then the
      other. *)

  Lemma carried_single : forall t, carried [t] = snd t.
  Proof. intros t. simpl. apply cmerge_nil. Qed.

  Lemma ljoin_list_pure :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') -> st' = st.
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us; simpl in H; [|discriminate].
      unfold ret in H. now inv H.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sta & Hr & Hret).
      unfold ret in Hret. inv Hret. eauto.
  Qed.

  Lemma assign_lexp_normalized_lexp_pure :
    forall G env base_ty rst_ty e,
      normalized_lexp e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        st' = st /\ List.length ts = 1 /\ carried ts = []
        /\ forall s, assign_lexp_type G env base_ty rst_ty e s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty e Hn.
    induction Hn; intros ts st st' H.
    - rewrite assign_lexp_Econst in H. unfold ret in H. inv H.
      split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
      intros s. now rewrite assign_lexp_Econst.
    - apply assign_lexp_Evar_inv in H as (b & Hb & ? & ?); subst.
      split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
      intros s. rewrite assign_lexp_Evar.
      eapply sec_bind_ok; [apply find_env_OK; exact Hb|]. reflexivity.
    - rewrite assign_lexp_Eunop in H. apply IHHn in H as (Ha & Hl & Hc & Hs).
      split; [exact Ha|split; [exact Hl|split; [exact Hc|]]].
      intros s. rewrite assign_lexp_Eunop. apply Hs.
    - rewrite assign_lexp_Ebinop in H.
      eapply sec_bind_inv in H as (t1 & sa & Ht1 & H).
      eapply sec_bind_inv in H as (t2 & sb & Ht2 & H).
      eapply sec_bind_inv in H as (a1 & sc & Ha1 & H).
      eapply sec_bind_inv in H as (a2 & sd & Ha2 & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Ha1 as (? & ?); subst.
      apply single_inv in Ha2 as (? & ?); subst.
      apply IHHn1 in Ht1 as (? & _ & Hc1 & Hs1); subst.
      apply IHHn2 in Ht2 as (? & _ & Hc2 & Hs2); subst.
      rewrite carried_single in Hc1, Hc2.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single. unfold ljoin. simpl snd.
        rewrite Hc1, Hc2. reflexivity.
      + intros s. rewrite assign_lexp_Ebinop.
        eapply sec_bind_ok; [apply Hs1|].
        eapply sec_bind_ok; [apply Hs2|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|]. reflexivity.
    - rewrite assign_lexp_Ewhen in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      apply find_env_inv in Hg as (Hgf & ?); subst.
      apply assign_lexps_single in Ht.
      apply IHHn in Ht as (? & Hlen & Hc & Hs); subst.
      destruct t as [|a [|]]; simpl in Hlen; try discriminate.
      split; [reflexivity|split; [reflexivity|split]].
      + simpl List.map. rewrite carried_single.
        rewrite carried_single in Hc.
        unfold ljoin. simpl snd. rewrite Hc. apply cmerge_nil.
      + intros s. rewrite assign_lexp_Ewhen.
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hs|].
        eapply sec_bind_ok; [apply find_env_OK; exact Hgf|]. reflexivity.
  Qed.

  Lemma assign_lexp_normalized_cexp_pure :
    forall G env base_ty rst_ty e,
      normalized_cexp e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        st' = st /\ List.length ts = 1 /\ carried ts = []
        /\ forall s, assign_lexp_type G env base_ty rst_ty e s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty e Hn.
    induction Hn as [x et ef ty cl Het IHet Hef IHef
                    | e1 et ef ty cl Hle Het IHet Hef IHef
                    | e1 Hle];
      intros ts st st' Hty.
    - rewrite assign_lexp_Emerge in Hty.
      eapply sec_bind_inv in Hty as (g & sa & Hg & Hty).
      eapply sec_bind_inv in Hty as (t & sb & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sc & Hu & Hj).
      apply find_env_inv in Hg as (Hgf & ?); subst.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      apply IHet in Ht as (? & Hlt & Hct & Hst); subst.
      apply IHef in Hu as (? & Hlu & Hcu & Hsu); subst.
      assert (st' = st) as ? by (eapply ljoin_list_pure; eauto); subst.
      destruct t as [|t0 [|]]; simpl in Hlt; try discriminate.
      destruct u as [|u0 [|]]; simpl in Hlu; try discriminate.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sd & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      rewrite carried_single in Hct, Hcu.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single.
        unfold ljoin, lvar. simpl snd. rewrite Hct, Hcu. reflexivity.
      + intros s. rewrite assign_lexp_Emerge.
        eapply sec_bind_ok; [apply find_env_OK; exact Hgf|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hst|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hsu|].
        reflexivity.
    - rewrite assign_lexp_Eite in Hty.
      eapply sec_bind_inv in Hty as (t0 & sa & Ht0 & Hty).
      eapply sec_bind_inv in Hty as (th & sb & Hth & Hty).
      eapply sec_bind_inv in Hty as (t & sc & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sd & Hu & Hj).
      apply single_inv in Hth as (? & ?); subst.
      assert (sa = st /\ List.length [th] = 1 /\ carried [th] = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s
                            = OK ([th], s))
        as (? & _ & Hcth & Hsth)
        by (eapply assign_lexp_normalized_lexp_pure with (e := e1); eauto).
      subst sa.
      rewrite carried_single in Hcth.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      apply IHet in Ht as (? & Hlt & Hct & Hst); subst.
      apply IHef in Hu as (? & Hlu & Hcu & Hsu); subst.
      assert (st' = st) as ? by (eapply ljoin_list_pure; eauto); subst.
      destruct t as [|t1 [|]]; simpl in Hlt; try discriminate.
      destruct u as [|u1 [|]]; simpl in Hlu; try discriminate.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & se & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      rewrite carried_single in Hct, Hcu.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single. unfold ljoin. simpl snd.
        rewrite Hct, Hcu, Hcth. reflexivity.
      + intros s. rewrite assign_lexp_Eite.
        eapply sec_bind_ok; [apply Hsth|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hst|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hsu|].
        reflexivity.
    - eapply assign_lexp_normalized_lexp_pure; eauto.
  Qed.

  Lemma assign_lexps_normalized_pure :
    forall G env base_ty rst_ty es,
      Forall normalized_cexp es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        st' = st /\ List.length ts = List.length es /\ carried ts = []
        /\ forall s, assign_lexps G env base_ty rst_ty es s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty es Hn.
    induction Hn as [|e es He Hes IH]; intros ts st st' H.
    - apply assign_lexps_carried_nil in H as (? & Hc & ?); subst.
      split; [reflexivity|split; [reflexivity|split; [exact Hc|]]].
      intros s. now rewrite assign_lexps_nil.
    - apply assign_lexps_carried_cons in H
        as (t & r & sta & Ht & Hr & ? & Hct); subst.
      eapply assign_lexp_normalized_cexp_pure in Ht as (? & Hlt & Hc1 & Hs1);
        eauto; subst.
      apply IH in Hr as (? & Hlr & Hc2 & Hs2); subst.
      split; [reflexivity|split; [|split]].
      + rewrite app_length, Hlt, Hlr. reflexivity.
      + rewrite Hct, Hc1, Hc2. reflexivity.
      + intros s. rewrite assign_lexps_cons.
        eapply sec_bind_ok; [apply Hs1|].
        eapply sec_bind_ok; [apply Hs2|]. reflexivity.
  Qed.

  (** Under [is_control] the merge does not lift: the branches are unnested
      and the sampling is pushed inward, one [Emerge] per resulting stream,
      exactly as [Ewhen] pushes its own. *)

  Lemma unnest_exp_Emerge_control_inv :
    forall G ckid es1 es2 tys cl es' eqs st st',
      unnest_exp G true (Emerge ckid es1 es2 (tys, cl)) st = ((es', eqs), st') ->
      exists es1' eqs1 st1 es2' eqs2,
        map_bind2 (unnest_exp G true) es1 st = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st')
        /\ es' = unnest_merge ckid (List.concat es1') (List.concat es2') tys cl
        /\ eqs = List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G ckid es1 es2 tys cl es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_merge_nil :
    forall ckid es2 tys cl, unnest_merge ckid [] es2 tys cl = [].
  Proof. reflexivity. Qed.

  Lemma unnest_merge_cons :
    forall ckid e1 es1 e2 es2 ty tys cl,
      unnest_merge ckid (e1 :: es1) (e2 :: es2) (ty :: tys) cl
      = Emerge ckid [e1] [e2] ([ty], cl) :: unnest_merge ckid es1 es2 tys cl.
  Proof. reflexivity. Qed.

  (** And the typer reads it back as the same function of the branches'
      types that the source rule is of the source branches' types.  Purity is
      what makes the interleaving harmless: every sub-call starts and ends at
      the state the whole list started at. *)

  Lemma assign_lexps_unnest_merge_inv :
    forall G env base_ty rst_ty ckid cl g (es1 es2 : list exp)
           (tys : list type) ts'' st st',
      Env.find ckid env = Some g ->
      Forall normalized_cexp es1 ->
      Forall normalized_cexp es2 ->
      List.length es1 = List.length tys ->
      List.length es2 = List.length tys ->
      assign_lexps G env base_ty rst_ty (unnest_merge ckid es1 es2 tys cl) st
        = OK (ts'', st') ->
      exists ts us,
        assign_lexps G env base_ty rst_ty es1 st = OK (ts, st)
        /\ assign_lexps G env base_ty rst_ty es2 st = OK (us, st)
        /\ st' = st
        /\ ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us st
           = OK (ts'', st).
  Proof.
    intros G env base_ty rst_ty ckid cl g es1.
    induction es1 as [|e1 es1 IH];
      intros es2 tys ts'' st st' Hg Hn1 Hn2 Hl1 Hl2 Has.
    - destruct tys; simpl in Hl1; try discriminate.
      destruct es2; simpl in Hl2; try discriminate.
      rewrite unnest_merge_nil in Has.
      apply assign_lexps_carried_nil in Has as (? & _ & ?); subst.
      exists [], []. rewrite assign_lexps_nil. repeat split; reflexivity.
    - destruct tys as [|ty tys]; simpl in Hl1; try discriminate.
      destruct es2 as [|e2 es2]; simpl in Hl2; try discriminate.
      inv Hn1. inv Hn2.
      rewrite unnest_merge_cons in Has.
      apply assign_lexps_carried_cons in Has
        as (t0 & r & sta & Ht0 & Hr & ? & _); subst.
      (** the head merge *)
      rewrite assign_lexp_Emerge in Ht0.
      eapply sec_bind_inv in Ht0 as (g' & sa & Hg' & Ht0).
      eapply sec_bind_inv in Ht0 as (t & sb & Ht & Ht0).
      eapply sec_bind_inv in Ht0 as (u & sc & Hu & Hj).
      apply find_env_inv in Hg' as (Hg' & ?); subst.
      rewrite Hg in Hg'. inv Hg'.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      assert (sb = st /\ List.length t = 1 /\ carried t = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s = OK (t, s))
        as (? & Hlt & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
      subst sb.
      assert (sc = st /\ List.length u = 1 /\ carried u = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e2 s = OK (u, s))
        as (? & Hlu & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
      subst sc.
      assert (sta = st) as ? by (eapply ljoin_list_pure; eauto). subst sta.
      apply IH in Hr as (ts & us & Hts & Hus & ? & Hjr); auto; subst.
      exists (t ++ ts), (u ++ us). split; [|split; [|split]]; auto.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [exact Hts|]. reflexivity.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Hu|].
        eapply sec_bind_ok; [exact Hus|]. reflexivity.
      + destruct t as [|a [|]]; simpl in Hlt; try discriminate.
        destruct u as [|b [|]]; simpl in Hlu; try discriminate.
        simpl List.map. simpl List.app.
        eapply sec_bind_ok; [exact Hjr|].
        simpl in Hj.
        eapply sec_bind_inv in Hj as (r0 & sd & Hr0 & Hret).
        unfold ret in Hret. inv Hret.
        simpl in Hr0. unfold ret in Hr0. inv Hr0. reflexivity.
  Qed.

  Lemma unnest_exp_Eite_control_inv :
    forall G e es1 es2 tys ck es' eqs st st',
      unnest_exp G true (Eite e es1 es2 (tys, ck)) st = ((es', eqs), st') ->
      exists e' eqs0 st0 es1' eqs1 st1 es2' eqs2,
        unnest_exp G false e st = ((e', eqs0), st0)
        /\ map_bind2 (unnest_exp G true) es1 st0 = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st')
        /\ es' = unnest_ite (hd_default e') (List.concat es1')
                   (List.concat es2') tys ck
        /\ eqs = eqs0 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G e es1 es2 tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_ite_nil :
    forall e es2 tys ck, unnest_ite e [] es2 tys ck = [].
  Proof. reflexivity. Qed.

  Lemma unnest_ite_cons :
    forall e e1 es1 e2 es2 ty tys ck,
      unnest_ite e (e1 :: es1) (e2 :: es2) (ty :: tys) ck
      = Eite e [e1] [e2] ([ty], ck) :: unnest_ite e es1 es2 tys ck.
  Proof. reflexivity. Qed.

  (** The scrutinee is typed once per resulting stream rather than once, but
      it is normalized, so the generator gives it the same answer every time
      and never moves the state.  That is the whole difference from the merge
      inversion above. *)

  Lemma assign_lexps_unnest_ite_inv :
    forall G env base_ty rst_ty e0 ck (es1 es2 : list exp)
           (tys : list type) ts'' st st',
      normalized_lexp e0 ->
      Forall normalized_cexp es1 ->
      Forall normalized_cexp es2 ->
      List.length es1 = List.length tys ->
      List.length es2 = List.length tys ->
      assign_lexps G env base_ty rst_ty (unnest_ite e0 es1 es2 tys ck) st
        = OK (ts'', st') ->
      st' = st
      /\ exists ts us,
           assign_lexps G env base_ty rst_ty es1 st = OK (ts, st)
           /\ assign_lexps G env base_ty rst_ty es2 st = OK (us, st)
           /\ ((exists th,
                   assign_lexp_type G env base_ty rst_ty e0 st = OK ([th], st)
                   /\ ljoin_list (List.map (fun t => ljoin th t) ts) us st
                      = OK (ts'', st))
               \/ (ts = [] /\ us = [] /\ ts'' = [])).
  Proof.
    intros G env base_ty rst_ty e0 ck es1.
    induction es1 as [|e1 es1 IH];
      intros es2 tys ts'' st st' Hn0 Hn1 Hn2 Hl1 Hl2 Has.
    - destruct tys; simpl in Hl1; try discriminate.
      destruct es2; simpl in Hl2; try discriminate.
      rewrite unnest_ite_nil in Has.
      apply assign_lexps_carried_nil in Has as (? & _ & ?); subst.
      split; auto. exists [], []. rewrite assign_lexps_nil.
      split; [reflexivity|split; [reflexivity|]]. right; auto.
    - destruct tys as [|ty tys]; simpl in Hl1; try discriminate.
      destruct es2 as [|e2 es2]; simpl in Hl2; try discriminate.
      inv Hn1. inv Hn2.
      rewrite unnest_ite_cons in Has.
      apply assign_lexps_carried_cons in Has
        as (t0 & r & sta & Ht0 & Hr & ? & _); subst.
      rewrite assign_lexp_Eite in Ht0.
      eapply sec_bind_inv in Ht0 as (t0' & sa & Ht0' & Ht0).
      eapply sec_bind_inv in Ht0 as (th & sb & Hth & Ht0).
      eapply sec_bind_inv in Ht0 as (t & sc & Ht & Ht0).
      eapply sec_bind_inv in Ht0 as (u & sd & Hu & Hj).
      assert (sa = st /\ List.length t0' = 1 /\ carried t0' = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e0 s
                            = OK (t0', s))
        as (? & _ & _ & _)
        by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
      subst sa.
      apply single_inv in Hth as (? & ?); subst.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      assert (sc = st /\ List.length t = 1 /\ carried t = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s = OK (t, s))
        as (? & Hlt & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
      subst sc.
      assert (sd = st /\ List.length u = 1 /\ carried u = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e2 s = OK (u, s))
        as (? & Hlu & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
      subst sd.
      assert (sta = st) as ? by (eapply ljoin_list_pure; eauto). subst sta.
      apply IH in Hr as (? & ts & us & Hts & Hus & Hrest); auto. subst.
      destruct t as [|a [|]]; simpl in Hlt; try discriminate.
      destruct u as [|b [|]]; simpl in Hlu; try discriminate.
      simpl in Hj.
      eapply sec_bind_inv in Hj as (r0 & se & Hr0 & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr0. unfold ret in Hr0. inv Hr0.
      split; auto.
      exists (a :: ts), (b :: us). split; [|split].
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [exact Hts|]. reflexivity.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Hu|].
        eapply sec_bind_ok; [exact Hus|]. reflexivity.
      + left. exists th. split; [exact Ht0'|].
        simpl List.map.
        eapply sec_bind_ok; [|reflexivity].
        destruct Hrest as [(th' & Hth' & Hjr)|(? & ? & ?)]; subst.
        * rewrite Ht0' in Hth'. inv Hth'. exact Hjr.
        * simpl. reflexivity.
  Qed.

  (** * How many flows the generator returns

      One per stream, exactly as the pass returns one expression per stream.
      Needed wherever the two sides have to be lined up positionally, and at
      the equation level to match a defined variable to its flow. *)

  Lemma ljoin_list_length :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') -> List.length rs = List.length ts.
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us; simpl in H; [|discriminate].
      unfold ret in H. inv H. reflexivity.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sa & Hr & Hret).
      unfold ret in Hret. inv Hret. simpl. f_equal. eauto.
  Qed.

  Lemma assign_lexps_length_aux :
    forall P G env base_ty rst_ty es,
      Forall (fun e => wl_exp P e -> forall ts st st',
                  assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
                  List.length ts = numstreams e) es ->
      Forall (wl_exp P) es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        List.length ts = List.length (annots es).
  Proof.
    intros P G env base_ty rst_ty es Hall.
    induction Hall as [|e es He Hes IH]; intros Hwl ts st st' H.
    - apply assign_lexps_carried_nil in H as (? & _ & ?); subst. reflexivity.
    - inv Hwl.
      apply assign_lexps_carried_cons in H as (t & r & sta & Ht & Hr & ? & _);
        subst.
      unfold annots. simpl List.flat_map. fold (annots es).
      rewrite !app_length. f_equal.
      + rewrite length_annot_numstreams. eapply He; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma assign_lexp_type_length :
    forall P G env base_ty rst_ty e,
      wl_exp P e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        List.length ts = numstreams e.
  Proof.
    intros P G env base_ty rst_ty e.
    induction e using exp_ind2; intros Hwl ts st st' Hty; inv Hwl.
    - rewrite assign_lexp_Econst in Hty. unfold ret in Hty. now inv Hty.
    - apply assign_lexp_Evar_inv in Hty as (? & _ & ? & _); subst. reflexivity.
    - rewrite assign_lexp_Eunop in Hty.
      assert (List.length ts = numstreams e) as Hl by (eapply IHe; eauto).
      simpl. rewrite Hl. assumption.
    - rewrite assign_lexp_Ebinop in Hty.
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hret).
      unfold ret in Hret. now inv Hret.
    - (** fby *)
      rewrite assign_lexp_Efby in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sb & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots e0s)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      rewrite Hl. simpl. assumption.
    - (** arrow *)
      rewrite assign_lexp_Earrow in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sb & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots e0s)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      rewrite Hl. simpl. assumption.
    - (** when *)
      rewrite assign_lexp_Ewhen in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      assert (List.length t = List.length (annots es)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** merge *)
      rewrite assign_lexp_Emerge in Hty.
      eapply sec_bind_inv in Hty as (g & sa & Hg & Hty).
      eapply sec_bind_inv in Hty as (t & sb & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sc & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots ets)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** ite *)
      rewrite assign_lexp_Eite in Hty.
      eapply sec_bind_inv in Hty as (t0 & sa & Ht0 & Hty).
      eapply sec_bind_inv in Hty as (th & sb & Hth & Hty).
      eapply sec_bind_inv in Hty as (t & sc & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sd & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots ets)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** call, and call with a reset: [wl_exp] has a rule for each, and the
          generator does not distinguish them here *)
      apply assign_lexp_Eapp_inv in Hty
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & _ & _ & _ & _ & Houts & _ & ?); subst.
      apply fresh_idents_length in Houts.
      simpl. rewrite map_length. assumption.
    - apply assign_lexp_Eapp_inv in Hty
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & _ & _ & _ & _ & Houts & _ & ?); subst.
      apply fresh_idents_length in Houts.
      simpl. rewrite map_length. assumption.
  Qed.

  Corollary assign_lexps_length :
    forall P G env base_ty rst_ty es,
      Forall (wl_exp P) es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        List.length ts = List.length (annots es).
  Proof.
    intros. eapply assign_lexps_length_aux; eauto.
    apply Forall_forall. intros e He Hwl.
    eapply assign_lexp_type_length; eauto.
  Qed.

  (** The clocking rules pin the annotation's clock, so inverting one
      substitutes it away.  These keep the annotation abstract, which the
      lifting cases need because they mention it. *)

  Lemma wc_Emerge_inv :
    forall P vars ckid es1 es2 tys cl,
      wc_exp P vars (Emerge ckid es1 es2 (tys, cl)) ->
      Forall (wc_exp P vars) es1 /\ Forall (wc_exp P vars) es2.
  Proof. intros * H. inv H. auto. Qed.

  Lemma wc_Eifte_inv :
    forall P vars e es1 es2 tys cl,
      wc_exp P vars (Eite e es1 es2 (tys, cl)) ->
      wc_exp P vars e
      /\ Forall (wc_exp P vars) es1 /\ Forall (wc_exp P vars) es2
      /\ 0 < List.length tys.
  Proof. intros * H. inv H. auto. Qed.


End SecLusUnnestingBase.
