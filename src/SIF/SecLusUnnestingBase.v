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

  (** * The security monad's state only advances

      [sec_state] is a positive and every allocation takes [Pos.succ], so a
      successful run never moves the counter backwards.  This is what lets a
      *finite* scope contain the names a run mints: the names live in the
      window between the state the run starts at and the state it ends at,
      and the run's sub-runs all lie inside that window.

      Without it the scoping hypotheses of the leg quantify over every state
      and so demand that a finite [scope] contain [Ids.gensym Ids.sec n] for
      unboundedly many [n] -- which no [scope] does.  The window is the
      "checkmark": names generated in lockstep up to it are the ones whose
      identity has to be tracked, and no others. *)

  Definition sec_le (s s' : sec_state) : Prop := Pos.le s s'.

  Lemma sec_le_refl : forall s, sec_le s s.
  Proof. intro s. apply Pos.le_refl. Qed.

  Lemma sec_le_trans : forall s1 s2 s3, sec_le s1 s2 -> sec_le s2 s3 -> sec_le s1 s3.
  Proof. intros s1 s2 s3. apply Pos.le_trans. Qed.

  Lemma sec_le_succ : forall s, sec_le s (Pos.succ s).
  Proof.
    intro s. unfold sec_le. apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  Lemma state_pure_sec_le :
    forall {A} (m : Sec A) a s s',
      state_pure m -> m s = OK (a, s') -> sec_le s s'.
  Proof.
    intros A m a s s' Hp Hm.
    destruct (Hp s s a s' Hm) as (Heq & _). subst s'. apply sec_le_refl.
  Qed.

  Lemma sec_bind_le :
    forall {A B} (m : Sec A) (f : A -> Sec B) b s s',
      (forall a s1 s2, m s1 = OK (a, s2) -> sec_le s1 s2) ->
      (forall a b' s1 s2, f a s1 = OK (b', s2) -> sec_le s1 s2) ->
      SC.bind m f s = OK (b, s') -> sec_le s s'.
  Proof.
    intros A B m f b s s' Hm Hf H.
    apply sec_bind_inv in H as (a & s1 & Ha & Hb).
    apply (sec_le_trans _ s1 _); [exact (Hm a s s1 Ha)|].
    exact (Hf a b s1 s' Hb).
  Qed.

  Lemma fresh_ident_sec_le :
    forall x s s', SC.fresh_ident s = OK (x, s') -> sec_le s s'.
  Proof.
    intros x s s' H. unfold SC.fresh_ident in H.
    inversion H; subst. apply sec_le_succ.
  Qed.

  Lemma fresh_idents_sec_le :
    forall n xs s s', fresh_idents n s = OK (xs, s') -> sec_le s s'.
  Proof.
    induction n as [|n IH]; intros xs s s' H; simpl in H.
    - unfold SC.ret in H. inversion H; subst. apply sec_le_refl.
    - apply sec_bind_inv in H as (x & s1 & Hx & H).
      apply sec_bind_inv in H as (ys & s2 & Hys & Hret).
      unfold SC.ret in Hret. inversion Hret; subst.
      apply (sec_le_trans _ s1 _); [exact (fresh_ident_sec_le x s s1 Hx)|].
      exact (IH ys s1 s' Hys).
  Qed.

  (** * The window a run mints in

      [minted s s'] lists [gensym sec s, …, gensym sec (s'-1)] -- exactly the
      names a run from [s] to [s'] can have minted, since [fresh_ident] is the
      only thing that moves the state and it mints at the state it is at.

      Two facts make the window usable.  Membership is *exactly* "a [sec]
      gensym at an index in [s, s')", which is what lets a name be shown
      *not* to be minted; and the window only widens, so a sub-run's names
      sit inside its parent's.  Together they are what discharges the call
      case of the dependency property: a call's result names are minted, so a
      name known not to be minted cannot be one of them. *)

  Lemma sec_span_spec :
    forall k s x,
      In x (sec_span s k) <->
      exists j, Pos.le s j
                /\ (Pos.to_nat j < Pos.to_nat s + k)%nat
                /\ x = Ids.gensym Ids.sec j.
  Proof.
    induction k as [|k IH]; intros s x; simpl.
    - split; [contradiction|].
      intros (j & Hsj & Hlt & _).
      apply Pos2Nat.inj_le in Hsj. lia.
    - split.
      + intros [Hx|Hx].
        * exists s. split; [apply Pos.le_refl|].
          split; [lia|exact (@Coq.Init.Logic.eq_sym _ _ _ Hx)].
        * apply IH in Hx as (j & Hsj & Hlt & Hxj).
          rewrite Pos2Nat.inj_succ in Hlt.
          exists j. split; [|split; [lia|exact Hxj]].
          apply (Pos.le_trans s (Pos.succ s) j);
            [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hsj].
      + intros (j & Hsj & Hlt & Hxj); subst x.
        apply Pos.lt_eq_cases in Hsj as [Hlt'|Heq].
        * right. apply IH. exists j.
          split; [apply Pos.le_succ_l; exact Hlt'|].
          split; [rewrite Pos2Nat.inj_succ; lia|reflexivity].
        * subst j. now left.
  Qed.

  Lemma minted_spec :
    forall s s' x,
      In x (minted s s') <->
      exists j, Pos.le s j /\ Pos.lt j s' /\ x = Ids.gensym Ids.sec j.
  Proof.
    intros s s' x. unfold minted. rewrite sec_span_spec.
    split; intros (j & Hsj & Hlt & Hxj); exists j;
      (split; [exact Hsj|]); (split; [|exact Hxj]).
    - apply Pos2Nat.inj_lt. apply Pos2Nat.inj_le in Hsj. lia.
    - apply Pos2Nat.inj_lt in Hlt. apply Pos2Nat.inj_le in Hsj. lia.
  Qed.

  Corollary minted_gensym :
    forall s s' x, In x (minted s s') -> exists j, x = Ids.gensym Ids.sec j.
  Proof.
    intros s s' x Hx. apply minted_spec in Hx as (j & _ & _ & ?).
    now exists j.
  Qed.

  (** The window only widens: a sub-run of a bounded run mints inside it. *)
  Corollary minted_window :
    forall s1 s s' s1',
      sec_le s1 s -> sec_le s' s1' -> incl (minted s s') (minted s1 s1').
  Proof.
    intros s1 s s' s1' H1 H2 x Hx.
    apply minted_spec in Hx as (j & Hsj & Hlt & Hxj).
    apply minted_spec. exists j.
    split; [exact (Pos.le_trans s1 s j H1 Hsj)|].
    split; [exact (Pos.lt_le_trans j s' s1' Hlt H2)|exact Hxj].
  Qed.

  Lemma fresh_ident_minted :
    forall x s s', SC.fresh_ident s = OK (x, s') -> In x (minted s s').
  Proof.
    intros x s s' H. unfold SC.fresh_ident in H. inversion H; subst.
    apply minted_spec. exists s.
    split; [apply Pos.le_refl|].
    split; [apply Pos.lt_succ_diag_r|reflexivity].
  Qed.

  Lemma fresh_idents_minted :
    forall n xs s s', fresh_idents n s = OK (xs, s') -> incl xs (minted s s').
  Proof.
    induction n as [|n IH]; intros xs s s' H; simpl in H.
    - unfold SC.ret in H. inversion H; subst. intros x [].
    - apply sec_bind_inv in H as (x & s1 & Hx & H).
      apply sec_bind_inv in H as (ys & s2 & Hys & Hret).
      unfold SC.ret in Hret. inversion Hret; subst.
      intros z [Hz|Hz].
      + subst z.
        apply (minted_window s s s1 s');
          [apply sec_le_refl|exact (fresh_idents_sec_le n ys s1 s' Hys)|].
        exact (fresh_ident_minted x s s1 Hx).
      + apply (minted_window s s1 s' s');
          [exact (fresh_ident_sec_le x s s1 Hx)|apply sec_le_refl|].
        exact (IH ys s1 s' Hys z Hz).
  Qed.

  (** * The scoping context of a typing run, stated once

      These three were declared, identically, in five separate sections --
      and carried the same defect in all five.  Stating them here means the
      sections quote a name rather than a body, so they cannot drift.

      Each is bounded above by a checkmark state [stF].  Without that bound
      they quantify over every state, and since a call's result type is
      [gensym sec s] for the state [s] the run is at, they would demand that
      a finite [scope] contain unboundedly many names -- unsatisfiable for
      any program with a call.  With it, a run's minted names lie in a
      window (see [assign_lexp_type_sec_le]) and a [scope] containing
      [minted st0 stF] covers them. *)

  (** A name the caller side may use in an actual: a name of the visible
      scope, or the security name of some variable of the node (the images of
      the variables unnesting creates are of the second kind). *)
  Definition caller_name (env : Env.t ident) (scope : list ident)
      (y : ident) : Prop :=
    In y scope \/ exists x, Env.find x env = Some y.

  Definition caller_st (env : Env.t ident) (scope : list ident)
      (st : ST) : Prop :=
    forall y, In y st -> caller_name env scope y.

  (** * Source clocks

      The clock types the node typer builds are built from the variables a
      clock mentions.  [clk_src] says a clock mentions only variables of the
      node, or variables mentioned by the clocks of the given expressions --
      which is what a well-clocked source expression's clocks do, and what the
      base clock of a call's arguments (a common suffix of their clocks) does.
      A clock that mentions a variable unnesting created is not a source
      clock, and the scoping hypotheses are not asked of it. *)
  Fixpoint ck_vars (ck : clock) : list ident :=
    match ck with
    | Cbase => []
    | Con ck' x _ => x :: ck_vars ck'
    end.

  Definition clk_src (vars : list (ident * clock)) (es : list exp)
      (ck : clock) : Prop :=
    incl (ck_vars ck) (List.map fst vars ++ flat_map ck_vars (clocksof es)).

  Lemma clk_src_in :
    forall vars es ck, In ck (clocksof es) -> clk_src vars es ck.
  Proof.
    intros vars es ck Hin x Hx. apply in_or_app. right.
    apply in_flat_map. exists ck. split; assumption.
  Qed.

  Lemma wc_equation_lhs_vars :
    forall P vars xs es,
      wc_equation P vars (xs, es) -> incl xs (List.map fst vars).
  Proof.
    intros P vars xs es (_ & _ & H).
    induction H as [|y ck xs cks Hy Hr IH]; intros x Hx; [contradiction|].
    destruct Hx as [Hxy|Hx].
    - subst. apply in_map_iff. exists (x, ck). split; [reflexivity|exact Hy].
    - exact (IH x Hx).
  Qed.

  Lemma wc_equations_vars_defined :
    forall P vars eqs,
      Forall (wc_equation P vars) eqs ->
      incl (vars_defined eqs) (List.map fst vars).
  Proof.
    intros P vars eqs. induction 1 as [|eq eqs Heq Hr IH]; intros x Hx.
    - contradiction.
    - unfold vars_defined in Hx. simpl in Hx. apply in_app_or in Hx as [Hx|Hx].
      + destruct eq as (xs, es). exact (wc_equation_lhs_vars P vars xs es Heq x Hx).
      + exact (IH x Hx).
  Qed.

  Lemma clk_src_clockof :
    forall vars e ck, In ck (clockof e) -> clk_src vars [e] ck.
  Proof.
    intros vars e ck Hin. apply clk_src_in.
    unfold clocksof. simpl. rewrite app_nil_r. exact Hin.
  Qed.

  Lemma clk_src_hd_clockof :
    forall vars e, clk_src vars [e] (hd Cbase (clockof e)).
  Proof.
    intros vars e. destruct (clockof e) as [|ck cks] eqn:E.
    - intros x []. 
    - apply clk_src_clockof. rewrite E. now left.
  Qed.

  Lemma ck_vars_of_suffix :
    forall sfx ck,
      incl (ck_vars (clock_of_suffix sfx ck)) (List.map fst sfx ++ ck_vars ck).
  Proof.
    induction sfx as [|[x b] sfx IH]; intros ck y Hy.
    - exact Hy.
    - simpl in Hy. specialize (IH (Con ck x b) y Hy).
      apply in_app_or in IH as [IH|IH]; [apply in_or_app; left; now right|].
      simpl in IH. destruct IH as [->|IH];
        [apply in_or_app; left; now left|apply in_or_app; now right].
  Qed.

  Lemma common_suffix_incl :
    forall a b p, In p (common_suffix a b) -> In p a.
  Proof.
    induction a as [|[x1 b1] a IH]; intros [|[x2 b2] b] p Hp; simpl in Hp;
      try contradiction.
    destruct (Pos.eqb x1 x2 && (b1 ==b b2)); [|contradiction].
    destruct Hp as [<-|Hp]; [now left|right; eapply IH; exact Hp].
  Qed.

  Lemma suffix_of_clock_vars :
    forall ck acc,
      incl (List.map fst (suffix_of_clock ck acc)) (ck_vars ck ++ List.map fst acc).
  Proof.
    induction ck as [|ck IH x b]; intros acc y Hy.
    - exact Hy.
    - simpl in Hy. specialize (IH ((x, b) :: acc) y Hy).
      apply in_app_or in IH as [IH|IH]; [apply in_or_app; left; now right|].
      simpl in IH. destruct IH as [->|IH];
        [apply in_or_app; left; now left|apply in_or_app; now right].
  Qed.

  Lemma find_base_clock_vars :
    forall cks,
      incl (ck_vars (find_base_clock cks)) (flat_map ck_vars cks).
  Proof.
    intros [|ck cks]; [intros y []|].
    unfold find_base_clock.
    set (acc0 := suffix_of_clock ck []).
    assert (forall cks0 sfx0,
              (forall p, In p sfx0 -> In (fst p) (ck_vars ck)) ->
              forall p, In p (fold_left
                (fun sfx1 ck2 => common_suffix sfx1 (suffix_of_clock ck2 []))
                cks0 sfx0) -> In (fst p) (ck_vars ck)) as Hfold.
    { induction cks0 as [|c cks0 IH]; intros sfx0 Hs p Hp; simpl in Hp.
      - exact (Hs p Hp).
      - eapply IH; [|exact Hp]. intros q Hq.
        apply Hs. eapply common_suffix_incl; exact Hq. }
    intros y Hy.
    pose proof (ck_vars_of_suffix
                  (fold_left
                     (fun sfx1 ck2 =>
                        common_suffix sfx1 (suffix_of_clock ck2 []))
                     cks acc0) Cbase y Hy) as Hy'.
    simpl in Hy'. rewrite app_nil_r in Hy'.
    apply in_map_iff in Hy' as (p & <- & Hp).
    simpl. apply in_or_app. left.
    refine (Hfold cks acc0 _ p Hp).
    intros q Hq. subst acc0.
    pose proof (suffix_of_clock_vars ck [] (fst q)
                  (in_map fst _ _ Hq)) as H. simpl in H.
    rewrite app_nil_r in H. exact H.
  Qed.

  Lemma clk_src_base :
    forall vars es,
      clk_src vars es (find_base_clock (clocksof es)).
  Proof.
    intros vars es x Hx. apply in_or_app. right.
    exact (find_base_clock_vars _ x Hx).
  Qed.

  (** The three scoping statements speak about the runs the source
      generator actually performs: source expressions (well clocked in the
      node's variables, so a created variable's name never occurs) and start
      states inside the window [stS, stF] the node's run lives in. *)
  Definition source_types_scoped_upto
      (GL : secglobal) (env : Env.t ident) (base_ty rst_ty : ident)
      (vars : list (ident * clock))
      (scope : list ident) (stLo stF : sec_state) : Prop :=
    forall P e ts s s',
      wc_exp P vars e ->
      sec_le stLo s ->
      assign_lexp_type GL env base_ty rst_ty e s = OK (ts, s') ->
      sec_le s' stF ->
      Forall (fun t => st_scoped scope (fst t)) ts.

  Definition source_lexps_scoped_upto
      (GL : secglobal) (env : Env.t ident) (base_ty rst_ty : ident)
      (vars : list (ident * clock))
      (scope : list ident) (stLo stF : sec_state) : Prop :=
    forall P es ts s s',
      Forall (wc_exp P vars) es ->
      sec_le stLo s ->
      assign_lexps GL env base_ty rst_ty es s = OK (ts, s') ->
      sec_le s' stF ->
      Forall (fun t => st_scoped scope (fst t)) ts.

  Definition source_lexps_carried_scoped_upto
      (GL : secglobal) (env : Env.t ident) (base_ty rst_ty : ident)
      (vars : list (ident * clock))
      (scope : list ident) (stLo stF : sec_state) : Prop :=
    forall P es ts s s',
      Forall (wc_exp P vars) es ->
      sec_le stLo s ->
      assign_lexps GL env base_ty rst_ty es s = OK (ts, s') ->
      sec_le s' stF ->
      constraints_scoped scope (carried ts).

  (** * Satisfaction depends only on the names a constraint mentions

      [hm_ext] is a join over the members of a type, so a valuation cannot
      tell two types with the same members apart.  Two consequences, both
      used by the call case: a type below another by inclusion is below it
      under every valuation, and two constraint lists whose sources have the
      same members are satisfied by exactly the same valuations.

      The second is what lets a call's argument types be *augmented* with the
      actuals of their own clock variables before the signature is
      instantiated.  The dependency property says those actuals are already
      in any constraint that mentions the argument, so the augmentation adds
      no member and changes no obligation -- while making the uniform
      ambient of [generate_constraints_mono_sem] correct, because each
      argument's ambient is then contained in the call's base ambient joined
      with the argument's own augmented type. *)

  Lemma satisfiable_of_incl :
    forall dlt a b, (forall z, In z a -> In z b) -> satisfiable dlt a b.
  Proof. intros dlt a b H. unfold satisfiable. apply hm_ext_incl. exact H. Qed.

  Lemma satisfiable_same_names :
    forall dlt a a' b b',
      (forall z, In z a <-> In z a') ->
      (forall z, In z b <-> In z b') ->
      satisfiable dlt a b -> satisfiable dlt a' b'.
  Proof.
    intros dlt a a' b b' Ha Hb H. unfold satisfiable in H |- *.
    apply Lat.order_trans with (y := hm_ext dlt a).
    - apply hm_ext_incl. intros z Hz. now apply Ha.
    - apply Lat.order_trans with (y := hm_ext dlt b); [exact H|].
      apply hm_ext_incl. intros z Hz. now apply Hb.
  Qed.

  Lemma listSatisfiable_same_sources :
    forall dlt cs cs',
      Forall2
        (fun c c' =>
           (forall z, In z (fst c) <-> In z (fst c'))
           /\ (forall z, In z (snd c) <-> In z (snd c'))) cs cs' ->
      listSatisfiable dlt cs ->
      listSatisfiable dlt cs'.
  Proof.
    intros dlt cs cs' Hrel Hsat.
    induction Hrel as [|c c' l l' (Hs & Ht) Hr IH]; [constructor|].
    inversion Hsat as [|z zs Hz Hzs]; subst.
    constructor; [|exact (IH Hzs)].
    destruct c as (s1 & t1). destruct c' as (s2 & t2).
    simpl in Hs, Ht. unfold constraintSatisfiable in Hz |- *.
    exact (satisfiable_same_names dlt s1 s2 t1 t2 Hs Ht Hz).
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

  (** Typing an expression advances the counter monotonically: the only thing
      that moves it is [fresh_idents] in the call case. *)

  Lemma assign_lexps_sec_le_of :
    forall G env base_ty rst_ty es,
      Forall (fun e => forall ts s s',
                  assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
                  sec_le s s') es ->
      forall ts s s',
        assign_lexps G env base_ty rst_ty es s = OK (ts, s') -> sec_le s s'.
  Proof.
    intros G env base_ty rst_ty es Hall.
    induction Hall as [|e es He Hes IH]; intros ts s s' H.
    - rewrite assign_lexps_nil in H. unfold SC.ret in H.
      inversion H; subst. apply sec_le_refl.
    - rewrite assign_lexps_cons in H.
      apply sec_bind_inv in H as (t & s1 & Ht & H).
      apply sec_bind_inv in H as (r & s2 & Hr & Hret).
      unfold SC.ret in Hret. inversion Hret; subst.
      apply (sec_le_trans _ s1 _); [exact (He t s s1 Ht)|].
      exact (IH r s1 s' Hr).
  Qed.

  Lemma assign_lexp_type_sec_le :
    forall G env base_ty rst_ty e ts s s',
      assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') -> sec_le s s'.
  Proof.
    intros G env base_ty rst_ty e.
    induction e using exp_ind2; intros ts s s' Hrun.
    - (** Econst *)
      rewrite assign_lexp_Econst in Hrun. unfold SC.ret in Hrun.
      inversion Hrun; subst. apply sec_le_refl.
    - (** Evar *)
      rewrite assign_lexp_Evar in Hrun.
      apply sec_bind_inv in Hrun as (b & s1 & Hb & Hret).
      apply find_env_inv in Hb as (_ & ?); subst s1.
      unfold SC.ret in Hret. inversion Hret; subst. apply sec_le_refl.
    - (** Eunop *)
      rewrite assign_lexp_Eunop in Hrun. exact (IHe ts s s' Hrun).
    - (** Ebinop *)
      rewrite assign_lexp_Ebinop in Hrun.
      apply sec_bind_inv in Hrun as (t1 & s1 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (t2 & s2 & Ht2 & Hrun).
      apply sec_bind_inv in Hrun as (a1 & s3 & Ha1 & Hrun).
      apply single_inv in Ha1 as (_ & ?); subst s3.
      apply sec_bind_inv in Hrun as (a2 & s4 & Ha2 & Hret).
      apply single_inv in Ha2 as (_ & ?); subst s4.
      unfold SC.ret in Hret. inversion Hret; subst.
      apply (sec_le_trans _ s1 _); [exact (IHe1 t1 s s1 Ht1)|].
      exact (IHe2 t2 s1 s' Ht2).
    - (** Efby *)
      rewrite assign_lexp_Efby in Hrun.
      apply sec_bind_inv in Hrun as (t1 & s1 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (t2 & s2 & Ht2 & Hj).
      apply (sec_le_trans _ s1 _).
      + exact (assign_lexps_sec_le_of G env base_ty rst_ty e0s H t1 s s1 Ht1).
      + apply (sec_le_trans _ s2 _).
        * exact (assign_lexps_sec_le_of G env base_ty rst_ty es H0 t2 s1 s2 Ht2).
        * rewrite (ljoin_list_pure t1 t2 ts s2 s' Hj). apply sec_le_refl.
    - (** Earrow *)
      rewrite assign_lexp_Earrow in Hrun.
      apply sec_bind_inv in Hrun as (t1 & s1 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (t2 & s2 & Ht2 & Hj).
      apply (sec_le_trans _ s1 _).
      + exact (assign_lexps_sec_le_of G env base_ty rst_ty e0s H t1 s s1 Ht1).
      + apply (sec_le_trans _ s2 _).
        * exact (assign_lexps_sec_le_of G env base_ty rst_ty es H0 t2 s1 s2 Ht2).
        * rewrite (ljoin_list_pure t1 t2 ts s2 s' Hj). apply sec_le_refl.
    - (** Ewhen *)
      rewrite assign_lexp_Ewhen in Hrun.
      apply sec_bind_inv in Hrun as (t1 & s1 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (g & s2 & Hg & Hret).
      apply find_env_inv in Hg as (_ & ?); subst s2.
      unfold SC.ret in Hret. inversion Hret; subst.
      exact (assign_lexps_sec_le_of G env base_ty rst_ty es H t1 s s' Ht1).
    - (** Emerge *)
      rewrite assign_lexp_Emerge in Hrun.
      apply sec_bind_inv in Hrun as (g & s1 & Hg & Hrun).
      apply find_env_inv in Hg as (_ & ?); subst s1.
      apply sec_bind_inv in Hrun as (t1 & s2 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (t2 & s3 & Ht2 & Hj).
      apply (sec_le_trans _ s2 _).
      + exact (assign_lexps_sec_le_of G env base_ty rst_ty ets H t1 s s2 Ht1).
      + apply (sec_le_trans _ s3 _).
        * exact (assign_lexps_sec_le_of G env base_ty rst_ty efs H0 t2 s2 s3 Ht2).
        * rewrite (ljoin_list_pure _ t2 ts s3 s' Hj). apply sec_le_refl.
    - (** Eite *)
      rewrite assign_lexp_Eite in Hrun.
      apply sec_bind_inv in Hrun as (t0 & s1 & Ht0 & Hrun).
      apply sec_bind_inv in Hrun as (th & s2 & Hth & Hrun).
      apply single_inv in Hth as (_ & ?); subst s2.
      apply sec_bind_inv in Hrun as (t1 & s3 & Ht1 & Hrun).
      apply sec_bind_inv in Hrun as (t2 & s4 & Ht2 & Hj).
      apply (sec_le_trans _ s1 _); [exact (IHe t0 s s1 Ht0)|].
      apply (sec_le_trans _ s3 _).
      + exact (assign_lexps_sec_le_of G env base_ty rst_ty ets H t1 s1 s3 Ht1).
      + apply (sec_le_trans _ s4 _).
        * exact (assign_lexps_sec_le_of G env base_ty rst_ty efs H0 t2 s3 s4 Ht2).
        * rewrite (ljoin_list_pure _ t2 ts s4 s' Hj). apply sec_le_refl.
    - (** Eapp: the only case that mints *)
      apply assign_lexp_Eapp_inv in Hrun
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & Hargs & _ & Hrst & _ & Houts & Hcs & _).
      apply (sec_le_trans _ sta _).
      + exact (assign_lexps_sec_le_of G env base_ty rst_ty es H0 argts s sta
                 Hargs).
      + apply (sec_le_trans _ stb _).
        * destruct ro as [e1|].
          -- destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg & _ & _).
             apply single_inv in Hsg as (_ & ?); subst stb.
             exact (H t1 sta stm Ht1).
          -- destruct Hrst as (_ & ?); subst stb. apply sec_le_refl.
        * apply (sec_le_trans _ stc _).
          -- exact (fresh_idents_sec_le (List.length a) outs stb stc Houts).
          -- exact (state_pure_sec_le _ cs stc s'
                      (state_pure_generate_constraints sg
                         (List.map fst argts) ckty (fst rstty) outs) Hcs).
  Qed.

  (** The list form, with no side condition: every element is monotone, so
      the [Forall] premise of [assign_lexps_sec_le_of] is always met. *)
  Corollary assign_lexps_sec_le :
    forall G env base_ty rst_ty es ts s s',
      assign_lexps G env base_ty rst_ty es s = OK (ts, s') -> sec_le s s'.
  Proof.
    intros G env base_ty rst_ty es ts s s' Hrun.
    eapply assign_lexps_sec_le_of; [|exact Hrun].
    apply Forall_forall. intros e _ t s1 s2 Ht.
    exact (assign_lexp_type_sec_le G env base_ty rst_ty e t s1 s2 Ht).
  Qed.

  (** Discharging a checkmark bound is always the same shape: walk the runs
      that the inversion of the enclosing run already put in the context,
      then land on the bound the caller supplied.  Collect the steps so the
      use sites can say [eauto with sec]. *)
  (** Discharging a checkmark bound always has the same shape: walk back
      along the runs the inversion of the enclosing run already put in the
      context, then land on the bound the caller supplied.  Each step is
      stated so that it *consumes* a run hypothesis and leaves a bound on an
      earlier state, which makes the search directed -- [sec_le_trans] as a
      hint would instead open a goal with an unknown middle state and search
      the whole context for it. *)

  Lemma sec_le_of_lexp :
    forall G env base_ty rst_ty e ts s s' stF,
      assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
      sec_le s' stF -> sec_le s stF.
  Proof.
    intros G env base_ty rst_ty e ts s s' stF Hrun Hb.
    exact (sec_le_trans _ _ _
             (assign_lexp_type_sec_le G env base_ty rst_ty e ts s s' Hrun) Hb).
  Qed.

  Lemma sec_le_of_lexps :
    forall G env base_ty rst_ty es ts s s' stF,
      assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
      sec_le s' stF -> sec_le s stF.
  Proof.
    intros G env base_ty rst_ty es ts s s' stF Hrun Hb.
    exact (sec_le_trans _ _ _
             (assign_lexps_sec_le G env base_ty rst_ty es ts s s' Hrun) Hb).
  Qed.

  Lemma sec_le_of_ljoin_list :
    forall ts us rs s s' stF,
      ljoin_list ts us s = OK (rs, s') -> sec_le s' stF -> sec_le s stF.
  Proof.
    intros ts us rs s s' stF Hrun Hb.
    rewrite (ljoin_list_pure ts us rs s s' Hrun) in Hb. exact Hb.
  Qed.

  Lemma sec_le_of_single :
    forall (ts : list LST) t s s' stF,
      single ts s = OK (t, s') -> sec_le s' stF -> sec_le s stF.
  Proof.
    intros ts t s s' stF Hrun Hb.
    apply single_inv in Hrun as (_ & ?); subst s'. exact Hb.
  Qed.

  Hint Resolve sec_le_refl : sec.
  Hint Resolve sec_le_of_lexp : sec.
  Hint Resolve sec_le_of_lexps : sec.
  Hint Resolve sec_le_of_ljoin_list : sec.
  Hint Resolve sec_le_of_single : sec.

  (** [Eapp] is the only constructor whose run has stages, so it is the only
      one where a bound on the whole run has to be pushed down by hand.  The
      stages come straight out of [assign_lexp_Eapp_inv]; this packages their
      order once so the call case does not have to repeat it. *)
  Lemma assign_lexp_Eapp_stages_le :
    forall G env base_ty rst_ty es er (anns : list LSyn.ann) st st'
           sg argts rstty ckty outs cs sta stb stc,
      assign_lexps G env base_ty rst_ty es st = OK (argts, sta) ->
      (match er with
       | None => rstty = lvar rst_ty /\ stb = sta
       | Some e1 =>
           exists t1 a1 rck stm,
             assign_lexp_type G env base_ty rst_ty e1 sta = OK (t1, stm)
             /\ single t1 stm = OK (a1, stb)
             /\ assign_clk_type env base_ty (hd Cbase (LSyn.clockof e1))
                = Some rck
             /\ rstty = ljoin (lvar rst_ty) (ljoin a1 (rck, []))
       end) ->
      fresh_idents (List.length anns) stb = OK (outs, stc) ->
      generate_constraints sg (List.map fst argts) ckty (fst rstty) outs stc
        = OK (cs, st') ->
      sec_le sta stb /\ sec_le stb stc /\ sec_le stc st'.
  Proof.
    intros G env base_ty rst_ty es er anns st st'
           sg argts rstty ckty outs cs sta stb stc Hargs Hrst Houts Hcs.
    repeat split.
    - destruct er as [e1|].
      + destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg & _ & _).
        apply single_inv in Hsg as (_ & ?); subst stb.
        exact (assign_lexp_type_sec_le G env base_ty rst_ty e1 t1 sta stm Ht1).
      + destruct Hrst as (_ & ?); subst stb. apply sec_le_refl.
    - exact (fresh_idents_sec_le (List.length anns) outs stb stc Houts).
    - exact (state_pure_sec_le _ cs stc st'
               (state_pure_generate_constraints sg (List.map fst argts)
                  ckty (fst rstty) outs) Hcs).
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


  (** * The dependency property, expression level

      What the call case of preservation needs about a *callee's* signature is
      this: a constraint whose source mentions an input also mentions the
      inputs of that input's declared clock.  On the Lustre side that is a
      property of [assign_lexp_type] -- the type of an expression, taken
      together with the type of the clock it runs on, already contains the
      clock type of every declared variable it mentions.  It is the mirror of
      [assign_cexp_type_clock_closed] above.

      Two things are new here.  The type is a list, one entry per stream, so
      the statement is a [Forall2] against [clocksof]; and the call case mints
      names that belong to no program variable, so a name has to be known
      *not* to have been minted by the run.  That is what the [minted] window
      algebra is for, and at the use site it is free: [generate_lnode_sig]
      runs [simplify] over [minted st0 st1], so no minted name survives into
      a signature.

      The statement is factored through a single-name form, because every
      case of the induction needs the same two moves -- widen the target, or
      account for a sampling variable -- and nothing else. *)

  Definition name_clock_closed
      (env : Env.t ident) (base_ty : ident) (vars : list (ident * clock))
      (ckty target : ST) (b : ident) : Prop :=
    forall v ckv ckvty,
      Env.find v env = Some b ->
      In (v, ckv) vars ->
      assign_clk_type env base_ty ckv = Some ckvty ->
      incl ckvty (merge ckty target).

  Definition lst_clock_closed
      (env : Env.t ident) (base_ty : ident) (vars : list (ident * clock))
      (nomint : list ident) (t : LST) (ck : clock) : Prop :=
    forall ckty b,
      assign_clk_type env base_ty ck = Some ckty ->
      ~ In b nomint ->
      In b (fst t) ->
      name_clock_closed env base_ty vars ckty (fst t) b.

  (** Widening the pair [(clock type, target)] is the only thing the single-name
      form ever needs. *)
  Lemma name_clock_closed_weaken :
    forall env base_ty vars ckty tgt ckty' tgt' b,
      incl (merge ckty tgt) (merge ckty' tgt') ->
      name_clock_closed env base_ty vars ckty tgt b ->
      name_clock_closed env base_ty vars ckty' tgt' b.
  Proof.
    intros env base_ty vars ckty tgt ckty' tgt' b Hincl H v ckv ckvty Hfv Hinv Hckv.
    intros z Hz. apply Hincl. exact (H v ckv ckvty Hfv Hinv Hckv z Hz).
  Qed.

  (** A sampling variable pays for itself: its own clock type is the one the
      deeper clock was built from, and the name is in the target. *)
  Lemma name_clock_closed_sampler :
    forall env base_ty vars ckty tgt x g ck ckty0,
      env_injective env ->
      NoDupMembers vars ->
      Env.find x env = Some g ->
      In (x, ck) vars ->
      assign_clk_type env base_ty ck = Some ckty0 ->
      incl ckty0 (merge ckty tgt) ->
      name_clock_closed env base_ty vars ckty tgt g.
  Proof.
    intros env base_ty vars ckty tgt x g ck ckty0 Hinj Hnd Hg Hin Hck0 Hincl
      v ckv ckvty Hfv Hinv Hckv.
    assert (v = x) as ?
        by (exact (Hinj v x g g Hfv Hg (@Coq.Init.Logic.eq_refl ident g)));
      subst v.
    assert (ckv = ck) as ? by (exact (NoDupMembers_det x ckv ck vars Hnd Hinv Hin));
      subst ckv.
    rewrite Hckv in Hck0. apply option_Some_inj in Hck0. subst ckty0.
    exact Hincl.
  Qed.

  Lemma lst_clock_closed_nomint :
    forall env base_ty vars ns ns' t ck,
      incl ns ns' ->
      lst_clock_closed env base_ty vars ns t ck ->
      lst_clock_closed env base_ty vars ns' t ck.
  Proof.
    intros env base_ty vars ns ns' t ck Hincl H ckty b Hck Hnm Hb.
    exact (H ckty b Hck (fun Hc => Hnm (Hincl b Hc)) Hb).
  Qed.

  Corollary lst_clock_closed_nomint_list :
    forall env base_ty vars ns ns' ts cks,
      incl ns ns' ->
      Forall2 (lst_clock_closed env base_ty vars ns) ts cks ->
      Forall2 (lst_clock_closed env base_ty vars ns') ts cks.
  Proof.
    intros env base_ty vars ns ns' ts cks Hincl H.
    induction H as [|t ck ts cks Ht Hr IH]; constructor;
      [exact (lst_clock_closed_nomint env base_ty vars ns ns' t ck Hincl Ht)
      |exact IH].
  Qed.

  (** Three [merge] inclusions, written once. *)
  Lemma incl_merge_r_l :
    forall a b c, incl (merge a b) (merge a (merge b c)).
  Proof.
    intros a b c z Hz. apply in_merge_inv in Hz as [Hz|Hz];
      [now apply in_merge_left|apply in_merge_right; now apply in_merge_left].
  Qed.

  Lemma incl_merge_r_r :
    forall a b c, incl (merge a c) (merge a (merge b c)).
  Proof.
    intros a b c z Hz. apply in_merge_inv in Hz as [Hz|Hz];
      [now apply in_merge_left|apply in_merge_right; now apply in_merge_right].
  Qed.

  Lemma incl_merge_mono :
    forall a a' b b', incl a a' -> incl b b' -> incl (merge a b) (merge a' b').
  Proof.
    intros a a' b b' Ha Hb z Hz. apply in_merge_inv in Hz as [Hz|Hz];
      [apply in_merge_left; exact (Ha z Hz)
      |apply in_merge_right; exact (Hb z Hz)].
  Qed.

  (** Joining two types at the same clock. *)
  Lemma lst_clock_closed_ljoin :
    forall env base_ty vars ns t u ck,
      lst_clock_closed env base_ty vars ns t ck ->
      lst_clock_closed env base_ty vars ns u ck ->
      lst_clock_closed env base_ty vars ns (ljoin t u) ck.
  Proof.
    intros env base_ty vars ns t u ck Ht Hu ckty b Hck Hnm Hb.
    rewrite fst_ljoin in Hb |- *.
    apply in_merge_inv in Hb as [Hb|Hb].
    - eapply name_clock_closed_weaken;
        [|exact (Ht ckty b Hck Hnm Hb)].
      apply incl_merge_mono;
        [apply incl_refl|intros z Hz; now apply in_merge_left].
    - eapply name_clock_closed_weaken;
        [|exact (Hu ckty b Hck Hnm Hb)].
      apply incl_merge_mono;
        [apply incl_refl|intros z Hz; now apply in_merge_right].
  Qed.

  Lemma ljoin_list_closed :
    forall env base_ty vars ns ts us rs cks s s',
      ljoin_list ts us s = OK (rs, s') ->
      Forall2 (lst_clock_closed env base_ty vars ns) ts cks ->
      Forall2 (lst_clock_closed env base_ty vars ns) us cks ->
      Forall2 (lst_clock_closed env base_ty vars ns) rs cks.
  Proof.
    intros env base_ty vars ns ts. revert ts.
    induction ts as [|t ts IH]; intros us rs cks s s' Hj Hts Hus.
    - destruct us as [|u us]; [|simpl in Hj; discriminate].
      simpl in Hj. unfold SC.ret in Hj. inversion Hj; subst rs.
      inversion Hts; subst. constructor.
    - destruct us as [|u us]; [simpl in Hj; discriminate|].
      simpl in Hj.
      apply sec_bind_inv in Hj as (r & s1 & Hr & Hret).
      unfold SC.ret in Hret. inversion Hret; subst rs.
      inversion Hts as [|t0 ck ts0 cks0 Ht Htr]; subst.
      inversion Hus as [|u0 ck0 us0 cks1 Hu Hur]; subst.
      constructor;
        [exact (lst_clock_closed_ljoin env base_ty vars ns t u ck Ht Hu)
        |eapply IH; [exact Hr|exact Htr|exact Hur]].
  Qed.

  Lemma Forall2_eq_l :
    forall {A} (l l' : list A),
      Forall2 (@Coq.Init.Logic.eq A) l l' -> l = l'.
  Proof. intros A l l' H. induction H as [|a b l0 l1 Hab Hr IH]; congruence. Qed.

  Lemma Forall2_all_In :
    forall {A B} (Q : A -> B -> Prop) l1 l2,
      List.length l1 = List.length l2 ->
      (forall a, In a l1 -> forall b, Q a b) ->
      Forall2 Q l1 l2.
  Proof.
    intros A B Q l1. induction l1 as [|a l1 IH]; intros l2 Hl HQ.
    - destruct l2; [constructor|discriminate].
    - destruct l2 as [|b l2]; [discriminate|].
      constructor.
      + apply HQ. now left.
      + apply IH; [simpl in Hl; congruence|].
        intros a0 Ha0. apply HQ. now right.
  Qed.

  Lemma Forall2_eq_clock :
    forall {A} (Q : A -> clock -> Prop) ts cks ck,
      Forall2 Q ts cks ->
      Forall (@Coq.Init.Logic.eq clock ck) cks ->
      Forall (fun t => Q t ck) ts.
  Proof.
    intros A Q ts cks ck H. induction H as [|t ck0 ts0 cks0 Ht Hr IH];
      intro Hall; [constructor|].
    inversion Hall as [|c0 cs0 Hc Hcs]; subst.
    constructor; [exact Ht|exact (IH Hcs)].
  Qed.

  Lemma assign_clk_type_Con :
    forall env base_ty ck x b ckty g,
      assign_clk_type env base_ty ck = Some ckty ->
      Env.find x env = Some g ->
      assign_clk_type env base_ty (Con ck x b) = Some (merge ckty [g]).
  Proof.
    intros env base_ty ck x b ckty g Hck Hg. simpl.
    now rewrite Hck, Hg.
  Qed.

  Lemma assign_clk_type_Con_inv :
    forall env base_ty ck x b ckty',
      assign_clk_type env base_ty (Con ck x b) = Some ckty' ->
      exists ckty g,
        assign_clk_type env base_ty ck = Some ckty
        /\ Env.find x env = Some g
        /\ ckty' = merge ckty [g].
  Proof.
    intros env base_ty ck x b ckty' H. simpl in H.
    destruct (assign_clk_type env base_ty ck) as [ckty|] eqn:Eck;
      [|discriminate].
    destruct (Env.find x env) as [g|] eqn:Eg; [|discriminate].
    simpl in H. apply option_Some_inj in H.
    exists ckty, g. auto.
  Qed.

  Section LexpClockClosed.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable P       : global.
    Variable vars    : list (ident * clock).

    Hypothesis Hinj : env_injective env.
    Hypothesis Hndv : NoDupMembers vars.

    Local Notation closed ns t ck :=
      (lst_clock_closed env base_ty vars ns t ck).

    (** Sampling on [x] deepens the clock by one [Con] and adds [x]'s own
        security name to the type, which is exactly what pays for it. *)
    Lemma lst_clock_closed_when :
      forall ns t x g ck b,
        Env.find x env = Some g ->
        In (x, ck) vars ->
        closed ns t ck ->
        closed ns (ljoin t (lvar g)) (Con ck x b).
    Proof.
      intros ns t x g ck b Hg Hin Ht ckty' b0 Hck' Hnm Hb0.
      apply assign_clk_type_Con_inv in Hck'
        as (ckty & g' & Hck & Hg' & ?); subst ckty'.
      rewrite Hg in Hg'. apply option_Some_inj in Hg'; subst g'.
      rewrite fst_ljoin, fst_lvar in Hb0 |- *.
      apply in_merge_inv in Hb0 as [Hb0|Hb0].
      - eapply name_clock_closed_weaken; [|exact (Ht ckty b0 Hck Hnm Hb0)].
        apply incl_merge_mono;
          [intros z Hz; now apply in_merge_left
          |intros z Hz; now apply in_merge_left].
      - destruct Hb0 as [Hb0|[]]; subst b0.
        eapply name_clock_closed_sampler;
          [exact Hinj|exact Hndv|exact Hg|exact Hin|exact Hck|].
        intros z Hz. apply in_merge_left. now apply in_merge_left.
    Qed.

    Lemma lst_clock_closed_when_list :
      forall {A} ns ts x g ck b (tys : list A),
        Env.find x env = Some g ->
        In (x, ck) vars ->
        Forall (fun t => closed ns t ck) ts ->
        List.length ts = List.length tys ->
        Forall2 (lst_clock_closed env base_ty vars ns)
          (List.map (fun t => ljoin t (lvar g)) ts)
          (List.map (fun _ : A => Con ck x b) tys).
    Proof.
      intros A ns ts x g ck b tys Hg Hin Hall. revert tys.
      induction Hall as [|t ts Ht Hr IH]; intros tys Hl.
      - destruct tys; [constructor|discriminate].
      - destruct tys as [|ty tys]; [discriminate|].
        simpl. constructor;
          [exact (lst_clock_closed_when ns t x g ck b Hg Hin Ht)
          |apply IH; simpl in Hl; congruence].
    Qed.

    (** [Emerge] is the other direction: the two branches run on the deeper
        clocks, the result on the shallower one, and the sampling name is in
        the merged type, so the branches' extra [Con] is paid for. *)
    Lemma lst_clock_closed_merge_el :
      forall ns t u x g ck,
        Env.find x env = Some g ->
        In (x, ck) vars ->
        closed ns t (Con ck x true) ->
        closed ns u (Con ck x false) ->
        closed ns (ljoin (ljoin (lvar g) t) u) ck.
    Proof.
      intros ns t u x g ck Hg Hin Ht Hu ckty b0 Hck Hnm Hb0.
      assert (assign_clk_type env base_ty (Con ck x true)
              = Some (merge ckty [g])) as Hct
          by exact (assign_clk_type_Con env base_ty ck x true ckty g Hck Hg).
      assert (assign_clk_type env base_ty (Con ck x false)
              = Some (merge ckty [g])) as Hcf
          by exact (assign_clk_type_Con env base_ty ck x false ckty g Hck Hg).
      rewrite !fst_ljoin, fst_lvar in Hb0 |- *.
      apply in_merge_inv in Hb0 as [Hb0|Hb0].
      - apply in_merge_inv in Hb0 as [Hb0|Hb0].
        + destruct Hb0 as [Hb0|[]]; subst b0.
          eapply name_clock_closed_sampler;
            [exact Hinj|exact Hndv|exact Hg|exact Hin|exact Hck|].
          intros z Hz. now apply in_merge_left.
        + eapply name_clock_closed_weaken;
            [|exact (Ht (merge ckty [g]) b0 Hct Hnm Hb0)].
          intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
          * apply in_merge_inv in Hz as [Hz|Hz];
              [now apply in_merge_left|].
            apply in_merge_right, in_merge_left. now apply in_merge_left.
          * apply in_merge_right, in_merge_left. now apply in_merge_right.
      - eapply name_clock_closed_weaken;
          [|exact (Hu (merge ckty [g]) b0 Hcf Hnm Hb0)].
        intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
        + apply in_merge_inv in Hz as [Hz|Hz]; [now apply in_merge_left|].
          apply in_merge_right, in_merge_left. now apply in_merge_left.
        + now apply in_merge_right, in_merge_right.
    Qed.

    Lemma lst_clock_closed_merge_list :
      forall {A} ns ts us rs x g ck s s' (tys : list A),
        Env.find x env = Some g ->
        In (x, ck) vars ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s = OK (rs, s') ->
        Forall (fun t => closed ns t (Con ck x true)) ts ->
        Forall (fun u => closed ns u (Con ck x false)) us ->
        List.length ts = List.length tys ->
        Forall2 (lst_clock_closed env base_ty vars ns) rs
          (List.map (fun _ : A => ck) tys).
    Proof.
      intros A ns ts. revert ts.
      induction ts as [|t ts IH];
        intros us rs x g ck s s' tys Hg Hin Hj Hts Hus Hl.
      - destruct us as [|u us]; [|simpl in Hj; discriminate].
        simpl in Hj. unfold SC.ret in Hj. inversion Hj; subst rs.
        destruct tys; [constructor|discriminate].
      - destruct us as [|u us]; [simpl in Hj; discriminate|].
        destruct tys as [|ty tys]; [discriminate|].
        simpl in Hj.
        apply sec_bind_inv in Hj as (r & s1 & Hr & Hret).
        unfold SC.ret in Hret. inversion Hret; subst rs.
        inversion Hts as [|t0 ts0 Ht Htr]; subst.
        inversion Hus as [|u0 us0 Hu Hur]; subst.
        simpl. constructor.
        + exact (lst_clock_closed_merge_el ns t u x g ck Hg Hin Ht Hu).
        + eapply IH; [exact Hg|exact Hin|exact Hr|exact Htr|exact Hur|].
          simpl in Hl; congruence.
    Qed.

    Lemma lst_clock_closed_ite_list :
      forall {A} ns th ts us rs ck s s' (tys : list A),
        closed ns th ck ->
        ljoin_list (List.map (fun t => ljoin th t) ts) us s = OK (rs, s') ->
        Forall (fun t => closed ns t ck) ts ->
        Forall (fun u => closed ns u ck) us ->
        List.length ts = List.length tys ->
        Forall2 (lst_clock_closed env base_ty vars ns) rs
          (List.map (fun _ : A => ck) tys).
    Proof.
      intros A ns th ts. revert ts.
      induction ts as [|t ts IH]; intros us rs ck s s' tys Hth Hj Hts Hus Hl.
      - destruct us as [|u us]; [|simpl in Hj; discriminate].
        simpl in Hj. unfold SC.ret in Hj. inversion Hj; subst rs.
        destruct tys; [constructor|discriminate].
      - destruct us as [|u us]; [simpl in Hj; discriminate|].
        destruct tys as [|ty tys]; [discriminate|].
        simpl in Hj.
        apply sec_bind_inv in Hj as (r & s1 & Hr & Hret).
        unfold SC.ret in Hret. inversion Hret; subst rs.
        inversion Hts as [|t0 ts0 Ht Htr]; subst.
        inversion Hus as [|u0 us0 Hu Hur]; subst.
        simpl. constructor.
        + apply lst_clock_closed_ljoin; [|exact Hu].
          apply lst_clock_closed_ljoin; [exact Hth|exact Ht].
        + eapply IH; [exact Hth|exact Hr|exact Htr|exact Hur|].
          simpl in Hl; congruence.
    Qed.

    (** * The induction

        [wc_exp] is inverted through these, so the main proof does not depend
        on generated hypothesis names. *)

    Lemma wc_Evar_inv' :
      forall x a, wc_exp P vars (Evar x a) -> In (x, clock_of_nclock a) vars.
    Proof. intros x a H. inv H; simpl; assumption. Qed.

    Lemma wc_Eunop_inv' :
      forall op e a,
        wc_exp P vars (Eunop op e a) ->
        wc_exp P vars e /\ clockof e = [clock_of_nclock a].
    Proof. intros op e a H. inv H. simpl. auto. Qed.

    Lemma wc_Ebinop_inv' :
      forall op e1 e2 a,
        wc_exp P vars (Ebinop op e1 e2 a) ->
        wc_exp P vars e1 /\ wc_exp P vars e2
        /\ clockof e1 = [clock_of_nclock a]
        /\ clockof e2 = [clock_of_nclock a].
    Proof. intros op e1 e2 a H. inv H. simpl. auto. Qed.

    Lemma wc_Efby_inv' :
      forall e0s es anns,
        wc_exp P vars (Efby e0s es anns) ->
        Forall (wc_exp P vars) e0s /\ Forall (wc_exp P vars) es
        /\ List.map clock_of_nclock anns = clocksof e0s
        /\ List.map clock_of_nclock anns = clocksof es.
    Proof.
      intros e0s es anns H. inv H.
      repeat split; try assumption; apply Forall2_eq_l; assumption.
    Qed.

    Lemma wc_Earrow_inv' :
      forall e0s es anns,
        wc_exp P vars (Earrow e0s es anns) ->
        Forall (wc_exp P vars) e0s /\ Forall (wc_exp P vars) es
        /\ List.map clock_of_nclock anns = clocksof e0s
        /\ List.map clock_of_nclock anns = clocksof es.
    Proof.
      intros e0s es anns H. inv H.
      repeat split; try assumption; apply Forall2_eq_l; assumption.
    Qed.

    Lemma wc_Ewhen_inv' :
      forall es x b tys cl,
        wc_exp P vars (Ewhen es x b (tys, cl)) ->
        exists ck,
          stripname cl = Con ck x b
          /\ Forall (wc_exp P vars) es
          /\ In (x, ck) vars
          /\ Forall (@Coq.Init.Logic.eq clock ck) (clocksof es)
          /\ List.length tys = List.length (clocksof es).
    Proof.
      intros es x b tys cl H. inv H. eexists.
      split; [reflexivity|]. repeat split; assumption.
    Qed.

    Lemma wc_Emerge_inv' :
      forall x ets efs tys cl,
        wc_exp P vars (Emerge x ets efs (tys, cl)) ->
        exists ck,
          stripname cl = ck
          /\ Forall (wc_exp P vars) ets
          /\ Forall (wc_exp P vars) efs
          /\ In (x, ck) vars
          /\ Forall (@Coq.Init.Logic.eq clock (Con ck x true)) (clocksof ets)
          /\ Forall (@Coq.Init.Logic.eq clock (Con ck x false)) (clocksof efs)
          /\ List.length tys = List.length (clocksof ets)
          /\ List.length tys = List.length (clocksof efs).
    Proof.
      intros x ets efs tys cl H. inv H. eexists.
      split; [reflexivity|]. repeat split; assumption.
    Qed.

    Lemma wc_Eite_inv' :
      forall e0 ets efs tys cl,
        wc_exp P vars (Eite e0 ets efs (tys, cl)) ->
        exists ck,
          stripname cl = ck
          /\ wc_exp P vars e0
          /\ Forall (wc_exp P vars) ets
          /\ Forall (wc_exp P vars) efs
          /\ clockof e0 = [ck]
          /\ Forall (@Coq.Init.Logic.eq clock ck) (clocksof ets)
          /\ Forall (@Coq.Init.Logic.eq clock ck) (clocksof efs)
          /\ List.length tys = List.length (clocksof ets)
          /\ List.length tys = List.length (clocksof efs).
    Proof.
      intros e0 ets efs tys cl H. inv H. eexists.
      split; [reflexivity|]. repeat split; assumption.
    Qed.

    Lemma wc_Eapp_inv' :
      forall f es ro anns,
        wc_exp P vars (Eapp f es ro anns) -> Forall (wc_exp P vars) es.
    Proof. intros f es ro anns H. inv H; assumption. Qed.

    (** A sub-run's window sits inside whatever the caller's does. *)
    Lemma minted_incl_sub :
      forall s s1 s2 s' ns,
        sec_le s s1 -> sec_le s2 s' ->
        incl (minted s s') ns -> incl (minted s1 s2) ns.
    Proof.
      intros s s1 s2 s' ns H1 H2 Hns y Hy.
      apply Hns. exact (minted_window s s1 s2 s' H1 H2 y Hy).
    Qed.

    (** The set of names to exclude is a parameter rather than the run's own
        window.  That is what keeps the induction's conclusion stable: a
        sub-run inherits the same set, so no case has to re-state which
        window it is talking about. *)
    Definition lexp_clock_closed (e : exp) : Prop :=
      wc_exp P vars e ->
      forall ts s s' ns,
        incl (minted s s') ns ->
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        Forall2 (lst_clock_closed env base_ty vars ns) ts (clockof e).

    Lemma assign_lexps_closed_of :
      forall es,
        Forall lexp_clock_closed es ->
        Forall (wc_exp P vars) es ->
        forall ts s s' ns,
          incl (minted s s') ns ->
          assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
          Forall2 (lst_clock_closed env base_ty vars ns) ts (clocksof es).
    Proof.
      induction es as [|e es IH]; intros Hall Hwc ts s s' ns Hns H.
      - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
          as (? & _ & ?); subst ts. constructor.
      - apply assign_lexps_carried_cons in H
          as (t & r & sa & Ht & Hr & ? & _); subst ts.
        inversion Hall as [|e0 es0 He Her]; subst.
        inversion Hwc as [|e1 es1 Hwce Hwcr]; subst.
        unfold clocksof. simpl flat_map. apply Forall2_app.
        + apply (He Hwce t s sa ns); [|exact Ht].
          apply (minted_incl_sub s s sa s' ns); [apply sec_le_refl| |exact Hns].
          eapply assign_lexps_sec_le; exact Hr.
        + apply (IH Her Hwcr r sa s' ns); [|exact Hr].
          apply (minted_incl_sub s sa s' s' ns);
            [|apply sec_le_refl|exact Hns].
          eapply assign_lexp_type_sec_le; exact Ht.
    Qed.

    (** The expression-level dependency property: the type of an expression,
        together with the type of the clock it runs on, already contains the
        clock type of every declared variable it mentions -- provided the name
        was not minted by the run, which a call's results always are. *)
    Theorem assign_lexp_type_clock_closed : forall e, lexp_clock_closed e.
    Proof.
      intro e. induction e using exp_ind2.

      - (** Econst: the bottom type mentions nothing *)
        intros Hwc ts s s' ns Hns Hrun.
        rewrite assign_lexp_Econst in Hrun. unfold SC.ret in Hrun.
        assert (ts = [lbot]) as ? by (inversion Hrun; reflexivity); subst ts.
        simpl clockof. constructor; [|constructor].
        intros ckty b Hck Hnm Hb. simpl in Hb. contradiction.

      - (** Evar: its own name, and it is declared on the clock asked about *)
        intros Hwc ts s s' ns Hns Hrun.
        pose proof (wc_Evar_inv' x a Hwc) as Hin.
        rewrite assign_lexp_Evar in Hrun.
        apply sec_bind_inv in Hrun as (g & s1 & Hg & Hret).
        apply find_env_inv in Hg as (Hg & ?); subst s1.
        unfold SC.ret in Hret.
        assert (ts = [lvar g]) as ? by (inversion Hret; reflexivity); subst ts.
        simpl clockof. constructor; [|constructor].
        intros ckty b Hck Hnm Hb. rewrite fst_lvar in Hb |- *.
        destruct Hb as [Hb|[]]; subst b.
        eapply name_clock_closed_sampler;
          [exact Hinj|exact Hndv|exact Hg|exact Hin|exact Hck|].
        intros z Hz. now apply in_merge_left.

      - (** Eunop: same type, same clock *)
        intros Hwc ts s s' ns Hns Hrun.
        apply wc_Eunop_inv' in Hwc as (Hwce & Hcke).
        rewrite assign_lexp_Eunop in Hrun.
        simpl clockof. rewrite <- Hcke.
        exact (IHe Hwce ts s s' ns Hns Hrun).

      - (** Ebinop: two single flows on one clock *)
        intros Hwc ts s s' ns Hns Hrun.
        apply wc_Ebinop_inv' in Hwc as (Hwc1 & Hwc2 & Hck1 & Hck2).
        rewrite assign_lexp_Ebinop in Hrun.
        apply sec_bind_inv in Hrun as (t1 & sa & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sb & Ht2 & Hrun).
        apply sec_bind_inv in Hrun as (a1 & sc & Ha1 & Hrun).
        apply sec_bind_inv in Hrun as (a2 & sd & Ha2 & Hret).
        apply single_inv in Ha1 as (? & ?); subst t1 sc.
        apply single_inv in Ha2 as (? & ?); subst t2 sd.
        unfold SC.ret in Hret.
        assert (ts = [ljoin a1 a2] /\ sb = s') as (? & ?)
            by (inversion Hret; auto); subst ts; subst sb.
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  [a1] (clockof e1)) as Hcl1.
        { apply (IHe1 Hwc1 [a1] s sa ns); [|exact Ht1].
          apply (minted_incl_sub s s sa s' ns); [apply sec_le_refl| |exact Hns].
          eapply assign_lexp_type_sec_le; exact Ht2. }
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  [a2] (clockof e2)) as Hcl2.
        { apply (IHe2 Hwc2 [a2] sa s' ns); [|exact Ht2].
          apply (minted_incl_sub s sa s' s' ns);
            [|apply sec_le_refl|exact Hns].
          eapply assign_lexp_type_sec_le; exact Ht1. }
        rewrite Hck1 in Hcl1. rewrite Hck2 in Hcl2.
        inversion Hcl1 as [|p1 c1 ps1 cs1 Hp1 _]; subst.
        inversion Hcl2 as [|p2 c2 ps2 cs2 Hp2 _]; subst.
        simpl clockof. constructor; [|constructor].
        exact (lst_clock_closed_ljoin env base_ty vars ns
                 a1 a2 (clock_of_nclock a) Hp1 Hp2).

      - (** Efby: one join per stream, all on the annotation's clock *)
        intros Hwc ts s s' ns Hns Hrun.
        apply wc_Efby_inv' in Hwc as (Hwc0 & Hwc1 & Hc0 & Hc1).
        rewrite assign_lexp_Efby in Hrun.
        apply sec_bind_inv in Hrun as (ts0 & sa & Hts0 & Hrun).
        apply sec_bind_inv in Hrun as (us & sb & Hus & Hj).
        assert (sec_le sb s') as Hbs'
            by (rewrite (ljoin_list_pure ts0 us ts sb s' Hj); apply sec_le_refl).
        simpl clockof.
        eapply ljoin_list_closed; [exact Hj| |].
        + rewrite Hc0. apply (assign_lexps_closed_of e0s H Hwc0 ts0 s sa ns);
            [|exact Hts0].
          apply (minted_incl_sub s s sa s' ns); [apply sec_le_refl| |exact Hns].
          apply (sec_le_trans _ sb _); [|exact Hbs'].
          eapply assign_lexps_sec_le; exact Hus.
        + rewrite Hc1. apply (assign_lexps_closed_of es H0 Hwc1 us sa sb ns);
            [|exact Hus].
          apply (minted_incl_sub s sa sb s' ns); [|exact Hbs'|exact Hns].
          eapply assign_lexps_sec_le; exact Hts0.

      - (** Earrow: the same body *)
        intros Hwc ts s s' ns Hns Hrun.
        apply wc_Earrow_inv' in Hwc as (Hwc0 & Hwc1 & Hc0 & Hc1).
        rewrite assign_lexp_Earrow in Hrun.
        apply sec_bind_inv in Hrun as (ts0 & sa & Hts0 & Hrun).
        apply sec_bind_inv in Hrun as (us & sb & Hus & Hj).
        assert (sec_le sb s') as Hbs'
            by (rewrite (ljoin_list_pure ts0 us ts sb s' Hj); apply sec_le_refl).
        simpl clockof.
        eapply ljoin_list_closed; [exact Hj| |].
        + rewrite Hc0. apply (assign_lexps_closed_of e0s H Hwc0 ts0 s sa ns);
            [|exact Hts0].
          apply (minted_incl_sub s s sa s' ns); [apply sec_le_refl| |exact Hns].
          apply (sec_le_trans _ sb _); [|exact Hbs'].
          eapply assign_lexps_sec_le; exact Hus.
        + rewrite Hc1. apply (assign_lexps_closed_of es H0 Hwc1 us sa sb ns);
            [|exact Hus].
          apply (minted_incl_sub s sa sb s' ns); [|exact Hbs'|exact Hns].
          eapply assign_lexps_sec_le; exact Hts0.

      - (** Ewhen: the sampling name is added, and the clock deepens by it *)
        intros Hwc ts s s' ns Hns Hrun. destruct a as (tys & cl).
        apply wc_Ewhen_inv' in Hwc as (ck & Hcl & Hwces & Hin & Heq & Hlen).
        rewrite assign_lexp_Ewhen in Hrun.
        apply sec_bind_inv in Hrun as (ts0 & sa & Hts0 & Hrun).
        apply sec_bind_inv in Hrun as (g & s1 & Hg & Hret).
        apply find_env_inv in Hg as (Hg & ?); subst s1.
        unfold SC.ret in Hret.
        assert (ts = List.map (fun t => ljoin t (lvar g)) ts0 /\ sa = s')
          as (? & ?) by (inversion Hret; auto); subst ts; subst sa.
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  ts0 (clocksof es)) as Hts
            by exact (assign_lexps_closed_of es H Hwces ts0 s s' ns Hns Hts0).
        assert (List.length ts0 = List.length tys) as Hl
            by (apply Forall2_length in Hts; congruence).
        assert (clock_of_nclock (tys, cl) = Con ck x b) as Hcc by exact Hcl.
        simpl clockof. rewrite Hcc.
        apply (lst_clock_closed_when_list ns ts0 x g ck b tys Hg Hin);
          [exact (Forall2_eq_clock _ ts0 (clocksof es) ck Hts Heq)|exact Hl].

      - (** Emerge: the branches run deeper; the sampling name pays for it *)
        intros Hwc ts s s' ns Hns Hrun. destruct a as (tys & cl).
        apply wc_Emerge_inv' in Hwc
          as (ck & Hcl & Hwct & Hwcf & Hin & Heqt & Heqf & Hlt & Hlf).
        rewrite assign_lexp_Emerge in Hrun.
        apply sec_bind_inv in Hrun as (g & s1 & Hg & Hrun).
        apply find_env_inv in Hg as (Hg & ?); subst s1.
        apply sec_bind_inv in Hrun as (ts0 & sa & Hts0 & Hrun).
        apply sec_bind_inv in Hrun as (us & sb & Hus & Hj).
        assert (sec_le sb s') as Hbs'
            by (rewrite (ljoin_list_pure _ us ts sb s' Hj); apply sec_le_refl).
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  ts0 (clocksof ets)) as Hts.
        { apply (assign_lexps_closed_of ets H Hwct ts0 s sa ns); [|exact Hts0].
          apply (minted_incl_sub s s sa s' ns); [apply sec_le_refl| |exact Hns].
          apply (sec_le_trans _ sb _); [|exact Hbs'].
          eapply assign_lexps_sec_le; exact Hus. }
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  us (clocksof efs)) as Hus'.
        { apply (assign_lexps_closed_of efs H0 Hwcf us sa sb ns); [|exact Hus].
          apply (minted_incl_sub s sa sb s' ns); [|exact Hbs'|exact Hns].
          eapply assign_lexps_sec_le; exact Hts0. }
        assert (List.length ts0 = List.length tys) as Hl
            by (apply Forall2_length in Hts; congruence).
        assert (clock_of_nclock (tys, cl) = ck) as Hcc by exact Hcl.
        simpl clockof. rewrite Hcc.
        eapply (lst_clock_closed_merge_list ns ts0 us ts x g ck sb s' tys
                  Hg Hin Hj);
          [exact (Forall2_eq_clock _ ts0 (clocksof ets) _ Hts Heqt)
          |exact (Forall2_eq_clock _ us (clocksof efs) _ Hus' Heqf)
          |exact Hl].

      - (** Eite: everything on the same clock *)
        intros Hwc ts s s' ns Hns Hrun. destruct a as (tys & cl).
        apply wc_Eite_inv' in Hwc
          as (ck & Hcl & Hwce & Hwct & Hwcf & Hcke & Heqt & Heqf & Hlt & Hlf).
        rewrite assign_lexp_Eite in Hrun.
        apply sec_bind_inv in Hrun as (t0 & sa & Ht0 & Hrun).
        apply sec_bind_inv in Hrun as (th & s1 & Hth & Hrun).
        apply single_inv in Hth as (? & ?); subst t0 s1.
        apply sec_bind_inv in Hrun as (ts0 & sb & Hts0 & Hrun).
        apply sec_bind_inv in Hrun as (us & sc & Hus & Hj).
        assert (sec_le sc s') as Hcs'
            by (rewrite (ljoin_list_pure _ us ts sc s' Hj); apply sec_le_refl).
        assert (sec_le sa sc) as Hac
            by (apply (sec_le_trans _ sb _);
                [eapply assign_lexps_sec_le; exact Hts0
                |eapply assign_lexps_sec_le; exact Hus]).
        assert (lst_clock_closed env base_ty vars ns th ck) as Hthc.
        { assert (Forall2 (lst_clock_closed env base_ty vars ns)
                    [th] (clockof e)) as Hh.
          { apply (IHe Hwce [th] s sa ns); [|exact Ht0].
            apply (minted_incl_sub s s sa s' ns);
              [apply sec_le_refl| |exact Hns].
            exact (sec_le_trans _ _ _ Hac Hcs'). }
          rewrite Hcke in Hh. now inversion Hh. }
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  ts0 (clocksof ets)) as Hts.
        { apply (assign_lexps_closed_of ets H Hwct ts0 sa sb ns); [|exact Hts0].
          apply (minted_incl_sub s sa sb s' ns); [| |exact Hns].
          - eapply assign_lexp_type_sec_le; exact Ht0.
          - apply (sec_le_trans _ sc _); [|exact Hcs'].
            eapply assign_lexps_sec_le; exact Hus. }
        assert (Forall2 (lst_clock_closed env base_ty vars ns)
                  us (clocksof efs)) as Hus'.
        { apply (assign_lexps_closed_of efs H0 Hwcf us sb sc ns); [|exact Hus].
          apply (minted_incl_sub s sb sc s' ns); [|exact Hcs'|exact Hns].
          apply (sec_le_trans _ sa _);
            [eapply assign_lexp_type_sec_le; exact Ht0
            |eapply assign_lexps_sec_le; exact Hts0]. }
        assert (List.length ts0 = List.length tys) as Hl
            by (apply Forall2_length in Hts; congruence).
        assert (clock_of_nclock (tys, cl) = ck) as Hcc by exact Hcl.
        simpl clockof. rewrite Hcc.
        eapply (lst_clock_closed_ite_list ns th ts0 us ts ck sc s' tys
                  Hthc Hj);
          [exact (Forall2_eq_clock _ ts0 (clocksof ets) _ Hts Heqt)
          |exact (Forall2_eq_clock _ us (clocksof efs) _ Hus' Heqf)
          |exact Hl].

      - (** Eapp: every result name was minted by this run, so no name the
            statement speaks about is one of them *)
        intros Hwc ts s s' ns Hns Hrun.
        apply assign_lexp_Eapp_inv in Hrun
          as (sg & argts & rstty & ckty0 & outs & cs & sta & stb & stc
              & Hargs & _ & Hrst & _ & Houts & Hcs & Hts).
        pose proof (assign_lexp_Eapp_stages_le G env base_ty rst_ty es ro a
                      s s' sg argts rstty ckty0 outs cs sta stb stc
                      Hargs Hrst Houts Hcs) as (Hab & Hbc & Hcs').
        assert (incl outs ns) as Hmo.
        { intros y Hy.
          apply (minted_incl_sub s stb stc s' ns);
            [apply (sec_le_trans _ sta _);
             [eapply assign_lexps_sec_le; exact Hargs|exact Hab]
            |exact Hcs'|exact Hns|].
          exact (fresh_idents_minted (List.length a) outs stb stc Houts y Hy). }
        subst ts. simpl clockof.
        apply Forall2_all_In.
        + rewrite !map_length.
          exact (fresh_idents_length (List.length a) outs stb stc Houts).
        + intros t Ht ck ckty b Hck Hnm Hb.
          apply in_map_iff in Ht as (o & Ho & Hin).
          subst t. simpl in Hb. destruct Hb as [Hb|[]]; subst b.
          exfalso. exact (Hnm (Hmo o Hin)).
    Qed.

  End LexpClockClosed.

  (** * The dependency property, constraint level

      A constraint's source is [merge (merge [rst_ty] ckty) (fst t)] -- the
      ambient reset, the clock of the variable being defined, and what the
      right-hand side carries.  The property to carry up is therefore
      self-contained: if the source mentions a declared variable's security
      name, it already contains that variable's clock type.

      Three things have to be accounted for, one per part of the source.  The
      reset name is not a declared variable's -- that is [rst_not_var], the
      sibling of the [base_not_var] hypothesis the CoreExpr closure lemmas
      already take.  The clock type is handled by
      [assign_clk_type_clock_closed].  And the right-hand side's own type is
      handled by [assign_lexp_type_clock_closed]. *)

  Definition constraint_clock_closed
      (env : Env.t ident) (base_ty : ident) (vars : list (ident * clock))
      (nomint : list ident) (c : constraint) : Prop :=
    forall v b ckv ckvty,
      Env.find v env = Some b ->
      ~ In b nomint ->
      In b (fst c) ->
      In (v, ckv) vars ->
      assign_clk_type env base_ty ckv = Some ckvty ->
      incl ckvty (fst c).

  Definition constraints_clock_closed
      (env : Env.t ident) (base_ty : ident) (vars : list (ident * clock))
      (nomint : list ident) (cs : list constraint) : Prop :=
    Forall (constraint_clock_closed env base_ty vars nomint) cs.

  Lemma constraints_clock_closed_cmerge :
    forall env base_ty vars ns c1 c2,
      constraints_clock_closed env base_ty vars ns (cmerge c1 c2)
      <-> constraints_clock_closed env base_ty vars ns c1
          /\ constraints_clock_closed env base_ty vars ns c2.
  Proof.
    intros env base_ty vars ns c1 c2.
    unfold constraints_clock_closed. rewrite !Forall_forall. split.
    - intros H. split; intros c Hin; apply H, cmerge_In; tauto.
    - intros (H1 & H2) c Hin. apply cmerge_In in Hin. destruct Hin; auto.
  Qed.

  Lemma constraints_clock_closed_app :
    forall env base_ty vars ns c1 c2,
      constraints_clock_closed env base_ty vars ns c1 ->
      constraints_clock_closed env base_ty vars ns c2 ->
      constraints_clock_closed env base_ty vars ns (c1 ++ c2).
  Proof.
    intros env base_ty vars ns c1 c2 H1 H2.
    unfold constraints_clock_closed. now apply Forall_app.
  Qed.

  Lemma constraint_clock_closed_head :
    forall env base_ty rst_ty vars ns ck ckty t tgt,
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      wc_clock vars ck ->
      assign_clk_type env base_ty ck = Some ckty ->
      lst_clock_closed env base_ty vars ns t ck ->
      constraint_clock_closed env base_ty vars ns
        (merge (merge [rst_ty] ckty) (fst t), tgt).
  Proof.
    intros env base_ty rst_ty vars ns ck ckty t tgt
      Hinj Hnd Hbase Hrst Hwc Hck Ht v b ckv ckvty Hfv Hnm Hb Hinv Hckv.
    cbn [fst] in Hb |- *.
    apply in_merge_inv in Hb as [Hb|Hb].
    - apply in_merge_inv in Hb as [Hb|Hb].
      + destruct Hb as [Hb|[]].
        exfalso. exact (Hrst v ckv b Hinv Hfv (@Coq.Init.Logic.eq_sym _ _ _ Hb)).
      + intros z Hz. apply in_merge_left, in_merge_right.
        exact (assign_clk_type_clock_closed env base_ty vars Hinj Hnd Hbase
                 ck ckty Hwc Hck v b ckv ckvty Hfv Hb Hinv Hckv z Hz).
    - intros z Hz.
      assert (In z (merge ckty (fst t))) as Hz'
          by exact (Ht ckty b Hck Hnm Hb v ckv ckvty Hfv Hinv Hckv z Hz).
      apply in_merge_inv in Hz' as [Hz'|Hz'];
        [apply in_merge_left; now apply in_merge_right
        |now apply in_merge_right].
  Qed.

  (** The ambient part of [ljoin (ambient ckty) t] carries nothing, so the
      generated block splits into the ordering constraint and whatever the
      right-hand side was already carrying. *)
  Lemma constraints_clock_closed_lconstrain :
    forall env base_ty rst_ty vars ns ck ckty t b,
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      wc_clock vars ck ->
      assign_clk_type env base_ty ck = Some ckty ->
      lst_clock_closed env base_ty vars ns t ck ->
      constraints_clock_closed env base_ty vars ns (snd t) ->
      constraints_clock_closed env base_ty vars ns
        (lconstrain (ljoin (ljoin (lvar rst_ty) (ckty, [])) t) b).
  Proof.
    intros env base_ty rst_ty vars ns ck ckty t b
      Hinj Hnd Hbase Hrst Hwc Hck Ht Hcar.
    unfold lconstrain. apply constraints_clock_closed_cmerge. split.
    - constructor; [|constructor].
      rewrite !fst_ljoin, fst_lvar. cbn [fst].
      exact (constraint_clock_closed_head env base_ty rst_ty vars ns ck ckty t
               [b] Hinj Hnd Hbase Hrst Hwc Hck Ht).
    - rewrite !snd_ljoin, snd_lvar. cbn [snd].
      rewrite cmerge_nil, cmerge_nil2. exact Hcar.
  Qed.

  Lemma eqn_clock_type_inv :
    forall env base_ty cenv x ckty s s',
      eqn_clock_type env base_ty cenv x s = OK (ckty, s') ->
      exists ck, find_clock cenv x = OK ck
                 /\ assign_clk_type env base_ty ck = Some ckty
                 /\ s' = s.
  Proof.
    intros env base_ty cenv x ckty s s' H. unfold eqn_clock_type in H.
    apply sec_bind_inv in H as (ck & s1 & Hck & H).
    unfold res_to_sec in Hck.
    destruct (find_clock cenv x) as [ck0|] eqn:Eck; [|discriminate].
    unfold SC.ret in Hck. inversion Hck; subst ck0 s1.
    apply option_to_sec_inv in H as (Hty & ?); subst s'.
    exists ck. auto.
  Qed.

  (** The variable rule mints nothing: [eqn_clock_type] is a lookup and the
      recursion threads the state untouched.  Proved here rather than reused
      from the equation file, which comes later. *)
  Lemma generate_lvars_constraints_advances :
    forall env base_ty rst_ty cenv xs bs ts cs s s',
      generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
        = OK (cs, s') ->
      sec_le s s'.
  Proof.
    intros env base_ty rst_ty cenv xs.
    induction xs as [|x xs IH]; intros bs ts cs s s' H.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      unfold SC.ret in H.
      assert (s' = s) as ? by (inversion H; reflexivity); subst s'.
      apply sec_le_refl.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      apply sec_bind_inv in H as (ckty & s1 & Hckty & H).
      apply sec_bind_inv in H as (rest & s2 & Hrest & Hret).
      apply eqn_clock_type_inv in Hckty as (ck & _ & _ & ?); subst s1.
      unfold SC.ret in Hret.
      assert (s' = s2) as ? by (inversion Hret; reflexivity); subst s'.
      eapply IH; exact Hrest.
  Qed.

  (** The variable rule, one ordering per defined name.  The hypothesis is
      the one the equation level can actually supply: each right-hand side
      type is closed at the clock its defined variable is declared on, which
      is what [wc_equation] pins. *)
  Lemma generate_lvars_constraints_clock_closed :
    forall env base_ty rst_ty vars cenv ns,
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      (forall x ck, find_clock cenv x = OK ck -> In (x, ck) vars) ->
      (forall x ck, In (x, ck) vars -> wc_clock vars ck) ->
      forall xs bs ts cs s s',
        Forall2 (fun x t =>
                   forall ck, find_clock cenv x = OK ck ->
                     lst_clock_closed env base_ty vars ns t ck) xs ts ->
        Forall (fun t => constraints_clock_closed env base_ty vars ns (snd t))
          ts ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
          = OK (cs, s') ->
        constraints_clock_closed env base_ty vars ns cs.
  Proof.
    intros env base_ty rst_ty vars cenv ns Hinj Hnd Hbase Hrst Hcv Hwcv
      xs. induction xs as [|x xs IH]; intros bs ts cs s s' Hall Hcar H.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      unfold SC.ret in H.
      assert (cs = []) as ? by (inversion H; reflexivity); subst cs.
      constructor.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      apply sec_bind_inv in H as (ckty & s1 & Hckty & H).
      apply sec_bind_inv in H as (rest & s2 & Hrest & Hret).
      apply eqn_clock_type_inv in Hckty as (ck & Hck & Hcka & ?); subst s1.
      unfold SC.ret in Hret.
      assert (cs = lconstrain (ljoin (ljoin (lvar rst_ty) (ckty, [])) t) b
                     ++ rest) as ?
          by (inversion Hret; reflexivity); subst cs.
      inversion Hall as [|x0 t0 xs0 ts0 Hxt Hallr]; subst.
      inversion Hcar as [|t1 ts1 Hct Hcarr]; subst.
      apply constraints_clock_closed_app.
      + apply (constraints_clock_closed_lconstrain env base_ty rst_ty vars ns
                 ck ckty t b Hinj Hnd Hbase Hrst);
          [exact (Hwcv x ck (Hcv x ck Hck))|exact Hcka
          |exact (Hxt ck Hck)|exact Hct].
      + eapply IH; [exact Hallr|exact Hcarr|exact Hrest].
  Qed.

  (** What a right-hand side's *carried* constraints have to satisfy.  These
      come only from nested calls, so this is where a callee's signature
      invariant will eventually plug in; isolating it as one hypothesis keeps
      the rules below independent of that step. *)
  Definition lexp_carried_closed
      (G : secglobal) (env : Env.t ident) (base_ty rst_ty : ident)
      (vars : list (ident * clock)) (ns : list ident) (e : exp) : Prop :=
    forall ts s s',
      assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
      Forall (fun t => constraints_clock_closed env base_ty vars ns (snd t)) ts.

  Lemma assign_lexps_carried_closed_of :
    forall G env base_ty rst_ty vars ns es ts s s',
      Forall (lexp_carried_closed G env base_ty rst_ty vars ns) es ->
      assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
      Forall (fun t => constraints_clock_closed env base_ty vars ns (snd t)) ts.
  Proof.
    intros G env base_ty rst_ty vars ns es.
    induction es as [|e es IH]; intros ts s s' Hall H.
    - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
        as (? & _ & ?); subst ts. constructor.
    - apply assign_lexps_carried_cons in H
        as (t & r & sa & Ht & Hr & ? & _); subst ts.
      inversion Hall as [|e0 es0 He Her]; subst.
      apply Forall_app. split; [exact (He t s sa Ht)|eapply IH; eauto].
  Qed.

  (** Two [Forall2]s over a common list of clocks, composed.  This is how the
      equation rule pairs each defined variable with the type of the
      expression that defines it: [wc_equation] relates the variables to
      [clocksof es], and the closure theorem relates the types to the same
      list. *)
  Lemma Forall2_trans_clock :
    forall {A B} (R : A -> clock -> Prop) (Q : B -> clock -> Prop)
           (S : A -> B -> Prop) xs ts cks,
      Forall2 R xs cks ->
      Forall2 Q ts cks ->
      (forall x t ck, R x ck -> Q t ck -> S x t) ->
      Forall2 S xs ts.
  Proof.
    intros A B R Q S xs ts cks HR. revert ts.
    induction HR as [|x ck xs cks Hx HRr IH]; intros ts HQ Hcomb.
    - inversion HQ; subst. constructor.
    - inversion HQ as [|t ck0 ts0 cks0 Ht HQr]; subst.
      constructor; [exact (Hcomb x t ck Hx Ht)|exact (IH ts0 HQr Hcomb)].
  Qed.

  (** The definition rule: one variable, one expression. *)
  Lemma generate_ldef_constraint_clock_closed :
    forall G env base_ty rst_ty vars cenv Pg ns x e cs s s',
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      (forall y ck, find_clock cenv y = OK ck -> In (y, ck) vars) ->
      (forall y ck, In (y, ck) vars -> wc_clock vars ck) ->
      wc_exp Pg vars e ->
      (forall ck, find_clock cenv x = OK ck -> clockof e = [ck]) ->
      lexp_carried_closed G env base_ty rst_ty vars ns e ->
      incl (minted s s') ns ->
      generate_ldef_constraint G env base_ty rst_ty cenv x e s = OK (cs, s') ->
      constraints_clock_closed env base_ty vars ns cs.
  Proof.
    intros G env base_ty rst_ty vars cenv Pg ns x e cs s s'
      Hinj Hnd Hbase Hrst Hcv Hwcv Hwce Hcke Hcar Hns H.
    apply generate_ldef_constraint_inv in H
      as (ck & ckty & sa & rho & b & Hck & Hcka & Hty & Hb & ?); subst cs.
    assert (lst_clock_closed env base_ty vars ns (sa, rho) ck) as Hcl.
    { assert (Forall2 (lst_clock_closed env base_ty vars ns)
                [(sa, rho)] (clockof e)) as Hf
          by exact (assign_lexp_type_clock_closed G env base_ty rst_ty Pg vars
                      Hinj Hnd e Hwce [(sa, rho)] s s' ns Hns Hty).
      rewrite (Hcke ck Hck) in Hf. now inversion Hf. }
    apply constraints_clock_closed_cmerge. split.
    - constructor; [|constructor].
      exact (constraint_clock_closed_head env base_ty rst_ty vars ns ck ckty
               (sa, rho) [b] Hinj Hnd Hbase Hrst
               (Hwcv x ck (Hcv x ck Hck)) Hcka Hcl).
    - assert (Forall (fun t =>
                 constraints_clock_closed env base_ty vars ns (snd t))
                [(sa, rho)]) as Hr by exact (Hcar [(sa, rho)] s s' Hty).
      inversion Hr as [|t0 ts0 Ht0 _]; subst. exact Ht0.
  Qed.

  (** The general rule: a list of expressions against a list of defined
      variables, typed and then ordered. *)
  Lemma generate_lgen_constraint_clock_closed :
    forall G env base_ty rst_ty vars cenv Pg ns xs es cs s s',
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      (forall y ck, find_clock cenv y = OK ck -> In (y, ck) vars) ->
      (forall y ck, In (y, ck) vars -> wc_clock vars ck) ->
      Forall (wc_exp Pg vars) es ->
      Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es) ->
      Forall (lexp_carried_closed G env base_ty rst_ty vars ns) es ->
      incl (minted s s') ns ->
      generate_lgen_constraint G env base_ty rst_ty cenv xs es s = OK (cs, s') ->
      constraints_clock_closed env base_ty vars ns cs.
  Proof.
    intros G env base_ty rst_ty vars cenv Pg ns xs es cs s s'
      Hinj Hnd Hbase Hrst Hcv Hwcv Hwces Hxck Hcar Hns H.
    unfold generate_lgen_constraint in H.
    apply sec_bind_inv in H as (ts & s1 & Hts & H).
    apply sec_bind_inv in H as (bs & s2 & Hbs & Hlv).
    apply option_to_sec_inv in Hbs as (_ & ?); subst s2.
    assert (sec_le s1 s') as Hle1
        by exact (generate_lvars_constraints_advances env base_ty rst_ty cenv
                    xs bs ts cs s1 s' Hlv).
    assert (incl (minted s s1) ns) as Hns1
        by exact (minted_incl_sub s s s1 s' ns (sec_le_refl s) Hle1 Hns).
    assert (Forall2 (lst_clock_closed env base_ty vars ns) ts (clocksof es))
      as Hcls.
    { eapply (assign_lexps_closed_of G env base_ty rst_ty Pg vars es);
        [|exact Hwces|exact Hns1|exact Hts].
      apply Forall_forall. intros e0 _.
      exact (assign_lexp_type_clock_closed G env base_ty rst_ty Pg vars
               Hinj Hnd e0). }
    eapply generate_lvars_constraints_clock_closed;
      [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv| | |
       exact Hlv].
    - eapply (Forall2_trans_clock (fun x ck => In (x, ck) vars)
                (lst_clock_closed env base_ty vars ns));
        [exact Hxck|exact Hcls|].
      intros x0 t ck Hin Hcl ck0 Hck0.
      assert (ck0 = ck) as ?
          by (exact (NoDupMembers_det x0 ck0 ck vars Hnd (Hcv x0 ck0 Hck0) Hin));
        subst ck0.
      exact Hcl.
    - exact (assign_lexps_carried_closed_of G env base_ty rst_ty vars ns es
               ts s s1 Hcar Hts).
  Qed.

  (** The equation rule, for a right-hand side with no call on it.  The call
      rule is the one case left: its constraints are a callee's, instantiated,
      so closing it needs the property as an invariant on [G] -- discharged at
      the program level, like [sig_good] and the others. *)
  Lemma generate_leqn_constraint_clock_closed_plain :
    forall G env base_ty rst_ty vars cenv Pg ns xs es cs s s',
      env_injective env ->
      NoDupMembers vars ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> base_ty) ->
      (forall v ckv c, In (v, ckv) vars ->
                       Env.find v env = Some c -> c <> rst_ty) ->
      (forall y ck, find_clock cenv y = OK ck -> In (y, ck) vars) ->
      (forall y ck, In (y, ck) vars -> wc_clock vars ck) ->
      Forall (fun e => match e with
                       | Eapp _ _ _ _ => False | _ => True end) es ->
      Forall (wc_exp Pg vars) es ->
      Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es) ->
      Forall (lexp_carried_closed G env base_ty rst_ty vars ns) es ->
      incl (minted s s') ns ->
      generate_leqn_constraint G env base_ty rst_ty cenv (xs, es) s
        = OK (cs, s') ->
      constraints_clock_closed env base_ty vars ns cs.
  Proof.
    intros G env base_ty rst_ty vars cenv Pg ns xs es cs s s'
      Hinj Hnd Hbase Hrst Hcv Hwcv Hne Hwces Hxck Hcar Hns H.
    destruct es as [|e [|e2 es2]].

    - (** nothing on the right: the general rule *)
      eapply generate_lgen_constraint_clock_closed;
        [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv
        |exact Hwces|exact Hxck|exact Hcar|exact Hns|exact H].

    - (** one expression: the definition rule when it defines one variable *)
      inversion Hne as [|e0 es0 Hnee _]; subst.
      inversion Hwces as [|e1 es1 Hwce _]; subst.
      inversion Hcar as [|e3 es3 Hcare _]; subst.
      rewrite <- generate_lone_is_leqn in H.
      assert (clocksof [e] = clockof e) as Hcl1
          by (unfold clocksof; simpl; now rewrite app_nil_r).
      destruct xs as [|x [|x2 xs2]].
      + eapply generate_lgen_constraint_clock_closed;
          [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv
          |exact Hwces|exact Hxck|exact Hcar|exact Hns|].
        destruct e; (exact H || contradiction).
      + assert (forall ck, find_clock cenv x = OK ck -> clockof e = [ck])
          as Hcke.
        { intros ck Hck.
          inversion Hxck as [|y ck0 ys cks Hin Hr]; subst.
          inversion Hr; subst.
          assert (ck0 = ck) as ?
              by (exact (NoDupMembers_det x ck0 ck vars Hnd Hin
                           (Hcv x ck Hck))); subst ck0.
          now rewrite <- Hcl1. }
        eapply generate_ldef_constraint_clock_closed;
          [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv
          |exact Hwce|exact Hcke|exact Hcare|exact Hns|].
        destruct e; (exact H || contradiction).
      + eapply generate_lgen_constraint_clock_closed;
          [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv
          |exact Hwces|exact Hxck|exact Hcar|exact Hns|].
        destruct e; (exact H || contradiction).

    - (** two or more, and none of them a call: the general rule again *)
      rewrite gen_leqn_cons2, (has_lcall_false _ Hne) in H.
      eapply generate_lgen_constraint_clock_closed;
        [exact Hinj|exact Hnd|exact Hbase|exact Hrst|exact Hcv|exact Hwcv
        |exact Hwces|exact Hxck|exact Hcar|exact Hns|exact H].
  Qed.

  (** * Transporting the property through [simplify]

      [generate_lnode_sig] does not publish the constraints it generated: it
      publishes [simplify cs (locals ++ minted st0 st1)], which eliminates
      every declared local and every minted call-result name by substituting
      what dominates it.  The dependency property has to survive that.

      It does, but only for the variables it is actually needed for.
      Elimination *removes* names from a source, so a clock type mentioning an
      eliminated name would not survive.  That never happens for an **input**:
      [wc_node] requires [wc_env (idck n_in)], so an input's declared clock
      mentions only inputs, and inputs are exactly what [simplify] keeps.
      That is what the [keep] set below is: the names a clock type of interest
      may mention, and which no elimination touches. *)

  Definition st_clock_closed
      (env : Env.t ident) (base_ty : ident) (vars : list (ident * clock))
      (nomint : list ident) (t : ST) : Prop :=
    forall v b ckv ckvty,
      Env.find v env = Some b ->
      ~ In b nomint ->
      In b t ->
      In (v, ckv) vars ->
      assign_clk_type env base_ty ckv = Some ckvty ->
      incl ckvty t.

  Lemma constraint_clock_closed_fst :
    forall env base_ty vars ns c,
      constraint_clock_closed env base_ty vars ns c
      <-> st_clock_closed env base_ty vars ns (fst c).
  Proof. intros env base_ty vars ns c. split; intro H; exact H. Qed.

  (** The three shapes an elimination can take, so the proof below can
      [rewrite] rather than unfold through an alias. *)
  Lemma subST_cases :
    forall st d st',
      SymTypes.subST st d st' = st
      \/ SymTypes.subST st d st'
         = merge (SymTypes.st_remove d st) (SymTypes.st_remove d st')
      \/ SymTypes.subST st d st' = merge (SymTypes.st_remove d st) st'.
  Proof.
    intros st d st'. unfold SymTypes.subST.
    destruct (SymTypes.st_mem d st) eqn:Em; [|now left].
    destruct (SymTypes.st_mem d st') eqn:Em';
      [right; now left|right; now right].
  Qed.

  (** One elimination step.  Three removals happen -- the eliminated name from
      the source, the eliminated name from the substituted type, and the
      constraint's own target -- and none of them can touch a clock type,
      because none of the three is in [keep]. *)
  Lemma subAll_clock_closed :
    forall env base_ty vars ns keep cns d st',
      (forall v ckv ckvty, In (v, ckv) vars ->
          assign_clk_type env base_ty ckv = Some ckvty -> incl ckvty keep) ->
      ~ In d keep ->
      (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep) ->
      st_clock_closed env base_ty vars ns st' ->
      constraints_clock_closed env base_ty vars ns cns ->
      constraints_clock_closed env base_ty vars ns (subAll cns d st').
  Proof.
    intros env base_ty vars ns keep cns d st' Hkeep Hd Htgt Hst' Hcns.
    induction cns as [|c cns IH]; [constructor|].
    inversion Hcns as [|c0 cns0 Hc Hcns']; subst.
    assert (forall c0, In c0 cns -> forall y, In y (snd c0) -> ~ In y keep)
      as Htgt' by (intros c0 Hin; apply Htgt; now right).
    destruct c as (st, tgt).
    destruct tgt as [|d' [|]]; simpl; try exact (IH Htgt' Hcns').
    destruct (ident_eqb d' d) eqn:Edd; [exact (IH Htgt' Hcns')|].
    constructor; [|exact (IH Htgt' Hcns')].
    assert (~ In d' keep) as Hd'
        by (apply (Htgt (st, [d'])); [now left|now left]).
    intros v b ckv ckvty Hfv Hnm Hb Hinv Hckv.
    assert (incl ckvty keep) as Hck by exact (Hkeep v ckv ckvty Hinv Hckv).
    cbn [fst] in Hb |- *.
    apply st_remove_in_inv in Hb as (Hb & _).
    (** the eliminated name and the target are both outside [keep], so a clock
        type survives every removal *)
    assert (forall t, incl ckvty t -> incl ckvty (st_remove d t)) as Hkd.
    { intros t Ht z Hz. apply st_remove_preserves_other_in;
        [intro; subst z; exact (Hd (Hck d Hz))|exact (Ht z Hz)]. }
    assert (incl ckvty (SymTypes.subST st d st')) as Hsub.
    { destruct (subST_cases st d st') as [E|[E|E]]; rewrite E in Hb |- *.
      - exact (Hc v b ckv ckvty Hfv Hnm Hb Hinv Hckv).
      - apply in_merge_inv in Hb as [Hb|Hb].
        + apply st_remove_in_inv in Hb as (Hb & _).
          intros z Hz. apply in_merge_left.
          exact (Hkd st (Hc v b ckv ckvty Hfv Hnm Hb Hinv Hckv) z Hz).
        + apply st_remove_in_inv in Hb as (Hb & _).
          intros z Hz. apply in_merge_right.
          exact (Hkd st' (Hst' v b ckv ckvty Hfv Hnm Hb Hinv Hckv) z Hz).
      - apply in_merge_inv in Hb as [Hb|Hb].
        + apply st_remove_in_inv in Hb as (Hb & _).
          intros z Hz. apply in_merge_left.
          exact (Hkd st (Hc v b ckv ckvty Hfv Hnm Hb Hinv Hckv) z Hz).
        + intros z Hz. apply in_merge_right.
          exact (Hst' v b ckv ckvty Hfv Hnm Hb Hinv Hckv z Hz). }
    intros z Hz. apply st_remove_preserves_other_in;
      [intro; subst z; exact (Hd' (Hck d' Hz))|exact (Hsub z Hz)].
  Qed.

  (** [findST] returns the source of a constraint of the list, so what gets
      substituted in is itself closed. *)
  Lemma findST_clock_closed :
    forall env base_ty vars ns cns d st',
      constraints_clock_closed env base_ty vars ns cns ->
      findST cns d = Some st' ->
      st_clock_closed env base_ty vars ns st'.
  Proof.
    intros env base_ty vars ns cns d st' Hcns Hf.
    apply find_correct in Hf.
    unfold constraints_clock_closed in Hcns.
    rewrite Forall_forall in Hcns.
    exact (Hcns (st', [d]) Hf).
  Qed.

  (** Eliminating a name can only drop targets, never add them, so the
      side condition on targets survives each step. *)
  Lemma subAll_targets :
    forall keep cns d st',
      (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep) ->
      forall c, In c (subAll cns d st') -> forall y, In y (snd c) -> ~ In y keep.
  Proof.
    intros keep cns d st' Htgt.
    induction cns as [|c0 cns IH]; [intros c []|].
    assert (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep)
      as Htgt' by (intros c Hin; apply Htgt; now right).
    destruct c0 as (st, tgt).
    destruct tgt as [|d' [|]]; simpl; try exact (IH Htgt').
    destruct (ident_eqb d' d); [exact (IH Htgt')|].
    intros c [Hc|Hc]; [|exact (IH Htgt' c Hc)].
    subst c. cbn [snd]. intros y Hy.
    exact (Htgt (st, [d']) (or_introl (@Coq.Init.Logic.eq_refl _ (st, [d'])))
             y Hy).
  Qed.

  (** And so the whole of [simplify].  The premise is about the eliminated
      names only: none of them may occur in a clock type of interest, which
      for a node's *inputs* is what [wc_env (idck n_in)] gives -- an input's
      clock mentions only inputs, and inputs are not eliminated. *)
  Lemma simplify_clock_closed :
    forall env base_ty vars ns keep ds cns,
      (forall v ckv ckvty, In (v, ckv) vars ->
          assign_clk_type env base_ty ckv = Some ckvty -> incl ckvty keep) ->
      (forall d, In d ds -> ~ In d keep) ->
      (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep) ->
      constraints_clock_closed env base_ty vars ns cns ->
      constraints_clock_closed env base_ty vars ns (simplify cns ds).
  Proof.
    intros env base_ty vars ns keep ds.
    induction ds as [|d ds IH]; intros cns Hkeep Hds Htgt Hcns;
      [exact Hcns|].
    simpl. destruct (SymTypes.findST cns d) as [st'|] eqn:Ef.
    - apply IH;
        [exact Hkeep|intros d0 Hd0; apply Hds; now right| |].
      + exact (subAll_targets keep cns d st' Htgt).
      + apply (subAll_clock_closed env base_ty vars ns keep cns d st' Hkeep);
          [apply Hds; now left|exact Htgt
          |exact (findST_clock_closed env base_ty vars ns cns d st' Hcns Ef)
          |exact Hcns].
    - apply IH; [exact Hkeep|intros d0 Hd0; apply Hds; now right
                |exact Htgt|exact Hcns].
  Qed.

  (** * Instantiating a clock, and what its type can mention

      At a call, a formal's declared clock [ck] is instantiated as
      [instck bck sub ck]: the sampling variables are mapped through [sub] to
      the caller's streams, and the whole thing is rooted at the call's base
      clock.  Its security type therefore mentions only the base clock's type
      and the security names of those substituted streams -- nothing else.

      That is the fact both remaining consumers need.  The dependency property
      needs it to see that an argument's clock type is already covered by the
      actuals; the pointwise contract needs it for the same reason on the
      streams side. *)

  Fixpoint clock_vars (ck : clock) : list ident :=
    match ck with
    | Cbase => []
    | Con ck' x _ => x :: clock_vars ck'
    end.

  Lemma assign_clk_type_instck :
    forall env base_ty bk sub ck ck' bkty ckty,
      instck bk sub ck = Some ck' ->
      assign_clk_type env base_ty bk = Some bkty ->
      assign_clk_type env base_ty ck' = Some ckty ->
      forall z, In z ckty ->
        In z bkty
        \/ exists x x', In x (clock_vars ck)
                        /\ sub x = Some x'
                        /\ Env.find x' env = Some z.
  Proof.
    intros env base_ty bk sub ck. revert bk.
    induction ck as [|ck0 IH x b]; intros bk ck' bkty ckty Hi Hbk Hck z Hz.
    - (** the base clock: the instantiated clock *is* the base clock *)
      simpl in Hi. apply option_Some_inj in Hi. subst ck'.
      rewrite Hbk in Hck. apply option_Some_inj in Hck. subst ckty.
      now left.
    - (** one more sampling variable, and it came from [sub] *)
      simpl in Hi.
      destruct (instck bk sub ck0) as [ck0'|] eqn:Ei; [|discriminate Hi].
      destruct (sub x) as [x'|] eqn:Ex; [|discriminate Hi].
      apply option_Some_inj in Hi. subst ck'.
      apply assign_clk_type_Con_inv in Hck
        as (ck0ty & g & Hck0 & Hg & ?); subst ckty.
      apply in_merge_inv in Hz as [Hz|Hz].
      + destruct (IH bk ck0' bkty ck0ty Ei Hbk Hck0 z Hz)
          as [Hzb|(x0 & x0' & Hin & Hs & He)];
          [now left|].
        right. exists x0, x0'. split; [now right|auto].
      + destruct Hz as [Hz|[]]; subst g.
        right. exists x, x'. split; [now left|auto].
  Qed.

  Corollary assign_clk_type_instck_incl :
    forall env base_ty bk sub ck ck' bkty ckty acts,
      instck bk sub ck = Some ck' ->
      assign_clk_type env base_ty bk = Some bkty ->
      assign_clk_type env base_ty ck' = Some ckty ->
      (forall x x' z, In x (clock_vars ck) -> sub x = Some x' ->
                      Env.find x' env = Some z -> In z acts) ->
      incl ckty (merge bkty acts).
  Proof.
    intros env base_ty bk sub ck ck' bkty ckty acts Hi Hbk Hck Hact z Hz.
    destruct (assign_clk_type_instck env base_ty bk sub ck ck' bkty ckty
                Hi Hbk Hck z Hz) as [Hzb|(x & x' & Hin & Hs & He)].
    - now apply in_merge_left.
    - apply in_merge_right. exact (Hact x x' z Hin Hs He).
  Qed.

  (** A well-clocked clock's variables are declared, which is what turns the
      membership above into a fact about [vars]. *)
  Lemma clock_vars_wc :
    forall vars ck,
      wc_clock vars ck ->
      forall x, In x (clock_vars ck) -> exists ckx, In (x, ckx) vars.
  Proof.
    intros vars ck Hwc. induction Hwc as [|ck0 y b Hwc IH Hin];
      intros x Hx; [contradiction|].
    destruct Hx as [Hx|Hx]; [subst x; now exists ck0|exact (IH x Hx)].
  Qed.

  (** * Clock types exist where the naming pass has named the clock's variables

      [assign_clk_type]'s only partiality is an [Env.find] on a sampling
      variable, so it succeeds on any clock whose variables the naming pass
      covered.  Together with [clock_vars_wc] that makes it total on the
      clocks of a well-clocked node: [wc_env] says a declared variable's clock
      is well clocked, and [wc_equation] says an equation's stream clocks are
      declared variables' clocks. *)

  Lemma assign_clk_type_total_of_vars :
    forall env base_ty ck,
      (forall x, In x (clock_vars ck) -> exists b, Env.find x env = Some b) ->
      exists ckty, assign_clk_type env base_ty ck = Some ckty.
  Proof.
    intros env base_ty ck. induction ck as [|ck IH x b]; intros Hvars.
    - exists [base_ty]. reflexivity.
    - destruct (IH ltac:(intros y Hy; apply Hvars; now right))
        as (ckty & Hck).
      destruct (Hvars x ltac:(now left)) as (bx & Hbx).
      exists (merge ckty [bx]).
      cbn [assign_clk_type]. rewrite Hck, Hbx. reflexivity.
  Qed.

  Lemma clocksof_types_defined :
    forall env base_ty P vars (eq : equation),
      wc_env vars ->
      wc_equation P vars eq ->
      (forall x ck, In (x, ck) vars -> exists b, Env.find x env = Some b) ->
      forall ck, In ck (clocksof (snd eq)) ->
                 exists ckty, assign_clk_type env base_ty ck = Some ckty.
  Proof.
    intros env base_ty P vars (xs & es) Hwcenv Hwceq Henv ck Hck.
    cbn [snd] in Hck.
    destruct Hwceq as (_ & _ & Hvars).
    assert (exists x, In (x, ck) vars) as (x & Hxv).
    { destruct (Forall2_in_right _ xs (clocksof es) ck Hvars Hck)
        as (y & _ & Hyv).
      exists y. exact Hyv. }
    assert (wc_clock vars ck) as Hwck.
    { unfold wc_env in Hwcenv. rewrite Forall_forall in Hwcenv.
      exact (Hwcenv (x, ck) Hxv). }
    apply assign_clk_type_total_of_vars.
    intros y Hy.
    destruct (clock_vars_wc vars ck Hwck y Hy) as (cky & Hyv).
    exact (Henv y cky Hyv).
  Qed.

  (** The same for an expression's own stream clocks, which is the form the
      call case's [clk_types_defined] asks for.  Note what it reduces to: the
      *arguments'* clocks being well clocked in [vars].  [wc_exp_clockof]
      gives that over [vars ++ idck (fresh_in e)], so it is immediate for an
      argument with no nested call in it, and for one with a nested call it is
      a genuine restriction -- a nested call's output name is anonymous, and
      [env_key_not_anon] says the naming pass never named it, so
      [assign_clk_type] on a clock sampled by one does not merely go
      unproved, it fails.  Programs where that happens are the ones the
      generator rejects. *)
  Lemma nclockof_types_defined :
    forall env base_ty vars e,
      Forall (wc_clock vars) (clockof e) ->
      (forall x ck, In (x, ck) vars -> exists b, Env.find x env = Some b) ->
      forall nck, In nck (nclockof e) ->
        exists ckty, assign_clk_type env base_ty (stripname nck) = Some ckty.
  Proof.
    intros env base_ty vars e Hwc Henv nck Hnck.
    assert (In (stripname nck) (clockof e)) as Hin.
    { rewrite clockof_nclockof. apply in_map_iff.
      exists nck. split; [reflexivity|exact Hnck]. }
    rewrite Forall_forall in Hwc.
    apply assign_clk_type_total_of_vars.
    intros y Hy.
    destruct (clock_vars_wc vars (stripname nck) (Hwc _ Hin) y Hy)
      as (cky & Hyv).
    exact (Henv y cky Hyv).
  Qed.

  (** The generator reads the call's base clock off the arguments, as
      [find_base_clock (clocksof es)]; clocking calls it [bck].  They agree,
      and this is where [wc_global] is needed -- the callee's own
      [wc_env (idck n_in)] is what makes [bck] the common parent.  The
      argument is Velus's, lifted out of [TrClocking] so both consumers can
      use it as a lemma. *)
  Lemma wc_exp_Eapp_base_clock :
    forall P n f es bck sub,
      wc_global P ->
      find_node f P = Some n ->
      Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
      find_base_clock (clocksof es) = bck.
  Proof.
    intros P n f es bck sub Hwcg Hfind WIi.
    pose proof (wc_find_node P f n Hwcg Hfind) as (G' & (Wcin & _)).
    apply find_base_clock_bck.
    - rewrite clocksof_nclocksof.
      eapply WellInstantiated_bck; [exact Wcin| |exact WIi].
      unfold idck. rewrite map_length. exact (n_ingt0 n).
    - apply WellInstantiated_parent in WIi.
      rewrite clocksof_nclocksof, Forall_map.
      eapply Forall_impl; [|exact WIi]. now simpl.
  Qed.

  (** * A named argument stream carries its own name

      The dependency property's call case needs this: the actual sitting at a
      *clock* position of a call contributes its own security name to its type,
      so the callee's instantiated clock type is covered by the actuals.

      Only two constructors can carry a stream name at all.  [wc_exp] forces
      [None] on every other one, so they are vacuous.  [Evar]'s name is pinned
      to the variable, and its type is exactly that variable's security name.
      [Eapp]'s names are *anonymous*: they are in [anon_streams] of the
      annotation, hence -- by [n_nodup] and the naming pass's domain -- not
      keys of [env] at all.  That last fact cannot be proved here, where [env]
      is abstract, so it is a premise; at the program level it is
      [call_arg_fresh_not_env_key].

      Note this speaks about the *top-level* streams only, so the premise is
      needed only for a call at the top of the expression -- no recursion. *)

  Lemma named_covered_vacuous :
    forall (env : Env.t ident) (l : list nclock) (us : list LST),
      List.length us = List.length l ->
      Forall (fun nck => forall w g,
                  snd nck = Some w -> Env.find w env <> Some g) l ->
      Forall2 (fun t nck => forall w g,
                   snd nck = Some w -> Env.find w env = Some g -> In g (fst t))
        us l.
  Proof.
    intros env l. induction l as [|nck l IH]; intros us Hl Hno.
    - destruct us; [constructor|discriminate].
    - destruct us as [|t us]; [discriminate|].
      inversion Hno as [|nck0 l0 Hn Hr]; subst.
      constructor; [|apply IH; [simpl in Hl; congruence|exact Hr]].
      intros w g Hw Hg. exfalso. exact (Hn w g Hw Hg).
  Qed.

  Lemma unnamed_no_key :
    forall (env : Env.t ident) (l : list nclock),
      Forall (fun nck => snd nck = None) l ->
      Forall (fun nck => forall w g,
                  snd nck = Some w -> Env.find w env <> Some g) l.
  Proof.
    intros env l H. rewrite Forall_forall in H |- *.
    intros nck Hin w g Hw Hg.
    specialize (H nck Hin).
    assert (@None ident = Some w) as Hc by (rewrite <- H; exact Hw).
    discriminate Hc.
  Qed.

  Lemma assign_lexp_named_covered :
    forall P G env base_ty rst_ty vars e,
      wl_exp P e ->
      wc_exp P vars e ->
      (forall f es' ro anns, e = Eapp f es' ro anns ->
          forall w g, In (Some w) (List.map stream_name anns) ->
                      Env.find w env <> Some g) ->
      forall ts s s',
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        Forall2 (fun t nck => forall w g,
                     snd nck = Some w -> Env.find w env = Some g ->
                     In g (fst t))
          ts (nclockof e).
  Proof.
    intros P G env base_ty rst_ty vars e Hwl Hwc Hanon ts s s' Hty.
    assert (List.length ts = List.length (nclockof e)) as Hlen'.
    { rewrite (assign_lexp_type_length P G env base_ty rst_ty e Hwl ts s s' Hty).
      symmetry. apply length_nclockof_numstreams. }
    destruct e as [c|x a|op e1 a|op e1 e2 a|e0s es anns|e0s es anns
                  |es x b a|x ets efs a|e0 ets efs a|f es ro anns].
    - (** Econst *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. simpl. now repeat constructor.
    - (** Evar: the name is the variable, and the type is its own *)
      rewrite assign_lexp_Evar in Hty.
      apply sec_bind_inv in Hty as (g0 & s1 & Hg0 & Hret).
      apply find_env_inv in Hg0 as (Hg0 & ?); subst s1.
      unfold SC.ret in Hret.
      assert (ts = [lvar g0]) as ? by (inversion Hret; reflexivity); subst ts.
      simpl nclockof. constructor; [|constructor].
      inv Hwc.
      + cbn [snd]. intros w g Hw Hg.
        assert (w = x) as ? by (inversion Hw; reflexivity); subst w.
        rewrite Hg0 in Hg. apply option_Some_inj in Hg; subst g.
        rewrite fst_lvar. now left.
      + cbn [snd]. intros w g Hw. discriminate.
    - (** Eunop *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl. now repeat constructor.
    - (** Ebinop *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl. now repeat constructor.
    - (** Efby: [wc_exp] makes every annotation unnamed *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl nclockof. rewrite Forall_map.
      match goal with H : Forall unnamed_stream anns |- _ =>
        eapply Forall_impl; [|exact H] end.
      intros ann Hann. exact Hann.
    - (** Earrow *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl nclockof. rewrite Forall_map.
      match goal with H : Forall unnamed_stream anns |- _ =>
        eapply Forall_impl; [|exact H] end.
      intros ann Hann. exact Hann.
    - (** Ewhen *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl nclockof. rewrite Forall_map.
      apply Forall_forall. intros ? _. reflexivity.
    - (** Emerge *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl nclockof. rewrite Forall_map.
      apply Forall_forall. intros ? _. reflexivity.
    - (** Eite *)
      apply named_covered_vacuous; [exact Hlen'|].
      apply unnamed_no_key. inv Hwc. simpl nclockof. rewrite Forall_map.
      apply Forall_forall. intros ? _. reflexivity.
    - (** Eapp: the names are anonymous, so the premise makes it vacuous *)
      apply named_covered_vacuous; [exact Hlen'|].
      simpl nclockof. rewrite Forall_map. apply Forall_forall.
      intros ann Hin w g Hw.
      apply (Hanon f es ro anns (@Coq.Init.Logic.eq_refl _ _) w g).
      apply in_map_iff. exists ann. split; [exact Hw|exact Hin].
  Qed.

  (** * Slots of a call, by position

      A call lines up four lists: the callee's declared inputs with their
      clocks, the callee's formal security names, the actuals' nclocks, and the
      actuals' types.  The arguments below match them up by index, so these
      two directions between [combine] and [nth_error] are needed. *)

  Lemma In_combine_nth_error :
    forall {A B} (xs : list A) (ys : list B) x y,
      In (x, y) (combine xs ys) ->
      exists i, nth_error xs i = Some x /\ nth_error ys i = Some y.
  Proof.
    intros A B xs. induction xs as [|a xs IH]; intros ys x y Hin.
    - destruct ys; simpl in Hin; contradiction.
    - destruct ys as [|b ys]; simpl in Hin; [contradiction|].
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst. exists 0%nat. split; reflexivity.
      + destruct (IH ys x y Hin) as (i & H1 & H2).
        exists (S i). split; [exact H1|exact H2].
  Qed.

  Lemma nth_error_In_combine :
    forall {A B} (xs : list A) (ys : list B) i x y,
      nth_error xs i = Some x -> nth_error ys i = Some y ->
      In (x, y) (combine xs ys).
  Proof.
    intros A B xs. induction xs as [|a xs IH]; intros ys i x y Hx Hy.
    - destruct i; discriminate.
    - destruct ys as [|b ys]; [destruct i; discriminate|].
      destruct i as [|i]; simpl in Hx, Hy.
      + inversion Hx; inversion Hy; subst. now left.
      + right. exact (IH ys i x y Hx Hy).
  Qed.

  Lemma nth_error_lt :
    forall {A} (l : list A) i,
      (i < List.length l)%nat -> exists x, nth_error l i = Some x.
  Proof.
    intros A l i Hi. destruct (nth_error l i) as [x|] eqn:E; [now exists x|].
    exfalso. apply nth_error_None in E. lia.
  Qed.

  Lemma nth_error_lt_inv :
    forall {A} (l : list A) i x,
      nth_error l i = Some x -> (i < List.length l)%nat.
  Proof.
    intros A l i x H. apply nth_error_Some. now rewrite H.
  Qed.

  (** Instantiation only ever *extends* the base clock, so the call's base
      clock is a prefix of every clock it instantiates -- of the outputs' as
      much as the inputs'.  With [assign_clk_type_prefix_incl] this is what
      makes the uniform ambient small enough for every result: it is below each
      output's own ambient. *)
  Lemma instck_clock_prefix :
    forall bk sub ck ck',
      instck bk sub ck = Some ck' -> clock_prefix bk ck'.
  Proof.
    intros bk sub ck. revert bk.
    induction ck as [|ck0 IH x b]; intros bk ck' Hi.
    - simpl in Hi. apply option_Some_inj in Hi. subst ck'.
      apply clock_prefix_refl.
    - simpl in Hi.
      destruct (instck bk sub ck0) as [ck0'|] eqn:Ei; [|discriminate Hi].
      destruct (sub x) as [x'|] eqn:Ex; [|discriminate Hi].
      apply option_Some_inj in Hi. subst ck'.
      apply clock_prefix_con. exact (IH bk ck0' Ei).
  Qed.

  Corollary assign_clk_type_instck_base_incl :
    forall env base_ty bk sub ck ck' bkty ckty,
      instck bk sub ck = Some ck' ->
      assign_clk_type env base_ty bk = Some bkty ->
      assign_clk_type env base_ty ck' = Some ckty ->
      incl bkty ckty.
  Proof.
    intros env base_ty bk sub ck ck' bkty ckty Hi Hbk Hck.
    exact (assign_clk_type_prefix_incl env base_ty bk ck' bkty ckty
             (instck_clock_prefix bk sub ck ck' Hi) Hbk Hck).
  Qed.

  (** [Forall2] read off by position, which is how a [WellInstantiated] chain
      feeds the positional statements. *)
  Lemma Forall2_nth_error :
    forall {A B} (R : A -> B -> Prop) xs ys i x y,
      Forall2 R xs ys ->
      nth_error xs i = Some x -> nth_error ys i = Some y -> R x y.
  Proof.
    intros A B R xs ys i x y H. revert i.
    induction H as [|a b xs' ys' Hab Hr IH]; intros i Hx Hy.
    - destruct i; discriminate.
    - destruct i as [|i]; simpl in Hx, Hy.
      + inversion Hx; inversion Hy; subst. exact Hab.
      + exact (IH i Hx Hy).
  Qed.

  Lemma nth_error_map_inv :
    forall {A B} (f : A -> B) (l : list A) i y,
      nth_error (List.map f l) i = Some y ->
      exists x, nth_error l i = Some x /\ y = f x.
  Proof.
    intros A B f l. induction l as [|a l IH]; intros i y H.
    - destruct i; discriminate.
    - destruct i as [|i]; simpl in H.
      + inversion H. now exists a.
      + exact (IH i y H).
  Qed.

  (** The list form of [assign_lexp_named_covered]: every stream of an argument
      list that carries a name carries its own security name.  The premise is
      needed only for the calls sitting at the top of the list. *)
  Lemma assign_lexps_named_covered :
    forall P G env base_ty rst_ty vars es,
      Forall (wl_exp P) es ->
      Forall (wc_exp P vars) es ->
      (forall e f es' ro anns, In e es -> e = Eapp f es' ro anns ->
          forall w g, In (Some w) (List.map stream_name anns) ->
                      Env.find w env <> Some g) ->
      forall ts s s',
        assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
        Forall2 (fun t nck => forall w g,
                     snd nck = Some w -> Env.find w env = Some g ->
                     In g (fst t))
          ts (nclocksof es).
  Proof.
    intros P G env base_ty rst_ty vars es.
    induction es as [|e es IH]; intros Hwl Hwc Hanon ts s s' H.
    - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
        as (? & _ & ?); subst ts. constructor.
    - apply assign_lexps_carried_cons in H
        as (t & r & sa & Ht & Hr & ? & _); subst ts.
      inversion Hwl as [|e0 es0 Hwle Hwlr]; subst.
      inversion Hwc as [|e1 es1 Hwce Hwcr]; subst.
      unfold nclocksof. simpl flat_map. apply Forall2_app.
      + eapply (assign_lexp_named_covered P G env base_ty rst_ty vars e
                  Hwle Hwce); [|exact Ht].
        intros f es' ro anns Heq w g Hw.
        exact (Hanon e f es' ro anns (or_introl (@Coq.Init.Logic.eq_refl _ e))
                 Heq w g Hw).
      + eapply (IH Hwlr Hwcr); [|exact Hr].
        intros e' f es' ro anns Hin Heq w g Hw.
        exact (Hanon e' f es' ro anns (or_intror Hin) Heq w g Hw).
  Qed.

  Lemma nth_error_combine :
    forall {A B} (xs : list A) (ys : list B) i x y,
      nth_error xs i = Some x -> nth_error ys i = Some y ->
      nth_error (combine xs ys) i = Some (x, y).
  Proof.
    intros A B xs. induction xs as [|a xs IH]; intros ys i x y Hx Hy.
    - destruct i; discriminate.
    - destruct ys as [|b ys]; [destruct i; discriminate|].
      destruct i as [|i]; simpl in Hx, Hy |- *.
      + inversion Hx; inversion Hy; subst. reflexivity.
      + exact (IH ys i x y Hx Hy).
  Qed.

  (** * Every generated source mentions the base and the reset

      The call rule of the dependency property needs the *callee's* sources to
      mention [s_clk] and [s_reset]: that is what puts the call's base clock
      type and reset level into the instantiated source, and those are what an
      argument's own clock type is covered by.  On the generating side the
      property is immediate -- every source is
      [merge (merge [rst_ty] ckty) (fst t)] and every clock type contains the
      base name -- but it has to be carried up the same way closure was, and
      through [simplify]. *)

  Lemma assign_clk_type_base :
    forall env base_ty ck ckty,
      assign_clk_type env base_ty ck = Some ckty -> In base_ty ckty.
  Proof.
    intros env base_ty ck. induction ck as [|ck0 IH x b]; intros ckty H.
    - simpl in H. apply option_Some_inj in H. subst ckty. now left.
    - apply assign_clk_type_Con_inv in H
        as (ckty0 & g & Hck0 & Hg & ?); subst ckty.
      apply in_merge_left. exact (IH ckty0 Hck0).
  Qed.

  Definition constraint_rooted (base_ty rst_ty : ident) (c : constraint) : Prop :=
    In base_ty (fst c) /\ In rst_ty (fst c).

  Definition constraints_rooted
      (base_ty rst_ty : ident) (cs : list constraint) : Prop :=
    Forall (constraint_rooted base_ty rst_ty) cs.

  Lemma constraints_rooted_cmerge :
    forall base_ty rst_ty c1 c2,
      constraints_rooted base_ty rst_ty (cmerge c1 c2)
      <-> constraints_rooted base_ty rst_ty c1
          /\ constraints_rooted base_ty rst_ty c2.
  Proof.
    intros base_ty rst_ty c1 c2.
    unfold constraints_rooted. rewrite !Forall_forall. split.
    - intros H. split; intros c Hin; apply H, cmerge_In; tauto.
    - intros (H1 & H2) c Hin. apply cmerge_In in Hin. destruct Hin; auto.
  Qed.

  Lemma constraints_rooted_app :
    forall base_ty rst_ty c1 c2,
      constraints_rooted base_ty rst_ty c1 ->
      constraints_rooted base_ty rst_ty c2 ->
      constraints_rooted base_ty rst_ty (c1 ++ c2).
  Proof.
    intros base_ty rst_ty c1 c2 H1 H2.
    unfold constraints_rooted. now apply Forall_app.
  Qed.

  Lemma constraint_rooted_head :
    forall env base_ty rst_ty ck ckty (t : LST) (tgt : list ident),
      assign_clk_type env base_ty ck = Some ckty ->
      constraint_rooted base_ty rst_ty
        (merge (merge [rst_ty] ckty) (fst t), tgt).
  Proof.
    intros env base_ty rst_ty ck ckty t tgt Hck.
    split; cbn [fst].
    - apply in_merge_left, in_merge_right.
      exact (assign_clk_type_base env base_ty ck ckty Hck).
    - apply in_merge_left, in_merge_left. now left.
  Qed.

  Lemma constraints_rooted_lconstrain :
    forall env base_ty rst_ty ck ckty t b,
      assign_clk_type env base_ty ck = Some ckty ->
      constraints_rooted base_ty rst_ty (snd t) ->
      constraints_rooted base_ty rst_ty
        (lconstrain (ljoin (ljoin (lvar rst_ty) (ckty, [])) t) b).
  Proof.
    intros env base_ty rst_ty ck ckty t b Hck Hcar.
    unfold lconstrain. apply constraints_rooted_cmerge. split.
    - constructor; [|constructor].
      rewrite !fst_ljoin, fst_lvar. cbn [fst].
      exact (constraint_rooted_head env base_ty rst_ty ck ckty t [b] Hck).
    - rewrite !snd_ljoin, snd_lvar. cbn [snd].
      rewrite cmerge_nil, cmerge_nil2. exact Hcar.
  Qed.

  Lemma generate_lvars_constraints_rooted :
    forall env base_ty rst_ty cenv xs bs ts cs s s',
      Forall (fun t => constraints_rooted base_ty rst_ty (snd t)) ts ->
      generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
        = OK (cs, s') ->
      constraints_rooted base_ty rst_ty cs.
  Proof.
    intros env base_ty rst_ty cenv xs.
    induction xs as [|x xs IH]; intros bs ts cs s s' Hcar H.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      unfold SC.ret in H.
      assert (cs = []) as ? by (inversion H; reflexivity); subst cs.
      constructor.
    - destruct bs as [|b bs]; destruct ts as [|t ts]; simpl in H;
        try discriminate.
      apply sec_bind_inv in H as (ckty & s1 & Hckty & H).
      apply sec_bind_inv in H as (rest & s2 & Hrest & Hret).
      apply eqn_clock_type_inv in Hckty as (ck & Hck & Hcka & ?); subst s1.
      unfold SC.ret in Hret.
      assert (cs = lconstrain (ljoin (ljoin (lvar rst_ty) (ckty, [])) t) b
                     ++ rest) as ?
          by (inversion Hret; reflexivity); subst cs.
      inversion Hcar as [|t1 ts1 Hct Hcarr]; subst.
      apply constraints_rooted_app.
      + exact (constraints_rooted_lconstrain env base_ty rst_ty ck ckty t b
                 Hcka Hct).
      + eapply IH; [exact Hcarr|exact Hrest].
  Qed.

  Definition lexp_carried_rooted
      (G : secglobal) (env : Env.t ident) (base_ty rst_ty : ident)
      (e : exp) : Prop :=
    forall ts s s',
      assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
      Forall (fun t => constraints_rooted base_ty rst_ty (snd t)) ts.

  Lemma assign_lexps_carried_rooted_of :
    forall G env base_ty rst_ty es ts s s',
      Forall (lexp_carried_rooted G env base_ty rst_ty) es ->
      assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
      Forall (fun t => constraints_rooted base_ty rst_ty (snd t)) ts.
  Proof.
    intros G env base_ty rst_ty es.
    induction es as [|e es IH]; intros ts s s' Hall H.
    - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
        as (? & _ & ?); subst ts. constructor.
    - apply assign_lexps_carried_cons in H
        as (t & r & sa & Ht & Hr & ? & _); subst ts.
      inversion Hall as [|e0 es0 He Her]; subst.
      apply Forall_app. split; [exact (He t s sa Ht)|eapply IH; eauto].
  Qed.

  Lemma generate_ldef_constraint_rooted :
    forall G env base_ty rst_ty cenv x e cs s s',
      lexp_carried_rooted G env base_ty rst_ty e ->
      generate_ldef_constraint G env base_ty rst_ty cenv x e s = OK (cs, s') ->
      constraints_rooted base_ty rst_ty cs.
  Proof.
    intros G env base_ty rst_ty cenv x e cs s s' Hcar H.
    apply generate_ldef_constraint_inv in H
      as (ck & ckty & sa & rho & b & _ & Hcka & Ht & _ & ?); subst cs.
    apply constraints_rooted_cmerge. split.
    - constructor; [|constructor].
      exact (constraint_rooted_head env base_ty rst_ty ck ckty (sa, rho) [b]
               Hcka).
    - assert (Forall (fun t => constraints_rooted base_ty rst_ty (snd t))
                [(sa, rho)]) as Hr by exact (Hcar [(sa, rho)] s s' Ht).
      inversion Hr as [|t0 ts0 Ht0 _]; subst. exact Ht0.
  Qed.

  Lemma generate_lgen_constraint_rooted :
    forall G env base_ty rst_ty cenv xs es cs s s',
      Forall (lexp_carried_rooted G env base_ty rst_ty) es ->
      generate_lgen_constraint G env base_ty rst_ty cenv xs es s = OK (cs, s') ->
      constraints_rooted base_ty rst_ty cs.
  Proof.
    intros G env base_ty rst_ty cenv xs es cs s s' Hcar H.
    unfold generate_lgen_constraint in H.
    apply sec_bind_inv in H as (ts & s1 & Hts & H).
    apply sec_bind_inv in H as (bs & s2 & Hbs & Hlv).
    apply option_to_sec_inv in Hbs as (_ & ?); subst s2.
    eapply generate_lvars_constraints_rooted; [|exact Hlv].
    exact (assign_lexps_carried_rooted_of G env base_ty rst_ty es ts s s1
             Hcar Hts).
  Qed.

  Lemma generate_leqn_constraint_rooted_plain :
    forall G env base_ty rst_ty cenv xs es cs s s',
      Forall (fun e => match e with
                       | Eapp _ _ _ _ => False | _ => True end) es ->
      Forall (lexp_carried_rooted G env base_ty rst_ty) es ->
      generate_leqn_constraint G env base_ty rst_ty cenv (xs, es) s
        = OK (cs, s') ->
      constraints_rooted base_ty rst_ty cs.
  Proof.
    intros G env base_ty rst_ty cenv xs es cs s s' Hne Hcar H.
    destruct es as [|e [|e2 es2]].
    - eapply generate_lgen_constraint_rooted; [exact Hcar|exact H].
    - inversion Hne as [|e0 es0 Hnee _]; subst.
      inversion Hcar as [|e3 es3 Hcare _]; subst.
      rewrite <- generate_lone_is_leqn in H.
      destruct xs as [|x [|x2 xs2]].
      + eapply generate_lgen_constraint_rooted; [exact Hcar|].
        destruct e; (exact H || contradiction).
      + eapply generate_ldef_constraint_rooted; [exact Hcare|].
        destruct e; (exact H || contradiction).
      + eapply generate_lgen_constraint_rooted; [exact Hcar|].
        destruct e; (exact H || contradiction).
    - rewrite gen_leqn_cons2, (has_lcall_false _ Hne) in H.
      eapply generate_lgen_constraint_rooted; [exact Hcar|exact H].
  Qed.

  (** And through [simplify].  The same [keep] discipline as for closure: what
      elimination removes is never the base name or the reset, because those
      are kept. *)
  Lemma subAll_rooted :
    forall base_ty rst_ty keep cns d st',
      In base_ty keep ->
      In rst_ty keep ->
      ~ In d keep ->
      (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep) ->
      constraints_rooted base_ty rst_ty cns ->
      constraints_rooted base_ty rst_ty (subAll cns d st').
  Proof.
    intros base_ty rst_ty keep cns d st' Hbk Hrk Hd Htgt Hcns.
    induction cns as [|c cns IH]; [constructor|].
    inversion Hcns as [|c0 cns0 Hc Hcns']; subst.
    assert (forall c0, In c0 cns -> forall y, In y (snd c0) -> ~ In y keep)
      as Htgt' by (intros c0 Hin; apply Htgt; now right).
    destruct c as (st, tgt).
    destruct tgt as [|d' [|]]; simpl; try exact (IH Htgt' Hcns').
    destruct (ident_eqb d' d) eqn:Edd; [exact (IH Htgt' Hcns')|].
    constructor; [|exact (IH Htgt' Hcns')].
    assert (~ In d' keep) as Hd'
        by (apply (Htgt (st, [d'])); [now left|now left]).
    destruct Hc as (Hb & Hr). cbn [fst] in Hb, Hr |- *.
    (** a kept name survives the removal of the eliminated name and of the
        constraint's own target *)
    assert (forall y, In y keep -> In y st ->
                      In y (st_remove d' (SymTypes.subST st d st'))) as Hkeepin.
    { intros y Hy Hyst. apply st_remove_preserves_other_in;
        [intro; subst y; contradiction|].
      destruct (subST_cases st d st') as [E|[E|E]]; rewrite E;
        [exact Hyst
        |apply in_merge_left; apply st_remove_preserves_other_in;
         [intro; subst y; contradiction|exact Hyst]
        |apply in_merge_left; apply st_remove_preserves_other_in;
         [intro; subst y; contradiction|exact Hyst]]. }
    split; [exact (Hkeepin base_ty Hbk Hb)|exact (Hkeepin rst_ty Hrk Hr)].
  Qed.

  Lemma simplify_rooted :
    forall base_ty rst_ty keep ds cns,
      In base_ty keep ->
      In rst_ty keep ->
      (forall d, In d ds -> ~ In d keep) ->
      (forall c, In c cns -> forall y, In y (snd c) -> ~ In y keep) ->
      constraints_rooted base_ty rst_ty cns ->
      constraints_rooted base_ty rst_ty (simplify cns ds).
  Proof.
    intros base_ty rst_ty keep ds.
    induction ds as [|d ds IH]; intros cns Hbk Hrk Hds Htgt Hcns;
      [exact Hcns|].
    simpl. destruct (SymTypes.findST cns d) as [st'|] eqn:Ef.
    - apply IH;
        [exact Hbk|exact Hrk|intros d0 Hd0; apply Hds; now right| |].
      + exact (subAll_targets keep cns d st' Htgt).
      + apply (subAll_rooted base_ty rst_ty keep cns d st' Hbk Hrk);
          [apply Hds; now left|exact Htgt|exact Hcns].
    - apply IH; [exact Hbk|exact Hrk|intros d0 Hd0; apply Hds; now right
                |exact Htgt|exact Hcns].
  Qed.

  (** A clock type is built from the base name and the security names of the
      clock's variables, and nothing else.  That is what makes a callee's
      interface names absent from any caller clock type -- the fact the closure
      call rule needs in order to know that substitution's removals never touch
      a closure obligation. *)
  Lemma assign_clk_type_members :
    forall env base_ty ck ckty,
      assign_clk_type env base_ty ck = Some ckty ->
      forall z, In z ckty ->
        z = base_ty \/ exists x, Env.find x env = Some z.
  Proof.
    intros env base_ty ck. induction ck as [|ck0 IH x b]; intros ckty H z Hz.
    - simpl in H. apply option_Some_inj in H. subst ckty.
      destruct Hz as [Hz|[]]. left. now symmetry.
    - apply assign_clk_type_Con_inv in H
        as (ckty0 & g & Hck0 & Hg & ?); subst ckty.
      apply in_merge_inv in Hz as [Hz|Hz]; [exact (IH ckty0 Hck0 z Hz)|].
      destruct Hz as [Hz|[]]. subst z. right. now exists x.
  Qed.

  (** * [preserves_on] survives elimination on both sides

      The node level publishes [simplify cs (locals ++ minted st0 st1)], not
      [cs], and the two sides eliminate *different* sets -- the target has more
      locals, and its run minted more names.  The entailment still transfers,
      and in three moves: come back through the source's elimination, cross with
      the equation-level theorem, then go forward through the target's.

      Both directions are already available -- [simplifyRel_complete] backwards
      and [simplify_is_correct] forwards -- so the only side condition is the
      one that makes the backward move sound: what the source eliminates is
      outside the scope the entailment is stated on.  That is exactly what
      [generate_lnode_sig] arranges, since it eliminates the locals and the
      minted names and the scope is the interface. *)

  (** [collapse] is precision-neutral on *both* sides.  [SecTypes.v] has the
      target half; the source half is the same two lines, and signature
      generation needs both -- it collapses before simplifying, so the pair
      of raw constraint sets a preservation result speaks about and the pair
      the signatures publish differ by a collapse on each side. *)
  Lemma preserves_on_collapse_l :
    forall scope c t,
      preserves_on scope c t ->
      preserves_on scope (SymTypes.collapse c) t.
  Proof.
    intros scope c t Hp dlt Hsat.
    exact (Hp dlt (proj1 (collapse_satisfaction dlt c) Hsat)).
  Qed.

  Corollary preserves_on_collapse2 :
    forall scope c t,
      preserves_on scope c t ->
      preserves_on scope (SymTypes.collapse c) (SymTypes.collapse t).
  Proof.
    intros scope c t Hp.
    apply preserves_on_collapse, preserves_on_collapse_l, Hp.
  Qed.

  Lemma preserves_on_simplify :
    forall scope ce cet Ds Ds',
      wf_constraints ce ->
      (forall x, In x Ds -> ~ In x scope) ->
      preserves_on scope ce cet ->
      preserves_on scope (simplify ce Ds) (simplify cet Ds').
  Proof.
    intros scope ce cet Ds Ds' Hwf Hdisj Hpres dlt Hsat.
    (** back through the source's elimination *)
    destruct (simplifyRel_complete ce Ds (simplify ce Ds) scope dlt Hwf
                (simplify_simplifyRel Ds ce (simplify ce Ds)
                   (@Coq.Init.Logic.eq_refl _ (simplify ce Ds)))
                Hdisj Hsat) as (dlt1 & Hag1 & Hsat1).
    (** across, by the equation-level theorem *)
    destruct (Hpres dlt1 Hsat1) as (dlt2 & Hag2 & Hsat2).
    (** and forward through the target's *)
    exists dlt2. split.
    - intros x Hx. rewrite (Hag1 x Hx). exact (Hag2 x Hx).
    - exact (simplify_is_correct dlt2 cet (simplify cet Ds') Ds' Hsat2
               (simplify_simplifyRel Ds' cet (simplify cet Ds')
                  (@Coq.Init.Logic.eq_refl _ (simplify cet Ds')))).
  Qed.

End SecLusUnnestingBase.
