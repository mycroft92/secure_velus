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
From Velus Require Import SIF.SecLusUnnestingExpr.

Module SecLusUnnestingCalls
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
  (Import UNN     : UNNESTING Ids Op OpAux LSyn)
.

Module EXPR := SecLusUnnestingExpr Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include EXPR.

Import SECMONADNotations.
Import UNN.Fresh.Tactics.

  Section Preservation.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable vars    : list (ident * clock).
    Variable cenv    : Env.t (type * clock).
    Variable scope   : list ident.
    Variable stLo     : sec_state.
    Variable stF     : sec_state.
    Variable amb     : ST.

    Hypothesis env_inj : env_injective env.
    Hypothesis amb_scoped : st_scoped scope amb.
    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.
    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).
    Hypothesis source_types_scoped :
      source_types_scoped_upto GL env base_ty rst_ty vars scope stLo stF.
    Hypothesis source_lexps_scoped :
      source_lexps_scoped_upto GL env base_ty rst_ty vars scope stLo stF.
    Hypothesis rst_ty_scoped : In rst_ty scope.
    Hypothesis clk_types_scoped :
      forall P es ck ckty,
        wc_global P ->
        Forall (wc_exp P vars) es ->
        (clk_src vars es ck \/
         exists x, In x (List.map fst vars) /\ find_clock cenv x = OK ck) ->
        assign_clk_type env base_ty ck = Some ckty -> st_scoped scope ckty.
    Hypothesis env_range_scoped :
      forall x b, In x (List.map fst vars) ->
                  Env.find x env = Some b -> In b scope.
    Hypothesis source_lexps_carried_scoped :
      source_lexps_carried_scoped_upto GL env base_ty rst_ty vars scope stLo stF.
    Hypothesis sig_scoped :
      forall f sg, find_signature f GL = Some sg -> signature_scoped sg.
    Hypothesis sig_actuals_fresh :
      forall f sg inp ck rst os cns sa sb,
        find_signature f GL = Some sg ->
        Forall (caller_st env scope) inp ->
        caller_st env scope ck ->
        caller_st env scope rst ->
        Forall (caller_name env scope) os ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    Local Notation sec_of := (EXPR.sec_of env).
    Local Notation moved_by := (EXPR.moved_by env).
    Local Notation carries_at :=
      (EXPR.carries_at GL env base_ty rst_ty vars cenv scope stLo stF amb).
    Local Notation carries :=
      (EXPR.carries GL env base_ty rst_ty vars cenv scope stLo stF amb).
    Local Notation carries_list :=
      (EXPR.carries_list GL env base_ty rst_ty vars cenv scope stLo stF amb).
    Local Notation lifted_defs_local :=
      (EXPR.lifted_defs GL env base_ty rst_ty cenv amb env_inj).
    Local Notation carries_list_intro_local :=
      (EXPR.carries_list_intro GL env base_ty rst_ty vars cenv scope stLo stF amb
         env_inj amb_scoped).
    Local Notation sig_nodup_pipeline_local :=
      (EXPR.sig_nodup_pipeline GL sig_nodup).
    Local Notation assign_lexps_elementwise_local :=
      (EXPR.assign_lexps_elementwise GL env base_ty rst_ty).
    Local Notation unnest_fby_types_local :=
      (EXPR.unnest_fby_types GL env base_ty rst_ty).
    Local Notation unnest_arrow_types_local :=
      (EXPR.unnest_arrow_types GL env base_ty rst_ty).

    Local Lemma moved_by_prefix_local :
      forall st st1 st', st_follows st1 st' ->
        incl (moved_by st st1) (moved_by st st').
    Proof. apply EXPR.moved_by_prefix. Qed.

    Local Lemma moved_by_suffix_local :
      forall st st1 st', st_follows st st1 ->
        incl (moved_by st1 st') (moved_by st st').
    Proof. apply EXPR.moved_by_suffix. Qed.

    Local Lemma moved_by_disjoint_local :
      forall sta stb stc x,
        In x (moved_by sta stb) -> ~ In x (moved_by stb stc).
    Proof. intros. eapply EXPR.moved_by_disjoint; eauto. Qed.

    (** * Instantiation is monotone in the actual arguments -- semantically

        The call case needs this and [SIFSignature.v]'s
        [generate_constraints_mono_inp] does not supply it: that one is
        *syntactic*, asking that every name of one actual occur in the other
        and concluding [constraints_src_le].  It was written for the
        Stc-to-Obc bridge, where the compiled arguments literally drop the
        [when] guards the source arguments carry, so inclusion holds on the
        nose.  Unnesting gives no such inclusion -- the two sides' argument
        types are related by domination under a valuation, and by nothing
        syntactic at all.

        The semantic form needs a side condition the syntactic one did not.
        Substitution removes the formal from both the body and the actual
        ([st_remove x ty ⊔ st_remove x v]), and while [st_remove] preserves
        set inclusion, it does *not* preserve domination: dropping a name can
        shrink the larger side below the smaller.  What rescues it is that the
        formal is a callee name and the actual is built from caller names, so
        the removal is vacuous on the actual.  That disjointness is the extra
        premise, and it is exactly what the call-site freshness lemmas
        already establish elsewhere in the development. *)

    Lemma subst_ident_in_type_mono_sem :
      forall dlt ty x v1 v2,
        ~ In x v1 -> ~ In x v2 ->
        satisfiable dlt v2 v1 ->
        satisfiable dlt (SIG.subst_ident_in_type ty x v2)
          (SIG.subst_ident_in_type ty x v1).
    Proof.
      intros dlt ty x v1 v2 Hn1 Hn2 Hdom.
      unfold SIG.subst_ident_in_type.
      destruct (SymTypes.my_set_mem x ty) eqn:Hmem; [|apply satisfiable_refl].
      rewrite (SymTypes.st_remove_notin x v1),
        (SymTypes.st_remove_notin x v2).
      2:{ destruct (SymTypes.my_set_mem x v2) eqn:E; [|reflexivity].
          exfalso. apply Hn2. now apply SymTypes.my_set_mem_correct. }
      2:{ destruct (SymTypes.my_set_mem x v1) eqn:E; [|reflexivity].
          exfalso. apply Hn1. now apply SymTypes.my_set_mem_correct. }
      unfold satisfiable. rewrite !hm_ext_merge_eq.
      apply Lat.join_least_upper_bound.
      - apply Lat.join_bound1.
      - eapply Lat.order_trans; [exact Hdom|apply Lat.join_bound2].
    Qed.

    (** The relation the chain carries: same targets, dominated sources,
        pointwise.  The substitutions are all [mmap]s, so they preserve order
        and length and a pointwise relation is enough -- unlike the syntactic
        chain, which has to work with an unordered set inclusion because its
        final lookup pass reorders. *)

    (** * The call chain, at the level of membership

        The decomposition the chain has to carry is structural, but it does
        not have to be *syntactic*.  Writing it as an equation
        [fst c = F ⊔ V] would need [st_remove] to distribute over [merge] on
        the nose, which is awkward: [st_remove] is a plain list filter and
        [merge] a sorted union, so such an equation holds only up to
        sortedness, and sortedness would then have to be threaded everywhere.

        [hm_ext] depends on a type only through its members, so the chain can
        be run at the level of membership instead and domination recovered at
        each use.  Nothing below needs a syntactic equality between the two
        sides, which is what makes the substitution steps tractable: each one
        only has to say which names survive it. *)

    Definition remove_all (R : list ident) (s : ST) : ST :=
      fold_right (fun x t => SymTypes.st_remove x t) s R.

    Lemma remove_all_In :
      forall R s z, In z (remove_all R s) <-> In z s /\ ~ In z R.
    Proof.
      induction R as [|x R IH]; intros s z; simpl.
      - split; [intros Hz; split; auto|intros (Hz & _); auto].
      - split.
        + intros Hin. apply SymTypes.st_remove_in_inv in Hin as (Hin & Hne).
          apply IH in Hin as (Hin & HnR). split; auto.
          intros [Heq|HR]; [now apply Hne|now apply HnR].
        + intros (Hs & Hn).
          apply SymTypes.st_remove_preserves_other_in.
          * intro; subst; apply Hn; now left.
          * apply IH. split; [exact Hs|intro; apply Hn; now right].
    Qed.

    Lemma satisfiable_of_members :
      forall dlt a b,
        (forall z, In z a -> In z b) -> satisfiable dlt a b.
    Proof. intros. unfold satisfiable. now apply hm_ext_incl. Qed.

    (** A type whose names all come from one of two others is bounded by
        their join, and conversely.  These are the two directions the
        substitution steps need: one to push a substituted body into the
        shape the hypothesis is stated in, one to pull the result back out. *)

    Lemma hm_ext_union_le :
      forall dlt s a b,
        (forall z, In z s -> In z a \/ In z b) ->
        Lat.order (hm_ext dlt s) (Lat.join (hm_ext dlt a) (hm_ext dlt b)).
    Proof.
      intros dlt s a b Hs. apply hm_ext_bound_from_members.
      intros z Hz. apply Hs in Hz as [Hz|Hz].
      - eapply Lat.order_trans; [apply hm_ext_list_in1; exact Hz|].
        apply Lat.join_bound1.
      - eapply Lat.order_trans; [apply hm_ext_list_in1; exact Hz|].
        apply Lat.join_bound2.
    Qed.

    Lemma hm_ext_union_ge :
      forall dlt s a b,
        (forall z, In z a -> In z s) ->
        (forall z, In z b -> In z s) ->
        Lat.order (Lat.join (hm_ext dlt a) (hm_ext dlt b)) (hm_ext dlt s).
    Proof.
      intros dlt s a b Ha Hb.
      apply Lat.join_least_upper_bound; apply hm_ext_incl; auto.
    Qed.

    (** What a substitution leaves behind, as a membership fact.  The formal
        is dropped from the body, and the actual replaces it whole -- the
        actual's own copy of the formal is removed too, but the freshness
        premise makes that vacuous. *)

    Lemma subst_ident_in_type_In :
      forall ty x v z,
        In x ty -> ~ In x v ->
        (In z (SIG.subst_ident_in_type ty x v)
         <-> ((In z ty /\ z <> x) \/ In z v)).
    Proof.
      intros ty x v z Hx Hv.
      unfold SIG.subst_ident_in_type.
      destruct (SymTypes.my_set_mem x ty) eqn:Hmem.
      2:{ exfalso. apply SymTypes.my_set_mem_correct in Hx. congruence. }
      rewrite (SymTypes.st_remove_notin x v).
      2:{ destruct (SymTypes.my_set_mem x v) eqn:E; [|reflexivity].
          exfalso. apply Hv. now apply SymTypes.my_set_mem_correct. }
      split.
      - intros Hin. apply in_merge_inv in Hin as [Hin|Hin]; [left|now right].
        now apply SymTypes.st_remove_in_inv in Hin.
      - intros [(Hin & Hne)|Hin].
        + apply in_merge_left.
          now apply SymTypes.st_remove_preserves_other_in.
        + now apply in_merge_right.
    Qed.

    (** * What the input map leaves behind

        Substituting the formals one at a time is a fold, but its *result* has
        a flat description: the source of a substituted constraint holds
        exactly the names the original held that are not formals, together
        with the actuals of every formal the original mentioned.  Stating it
        this way avoids reasoning about the fold's intermediate states, which
        is where two earlier attempts at the call case came apart.

        The freshness premise -- no actual mentions a formal -- is what makes
        the description stable: substituting one formal neither creates nor
        destroys an occurrence of another. *)

    Lemma subst_ident_in_constraints_members :
      forall cs x v d sa sa',
        ~ In x v ->
        SIG.subst_ident_in_constraints cs x v sa = OK (d, sa') ->
        Forall2
          (fun c c' =>
             snd c' = snd c
             /\ forall z,
                  In z (fst c') <->
                  ((In z (fst c) /\ z <> x)
                   \/ (In x (fst c) /\ In z v)))
          cs d.
    Proof.
      intros cs x v. unfold SIG.subst_ident_in_constraints.
      induction cs as [|c cs IH]; intros d sa sa' Hxv H.
      - simpl in H. unfold SC.ret in H. inv H. constructor.
      - simpl in H.
        eapply sec_bind_inv in H as (c' & s1 & Hc' & H).
        eapply sec_bind_inv in H as (cs' & s2 & Hcs' & Hret).
        unfold SC.ret in Hret. inv Hret.
        constructor; [|exact (IH cs' _ _ Hxv Hcs')].
        destruct c as (ty & tg).
        unfold SIG.subst_inp_ident_in_constraint in Hc'.
        destruct tg as [|y [|]]; try discriminate Hc'.
        destruct (ident_eqb x y) eqn:Hxy; try discriminate Hc'.
        unfold SC.ret in Hc'. inv Hc'.
        simpl. split; [reflexivity|].
        destruct (in_dec ident_eq_dec x ty) as [Hin|Hnin].
        + intros z. rewrite (subst_ident_in_type_In ty x v z Hin Hxv).
          split.
          * intros [(Hz & Hne)|Hz]; [left; split; assumption
                                    |right; split; assumption].
          * intros [(Hz & Hne)|(_ & Hz)]; [left; split; assumption
                                          |right; exact Hz].
        + rewrite subst_ident_in_type_notin by exact Hnin.
          intros z. split.
          * intros Hz. left. split; [exact Hz|].
            intro; subst z; contradiction.
          * intros [(Hz & _)|(Hc & _)]; [exact Hz|contradiction].
    Qed.

    Lemma subst_constraints_inp_map_members :
      forall xs vs cs d sa sa',
        NoDup xs ->
        Forall (fun v => forall y, In y xs -> ~ In y v) vs ->
        SIG.subst_constraints_inp_map cs xs vs sa = OK (d, sa') ->
        Forall2
          (fun c c' =>
             snd c' = snd c
             /\ forall z,
                  In z (fst c') <->
                  ((In z (fst c) /\ ~ In z xs)
                   \/ (exists y w, In (y, w) (combine xs vs)
                                   /\ In y (fst c) /\ In z w)))
          cs d.
    Proof.
      induction xs as [|x xs IH]; intros vs cs d sa sa' Hnd Hfr H.
      - destruct vs; simpl in H; [|discriminate].
        unfold SC.ret in H. inv H.
        clear. induction d as [|c cs IH]; constructor; [|exact IH].
        split; [reflexivity|]. intros z. split.
        + intros Hz. left. split; [exact Hz|intros []].
        + intros [(Hz & _)|(y & w & Hyw & _)]; [exact Hz|inversion Hyw].
      - destruct vs as [|v vs]; simpl in H; [discriminate|].
        eapply sec_bind_inv in H as (d1 & s1 & Hd1 & H).
        inversion Hfr as [|v0 vs0 Hv Hvs]; subst.
        inversion Hnd as [|x0 xs0 Hxnin Hndr]; subst.
        assert (~ In x v) as Hxv by (apply Hv; now left).
        pose proof
          (subst_ident_in_constraints_members cs x v d1 _ _ Hxv Hd1)
          as Hstep.
        assert (Forall (fun w => forall y, In y xs -> ~ In y w) vs) as Hfr'.
        { eapply Forall_impl; [|exact Hvs].
          intros w Hw y Hy. apply Hw. now right. }
        pose proof (IH vs d1 d _ _ Hndr Hfr' H) as Hrest.

        (** the formals still to come are untouched by this substitution *)
        assert (forall (c c1 : SymTypes.constraint),
                   (forall z, In z (fst c1) <->
                              ((In z (fst c) /\ z <> x)
                               \/ (In x (fst c) /\ In z v))) ->
                   forall y, In y xs -> (In y (fst c1) <-> In y (fst c)))
          as Hkeep.
        { intros c c1 Hc1 y Hy. rewrite Hc1. split.
          - intros [(Hz & _)|(_ & Hz)]; [exact Hz|].
            exfalso. eapply (Hv y); [now right|exact Hz].
          - intros Hz. left. split; [exact Hz|].
            intro; subst y; contradiction. }

        (** and the two descriptions compose *)
        clear - Hstep Hrest Hkeep Hv Hxnin.
        revert d1 d Hstep Hrest.
        induction cs as [|c cs IHcs]; intros d1 d Hstep Hrest.
        + inversion Hstep; subst. inversion Hrest; subst. constructor.
        + inversion Hstep as [|c0 c1 cs0 d1r Hc1 Hstepr]; subst.
          inversion Hrest as [|c1' c' d1r' dr Hc' Hrestr]; subst.
          constructor; [|exact (IHcs d1r dr Hstepr Hrestr)].
          destruct Hc1 as (Ht1 & Hm1). destruct Hc' as (Ht2 & Hm2).
          split; [rewrite Ht2; exact Ht1|].
          intros z. rewrite Hm2, (Hm1 z).
          assert (forall y, In y xs -> (In y (fst c1) <-> In y (fst c)))
            as Hkc by (intros y Hy; exact (Hkeep c c1 Hm1 y Hy)).
          split.
          * intros [(Hz & Hnxs)|(y & w & Hyw & Hy & Hzw)].
            -- destruct Hz as [(Hz & Hne)|(Hx & Hzv)].
               ++ left. split; [exact Hz|].
                  intros [Heq|Hin]; [now apply Hne|now apply Hnxs].
               ++ right. exists x, v. split; [now left|].
                  split; [exact Hx|exact Hzv].
            -- assert (In y xs) as Hyxs by (eapply in_combine_l; exact Hyw).
               right. exists y, w. split; [now right|].
               split; [|exact Hzw]. exact (proj1 (Hkc y Hyxs) Hy).
          * intros [(Hz & Hnxs)|(y & w & Hyw & Hy & Hzw)].
            -- left. split.
               ++ left. split;
                    [exact Hz|intro; subst z; apply Hnxs; now left].
               ++ intro Hin. apply Hnxs. now right.
            -- destruct Hyw as [Heq|Hyw].
               ++ assert (y = x /\ w = v) as (Hy1 & Hw1)
                      by (split; congruence).
                  subst y w.
                  left. split.
                  ** right. split; [exact Hy|exact Hzw].
                  ** intro Hin. eapply (Hv z); [now right|exact Hzw].
               ++ assert (In y xs) as Hyxs by (eapply in_combine_l; exact Hyw).
                  right. exists y, w. split; [exact Hyw|].
                  split; [|exact Hzw]. exact (proj2 (Hkc y Hyxs) Hy).
    Qed.

    (** Positions line up, because [combine] pairs by position. *)

    Lemma combine_grow_r :
      forall (xs : list ident) (vs vs' : list ST),
        Forall2 (fun v v' => forall z, In z v -> In z v') vs vs' ->
        forall y w, In (y, w) (combine xs vs) ->
          exists w', In (y, w') (combine xs vs')
                     /\ (forall z, In z w -> In z w').
    Proof.
      intros xs vs vs' H. revert xs.
      induction H as [|v v' l l' Hv Hl IH]; intros xs y w Hin.
      - destruct xs; simpl in Hin; contradiction.
      - destruct xs as [|x xs]; simpl in Hin; [contradiction|].
        destruct Hin as [Heq|Hin].
        + assert (y = x /\ w = v) as (? & ?) by (split; congruence); subst.
          exists v'. split; [now left|exact Hv].
        + destruct (IH xs y w Hin) as (w' & Hin' & Hsub).
          exists w'. split; [now right|exact Hsub].
    Qed.

    Lemma combine_grow_l :
      forall (xs : list ident) (vs vs' : list ST),
        Forall2 (fun v v' => forall z, In z v -> In z v') vs vs' ->
        forall y w', In (y, w') (combine xs vs') ->
          exists w, In (y, w) (combine xs vs)
                    /\ (forall z, In z w -> In z w').
    Proof.
      intros xs vs vs' H. revert xs.
      induction H as [|v v' l l' Hv Hl IH]; intros xs y w' Hin.
      - destruct xs; simpl in Hin; contradiction.
      - destruct xs as [|x xs]; simpl in Hin; [contradiction|].
        destruct Hin as [Heq|Hin].
        + assert (y = x /\ w' = v') as (? & ?) by (split; congruence); subst.
          exists v. split; [now left|exact Hv].
        + destruct (IH xs y w' Hin) as (w & Hin' & Hsub).
          exists w. split; [now right|exact Hsub].
    Qed.

    (** * Augmenting the actuals changes nothing

        If every name an argument's type gains is one that some *other*
        argument the constraint already mentions contributes, then
        instantiating the signature with the larger types produces
        constraints with exactly the same members -- and so, by
        [listSatisfiable_same_sources], exactly the same obligations.

        This is what the call case needs.  Each argument's ambient is the
        call's base ambient joined with the security names of its own clock
        variables; those variables are other arguments of the same call, and
        the dependency property says a constraint mentioning the argument
        mentions them too.  Augmenting by them therefore costs nothing, and
        it is what makes the single ambient of
        [generate_constraints_mono_sem] large enough for every argument
        without being too large for any result. *)

    (** * The last premise of the augmentation argument, discharged

        [subst_constraints_inp_map_augment] above leaves exactly one premise:
        that augmenting an actual with the security names of the clock it runs
        on adds nothing the constraint's source did not already reach through
        *some* formal.  This is where that is discharged.

        The invariant it rests on is the dependency property itself, read at
        the callee and restricted to its inputs: a constraint of the callee's
        signature whose source mentions formal input [x] also mentions the
        formals of [x]'s declared clock.  So the property is inductive over the
        call graph, and the [keep] set of the [simplify] transport -- the base
        name plus the inputs' security names -- is exactly what carries it into
        the published signature.

        Each node has its own naming, so the invariant is stated over the
        callee's inputs [ins] and its own [nm], never the caller's [env]. *)

    Definition sig_inputs_clock_closed
        (sg : signature) (ins : list (ident * clock))
        (nm : ident -> option ident) : Prop :=
      forall c, In c (s_constraints sg) ->
      forall x ck y,
        In (x, ck) ins -> nm x = Some y -> In y (fst c) ->
        forall x' y', In x' (clock_vars ck) -> nm x' = Some y' -> In y' (fst c).

    (** The invariant is monotone in the declared list: stating it over the
        whole interface is *stronger* than over the inputs alone, and the
        augmentation argument only needs the inputs.  That matters because the
        closure call rule needs the outputs too -- a callee constraint's source
        may mention another output formal, whose actual is one of the caller's
        defined variables, and then *its* clock type has to be accounted for. *)
    Lemma sig_inputs_clock_closed_incl :
      forall sg ins1 ins2 nm,
        incl ins1 ins2 ->
        sig_inputs_clock_closed sg ins2 nm ->
        sig_inputs_clock_closed sg ins1 nm.
    Proof.
      intros sg ins1 ins2 nm Hincl H c Hc x ck y Hin Hnm Hy x' y' Hx' Hnm'.
      exact (H c Hc x ck y (Hincl (x, ck) Hin) Hnm Hy x' y' Hx' Hnm').
    Qed.

    (** The four lists of a call, matched by position, and what each one
        contributes.  [augs] is the augmented actuals; the hypothesis on it
        says only that what it adds are clock names of *its own* formal's
        clock, which is what [assign_clk_type_instck] delivers. *)
    Lemma call_augment_dep :
      forall (bad : ident -> Prop) (sg : signature) (ins : list (ident * clock))
             (nm sub : ident -> option ident) (ncks : list nclock)
             (argts augs : list SymTypes.ST) (c : SymTypes.constraint),
        List.length ins = List.length (s_in sg) ->
        List.length ins = List.length ncks ->
        List.length ins = List.length argts ->
        sig_inputs_clock_closed sg ins nm ->
        (** the callee's naming agrees with its signature's input list *)
        (forall i x ck y,
            nth_error ins i = Some (x, ck) ->
            nth_error (s_in sg) i = Some y -> nm x = Some y) ->
        (** [WellInstantiated]: the formal's image is the actual's stream name *)
        (forall i x ck nck,
            nth_error ins i = Some (x, ck) ->
            nth_error ncks i = Some nck -> sub x = snd nck) ->
        (** a named actual stream carries its own name, unless it is one of
            the [bad] names *)
        (forall i nck w u g,
            nth_error ncks i = Some nck -> nth_error argts i = Some w ->
            snd nck = Some u -> ~ bad u -> Env.find u env = Some g -> In g w) ->
        (** and no variable of a formal's clock is sent to a [bad] name *)
        (forall i x ck x' u,
            nth_error ins i = Some (x, ck) -> In x' (clock_vars ck) ->
            sub x' = Some u -> ~ bad u) ->
        (** the augmentation adds only clock names of its own formal's clock *)
        (forall i x ck w w' z,
            nth_error ins i = Some (x, ck) -> nth_error argts i = Some w ->
            nth_error augs i = Some w' -> In z w' ->
            In z w
            \/ exists x' u, In x' (clock_vars ck)
                            /\ sub x' = Some u
                            /\ Env.find u env = Some z) ->
        (** every variable of a formal's clock is itself a formal *)
        (forall i x ck x',
            nth_error ins i = Some (x, ck) -> In x' (clock_vars ck) ->
            exists ck', In (x', ck') ins) ->
        In c (s_constraints sg) ->
        forall y w', In (y, w') (combine (s_in sg) augs) -> In y (fst c) ->
          forall z, In z w' ->
            exists y2 w2, In (y2, w2) (combine (s_in sg) argts)
                          /\ In y2 (fst c) /\ In z w2.
    Proof.
      intros bad sg ins nm sub ncks argts augs c Hl1 Hl2 Hl3 Hinv
        Hnm Hwi Hnamed Hbadok Haug Hformal Hc y w' Hyw Hy z Hz.
      apply In_combine_nth_error in Hyw as (i & Hyi & Hwi').
      (** the slot this name came from *)
      assert (exists x ck, nth_error ins i = Some (x, ck)) as (x & ck & Hxi).
      { assert (i < List.length ins)%nat as Hlt
            by (rewrite Hl1; exact (nth_error_lt_inv (s_in sg) i y Hyi)).
        destruct (nth_error_lt ins i Hlt) as ((x & ck) & Hxi).
        now exists x, ck. }
      assert (exists w, nth_error argts i = Some w) as (w & Hwi0).
      { apply nth_error_lt. rewrite <- Hl3.
        exact (nth_error_lt_inv ins i (x, ck) Hxi). }
      destruct (Haug i x ck w w' z Hxi Hwi0 Hwi' Hz)
        as [Hzw|(x' & u & Hx' & Hsub & Hu)].
      - (** already in the actual: the formal itself will do *)
        exists y, w. split; [exact (nth_error_In_combine (s_in sg) argts i y w Hyi Hwi0)|].
        split; [exact Hy|exact Hzw].
      - (** a clock name: the formal of that clock variable will do *)
        destruct (Hformal i x ck x' Hxi Hx') as (ck2 & Hin2).
        apply In_nth_error in Hin2 as (j & Hxj).
        assert (exists y2, nth_error (s_in sg) j = Some y2) as (y2 & Hyj).
        { apply nth_error_lt. rewrite <- Hl1.
          exact (nth_error_lt_inv ins j (x', ck2) Hxj). }
        assert (exists nck2, nth_error ncks j = Some nck2) as (nck2 & Hnj).
        { apply nth_error_lt. rewrite <- Hl2.
          exact (nth_error_lt_inv ins j (x', ck2) Hxj). }
        assert (exists w2, nth_error argts j = Some w2) as (w2 & Hwj).
        { apply nth_error_lt. rewrite <- Hl3.
          exact (nth_error_lt_inv ins j (x', ck2) Hxj). }
        exists y2, w2.
        split;
          [exact (nth_error_In_combine (s_in sg) argts j y2 w2 Hyj Hwj)|].
        split.
        + (** here the invariant is used: the source reaches that formal too *)
          assert (In (x, ck) ins) as Hinx
              by exact (nth_error_In ins i Hxi).
          exact (Hinv c Hc x ck y Hinx (Hnm i x ck y Hxi Hyi) Hy x' y2 Hx'
                   (Hnm j x' ck2 y2 Hxj Hyj)).
        + (** and the actual at that slot carries the name *)
          assert (snd nck2 = Some u) as Hs2
              by (rewrite <- (Hwi j x' ck2 nck2 Hxj Hnj); exact Hsub).
          exact (Hnamed j nck2 w2 u z Hnj Hwj Hs2
                   (Hbadok i x ck x' u Hxi Hx' Hsub) Hu).
    Qed.

    (** * Substitution succeeds or fails for reasons that do not mention the
          actuals

        [subst_inp_ident_in_constraint] fails on exactly two things: a
        malformed constraint, and a formal that is also the constraint's
        target.  Neither mentions the type being substituted in.  So a
        successful run with one set of actuals gives a successful run with any
        other of the same length -- which is what lets the augmented
        instantiation be *built* from the plain one rather than assumed.

        The statement has to be generalised over target-equal lists, because
        the fold substitutes into the list the previous step produced, and that
        list differs between the two runs.  What does *not* differ is the
        targets, which is exactly the data success depends on. *)

    Lemma subst_ident_in_constraints_targets :
      forall cs x v d sa sa',
        SIG.subst_ident_in_constraints cs x v sa = OK (d, sa') ->
        List.map snd d = List.map snd cs.
    Proof.
      intros cs x v. revert x v.
      induction cs as [|c cs IH]; intros x v d sa sa' H.
      - unfold SIG.subst_ident_in_constraints in H. simpl in H.
        unfold SC.ret in H.
        assert (d = []) as ? by (inversion H; reflexivity); subst d. reflexivity.
      - unfold SIG.subst_ident_in_constraints in H. simpl in H.
        apply sec_bind_inv in H as (c1 & s1 & Hc1 & H).
        apply sec_bind_inv in H as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        assert (d = c1 :: cr) as ? by (inversion Hret; reflexivity); subst d.
        simpl. f_equal.
        + unfold SIG.subst_inp_ident_in_constraint in Hc1.
          destruct c as (ty & tgt).
          destruct tgt as [|x0 [|]]; try discriminate Hc1.
          destruct (ident_eqb x x0) eqn:Ex; [discriminate Hc1|].
          unfold SC.ret in Hc1. inversion Hc1; subst. reflexivity.
        + exact (IH x v cr s1 s2 Hcr).
    Qed.

    Lemma subst_ident_in_constraints_total :
      forall cs1 cs2 x v v' d sa sa' sb,
        List.map snd cs1 = List.map snd cs2 ->
        SIG.subst_ident_in_constraints cs1 x v sa = OK (d, sa') ->
        exists d', SIG.subst_ident_in_constraints cs2 x v' sb = OK (d', sb).
    Proof.
      intros cs1. induction cs1 as [|c cs1 IH];
        intros cs2 x v v' d sa sa' sb Ht H.
      - destruct cs2; [|discriminate Ht].
        exists []. apply mmap_nil_ok.
      - destruct cs2 as [|c2 cs2]; [discriminate Ht|].
        simpl in Ht. injection Ht as Htc Htr.
        unfold SIG.subst_ident_in_constraints in H. simpl in H.
        apply sec_bind_inv in H as (c1 & s1 & Hc1 & H).
        apply sec_bind_inv in H as (cr & s2 & Hcr & _).
        assert (exists c1', SIG.subst_inp_ident_in_constraint c2 x v' sb
                            = OK (c1', sb)) as (c1' & Hc1').
        { unfold SIG.subst_inp_ident_in_constraint in Hc1 |- *.
          destruct c as (ty & tgt). destruct c2 as (ty2 & tgt2).
          cbn [snd] in Htc. subst tgt2.
          destruct tgt as [|x0 [|]]; try discriminate Hc1.
          destruct (ident_eqb x x0) eqn:Ex; [discriminate Hc1|].
          eexists. reflexivity. }
        destruct (IH cs2 x v v' cr s1 s2 sb Htr Hcr) as (cr' & Hcr').
        exists (c1' :: cr').
        exact (mmap_cons_ok _ c2 cs2 sb c1' sb cr' sb Hc1' Hcr').
    Qed.

    Lemma subst_constraints_inp_map_targets :
      forall xs cs vs d sa sa',
        SIG.subst_constraints_inp_map cs xs vs sa = OK (d, sa') ->
        List.map snd d = List.map snd cs.
    Proof.
      intros xs. induction xs as [|x xs IH]; intros cs vs d sa sa' H.
      - destruct vs; [|simpl in H; discriminate].
        simpl in H. unfold SC.ret in H.
        assert (d = cs) as ? by (inversion H; reflexivity); subst d.
        reflexivity.
      - destruct vs as [|v vs]; [simpl in H; discriminate|].
        simpl in H.
        apply sec_bind_inv in H as (d1 & s1 & Hd1 & H).
        rewrite (IH d1 vs d s1 sa' H).
        exact (subst_ident_in_constraints_targets cs x v d1 sa s1 Hd1).
    Qed.

    Lemma subst_constraints_inp_map_total :
      forall xs cs1 cs2 vs vs' d sa sa' sb,
        List.length vs = List.length vs' ->
        List.map snd cs1 = List.map snd cs2 ->
        SIG.subst_constraints_inp_map cs1 xs vs sa = OK (d, sa') ->
        exists d', SIG.subst_constraints_inp_map cs2 xs vs' sb = OK (d', sb).
    Proof.
      intros xs. induction xs as [|x xs IH];
        intros cs1 cs2 vs vs' d sa sa' sb Hl Ht H.
      - destruct vs; [|simpl in H; discriminate].
        destruct vs'; [|simpl in Hl; discriminate].
        exists cs2. reflexivity.
      - destruct vs as [|v vs]; [simpl in H; discriminate|].
        destruct vs' as [|v' vs']; [simpl in Hl; discriminate|].
        simpl in H.
        apply sec_bind_inv in H as (d1 & s1 & Hd1 & H).
        destruct (subst_ident_in_constraints_total cs1 cs2 x v v' d1 sa s1 sb
                    Ht Hd1) as (d1' & Hd1').
        assert (List.map snd d1 = List.map snd d1') as Ht'.
        { rewrite (subst_ident_in_constraints_targets cs1 x v d1 sa s1 Hd1).
          rewrite (subst_ident_in_constraints_targets cs2 x v' d1' sb sb Hd1').
          exact Ht. }
        destruct (IH d1 d1' vs vs' d s1 sa' sb (f_equal Nat.pred Hl) Ht' H)
          as (d' & Hd').
        exists d'. simpl. unfold SC.bind. rewrite Hd1'. exact Hd'.
    Qed.

    (** [findST] looks a constraint up by its target, so whether it finds
        anything depends on the targets alone. *)
    Lemma findST_targets_some :
      forall cs1 cs2 v,
        List.map snd cs1 = List.map snd cs2 ->
        (exists t1, SymTypes.findST cs1 v = Some t1) ->
        exists t2, SymTypes.findST cs2 v = Some t2.
    Proof.
      induction cs1 as [|c1 cs1 IH]; intros cs2 v Ht (t1 & H1).
      - simpl in H1. discriminate.
      - destruct cs2 as [|c2 cs2]; [discriminate Ht|].
        simpl in Ht. injection Ht as Htc Htr.
        destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
        cbn [snd] in Htc. subst tg2.
        simpl in H1 |- *.
        destruct tg1 as [|d [|]];
          [exact (IH cs2 v Htr (ex_intro _ t1 H1))| |
           exact (IH cs2 v Htr (ex_intro _ t1 H1))].
        destruct (ident_eqb d v) eqn:E; [now exists s2|].
        exact (IH cs2 v Htr (ex_intro _ t1 H1)).
    Qed.

    Lemma findST_targets_none :
      forall cs1 cs2 v,
        List.map snd cs1 = List.map snd cs2 ->
        SymTypes.findST cs1 v = None -> SymTypes.findST cs2 v = None.
    Proof.
      induction cs1 as [|c1 cs1 IH]; intros cs2 v Ht H1.
      - destruct cs2; [reflexivity|discriminate Ht].
      - destruct cs2 as [|c2 cs2]; [discriminate Ht|].
        simpl in Ht. injection Ht as Htc Htr.
        destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
        cbn [snd] in Htc. subst tg2.
        simpl in H1 |- *.
        destruct tg1 as [|d [|]]; [exact (IH cs2 v Htr H1)| |
                                   exact (IH cs2 v Htr H1)].
        destruct (ident_eqb d v) eqn:E; [discriminate H1|].
        exact (IH cs2 v Htr H1).
    Qed.

    (** The output substitution: it rewrites targets, but identically on
        target-equal lists, so both runs succeed together. *)
    Lemma subst_ident_constraints_total :
      forall cs1 cs2 x v d sa sa' sb,
        List.map snd cs1 = List.map snd cs2 ->
        SIG.subst_ident_constraints cs1 x v sa = OK (d, sa') ->
        exists d', SIG.subst_ident_constraints cs2 x v sb = OK (d', sb)
                   /\ List.map snd d' = List.map snd d.
    Proof.
      intros cs1. induction cs1 as [|c1 cs1 IH];
        intros cs2 x v d sa sa' sb Ht H.
      - destruct cs2; [|discriminate Ht].
        unfold SIG.subst_ident_constraints in H. simpl in H.
        unfold SC.ret in H.
        assert (d = []) as ? by (inversion H; reflexivity); subst d.
        exists []. split; [apply mmap_nil_ok|reflexivity].
      - destruct cs2 as [|c2 cs2]; [discriminate Ht|].
        simpl in Ht. injection Ht as Htc Htr.
        unfold SIG.subst_ident_constraints in H. simpl in H.
        apply sec_bind_inv in H as (h & s1 & Hh & H).
        apply sec_bind_inv in H as (r & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        assert (d = h :: r) as ? by (inversion Hret; reflexivity); subst d.
        destruct (IH cs2 x v r s1 s2 sb Htr Hr) as (r' & Hr' & Htr').
        assert (exists h', SIG.subst_ident_constraint c2 x v sb = OK (h', sb)
                           /\ snd h' = snd h) as (h' & Hh' & Hht).
        { unfold SIG.subst_ident_constraint in Hh |- *.
          destruct (ident_eqb x v) eqn:Exv; [discriminate Hh|].
          destruct c1 as (ty1 & tg1). destruct c2 as (ty2 & tg2).
          cbn [snd] in Htc. subst tg2.
          destruct tg1 as [|x0 [|]]; try discriminate Hh;
            destruct (ident_eqb x x0) eqn:Ex; unfold SC.ret in Hh;
              inversion Hh; subst;
              (eexists; split; [reflexivity|reflexivity]). }
        exists (h' :: r'). split.
        + exact (mmap_cons_ok _ c2 cs2 sb h' sb r' sb Hh' Hr').
        + simpl. now rewrite Hht, Htr'.
    Qed.

    Lemma subst_constraints_out_map_total :
      forall xs vs cs1 cs2 d sa sa' sb,
        List.map snd cs1 = List.map snd cs2 ->
        SIG.subst_constraints_out_map cs1 xs vs sa = OK (d, sa') ->
        exists d', SIG.subst_constraints_out_map cs2 xs vs sb = OK (d', sb)
                   /\ List.map snd d' = List.map snd d.
    Proof.
      intros xs. induction xs as [|x xs IH];
        intros vs cs1 cs2 d sa sa' sb Ht H.
      - destruct vs; [|simpl in H; discriminate].
        simpl in H. unfold SC.ret in H.
        assert (d = cs1) as ? by (inversion H; reflexivity); subst d.
        exists cs2. split; [reflexivity|now rewrite Ht].
      - destruct vs as [|v vs]; [simpl in H; discriminate|].
        simpl in H.
        destruct (SymTypes.findST cs1 v) as [t|] eqn:Ef;
          [exfalso; unfold SC.error in H; discriminate H|].
        apply sec_bind_inv in H as (c1' & s1 & Hc1' & H).
        destruct (subst_ident_constraints_total cs1 cs2 x v c1' sa s1 sb
                    Ht Hc1') as (c2' & Hc2' & Ht2).
        destruct (IH vs c1' c2' d s1 sa' sb
                    (@Coq.Init.Logic.eq_sym _ _ _ Ht2) H) as (d' & Hd' & Htd).
        exists d'. split; [|exact Htd].
        simpl. rewrite (findST_targets_none cs1 cs2 v Ht Ef).
        unfold SC.bind. rewrite Hc2'. exact Hd'.
    Qed.

    Lemma mmap_findST_total :
      forall (e1 e2 : list SymTypes.constraint) out r sa sa' sb,
        List.map snd e1 = List.map snd e2 ->
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e1 x))
                            (fun st => SC.ret (st, [x]))) out sa = OK (r, sa') ->
        exists r',
          SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e2 x))
                              (fun st => SC.ret (st, [x]))) out sb
          = OK (r', sb).
    Proof.
      intros e1 e2 out. induction out as [|x out IH]; intros r sa sa' sb Ht H.
      - exists []. apply mmap_nil_ok.
      - simpl in H.
        apply sec_bind_inv in H as (h & s1 & Hh & H).
        apply sec_bind_inv in H as (rr & s2 & Hrr & _).
        cbv beta in Hh.
        apply sec_bind_inv in Hh as (t & s3 & Ht3 & Hret).
        apply option_to_sec_inv in Ht3 as (Ht3 & ?); subst s3.
        destruct (findST_targets_some e1 e2 x Ht (ex_intro _ t Ht3))
          as (t2 & Ht2).
        destruct (IH rr s1 s2 sb Ht Hrr) as (rr' & Hrr').
        exists ((t2, [x]) :: rr').
        eapply mmap_cons_ok; [|exact Hrr'].
        eapply sec_bind_ok; [unfold option_to_sec; now rewrite Ht2|reflexivity].
    Qed.

    (** * Set-equality of sources survives substitution

        [subst_constraints_inp_map_augment] concludes exactly the relation
        [listSatisfiable_same_sources] consumes, but only for the input-map
        stage.  The satisfaction transfer needs it at the *end* of
        [generate_constraints], so it has to survive the clock, the reset, the
        outputs and the final lookup.

        It does, and for one reason: [subst_ident_in_type] reads its argument
        only through membership.  That is [subst_ident_in_type_In] when the
        name occurs and [subst_ident_in_type_notIn] when it does not. *)

    Lemma subst_ident_in_type_notIn :
      forall ty x v, ~ In x ty -> SIG.subst_ident_in_type ty x v = ty.
    Proof.
      intros ty x v Hx. unfold SIG.subst_ident_in_type.
      destruct (SymTypes.my_set_mem x ty) eqn:Hmem; [|reflexivity].
      exfalso. apply Hx. now apply SymTypes.my_set_mem_correct.
    Qed.

    Lemma subst_ident_in_type_same :
      forall ty1 ty2 x v,
        ~ In x v ->
        (forall z, In z ty1 <-> In z ty2) ->
        forall z, In z (SIG.subst_ident_in_type ty1 x v)
                  <-> In z (SIG.subst_ident_in_type ty2 x v).
    Proof.
      intros ty1 ty2 x v Hv Hsame z.
      destruct (in_dec ident_eq_dec x ty1) as [Hx1|Hx1].
      - assert (In x ty2) as Hx2 by (apply Hsame; exact Hx1).
        rewrite (subst_ident_in_type_In ty1 x v z Hx1 Hv).
        rewrite (subst_ident_in_type_In ty2 x v z Hx2 Hv).
        split; (intros [(Hz & Hne)|Hz]; [left; split; [|exact Hne]|now right]);
          [now apply Hsame|now apply Hsame].
      - assert (~ In x ty2) as Hx2 by (intro Hc; apply Hx1, Hsame; exact Hc).
        rewrite (subst_ident_in_type_notIn ty1 x v Hx1).
        rewrite (subst_ident_in_type_notIn ty2 x v Hx2).
        exact (Hsame z).
    Qed.

    (** Targets equal, sources equal as sets.  Stronger than what
        [listSatisfiable_same_sources] needs, and what every stage preserves. *)
    Definition cs_same_src (cs cs' : list SymTypes.constraint) : Prop :=
      Forall2 (fun c c' => snd c' = snd c
                           /\ (forall z, In z (fst c) <-> In z (fst c'))) cs cs'.

    Lemma cs_same_src_weaken :
      forall cs cs',
        cs_same_src cs cs' ->
        Forall2
          (fun c c' =>
             (forall z, In z (fst c) <-> In z (fst c'))
             /\ (forall z, In z (snd c) <-> In z (snd c'))) cs cs'.
    Proof.
      intros cs cs' H. induction H as [|c c' l l' (Ht & Hs) Hr IH];
        constructor; [|exact IH].
      destruct c as (sa1 & tg1). destruct c' as (sa2 & tg2).
      cbn [fst snd] in Ht, Hs |- *. subst tg2.
      split; [exact Hs|intro z; reflexivity].
    Qed.

    Lemma subst_ident_in_constraints_same :
      forall cs1 cs2 x v d1 d2 sa sa' sb sb',
        ~ In x v ->
        cs_same_src cs1 cs2 ->
        SIG.subst_ident_in_constraints cs1 x v sa = OK (d1, sa') ->
        SIG.subst_ident_in_constraints cs2 x v sb = OK (d2, sb') ->
        cs_same_src d1 d2.
    Proof.
      intros cs1 cs2 x v d1 d2 sa sa' sb sb' Hv Hsame.
      revert d1 d2 sa sa' sb sb'.
      induction Hsame as [|c1 c2 l1 l2 (Ht & Hs) Hr IH];
        intros d1 d2 sa sa' sb sb' H1 H2.
      - unfold SIG.subst_ident_in_constraints in H1, H2. simpl in H1, H2.
        unfold SC.ret in H1, H2.
        assert (d1 = []) as ? by (inversion H1; reflexivity); subst d1.
        assert (d2 = []) as ? by (inversion H2; reflexivity); subst d2.
        constructor.
      - unfold SIG.subst_ident_in_constraints in H1, H2. simpl in H1, H2.
        apply sec_bind_inv in H1 as (h1 & p1 & Hh1 & H1).
        apply sec_bind_inv in H1 as (r1 & q1 & Hr1 & Hret1).
        apply sec_bind_inv in H2 as (h2 & p2 & Hh2 & H2).
        apply sec_bind_inv in H2 as (r2 & q2 & Hr2 & Hret2).
        unfold SC.ret in Hret1, Hret2.
        assert (d1 = h1 :: r1) as ? by (inversion Hret1; reflexivity); subst d1.
        assert (d2 = h2 :: r2) as ? by (inversion Hret2; reflexivity); subst d2.
        constructor; [|exact (IH r1 r2 p1 q1 p2 q2 Hr1 Hr2)].
        unfold SIG.subst_inp_ident_in_constraint in Hh1, Hh2.
        destruct c1 as (ty1 & tg1). destruct c2 as (ty2 & tg2).
        cbn [snd] in Ht. subst tg2.
        destruct tg1 as [|x0 [|]]; try discriminate Hh1.
        destruct (ident_eqb x x0) eqn:Ex; [discriminate Hh1|].
        unfold SC.ret in Hh1, Hh2.
        assert (h1 = (SIG.subst_ident_in_type ty1 x v, [x0])) as ?
            by (inversion Hh1; reflexivity); subst h1.
        assert (h2 = (SIG.subst_ident_in_type ty2 x v, [x0])) as ?
            by (inversion Hh2; reflexivity); subst h2.
        cbn [fst snd]. split; [reflexivity|].
        cbn [fst] in Hs.
        exact (subst_ident_in_type_same ty1 ty2 x v Hv Hs).
    Qed.

    Lemma cs_same_src_targets :
      forall cs cs', cs_same_src cs cs' -> List.map snd cs = List.map snd cs'.
    Proof.
      intros cs cs' H. induction H as [|c c' l l' (Ht & _) Hr IH];
        [reflexivity|].
      destruct c as (sa1 & tg1). destruct c' as (sa2 & tg2).
      cbn [snd] in Ht. subst tg2. simpl. congruence.
    Qed.

    Lemma subst_ident_constraints_same :
      forall cs1 cs2 x v d1 d2 sa sa' sb sb',
        cs_same_src cs1 cs2 ->
        SIG.subst_ident_constraints cs1 x v sa = OK (d1, sa') ->
        SIG.subst_ident_constraints cs2 x v sb = OK (d2, sb') ->
        cs_same_src d1 d2.
    Proof.
      intros cs1 cs2 x v d1 d2 sa sa' sb sb' Hsame.
      revert d1 d2 sa sa' sb sb'.
      induction Hsame as [|c1 c2 l1 l2 (Ht & Hs) Hr IH];
        intros d1 d2 sa sa' sb sb' H1 H2.
      - unfold SIG.subst_ident_constraints in H1, H2. simpl in H1, H2.
        unfold SC.ret in H1, H2.
        assert (d1 = []) as ? by (inversion H1; reflexivity); subst d1.
        assert (d2 = []) as ? by (inversion H2; reflexivity); subst d2.
        constructor.
      - unfold SIG.subst_ident_constraints in H1, H2. simpl in H1, H2.
        apply sec_bind_inv in H1 as (h1 & p1 & Hh1 & H1).
        apply sec_bind_inv in H1 as (r1 & q1 & Hr1 & Hret1).
        apply sec_bind_inv in H2 as (h2 & p2 & Hh2 & H2).
        apply sec_bind_inv in H2 as (r2 & q2 & Hr2 & Hret2).
        unfold SC.ret in Hret1, Hret2.
        assert (d1 = h1 :: r1) as ? by (inversion Hret1; reflexivity); subst d1.
        assert (d2 = h2 :: r2) as ? by (inversion Hret2; reflexivity); subst d2.
        constructor; [|exact (IH r1 r2 p1 q1 p2 q2 Hr1 Hr2)].
        unfold SIG.subst_ident_constraint in Hh1, Hh2.
        destruct (ident_eqb x v) eqn:Exv; [discriminate Hh1|].
        destruct c1 as (sa1 & tg1). destruct c2 as (sa2 & tg2).
        cbn [fst snd] in Ht, Hs. subst tg2.
        assert (~ In x [v]) as Hxv.
        { intros [Hc|[]]. subst v.
          rewrite (proj2 (ident_eqb_eq x x) (@Coq.Init.Logic.eq_refl _ x))
            in Exv. discriminate. }
        destruct tg1 as [|x0 [|]]; try discriminate Hh1;
          destruct (ident_eqb x x0) eqn:Ex; unfold SC.ret in Hh1, Hh2;
            (assert (h1 = (SIG.subst_ident_in_type sa1 x [v], _)) as ?
                 by (inversion Hh1; reflexivity); subst h1);
            (assert (h2 = (SIG.subst_ident_in_type sa2 x [v], _)) as ?
                 by (inversion Hh2; reflexivity); subst h2);
            cbn [fst snd]; split;
            [reflexivity|exact (subst_ident_in_type_same sa1 sa2 x [v] Hxv Hs)
            |reflexivity|exact (subst_ident_in_type_same sa1 sa2 x [v] Hxv Hs)].
    Qed.

    Lemma subst_constraints_out_map_same :
      forall xs vs cs1 cs2 d1 d2 sa sa' sb sb',
        cs_same_src cs1 cs2 ->
        SIG.subst_constraints_out_map cs1 xs vs sa = OK (d1, sa') ->
        SIG.subst_constraints_out_map cs2 xs vs sb = OK (d2, sb') ->
        cs_same_src d1 d2.
    Proof.
      intros xs. induction xs as [|x xs IH];
        intros vs cs1 cs2 d1 d2 sa sa' sb sb' Hsame H1 H2.
      - destruct vs; [|simpl in H1; discriminate].
        simpl in H1, H2. unfold SC.ret in H1, H2.
        assert (d1 = cs1) as ? by (inversion H1; reflexivity); subst d1.
        assert (d2 = cs2) as ? by (inversion H2; reflexivity); subst d2.
        exact Hsame.
      - destruct vs as [|v vs]; [simpl in H1; discriminate|].
        simpl in H1, H2.
        destruct (SymTypes.findST cs1 v) as [t|] eqn:Ef1;
          [exfalso; unfold SC.error in H1; discriminate H1|].
        destruct (SymTypes.findST cs2 v) as [t|] eqn:Ef2;
          [exfalso; unfold SC.error in H2; discriminate H2|].
        apply sec_bind_inv in H1 as (e1 & p1 & He1 & H1).
        apply sec_bind_inv in H2 as (e2 & p2 & He2 & H2).
        eapply IH; [|exact H1|exact H2].
        exact (subst_ident_constraints_same cs1 cs2 x v e1 e2 sa p1 sb p2
                 Hsame He1 He2).
    Qed.

    Lemma findST_same :
      forall e1 e2 x t1 t2,
        cs_same_src e1 e2 ->
        SymTypes.findST e1 x = Some t1 ->
        SymTypes.findST e2 x = Some t2 ->
        forall z, In z t1 <-> In z t2.
    Proof.
      intros e1 e2 x t1 t2 H. revert t1 t2.
      induction H as [|c1 c2 l1 l2 (Ht & Hs) Hr IH];
        intros t1 t2 H1 H2 z.
      - simpl in H1. discriminate.
      - destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
        cbn [fst snd] in Ht, Hs. subst tg2.
        simpl in H1, H2.
        destruct tg1 as [|d [|]]; [exact (IH t1 t2 H1 H2 z)| |
                                   exact (IH t1 t2 H1 H2 z)].
        destruct (ident_eqb d x) eqn:E; [|exact (IH t1 t2 H1 H2 z)].
        assert (t1 = s1) as ? by (inversion H1; reflexivity); subst t1.
        assert (t2 = s2) as ? by (inversion H2; reflexivity); subst t2.
        exact (Hs z).
    Qed.

    Lemma mmap_findST_same :
      forall (e1 e2 : list SymTypes.constraint) out r1 r2 sa sa' sb sb',
        cs_same_src e1 e2 ->
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e1 x))
                            (fun st => SC.ret (st, [x]))) out sa
          = OK (r1, sa') ->
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e2 x))
                            (fun st => SC.ret (st, [x]))) out sb
          = OK (r2, sb') ->
        cs_same_src r1 r2.
    Proof.
      intros e1 e2 out. induction out as [|x out IH];
        intros r1 r2 sa sa' sb sb' Hsame H1 H2.
      - simpl in H1, H2. unfold SC.ret in H1, H2.
        assert (r1 = []) as ? by (inversion H1; reflexivity); subst r1.
        assert (r2 = []) as ? by (inversion H2; reflexivity); subst r2.
        constructor.
      - simpl in H1, H2.
        apply sec_bind_inv in H1 as (h1 & p1 & Hh1 & H1).
        apply sec_bind_inv in H1 as (rr1 & q1 & Hrr1 & Hret1).
        apply sec_bind_inv in H2 as (h2 & p2 & Hh2 & H2).
        apply sec_bind_inv in H2 as (rr2 & q2 & Hrr2 & Hret2).
        unfold SC.ret in Hret1, Hret2.
        assert (r1 = h1 :: rr1) as ? by (inversion Hret1; reflexivity);
          subst r1.
        assert (r2 = h2 :: rr2) as ? by (inversion Hret2; reflexivity);
          subst r2.
        cbv beta in Hh1, Hh2.
        apply sec_bind_inv in Hh1 as (u1 & m1 & Hu1 & Hv1).
        apply sec_bind_inv in Hh2 as (u2 & m2 & Hu2 & Hv2).
        apply option_to_sec_inv in Hu1 as (Hu1 & ?); subst m1.
        apply option_to_sec_inv in Hu2 as (Hu2 & ?); subst m2.
        unfold SC.ret in Hv1, Hv2.
        assert (h1 = (u1, [x])) as ? by (inversion Hv1; reflexivity); subst h1.
        assert (h2 = (u2, [x])) as ? by (inversion Hv2; reflexivity); subst h2.
        constructor;
          [cbn [fst snd]; split;
             [reflexivity|exact (findST_same e1 e2 x u1 u2 Hsame Hu1 Hu2)]
          |exact (IH rr1 rr2 p1 q1 p2 q2 Hsame Hrr1 Hrr2)].
    Qed.

    (** And the whole of [generate_constraints]: given that the input map's
        results agree as sets, the final constraint lists do, which is what
        [listSatisfiable_same_sources] needs to carry satisfaction from the
        plain instantiation to the augmented one. *)
    Lemma generate_constraints_same_inp :
      forall sig inp inp' clk rst out cns cns' sa sa' sb sb',
        ~ In sig.(s_clk) clk ->
        ~ In sig.(s_reset) rst ->
        (forall a1 a2 t1 t2,
            SIG.subst_constraints_inp_map sig.(s_constraints) sig.(s_in) inp sa
              = OK (a1, t1) ->
            SIG.subst_constraints_inp_map sig.(s_constraints) sig.(s_in) inp' sb
              = OK (a2, t2) ->
            cs_same_src a1 a2) ->
        generate_constraints sig inp clk rst out sa = OK (cns, sa') ->
        generate_constraints sig inp' clk rst out sb = OK (cns', sb') ->
        Forall2
          (fun c c' =>
             (forall z, In z (fst c) <-> In z (fst c'))
             /\ (forall z, In z (snd c) <-> In z (snd c'))) cns cns'.
    Proof.
      intros sig inp inp' clk rst out cns cns' sa sa' sb sb'
        Hclk Hrst Hinp H1 H2.
      unfold generate_constraints in H1, H2.
      apply sec_bind_inv in H1 as (a1 & t1 & Ha1 & H1).
      apply sec_bind_inv in H1 as (b1 & u1 & Hb1 & H1).
      apply sec_bind_inv in H1 as (c1 & v1 & Hc1 & H1).
      apply sec_bind_inv in H1 as (e1 & w1 & He1 & Hr1).
      apply sec_bind_inv in H2 as (a2 & t2 & Ha2 & H2).
      apply sec_bind_inv in H2 as (b2 & u2 & Hb2 & H2).
      apply sec_bind_inv in H2 as (c2 & v2 & Hc2 & H2).
      apply sec_bind_inv in H2 as (e2 & w2 & He2 & Hr2).
      apply cs_same_src_weaken.
      eapply mmap_findST_same; [|exact Hr1|exact Hr2].
      eapply subst_constraints_out_map_same; [|exact He1|exact He2].
      eapply subst_ident_in_constraints_same;
        [exact Hrst| |exact Hc1|exact Hc2].
      eapply subst_ident_in_constraints_same;
        [exact Hclk| |exact Hb1|exact Hb2].
      exact (Hinp a1 a2 t1 t2 Ha1 Ha2).
    Qed.

    (** * A name present in every source, through the whole pipeline

        Rootedness of an *instantiated* block is a statement of this shape: the
        base name is in every final source because the callee's clock formal is
        in every callee source and the base name is in the type substituted for
        it; likewise the reset.  So two moves are needed per stage -- a name
        already there survives, and a name in the substituted type is
        introduced -- and then the remaining stages only have to preserve. *)

    Definition all_sources_have (y : ident) (cs : list SymTypes.constraint)
      : Prop := Forall (fun c => In y (fst c)) cs.

    Lemma subst_ident_in_constraints_all_keeps :
      forall cs x v d sa sa' y,
        ~ In x v ->
        y <> x ->
        all_sources_have y cs ->
        SIG.subst_ident_in_constraints cs x v sa = OK (d, sa') ->
        all_sources_have y d.
    Proof.
      intros cs x v d sa sa' y Hxv Hyx Hall H.
      pose proof (subst_ident_in_constraints_members cs x v d sa sa' Hxv H)
        as Hm. clear H.
      unfold all_sources_have in Hall |- *.
      revert Hall. induction Hm as [|c c' l l' (_ & Hs) Hr IH]; intro Hall;
        [constructor|].
      inversion Hall as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      apply Hs. left. split; [exact Hc|exact Hyx].
    Qed.

    Lemma subst_ident_in_constraints_all_intro :
      forall cs x v d sa sa' y,
        ~ In x v ->
        In y v ->
        all_sources_have x cs ->
        SIG.subst_ident_in_constraints cs x v sa = OK (d, sa') ->
        all_sources_have y d.
    Proof.
      intros cs x v d sa sa' y Hxv Hyv Hall H.
      pose proof (subst_ident_in_constraints_members cs x v d sa sa' Hxv H)
        as Hm. clear H.
      unfold all_sources_have in Hall |- *.
      revert Hall. induction Hm as [|c c' l l' (_ & Hs) Hr IH]; intro Hall;
        [constructor|].
      inversion Hall as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      apply Hs. right. split; [exact Hc|exact Hyv].
    Qed.

    Lemma subst_constraints_inp_map_all_keeps :
      forall xs vs cs d sa sa' y,
        NoDup xs ->
        Forall (fun v => forall z, In z xs -> ~ In z v) vs ->
        ~ In y xs ->
        all_sources_have y cs ->
        SIG.subst_constraints_inp_map cs xs vs sa = OK (d, sa') ->
        all_sources_have y d.
    Proof.
      intros xs vs cs d sa sa' y Hnd Hfr Hy Hall H.
      pose proof (subst_constraints_inp_map_members xs vs cs d sa sa'
                    Hnd Hfr H) as Hm. clear H.
      unfold all_sources_have in Hall |- *.
      revert Hall. induction Hm as [|c c' l l' (_ & Hs) Hr IH]; intro Hall;
        [constructor|].
      inversion Hall as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      apply Hs. left. split; [exact Hc|exact Hy].
    Qed.

    (** The output stage substitutes a formal output by an actual name; a name
        distinct from the formal survives it. *)
    Lemma subst_ident_constraints_all_keeps :
      forall cs x v d sa sa' y,
        y <> x ->
        all_sources_have y cs ->
        SIG.subst_ident_constraints cs x v sa = OK (d, sa') ->
        all_sources_have y d.
    Proof.
      intros cs x v d sa sa' y Hyx Hall.
      unfold all_sources_have in Hall |- *. revert d sa sa'.
      induction Hall as [|c l Hc Hl IH]; intros d sa sa' H.
      - unfold SIG.subst_ident_constraints in H. simpl in H.
        unfold SC.ret in H.
        assert (d = []) as ? by (inversion H; reflexivity); subst d.
        constructor.
      - unfold SIG.subst_ident_constraints in H. simpl in H.
        apply sec_bind_inv in H as (h & p & Hh & H).
        apply sec_bind_inv in H as (r & q & Hr & Hret).
        unfold SC.ret in Hret.
        assert (d = h :: r) as ? by (inversion Hret; reflexivity); subst d.
        constructor; [|exact (IH r p q Hr)].
        unfold SIG.subst_ident_constraint in Hh.
        destruct (ident_eqb x v) eqn:Exv; [discriminate Hh|].
        destruct c as (ty & tg).
        cbn [fst] in Hc.
        assert (~ In x [v]) as Hxv.
        { intros [Hc0|[]]. subst v.
          rewrite (proj2 (ident_eqb_eq x x) (@Coq.Init.Logic.eq_refl _ x))
            in Exv. discriminate. }
        destruct tg as [|x0 [|]]; try discriminate Hh;
          destruct (ident_eqb x x0) eqn:Ex; unfold SC.ret in Hh;
            inversion Hh; subst; cbn [fst];
            (destruct (in_dec ident_eq_dec x ty) as [Hin|Hnin];
             [rewrite (subst_ident_in_type_In ty x [v] y Hin Hxv);
              left; split; [exact Hc|exact Hyx]
             |rewrite (subst_ident_in_type_notIn ty x [v] Hnin); exact Hc]).
    Qed.

    Lemma subst_constraints_out_map_all_keeps :
      forall xs vs cs d sa sa' y,
        ~ In y xs ->
        all_sources_have y cs ->
        SIG.subst_constraints_out_map cs xs vs sa = OK (d, sa') ->
        all_sources_have y d.
    Proof.
      intros xs. induction xs as [|x xs IH];
        intros vs cs d sa sa' y Hy Hall H.
      - destruct vs; [|simpl in H; discriminate].
        simpl in H. unfold SC.ret in H.
        assert (d = cs) as ? by (inversion H; reflexivity); subst d.
        exact Hall.
      - destruct vs as [|v vs]; [simpl in H; discriminate|].
        simpl in H.
        destruct (SymTypes.findST cs v) as [t|] eqn:Ef;
          [exfalso; unfold SC.error in H; discriminate H|].
        apply sec_bind_inv in H as (e & p & He & H).
        eapply IH; [intro Hc; apply Hy; now right| |exact H].
        exact (subst_ident_constraints_all_keeps cs x v e sa p y
                 (fun Hc => Hy (or_introl (@Coq.Init.Logic.eq_sym _ _ _ Hc)))
                 Hall He).
    Qed.

    Lemma mmap_findST_all_keeps :
      forall (e : list SymTypes.constraint) out r sa sa' y,
        all_sources_have y e ->
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e x))
                            (fun st => SC.ret (st, [x]))) out sa
          = OK (r, sa') ->
        all_sources_have y r.
    Proof.
      intros e out. induction out as [|x out IH]; intros r sa sa' y Hall H.
      - simpl in H. unfold SC.ret in H.
        assert (r = []) as ? by (inversion H; reflexivity); subst r.
        constructor.
      - simpl in H.
        apply sec_bind_inv in H as (h & p & Hh & H).
        apply sec_bind_inv in H as (rr & q & Hrr & Hret).
        unfold SC.ret in Hret.
        assert (r = h :: rr) as ? by (inversion Hret; reflexivity); subst r.
        cbv beta in Hh.
        apply sec_bind_inv in Hh as (t & m & Ht & Hv).
        apply option_to_sec_inv in Ht as (Ht & ?); subst m.
        unfold SC.ret in Hv.
        assert (h = (t, [x])) as ? by (inversion Hv; reflexivity); subst h.
        constructor; [|exact (IH rr p q y Hall Hrr)].
        cbn [fst]. apply find_correct in Ht.
        unfold all_sources_have in Hall. rewrite Forall_forall in Hall.
        exact (Hall (t, [x]) Ht).
    Qed.

    (** * Closure, through a substitution

        [subAll_clock_closed] did this for [simplify]; these do it for the four
        slots of [generate_constraints].  The shape is the same: a name already
        accounted for keeps its obligation provided the removal misses it, and a
        name arriving from the substituted type is accounted for provided that
        type is itself closed.

        What makes the removals miss is that a callee's interface names are not
        caller clock-type names.  By [assign_clk_type_members] a clock type
        holds only the base name and security names of caller variables, so the
        single hypothesis below suffices -- and it is a fact about the naming
        pass, which allocates each node's environment separately. *)

    Definition sig_scope_fresh_for_env (sg : signature) : Prop :=
      ~ In base_ty (signature_scope sg)
      /\ ~ In rst_ty (signature_scope sg)
      /\ (forall x b, Env.find x env = Some b -> ~ In b (signature_scope sg)).

    Lemma sig_scope_not_in_clock_type :
      forall sg y ck ckty,
        sig_scope_fresh_for_env sg ->
        In y (signature_scope sg) ->
        assign_clk_type env base_ty ck = Some ckty ->
        ~ In y ckty.
    Proof.
      intros sg y ck ckty (Hb & _ & He) Hy Hck Hc.
      destruct (assign_clk_type_members env base_ty ck ckty Hck y Hc)
        as [Hz|(x & Hx)]; [subst y; exact (Hb Hy)|exact (He x y Hx Hy)].
    Qed.

    (** Closure *modulo a cover*.  An actual argument type is not closed by
        itself -- an argument's type is closed only relative to the clock it
        runs on -- so the property that survives substitution is closure up to a
        fixed set [cov] holding every clock type the call involves.  At the end
        [cov] is shown to be inside the source anyway, which upgrades it to
        closure proper; that last step is the rootedness argument again.

        Getting this wrong is the same mistake as the original
        [source_types_scoped]: a premise that reads plausibly and is met by
        nothing. *)

    Definition constraint_closed_mod (ns : list ident) (cov : ST)
        (c : SymTypes.constraint) : Prop :=
      forall v b ckv ckvty,
        Env.find v env = Some b ->
        ~ In b ns ->
        In b (fst c) ->
        In (v, ckv) vars ->
        assign_clk_type env base_ty ckv = Some ckvty ->
        incl ckvty (merge cov (fst c)).

    Definition constraints_closed_mod (ns : list ident) (cov : ST)
        (cs : list SymTypes.constraint) : Prop :=
      Forall (constraint_closed_mod ns cov) cs.

    Definition st_closed_mod (ns : list ident) (cov t : ST) : Prop :=
      forall v b ckv ckvty,
        Env.find v env = Some b ->
        ~ In b ns ->
        In b t ->
        In (v, ckv) vars ->
        assign_clk_type env base_ty ckv = Some ckvty ->
        incl ckvty (merge cov t).

    Lemma subst_ident_in_constraints_closed_mod :
      forall ns cov cs x v d sa sa',
        ~ In x v ->
        (forall v0 ckv ckvty, In (v0, ckv) vars ->
            assign_clk_type env base_ty ckv = Some ckvty -> ~ In x ckvty) ->
        constraints_closed_mod ns cov cs ->
        st_closed_mod ns cov v ->
        SIG.subst_ident_in_constraints cs x v sa = OK (d, sa') ->
        constraints_closed_mod ns cov d.
    Proof.
      intros ns cov cs x v d sa sa' Hxv Hxck Hcs Hv H.
      pose proof (subst_ident_in_constraints_members cs x v d sa sa' Hxv H)
        as Hm. clear H.
      unfold constraints_closed_mod in Hcs |- *.
      revert Hcs. induction Hm as [|c c' l l' (_ & Hs) Hr IH]; intro Hcs;
        [constructor|].
      inversion Hcs as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      intros v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv.
      assert (~ In x ckvty) as Hnx by exact (Hxck v0 ckv ckvty Hinv Hckv).
      apply Hs in Hb. destruct Hb as [(Hb & Hbx)|(Hxc & Hbv)].
      - intros w Hw.
        assert (In w (merge cov (fst c))) as Hw'
            by exact (Hc v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv w Hw).
        apply in_merge_inv in Hw' as [Hw'|Hw'];
          [now apply in_merge_left|].
        apply in_merge_right, Hs. left. split;
          [exact Hw'|intro; subst w; contradiction].
      - intros w Hw.
        assert (In w (merge cov v)) as Hw'
            by exact (Hv v0 b ckv ckvty Hfv Hnm Hbv Hinv Hckv w Hw).
        apply in_merge_inv in Hw' as [Hw'|Hw'];
          [now apply in_merge_left|].
        apply in_merge_right, Hs. right. split; [exact Hxc|exact Hw'].
    Qed.

    Lemma subst_constraints_inp_map_closed_mod :
      forall ns cov xs vs cs d sa sa',
        NoDup xs ->
        Forall (fun v => forall y, In y xs -> ~ In y v) vs ->
        (forall y, In y xs ->
           forall v0 ckv ckvty, In (v0, ckv) vars ->
             assign_clk_type env base_ty ckv = Some ckvty -> ~ In y ckvty) ->
        constraints_closed_mod ns cov cs ->
        Forall (st_closed_mod ns cov) vs ->
        SIG.subst_constraints_inp_map cs xs vs sa = OK (d, sa') ->
        constraints_closed_mod ns cov d.
    Proof.
      intros ns cov xs vs cs d sa sa' Hnd Hfr Hxck Hcs Hvs H.
      pose proof (subst_constraints_inp_map_members xs vs cs d sa sa'
                    Hnd Hfr H) as Hm. clear H.
      unfold constraints_closed_mod in Hcs |- *.
      revert Hcs. induction Hm as [|c c' l l' (_ & Hs) Hr IH]; intro Hcs;
        [constructor|].
      inversion Hcs as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      intros v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv.
      apply Hs in Hb. destruct Hb as [(Hb & Hbx)|(y & w & Hyw & Hy & Hbw)].
      - intros z Hz.
        assert (In z (merge cov (fst c))) as Hz'
            by exact (Hc v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv z Hz).
        apply in_merge_inv in Hz' as [Hz'|Hz'];
          [now apply in_merge_left|].
        apply in_merge_right, Hs. left. split; [exact Hz'|].
        intro Hc0. exact (Hxck z Hc0 v0 ckv ckvty Hinv Hckv Hz).
      - assert (In w vs) as Hwvs.
        { apply In_combine_nth_error in Hyw as (i & _ & Hwi).
          exact (nth_error_In _ i Hwi). }
        rewrite Forall_forall in Hvs.
        intros z Hz.
        assert (In z (merge cov w)) as Hz'
            by exact (Hvs w Hwvs v0 b ckv ckvty Hfv Hnm Hbw Hinv Hckv z Hz).
        apply in_merge_inv in Hz' as [Hz'|Hz'];
          [now apply in_merge_left|].
        apply in_merge_right, Hs. right. exists y, w.
        split; [exact Hyw|split; [exact Hy|exact Hz']].
    Qed.

    (** The output stage's membership description, which did not exist: it
        substitutes a formal output by an actual *name*, so what arrives is the
        singleton [[v]]. *)
    Lemma subst_ident_constraints_members :
      forall cs x v d sa sa',
        x <> v ->
        SIG.subst_ident_constraints cs x v sa = OK (d, sa') ->
        Forall2
          (fun c c' =>
             forall z,
               In z (fst c') <->
               ((In z (fst c) /\ z <> x) \/ (In x (fst c) /\ z = v)))
          cs d.
    Proof.
      intros cs x v d sa sa' Hxv.
      assert (~ In x [v]) as Hxv' by (intros [Hc|[]]; exact (Hxv (@Coq.Init.Logic.eq_sym _ _ _ Hc))).
      revert d sa sa'.
      induction cs as [|c cs IH]; intros d sa sa' H.
      - unfold SIG.subst_ident_constraints in H. simpl in H. unfold SC.ret in H.
        assert (d = []) as ? by (inversion H; reflexivity); subst d. constructor.
      - unfold SIG.subst_ident_constraints in H. simpl in H.
        apply sec_bind_inv in H as (h & p & Hh & H).
        apply sec_bind_inv in H as (r & q & Hr & Hret).
        unfold SC.ret in Hret.
        assert (d = h :: r) as ? by (inversion Hret; reflexivity); subst d.
        constructor; [|exact (IH r p q Hr)].
        unfold SIG.subst_ident_constraint in Hh.
        destruct (ident_eqb x v) eqn:Exv;
          [exfalso; exact (Hxv (proj1 (ident_eqb_eq x v) Exv))|].
        destruct c as (ty & tg).
        destruct tg as [|x0 [|]]; try discriminate Hh;
          destruct (ident_eqb x x0) eqn:Ex; unfold SC.ret in Hh;
            inversion Hh; subst; cbn [fst snd];
            (destruct (in_dec ident_eq_dec x ty) as [Hin|Hnin];
             [intro z; rewrite (subst_ident_in_type_In ty x [v] z Hin Hxv');
              split;
              [intros [(Hz & Hne)|[Hz|[]]];
                 [left; split; [exact Hz|exact Hne]
                 |right; split; [exact Hin|now symmetry]]
              |intros [(Hz & Hne)|(_ & Hz)];
                 [left; split; [exact Hz|exact Hne]
                 |right; left; now symmetry]]
             |intro z; rewrite (subst_ident_in_type_notIn ty x [v] Hnin);
              split;
              [intro Hz; left; split;
                 [exact Hz|intro; subst z; contradiction]
              |intros [(Hz & _)|(Hz & _)]; [exact Hz|contradiction]]]).
    Qed.

    Lemma subst_ident_constraints_closed_mod :
      forall ns cov cs x v d sa sa',
        x <> v ->
        (forall v0 ckv ckvty, In (v0, ckv) vars ->
            assign_clk_type env base_ty ckv = Some ckvty -> ~ In x ckvty) ->
        constraints_closed_mod ns cov cs ->
        st_closed_mod ns cov [v] ->
        SIG.subst_ident_constraints cs x v sa = OK (d, sa') ->
        constraints_closed_mod ns cov d.
    Proof.
      intros ns cov cs x v d sa sa' Hxv Hxck Hcs Hv H.
      pose proof (subst_ident_constraints_members cs x v d sa sa' Hxv H)
        as Hm. clear H.
      unfold constraints_closed_mod in Hcs |- *.
      revert Hcs. induction Hm as [|c c' l l' Hs Hr IH]; intro Hcs;
        [constructor|].
      inversion Hcs as [|c0 l0 Hc Hl]; subst.
      constructor; [|exact (IH Hl)].
      intros v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv.
      assert (~ In x ckvty) as Hnx by exact (Hxck v0 ckv ckvty Hinv Hckv).
      apply Hs in Hb. destruct Hb as [(Hb & Hbx)|(Hxc & Hbv)].
      - intros w Hw.
        assert (In w (merge cov (fst c))) as Hw'
            by exact (Hc v0 b ckv ckvty Hfv Hnm Hb Hinv Hckv w Hw).
        apply in_merge_inv in Hw' as [Hw'|Hw'];
          [now apply in_merge_left|].
        apply in_merge_right, Hs. left. split;
          [exact Hw'|intro; subst w; contradiction].
      - intros w Hw.
        assert (In b [v]) as Hbv' by (subst b; now left).
        assert (In w (merge cov [v])) as Hw'
            by exact (Hv v0 b ckv ckvty Hfv Hnm Hbv' Hinv Hckv w Hw).
        apply in_merge_inv in Hw' as [Hw'|Hw'];
          [now apply in_merge_left|].
        destruct Hw' as [Hw'|[]].
        apply in_merge_right, Hs. right. split; [exact Hxc|now symmetry].
    Qed.

    Lemma subst_constraints_out_map_closed_mod :
      forall ns cov xs vs cs d sa sa',
        Forall2 (fun x v => x <> v) xs vs ->
        (forall y, In y xs ->
           forall v0 ckv ckvty, In (v0, ckv) vars ->
             assign_clk_type env base_ty ckv = Some ckvty -> ~ In y ckvty) ->
        Forall (fun v => st_closed_mod ns cov [v]) vs ->
        constraints_closed_mod ns cov cs ->
        SIG.subst_constraints_out_map cs xs vs sa = OK (d, sa') ->
        constraints_closed_mod ns cov d.
    Proof.
      intros ns cov xs vs cs d sa sa' Hne.
      revert cs d sa sa'.
      induction Hne as [|x v xs vs Hxv Hr IH]; intros cs d sa sa' Hxck Hvs Hcs H.
      - simpl in H. unfold SC.ret in H.
        assert (d = cs) as ? by (inversion H; reflexivity); subst d. exact Hcs.
      - simpl in H.
        destruct (SymTypes.findST cs v) as [t|] eqn:Ef;
          [exfalso; unfold SC.error in H; discriminate H|].
        apply sec_bind_inv in H as (e & p & He & H).
        inversion Hvs as [|v0 vs0 Hv Hvsr]; subst.
        eapply IH; [|exact Hvsr| |exact H].
        + intros y Hy. apply Hxck. now right.
        + eapply subst_ident_constraints_closed_mod;
            [exact Hxv| |exact Hcs|exact Hv|exact He].
          intros v1 ckv ckvty Hinv Hckv.
          exact (Hxck x (or_introl (@Coq.Init.Logic.eq_refl _ x))
                   v1 ckv ckvty Hinv Hckv).
    Qed.

    Lemma mmap_findST_closed_mod :
      forall ns cov (e : list SymTypes.constraint) out r sa sa',
        constraints_closed_mod ns cov e ->
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e x))
                            (fun st => SC.ret (st, [x]))) out sa
          = OK (r, sa') ->
        constraints_closed_mod ns cov r.
    Proof.
      intros ns cov e out. induction out as [|x out IH];
        intros r sa sa' Hcs H.
      - simpl in H. unfold SC.ret in H.
        assert (r = []) as ? by (inversion H; reflexivity); subst r. constructor.
      - simpl in H.
        apply sec_bind_inv in H as (h & p & Hh & H).
        apply sec_bind_inv in H as (rr & q & Hrr & Hret).
        unfold SC.ret in Hret.
        assert (r = h :: rr) as ? by (inversion Hret; reflexivity); subst r.
        cbv beta in Hh.
        apply sec_bind_inv in Hh as (t & m & Ht & Hv).
        apply option_to_sec_inv in Ht as (Ht & ?); subst m.
        unfold SC.ret in Hv.
        assert (h = (t, [x])) as ? by (inversion Hv; reflexivity); subst h.
        constructor; [|exact (IH rr p q Hcs Hrr)].
        apply find_correct in Ht.
        unfold constraints_closed_mod in Hcs. rewrite Forall_forall in Hcs.
        exact (Hcs (t, [x]) Ht).
    Qed.

    (** * The call rule of rootedness

        Chaining the six steps.  The base name reaches every final source
        through the *clock* slot: the callee's clock formal is in every callee
        source, and the base name is in the type substituted for it.  The reset
        level reaches it the same way through the reset slot.  Everything else
        is preservation, and the side conditions are exactly
        [call_subst_fresh] and the distinctness of the formals. *)
    (** * What a slot's contribution reaches

        The uniform half of discharging the cover.  Generalising the rootedness
        proof: *every* member of the clock actual reaches every final source,
        for the same reason the base name does -- the callee's clock formal is
        in every callee source -- and likewise for the reset.  So the [bckty]
        and [fst rstty] parts of the cover are inside every final source, with
        no reference to which formals a particular constraint mentions. *)

    Lemma generate_constraints_clk_reaches :
      forall sg inp clk rst out cns sa sa' z,
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
        call_subst_fresh sg inp clk rst out ->
        all_sources_have sg.(s_clk) sg.(s_constraints) ->
        In z clk ->
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        all_sources_have z cns.
    Proof.
      intros sg inp clk rst out cns sa sa' z Hnd Hfresh Hck0 Hz H.
      destruct Hfresh as (Hfi & Hfc & Hfr & Hfo).
      unfold types_fresh, type_fresh, outputs_fresh in Hfi, Hfc, Hfr, Hfo.
      assert (NoDup sg.(s_in)) as Hndin by (eapply NoDup_app_l; exact Hnd).
      assert (~ In sg.(s_clk) sg.(s_in)) as Hclkin.
      { intro Hc. eapply NoDup_app_In; [exact Hnd|exact Hc|now left]. }
      assert (In sg.(s_clk) (signature_scope sg)) as Hinclk
          by (unfold signature_scope; apply in_or_app; right;
              apply in_or_app; right; now left).
      assert (In sg.(s_reset) (signature_scope sg)) as Hinrst
          by (unfold signature_scope; apply in_or_app; right;
              apply in_or_app; right; right; now left).
      assert (forall y, In y sg.(s_out) -> In y (signature_scope sg))
        as Hinout
          by (intros y Hy; unfold signature_scope; apply in_or_app; right;
              apply in_or_app; now left).
      assert (forall y, In y sg.(s_in) -> In y (signature_scope sg)) as Hinin
          by (intros y Hy; unfold signature_scope; apply in_or_app; now left).
      assert (~ In sg.(s_clk) clk) as Hnckclk
          by (rewrite Forall_forall in Hfc; intro Hc;
              exact (Hfc sg.(s_clk) Hc Hinclk)).
      assert (~ In sg.(s_reset) rst) as Hnrsrst
          by (rewrite Forall_forall in Hfr; intro Hc;
              exact (Hfr sg.(s_reset) Hc Hinrst)).
      assert (Forall (fun v => forall y, In y sg.(s_in) -> ~ In y v) inp)
        as Hfiv.
      { rewrite Forall_forall in Hfi |- *. intros v Hv y Hy Hc.
        specialize (Hfi v Hv). unfold type_fresh in Hfi.
        rewrite Forall_forall in Hfi. exact (Hfi y Hc (Hinin y Hy)). }
      assert (~ In z (signature_scope sg)) as Hzfr
          by (rewrite Forall_forall in Hfc; exact (Hfc z Hz)).
      assert (z <> sg.(s_reset)) as Hzne
          by (intro Hc; apply Hzfr; rewrite Hc; exact Hinrst).
      assert (~ In z sg.(s_out)) as Hzout
          by (intro Hc; exact (Hzfr (Hinout z Hc))).
      unfold generate_constraints in H.
      apply sec_bind_inv in H as (a1 & t1 & Ha1 & H).
      apply sec_bind_inv in H as (b1 & u1 & Hb1 & H).
      apply sec_bind_inv in H as (c1 & v1 & Hc1 & H).
      apply sec_bind_inv in H as (e1 & w1 & He1 & Hr1).
      eapply mmap_findST_all_keeps; [|exact Hr1].
      eapply subst_constraints_out_map_all_keeps; [exact Hzout| |exact He1].
      eapply subst_ident_in_constraints_all_keeps;
        [exact Hnrsrst|exact Hzne| |exact Hc1].
      eapply subst_ident_in_constraints_all_intro;
        [exact Hnckclk|exact Hz| |exact Hb1].
      eapply subst_constraints_inp_map_all_keeps;
        [exact Hndin|exact Hfiv|exact Hclkin|exact Hck0|exact Ha1].
    Qed.

    Lemma generate_constraints_rst_reaches :
      forall sg inp clk rst out cns sa sa' z,
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
        call_subst_fresh sg inp clk rst out ->
        all_sources_have sg.(s_reset) sg.(s_constraints) ->
        In z rst ->
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        all_sources_have z cns.
    Proof.
      intros sg inp clk rst out cns sa sa' z Hnd Hfresh Hrst0 Hz H.
      destruct Hfresh as (Hfi & Hfc & Hfr & Hfo).
      unfold types_fresh, type_fresh, outputs_fresh in Hfi, Hfc, Hfr, Hfo.
      assert (NoDup sg.(s_in)) as Hndin by (eapply NoDup_app_l; exact Hnd).
      assert (NoDup (sg.(s_clk) :: sg.(s_reset) :: sg.(s_out))) as Hnd2
          by (eapply NoDup_app_r; exact Hnd).
      inversion Hnd2 as [|z1 zs1 Hnclk Hnd3]; subst.
      assert (~ In sg.(s_reset) sg.(s_in)) as Hrstin.
      { intro Hc. eapply NoDup_app_In; [exact Hnd|exact Hc|now right; left]. }
      assert (In sg.(s_clk) (signature_scope sg)) as Hinclk
          by (unfold signature_scope; apply in_or_app; right;
              apply in_or_app; right; now left).
      assert (In sg.(s_reset) (signature_scope sg)) as Hinrst
          by (unfold signature_scope; apply in_or_app; right;
              apply in_or_app; right; right; now left).
      assert (forall y, In y sg.(s_out) -> In y (signature_scope sg))
        as Hinout
          by (intros y Hy; unfold signature_scope; apply in_or_app; right;
              apply in_or_app; now left).
      assert (forall y, In y sg.(s_in) -> In y (signature_scope sg)) as Hinin
          by (intros y Hy; unfold signature_scope; apply in_or_app; now left).
      assert (~ In sg.(s_clk) clk) as Hnckclk
          by (rewrite Forall_forall in Hfc; intro Hc;
              exact (Hfc sg.(s_clk) Hc Hinclk)).
      assert (~ In sg.(s_reset) rst) as Hnrsrst
          by (rewrite Forall_forall in Hfr; intro Hc;
              exact (Hfr sg.(s_reset) Hc Hinrst)).
      assert (Forall (fun v => forall y, In y sg.(s_in) -> ~ In y v) inp)
        as Hfiv.
      { rewrite Forall_forall in Hfi |- *. intros v Hv y Hy Hc.
        specialize (Hfi v Hv). unfold type_fresh in Hfi.
        rewrite Forall_forall in Hfi. exact (Hfi y Hc (Hinin y Hy)). }
      assert (~ In z (signature_scope sg)) as Hzfr
          by (rewrite Forall_forall in Hfr; exact (Hfr z Hz)).
      assert (~ In z sg.(s_out)) as Hzout
          by (intro Hc; exact (Hzfr (Hinout z Hc))).
      unfold generate_constraints in H.
      apply sec_bind_inv in H as (a1 & t1 & Ha1 & H).
      apply sec_bind_inv in H as (b1 & u1 & Hb1 & H).
      apply sec_bind_inv in H as (c1 & v1 & Hc1 & H).
      apply sec_bind_inv in H as (e1 & w1 & He1 & Hr1).
      eapply mmap_findST_all_keeps; [|exact Hr1].
      eapply subst_constraints_out_map_all_keeps; [exact Hzout| |exact He1].
      eapply subst_ident_in_constraints_all_intro;
        [exact Hnrsrst|exact Hz| |exact Hc1].
      eapply subst_ident_in_constraints_all_keeps;
        [exact Hnckclk| | |exact Hb1].
      - intro Hc. apply Hnclk. rewrite <- Hc. now left.
      - eapply subst_constraints_inp_map_all_keeps;
          [exact Hndin|exact Hfiv|exact Hrstin|exact Hrst0|exact Ha1].
    Qed.

    (** And rootedness is the special case at the base name and the reset
        level, which is how it was first proved. *)
    Corollary generate_constraints_rooted :
      forall sg inp clk rst out cns sa sa',
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
        call_subst_fresh sg inp clk rst out ->
        all_sources_have sg.(s_clk) sg.(s_constraints) ->
        all_sources_have sg.(s_reset) sg.(s_constraints) ->
        In base_ty clk ->
        In rst_ty rst ->
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        constraints_rooted base_ty rst_ty cns.
    Proof.
      intros sg inp clk rst out cns sa sa' Hnd Hfresh Hck0 Hrst0 Hb Hr H.
      assert (all_sources_have base_ty cns) as Hbc
          by exact (generate_constraints_clk_reaches sg inp clk rst out cns
                      sa sa' base_ty Hnd Hfresh Hck0 Hb H).
      assert (all_sources_have rst_ty cns) as Hrc
          by exact (generate_constraints_rst_reaches sg inp clk rst out cns
                      sa sa' rst_ty Hnd Hfresh Hrst0 Hr H).
      unfold constraints_rooted, all_sources_have in *.
      rewrite Forall_forall in Hbc, Hrc |- *.
      intros c Hc. split; [exact (Hbc c Hc)|exact (Hrc c Hc)].
    Qed.

    (** * A call's outputs sit above the call's own ambient

        The last ambient fact Leg U needs, and -- unlike the premise it
        replaces -- a property of the *instantiation* rather than an
        assumption about the valuation.  Two things make it go through:

          [generate_constraints_shape], which says the generated block has
          exactly one constraint per output, so each output is a target;

          [generate_constraints_clk_reaches] and
          [generate_constraints_rst_reaches], which say the clock and reset
          levels reach *every* constraint of the block.

        Satisfying the block therefore puts the clock and reset levels below
        each output, which is exactly the bound the equation-level call rule
        was previously handed. *)


    (** The block's targets are its outputs, in order.  This is the [map snd]
        half of [generate_constraints_shape] without its [NoDup out] premise:
        that premise is there for the [wf_constraints] half, and the equation
        level has no [NoDup] on a source equation's variables to offer. *)

    Lemma mmap_findST_targets_eq :
      forall (e : list SymTypes.constraint) out r sa sa',
        SC.mmap (fun x => SC.bind (option_to_sec (SymTypes.findST e x))
                            (fun st => SC.ret (st, [x]))) out sa
          = OK (r, sa') ->
        List.map snd r = List.map (fun ty => [ty]) out.
    Proof.
      intros e out. induction out as [|x out IH]; intros r sa sa' H.
      - simpl in H. unfold SC.ret in H.
        assert (r = []) as ? by (inversion H; reflexivity); subst r.
        reflexivity.
      - simpl in H.
        apply sec_bind_inv in H as (h & p & Hh & H).
        apply sec_bind_inv in H as (rr & q & Hrr & Hret).
        unfold SC.ret in Hret.
        assert (r = h :: rr) as ? by (inversion Hret; reflexivity); subst r.
        apply sec_bind_inv in Hh as (st0 & p0 & Hfind & Hreth).
        apply option_to_sec_inv in Hfind as (_ & ?); subst p0.
        unfold SC.ret in Hreth.
        assert (h = (st0, [x])) as ? by (inversion Hreth; reflexivity);
          subst h.
        cbn [List.map snd]. f_equal. exact (IH rr p q Hrr).
    Qed.

    Lemma generate_constraints_targets :
      forall sg inp clk rst out cns sa sa',
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        List.map snd cns = List.map (fun ty => [ty]) out.
    Proof.
      intros sg inp clk rst out cns sa sa' Hgen.
      unfold generate_constraints in Hgen.
      apply sec_bind_inv in Hgen as (c1 & t1 & _ & Hgen).
      apply sec_bind_inv in Hgen as (c2 & t2 & _ & Hgen).
      apply sec_bind_inv in Hgen as (c3 & t3 & _ & Hgen).
      apply sec_bind_inv in Hgen as (c4 & t4 & _ & Hmap).
      exact (mmap_findST_targets_eq c4 out cns t4 sa' Hmap).
    Qed.

    Lemma generate_constraints_target_In :
      forall sg inp clk rst out cns sa sa' b,
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        In b out ->
        exists t, In (t, [b]) cns.
    Proof.
      intros sg inp clk rst out cns sa sa' b Hgen Hb.
      pose proof (generate_constraints_targets sg inp clk rst out cns
                    sa sa' Hgen) as Hsnd.
      assert (In [b] (List.map snd cns)) as Hin.
      { rewrite Hsnd. apply in_map_iff. exists b.
        split; [reflexivity|exact Hb]. }
      apply in_map_iff in Hin as (c & Hr & Hc).
      destruct c as (t & rhs). cbn [snd] in Hr. subst rhs.
      now exists t.
    Qed.

    Lemma all_sources_below_target :
      forall dlt cns a t b,
        listSatisfiable dlt cns ->
        In (t, [b]) cns ->
        (forall z, In z a -> In z t) ->
        satisfiable dlt a [b].
    Proof.
      intros dlt cns a t b Hsat Hin Hincl.
      assert (constraintSatisfiable dlt (t, [b])) as Hc.
      { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
        exact (Hsat _ Hin). }
      eapply satisfiable_trans; [|exact Hc].
      apply satisfiable_of_members. exact Hincl.
    Qed.

    Lemma generate_constraints_amb_below_out :
      forall sg inp clk rst out cns sa sa' dlt,
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
        call_subst_fresh sg inp clk rst out ->
        all_sources_have sg.(s_clk) sg.(s_constraints) ->
        all_sources_have sg.(s_reset) sg.(s_constraints) ->
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        listSatisfiable dlt cns ->
        forall b, In b out -> satisfiable dlt (merge rst clk) [b].
    Proof.
      intros sg inp clk rst out cns sa sa' dlt
        Hnd Hfresh Hck0 Hrst0 Hgen Hsat b Hb.
      destruct (generate_constraints_target_In sg inp clk rst out cns sa sa' b
                  Hgen Hb) as (t & Hin).
      apply satisfiable_merge_intro.
      - eapply all_sources_below_target; [exact Hsat|exact Hin|].
        intros z Hz.
        assert (all_sources_have z cns) as Hz'
            by exact (generate_constraints_rst_reaches sg inp clk rst out cns
                        sa sa' z Hnd Hfresh Hrst0 Hz Hgen).
        unfold all_sources_have in Hz'. rewrite Forall_forall in Hz'.
        exact (Hz' _ Hin).
      - eapply all_sources_below_target; [exact Hsat|exact Hin|].
        intros z Hz.
        assert (all_sources_have z cns) as Hz'
            by exact (generate_constraints_clk_reaches sg inp clk rst out cns
                        sa sa' z Hnd Hfresh Hck0 Hz Hgen).
        unfold all_sources_have in Hz'. rewrite Forall_forall in Hz'.
        exact (Hz' _ Hin).
    Qed.

    (** * The augmented instantiation can be built, not assumed

        Putting the four stages together: a successful [generate_constraints]
        with one set of actuals gives a successful one with any other of the
        same length.  This is what lets the augmented run exist, which is what
        [subst_constraints_inp_map_augment] and then
        [generate_constraints_mono_sem] are applied to. *)
    Lemma generate_constraints_total_inp :
      forall sig inp inp' clk rst out cns sa sa' sb,
        List.length inp = List.length inp' ->
        generate_constraints sig inp clk rst out sa = OK (cns, sa') ->
        exists cns', generate_constraints sig inp' clk rst out sb
                     = OK (cns', sb).
    Proof.
      intros sig inp inp' clk rst out cns sa sa' sb Hl H.
      unfold generate_constraints in H |- *.
      apply sec_bind_inv in H as (a1 & t1 & Ha1 & H).
      apply sec_bind_inv in H as (b1 & u1 & Hb1 & H).
      apply sec_bind_inv in H as (c1 & v1 & Hc1 & H).
      apply sec_bind_inv in H as (e1 & w1 & He1 & Hr1).
      (** stage 1: the input map, where the actuals differ *)
      destruct (subst_constraints_inp_map_total sig.(s_in)
                  sig.(s_constraints) sig.(s_constraints) inp inp' a1
                  sa t1 sb Hl (@Coq.Init.Logic.eq_refl _ _) Ha1)
        as (a2 & Ha2).
      assert (List.map snd a1 = List.map snd a2) as Hta.
      { rewrite (subst_constraints_inp_map_targets sig.(s_in)
                   sig.(s_constraints) inp a1 sa t1 Ha1).
        rewrite (subst_constraints_inp_map_targets sig.(s_in)
                   sig.(s_constraints) inp' a2 sb sb Ha2).
        reflexivity. }
      (** stage 2: the clock, unchanged *)
      destruct (subst_ident_in_constraints_total a1 a2 sig.(s_clk) clk clk
                  b1 t1 u1 sb Hta Hb1) as (b2 & Hb2).
      assert (List.map snd b1 = List.map snd b2) as Htb.
      { rewrite (subst_ident_in_constraints_targets a1 sig.(s_clk) clk b1
                   t1 u1 Hb1).
        rewrite (subst_ident_in_constraints_targets a2 sig.(s_clk) clk b2
                   sb sb Hb2).
        exact Hta. }
      (** stage 3: the reset, unchanged *)
      destruct (subst_ident_in_constraints_total b1 b2 sig.(s_reset) rst rst
                  c1 u1 v1 sb Htb Hc1) as (c2 & Hc2).
      assert (List.map snd c1 = List.map snd c2) as Htc.
      { rewrite (subst_ident_in_constraints_targets b1 sig.(s_reset) rst c1
                   u1 v1 Hc1).
        rewrite (subst_ident_in_constraints_targets b2 sig.(s_reset) rst c2
                   sb sb Hc2).
        exact Htb. }
      (** stage 4: the outputs, unchanged *)
      destruct (subst_constraints_out_map_total sig.(s_out) out c1 c2 e1
                  v1 w1 sb Htc He1) as (e2 & He2 & Hte).
      (** and the final lookup *)
      destruct (mmap_findST_total e1 e2 out cns w1 sa' sb
                  (@Coq.Init.Logic.eq_sym _ _ _ Hte) Hr1) as (cns' & Hr2).
      exists cns'.
      eapply sec_bind_ok; [exact Ha2|].
      eapply sec_bind_ok; [exact Hb2|].
      eapply sec_bind_ok; [exact Hc2|].
      eapply sec_bind_ok; [exact He2|].
      exact Hr2.
    Qed.

    Lemma subst_constraints_inp_map_augment :
      forall xs vs vs' cs d d' sa sa' sb sb',
        NoDup xs ->
        Forall (fun v => forall y, In y xs -> ~ In y v) vs ->
        Forall (fun v => forall y, In y xs -> ~ In y v) vs' ->
        Forall2 (fun v v' => forall z, In z v -> In z v') vs vs' ->
        (forall c, In c cs ->
           forall y w', In (y, w') (combine xs vs') -> In y (fst c) ->
             forall z, In z w' ->
               exists y2 w2, In (y2, w2) (combine xs vs)
                             /\ In y2 (fst c) /\ In z w2) ->
        SIG.subst_constraints_inp_map cs xs vs  sa = OK (d,  sa') ->
        SIG.subst_constraints_inp_map cs xs vs' sb = OK (d', sb') ->
        Forall2
          (fun a b =>
             (forall z, In z (fst a) <-> In z (fst b))
             /\ (forall z, In z (snd a) <-> In z (snd b)))
          d d'.
    Proof.
      intros xs vs vs' cs d d' sa sa' sb sb' Hnd Hfr Hfr' Hgrow Hdep H H'.
      pose proof (subst_constraints_inp_map_members xs vs cs d _ _ Hnd Hfr H)
        as Hm.
      pose proof (subst_constraints_inp_map_members xs vs' cs d' _ _ Hnd Hfr' H')
        as Hm'.
      clear H H'. revert d d' Hm Hm' Hdep.
      induction cs as [|c cs IH]; intros d d' Hm Hm' Hdep.
      - inversion Hm; subst. inversion Hm'; subst. constructor.
      - inversion Hm as [|c0 a cs0 dr (Hta & Hma) Hmr]; subst.
        inversion Hm' as [|c0' b cs0' dr' (Htb & Hmb) Hmr']; subst.
        constructor.
        + split.
          * intros z. rewrite Hma, Hmb. split.
            -- intros [Hz|(y & w & Hyw & Hy & Hzw)]; [now left|].
               destruct (combine_grow_r xs vs vs' Hgrow y w Hyw)
                 as (w' & Hyw' & Hsub).
               right. exists y, w'. split; [exact Hyw'|].
               split; [exact Hy|exact (Hsub z Hzw)].
            -- intros [Hz|(y & w' & Hyw' & Hy & Hzw')]; [now left|].
               right.
               exact (Hdep c (or_introl (@Coq.Init.Logic.eq_refl _ c))
                        y w' Hyw' Hy z Hzw').
          * intros z.
            destruct a as (a1 & a2). destruct b as (b1 & b2).
            simpl in Hta, Htb |- *. subst a2 b2. tauto.
        + apply IH; [exact Hmr|exact Hmr'|].
          intros c1 Hc1. apply Hdep. now right.
    Qed.

    (** * The augmentation, made concrete

        The design in force prescribes

            inp1''_j := inp1_j joined with the actuals of j's clock variables

        and what that has to contribute is exactly the security names of the
        streams those clock variables were instantiated to -- minimal, and by
        [call_amb_covers_augmented] sufficient: it is precisely the part of an
        argument's own ambient that the uniform ambient does not already
        carry. *)

    Fixpoint sub_names (sub : ident -> option ident) (xs : list ident) : ST :=
      match xs with
      | [] => []
      | x :: xs' =>
          match sub x with
          | Some u =>
              match Env.find u env with
              | Some g => merge [g] (sub_names sub xs')
              | None => sub_names sub xs'
              end
          | None => sub_names sub xs'
          end
      end.

    Definition clock_actuals (sub : ident -> option ident) (ck : clock) : ST :=
      sub_names sub (clock_vars ck).

    Lemma sub_names_inv :
      forall sub xs z,
        In z (sub_names sub xs) ->
        exists x u, In x xs /\ sub x = Some u /\ Env.find u env = Some z.
    Proof.
      intros sub xs. induction xs as [|x xs IH]; intros z Hz; [contradiction|].
      cbn [sub_names] in Hz.
      destruct (sub x) as [u|] eqn:Ex;
        [|destruct (IH z Hz) as (x0 & u0 & H1 & H2 & H3);
          exists x0, u0; split; [now right|auto]].
      destruct (Env.find u env) as [g|] eqn:Eg;
        [|destruct (IH z Hz) as (x0 & u0 & H1 & H2 & H3);
          exists x0, u0; split; [now right|auto]].
      apply in_merge_inv in Hz as [Hz|Hz].
      - destruct Hz as [Hz|[]]; subst g.
        exists x, u. split; [now left|auto].
      - destruct (IH z Hz) as (x0 & u0 & H1 & H2 & H3).
        exists x0, u0. split; [now right|auto].
    Qed.

    Lemma sub_names_intro :
      forall sub xs x u g,
        In x xs -> sub x = Some u -> Env.find u env = Some g ->
        In g (sub_names sub xs).
    Proof.
      intros sub xs. induction xs as [|x0 xs IH]; intros x u g Hin Hs Hg;
        [contradiction|].
      cbn [sub_names]. destruct Hin as [Heq|Hin].
      - subst x0. rewrite Hs, Hg. apply in_merge_left. now left.
      - destruct (sub x0) as [u0|] eqn:E0; [|exact (IH x u g Hin Hs Hg)].
        destruct (Env.find u0 env) as [g0|] eqn:Eg0;
          [|exact (IH x u g Hin Hs Hg)].
        apply in_merge_right. exact (IH x u g Hin Hs Hg).
    Qed.

    Corollary clock_actuals_inv :
      forall sub ck z,
        In z (clock_actuals sub ck) ->
        exists x u, In x (clock_vars ck) /\ sub x = Some u
                    /\ Env.find u env = Some z.
    Proof. intros sub ck z. apply sub_names_inv. Qed.

    Corollary clock_actuals_intro :
      forall sub ck x u g,
        In x (clock_vars ck) -> sub x = Some u -> Env.find u env = Some g ->
        In g (clock_actuals sub ck).
    Proof. intros sub ck. apply sub_names_intro. Qed.

    Definition augment_actuals (sub : ident -> option ident)
        (ins : list (ident * clock)) (argts : list LST) : list ST :=
      List.map (fun p => merge (fst (snd p)) (clock_actuals sub (snd (fst p))))
        (combine ins argts).

    Lemma augment_actuals_cons :
      forall sub p ins t argts,
        augment_actuals sub (p :: ins) (t :: argts)
        = merge (fst t) (clock_actuals sub (snd p))
            :: augment_actuals sub ins argts.
    Proof. reflexivity. Qed.

    Lemma augment_actuals_nth :
      forall sub ins argts i x ck t,
        nth_error ins i = Some (x, ck) ->
        nth_error argts i = Some t ->
        nth_error (augment_actuals sub ins argts) i
          = Some (merge (fst t) (clock_actuals sub ck)).
    Proof.
      intros sub ins argts i x ck t Hxi Hti.
      unfold augment_actuals.
      rewrite (map_nth_error _ i (combine ins argts)
                 (nth_error_combine ins argts i (x, ck) t Hxi Hti)).
      reflexivity.
    Qed.

    (** Read off by position, without going through the equation -- which
        would have to be rewritten under an alias. *)
    Lemma augment_actuals_nth_inv :
      forall sub ins argts i x ck t w' z,
        nth_error ins i = Some (x, ck) ->
        nth_error argts i = Some t ->
        nth_error (augment_actuals sub ins argts) i = Some w' ->
        In z w' ->
        In z (fst t) \/ In z (clock_actuals sub ck).
    Proof.
      intros sub ins. induction ins as [|p ins IH];
        intros argts i x ck t w' z Hxi Hti Hw' Hz.
      - destruct i; discriminate Hxi.
      - destruct argts as [|t0 argts]; [destruct i; discriminate Hti|].
        rewrite augment_actuals_cons in Hw'.
        destruct i as [|i]; simpl in Hxi, Hti, Hw'.
        + inversion Hxi; inversion Hti; inversion Hw'; subst.
          cbn [snd] in Hz.
          apply in_merge_inv in Hz as [Hz|Hz]; [now left|now right].
        + exact (IH argts i x ck t w' z Hxi Hti Hw' Hz).
    Qed.

    Lemma augment_actuals_grows :
      forall sub ins argts,
        List.length ins = List.length argts ->
        Forall2 (fun v v' => forall z, In z v -> In z v')
          (List.map fst argts) (augment_actuals sub ins argts).
    Proof.
      intros sub ins. induction ins as [|p ins IH]; intros argts Hl.
      - destruct argts; [constructor|discriminate].
      - destruct argts as [|t argts]; [discriminate|].
        rewrite augment_actuals_cons. cbn [List.map].
        constructor;
          [intros z Hz; now apply in_merge_left
          |apply IH; simpl in Hl; congruence].
    Qed.

    (** The same, read off what the call site actually has: [wc_exp]'s
        [WellInstantiated] chain, the callee's own [wc_env (idck n_in)], and the
        argument types the generator produced.  The three positional hypotheses
        of [call_augment_dep] are discharged from those; what remains as a
        hypothesis is the callee's naming agreement with its signature's input
        list, which is a fact about [generate_lnode_sig] and so belongs at the
        program level, like [sig_good]. *)
    Lemma call_augment_dep_at_call :
      forall (bad : ident -> Prop) (sg : signature) (n : LSyn.node) (bck : clock)
             (sub nm : ident -> option ident) (es : list exp)
             (argts : list LST) (augs : list SymTypes.ST)
             (c : SymTypes.constraint),
        List.length (idck n.(n_in)) = List.length (s_in sg) ->
        (forall i x ck y,
            nth_error (idck n.(n_in)) i = Some (x, ck) ->
            nth_error (s_in sg) i = Some y -> nm x = Some y) ->
        sig_inputs_clock_closed sg (idck n.(n_in)) nm ->
        wc_env (idck n.(n_in)) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (fun t nck => forall w g,
                     snd nck = Some w -> ~ bad w ->
                     Env.find w env = Some g -> In g (fst t))
          argts (nclocksof es) ->
        (forall i x ck x' u,
            nth_error (idck n.(n_in)) i = Some (x, ck) ->
            In x' (clock_vars ck) -> sub x' = Some u -> ~ bad u) ->
        (forall i x ck w w' z,
            nth_error (idck n.(n_in)) i = Some (x, ck) ->
            nth_error (List.map fst argts) i = Some w ->
            nth_error augs i = Some w' -> In z w' ->
            In z w
            \/ exists x' u, In x' (clock_vars ck)
                            /\ sub x' = Some u
                            /\ Env.find u env = Some z) ->
        In c (s_constraints sg) ->
        forall y w', In (y, w') (combine (s_in sg) augs) -> In y (fst c) ->
          forall z, In z w' ->
            exists y2 w2,
              In (y2, w2) (combine (s_in sg) (List.map fst argts))
              /\ In y2 (fst c) /\ In z w2.
    Proof.
      intros bad sg n bck sub nm es argts augs c Hl1 Hnm Hinv Hwce Hwi Hcov
        Hbadok Haug.
      eapply (call_augment_dep bad sg (idck n.(n_in)) nm sub (nclocksof es)
                (List.map fst argts) augs c);
        [exact Hl1| | |exact Hinv|exact Hnm| | | |exact Haug| ].
      - (** the actuals' nclocks are one per formal *)
        exact (Forall2_length _ _ _ Hwi).
      - (** and so are the argument types *)
        rewrite map_length.
        transitivity (List.length (nclocksof es));
          [exact (Forall2_length _ _ _ Hwi)
          |symmetry; exact (Forall2_length _ _ _ Hcov)].
      - (** [WellInstantiated]'s first component *)
        intros i x ck nck Hxi Hni.
        destruct (Forall2_nth_error _ (idck n.(n_in)) (nclocksof es) i
                    (x, ck) nck Hwi Hxi Hni) as (Hs & _).
        exact Hs.
      - (** a named actual carries its own name *)
        intros i nck w u g Hni Hwi0 Hs Hnb Hu.
        apply nth_error_map_inv in Hwi0 as (t & Hti & ?); subst w.
        exact (Forall2_nth_error _ argts (nclocksof es) i t nck Hcov Hti Hni
                 u g Hs Hnb Hu).
      - (** and no clock variable goes to a [bad] name *)
        exact Hbadok.
      - (** every variable of a formal's clock is itself a formal *)
        intros i x ck x' Hxi Hx'.
        assert (In (x, ck) (idck n.(n_in))) as Hin
            by exact (nth_error_In _ i Hxi).
        exact (clock_vars_wc (idck n.(n_in)) ck
                 (wc_env_var (idck n.(n_in)) x ck Hwce Hin) x' Hx').
    Qed.


    (** The two freshness premises of [subst_constraints_inp_map_augment], for
        the augmented actuals.  They come free: every member of the
        augmentation is a member of *some* actual -- its own, or the one at the
        slot of the clock variable it came from -- so freshness transfers from
        the plain actuals, which is what [call_subst_fresh] already gives. *)
    Lemma augment_actuals_fresh :
      forall (bad : ident -> Prop)
             (sub : ident -> option ident) (ins : list (ident * clock))
             (argts : list LST) (ncks : list nclock) (xs : list ident),
        List.length ins = List.length ncks ->
        List.length ins = List.length argts ->
        (forall i x ck nck,
            nth_error ins i = Some (x, ck) ->
            nth_error ncks i = Some nck -> sub x = snd nck) ->
        (forall i nck t u g,
            nth_error ncks i = Some nck -> nth_error argts i = Some t ->
            snd nck = Some u -> ~ bad u -> Env.find u env = Some g ->
            In g (fst t)) ->
        (forall i x ck x' u,
            nth_error ins i = Some (x, ck) -> In x' (clock_vars ck) ->
            sub x' = Some u -> ~ bad u) ->
        (forall i x ck x',
            nth_error ins i = Some (x, ck) -> In x' (clock_vars ck) ->
            exists ck', In (x', ck') ins) ->
        Forall (fun v => forall y, In y xs -> ~ In y v) (List.map fst argts) ->
        Forall (fun v => forall y, In y xs -> ~ In y v)
          (augment_actuals sub ins argts).
    Proof.
      intros bad sub ins argts ncks xs Hl2 Hl3 Hwi Hnamed Hbadok Hformal Hfr.
      rewrite Forall_forall in Hfr |- *.
      intros v' Hv' y Hy Hz.
      apply In_nth_error in Hv' as (i & Hvi).
      (** the slot this augmented actual belongs to *)
      assert (exists x ck, nth_error ins i = Some (x, ck)) as (x & ck & Hxi).
      { assert (i < List.length ins)%nat as Hlt.
        { unfold augment_actuals in Hvi.
          apply nth_error_lt_inv in Hvi. rewrite map_length in Hvi.
          rewrite combine_length in Hvi. lia. }
        destruct (nth_error_lt ins i Hlt) as ((x & ck) & Hxi).
        now exists x, ck. }
      assert (exists t, nth_error argts i = Some t) as (t & Hti)
          by (apply nth_error_lt; rewrite <- Hl3;
              exact (nth_error_lt_inv ins i (x, ck) Hxi)).
      destruct (augment_actuals_nth_inv sub ins argts i x ck t v' y
                  Hxi Hti Hvi Hz) as [Hy'|Hy'].
      - (** its own actual *)
        exact (Hfr (fst t)
                 (nth_error_In _ i (map_nth_error fst i argts Hti)) y Hy Hy').
      - (** the actual at the slot of the clock variable it came from *)
        destruct (clock_actuals_inv sub ck y Hy')
          as (x' & u & Hx' & Hs & Hu).
        destruct (Hformal i x ck x' Hxi Hx') as (ck2 & Hin2).
        apply In_nth_error in Hin2 as (j & Hxj).
        assert (exists nck2, nth_error ncks j = Some nck2) as (nck2 & Hnj)
            by (apply nth_error_lt; rewrite <- Hl2;
                exact (nth_error_lt_inv ins j (x', ck2) Hxj)).
        assert (exists t2, nth_error argts j = Some t2) as (t2 & Hwj)
            by (apply nth_error_lt; rewrite <- Hl3;
                exact (nth_error_lt_inv ins j (x', ck2) Hxj)).
        assert (snd nck2 = Some u) as Hs2
            by (rewrite <- (Hwi j x' ck2 nck2 Hxj Hnj); exact Hs).
        exact (Hfr (fst t2)
                 (nth_error_In _ j (map_nth_error fst j argts Hwj)) y Hy
                 (Hnamed j nck2 t2 u y Hnj Hwj Hs2
                    (Hbadok i x ck x' u Hxi Hx' Hs) Hu)).
    Qed.

    (** * What the program level must supply about the signatures

        Two facts, paired because they are established together when
        [generate_lnode_sig] runs: a callee's signature input list lines up with
        its node's inputs under the callee's own naming, and its constraints are
        closed under those inputs' declared clocks.  Parameterised by the Lustre
        program, because the pairing of [GL] with [P] is fixed at the program
        level -- this joins [sig_good], [sig_scoped] and [sig_actuals_fresh] as
        a hypothesis discharged there. *)
    Definition sig_inputs_ok (P : global) : Prop :=
      forall f n sg,
        find_node f P = Some n ->
        find_signature f GL = Some sg ->
        exists nm,
          List.length (idck n.(n_in)) = List.length (s_in sg)
          /\ (forall i x ck y,
                 nth_error (idck n.(n_in)) i = Some (x, ck) ->
                 nth_error (s_in sg) i = Some y -> nm x = Some y)
          (** over the whole interface, not just the inputs: see
              [sig_inputs_clock_closed_incl] *)
          /\ sig_inputs_clock_closed sg (idck (n.(n_in) ++ n.(n_out))) nm.

    (** And the whole of it, on the concrete augmentation: the premise
        [subst_constraints_inp_map_augment] asks for, with nothing left
        abstract but the two program-level facts. *)
    Corollary call_augment_dep_concrete :
      forall (bad : ident -> Prop) (P : global) (sg : signature)
             (n : LSyn.node) (bck : clock)
             (sub : ident -> option ident) (f : ident) (es : list exp)
             (argts : list LST) (c : SymTypes.constraint),
        sig_inputs_ok P ->
        find_node f P = Some n ->
        find_signature f GL = Some sg ->
        wc_env (idck n.(n_in)) ->
        Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
        Forall2 (fun t nck => forall w g,
                     snd nck = Some w -> ~ bad w ->
                     Env.find w env = Some g -> In g (fst t))
          argts (nclocksof es) ->
        (forall i x ck x' u,
            nth_error (idck n.(n_in)) i = Some (x, ck) ->
            In x' (clock_vars ck) -> sub x' = Some u -> ~ bad u) ->
        In c (s_constraints sg) ->
        forall y w',
          In (y, w') (combine (s_in sg)
                        (augment_actuals sub (idck n.(n_in)) argts)) ->
          In y (fst c) ->
          forall z, In z w' ->
            exists y2 w2,
              In (y2, w2) (combine (s_in sg) (List.map fst argts))
              /\ In y2 (fst c) /\ In z w2.
    Proof.
      intros bad P sg n bck sub f es argts c Hok Hfn Hfs Hwce Hwi Hcov Hbadok
        Hc.
      destruct (Hok f n sg Hfn Hfs) as (nm & Hl1 & Hnm & Hinv).
      assert (sig_inputs_clock_closed sg (idck n.(n_in)) nm) as Hinv'.
      { eapply sig_inputs_clock_closed_incl; [|exact Hinv].
        unfold idck. intros p Hp. apply in_map_iff in Hp as (q & ? & Hq).
        apply in_map_iff. exists q. split; [assumption|].
        apply in_or_app. now left. }
      eapply (call_augment_dep_at_call bad sg n bck sub nm es argts
                (augment_actuals sub (idck n.(n_in)) argts) c);
        [exact Hl1|exact Hnm|exact Hinv'|exact Hwce|exact Hwi|exact Hcov
        |exact Hbadok|
         |exact Hc].
      (** the shape of the augmentation: it adds only clock names *)
      intros i x ck w w' z Hxi Hwi0 Hw' Hz.
      apply nth_error_map_inv in Hwi0 as (t & Hti & ?); subst w.
      destruct (augment_actuals_nth_inv sub (idck n.(n_in)) argts i x ck t w' z
                  Hxi Hti Hw' Hz) as [Hz'|Hz']; [now left|].
      right. exact (clock_actuals_inv sub ck z Hz').
    Qed.

    (** * Clause 3 of the chain, uniformly

        The obligation the design in force records for the augmented
        instantiation, and the reason the augmentation carries *only* the clock
        variables' actuals: the base and reset levels are not its job, they are
        the uniform ambient's.

        An argument's own ambient is [merge [rst_ty] ckjty] for its
        instantiated clock; that clock is the call's base clock extended by
        exactly the formal's clock variables, so by
        [assign_clk_type_instck_incl] its type splits into the base clock's
        type -- which [call_amb] already carries -- and the actuals of those
        variables, which are what the augmentation adds.  Nothing else. *)

    Lemma call_amb_covers_augmented :
      forall bck sub ckf ckj bckty ckjty (w acts : SymTypes.ST),
        instck bck sub ckf = Some ckj ->
        assign_clk_type env base_ty bck = Some bckty ->
        assign_clk_type env base_ty ckj = Some ckjty ->
        (forall x' u z, In x' (clock_vars ckf) -> sub x' = Some u ->
                        Env.find u env = Some z -> In z acts) ->
        incl (merge (merge [rst_ty] ckjty) w)
             (merge (merge [rst_ty] bckty) (merge w acts)).
    Proof.
      intros bck sub ckf ckj bckty ckjty w acts Hi Hbk Hck Hact z Hz.
      apply in_merge_inv in Hz as [Hz|Hz].
      - apply in_merge_inv in Hz as [Hz|Hz].
        + apply in_merge_left. now apply in_merge_left.
        + (** the argument's clock, split by [assign_clk_type_instck] *)
          assert (In z (merge bckty acts)) as Hz'
              by exact (assign_clk_type_instck_incl env base_ty bck sub ckf ckj
                          bckty ckjty acts Hi Hbk Hck Hact z Hz).
          apply in_merge_inv in Hz' as [Hz'|Hz'].
          * apply in_merge_left. now apply in_merge_right.
          * apply in_merge_right. now apply in_merge_right.
      - apply in_merge_right. now apply in_merge_left.
    Qed.

    (** Clause 3, on the concrete augmentation. *)
    Corollary call_amb_covers_augmented_concrete :
      forall bck sub ck (t : LST) bckty ckjty ckj,
        instck bck sub ck = Some ckj ->
        assign_clk_type env base_ty bck = Some bckty ->
        assign_clk_type env base_ty ckj = Some ckjty ->
        incl (merge (merge [rst_ty] ckjty) (fst t))
             (merge (merge [rst_ty] bckty)
                (merge (fst t) (clock_actuals sub ck))).
    Proof.
      intros bck sub ck t bckty ckjty ckj Hi Hbk Hck.
      eapply call_amb_covers_augmented; [exact Hi|exact Hbk|exact Hck|].
      intros x' u z Hx' Hs Hu.
      exact (clock_actuals_intro sub ck x' u z Hx' Hs Hu).
    Qed.

    (** * The ambients the streams call case hands its arguments

        The argument streams run on the instantiated formal clocks, so each one
        needs an ambient covering [merge [rst_ty] (its clock's type)].  Taking
        the call's own ambient joined with that slot's clock actuals does it --
        which is the same set the augmentation uses, and by
        [call_amb_covers_augmented] it covers exactly what is needed and no
        more. *)
    Definition call_arg_ambient (sub : ident -> option ident)
        (bckty : ST) (ck : clock) : ST :=
      merge (merge [rst_ty] bckty) (clock_actuals sub ck).

    Lemma call_arg_ambient_covers :
      forall bck sub bckty ck ckj ckjty,
        instck bck sub ck = Some ckj ->
        assign_clk_type env base_ty bck = Some bckty ->
        assign_clk_type env base_ty ckj = Some ckjty ->
        incl (merge [rst_ty] ckjty) (call_arg_ambient sub bckty ck).
    Proof.
      intros bck sub bckty ck ckj ckjty Hi Hbk Hck.
      unfold call_arg_ambient.
      intros z Hz.
      assert (In z (merge (merge [rst_ty] bckty) (merge [] (clock_actuals sub ck))))
        as Hz'.
      { eapply call_amb_covers_augmented;
          [exact Hi|exact Hbk|exact Hck| |].
        - intros x' u g Hx' Hs Hu.
          exact (clock_actuals_intro sub ck x' u g Hx' Hs Hu).
        - apply in_merge_left. exact Hz. }
      apply in_merge_inv in Hz' as [Hz'|Hz'];
        [now apply in_merge_left|].
      apply in_merge_inv in Hz' as [[]|Hz'].
      now apply in_merge_right.
    Qed.



    (** * The invariant the chain carries

        Both sides start from the same signature, so what separates them is
        only which actuals have been substituted in.  [rest] is the formals
        still to come.  Three clauses: the targets never move; the remaining
        formals occur on one side exactly when they occur on the other, so the
        two sides branch alike at every remaining step; and domination holds
        not just as it stands but after dropping any of the remaining formals,
        which is what survives the next substitution. *)

    Definition cs_chain (dlt : ident -> Lat.t) (rest : list ident)
      (cs1 cs2 : list constraint) : Prop :=
      Forall2 (fun c1 c2 =>
                 snd c1 = snd c2
                 /\ (forall x, In x rest -> (In x (fst c1) <-> In x (fst c2)))
                 /\ (forall R, (forall y, In y R -> In y rest) ->
                       satisfiable dlt (remove_all R (fst c2))
                         (merge amb (remove_all R (fst c1)))))
        cs1 cs2.

    Lemma cs_chain_refl :
      forall dlt rest cs, cs_chain dlt rest cs cs.
    Proof.
      intros dlt rest cs. induction cs as [|c cs IH]; [constructor|].
      constructor; [|exact IH].
      split; [reflexivity|split].
      - intros x Hx. reflexivity.
      - intros R HR. apply satisfiable_merge_r.
    Qed.

    Lemma join_amb_distr :
      forall a x y,
        Lat.order (Lat.join (Lat.join a x) (Lat.join a y))
          (Lat.join a (Lat.join x y)).
    Proof.
      intros a x y. apply Lat.join_least_upper_bound.
      - apply Lat.join_least_upper_bound;
          [apply Lat.join_bound1|].
        eapply Lat.order_trans; [apply Lat.join_bound1|apply Lat.join_bound2].
      - apply Lat.join_least_upper_bound;
          [apply Lat.join_bound1|].
        eapply Lat.order_trans; [apply Lat.join_bound2|apply Lat.join_bound2].
    Qed.

    Lemma join_mono :
      forall a a' b b',
        Lat.order a a' -> Lat.order b b' ->
        Lat.order (Lat.join a b) (Lat.join a' b').
    Proof.
      intros a a' b b' Ha Hb. apply Lat.join_least_upper_bound.
      - eapply Lat.order_trans; [exact Ha|apply Lat.join_bound1].
      - eapply Lat.order_trans; [exact Hb|apply Lat.join_bound2].
    Qed.

    (** One formal, substituted on both sides.  The two sides branch alike
        because the invariant says the formal occurs on one exactly when it
        occurs on the other; and what the substitution leaves is the body
        with one more formal dropped, joined with the actual -- which is the
        shape the invariant is stated in, one step further along. *)

    (** The core of a substitution step, on one source type.  Both phases of
        the chain use it: the input map substitutes an actual type for a
        formal input, the output map substitutes a single actual name for a
        formal output, and as far as the *sources* go those are the same
        operation.  Only the targets tell the two phases apart. *)

    Lemma subst_type_step :
      forall dlt rest x s1 s2 v1 v2,
        (forall y, In y (x :: rest) -> (In y s1 <-> In y s2)) ->
        (forall R, (forall y, In y R -> In y (x :: rest)) ->
           satisfiable dlt (remove_all R s2) (merge amb (remove_all R s1))) ->
        ~ In x rest ->
        (forall y, In y (x :: rest) -> ~ In y v1) ->
        (forall y, In y (x :: rest) -> ~ In y v2) ->
        satisfiable dlt v2 (merge amb v1) ->
        (forall y, In y rest ->
           (In y (SIG.subst_ident_in_type s1 x v1)
            <-> In y (SIG.subst_ident_in_type s2 x v2)))
        /\ (forall R, (forall y, In y R -> In y rest) ->
              satisfiable dlt (remove_all R (SIG.subst_ident_in_type s2 x v2))
                (merge amb
                   (remove_all R (SIG.subst_ident_in_type s1 x v1)))).
    Proof.
      intros dlt rest x s1 s2 v1 v2 Hiff Hdom Hxr Hv1 Hv2 Hdv.
      destruct (in_dec ident_eq_dec x s1) as [Hin1|Hnin1].
      - assert (In x s2) as Hin2 by (apply Hiff; [now left|exact Hin1]).
        assert (forall z, In z (SIG.subst_ident_in_type s1 x v1)
                          <-> ((In z s1 /\ z <> x) \/ In z v1)) as Hm1
          by (intros; apply subst_ident_in_type_In;
              [exact Hin1|apply Hv1; now left]).
        assert (forall z, In z (SIG.subst_ident_in_type s2 x v2)
                          <-> ((In z s2 /\ z <> x) \/ In z v2)) as Hm2
          by (intros; apply subst_ident_in_type_In;
              [exact Hin2|apply Hv2; now left]).
        split.
        + intros z Hz. rewrite Hm1, Hm2.
          assert (~ In z v1) as Hzv1 by (apply Hv1; now right).
          assert (~ In z v2) as Hzv2 by (apply Hv2; now right).
          split.
          * intros [(Hs & Hne)|Hvz]; [|contradiction].
            left. split; [apply Hiff; [now right|exact Hs]|exact Hne].
          * intros [(Hs & Hne)|Hvz]; [|contradiction].
            left. split; [apply Hiff; [now right|exact Hs]|exact Hne].
        + intros R HR.
          assert (forall (si vi : ST),
                    (forall z, In z (SIG.subst_ident_in_type si x vi)
                               <-> ((In z si /\ z <> x) \/ In z vi)) ->
                    forall z,
                      In z (remove_all R (SIG.subst_ident_in_type si x vi)) ->
                      In z (remove_all (x :: R) si) \/ In z vi) as Hsub.
          { intros si vi Hm z Hz.
            apply remove_all_In in Hz as (Hz & HzR).
            apply Hm in Hz as [(Hs & Hne)|Hvz]; [|now right].
            left. apply remove_all_In. split; [exact Hs|].
            intros [Heq|HR']; [now apply Hne|now apply HzR]. }
          assert (forall (si vi : ST),
                    (forall z, In z (SIG.subst_ident_in_type si x vi)
                               <-> ((In z si /\ z <> x) \/ In z vi)) ->
                    (forall y0, In y0 (x :: rest) -> ~ In y0 vi) ->
                    forall z,
                      In z (remove_all (x :: R) si) \/ In z vi ->
                      In z (remove_all R (SIG.subst_ident_in_type si x vi)))
            as Hsup.
          { intros si vi Hm Hvi z [Hz|Hz].
            - apply remove_all_In in Hz as (Hz & HzR).
              apply remove_all_In. split.
              + apply Hm. left. split;
                  [exact Hz|intro; subst; apply HzR; now left].
              + intro; apply HzR; now right.
            - apply remove_all_In. split.
              + apply Hm. now right.
              + intro HzR. eapply (Hvi z); [|exact Hz]. right. now apply HR. }
          assert (satisfiable dlt (remove_all (x :: R) s2)
                    (merge amb (remove_all (x :: R) s1))) as Hd1.
          { apply (Hdom (x :: R)). intros z [Hz|Hz]; subst; [now left|].
            right. now apply HR. }
          unfold satisfiable in Hd1, Hdv |- *.
          rewrite hm_ext_merge_eq in Hd1, Hdv |- *.
          eapply Lat.order_trans;
            [apply hm_ext_union_le with
               (a := remove_all (x :: R) s2) (b := v2);
             intros z Hz; now apply (Hsub s2 v2 Hm2)|].
          eapply Lat.order_trans;
            [apply join_mono; [exact Hd1|exact Hdv]|].
          eapply Lat.order_trans; [apply join_amb_distr|].
          apply join_mono; [apply Lat.order_refl, Lat.eq_refl|].
          apply hm_ext_union_ge with
            (a := remove_all (x :: R) s1) (b := v1);
            intros z Hz; apply (Hsup s1 v1 Hm1 Hv1); auto.
      - assert (~ In x s2) as Hnin2
          by (intro Hc; apply Hnin1, Hiff; [now left|exact Hc]).
        rewrite !subst_ident_in_type_notin by assumption.
        split.
        + intros z Hz. apply Hiff. now right.
        + intros R HR. apply Hdom. intros z Hz. right. now apply HR.
    Qed.

    Lemma subst_ident_in_constraints_chain :
      forall dlt rest x cs1 cs2 v1 v2 d1 d2 sa sa' sb sb',
        cs_chain dlt (x :: rest) cs1 cs2 ->
        ~ In x rest ->
        (forall y, In y (x :: rest) -> ~ In y v1) ->
        (forall y, In y (x :: rest) -> ~ In y v2) ->
        satisfiable dlt v2 (merge amb v1) ->
        SIG.subst_ident_in_constraints cs1 x v1 sa = OK (d1, sa') ->
        SIG.subst_ident_in_constraints cs2 x v2 sb = OK (d2, sb') ->
        cs_chain dlt rest d1 d2.
    Proof.
      intros dlt rest x cs1 cs2 v1 v2 d1 d2 sa sa' sb sb'
        Hch Hxr Hv1 Hv2 Hdv H1 H2.
      unfold SIG.subst_ident_in_constraints in H1, H2.
      revert d1 d2 sa sa' sb sb' H1 H2.
      induction Hch as [|c1 c2 l1 l2 (Ht & Hiff & Hdom) Hr IH];
        intros d1 d2 sa sa' sb sb' H1 H2.
      - simpl in H1, H2. unfold ret in H1, H2. inv H1. inv H2. constructor.
      - simpl in H1, H2.
        eapply sec_bind_inv in H1 as (e1 & t1 & He1 & H1).
        eapply sec_bind_inv in H1 as (r1 & u1 & Hr1 & Hret1).
        unfold ret in Hret1. inv Hret1.
        eapply sec_bind_inv in H2 as (e2 & t2 & He2 & H2).
        eapply sec_bind_inv in H2 as (r2 & u2 & Hr2 & Hret2).
        unfold ret in Hret2. inv Hret2.
        constructor; [|eapply IH; eauto].
        destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
        simpl in Ht, Hiff, Hdom. subst tg2.
        destruct tg1 as [|y [|]]; simpl in He1, He2; try discriminate.
        destruct (ident_eqb x y) eqn:Hxy; try discriminate.
        unfold ret in He1, He2. inv He1. inv He2.
        simpl. split; [reflexivity|].
        eapply subst_type_step; eauto.
    Qed.

    (** The whole input map.  [rest] is what the clock and reset steps will
        still consume, so the invariant comes out of the fold still carrying
        them. *)

    Lemma subst_constraints_inp_map_chain :
      forall dlt xs rest vs1 vs2 cs1 cs2 d1 d2 sa sa' sb sb',
        NoDup (xs ++ rest) ->
        cs_chain dlt (xs ++ rest) cs1 cs2 ->
        Forall (fun v => forall y, In y (xs ++ rest) -> ~ In y v) vs1 ->
        Forall (fun v => forall y, In y (xs ++ rest) -> ~ In y v) vs2 ->
        Forall2 (fun t1 t2 => satisfiable dlt t2 (merge amb t1)) vs1 vs2 ->
        SIG.subst_constraints_inp_map cs1 xs vs1 sa = OK (d1, sa') ->
        SIG.subst_constraints_inp_map cs2 xs vs2 sb = OK (d2, sb') ->
        cs_chain dlt rest d1 d2.
    Proof.
      intros dlt xs. revert dlt.
      induction xs as [|x xs IH];
        intros dlt rest vs1 vs2 cs1 cs2 d1 d2 sa sa' sb sb'
          Hnd Hch Hf1 Hf2 Hv H1 H2.
      - destruct vs1 as [|p ps]; simpl in H1; [|discriminate].
        inv Hv. simpl in H2.
        unfold ret in H1, H2. inv H1. inv H2. exact Hch.
      - destruct vs1 as [|p ps]; simpl in H1; [discriminate|].
        inversion Hv as [|p0 q ps0 qs Hpq Hvr]; subst.
        inversion Hf1 as [|z zs Hz Hzr]; subst.
        inversion Hf2 as [|w ws Hw Hwr]; subst.
        simpl in H1, H2.
        eapply sec_bind_inv in H1 as (e1 & t1 & He1 & H1).
        eapply sec_bind_inv in H2 as (e2 & t2 & He2 & H2).
        eapply IH; [| | | |exact Hvr|exact H1|exact H2].
        + rewrite <- app_comm_cons in Hnd. now inv Hnd.
        + eapply subst_ident_in_constraints_chain;
            [exact Hch| |exact Hz|exact Hw|exact Hpq|exact He1|exact He2].
          rewrite <- app_comm_cons in Hnd. now inv Hnd.
        + eapply Forall_impl; [|exact Hzr].
          intros v Hv0 y Hy. apply Hv0. now right.
        + eapply Forall_impl; [|exact Hwr].
          intros v Hv0 y Hy. apply Hv0. now right.
    Qed.

    (** The clock and the reset are one formal each, and the same actual goes
        in on both sides, so those two steps only have to preserve what the
        input map left. *)

    Corollary subst_ident_in_constraints_chain_same :
      forall dlt rest x cs1 cs2 v d1 d2 sa sa' sb sb',
        cs_chain dlt (x :: rest) cs1 cs2 ->
        ~ In x rest ->
        (forall y, In y (x :: rest) -> ~ In y v) ->
        SIG.subst_ident_in_constraints cs1 x v sa = OK (d1, sa') ->
        SIG.subst_ident_in_constraints cs2 x v sb = OK (d2, sb') ->
        cs_chain dlt rest d1 d2.
    Proof.
      intros dlt rest x cs1 cs2 v d1 d2 sa sa' sb sb' Hch Hxr Hv H1 H2.
      eapply subst_ident_in_constraints_chain;
        [exact Hch|exact Hxr|exact Hv|exact Hv|apply satisfiable_merge_r
        |exact H1|exact H2].
    Qed.

    (** * The output phase

        The sources are substituted exactly as in the input phase, so clauses
        two and three of the chain are still what carries them -- which is why
        the chain has to be run leaving the outputs in [rest] rather than
        emptied.  What is new is the targets: the two sides rename them to
        *different* actuals, and all that survives is that the two actuals
        agree under the witness.  That agreement is how the witness was chosen
        on the target names in the first place. *)

    Definition cs_le (dlt : ident -> Lat.t) (cs1 cs2 : list constraint)
      : Prop :=
      Forall2 (fun c1 c2 => satisfiable dlt (fst c2) (merge amb (fst c1))
                            /\ satisfiable dlt (merge amb (snd c1)) (snd c2))
        cs1 cs2.

    Lemma cs_le_satisfaction :
      forall dlt cs1 cs2,
        cs_le dlt cs1 cs2 -> listSatisfiable dlt cs1 -> listSatisfiable dlt cs2.
    Proof.
      intros dlt cs1 cs2 Hle Hs.
      induction Hle as [|c1 c2 l1 l2 (Hsrc & Htgt) Hr IH]; [constructor|].
      inversion Hs as [|z zs Hz Hzr]; subst.
      constructor; [|now apply IH].
      destruct c1 as (s1 & t1). destruct c2 as (s2 & t2).
      simpl in Hsrc, Htgt. unfold constraintSatisfiable in *.
      eapply satisfiable_trans; [exact Hsrc|].
      eapply satisfiable_trans; [apply satisfiable_merge_mono; exact Hz|exact Htgt].
    Qed.

    Lemma satisfiable_singleton_eq :
      forall dlt a b, dlt a = dlt b -> satisfiable dlt [a] [b].
    Proof.
      intros dlt a b H. unfold satisfiable. simpl. rewrite H.
      apply Lat.order_refl, Lat.eq_refl.
    Qed.

    Definition amb_pair (dlt : ident -> Lat.t) (o b : ident) : Prop :=
      satisfiable dlt [b] (merge amb [o]) /\ satisfiable dlt (merge amb [o]) [b].

    Definition cs_out (dlt : ident -> Lat.t) (rest : list ident)
      (cs1 cs2 : list constraint) : Prop :=
      Forall2 (fun c1 c2 =>
        (exists t1 t2, snd c1 = [t1] /\ snd c2 = [t2]
                       /\ (In t1 rest \/ satisfiable dlt (merge amb [t1]) [t2])
                       /\ (forall x, In x rest -> (x = t1 <-> x = t2)))
        /\ (forall x, In x rest -> (In x (fst c1) <-> In x (fst c2)))
        /\ (forall R, (forall y, In y R -> In y rest) ->
              satisfiable dlt (remove_all R (fst c2))
                (merge amb (remove_all R (fst c1)))))
        cs1 cs2.

    Lemma cs_chain_out :
      forall dlt rest cs1 cs2,
        cs_chain dlt rest cs1 cs2 ->
        Forall (fun c => exists t, snd c = [t] /\ In t rest) cs1 ->
        cs_out dlt rest cs1 cs2.
    Proof.
      intros dlt rest cs1 cs2 Hch Hsing.
      induction Hch as [|c1 c2 l1 l2 (Ht & Hiff & Hdom) Hr IH]; [constructor|].
      inversion Hsing as [|z zs (t & Hz & Htr) Hzr]; subst.
      constructor; [|now apply IH].
      split; [|split; assumption].
      assert (snd c2 = [t]) as Hz2 by (rewrite <- Ht; exact Hz).
      exists t, t.
      split; [exact Hz|split; [exact Hz2|split; [now left|]]].
      intros x Hx. tauto.
    Qed.

    (** The targets of a well-formed constraint list are exactly its node's
        outputs, one each -- which is what puts every target in [rest] when
        the output phase starts. *)

    Lemma singleton_targets_of_perm :
      forall (cs : list constraint) (out : list ident),
        Permutation (map snd cs) (map (fun y => [y]) out) ->
        Forall (fun c => exists t, snd c = [t] /\ In t out) cs.
    Proof.
      intros cs out Hp. apply Forall_forall. intros c Hc.
      assert (In (snd c) (map (fun y => [y]) out)) as Hin
        by (eapply Permutation_in; [exact Hp|now apply in_map]).
      apply in_map_iff in Hin as (t & Ht & Hto).
      exists t. split; [now symmetry|exact Hto].
    Qed.

    Lemma cs_out_nil_le :
      forall dlt cs1 cs2, cs_out dlt [] cs1 cs2 -> cs_le dlt cs1 cs2.
    Proof.
      intros dlt cs1 cs2 H.
      induction H as [|c1 c2 l1 l2 ((t1 & t2 & Ht1 & Ht2 & Hdt & _)
                                    & _ & Hdom) Hr IH];
        [constructor|].
      constructor; [|exact IH].
      destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
      simpl in Ht1, Ht2, Hdom. subst tg1 tg2.
      split.
      - specialize (Hdom [] (fun y Hy => Hy)). exact Hdom.
      - destruct Hdt as [[]|Hdt]. exact Hdt.
    Qed.

    (** One output, renamed differently on the two sides. *)

    Lemma subst_ident_constraints_out :
      forall dlt rest x o b cs1 cs2 d1 d2 sa sa' sb sb',
        cs_out dlt (x :: rest) cs1 cs2 ->
        ~ In x rest ->
        amb_pair dlt o b ->
        ~ In o (x :: rest) -> ~ In b (x :: rest) ->
        SIG.subst_ident_constraints cs1 x o sa = OK (d1, sa') ->
        SIG.subst_ident_constraints cs2 x b sb = OK (d2, sb') ->
        cs_out dlt rest d1 d2.
    Proof.
      intros dlt rest x o b cs1 cs2 d1 d2 sa sa' sb sb'
        Hout Hxr Hdob Hno Hnb H1 H2.
      unfold SIG.subst_ident_constraints in H1, H2.
      revert d1 d2 sa sa' sb sb' H1 H2.
      induction Hout as [|c1 c2 l1 l2
                          ((t1 & t2 & Ht1 & Ht2 & Hdt & Hteq) & Hiff & Hdom)
                          Hr IH];
        intros d1 d2 sa sa' sb sb' H1 H2.
      - simpl in H1, H2. unfold ret in H1, H2. inv H1. inv H2. constructor.
      - simpl in H1, H2.
        eapply sec_bind_inv in H1 as (e1 & u1 & He1 & H1).
        eapply sec_bind_inv in H1 as (r1 & w1 & Hr1 & Hret1).
        unfold ret in Hret1. inv Hret1.
        eapply sec_bind_inv in H2 as (e2 & u2 & He2 & H2).
        eapply sec_bind_inv in H2 as (r2 & w2 & Hr2 & Hret2).
        unfold ret in Hret2. inv Hret2.
        constructor; [|eapply IH; eauto].
        destruct c1 as (s1 & tg1). destruct c2 as (s2 & tg2).
        simpl in Ht1, Ht2, Hiff, Hdom. subst tg1 tg2.
        unfold SIG.subst_ident_constraint in He1, He2.
        destruct (ident_eqb x o) eqn:Hxo; [discriminate|].
        destruct (ident_eqb x b) eqn:Hxb; [discriminate|].
        assert (x = t1 <-> x = t2) as Htt by (apply Hteq; now left).
        assert (forall y, In y (x :: rest) -> ~ In y [o]) as Hfo
          by (intros y Hy Hc; destruct Hc as [Hc|[]]; subst; now apply Hno).
        assert (forall y, In y (x :: rest) -> ~ In y [b]) as Hfb
          by (intros y Hy Hc; destruct Hc as [Hc|[]]; subst; now apply Hnb).
        destruct Hdob as (Hsob & Hsbo).
        assert ((forall y, In y rest ->
                   (In y (SIG.subst_ident_in_type s1 x [o])
                    <-> In y (SIG.subst_ident_in_type s2 x [b])))
                /\ (forall R, (forall y, In y R -> In y rest) ->
                      satisfiable dlt
                        (remove_all R (SIG.subst_ident_in_type s2 x [b]))
                        (merge amb
                           (remove_all R (SIG.subst_ident_in_type s1 x [o])))))
          as Hsrc
          by (eapply subst_type_step with (rest := rest);
              [exact Hiff|exact Hdom|exact Hxr|exact Hfo|exact Hfb|exact Hsob]).
        destruct (ident_eqb x t1) eqn:Hx1; destruct (ident_eqb x t2) eqn:Hx2.
        + (** both targets are this formal: both get renamed *)
          unfold ret in He1, He2. inv He1. inv He2.
          split; [|exact Hsrc].
          exists o, b. simpl.
          split; [reflexivity|split; [reflexivity|split; [now right|]]].
          intros y Hy. split.
          * intros ?; subst. exfalso. apply Hno. now right.
          * intros ?; subst. exfalso. apply Hnb. now right.
        + exfalso. apply ident_eqb_eq in Hx1.
          apply ident_eqb_neq in Hx2. apply Hx2, Htt, Hx1.
        + exfalso. apply ident_eqb_eq in Hx2.
          apply ident_eqb_neq in Hx1. apply Hx1, Htt, Hx2.
        + (** neither is: the targets stay where they were *)
          unfold ret in He1, He2. inv He1. inv He2.
          split; [|exact Hsrc].
          exists t1, t2. simpl.
          split; [reflexivity|split; [reflexivity|split; [|]]].
          { destruct Hdt as [[Hc|Hc]|Hc]; [|now left|now right].
            exfalso. apply ident_eqb_neq in Hx1. now apply Hx1. }
          intros y Hy. apply Hteq. now right.
    Qed.

    Lemma subst_out_map_cons_eq :
      forall cs x xs v vs,
        SIG.subst_constraints_out_map cs (x :: xs) (v :: vs)
        = match findST cs v with
          | Some _ =>
              SC.error (MSG "Output substitution captures an existing RHS identifier: "
                        :: [CTX v])
          | None => (do cs' <- SIG.subst_ident_constraints cs x v;
                     SIG.subst_constraints_out_map cs' xs vs)
          end.
    Proof. reflexivity. Qed.

    Lemma subst_out_map_nil_eq :
      forall cs, SIG.subst_constraints_out_map cs [] [] = SC.ret cs.
    Proof. reflexivity. Qed.

    Lemma subst_out_map_nil_cons_eq :
      forall cs v vs,
        SIG.subst_constraints_out_map cs [] (v :: vs)
        = SC.error (msg "Malformed replace map").
    Proof. reflexivity. Qed.

    Lemma subst_out_map_cons_nil_eq :
      forall cs x xs,
        SIG.subst_constraints_out_map cs (x :: xs) []
        = SC.error (msg "Malformed replace map").
    Proof. reflexivity. Qed.

    Lemma subst_constraints_out_map_out :
      forall dlt xs os bs cs1 cs2 d1 d2 sa sa' sb sb',
        NoDup xs ->
        cs_out dlt xs cs1 cs2 ->
        (forall y, In y xs -> ~ In y os) ->
        (forall y, In y xs -> ~ In y bs) ->
        Forall2 (amb_pair dlt) os bs ->
        SIG.subst_constraints_out_map cs1 xs os sa = OK (d1, sa') ->
        SIG.subst_constraints_out_map cs2 xs bs sb = OK (d2, sb') ->
        cs_out dlt [] d1 d2.
    Proof.
      intros dlt xs. revert dlt.
      induction xs as [|x xs IH];
        intros dlt os bs cs1 cs2 d1 d2 sa sa' sb sb'
          Hnd Hout Hfo Hfb Hob H1 H2.
      - destruct os as [|o os].
        + inv Hob. rewrite subst_out_map_nil_eq in H1, H2.
          unfold SC.ret in H1, H2. inv H1. inv H2. exact Hout.
        + rewrite subst_out_map_nil_cons_eq in H1.
          unfold SC.error in H1. discriminate H1.
      - destruct os as [|o os].
        + rewrite subst_out_map_cons_nil_eq in H1.
          unfold SC.error in H1. discriminate H1.
        + inversion Hob as [|o0 b0 os0 bs0 Hob0 Hobr]; subst.
          rewrite subst_out_map_cons_eq in H1, H2.
          destruct (findST cs1 o) as [sx|] eqn:Hf1;
            try rewrite Hf1 in H1; simpl in H1.
          { inv H1. }
          destruct (findST cs2 b0) as [sy|] eqn:Hf2;
            try rewrite Hf2 in H2; simpl in H2.
          { inv H2. }
          eapply sec_bind_inv in H1 as (e1 & u1 & He1 & H1).
          eapply sec_bind_inv in H2 as (e2 & u2 & He2 & H2).
          inv Hnd.
          eapply IH; [assumption| | | |exact Hobr|exact H1|exact H2].
          * eapply subst_ident_constraints_out;
              [exact Hout|assumption|exact Hob0| | |exact He1|exact He2].
            -- intro Hc. eapply (Hfo o); [exact Hc|now left].
            -- intro Hc. eapply (Hfb b0); [exact Hc|now left].
          * intros y Hy Hc. eapply (Hfo y); [now right|now right].
          * intros y Hy Hc. eapply (Hfb y); [now right|now right].
    Qed.

    Lemma wf_constraints_singleton_targets :
      forall cs, wf_constraints cs -> Forall (fun c => exists t, snd c = [t]) cs.
    Proof.
      intros cs (_ & Hall). eapply Forall_impl; [|exact Hall].
      intros (s & r) Hr. simpl in *.
      destruct r as [|t [|]]; simpl in Hr; try discriminate. now exists t.
    Qed.

    (** * Instantiation is monotone in the actuals

        The lemma the call case needs, and the one [SIFSignature.v]'s
        [generate_constraints_mono_inp] does not supply.  Weaken the actual
        arguments -- not by dropping names, which is what the syntactic
        version asks, but by dominating them under a valuation -- and the
        generated obligations weaken with them.

        The pipeline is walked once through [cs_chain], which carries the two
        sides' sources through the input map, the clock, the reset and the
        outputs.  The final lookup pass is not walked at all: what transfers
        is satisfaction of a whole constraint list, and [SIFSignature.v]
        already relates the list before the lookup to the list after it in
        both directions. *)

    Lemma generate_constraints_mono_sem :
      forall dlt sig inp1 inp2 clk1 clk2 rst1 rst2 os bs cns1 cns2
             sa sa' sb sb',
        signature_good sig ->
        NoDup (sig.(s_in) ++ sig.(s_clk) :: sig.(s_reset) :: sig.(s_out)) ->
        (forall y, In y (sig.(s_in) ++ sig.(s_clk) :: sig.(s_reset)
                         :: sig.(s_out)) ->
           Forall (fun v => ~ In y v) inp1 /\ Forall (fun v => ~ In y v) inp2
           /\ ~ In y clk1 /\ ~ In y clk2 /\ ~ In y rst1 /\ ~ In y rst2
           /\ ~ In y os /\ ~ In y bs) ->
        Forall2 (fun t1 t2 => satisfiable dlt t2 (merge amb t1)) inp1 inp2 ->
        satisfiable dlt clk2 (merge amb clk1) ->
        satisfiable dlt rst2 (merge amb rst1) ->
        Forall2 (amb_pair dlt) os bs ->
        generate_constraints sig inp1 clk1 rst1 os sa = OK (cns1, sa') ->
        generate_constraints sig inp2 clk2 rst2 bs sb = OK (cns2, sb') ->
        listSatisfiable dlt cns1 -> listSatisfiable dlt cns2.
    Proof.
      intros dlt sig inp1 inp2 clk1 clk2 rst1 rst2 os bs cns1 cns2
        sa sa' sb sb'
        Hgood Hnd Hfresh Hinp Hclk Hrst Hob H1 H2 Hsat1.
      destruct Hgood as (Hwf0 & Hperm0).
      unfold generate_constraints in H1, H2.
      eapply sec_bind_inv in H1 as (a1 & t1 & Ha1 & H1).
      eapply sec_bind_inv in H1 as (b1 & u1 & Hb1 & H1).
      eapply sec_bind_inv in H1 as (c1 & v1 & Hc1 & H1).
      eapply sec_bind_inv in H1 as (e1 & w1 & He1 & Hr1).
      eapply sec_bind_inv in H2 as (a2 & t2 & Ha2 & H2).
      eapply sec_bind_inv in H2 as (b2 & u2 & Hb2 & H2).
      eapply sec_bind_inv in H2 as (c2 & v2 & Hc2 & H2).
      eapply sec_bind_inv in H2 as (e2 & w2 & He2 & Hr2).

      (** the formals are distinct, phase by phase *)
      assert (NoDup (sig.(s_clk) :: sig.(s_reset) :: sig.(s_out))) as Hnd2
        by (eapply NoDup_app_r; exact Hnd).
      inversion Hnd2 as [|z1 zs1 Hnclk Hnd3]; subst.
      inversion Hnd3 as [|z2 zs2 Hnrst Hnd4]; subst.

      (** the targets are untouched until the output map *)
      assert (map snd c1 = map snd sig.(s_constraints)) as Hrhs1.
      { erewrite (subst_ident_in_constraints_rhs _ _ _ _ _ _ Hc1),
          (subst_ident_in_constraints_rhs _ _ _ _ _ _ Hb1),
          (SIGPROOFS.subst_constraints_inp_map_rhs _ _ _ _ _ _ Ha1). reflexivity. }
      assert (Permutation (map snd c1) (map (fun y => [y]) sig.(s_out)))
        as Hpc1 by (rewrite Hrhs1; exact Hperm0).
      assert (wf_constraints c1) as Hwfc1
        by (eapply SIGPROOFS.wf_constraints_of_singleton_perm; eauto).

      (** the substitution chain, run as far as the outputs *)
      assert (cs_chain dlt (sig.(s_clk) :: sig.(s_reset) :: sig.(s_out)) a1 a2)
        as Hcha.
      { eapply subst_constraints_inp_map_chain;
          [exact Hnd|apply cs_chain_refl| | |exact Hinp|exact Ha1|exact Ha2].
        - apply Forall_forall. intros v Hv y Hy.
          apply Hfresh in Hy as (Hy1 & _).
          rewrite Forall_forall in Hy1. now apply Hy1.
        - apply Forall_forall. intros v Hv y Hy.
          apply Hfresh in Hy as (_ & Hy2 & _).
          rewrite Forall_forall in Hy2. now apply Hy2. }
      assert (cs_chain dlt (sig.(s_reset) :: sig.(s_out)) b1 b2) as Hchb.
      { eapply subst_ident_in_constraints_chain;
          [exact Hcha|exact Hnclk| | |exact Hclk|exact Hb1|exact Hb2].
        - intros y Hy. apply Hfresh. apply in_or_app. now right.
        - intros y Hy. apply Hfresh. apply in_or_app. now right. }
      assert (cs_chain dlt sig.(s_out) c1 c2) as Hchc.
      { eapply subst_ident_in_constraints_chain;
          [exact Hchb|exact Hnrst| | |exact Hrst|exact Hc1|exact Hc2].
        - intros y Hy. apply Hfresh. apply in_or_app. right. now right.
        - intros y Hy. apply Hfresh. apply in_or_app. right. now right. }

      (** the output map *)
      assert (cs_out dlt [] e1 e2) as Hout.
      { eapply subst_constraints_out_map_out;
          [exact Hnd4| | | |exact Hob|exact He1|exact He2].
        - apply cs_chain_out; [exact Hchc|].
          apply singleton_targets_of_perm; exact Hpc1.
        - intros y Hy. apply Hfresh. apply in_or_app. right.
          right. now right.
        - intros y Hy. apply Hfresh. apply in_or_app. right.
          right. now right. }

      (** and the lookup pass, which is not walked but transferred *)
      destruct (SIGPROOFS.subst_constraints_out_map_shape _ _ _ _ _ _ Hwfc1 Hpc1 He1)
        as (Hwfe1 & Hperme1).
      assert (listSatisfiable dlt e1) as Hse1
        by (eapply SIGPROOFS.reorder_constraints_complete;
            [exact Hwfe1|exact Hperme1|exact Hr1|exact Hsat1]).
      assert (listSatisfiable dlt e2) as Hse2
        by (eapply cs_le_satisfaction; [apply cs_out_nil_le; exact Hout|exact Hse1]).
      eapply SIGPROOFS.reorder_constraints_correct; [exact Hr2|exact Hse2].
    Qed.

    (** * Instantiation is monotone in the actuals, with the augmentation

        The design in force, packaged: leave [generate_constraints_mono_sem]
        untouched and feed it the *augmented* source actuals, which is what
        makes its uniform ambient large enough for every argument.  The four
        steps are

          1. build the augmented run    [generate_constraints_total_inp];
          2. its sources agree with the plain one's
             [subst_constraints_inp_map_augment] propagated by
             [generate_constraints_same_inp];
          3. carry satisfaction across  [listSatisfiable_same_sources];
          4. transport to the target    [generate_constraints_mono_sem].

        Everything the caller has to supply is a fact about the call site. *)
    Lemma generate_constraints_mono_sem_aug :
      forall dlt sg (ins : list (ident * clock)) (sub : ident -> option ident)
             (argts : list LST) (inp2 : list SymTypes.ST)
             clk1 clk2 rst1 rst2 os bs cns1 cns2 sa sa' sb sb',
        signature_good sg ->
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
        List.length ins = List.length argts ->
        (** freshness, for the plain actuals and everything else *)
        (forall y, In y (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
           Forall (fun v => ~ In y v) (List.map fst argts)
           /\ Forall (fun v => ~ In y v) inp2
           /\ ~ In y clk1 /\ ~ In y clk2 /\ ~ In y rst1 /\ ~ In y rst2
           /\ ~ In y os /\ ~ In y bs) ->
        (** and for the augmented ones, which [augment_actuals_fresh] gives *)
        Forall (fun v => forall y,
                    In y (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out))
                    -> ~ In y v)
          (augment_actuals sub ins argts) ->
        (** the premise the augmentation exists for: the target actual is
            dominated by the *augmented* source actual under the call's own
            ambient *)
        Forall2 (fun t1 t2 => satisfiable dlt t2 (merge amb t1))
          (augment_actuals sub ins argts) inp2 ->
        satisfiable dlt clk2 (merge amb clk1) ->
        satisfiable dlt rst2 (merge amb rst1) ->
        Forall2 (amb_pair dlt) os bs ->
        (** and that augmenting changes no source *)
        (forall c, In c sg.(s_constraints) ->
           forall y w', In (y, w') (combine sg.(s_in)
                                      (augment_actuals sub ins argts)) ->
             In y (fst c) ->
             forall z, In z w' ->
               exists y2 w2, In (y2, w2) (combine sg.(s_in)
                                            (List.map fst argts))
                             /\ In y2 (fst c) /\ In z w2) ->
        generate_constraints sg (List.map fst argts) clk1 rst1 os sa
          = OK (cns1, sa') ->
        generate_constraints sg inp2 clk2 rst2 bs sb = OK (cns2, sb') ->
        listSatisfiable dlt cns1 -> listSatisfiable dlt cns2.
    Proof.
      intros dlt sg ins sub argts inp2 clk1 clk2 rst1 rst2 os bs cns1 cns2
        sa sa' sb sb' Hgood Hnd Hlen Hfresh Hfaug Hrel Hclk Hrst Hob Hdep
        H1 H2 Hsat1.
      assert (NoDup sg.(s_in)) as Hndin by (eapply NoDup_app_l; exact Hnd).
      (** the plain and augmented actual lists have the same length *)
      assert (List.length (List.map fst argts)
              = List.length (augment_actuals sub ins argts)) as Hlaug.
      { assert (forall (A B : Type) (l1 : list A) (l2 : list B),
                   List.length l1 = List.length l2 ->
                   List.length (combine l1 l2) = List.length l2) as Hcl.
        { intros A B l1. induction l1 as [|a l1 IH]; intros l2 Hl.
          - destruct l2; [reflexivity|discriminate].
          - destruct l2 as [|b l2]; [discriminate|].
            simpl. f_equal. apply IH. simpl in Hl; congruence. }
        unfold augment_actuals. rewrite !map_length.
        symmetry. exact (Hcl _ _ ins argts Hlen). }
      (** 1. the augmented run exists *)
      destruct (generate_constraints_total_inp sg (List.map fst argts)
                  (augment_actuals sub ins argts) clk1 rst1 os cns1 sa sa' sa
                  Hlaug H1) as (cnsa & Ha).
      (** the freshness both stages of the augmentation argument want *)
      assert (Forall (fun v => forall y, In y sg.(s_in) -> ~ In y v)
                (List.map fst argts)) as Hfp.
      { apply Forall_forall. intros v Hv y Hy Hc.
        destruct (Hfresh y (in_or_app _ _ _ (or_introl Hy))) as (Hp & _).
        rewrite Forall_forall in Hp. exact (Hp v Hv Hc). }
      assert (Forall (fun v => forall y, In y sg.(s_in) -> ~ In y v)
                (augment_actuals sub ins argts)) as Hfa.
      { eapply Forall_impl; [|exact Hfaug].
        intros v Hv y Hy. exact (Hv y (in_or_app _ _ _ (or_introl Hy))). }
      (** 2. the two input-map results agree as sets *)
      assert (forall a1 a2 t1 t2,
                 SIG.subst_constraints_inp_map sg.(s_constraints) sg.(s_in)
                   (List.map fst argts) sa = OK (a1, t1) ->
                 SIG.subst_constraints_inp_map sg.(s_constraints) sg.(s_in)
                   (augment_actuals sub ins argts) sa = OK (a2, t2) ->
                 cs_same_src a1 a2) as Hsame.
      { intros a1 a2 t1 t2 Hp1 Hp2.
        assert (Forall2
                  (fun a b =>
                     (forall z, In z (fst a) <-> In z (fst b))
                     /\ (forall z, In z (snd a) <-> In z (snd b))) a1 a2)
          as Hrelset
            by (eapply subst_constraints_inp_map_augment;
                [exact Hndin|exact Hfp|exact Hfa
                |exact (augment_actuals_grows sub ins argts Hlen)
                |exact Hdep|exact Hp1|exact Hp2]).
        assert (List.map snd a1 = List.map snd a2) as Ht.
        { rewrite (subst_constraints_inp_map_targets sg.(s_in)
                     sg.(s_constraints) (List.map fst argts) a1 sa t1 Hp1).
          rewrite (subst_constraints_inp_map_targets sg.(s_in)
                     sg.(s_constraints) (augment_actuals sub ins argts) a2
                     sa t2 Hp2).
          reflexivity. }
        unfold cs_same_src.
        clear Hp1 Hp2. revert Ht.
        induction Hrelset as [|a b l l' (Hs & _) Hr IH]; intro Ht;
          [constructor|].
        simpl in Ht. injection Ht as Htc Htr.
        constructor; [split; [now symmetry|exact Hs]|exact (IH Htr)]. }
      (** 3. satisfaction carries to the augmented run *)
      assert (listSatisfiable dlt cnsa) as Hsata.
      { eapply listSatisfiable_same_sources; [|exact Hsat1].
        eapply generate_constraints_same_inp;
          [ |  |exact Hsame|exact H1|exact Ha].
        - assert (In sg.(s_clk)
                    (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)))
            as Hin by (apply in_or_app; right; now left).
          destruct (Hfresh sg.(s_clk) Hin) as (_ & _ & Hc & _). exact Hc.
        - assert (In sg.(s_reset)
                    (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)))
            as Hin by (apply in_or_app; right; right; now left).
          destruct (Hfresh sg.(s_reset) Hin) as (_ & _ & _ & _ & Hc & _).
          exact Hc. }
      (** 4. and transports to the target *)
      eapply generate_constraints_mono_sem;
        [exact Hgood|exact Hnd| |exact Hrel|exact Hclk|exact Hrst|exact Hob
        |exact Ha|exact H2|exact Hsata].
      intros y Hy. destruct (Hfresh y Hy) as (_ & Hp2 & Hc1 & Hc2 & Hr1 & Hr2
                                              & Ho & Hb).
      repeat split; try assumption.
      rewrite Forall_forall in Hfaug |- *. intros v Hv.
      exact (Hfaug v Hv y Hy).
    Qed.



    (** * The no-op arguments

        Between unnesting a call's arguments and emitting the call,
        [unnest_noops_exps] walks the arguments once more: an argument whose
        shape the transcription can carry as a sub-expression is kept, and any
        other is bound to a fresh variable and emitted.  So the step is
        selective -- unlike [Efby]'s, which lifts every result -- and the two
        branches have to be related separately.

        The kept branch changes nothing: the same expression, the same type,
        no equation.  The bound branch is [lifted_defs] on one element: the
        minted variable's defining equation constrains its security name above
        the ambient joined with the argument's type, and the witness is chosen
        to meet that constraint exactly. *)

    Lemma unnest_noops_exp_inv :
      forall ck e e' eqs st st',
        unnest_noops_exp ck e st = ((e', eqs), st') ->
        (e' = e /\ eqs = [] /\ st' = st)
        \/ (exists x an, e' = Evar x an
                        /\ eqs = [([x], [e])]
                        /\ Permutation (x :: st_ids st) (st_ids st')).
    Proof.
      intros ck e e' eqs st st' H.
      unfold unnest_noops_exp in H.
      destruct (hd _ _) as (ty & ck0 & o).
      destruct (is_noops_exp ck e) eqn:Enoop; repeat inv_bind.
      - left. repeat split; reflexivity.
      - right. do 2 eexists.
        split; [reflexivity|split; [reflexivity|]].
        eapply UNN.Fresh.Facts.fresh_ident_vars_perm; eauto.
    Qed.

    Lemma unnest_noops_exps_nil_l :
      forall es es2 eqs2 st st',
        unnest_noops_exps [] es st = ((es2, eqs2), st') ->
        es2 = [] /\ eqs2 = [] /\ st' = st.
    Proof.
      intros es es2 eqs2 st st' H.
      unfold unnest_noops_exps in H. simpl in H. repeat inv_bind.
      repeat split; reflexivity.
    Qed.

    Lemma unnest_noops_exps_cons :
      forall ck cks e es es2 eqs2 st st',
        unnest_noops_exps (ck :: cks) (e :: es) st = ((es2, eqs2), st') ->
        exists e2 eqh st1 es2t eqt,
          unnest_noops_exp ck e st = ((e2, eqh), st1)
          /\ unnest_noops_exps cks es st1 = ((es2t, eqt), st')
          /\ es2 = e2 :: es2t
          /\ eqs2 = eqh ++ eqt.
    Proof.
      intros ck cks e es es2 eqs2 st st' H.
      unfold unnest_noops_exps in H. simpl in H. repeat inv_bind.
      do 5 eexists. split; [eassumption|]. split; [|split; reflexivity].
      unfold unnest_noops_exps. apply bind2_spec.
      do 3 eexists. split; [eassumption|apply ret_spec].
    Qed.

    (** What one no-op step did to the fresh state: nothing, or exactly the
        one variable it bound. *)

    Lemma unnest_noops_exp_vars_perm :
      forall ck e e' eqs st st',
        unnest_noops_exp ck e st = ((e', eqs), st') ->
        Permutation (vars_defined eqs ++ st_ids st) (st_ids st').
    Proof.
      intros ck e e' eqs st st' H.
      apply unnest_noops_exp_inv in H as [(? & ? & ?)|(x & an & ? & ? & Hp)];
        subst; simpl; [reflexivity|exact Hp].
    Qed.

    (** * The no-op step, on the security side

        Between unnesting a call's arguments and emitting the call,
        [unnest_noops_exps] walks the arguments once more: one whose shape the
        transcription can carry as a sub-expression is kept, and any other is
        bound to a fresh variable.  So the step is selective -- unlike
        [Efby]'s, which lifts every result -- and the two branches are related
        separately.

        The kept branch is an identity: the arguments are already normalized,
        so the same expression has the same type at any state, and nothing is
        emitted.  The bound branch is [lifted_defs] on a one-element list --
        what it emits is literally
        [map (fun '(x, e) => ([x], [e])) (combine [x] [e])] -- so the witness
        is built there, and the only work left is carrying it past the tail. *)

    Lemma noops_step :
      forall bound ckis es1 es2 eqs2 st st' ts1 ts2 ce
             xst xst' zst zst' yst yst' dlt,
        List.length ckis = List.length es1 ->
        Forall normalized_lexp es1 ->
        unnest_noops_exps ckis es1 st = ((es2, eqs2), st') ->
        NoDup (vars_defined eqs2 ++ st_ids st) ->
        (forall b, In b (moved_by st st') -> ~ In b bound) ->
        (forall x ck ckty, In x (vars_defined eqs2) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        st_scoped bound amb ->
        assign_lexps GL env base_ty rst_ty es1 zst = OK (ts1, zst') ->
        assign_lexps GL env base_ty rst_ty es2 yst = OK (ts2, yst') ->
        Forall (fun t => st_scoped bound (fst t)) ts1 ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst
          = OK (ce, xst') ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t1 t2 => satisfiable dlt' (fst t2) (merge amb (fst t1)))
               ts1 ts2
          /\ constraints_scoped (bound ++ moved_by st st') ce
          /\ Forall (fun t2 => st_scoped (bound ++ moved_by st st') (fst t2)) ts2.
    Proof.
      intros bound ckis es1. revert bound ckis.
      induction es1 as [|e es1 IH];
        intros bound ckis es2 eqs2 st st' ts1 ts2 ce
          xst xst' zst zst' yst yst' dlt
          Hlen Hnorm Hun Hnd Hmv Hamb Hambsc Has1 Has2 Hsc1 Hgen.

      - (** nothing left: the state has not moved *)
        destruct ckis; simpl in Hlen; [|discriminate].
        apply unnest_noops_exps_nil_l in Hun as (? & ? & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has1
          as (? & _ & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has2
          as (? & _ & ?); subst.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. split; [|split; [|split; [|split]]];
          solve [apply agree_off_refl | constructor].

      - (** one argument, then the rest on top of it *)
        destruct ckis as [|ck ckis]; simpl in Hlen; [discriminate|].
        inversion Hlen as [Hlen'].
        inversion Hnorm as [|e0 es0 Hne Hnes]; subst.
        apply unnest_noops_exps_cons in Hun
          as (e2 & eqh & st1 & es2t & eqt & Hh & Ht & ? & ?); subst.
        assert (st_follows st st1) as Hf0
            by (eapply unnest_noops_exp_st_follows; eauto).
        assert (st_follows st1 st') as Hf1
            by (eapply unnest_noops_exps_st_follows; eauto).
        assert (Permutation (vars_defined eqh ++ st_ids st) (st_ids st1))
          as Hp0 by (eapply unnest_noops_exp_vars_perm; eauto).

        (** the two sides' types, head and tail *)
        apply assign_lexps_carried_cons in Has1
          as (t & r & sa & Ht0 & Hr & ? & _); subst.
        apply assign_lexps_carried_cons in Has2
          as (u & r2 & sb & Hu0 & Hr2 & ? & _); subst.
        assert (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK (t, s))
          as Hpure
            by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        assert (List.length t = 1) as Hlt
            by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        destruct t as [|t0 [|]]; simpl in Hlt; try discriminate.
        apply Forall_app in Hsc1 as (Hsc1h & Hsc1t).
        inversion Hsc1h as [|z zs Hz _]; subst.

        (** the emitted equations, head and tail *)
        apply generate_leqns_constraints_app in Hgen
          as (ceh & cet & xstm & Hgenh & Hgent & ?); subst.
        assert (NoDup (vars_defined eqt ++ st_ids st1)) as Hndt
            by (eapply NoDup_vd_app_r; [exact Hp0|exact Hnd]).

        (** the rest of the arguments *)
        edestruct (IH bound ckis es2t eqt st1 st' r r2 cet
                     xstm xst' sa zst' sb yst' dlt)
          as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hsc2t).
        { exact Hlen'. }
        { exact Hnes. }
        { exact Ht. }
        { exact Hndt. }
        { intros b Hb. apply Hmv. apply (moved_by_suffix_local st st1 st' Hf0). exact Hb. }
        { intros y cky ckty Hy. apply Hamb.
          rewrite vars_defined_app. apply in_or_app. now right. }
        { exact Hambsc. }
        { exact Hr. }
        { exact Hr2. }
        { exact Hsc1t. }
        { exact Hgent. }

        (** and the head *)
        apply unnest_noops_exp_inv in Hh
          as [(? & ? & ?)|(x & an & ? & ? & Hpx)]; subst.
        + (** kept: the same expression, so the same type, nothing emitted *)
          apply generate_leqns_constraints_nil in Hgenh as (? & ?); subst.
          rewrite (Hpure yst) in Hu0. inv Hu0.
          exists dlt1. split; [|split; [|split; [|split]]].
          * exact Hoff1.
          * exact Hce1.
          * simpl. constructor; [apply satisfiable_merge_r|exact Hrel1].
          * exact Hscope1.
          * simpl. constructor; [|exact Hsc2t].
            eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz].
        + (** bound: [lifted_defs] on the one variable it minted *)
          apply assign_lexp_Evar_inv in Hu0 as (b & Hb & ? & ?); subst.
          assert (~ In x (st_ids st)) as Hxst.
          { simpl in Hnd. inversion Hnd as [|z zs Hzn _]; subst.
            intro Hc. apply Hzn. apply in_or_app. now right. }
          assert (In x (new_ids st st1)) as Hxnew.
          { apply new_ids_spec. split; [|exact Hxst].
            eapply Permutation_in; [exact Hpx|now left]. }
          assert (In b (moved_by st st1)) as Hbmv.
          { unfold moved_by, sec_of. apply in_flat_map.
            exists x. split; [exact Hxnew|]. rewrite Hb. now left. }
          assert (forall c, In c (sec_of [x]) -> In c (moved_by st st1)) as Hbnew.
          { intros c Hc. unfold sec_of in Hc. simpl in Hc.
            rewrite Hb in Hc. destruct Hc as [|[]]; subst. exact Hbmv. }
          assert (forall c, In c (sec_of [x]) ->
                            ~ In c (bound ++ moved_by st1 st')) as Hsepx.
          { intros c Hc Hin. apply Hbnew in Hc.
            apply in_app_or in Hin as [Hin|Hin].
            - eapply (Hmv c); [|exact Hin].
              apply (moved_by_prefix_local st st1 st' Hf1). exact Hc.
            - exact (moved_by_disjoint_local st st1 st' c Hc Hin). }

          edestruct (lifted_defs_local (bound ++ moved_by st1 st') [x] [e] [t0]
                       ceh xst xstm dlt1)
            as (dlt2 & Hoff2 & Hce2 & Hscope2 & Hrel2).
          { constructor; [intros []|constructor]. }
          { reflexivity. }
          { exact Hsepx. }
          { intros y cky ckty Hy. apply Hamb.
            rewrite vars_defined_app. apply in_or_app. left.
            simpl. simpl in Hy. exact Hy. }
          { eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hambsc]. }
          { constructor; [|constructor]. split.
            - destruct e; try exact I. inv Hne.
            - intros tf s s' Htf. rewrite (Hpure s) in Htf. inv Htf.
              split; [reflexivity|split; [reflexivity|]].
              eapply assign_lexp_normalized_lexp_pure with (e := e); eauto. }
          { constructor; [|constructor].
            eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz]. }
          { constructor; [|constructor]. intros tf s s' Htf.
            rewrite (Hpure s) in Htf. inv Htf.
            split; [apply satisfiable_merge_r|].
            eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz]. }
          { exact Hgenh. }

          (** the head's witness, carried over the tail's *)
          assert (satisfiable dlt2 [b] (merge amb (fst t0))) as Hhead.
          { inversion Hrel2 as [|p q ps qs Hpq _]; subst. now apply Hpq. }
          assert (incl (sec_of [x]) (moved_by st st')) as Hincx.
          { intros c Hc. apply (moved_by_prefix_local st st1 st' Hf1).
            now apply Hbnew. }
          exists dlt2. split; [|split; [|split; [|split]]].
          * eapply agree_off_trans.
            -- eapply agree_off_incl; [|exact Hoff1].
               apply (moved_by_suffix_local st st1 st' Hf0).
            -- eapply agree_off_incl; [|exact Hoff2]. exact Hincx.
          * apply listSatisfiable_app. split; [exact Hce2|].
            eapply listSatisfiable_off_scope
              with (sc := bound ++ moved_by st1 st') (xs := sec_of [x]); eauto.
          * simpl. constructor.
            -- exact Hhead.
            -- eapply Forall2_impl_In; [|exact Hrel1].
               intros p q Hp Hq Hpq.
               eapply satisfiable_off with (xs := sec_of [x]); eauto.
               ++ intros c Hc Hin. apply (Hsepx c Hin).
                  eapply Forall_forall in Hsc2t; [|exact Hq]. now apply Hsc2t.
               ++ intros c Hc Hin. apply in_merge_inv in Hc as [Hc|Hc].
                  ** apply (Hsepx c Hin). apply in_or_app. left.
                     now apply Hambsc.
                  ** apply (Hsepx c Hin). apply in_or_app. left.
                     eapply Forall_forall in Hsc1t; [|exact Hp]. now apply Hsc1t.
          * apply Forall_app. split.
            -- eapply Forall_impl; [|exact Hscope2].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app;
                 [|eapply incl_tran; [exact Hincx|apply incl_appr, incl_refl]].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr, (moved_by_suffix_local st st1 st' Hf0).
            -- eapply Forall_impl; [|exact Hscope1].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr, (moved_by_suffix_local st st1 st' Hf0).
          * simpl. constructor.
            -- intros c Hc. destruct Hc as [|[]]; subst.
               apply in_or_app. right. apply Hincx.
               unfold sec_of. simpl. rewrite Hb. now left.
            -- eapply Forall_impl; [|exact Hsc2t].
               intros q Hq. eapply st_scoped_weaken; [|exact Hq].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr, (moved_by_suffix_local st st1 st' Hf0).
    Qed.

    (** * The reset of a call

        [unnest_reset] keeps the reset when what it unnests to is already a
        variable, and otherwise binds it to one.  Either way the call that is
        emitted has a variable for its reset, and what the security side has
        to produce is the level of that variable: dominated by the ambient
        joined with what the source reset expression carried.

        The kept branch is the induction hypothesis read off a one-element
        list.  The bound branch is the same, with [lifted_defs] on the one
        variable in between -- which costs one more join of the ambient, and
        the ambient is idempotent. *)

    Lemma reset_step :
      forall (P : global) e1 r an rty eqs3 st st' a1 sst sst' ce xst xst'
             (yst : sec_state) dlt,
        carries P e1 ->
        wl_exp P e1 -> wc_exp P vars e1 -> numstreams e1 = 1 ->
        unnest_reset (unnest_exp P true) (Some e1) st
          = ((Some (Evar r an), eqs3), st') ->
        Env.find r env = Some rty ->
        NoDup (vars_defined eqs3 ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty, In x (vars_defined eqs3) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        assign_lexp_type GL env base_ty rst_ty e1 sst = OK ([a1], sst') ->
        constraints_scoped scope (carried [a1]) ->
        st_scoped scope (fst a1) ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs3 xst
          = OK (ce, xst') ->
        listSatisfiable dlt (carried [a1]) ->
        (** the checkmark bound, as [carries] asks for it *)
        sec_le sst' stF -> sec_le stLo sst ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ satisfiable dlt' [rty] (merge amb (fst a1))
          /\ In rty (scope ++ moved_by st st')
          /\ constraints_scoped (scope ++ moved_by st st') ce.
    Proof.
      intros P e1 r an rty eqs3 st st' a1 sst sst' ce xst xst' yst dlt
        Hcar Hwl Hwc Hns Hun Hr Hnd Hmv Hamb Hty Hsc Hsct Hgen Hsat Hbnd Hlow.
      pose proof Hun as Hun0.
      destruct (unnest_exp P true e1 st) as [[es' eqs1] st1] eqn:Hk.
      pose proof Hk as Hk0.
      eapply unnest_reset_spec in Hk
        as [(v & a & Ehd & Hnorm)
           |(ty0 & ck0 & o0 & x & st2 & Hhd & Hfresh & Hnorm)];
        rewrite Hnorm in Hun0; inv Hun0.

      - (** kept: the unnested reset is already a variable *)
        assert (List.length es' = 1) as Hlen
            by (erewrite unnest_exp_length; eauto).
        destruct es' as [|e0 [|]]; simpl in Hlen; try discriminate.
        simpl in Ehd. subst e0.
        assert (assign_lexps GL env base_ty rst_ty [Evar r an] yst
                  = OK ([(([rty] : ST), [])], yst)) as Hasr.
        { apply assign_lexps_single_intro.
          simpl. unfold find_env. rewrite Hr. reflexivity. }
        edestruct (Hcar true [Evar r an] eqs3 st st' [a1] sst sst'
                     ce xst xst' [(([rty] : ST), [])] yst yst dlt)
          as (dlt' & Hoff & Hce & Hrel & Hscope & Hts);
          try assumption.
        { constructor; [exact Hsct|constructor]. }
        exists dlt'. split; [exact Hoff|split; [exact Hce|split]].
        + inversion Hrel as [|p q ps qs Hpq _]; subst. exact Hpq.
        + split; [|exact Hscope].
          inversion Hts as [|z zs Hz _]; subst. apply Hz. now left.

      - (** bound: one more variable, and [lifted_defs] on it *)
        assert (List.length es' = 1) as Hlen
            by (erewrite unnest_exp_length; eauto).
        destruct es' as [|e0 [|]]; simpl in Hlen; try discriminate.
        simpl hd_default in *.
        assert (normalized_cexp e0) as Hne0.
        { assert (Forall normalized_cexp [e0]) as Hall
              by (eapply unnest_exp_normalized_cexp; eauto).
          now inv Hall. }
        assert (st_follows st st1) as Hf0
            by (eapply unnest_exp_st_follows; eauto).
        assert (st_follows st1 st') as Hf1
            by (eapply UNN.Fresh.fresh_ident_st_follows; eauto).
        assert (Permutation (r :: st_ids st1) (st_ids st')) as Hpx
            by (eapply UNN.Fresh.Facts.fresh_ident_vars_perm; eauto).

        (** the emitted equations: the binding, then the reset's own *)
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (ceh & xstm & Hgenh & Hgen).
        eapply sec_bind_inv in Hgen as (cet & xstn & Hgent & Hret).
        unfold SC.ret in Hret. inv Hret.
        pose proof Hgenh as Hgenh0.
        rewrite generate_leqn_constraint_def in Hgenh0
          by (destruct e0; try exact I; inv Hne0; inv H).
        apply generate_ldef_constraint_inv in Hgenh0
          as (ck1 & ckty1 & sa & rb & stm2 & Hck1 & Hcl1 & Hte0 & Hb & Hceh).
        assert (carried [sa] = [] /\ forall s,
                   assign_lexp_type GL env base_ty rst_ty e0 s = OK ([sa], s))
          as (Hsnd & Hpure).
        { eapply assign_lexp_normalized_cexp_pure in Hte0
            as (? & _ & Hcr & Hs); eauto. }

        assert (NoDup (vars_defined eqs1 ++ st_ids st)) as Hnd1
            by (simpl in Hnd; now inv Hnd).
        edestruct (Hcar true [e0] eqs1 st st1 [a1] sst sst'
                     cet xstm xst' [sa] yst yst dlt)
          as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
        { exact Hwl. }
        { exact Hwc. }
        { exact Hnd1. }
        { intros y Hy. apply Hmv. apply (moved_by_prefix_local st st1 st' Hf1). exact Hy. }
        { exact Hsc. }
        { constructor; [exact Hsct|constructor]. }
        { intros y cky ckty Hy. apply Hamb. simpl. now right. }
        { exact Hk0. }
        { exact Hty. }
        { exact Hgent. }
        { apply assign_lexps_single_intro. apply (Hpure yst). }
        { exact Hsat. }
        { exact Hbnd. }
        { first [exact Hlow | (eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec)]. }

        assert (satisfiable dlt1 (fst sa) (merge amb (fst a1))) as Hsa
            by (inversion Hrel1 as [|p q ps qs Hpq _]; subst; exact Hpq).
        assert (st_scoped (scope ++ moved_by st st1) (fst sa)) as Hsasc
            by (inversion Hts1 as [|z zs Hz _]; subst; exact Hz).

        (** the variable the reset was bound to *)
        assert (Permutation (vars_defined eqs1 ++ st_ids st) (st_ids st1))
          as Hp1 by (eapply unnest_exp_vars_perm; eauto).
        assert (~ In r (st_ids st1)) as Hrst.
        { simpl in Hnd. inversion Hnd as [|z zs Hzn _]; subst.
          intro Hc. apply Hzn.
          eapply Permutation_in; [symmetry; exact Hp1|exact Hc]. }
        assert (In r (new_ids st1 st')) as Hrnew.
        { apply new_ids_spec. split; [|exact Hrst].
          eapply Permutation_in; [exact Hpx|now left]. }
        assert (In rty (moved_by st1 st')) as Hrtymv.
        { unfold moved_by, sec_of. apply in_flat_map.
          exists r. split; [exact Hrnew|]. rewrite Hr. now left. }
        assert (forall c, In c (sec_of [r]) -> In c (moved_by st1 st')) as Hbnew.
        { intros c Hc. unfold sec_of in Hc. simpl in Hc.
          rewrite Hr in Hc. destruct Hc as [|[]]; subst. exact Hrtymv. }
        assert (forall c, In c (sec_of [r]) ->
                          ~ In c (scope ++ moved_by st st1)) as Hsepx.
        { intros c Hc Hin. apply Hbnew in Hc.
          apply in_app_or in Hin as [Hin|Hin].
          - eapply (Hmv c); [|exact Hin].
            apply (moved_by_suffix_local st st1 st' Hf0). exact Hc.
          - exact (moved_by_disjoint_local st st1 st' c Hin Hc). }

        edestruct (lifted_defs_local (scope ++ moved_by st st1) [r] [e0] [sa]
                     ceh xst xstm dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2 & Hrel2).
        { constructor; [intros []|constructor]. }
        { reflexivity. }
        { exact Hsepx. }
        { intros y cky ckty Hy. apply Hamb. simpl.
          destruct Hy as [Hy|[]]. now left. }
        { eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact amb_scoped]. }
        { constructor; [|constructor]. split.
          - destruct e0; try exact I; inv Hne0; inv H.
          - intros tf s s' Htf. rewrite (Hpure s) in Htf. inv Htf.
            split; [reflexivity|split; [reflexivity|exact Hsnd]]. }
        { constructor; [|constructor]. exact Hsasc. }
        { constructor; [|constructor]. intros tf s s' Htf.
          rewrite (Hpure s) in Htf. inv Htf.
          split; [apply satisfiable_merge_r|exact Hsasc]. }
        { assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                    [([r], [e0])] xst = OK (ceh, xstm)) as Hgenh1.
          { rewrite generate_leqns_constraints_cons.
            eapply sec_bind_ok; [exact Hgenh|].
            eapply sec_bind_ok with (y := ([] : list SymTypes.constraint));
              [reflexivity|].
            unfold SC.ret. now rewrite app_nil_r. }
          exact Hgenh1. }

        assert (satisfiable dlt2 [rty] (merge amb (fst sa))) as Hhead.
        { inversion Hrel2 as [|p q ps qs Hpq _]; subst. now apply Hpq. }
        assert (incl (sec_of [r]) (moved_by st st')) as Hincx
            by (intros c Hc; apply (moved_by_suffix_local st st1 st' Hf0);
                now apply Hbnew).

        exists dlt2. split; [|split; [|split; [|split]]].
        + eapply agree_off_trans.
          * eapply agree_off_incl; [|exact Hoff1].
            apply (moved_by_prefix_local st st1 st' Hf1).
          * eapply agree_off_incl; [|exact Hoff2]. exact Hincx.
        + apply listSatisfiable_app. split; [exact Hce2|].
          eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1) (xs := sec_of [r]); eauto.
        + eapply satisfiable_trans; [exact Hhead|].
          apply satisfiable_merge_intro; [apply satisfiable_merge_l|].
          eapply satisfiable_off with (xs := sec_of [r]); eauto.
          * intros c Hc Hin. apply (Hsepx c Hin). now apply Hsasc.
          * intros c Hc Hin. apply in_merge_inv in Hc as [Hc|Hc].
            -- apply (Hsepx c Hin). apply in_or_app. left. now apply amb_scoped.
            -- apply (Hsepx c Hin). apply in_or_app. left. now apply Hsct.
        + apply in_or_app. right. apply Hincx.
          unfold sec_of. simpl. rewrite Hr. now left.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope2].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app;
              [|eapply incl_tran; [exact Hincx|apply incl_appr, incl_refl]].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix_local st st1 st' Hf1).
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix_local st st1 st' Hf1).
    Qed.

    (** The unnested arguments' types, read back off what came after them.
        [carries_list] needs the types of the arguments as [unnest_exp] left
        them, but nothing computes those: the source side types the *source*
        arguments and the emitted call types the *no-opped* ones.  Both ends
        are available, and between them every argument is accounted for --
        one that the no-op pass kept has the type the emitted call gave it,
        and one that it bound has the type the equation it emitted
        computed. *)

    Lemma noops_operand_types :
      forall ckis es1 es2 eqs2 st st' ce xst xst' ts2 (yst yst' : sec_state),
        List.length ckis = List.length es1 ->
        Forall normalized_lexp es1 ->
        unnest_noops_exps ckis es1 st = ((es2, eqs2), st') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty es2 yst = OK (ts2, yst') ->
        exists ts1,
          forall s, assign_lexps GL env base_ty rst_ty es1 s = OK (ts1, s).
    Proof.
      intros ckis es1. revert ckis.
      induction es1 as [|e es1 IH];
        intros ckis es2 eqs2 st st' ce xst xst' ts2 yst yst'
          Hlen Hnorm Hun Hgen Has2.
      - exists []. intros s. now rewrite assign_lexps_nil.
      - destruct ckis as [|ck ckis]; simpl in Hlen; [discriminate|].
        inversion Hlen as [Hlen'].
        inversion Hnorm as [|e0 es0 Hne Hnes]; subst.
        apply unnest_noops_exps_cons in Hun
          as (e2 & eqh & st1 & es2t & eqt & Hh & Ht & ? & ?); subst.
        apply assign_lexps_carried_cons in Has2
          as (u & r2 & sb & Hu0 & Hr2 & ? & _); subst.
        apply generate_leqns_constraints_app in Hgen
          as (ceh & cet & xstm & Hgenh & Hgent & ?); subst.

        assert (exists t0, forall s,
                   assign_lexp_type GL env base_ty rst_ty e s = OK ([t0], s))
          as (t0 & Ht0).
        { apply unnest_noops_exp_inv in Hh
            as [(? & ? & ?)|(x & an & ? & ? & _)]; subst.
          - assert (List.length u = 1) as Hlu
                by (eapply assign_lexp_normalized_lexp_pure with (e := e);
                    eauto).
            destruct u as [|t0 [|]]; simpl in Hlu; try discriminate.
            exists t0.
            eapply assign_lexp_normalized_lexp_pure with (e := e); eauto.
          - rewrite generate_leqns_constraints_cons in Hgenh.
            eapply sec_bind_inv in Hgenh as (c & xst1 & Hc & _).
            rewrite generate_leqn_constraint_def in Hc
              by (destruct e; try exact I; inv Hne).
            apply generate_ldef_constraint_inv in Hc
              as (ck1 & ckty1 & t0 & rb & stm2 & _ & _ & Hte & _ & _).
            exists t0.
            eapply assign_lexp_normalized_lexp_pure with (e := e); eauto. }

        edestruct IH as (ts1 & Hts1);
          [exact Hlen'|exact Hnes|exact Ht|exact Hgent|exact Hr2|].
        exists (t0 :: ts1). intros s.
        rewrite assign_lexps_cons.
        eapply sec_bind_ok; [apply Ht0|].
        eapply sec_bind_ok; [apply Hts1|]. reflexivity.
    Qed.

    (** * What the two sides agree on without argument

        Two syntactic facts the call case turns on.  The first: the clock the
        emitted call is instantiated at is the clock the source call was
        instantiated at, because unnesting and the no-op pass both preserve
        annotations and a base clock is read off those.  The second: the
        clock the emitted call's reset variable carries is the clock of the
        source reset expression, for the same reason -- [unnest_reset] takes
        the annotation it mints from, or keeps, from the unnested reset. *)

    Lemma unnest_call_clocksof :
      forall (P : global) es es1 eqs1 st st1 ckis es2 eqs2 st2,
        Forall (wl_exp P) es ->
        unnest_exps P es st = ((es1, eqs1), st1) ->
        List.length ckis = List.length es1 ->
        Forall (fun e => numstreams e = 1) es1 ->
        unnest_noops_exps ckis es1 st1 = ((es2, eqs2), st2) ->
        LSyn.clocksof es2 = LSyn.clocksof es.
    Proof.
      intros P es es1 eqs1 st st1 ckis es2 eqs2 st2 Hwl Hune Hlen Hns Hunn.
      assert (annots es1 = annots es) as Ha1
          by (eapply unnest_exps_annots; eauto).
      assert (annots es2 = annots es1) as Ha2
          by (eapply unnest_noops_exps_annots; eauto).
      rewrite !clocksof_annots, Ha2, Ha1. reflexivity.
    Qed.

    Lemma unnest_reset_ann_clock :
      forall (P : global) e1 r ty ckr nm eqs3 st st',
        wl_exp P e1 -> numstreams e1 = 1 ->
        unnest_reset (unnest_exp P true) (Some e1) st
          = ((Some (Evar r (ty, (ckr, nm))), eqs3), st') ->
        LSyn.clockof e1 = [ckr].
    Proof.
      intros P e1 r ty ckr nm eqs3 st st' Hwl Hns Hun.
      destruct (unnest_exp P true e1 st) as [[es' eqs1] st1] eqn:Hk.
      assert (annots es' = annot e1) as Hann
          by (eapply unnest_exp_annot; eauto).
      assert (List.length es' = 1) as Hlen
          by (erewrite unnest_exp_length; eauto).
      destruct es' as [|e0 [|]]; simpl in Hlen; try discriminate.
      assert (annot e0 = annot e1) as Hann0.
      { unfold annots in Hann. simpl in Hann. now rewrite app_nil_r in Hann. }
      assert (List.length (annot e1) = 1) as Hla
          by (rewrite length_annot_numstreams; exact Hns).
      destruct (annot e1) as [|a [|]] eqn:Ea; simpl in Hla; try discriminate.
      destruct a as (tya & cka & na).
      assert (LSyn.clockof e1 = [cka]) as Hcl
          by (rewrite clockof_annot, Ea; reflexivity).
      eapply unnest_reset_spec in Hk
        as [(v & an & Ehd & Hnorm)
           |(ty0 & ck0 & o0 & x & st2 & Hhd & Hfresh & Hnorm)];
        rewrite Hnorm in Hun; inv Hun.
      - simpl in Ehd. subst e0. simpl in Hann0. inv Hann0. exact Hcl.
      - change (hd_default [e0]) with e0 in Hhd.
        rewrite Hann0 in Hhd. simpl in Hhd. inv Hhd. exact Hcl.
    Qed.

    (** * The witness on a call's results

        A call's results are named twice over.  The security monad minted one
        name per result when it typed the source expression; unnesting minted
        one program variable per result, and the naming pass gave each of
        those a security name of its own.  Nothing relates the two lists but
        position, and nothing has to: the witness is *chosen* so that the
        second is the ambient-inflated value of the first.

        That choice is forced.  The emitted call equation constrains its
        results above the instantiated block, which on the source side is
        constrained above the minted names; the ambient comes in because the
        equation is emitted under one.  Under a two-sided reading of the
        result correspondence the same choice would force the ambient below
        each result, which is why [cs_out]'s first clause is one-sided. *)

    Lemma call_outputs_witness :
      forall dlt (outs bs : list ident),
        NoDup bs ->
        List.length outs = List.length bs ->
        (forall b, In b bs -> ~ In b scope) ->
        Forall (fun o => In o scope) outs ->
        exists dlt',
          agree_off bs dlt dlt'
          /\ Forall2 (amb_pair dlt') outs bs.
    Proof.
      intros dlt outs bs Hnd Hlen Hbs Hos.
      remember (fun o => hm_ext dlt (merge amb [o])) as fv eqn:Efv.
      exists (upds bs (List.map fv outs) dlt).
      split; [apply upds_agree_off|].
      assert (List.length bs = List.length (List.map fv outs)) as Hlen'
          by (rewrite map_length; now symmetry).

      assert (forall (os bs0 : list ident) C,
                 List.length os = List.length bs0 ->
                 incl (combine bs0 (List.map fv os)) C ->
                 Forall2 (fun o b => In (b, fv o) C) os bs0) as Hgen.
      { induction os as [|o os IH]; intros bs0 C Hl Hincl;
          destruct bs0 as [|b bs0]; simpl in Hl; try discriminate;
          [constructor|].
        constructor.
        - apply Hincl. simpl. now left.
        - eapply IH; [congruence|].
          intros p Hp. apply Hincl. simpl. now right. }

      assert (Forall2 (fun o b => In (b, fv o) (combine bs (List.map fv outs)))
                outs bs) as Hin
          by (apply Hgen; [exact Hlen|apply incl_refl]).

      eapply Forall2_impl_In; [|exact Hin].
      intros o b Ho Hb Hinob.
      assert (upds bs (List.map fv outs) dlt b = fv o) as Hbv
          by (eapply upds_nth; eauto).
      assert (hm_ext (upds bs (List.map fv outs) dlt) (merge amb [o])
                = hm_ext dlt (merge amb [o])) as Hstable.
      { apply hm_ext_upds. intros x Hx Hxb. apply (Hbs x Hxb).
        apply in_merge_inv in Hx as [Hx|Hx].
        - now apply amb_scoped.
        - destruct Hx as [Hx|[]]; subst.
          rewrite Forall_forall in Hos. now apply Hos. }
      unfold amb_pair, satisfiable.
      rewrite Hstable, hm_ext_single, Hbv, Efv, <- join_bottom_eq1.
      split; apply Lat.order_refl, Lat.eq_refl.
    Qed.


    (** The no-op pass leaves the arguments normalized: it either keeps one
        or replaces it with a variable. *)

    Lemma unnest_noops_normalized :
      forall ckis es1 es2 eqs2 st st',
        List.length ckis = List.length es1 ->
        Forall normalized_lexp es1 ->
        unnest_noops_exps ckis es1 st = ((es2, eqs2), st') ->
        Forall normalized_lexp es2.
    Proof.
      intros ckis es1. revert ckis.
      induction es1 as [|e es1 IH];
        intros ckis es2 eqs2 st st' Hlen Hnorm Hun.
      - destruct ckis; simpl in Hlen; [|discriminate].
        apply unnest_noops_exps_nil_l in Hun as (? & _ & _); subst. constructor.
      - destruct ckis as [|ck ckis]; simpl in Hlen; [discriminate|].
        inversion Hlen as [Hlen'].
        inversion Hnorm as [|e0 es0 Hne Hnes]; subst.
        apply unnest_noops_exps_cons in Hun
          as (e2 & eqh & st1 & es2t & eqt & Hh & Ht & ? & ?); subst.
        constructor; [|eapply IH; eauto].
        apply unnest_noops_exp_inv in Hh
          as [(? & _ & _)|(x & an & ? & _ & _)]; subst; [exact Hne|].
        destruct an. constructor.
    Qed.

    (** The ambient is idempotent, so two domination steps modulo it
        compose into one. *)

    Lemma amb_trans :
      forall dlt a b c,
        satisfiable dlt a (merge amb b) ->
        satisfiable dlt b (merge amb c) ->
        satisfiable dlt a (merge amb c).
    Proof.
      intros dlt a b c H1 H2. eapply satisfiable_trans; [exact H1|].
      apply satisfiable_merge_intro; [apply satisfiable_merge_l|exact H2].
    Qed.

    (** And a relation between two type lists survives a witness that only
        moves names neither of them can see. *)

    Lemma Forall2_rel_off :
      forall dlt dlt' zs (l1 l2 : list LST) sc,
        agree_off zs dlt dlt' ->
        (forall y, In y zs -> ~ In y sc) ->
        st_scoped sc amb ->
        Forall (fun t => st_scoped sc (fst t)) l1 ->
        Forall (fun t => st_scoped sc (fst t)) l2 ->
        Forall2 (fun t1 t2 => satisfiable dlt (fst t2) (merge amb (fst t1)))
          l1 l2 ->
        Forall2 (fun t1 t2 => satisfiable dlt' (fst t2) (merge amb (fst t1)))
          l1 l2.
    Proof.
      intros dlt dlt' zs l1 l2 sc Hoff Hzs Hamb' Hs1 Hs2 Hrel.
      eapply Forall2_impl_In; [|exact Hrel].
      intros p q Hp Hq Hpq.
      eapply satisfiable_off with (xs := zs); eauto.
      - intros y Hy Hin. apply (Hzs y Hin).
        eapply Forall_forall in Hs2; [|exact Hq]. now apply Hs2.
      - intros y Hy Hin. apply in_merge_inv in Hy as [Hy|Hy].
        + apply (Hzs y Hin). now apply Hamb'.
        + apply (Hzs y Hin).
          eapply Forall_forall in Hs1; [|exact Hp]. now apply Hs1.
    Qed.

    Lemma Forall2_amb_compose :
      forall dlt (l1 l2 l3 : list LST),
        Forall2 (fun a b => satisfiable dlt (fst b) (merge amb (fst a))) l1 l2 ->
        Forall2 (fun b c => satisfiable dlt (fst c) (merge amb (fst b))) l2 l3 ->
        Forall2 (fun a c => satisfiable dlt (fst c) (merge amb (fst a))) l1 l3.
    Proof.
      intros dlt l1 l2 l3 H1. revert l3.
      induction H1 as [|a b k1 k2 Hab Hr IH]; intros l3 H2; inv H2;
        constructor.
      - eapply amb_trans; [eassumption|exact Hab].
      - now apply IH.
    Qed.

    (** The results' two namings line up because [Env.find] is a function. *)

    Lemma evars_outt :
      forall (ys : list (ident * ann)) bs (us : list LST),
        Forall2 (fun x b => Env.find x env = Some b) (List.map fst ys) bs ->
        Forall2 (fun xa t => exists b, Env.find (fst xa) env = Some b
                                       /\ t = lvar b) ys us ->
        Forall2 (fun b t => t = lvar b) bs us.
    Proof.
      induction ys as [|[ya1 ya2] ys IH]; intros bs us H1 H2; simpl in H1.
      - inv H1. inv H2. constructor.
      - inversion H1 as [|y b ys0 bs0 Hyb Hr1]; subst.
        inversion H2 as [|ya0 t ys1 ts1 (b' & Hb' & ?) Hr2]; subst.
        simpl in Hb'. rewrite Hyb in Hb'. inv Hb'.
        constructor; [reflexivity|eapply IH; eauto].
    Qed.

    (** Which of the two branches [unnest_reset] took is visible in the
        option itself: a call with no reset keeps none and emits nothing, and
        a call with one comes back with a variable either way. *)

    Lemma unnest_reset_option_shape :
      forall k er er' eqs st st',
        unnest_reset k er st = ((er', eqs), st') ->
        (er = None /\ er' = None /\ eqs = [] /\ st' = st)
        \/ (exists e1 v an, er = Some e1 /\ er' = Some (Evar v an)).
    Proof.
      intros k er er' eqs st st' H.
      destruct er as [e1|].
      - right.
        destruct (k e1 st) as [[zs zeqs] zst] eqn:Hk.
        eapply unnest_reset_spec in Hk
          as [(v & a & _ & Hnorm)|(t0 & c0 & o0 & xx & s0 & _ & _ & Hnorm)];
          rewrite Hnorm in H; inv H; eauto 10.
      - left. simpl in H. repeat inv_bind. auto.
    Qed.

    Lemma mmap_find_env_Forall2 :
      forall (ys : list ident) outt st st',
        SC.mmap (fun x => find_env x env) ys st = OK (outt, st') ->
        Forall2 (fun x b => Env.find x env = Some b) ys outt.
    Proof.
      induction ys as [|y ys IH]; intros outt st st' H; simpl in H.
      - unfold SC.ret in H. inv H. constructor.
      - eapply sec_bind_inv in H as (b & st1 & Hb & H).
        eapply sec_bind_inv in H as (bs & st2 & Hbs & Hret).
        unfold SC.ret in Hret. inv Hret.
        apply find_env_inv in Hb as (Hb & ?); subst.
        constructor; [exact Hb|eapply IH; eauto].
    Qed.

    Lemma sec_names_NoDup :
      forall (ys : list ident) bs,
        NoDup ys ->
        Forall2 (fun x b => Env.find x env = Some b) ys bs ->
        NoDup bs.
    Proof.
      intros ys bs Hnd Hf. revert Hnd.
      induction Hf as [|y b ys bs Hyb Hr IH]; intros Hnd; [constructor|].
      inv Hnd. constructor; [|now apply IH].
      intro Hc. apply H1.
      assert (exists y', In y' ys /\ Env.find y' env = Some b) as (y' & Hy' & Hfy').
      { clear - Hr Hc. induction Hr as [|z c zs cs Hzc Hrr IHr];
          [contradiction|].
        destruct Hc as [Hc|Hc]; subst.
        - exists z. split; [now left|exact Hzc].
        - destruct (IHr Hc) as (y' & Hy' & Hfy').
          exists y'. split; [now right|exact Hfy']. }
      replace y with y'; [exact Hy'|].
      eapply env_inj; [exact Hfy'|exact Hyb|reflexivity].
    Qed.

    Lemma Forall2_in_sec_of :
      forall (ys : list ident) bs b,
        Forall2 (fun x b => Env.find x env = Some b) ys bs ->
        In b bs -> In b (sec_of ys).
    Proof.
      intros ys bs b Hf. revert b.
      induction Hf as [|y c ys bs Hyc Hr IH]; intros b Hb; [contradiction|].
      unfold sec_of. simpl. rewrite Hyc.
      destruct Hb as [|Hb]; subst; [now left|].
      right. now apply IH.
    Qed.

    (** * The call, assembled

        Everything the case needs is now in place: the arguments are related
        by the induction hypothesis and the no-op step, the reset by the
        reset step, the clocks agree on the nose, the results' witness is
        chosen, and the instantiated block transfers by monotonicity in the
        actuals.  What is left is the bookkeeping that keeps the four
        witnesses from disturbing one another. *)

    (** Names a caller may use in an actual, from the three places the
        proofs find them: the scope, the environment, and the names a run
        moved (which are environment images of the variables it created). *)
    Lemma caller_st_scoped :
      forall t, st_scoped scope t -> caller_st env scope t.
    Proof. intros t H y Hy. left. exact (H y Hy). Qed.

    Lemma caller_name_moved :
      forall st1 st2 y, In y (moved_by st1 st2) -> caller_name env scope y.
    Proof.
      intros st1 st2 y Hy. right. unfold moved_by, sec_of in Hy.
      apply in_flat_map in Hy as (x & _ & Hx).
      destruct (Env.find x env) as [b|] eqn:Hf; [|contradiction].
      destruct Hx as [Hx|[]]. subst b. now exists x.
    Qed.

    Lemma caller_st_moved :
      forall st1 st2 t,
        st_scoped (scope ++ moved_by st1 st2) t -> caller_st env scope t.
    Proof.
      intros st1 st2 t H y Hy. apply H in Hy.
      apply in_app_or in Hy as [Hy|Hy]; [now left|].
      exact (caller_name_moved st1 st2 y Hy).
    Qed.

    Lemma carries_Eapp :
      forall P ic f es er anns,
        wc_global P ->
        Forall (carries P) es ->
        (forall e1, er = Some e1 -> carries P e1) ->
        carries_at P ic (Eapp f es er anns).
    Proof.
      intros P ic f es er anns Hwcg Halls Hallr
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hwl as Hwl0. pose proof Hwc as Hwc0.
      assert (anns <> []) as Hanne.
      { intro Hc. subst anns. inv Hwl0;
          match goal with H : _ = List.length (n_out ?nn) |- _ =>
            pose proof (n_outgt0 nn); simpl in H; lia end. }
      assert (Forall (wl_exp P) es) as Hwles by (inv Hwl0; assumption).
      assert (Forall (wc_exp P vars) es) as Hwces by (inv Hwc0; assumption).

      (** the two sides, taken apart *)
      pose proof Hun as Hun0.
      apply unnest_exp_Eapp_inv in Hun
        as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er2 & eqs3 & st3 & xs
            & Hune & Hunn & Hunr & Hids & ? & ?); subst.
      pose proof Hune as Hune0.
      apply unnest_exps_inv in Hune as (ess & eqss & Hmap & ? & ?); subst.
      pose proof Has as Has0.
      apply assign_lexp_Eapp_inv in Has
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & Hargs & Hck & Hrst & Esg & Houts & Hcs & Hts).
      apply assign_lexps_evars in Has' as (? & Hevars); subst.

      (** the states the run passed through *)
      assert (st_follows st st1) as Hfa
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hfb
          by (eapply unnest_noops_exps_st_follows; eauto).
      assert (st_follows st2 st3) as Hfc
          by (eapply unnest_reset_st_follows; eauto).
      assert (st_follows st3 st') as Hfd
          by (eapply idents_for_anns'_st_follows; eauto).
      assert (st_follows st st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st st3) as Hf03 by (etransitivity; eauto).
      assert (st_follows st1 st3) as Hf13 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).
      assert (st_follows st2 st') as Hf2' by (etransitivity; eauto).

      (** the same, on the security monad.  The whole source run ends before
          the checkmark, and its stages run in order, so each stage's final
          state is before it too -- which is what the scoping hypotheses on
          the source generator ask for. *)
      pose proof (assign_lexp_Eapp_stages_le GL env base_ty rst_ty es er anns
                    sst sst' sg argts rstty ckty outs cs sta stb stc
                    Hargs Hrst Houts Hcs) as (Hlab & Hlbc & Hlcs).
      assert (sec_le stc stF) as Hbstc by exact (sec_le_trans _ _ _ Hlcs Hbnd).
      assert (sec_le stb stF) as Hbstb by exact (sec_le_trans _ _ _ Hlbc Hbstc).
      assert (sec_le sta stF) as Hbsta by exact (sec_le_trans _ _ _ Hlab Hbstb).
      assert (sec_le stLo sta) as Hlsa
          by (eapply sec_le_trans; [exact Hlow|]; eapply assign_lexps_sec_le; exact Hargs).

      (** the emitted constraints, equation by equation *)
      rewrite generate_leqns_constraints_cons in Hgen.
      eapply sec_bind_inv in Hgen as (ce0 & xsta & Hgen0 & Hgen).
      eapply sec_bind_inv in Hgen as (cer & xstb & Hgenr & Hret).
      unfold SC.ret in Hret. inv Hret.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & cerr & xstc & Hgen1 & Hgenrr & ?); subst.
      apply generate_leqns_constraints_app in Hgenrr
        as (ce2 & ce3 & xstd & Hgen2 & Hgen3 & ?); subst.

      (** what the run defines, split between its four stages *)
      assert (vars_defined
                ((List.map fst xs, [Eapp f es2 er2 (List.map snd xs)])
                   :: (List.concat eqss ++ eqs2 ++ eqs3))
              = List.map fst xs
                ++ vars_defined (List.concat eqss ++ eqs2 ++ eqs3)) as Hvd
          by reflexivity.
      rewrite Hvd in Hnd, Hamb.
      rewrite <- app_assoc in Hnd.
      assert (NoDup (vars_defined (List.concat eqss ++ eqs2 ++ eqs3)
                       ++ st_ids st)) as Hndr
          by (eapply NoDup_app_r; exact Hnd).
      assert (Permutation (vars_defined (List.concat eqss) ++ st_ids st)
                (st_ids st1)) as Hp1
          by (eapply map_bind2_unnest_vars_perm; eauto).
      assert (Permutation (vars_defined eqs2 ++ st_ids st1) (st_ids st2))
        as Hp2 by (eapply unnest_noops_exps_vars_perm; eauto).
      assert (Permutation (vars_defined eqs3 ++ st_ids st2) (st_ids st3))
        as Hp3.
      { assert (LiftO True
                  (fun e => forall es'0 eqs'0 st0 st'0,
                       unnest_exp P true e st0 = ((es'0, eqs'0), st'0) ->
                       Permutation (vars_defined eqs'0 ++ st_ids st0)
                         (st_ids st'0)) er) as Hlift.
        { destruct er as [e1|]; simpl; [|exact I].
          intros es'0 eqs'0 st0 st'0 Hk.
          eapply unnest_exp_vars_perm; [|exact Hk]. inv Hwl0; assumption. }
        eapply unnest_reset_vars_perm; [exact Hlift|exact Hunr]. }
      assert (NoDup (vars_defined (List.concat eqss) ++ st_ids st)) as Hnd1
          by (eapply NoDup_vd_app_l; exact Hndr).
      assert (NoDup (vars_defined (eqs2 ++ eqs3) ++ st_ids st1)) as Hnd23
          by (eapply NoDup_vd_app_r; [exact Hp1|exact Hndr]).
      assert (NoDup (vars_defined eqs2 ++ st_ids st1)) as Hnd2
          by (eapply NoDup_vd_app_l; exact Hnd23).
      assert (NoDup (vars_defined eqs3 ++ st_ids st2)) as Hnd3
          by (eapply NoDup_vd_app_r; [exact Hp2|exact Hnd23]).

      (** the call binds at least one result, so its equation reduces *)
      assert (List.length xs = List.length anns) as Hlxs
          by (eapply idents_for_anns'_length; eauto).
      assert (exists x0 xs0, List.map fst xs = x0 :: xs0)
        as (x0 & xs0 & Exs).
      { destruct xs as [|xa xsr]; [|simpl; eauto].
        exfalso. apply Hanne. simpl in Hlxs.
        destruct anns; [reflexivity|discriminate Hlxs]. }

      (** what the emitted call generates, whichever way its reset came out *)
      pose proof Hunr as Hunr1.
      assert (exists rstty' ckt argt outt sti cs0,
                 ((er = None /\ er2 = None /\ eqs3 = [] /\ st3 = st2
                   /\ rstty' = lvar rst_ty)
                  \/ (exists e1 r ty0 ckr nm rty rstck,
                        er = Some e1
                        /\ er2 = Some (Evar r (ty0, (ckr, nm)))
                        /\ Env.find r env = Some rty
                        /\ assign_clk_type env base_ty ckr = Some rstck
                        /\ rstty' = ljoin (lvar rst_ty)
                                      (merge [rty] rstck, [])))
                 /\ assign_clk_type env base_ty
                      (find_base_clock (LSyn.clocksof es2)) = Some ckt
                 /\ assign_lexps GL env base_ty rst_ty es2 xst = OK (argt, sti)
                 /\ SC.mmap (fun x => find_env x env) (x0 :: xs0) sti
                    = OK (outt, sti)
                 /\ generate_constraints sg (List.map fst argt) ckt
                      (fst rstty') outt sti = OK (cs0, xsta)
                 /\ ce0 = cmerge cs0 (cmerge (carried argt) (snd rstty')))
        as (rstty' & ckt & argt & outt & sti & cs0
            & Hshape & Hckt & Hargt & Houtt & Hgc & Hce0).
      { rewrite Exs in Hgen0.
        apply unnest_reset_option_shape in Hunr1
          as [(Hern & Hn2 & ? & ?)|(e1 & rv & ran & Her & Hs2)]; subst.
        - rewrite gen_leqn_Eapp in Hgen0.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & sti & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (lvar rst_ty), ckt, argt, outt, sti, cs0.
          split;
            [left; repeat split; reflexivity
            |split; [exact Hckt|split; [exact Hargt
             |split; [exact Houtt|split; [exact Hgc|exact Hce0]]]]].
        - destruct ran as (ty0 & ckr0 & nm0).
          rewrite gen_leqn_Eapp_reset in Hgen0.
          eapply sec_bind_inv in Hgen0 as (rty & s1 & Hrty & Hgen0).
          apply find_env_inv in Hrty as (Hrty & ?); subst s1.
          eapply sec_bind_inv in Hgen0 as (rstck & s2 & Hrstck & Hgen0).
          apply option_to_sec_inv in Hrstck as (Hrstck & ?); subst s2.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & sti & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (ljoin (lvar rst_ty) (merge [rty] rstck, [])),
                 ckt, argt, outt, sti, cs0.
          split;
            [|split; [exact Hckt|split; [exact Hargt
              |split; [exact Houtt|split; [exact Hgc|exact Hce0]]]]].
          right. exists e1, rv, ty0, ckr0, nm0, rty, rstck.
          repeat split; auto. }

      (** what the source expression carries, taken apart *)
      assert (outs <> []) as Houtsne.
      { intro Hc. apply Hanne. apply fresh_idents_length in Houts.
        rewrite Hc in Houts. simpl in Houts.
        destruct anns; [reflexivity|discriminate Houts]. }
      assert (match outs with
              | [] => ([] : list SymTypes.constraint)
              | _ => cmerge cs (cmerge (carried argts) (snd rstty))
              end = cmerge cs (cmerge (carried argts) (snd rstty))) as Hmt
          by (destruct outs; [now elim Houtsne|reflexivity]).
      rewrite carried_uniform, Hmt in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsccs & Hscr).
      apply constraints_scoped_cmerge in Hscr as (Hscarg & Hscrst).
      apply listSatisfiable_cmerge in Hcar as (Hcarcs & Hcarr).
      apply listSatisfiable_cmerge in Hcarr as (Hcararg & Hcarrst).
      assert (Forall (fun t => st_scoped scope (fst t)) argts) as Hscargts
          by (exact (source_lexps_scoped P es argts sst sta Hwces Hlow Hargs Hbsta)).

      (** the arguments, as the pass left them *)
      assert (Forall normalized_lexp (List.concat ess)) as Hnorm1
          by (eapply map_bind2_unnest_normalized_lexp; eauto).
      assert (List.length (List.concat ess) = List.length (annots es))
        as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (List.length (find_node_incks P f)
              = List.length (List.concat ess)) as Hlck.
      { unfold find_node_incks. rewrite Hlen1.
        inv Hwl0;
          match goal with
          | H : find_node f P = Some ?nn |- _ => rewrite H
          end; rewrite map_length;
          match goal with
          | H : List.length (annots es) = _ |- _ => now rewrite H
          end. }
      edestruct (noops_operand_types (find_node_incks P f) (List.concat ess)
                   es2 eqs2 st1 st2 ce2 xstc xstd argt xst sti)
        as (argts1 & Hargts1);
        [exact Hlck|exact Hnorm1|exact Hunn|exact Hgen2|exact Hargt|].

      (** the induction hypothesis, on the arguments *)
      edestruct (carries_list_intro_local P es Halls false ess eqss st st1 argts
                   sst sta ce1 xsta xstc argts1 xst xst dlt)
        as (dlt1 & Hoff1 & Hce1' & Hrel1 & Hscope1 & Hsca1).
      { exact Hwles. }
      { exact Hwces. }
      { exact Hnd1. }
      { intros y Hy. apply Hmv.
        apply (moved_by_prefix_local st st1 st' Hf1'). exact Hy. }
      { exact Hscarg. }
      { exact Hscargts. }
      { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap. }
      { exact Hargs. }
      { exact Hgen1. }
      { apply Hargts1. }
      { exact Hcararg. }
      { exact Hbsta. }
      { exact Hlow. }

      (** and the no-op pass on top of it *)
      assert (forall y, In y (moved_by st1 st2) ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix_local st st1 st' Hfa).
          apply (moved_by_prefix_local st1 st2 st' Hf2'). exact Hin.
        - exact (moved_by_disjoint_local st st1 st2 y Hy Hin). }
      edestruct (noops_step (scope ++ moved_by st st1) (find_node_incks P f)
                   (List.concat ess) es2 eqs2 st1 st2 argts1 argt ce2
                   xstc xstd xst xst xst sti dlt1)
        as (dlt2 & Hoff2 & Hce2' & Hrel2 & Hscope2 & Hsca2).
      { exact Hlck. }
      { exact Hnorm1. }
      { exact Hunn. }
      { exact Hnd2. }
      { exact Hsep12. }
      { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact amb_scoped]. }
      { apply Hargts1. }
      { exact Hargt. }
      { exact Hsca1. }
      { exact Hgen2. }

      (** the reset *)
      assert (agree_off (moved_by st st2) dlt dlt2) as Hoff12.
      { eapply agree_off_trans;
          [eapply agree_off_incl; [|exact Hoff1];
           apply (moved_by_prefix_local st st1 st2 Hfb)
          |eapply agree_off_incl; [|exact Hoff2];
           apply (moved_by_suffix_local st st1 st2 Hfa)]. }
      assert (exists dlt3,
                 agree_off (moved_by st2 st3) dlt2 dlt3
                 /\ listSatisfiable dlt3 ce3
                 /\ constraints_scoped (scope ++ moved_by st2 st3) ce3
                 /\ satisfiable dlt3 (fst rstty') (merge amb (fst rstty))
                 /\ st_scoped (scope ++ moved_by st st3) (fst rstty'))
        as (dlt3 & Hoff3 & Hce3' & Hscope3 & Hrelrst & Hscrst').
      { destruct Hshape
          as [(Hern & Hn2 & Heq3 & Hst3 & Hrs')
             |(e1 & rv & ty0 & ckr0 & nm0 & rty & rstck
               & Her & Hs2 & Hrty & Hrstck & Hrs')].
        - (** no reset: nothing was emitted and nothing moved *)
          subst. destruct Hrst as (Hrstty & ?); subst rstty.
          apply generate_leqns_constraints_nil in Hgen3 as (? & ?); subst.
          exists dlt2. split; [apply agree_off_refl|].
          split; [constructor|]. split; [constructor|].
          split; [apply satisfiable_merge_r|].
          rewrite fst_lvar. intros y Hy. destruct Hy as [Hy|[]]; subst y.
          apply in_or_app. now left.
        - (** a reset: the reset step, on the variable it came back as *)
          subst er er2 rstty'.
          destruct Hrst as (t1 & a1 & rck & stm & Hty1 & Hsg1 & Hrck & Hrstty).
          apply single_inv in Hsg1 as (? & ?); subst t1 stb.
          assert (wl_exp P e1) as Hwle1 by (inv Hwl0; assumption).
          assert (wc_exp P vars e1) as Hwce1 by (inv Hwc0; assumption).
          assert (numstreams e1 = 1) as Hns1 by (inv Hwl0; assumption).
          assert (st_scoped scope (fst a1)) as Hsca1'.
          { assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hf
                by (exact (source_types_scoped P e1 [a1] sta stm Hwce1 Hlsa Hty1 Hbstb)).
            now inv Hf. }
          assert (snd rstty = snd a1) as Hsndr.
          { subst rstty. rewrite !snd_ljoin, snd_lvar.
            simpl snd. now rewrite cmerge_nil, cmerge_nil2. }
          assert (rstck = rck) as Hcke.
          { assert (LSyn.clockof e1 = [ckr0]) as Hcl
                by (eapply unnest_reset_ann_clock; eauto).
            rewrite Hcl in Hrck. simpl hd in Hrck.
            rewrite Hrstck in Hrck. now inv Hrck. }
          assert (In ckr0 (clockof e1)) as Hclin.
          { assert (LSyn.clockof e1 = [ckr0]) as Hcl0
                by (eapply unnest_reset_ann_clock; eauto).
            rewrite Hcl0. now left. }
          edestruct (reset_step P e1 rv (ty0, (ckr0, nm0)) rty eqs3 st2 st3
                       a1 sta stm ce3 xstd xst' xst dlt2)
            as (dlt3 & Hoff3 & Hce3' & Hrelr & Hinr & Hscope3).
          { apply Hallr. reflexivity. }
          { exact Hwle1. }
          { exact Hwce1. }
          { exact Hns1. }
          { exact Hunr. }
          { exact Hrty. }
          { exact Hnd3. }
          { intros y Hy. apply Hmv.
            apply (moved_by_suffix_local st st2 st' Hf02).
            apply (moved_by_prefix_local st2 st3 st' Hfd). exact Hy. }
          { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
            rewrite vars_defined_app. apply in_or_app. right.
            rewrite vars_defined_app. apply in_or_app. now right. }
          { exact Hty1. }
          { rewrite carried_single, <- Hsndr. exact Hscrst. }
          { exact Hsca1'. }
          { exact Hgen3. }
          { rewrite carried_single, <- Hsndr.
            eapply listSatisfiable_off_scope
              with (sc := scope) (xs := moved_by st st2);
              [exact Hscrst| |exact Hoff12|exact Hcarrst].
            intros y Hy. apply Hmv.
            apply (moved_by_prefix_local st st2 st' Hf2'). exact Hy. }
          { exact Hbstb. }
          { exact Hlsa. }
          exists dlt3. split; [exact Hoff3|]. split; [exact Hce3'|].
          split; [exact Hscope3|]. split.
          + subst rstty rstck. rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            apply satisfiable_merge_intro.
            * eapply satisfiable_trans; [apply satisfiable_merge_l|].
              apply satisfiable_merge_r.
            * apply satisfiable_merge_intro.
              -- eapply satisfiable_trans; [exact Hrelr|].
                 apply satisfiable_merge_intro; [apply satisfiable_merge_l|].
                 eapply satisfiable_trans; [apply satisfiable_merge_l|].
                 eapply satisfiable_trans; [apply satisfiable_merge_r|].
                 apply satisfiable_merge_r.
              -- eapply satisfiable_trans; [apply satisfiable_merge_r|].
                 eapply satisfiable_trans; [apply satisfiable_merge_r|].
                 apply satisfiable_merge_r.
          + rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            intros y Hy. apply in_merge_inv in Hy as [Hy|Hy].
            * destruct Hy as [Hy|[]]; subst y. apply in_or_app. now left.
            * apply in_merge_inv in Hy as [Hy|Hy].
              -- destruct Hy as [Hy|[]]; subst y.
                 apply in_app_or in Hinr as [Hinr|Hinr];
                   apply in_or_app; [now left|].
                 right. apply (moved_by_suffix_local st st2 st3 Hf02). exact Hinr.
              -- apply in_or_app. left.
                 exact (clk_types_scoped P [e1] ckr0 rstck Hwcg (Forall_cons _ Hwce1 (Forall_nil _))
                          (or_introl (clk_src_clockof vars e1 ckr0 (Hclin))) Hrstck y Hy). }

      (** the results, and the witness on them *)
      assert (Forall2 (fun x b => Env.find x env = Some b) (List.map fst xs) outt)
        as Houttf by (rewrite Exs; eapply mmap_find_env_Forall2; eauto).
      assert (Permutation (List.map fst xs ++ st_ids st3) (st_ids st'))
        as Hpx by (eapply idents_for_anns'_vars_perm; eauto).
      assert (Permutation
                (vars_defined
                   ((List.map fst xs, [Eapp f es2 er2 (List.map snd xs)])
                      :: (List.concat eqss ++ eqs2 ++ eqs3)) ++ st_ids st)
                (st_ids st')) as Hpall
          by (eapply unnest_exp_vars_perm; eauto).
      rewrite Hvd, <- app_assoc in Hpall.
      assert (NoDup (st_ids st')) as Hndst'
          by (eapply Permutation_NoDup; [exact Hpall|exact Hnd]).
      assert (NoDup (List.map fst xs ++ st_ids st3)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (NoDup outt) as Hndoutt
          by (eapply sec_names_NoDup; [exact Hndfst|exact Houttf]).
      assert (forall b, In b outt -> In b (moved_by st3 st')) as Houttmv.
      { intros b Hb.
        assert (In b (sec_of (List.map fst xs))) as Hbs
            by (eapply Forall2_in_sec_of; eauto).
        unfold sec_of, moved_by in *.
        apply in_flat_map in Hbs as (x & Hx & Hbx).
        apply in_flat_map. exists x. split; [|exact Hbx].
        apply new_ids_spec. split.
        - eapply idents_for_anns'_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (incl outt (moved_by st st')) as Houttmv0
          by (intros b Hb; apply (moved_by_suffix_local st st3 st' Hf03);
              now apply Houttmv).
      assert (incl outt (moved_by st2 st')) as Houttmv2
          by (intros b Hb; apply (moved_by_suffix_local st2 st3 st' Hfc);
              now apply Houttmv).
      assert (forall b, In b outt -> ~ In b scope) as Houttsc
          by (intros b Hb Hc; eapply (Hmv b); [now apply Houttmv0|exact Hc]).
      assert (Forall (fun o => In o scope) outs) as Houtssc.
      { rewrite Forall_map in Hsts.
        eapply Forall_impl; [|exact Hsts].
        intros o Ho. apply Ho. now left. }
      assert (List.length outs = List.length outt) as Hlenout.
      { apply fresh_idents_length in Houts.
        apply Forall2_length in Houttf.
        rewrite Houts, <- Houttf, map_length. now symmetry. }
      edestruct (call_outputs_witness dlt3 outs outt)
        as (dlt4 & Hoff4 & Hpairs);
        [exact Hndoutt|exact Hlenout|exact Houttsc|exact Houtssc|].

      (** the emitted call generates just the instantiated block *)
      assert (Forall normalized_lexp es2) as Hnorm2
          by (eapply unnest_noops_normalized; eauto).
      assert (carried argt = []) as Hcargt.
      { eapply assign_lexps_normalized_pure with (es := es2); [|exact Hargt].
        eapply Forall_impl; [|exact Hnorm2]. intros; now constructor. }
      assert (snd rstty' = []) as Hsrst'.
      { destruct Hshape
          as [(_ & _ & _ & _ & Hrs')
             |(e1 & rv & ty0 & ckr0 & nm0 & rty & rstck
               & _ & _ & _ & _ & Hrs')]; subst rstty'; [reflexivity|].
        rewrite snd_ljoin, snd_lvar. cbn [snd]. apply cmerge_nil. }
      assert (ce0 = cs0) as Hce0'
          by (now rewrite Hce0, Hcargt, Hsrst', !cmerge_nil).

      (** the clock is the same on both sides *)
      assert (Forall (fun e => numstreams e = 1) (List.concat ess)) as Hns1s
          by (eapply map_bind2_unnest_exp_numstreams; eauto).
      assert (ckt = ckty) as Hckeq.
      { assert (LSyn.clocksof es2 = LSyn.clocksof es) as Hcl.
        { eapply unnest_call_clocksof;
            [exact Hwles|exact Hune0|exact Hlck|exact Hns1s|exact Hunn]. }
        rewrite Hcl, Hck in Hckt. now inv Hckt. }

      (** the witnesses, composed *)
      assert (agree_off (moved_by st2 st') dlt2 dlt4) as Hoff34.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff3].
          apply (moved_by_prefix_local st2 st3 st' Hfd).
        - eapply agree_off_incl; [|exact Hoff4]. exact Houttmv2. }
      assert (agree_off (moved_by st1 st') dlt1 dlt4) as Hoff1all.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff2].
          apply (moved_by_prefix_local st1 st2 st' Hf2').
        - eapply agree_off_incl; [|exact Hoff34].
          apply (moved_by_suffix_local st1 st2 st' Hfb). }
      assert (agree_off (moved_by st st') dlt dlt4) as Hoffall.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff1].
          apply (moved_by_prefix_local st st1 st' Hf1').
        - eapply agree_off_incl; [|exact Hoff1all].
          apply (moved_by_suffix_local st st1 st' Hfa). }

      (** the argument types, related at the final witness *)
      assert (forall y, In y (moved_by st2 st') ->
                        ~ In y (scope ++ moved_by st st2)) as Hsep2.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix_local st st2 st' Hf02). exact Hin.
        - exact (moved_by_disjoint_local st st2 st' y Hy Hin). }
      assert (st_scoped (scope ++ moved_by st st2) amb) as Hambsc2
          by (eapply st_scoped_weaken;
              [apply incl_appl, incl_refl|exact amb_scoped]).
      assert (Forall (fun t => st_scoped (scope ++ moved_by st st2) (fst t))
                argts) as Hsc_argts.
      { eapply Forall_impl; [|exact Hscargts]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      assert (Forall (fun t => st_scoped (scope ++ moved_by st st2) (fst t))
                argts1) as Hsc_argts1.
      { eapply Forall_impl; [|exact Hsca1]. intros q Hq.
        eapply st_scoped_weaken; [|exact Hq].
        apply incl_app; [apply incl_appl, incl_refl|].
        apply incl_appr, (moved_by_prefix_local st st1 st2 Hfb). }
      assert (Forall (fun t => st_scoped (scope ++ moved_by st st2) (fst t))
                argt) as Hsc_argt.
      { eapply Forall_impl; [|exact Hsca2]. intros q Hq.
        eapply st_scoped_weaken; [|exact Hq].
        apply incl_app.
        - apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix_local st st1 st2 Hfb).
        - apply incl_appr, (moved_by_suffix_local st st1 st2 Hfa). }
      assert (Forall2 (fun t1 t2 =>
                satisfiable dlt4 (fst t2) (merge amb (fst t1))) argts argt)
        as Hrelargs.
      { eapply Forall2_amb_compose with (l2 := argts1).
        - eapply Forall2_rel_off with (zs := moved_by st2 st')
              (sc := scope ++ moved_by st st2);
            [exact Hoff34|exact Hsep2|exact Hambsc2|exact Hsc_argts
            |exact Hsc_argts1|].
          eapply Forall2_rel_off with (zs := moved_by st1 st2)
              (sc := scope ++ moved_by st st1);
            [exact Hoff2|exact Hsep12| | | |exact Hrel1].
          + eapply st_scoped_weaken;
              [apply incl_appl, incl_refl|exact amb_scoped].
          + eapply Forall_impl; [|exact Hscargts]. intros q Hq.
            eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq].
          + exact Hsca1.
        - eapply Forall2_rel_off with (zs := moved_by st2 st')
              (sc := scope ++ moved_by st st2);
            [exact Hoff34|exact Hsep2|exact Hambsc2|exact Hsc_argts1
            |exact Hsc_argt|exact Hrel2]. }


      (** the reset type the source built is a source type *)
      assert (st_scoped scope (fst rstty)) as Hscrsty.
      { destruct er as [e1|].
        - destruct Hrst
            as (t1 & a1 & rck & stm & Hty1 & Hsg1 & Hrck & Hrstty).
          apply single_inv in Hsg1 as (? & ?); subst t1 stb.
          assert (wc_exp P vars e1) as Hwce1 by (inv Hwc0; assumption).
          subst rstty. rewrite !fst_ljoin, !fst_lvar. cbn [fst].
          intros y Hy. apply in_merge_inv in Hy as [Hy|Hy].
          + destruct Hy as [Hy|[]]; subst y. exact rst_ty_scoped.
          + apply in_merge_inv in Hy as [Hy|Hy].
            * assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hf
                  by (exact (source_types_scoped P e1 [a1] sta stm Hwce1 Hlsa Hty1 Hbstb)).
              inv Hf. auto.
            * exact (clk_types_scoped P [e1] _ rck Hwcg (Forall_cons _ Hwce1 (Forall_nil _))
                          (or_introl (clk_src_hd_clockof vars e1)) Hrck y Hy).
        - destruct Hrst as (Hrstty & ?). subst rstty.
          rewrite fst_lvar. intros y Hy.
          destruct Hy as [Hy|[]]; subst y. exact rst_ty_scoped. }

      (** the actuals, as names a caller may use *)
      assert (Forall (caller_st env scope) (List.map fst argts)) as Hcs_src.
      { rewrite Forall_map. eapply Forall_impl; [|exact Hscargts].
        intros q Hq. exact (caller_st_scoped _ Hq). }
      assert (caller_st env scope ckty) as Hck_src
          by exact (caller_st_scoped _
                      (clk_types_scoped P es _ ckty Hwcg Hwces (or_introl (clk_src_base vars es))
                         Hck)).
      assert (caller_st env scope (fst rstty)) as Hrs_src
          by exact (caller_st_scoped _ Hscrsty).
      assert (Forall (caller_name env scope) outs) as Hos_src.
      { eapply Forall_impl; [|exact Houtssc]. intros o Ho. left. exact Ho. }
      assert (Forall (caller_st env scope) (List.map fst argt)) as Hcs_tgt.
      { rewrite Forall_map. eapply Forall_impl; [|exact Hsc_argt].
        intros q Hq. exact (caller_st_moved _ _ _ Hq). }
      assert (caller_st env scope ckt) as Hckt_tgt
          by (rewrite Hckeq; exact Hck_src).
      assert (caller_st env scope (fst rstty')) as Hrs_tgt
          by exact (caller_st_moved _ _ _ Hscrst').
      assert (Forall (caller_name env scope) outt) as Hos_tgt.
      { rewrite Forall_forall. intros b Hb.
        exact (caller_name_moved st st' b (Houttmv0 b Hb)). }

      (** and the instantiated block, by monotonicity in the actuals *)
      assert (listSatisfiable dlt4 cs) as Hcs4.
      { eapply listSatisfiable_off_scope
          with (sc := scope) (xs := moved_by st st');
          [exact Hsccs|exact Hmv|exact Hoffall|exact Hcarcs]. }
      assert (listSatisfiable dlt4 cs0) as Hcs04.
      { eapply generate_constraints_mono_sem
          with (sig := sg) (inp1 := List.map fst argts)
               (inp2 := List.map fst argt)
               (clk1 := ckty) (clk2 := ckt)
               (rst1 := fst rstty) (rst2 := fst rstty')
               (os := outs) (bs := outt);
          [eapply sig_good; exact Esg
          |eapply sig_nodup_pipeline_local; exact Esg
          | | | | | |exact Hcs|exact Hgc|exact Hcs4].
        - eapply call_subst_fresh_pipeline;
            [eapply sig_actuals_fresh;
               [exact Esg|exact Hcs_src|exact Hck_src|exact Hrs_src
               |exact Hos_src|exact Hcs]
            |eapply sig_actuals_fresh;
               [exact Esg|exact Hcs_tgt|exact Hckt_tgt|exact Hrs_tgt
               |exact Hos_tgt|exact Hgc]].
        - rewrite Forall2_map_1, Forall2_map_2. exact Hrelargs.
        - rewrite Hckeq. apply satisfiable_merge_r.
        - eapply satisfiable_off with (xs := outt);
            [exact Hoff4| | |exact Hrelrst].
          + intros y Hy Hin.
            apply Hscrst' in Hy. apply in_app_or in Hy as [Hy|Hy].
            * eapply (Hmv y); [now apply Houttmv0|exact Hy].
            * exact (moved_by_disjoint_local st st3 st' y Hy (Houttmv y Hin)).
          + intros y Hy Hin. apply in_merge_inv in Hy as [Hy|Hy].
            * eapply (Houttsc y Hin). now apply amb_scoped.
            * eapply (Houttsc y Hin). now apply Hscrsty.
        - exact Hpairs. }

      (** the results' types, on the two sides *)
      assert (Forall2 (fun b t => t = lvar b) outt ts'') as Hevars'
          by (eapply evars_outt; eauto).
      assert (Forall2 (fun o t => satisfiable dlt4 (fst t) (merge amb [o]))
                outs ts'') as Hrelres.
      { clear - Hpairs Hevars'. revert ts'' Hevars'.
        induction Hpairs as [|o b outs0 outt0 (Hp & _) Hr IH];
          intros ts'' H; inv H; constructor.
        - subst. rewrite fst_lvar. exact Hp.
        - now apply IH. }

      exists dlt4. split; [|split; [|split; [|split]]].
      - exact Hoffall.
      - apply listSatisfiable_app. split; [rewrite Hce0'; exact Hcs04|].
        apply listSatisfiable_app. split.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st');
            [exact Hscope1| |exact Hoff1all|exact Hce1'].
          intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
          * eapply (Hmv y); [|exact Hin].
            apply (moved_by_suffix_local st st1 st' Hfa). exact Hy.
          * exact (moved_by_disjoint_local st st1 st' y Hin Hy).
        + apply listSatisfiable_app. split.
          * eapply listSatisfiable_off_scope
              with (sc := (scope ++ moved_by st st1) ++ moved_by st1 st2)
                   (xs := moved_by st2 st');
              [exact Hscope2| |exact Hoff34|exact Hce2'].
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- apply in_app_or in Hin as [Hin|Hin].
               ++ eapply (Hmv y); [|exact Hin].
                  apply (moved_by_suffix_local st st2 st' Hf02). exact Hy.
               ++ exact (moved_by_disjoint_local st st1 st' y Hin
                           (moved_by_suffix_local st1 st2 st' Hfb y Hy)).
            -- exact (moved_by_disjoint_local st1 st2 st' y Hin Hy).
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st2 st3) (xs := outt);
              [exact Hscope3| |exact Hoff4|exact Hce3'].
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- exact (Houttsc y Hy Hin).
            -- exact (moved_by_disjoint_local st2 st3 st' y Hin (Houttmv y Hy)).
      - rewrite Forall2_map_1. eapply Forall2_impl_In; [|exact Hrelres].
        intros o t Ho Ht Hot. cbn [fst]. exact Hot.
      - apply Forall_app. split.
        + rewrite Hce0'.
          eapply generate_constraints_scoped with (sig := sg);
            [eapply sig_scoped; exact Esg| | | | |exact Hgc].
          * rewrite Forall_map. eapply Forall_impl; [|exact Hsc_argt].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix_local st st2 st' Hf2').
          * rewrite Hckeq. eapply st_scoped_weaken;
              [apply incl_appl, incl_refl|].
            intros y Hy. exact (clk_types_scoped P es _ ckty Hwcg Hwces (or_introl (clk_src_base vars es)) Hck y Hy).
          * eapply st_scoped_weaken; [|exact Hscrst'].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix_local st st3 st' Hfd).
          * rewrite Forall_forall. intros b Hb. apply in_or_app. right.
            now apply Houttmv0.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix_local st st1 st' Hf1').
          * apply Forall_app. split.
            -- eapply Forall_impl; [|exact Hscope2].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app.
               ++ apply incl_app; [apply incl_appl, incl_refl|].
                  apply incl_appr, (moved_by_prefix_local st st1 st' Hf1').
               ++ apply incl_appr. eapply incl_tran;
                    [apply (moved_by_prefix_local st1 st2 st' Hf2')
                    |apply (moved_by_suffix_local st st1 st' Hfa)].
            -- eapply Forall_impl; [|exact Hscope3].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr. eapply incl_tran;
                 [apply (moved_by_prefix_local st2 st3 st' Hfd)
                 |apply (moved_by_suffix_local st st2 st' Hf02)].
      - eapply Forall2_right_In; [exact Hevars'|].
        intros b t Hb Heq. rewrite Heq, fst_lvar.
        intros y Hy. destruct Hy as [Hy|[]]; subst y.
        apply in_or_app. right. now apply Houttmv0.
    Qed.




  End Preservation.

End SecLusUnnestingCalls.
