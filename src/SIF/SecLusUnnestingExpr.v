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
From Velus Require Import SIF.SecLusUnnestingBase.

Module SecLusUnnestingExpr
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

Module BASE := SecLusUnnestingBase Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include BASE.

Import SECMONADNotations.
Import UNN.Fresh.Tactics.

  Section Preservation.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.

    (** The source node's variables, with their clocks.  Only the source
        expressions are ever checked against it. *)
    Variable vars    : list (ident * clock).

    (** The *target* node's declared clocks.  [lnode_clock_env_extended] above
        is what says using the target's here loses nothing: on every variable
        the source equations mention, the two environments answer alike. *)
    Variable cenv    : Env.t (type * clock).

    (** Every security name the *source* expression can mention: the names of
        the source node's own variables, and the names the security monad
        mints for its nested calls. *)
    Variable scope   : list ident.
    Variable stLo     : sec_state.
    Variable stF     : sec_state.

    (** The ambient every equation this expression gets lifted into sits
        under.  A parameter rather than a computed term: *which* ambient a
        lifted equation sits under is a fact about clocks, and belongs where
        the clocks are known.

        The premise that ties it down is deliberately syntactic -- [amb]
        contains the reset level and the clock level of every variable the
        run's emitted equations define, as lists of names.  [hm_ext] is
        monotone under inclusion, so domination follows; and a syntactic
        premise passes to the sub-expressions for free, since their emitted
        equations are a sublist of this one's. *)
    Variable amb     : ST.

    (** A program variable's security name, as the naming pass assigned it. *)
    Definition sec_of (xs : list ident) : list ident :=
      flat_map (fun x => match Env.find x env with
                         | Some b => [b]
                         | None   => []
                         end) xs.

    (** The variables unnesting created during one run, and their security
        names.  Indexed by the *pair* of states, not fixed once for the node:
        two sibling sub-expressions run over disjoint stretches of the fresh
        state, and it is exactly that disjointness that lets one sibling's
        conclusion survive the other's witness. *)
    Definition new_ids (st st' : fresh_st (type * clock)) : list ident :=
      filter (fun x => if in_dec ident_eq_dec x (st_ids st) then false else true)
        (st_ids st').

    Definition moved_by (st st' : fresh_st (type * clock)) : list ident :=
      sec_of (new_ids st st').

    Lemma new_ids_spec :
      forall st st' x,
        In x (new_ids st st') <-> In x (st_ids st') /\ ~ In x (st_ids st).
    Proof.
      intros st st' x. unfold new_ids. rewrite filter_In.
      destruct (in_dec ident_eq_dec x (st_ids st)); split;
        (intros (?&?) || intros ?); try tauto; try discriminate; auto.
    Qed.

    (** Widening a run widens what it may have moved, in both directions:
        a prefix and a suffix of a run both move inside the whole run's set.
        This is what passes the premise down to the sub-expressions and the
        conclusions back up. *)
    Lemma new_ids_prefix :
      forall st st1 st', st_follows st1 st' ->
        incl (new_ids st st1) (new_ids st st').
    Proof.
      intros st st1 st' Hf x Hx. apply new_ids_spec in Hx as (Hx & Hn).
      apply new_ids_spec. split; auto.
      unfold st_ids in *. apply in_map_iff in Hx as ((y&a) & ? & Hin); simpl in *; subst.
      apply in_map_iff. exists (x, a). split; auto.
      eapply st_follows_incl; eauto.
    Qed.

    Lemma new_ids_suffix :
      forall st st1 st', st_follows st st1 ->
        incl (new_ids st1 st') (new_ids st st').
    Proof.
      intros st st1 st' Hf x Hx. apply new_ids_spec in Hx as (Hx & Hn).
      apply new_ids_spec. split; auto.
      intro Hin. apply Hn.
      unfold st_ids in *. apply in_map_iff in Hin as ((y&a) & ? & Hin); simpl in *; subst.
      apply in_map_iff. exists (x, a). split; auto.
      eapply st_follows_incl; eauto.
    Qed.

    Lemma sec_of_incl :
      forall xs ys, incl xs ys -> incl (sec_of xs) (sec_of ys).
    Proof.
      intros xs ys Hincl b Hb.
      unfold sec_of in *. apply in_flat_map in Hb as (x & Hx & Hb).
      apply in_flat_map. exists x. auto.
    Qed.

    Corollary moved_by_prefix :
      forall st st1 st', st_follows st1 st' ->
        incl (moved_by st st1) (moved_by st st').
    Proof. intros. apply sec_of_incl, new_ids_prefix; auto. Qed.

    Corollary moved_by_suffix :
      forall st st1 st', st_follows st st1 ->
        incl (moved_by st1 st') (moved_by st st').
    Proof. intros. apply sec_of_incl, new_ids_suffix; auto. Qed.

    (** The complement of [agree_on]: the two valuations coincide everywhere
        *outside* a set.  This, and not [agree_on], is what the induction can
        carry.  [agree_on scope] says the witness keeps the visible names
        fixed but says nothing about the rest -- and "the rest" includes the
        names the security monad minted for a *sibling* sub-expression, whose
        constraints the sibling's own hypothesis still has to be applied to.
        A witness free to move those cannot be composed with its sibling's.
        Bounding the movement instead makes composition immediate: sibling
        constraints mention [scope] only, and [moved] misses [scope]. *)
    Definition agree_off (xs : list ident) (dlt1 dlt2 : ident -> Lat.t) : Prop :=
      forall x, ~ In x xs -> dlt1 x = dlt2 x.

    Lemma agree_off_refl : forall xs dlt, agree_off xs dlt dlt.
    Proof. intros xs dlt x _. reflexivity. Qed.

    Lemma agree_off_incl :
      forall xs ys dlt dlt',
        incl xs ys -> agree_off xs dlt dlt' -> agree_off ys dlt dlt'.
    Proof. intros xs ys d d' Hincl H x Hx. apply H. auto. Qed.

    Lemma agree_off_trans :
      forall xs dlt1 dlt2 dlt3,
        agree_off xs dlt1 dlt2 -> agree_off xs dlt2 dlt3 ->
        agree_off xs dlt1 dlt3.
    Proof.
      intros xs d1 d2 d3 H12 H23 x Hx.
      rewrite H12 by exact Hx. now apply H23.
    Qed.

    (** And nothing is lost: bounded movement still gives the visible
        agreement the node level asks for. *)
    Lemma agree_off_agree_on :
      forall xs dlt dlt',
        (forall x, In x xs -> ~ In x scope) ->
        agree_off xs dlt dlt' -> agree_on scope dlt dlt'.
    Proof.
      intros xs dlt dlt' Hfresh H x Hx. apply H. intro Hm.
      eapply Hfresh; eauto.
    Qed.

    Definition carries_at (P : global) (is_control : bool) (e : exp) : Prop :=
      forall es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        wl_exp P e ->
        wc_exp P vars e ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        (forall x ck ckty,
            In x (vars_defined eqs) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        unnest_exp P is_control e st = ((es', eqs), st') ->
        assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty es' yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le sst' stF -> sec_le stLo sst ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          (** What the emitted constraints and the target types are allowed to
              mention.  Without this the third conjunct does not survive a
              sibling's witness: the emitted set names the variables this run
              created, those are invisible to [scope], and nothing would then
              stop the sibling from moving them. *)
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    (** The two [is_control] branches of [Emerge] and [Eite] are different
        proofs -- one lifts and one does not -- so the statement is indexed by
        the flag and the expression-level property quantifies over it. *)
    Definition carries (P : global) (e : exp) : Prop :=
      forall is_control, carries_at P is_control e.

    (** Nothing was emitted, so nothing has to be satisfied. *)

    Lemma generate_leqns_constraints_cons :
      forall eq eqs,
        generate_leqns_constraints GL env base_ty rst_ty cenv (eq :: eqs)
        = (do c  <- generate_leqn_constraint GL env base_ty rst_ty cenv eq;
           do cs <- generate_leqns_constraints GL env base_ty rst_ty cenv eqs;
           SC.ret (c ++ cs)).
    Proof. reflexivity. Qed.

    Lemma generate_leqns_constraints_nil :
      forall ce xst xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv [] xst
          = OK (ce, xst') ->
        ce = [] /\ xst' = xst.
    Proof.
      intros ce xst xst' H. simpl in H. unfold ret in H. inv H. auto.
    Qed.

    (** The shape both leaves land in: the pass returned the expression
        untouched, so the two generators ran on the same term, and the
        witness is the valuation we started with. *)

    Lemma carries_unchanged :
      forall mv (ts ts'' : list LST) (ce : list constraint) dlt,
        ts'' = ts ->
        ce = [] ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        exists dlt',
          agree_off mv dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ mv) ce
          /\ Forall (fun t'' => st_scoped (scope ++ mv) (fst t'')) ts''.
    Proof.
      intros mv ts ts'' ce dlt Hts Hce Hsc; subst.
      exists dlt. split; [|split; [|split; [|split]]].
      - apply agree_off_refl.
      - constructor.
      - clear Hsc. induction ts as [|t ts IH]; [constructor|].
        constructor; [apply satisfiable_merge_r|exact IH].
      - constructor.
      - eapply Forall_impl; [|exact Hsc].
        intros t Ht. eapply st_scoped_weaken; [|exact Ht].
        apply incl_appl, incl_refl.
    Qed.

    Lemma carries_Econst : forall P c, carries P (Econst c).
    Proof.
      intros P c is_control es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst'
        dlt _ _ _ _ _ Hsc _ Hun Has Hgen Has' _ _ _.
      rewrite unnest_exp_Econst in Hun. inv Hun.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Econst in Has, Has'.
      unfold ret in Has, Has'. inv Has. inv Has'.
      eapply carries_unchanged; auto.
    Qed.

    Lemma carries_Evar : forall P x a, carries P (Evar x a).
    Proof.
      intros P x a is_control es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst'
        dlt _ _ _ _ _ Hsc _ Hun Has Hgen Has' _ _ _.
      rewrite unnest_exp_Evar in Hun. inv Hun.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      apply assign_lexps_single in Has'.
      apply assign_lexp_Evar_inv in Has as (b & Hb & ? & ?); subst.
      apply assign_lexp_Evar_inv in Has' as (b' & Hb' & ? & ?); subst.
      rewrite Hb in Hb'. inv Hb'.
      eapply carries_unchanged; auto.
    Qed.

    (** A one-stream sub-expression comes back as a one-element list, so
        [hd_default] is not losing anything -- which is why the unary and
        binary cases can hand their operand straight to the hypothesis. *)

    Lemma unnest_exp_one :
      forall P e es' eqs st st',
        wl_exp P e ->
        numstreams e = 1 ->
        unnest_exp P false e st = ((es', eqs), st') ->
        es' = [hd_default es'].
    Proof.
      intros P e es' eqs st st' Hwl Hnum Hun.
      eapply unnest_exp_length in Hun; eauto.
      rewrite Hnum in Hun.
      destruct es' as [|x [|]]; simpl in Hun; try discriminate; auto.
    Qed.

    Lemma carries_Eunop :
      forall P op e a, carries P e -> carries P (Eunop op e a).
    Proof.
      intros P op e a IH is_control es' eqs st st' ts sst sst' ce xst xst' ts''
        yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Eunop_inv in Hun as (e1' & st1 & Hun & ? & ?); subst.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Eunop in Has, Has'.
      eapply IH; eauto.
      - eapply unnest_exp_one in Hun as Hone; eauto.
        rewrite Hone at 1.
        apply assign_lexps_single_intro. exact Has'.
    Qed.

    (** * Composing two sub-expressions

        A compound expression emits the concatenation of what its operands
        emitted, and the generator is a fold over the equation list, so the
        generated set splits the same way.  This is the join point of the
        induction: the operands' hypotheses each produce a witness, and these
        are the lemmas that let the second witness be applied on top of the
        first without undoing it. *)

    Lemma generate_leqns_constraints_app :
      forall eqs1 eqs2 ce xst xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv (eqs1 ++ eqs2) xst
          = OK (ce, xst') ->
        exists ce1 ce2 xst1,
          generate_leqns_constraints GL env base_ty rst_ty cenv eqs1 xst
            = OK (ce1, xst1)
          /\ generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst1
            = OK (ce2, xst')
          /\ ce = ce1 ++ ce2.
    Proof.
      induction eqs1 as [|eq eqs1 IH]; intros eqs2 ce xst xst' H.
      - exists [], ce, xst. simpl. repeat split; auto.
      - simpl in H.
        eapply sec_bind_inv in H as (c & sta & Hc & H).
        eapply sec_bind_inv in H as (cs & stb & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        apply IH in Hcs as (ce1 & ce2 & xst1 & H1 & H2 & ?); subst.
        exists (c ++ ce1), ce2, xst1. split; [|split]; auto.
        + simpl. eapply sec_bind_ok; [exact Hc|].
          eapply sec_bind_ok; [exact H1|]. reflexivity.
        + now rewrite app_assoc.
    Qed.

    (** * What the run moved is what its equations define

        [unnest_exp_vars_perm] says the pass adds to the fresh state exactly
        the variables its emitted equations define.  With no duplicates, that
        turns the abstract [moved_by] into something concrete and checkable:
        the names this run may move are the security names of
        [vars_defined eqs] -- the same list the ambient premise quantifies
        over.

        This is also why the state-validity invariant does not have to be
        carried in Velus's own form.  All the lifting cases need of it is
        that what the run minted is new, and the permutation plus a single
        [NoDup] premise deliver exactly that, without the shrinking reusable
        set that [unnest_exp_st_valid] threads. *)

    Lemma map_bind2_unnest_vars_perm :
      forall P ic es es' eqs st st',
        Forall (wl_exp P) es ->
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        Permutation (vars_defined (List.concat eqs) ++ st_ids st) (st_ids st').
    Proof.
      intros P ic es es' eqs st st' Hwl Hmap.
      eapply map_bind2_vars_perm; eauto.
      eapply Forall_impl; [|exact Hwl].
      intros e He es'0 eqs0 st0 st0' Hun.
      eapply unnest_exp_vars_perm; eauto.
    Qed.

    Lemma NoDup_vd_app_l :
      forall (eqs1 eqs2 : list equation) (s : list ident),
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs1 ++ s).
    Proof.
      intros eqs1 eqs2 s H.
      rewrite vars_defined_app, <- app_assoc in H.
      rewrite Permutation_swap in H.
      eapply NoDup_app_r; eauto.
    Qed.

    Lemma NoDup_vd_app_r :
      forall (eqs1 eqs2 : list equation) (s s1 : list ident),
        Permutation (vars_defined eqs1 ++ s) s1 ->
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs2 ++ s1).
    Proof.
      intros eqs1 eqs2 s s1 Hperm H.
      rewrite <- Hperm.
      rewrite vars_defined_app, <- app_assoc in H.
      now rewrite Permutation_swap.
    Qed.

    Lemma NoDup_vd_drop :
      forall (eqs1 eqs2 : list equation) (s : list ident),
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs2 ++ s).
    Proof.
      intros eqs1 eqs2 s H.
      rewrite vars_defined_app, <- app_assoc in H.
      eapply NoDup_app_r; eauto.
    Qed.

    Lemma vars_defined_in_new_ids :
      forall eqs st st' x,
        Permutation (vars_defined eqs ++ st_ids st) (st_ids st') ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        In x (vars_defined eqs) ->
        In x (new_ids st st').
    Proof.
      intros eqs st st' x Hperm Hnd Hx.
      apply new_ids_spec. split.
      - rewrite <- Hperm. apply in_or_app. now left.
      - eapply NoDup_app_In; eauto.
    Qed.

    Corollary sec_of_vars_defined_moved :
      forall eqs st st' x b,
        Permutation (vars_defined eqs ++ st_ids st) (st_ids st') ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        In x (vars_defined eqs) ->
        Env.find x env = Some b ->
        In b (moved_by st st').
    Proof.
      intros eqs st st' x b Hperm Hnd Hx Hb.
      unfold moved_by, sec_of. apply in_flat_map.
      exists x. split; [eapply vars_defined_in_new_ids; eauto|].
      rewrite Hb. now left.
    Qed.

    Lemma vars_defined_incl_l :
      forall eqs1 eqs2, incl (vars_defined eqs1) (vars_defined (eqs1 ++ eqs2)).
    Proof.
      intros. rewrite vars_defined_app. apply incl_appl, incl_refl.
    Qed.

    Lemma vars_defined_incl_r :
      forall eqs1 eqs2, incl (vars_defined eqs2) (vars_defined (eqs1 ++ eqs2)).
    Proof.
      intros. rewrite vars_defined_app. apply incl_appr, incl_refl.
    Qed.

    Lemma listSatisfiable_app :
      forall dlt cs1 cs2,
        listSatisfiable dlt (cs1 ++ cs2)
        <-> listSatisfiable dlt cs1 /\ listSatisfiable dlt cs2.
    Proof. intros. unfold listSatisfiable. apply Forall_app. Qed.

    (** A type whose names the witness did not move keeps its meaning. *)

    Lemma hm_ext_off :
      forall (s : ST) xs dlt dlt',
        agree_off xs dlt dlt' ->
        (forall x, In x s -> ~ In x xs) ->
        hm_ext dlt s = hm_ext dlt' s.
    Proof.
      induction s as [|y s IH]; intros xs d d' Hoff Havoid; simpl; auto.
      rewrite (Hoff y) by (apply Havoid; now left).
      erewrite (IH xs); eauto.
      intros x Hx. apply Havoid. now right.
    Qed.

    Corollary satisfiable_off :
      forall u v xs dlt dlt',
        agree_off xs dlt dlt' ->
        (forall x, In x u -> ~ In x xs) ->
        (forall x, In x v -> ~ In x xs) ->
        satisfiable dlt u v -> satisfiable dlt' u v.
    Proof.
      intros u v xs dlt dlt' Hoff Hu Hv H. unfold satisfiable in *.
      erewrite <- (hm_ext_off u xs), <- (hm_ext_off v xs); eauto.
    Qed.

    (** The sibling transfer itself: a sub-expression's obligations mention
        only names the source can see, and a witness never moves those. *)

    Lemma listSatisfiable_off :
      forall cs xs dlt dlt',
        constraints_scoped scope cs ->
        (forall x, In x xs -> ~ In x scope) ->
        agree_off xs dlt dlt' ->
        listSatisfiable dlt cs ->
        listSatisfiable dlt' cs.
    Proof.
      intros cs xs dlt dlt' Hsc Hfresh Hoff Hsat.
      assert (agree_on scope dlt dlt') as Hagree
        by (eapply agree_off_agree_on; eauto).
      clear Hoff.
      unfold constraints_scoped, SymTypes.constraints_scoped in Hsc.
      unfold listSatisfiable in *.
      rewrite Forall_forall in Hsc, Hsat |- *.
      intros c Hin.
      eapply constraintSatisfiable_ext with (scope := scope); eauto.
      apply Hsc; exact Hin.
    Qed.

    (** And the arithmetic the joining rules need: an operand's bound still
        holds once the other operand is joined on the right. *)

    Lemma satisfiable_merge_grow_l :
      forall dlt a u v,
        satisfiable dlt a (merge u v) ->
        forall w, satisfiable dlt a (merge u (merge v w)).
    Proof.
      intros dlt a u v H w.
      eapply satisfiable_trans; [exact H|].
      apply satisfiable_merge_intro.
      - apply satisfiable_merge_l.
      - eapply satisfiable_trans; [apply satisfiable_merge_l|].
        apply satisfiable_merge_r.
    Qed.

    Lemma satisfiable_merge_grow_r :
      forall dlt a u w,
        satisfiable dlt a (merge u w) ->
        forall v, satisfiable dlt a (merge u (merge v w)).
    Proof.
      intros dlt a u w H v.
      eapply satisfiable_trans; [exact H|].
      apply satisfiable_merge_intro.
      - apply satisfiable_merge_l.
      - eapply satisfiable_trans; [apply satisfiable_merge_r|].
        apply satisfiable_merge_r.
    Qed.

    (** * Two operands, two witnesses

        The first genuine composition.  The two operands run over consecutive
        stretches of the fresh state, so the names the first witness moved are
        already in the state when the second starts, and the second therefore
        does not move them.  That is the whole argument, and it needs the
        naming pass to be injective: two distinct variables never share a
        security name, so disjoint variable sets give disjoint name sets. *)

    Hypothesis env_inj : env_injective env.

    (** The ambient names program variables only. *)
    Hypothesis amb_scoped : st_scoped scope amb.

    (** * What the call case assumes of the callees

        Three facts about the security global this node is typed against.
        None of them is about *this* node, and none can be read off the run:
        they are well-formedness of the signatures [GL] already holds, and
        they are discharged where [GL] is built.

        [sig_good] and [sig_nodup] are the shape [SIFSignature.v]'s
        reordering lemmas ask for -- one constraint per output, targets
        exactly the outputs, and formals all distinct.

        [sig_actuals_fresh] is the separation between a callee's formals and
        a caller's actuals.  It is stated as a property of a *successful*
        instantiation rather than of arbitrary actuals, which is what makes
        it true: the generator is only ever run on actuals the naming pass
        kept clear of the callee's private names. *)

    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.

    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).

    (** Every type the source typer produces mentions only names in [scope]:
        the source node's own variables' names, and the names the security
        monad minted for its nested calls.  That is exactly what [scope] is,
        and it is a parameter precisely so that this can be established once,
        where the monad's state and the naming pass are both in hand.  The
        expression-level statement's own scoping premises are instances of
        it; the call case needs it for the argument list, whose types its own
        result types say nothing about. *)

    Hypothesis source_types_scoped :
      source_types_scoped_upto GL env base_ty rst_ty vars scope stLo stF.

    Hypothesis source_lexps_scoped :
      source_lexps_scoped_upto GL env base_ty rst_ty vars scope stLo stF.

    (** The node's reset name, and the types its clocks get, are in [scope]
        for the same reason the typer's outputs are. *)

    Hypothesis rst_ty_scoped : In rst_ty scope.

    Hypothesis clk_types_scoped :
      forall P es ck ckty,
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

    (** [signature_scope] lists the formals clock and reset last; the
        substitution chain consumes them in pipeline order, inputs first.
        Same names, different order. *)

    Lemma signature_scope_perm :
      forall sg,
        Permutation (signature_scope sg)
          (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)).
    Proof.
      intros sg. unfold signature_scope.
      apply Permutation_app_head. apply Permutation_app_comm.
    Qed.

    Lemma sig_nodup_pipeline :
      forall f sg,
        find_signature f GL = Some sg ->
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)).
    Proof.
      intros f sg Hf. eapply Permutation_NoDup;
        [apply signature_scope_perm|eapply sig_nodup; exact Hf].
    Qed.

    Lemma call_subst_fresh_pipeline :
      forall sg inp1 inp2 ck1 ck2 rst1 rst2 os bs,
        call_subst_fresh sg inp1 ck1 rst1 os ->
        call_subst_fresh sg inp2 ck2 rst2 bs ->
        forall y, In y (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
          Forall (fun v => ~ In y v) inp1 /\ Forall (fun v => ~ In y v) inp2
          /\ ~ In y ck1 /\ ~ In y ck2 /\ ~ In y rst1 /\ ~ In y rst2
          /\ ~ In y os /\ ~ In y bs.
    Proof.
      intros sg inp1 inp2 ck1 ck2 rst1 rst2 os bs
        (Hi1 & Hc1 & Hr1 & Ho1) (Hi2 & Hc2 & Hr2 & Ho2) y Hy.
      assert (In y (signature_scope sg)) as Hy'
        by (eapply Permutation_in; [symmetry; apply signature_scope_perm|exact Hy]).
      unfold types_fresh, type_fresh, outputs_fresh in *.
      repeat split.
      - eapply Forall_impl; [|exact Hi1]. intros v Hv Hc.
        rewrite Forall_forall in Hv. now apply (Hv y).
      - eapply Forall_impl; [|exact Hi2]. intros v Hv Hc.
        rewrite Forall_forall in Hv. now apply (Hv y).
      - rewrite Forall_forall in Hc1. intro Hc. now apply (Hc1 y).
      - rewrite Forall_forall in Hc2. intro Hc. now apply (Hc2 y).
      - rewrite Forall_forall in Hr1. intro Hc. now apply (Hr1 y).
      - rewrite Forall_forall in Hr2. intro Hc. now apply (Hr2 y).
      - rewrite Forall_forall in Ho1. intro Hc. now apply (Ho1 y).
      - rewrite Forall_forall in Ho2. intro Hc. now apply (Ho2 y).
    Qed.

    Lemma moved_by_disjoint :
      forall sta stb stc x,
        In x (moved_by sta stb) -> ~ In x (moved_by stb stc).
    Proof.
      intros sta stb stc x Hx Hy.
      unfold moved_by, sec_of in *.
      apply in_flat_map in Hx as (u & Hu & Hx).
      apply in_flat_map in Hy as (v & Hv & Hy).
      destruct (Env.find u env) as [bu|] eqn:Eu; simpl in Hx; [|contradiction].
      destruct (Env.find v env) as [bv|] eqn:Ev; simpl in Hy; [|contradiction].
      destruct Hx as [Hx|[]]; destruct Hy as [Hy|[]]; subst.
      assert (u = v) as ? by (eapply env_inj; eauto); subst.
      apply new_ids_spec in Hu as (Hu & _).
      apply new_ids_spec in Hv as (_ & Hv). contradiction.
    Qed.

    (** The same transfer as [listSatisfiable_off], at whatever scope the
        constraints actually have -- the emitted ones name variables the
        source never had. *)

    Lemma listSatisfiable_off_scope :
      forall cs sc xs dlt dlt',
        constraints_scoped sc cs ->
        (forall x, In x xs -> ~ In x sc) ->
        agree_off xs dlt dlt' ->
        listSatisfiable dlt cs ->
        listSatisfiable dlt' cs.
    Proof.
      intros cs sc xs dlt dlt' Hsc Hfresh Hoff Hsat.
      assert (agree_on sc dlt dlt') as Hagree
        by (intros x Hx; apply Hoff; intro Hm; eapply Hfresh; eauto).
      clear Hoff.
      unfold constraints_scoped, SymTypes.constraints_scoped in Hsc.
      unfold listSatisfiable in *.
      rewrite Forall_forall in Hsc, Hsat |- *.
      intros c Hin.
      eapply constraintSatisfiable_ext with (scope := sc); eauto.
      apply Hsc; exact Hin.
    Qed.

    Lemma constraints_scoped_cmerge :
      forall sc c1 c2,
        constraints_scoped sc (cmerge c1 c2)
        <-> constraints_scoped sc c1 /\ constraints_scoped sc c2.
    Proof.
      intros sc c1 c2.
      unfold constraints_scoped, SymTypes.constraints_scoped.
      rewrite !Forall_forall. split.
      - intros H. split; intros c Hin; apply H, cmerge_In; tauto.
      - intros (H1 & H2) c Hin. apply cmerge_In in Hin. destruct Hin; auto.
    Qed.

    Lemma st_scoped_merge :
      forall sc u v,
        st_scoped sc u -> st_scoped sc v -> st_scoped sc (merge u v).
    Proof.
      intros sc u v Hu Hv x Hx. apply in_merge_inv in Hx as [Hx|Hx]; auto.
    Qed.

    Lemma st_scoped_merge_inv :
      forall sc u v,
        st_scoped sc (merge u v) -> st_scoped sc u /\ st_scoped sc v.
    Proof.
      intros sc u v H. split; intros x Hx; apply H.
      - now apply in_merge_left.
      - now apply in_merge_right.
    Qed.

    Lemma carries_Ebinop :
      forall P op e1 e2 a,
        carries P e1 -> carries P e2 -> carries P (Ebinop op e1 e2 a).
    Proof.
      intros P op e1 e2 a IH1 IH2 is_control es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has
        Hgen Has' Hcar Hbnd Hlow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Ebinop_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st1) as Hf1 by (eapply unnest_exp_st_follows; eauto).
      assert (st_follows st1 st') as Hf2 by (eapply unnest_exp_st_follows; eauto).

      (** the source side: two operand types, each a single flow *)
      rewrite assign_lexp_Ebinop in Has.
      eapply sec_bind_inv in Has as (t1 & sa & Ht1 & Has).
      eapply sec_bind_inv in Has as (t2 & sb & Ht2 & Has).
      eapply sec_bind_inv in Has as (a1 & sc1 & Ha1 & Has).
      eapply sec_bind_inv in Has as (a2 & sc2 & Ha2 & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Ha1 as (? & ?); subst.
      apply single_inv in Ha2 as (? & ?); subst.

      (** the target side, the same shape on the unnested operands *)
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Ebinop in Has'.
      eapply sec_bind_inv in Has' as (u1 & ya & Hu1 & Has').
      eapply sec_bind_inv in Has' as (u2 & yb & Hu2 & Has').
      eapply sec_bind_inv in Has' as (b1 & yc & Hb1 & Has').
      eapply sec_bind_inv in Has' as (b2 & yd & Hb2 & Hret').
      unfold ret in Hret'. inv Hret'.
      apply single_inv in Hb1 as (? & ?); subst.
      apply single_inv in Hb2 as (? & ?); subst.
      eapply unnest_exp_one in Hun1 as Hone1; eauto.
      eapply unnest_exp_one in Hun2 as Hone2; eauto.

      (** the emitted set splits with the emitted equations *)
      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each operand carries, and where its names live *)
      rewrite carried_ljoin in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
      inversion Hsts as [|z zs Hsts0 Hstsr]; subst. simpl in Hsts0.
      apply st_scoped_merge_inv in Hsts0 as (Hst1 & Hst2).
      assert (carried [a1] = snd a1) as Hc1 by (simpl; apply cmerge_nil).
      assert (carried [a2] = snd a2) as Hc2 by (simpl; apply cmerge_nil).

      (** the first operand *)
      assert (Permutation (vars_defined eqs1 ++ st_ids st) (st_ids st1)) as Hp1
          by (eapply unnest_exp_vars_perm with (e := e1); eauto).
      edestruct (IH1 false f1 eqs1 st st1 [a1] sst sa ce1 xst xst1 [b1] yst ya dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
      { now rewrite Hc1. }
      { constructor; [exact Hst1|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Ht1. }
      { exact Hgen1. }
      { rewrite Hone1 at 1. apply assign_lexps_single_intro. exact Hu1. }
      { now rewrite Hc1. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the second, on top of the first: its obligations name only what the
          source can see, and the first witness left all of that alone *)
      edestruct (IH2 false f2 eqs2 st1 st' [a2] sa sb ce2 xst1 xst' [b2] ya yb dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
      { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
      { now rewrite Hc2. }
      { constructor; [exact Hst2|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Ht2. }
      { exact Hgen2. }
      { rewrite Hone2 at 1. apply assign_lexps_single_intro. exact Hu2. }
      { eapply listSatisfiable_off with (xs := moved_by st st1).
        - now rewrite Hc2.
        - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
        - exact Hoff1.
        - now rewrite Hc2. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      inversion Hrel1 as [|p q ps qs Hr1 Hrel1r]; subst.
      inversion Hrel2 as [|p q ps qs Hr2 Hrel2r]; subst.
      inversion Hts1 as [|p ps Hb1s Hts1r]; subst.
      inversion Hts2 as [|p ps Hb2s Hts2r]; subst.

      (** the composite witness *)
      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        + eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
      - apply listSatisfiable_app. split; [|exact Hce2].
        eapply listSatisfiable_off_scope
          with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
        + exact Hscope1.
        + intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
          * eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact (moved_by_disjoint st st1 st' x Hx Hin).
        + exact Hoff2.
        + exact Hce1.
      - constructor; [|constructor]. unfold ljoin; simpl.
        apply satisfiable_merge_intro.
        + apply satisfiable_merge_grow_l.
          eapply satisfiable_off with (xs := moved_by st1 st').
          * exact Hoff2.
          * intros x Hx Hin. apply Hb1s in Hx.
            apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|now apply amb_scoped].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- eapply (Hmv x); [|now apply Hst1].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact Hr1.
        + now apply satisfiable_merge_grow_r.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
      - constructor; [|constructor]. unfold ljoin; simpl.
        apply st_scoped_merge.
        + eapply st_scoped_weaken; [|exact Hb1s].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply st_scoped_weaken; [|exact Hb2s].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Expression lists

        Every remaining constructor recurses through a list -- [unnest_exps]
        on one side, [assign_lexps] on the other -- so this is the gate.  The
        argument is the [Ebinop] argument folded: each element runs over the
        stretch of the fresh state the previous one left, so the witnesses
        chain, and each element's conclusion survives the rest because the
        rest moves elsewhere. *)

    Lemma assign_lexps_app_inv :
      forall es1 es2 ts st st',
        assign_lexps GL env base_ty rst_ty (es1 ++ es2) st = OK (ts, st') ->
        exists ts1 ts2 st1,
          assign_lexps GL env base_ty rst_ty es1 st = OK (ts1, st1)
          /\ assign_lexps GL env base_ty rst_ty es2 st1 = OK (ts2, st')
          /\ ts = ts1 ++ ts2.
    Proof.
      induction es1 as [|e es1 IH]; intros es2 ts st st' H.
      - exists [], ts, st. rewrite assign_lexps_nil. auto.
      - rewrite <- app_comm_cons, assign_lexps_cons in H.
        eapply sec_bind_inv in H as (t & sta & Ht & H).
        eapply sec_bind_inv in H as (r & stb & Hr & Hret).
        unfold ret in Hret. inv Hret.
        apply IH in Hr as (ts1 & ts2 & st1 & H1 & H2 & ?); subst.
        exists (t ++ ts1), ts2, st1. split; [|split]; auto.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [exact Ht|].
          eapply sec_bind_ok; [exact H1|]. reflexivity.
        + now rewrite app_assoc.
    Qed.

    Lemma assign_lexps_app_intro :
      forall es1 es2 ts1 ts2 st st1 st',
        assign_lexps GL env base_ty rst_ty es1 st = OK (ts1, st1) ->
        assign_lexps GL env base_ty rst_ty es2 st1 = OK (ts2, st') ->
        assign_lexps GL env base_ty rst_ty (es1 ++ es2) st
          = OK (ts1 ++ ts2, st').
    Proof.
      induction es1 as [|e es1 IH]; intros es2 ts1 ts2 st st1 st' H1 H2.
      - rewrite assign_lexps_nil in H1. unfold ret in H1. inv H1. exact H2.
      - rewrite assign_lexps_cons in H1.
        eapply sec_bind_inv in H1 as (t & sta & Ht & H1).
        eapply sec_bind_inv in H1 as (r & stb & Hr & Hret).
        unfold ret in Hret. inv Hret.
        rewrite <- app_comm_cons, assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [eapply IH; eauto|].
        unfold ret. now rewrite app_assoc.
    Qed.

    Lemma map_bind2_unnest_cons :
      forall P ic e es es' eqs st st',
        map_bind2 (unnest_exp P ic) (e :: es) st = ((es', eqs), st') ->
        exists e' eq1 st1 es'r eqsr,
          unnest_exp P ic e st = ((e', eq1), st1)
          /\ map_bind2 (unnest_exp P ic) es st1 = ((es'r, eqsr), st')
          /\ es' = e' :: es'r
          /\ eqs = eq1 :: eqsr.
    Proof.
      intros P ic e es es' eqs st st' H.
      simpl in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma map_bind2_unnest_nil :
      forall P ic es' eqs st st',
        map_bind2 (unnest_exp P ic) [] st = ((es', eqs), st') ->
        es' = [] /\ eqs = [] /\ st' = st.
    Proof.
      intros P ic es' eqs st st' H. simpl in H.
      rewrite ret_spec in H. inv H. repeat split.
    Qed.

    Lemma map_bind2_unnest_st_follows :
      forall P ic es es' eqs st st',
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        st_follows st st'.
    Proof.
      intros P ic es es' eqs st st' H.
      eapply map_bind2_st_follows; eauto.
      rewrite Forall_forall; intros; eauto.
    Qed.

    Definition carries_list (P : global) (es : list exp) : Prop :=
      forall ic es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        Forall (wl_exp P) es ->
        Forall (wc_exp P vars) es ->
        NoDup (vars_defined (List.concat eqs) ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        (forall x ck ckty,
            In x (vars_defined (List.concat eqs)) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv (List.concat eqs) xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty (List.concat es') yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le sst' stF -> sec_le stLo sst ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    Lemma carries_list_intro :
      forall P es, Forall (carries P) es -> carries_list P es.
    Proof.
      intros P es Hall.
      induction Hall as [|e es IHe IHes IH];
        intros ic es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
          Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.

      - (** nothing to unnest, nothing emitted *)
        apply map_bind2_unnest_nil in Hun as (? & ? & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has'
          as (? & _ & ?); subst.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. split; [|split; [|split; [|split]]];
          solve [apply agree_off_refl | constructor].

      - (** head, then tail on top of it *)
        inv Hwl. inv Hwc.
        apply map_bind2_unnest_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        assert (st_follows st st1) as Hf1 by (eapply unnest_exp_st_follows; eauto).
        assert (st_follows st1 st') as Hf2
            by (eapply map_bind2_unnest_st_follows; eauto).

        apply assign_lexps_carried_cons in Has
          as (t & r & sa & Ht & Hr & ? & Hcts); subst.
        simpl in Has'.
        apply assign_lexps_app_inv in Has'
          as (u & v & ya & Hu & Hv & ?); subst.
        simpl in Hgen.
        apply generate_leqns_constraints_app in Hgen
          as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

        rewrite Hcts in Hsc, Hcar.
        apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
        apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
        apply Forall_app in Hsts as (Hsts1 & Hsts2).

        assert (Permutation (vars_defined eq1 ++ st_ids st) (st_ids st1)) as Hp1
            by (eapply unnest_exp_vars_perm with (e := e); eauto).
        edestruct (IHe ic f1 eq1 st st1 t sst sa ce1 xst xst1 u yst ya dlt)
          as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
        { assumption. }
        { assumption. }
        { eapply NoDup_vd_app_l; exact Hnd. }
        { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
        { exact Hsc1. }
        { exact Hsts1. }
        { intros y cky ckty Hy. apply Hamb.
          apply vars_defined_incl_l; exact Hy. }
        { exact Hun1. }
        { exact Ht. }
        { exact Hgen1. }
        { exact Hu. }
        { exact Hcar1. }
        { eauto 4 with sec. }
        { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

        edestruct (IH ic fr eqsr st1 st' r sa sst' ce2 xst1 xst' v ya yst' dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
        { assumption. }
        { assumption. }
        { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
        { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
        { exact Hsc2. }
        { exact Hsts2. }
        { intros y cky ckty Hy. apply Hamb.
          apply vars_defined_incl_r; exact Hy. }
        { exact Hunr. }
        { exact Hr. }
        { exact Hgen2. }
        { exact Hv. }
        { eapply listSatisfiable_off with (xs := moved_by st st1).
          - exact Hsc2.
          - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
          - exact Hoff1.
          - exact Hcar2. }
        { eauto 4 with sec. }
        { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

        exists dlt2. split; [|split; [|split; [|split]]].
        + eapply agree_off_trans.
          * eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
          * eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
        + apply listSatisfiable_app. split; [|exact Hce2].
          eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
          * exact Hscope1.
          * intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * exact Hoff2.
          * exact Hce1.
        + apply Forall2_app; [|exact Hrel2].
          (** the head's bound survives the tail's witness: the head's target
              names were created before the tail started *)
          eapply Forall2_impl_In; [|exact Hrel1].
          intros p q Hp Hq Hpq.
          eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
          * intros x Hx Hin.
            eapply Forall_forall in Hts1; [|exact Hq]. apply Hts1 in Hx.
            apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|now apply amb_scoped].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- eapply (Hmv x); [|].
               ++ apply (moved_by_suffix st st1 st' Hf1). exact Hin.
               ++ eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hscope2].
            intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hts1].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hts2].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Sampling

        [Ewhen] lifts nothing: unnesting pushes the sampling inward, one
        [Ewhen] per resulting stream, and the typer's rule is a map.  So the
        target types are the source's transformation applied to the operands'
        target types, and the only thing to check is that the sampling
        variable's own level rides along on both sides -- which it does, by
        the same [ljoin _ (lvar g)]. *)

    Lemma unnest_exps_inv :
      forall P es es1 eqs st st',
        unnest_exps P es st = ((es1, eqs), st') ->
        exists ess eqss,
          map_bind2 (unnest_exp P false) es st = ((ess, eqss), st')
          /\ es1 = List.concat ess
          /\ eqs = List.concat eqss.
    Proof.
      intros P es es1 eqs st st' H.
      unfold unnest_exps in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma unnest_when_nil :
      forall ckid b tys ck, unnest_when ckid b [] tys ck = [].
    Proof. reflexivity. Qed.

    Lemma unnest_when_cons :
      forall ckid b e es ty tys ck,
        unnest_when ckid b (e :: es) (ty :: tys) ck
        = Ewhen [e] ckid b ([ty], ck) :: unnest_when ckid b es tys ck.
    Proof. reflexivity. Qed.

    Lemma assign_lexps_unnest_when_inv :
      forall ckid b (tys : list type) ck g (es : list exp) ts'' st st',
        Env.find ckid env = Some g ->
        List.length es = List.length tys ->
        assign_lexps GL env base_ty rst_ty (unnest_when ckid b es tys ck) st
          = OK (ts'', st') ->
        exists ts,
          assign_lexps GL env base_ty rst_ty es st = OK (ts, st')
          /\ ts'' = List.map (fun t => ljoin t (lvar g)) ts.
    Proof.
      intros ckid b tys ck g es. revert tys.
      induction es as [|e es IH]; intros tys ts'' st st' Hg Hlen Has.
      - destruct tys; simpl in Hlen; try discriminate.
        rewrite unnest_when_nil in Has.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        exists []. rewrite assign_lexps_nil. auto.
      - destruct tys as [|ty tys]; simpl in Hlen; try discriminate.
        rewrite unnest_when_cons in Has.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in Has
          as (t & r & sta & Ht & Hr & ? & _); subst.
        rewrite assign_lexp_Ewhen in Ht.
        eapply sec_bind_inv in Ht as (te & stm & Hte & Ht).
        eapply sec_bind_inv in Ht as (g' & stn & Hg' & Hret).
        unfold ret in Hret. inv Hret.
        apply find_env_inv in Hg' as (Hg' & ?); subst.
        rewrite Hg in Hg'. inv Hg'.
        apply assign_lexps_single in Hte.
        apply IH in Hr as (ts & Hts & ?); subst; auto.
        exists (te ++ ts). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [exact Hte|].
          eapply sec_bind_ok; [exact Hts|]. reflexivity.
        + now rewrite map_app.
    Qed.

    Lemma carried_cons :
      forall t ts, carried (t :: ts) = cmerge (snd t) (carried ts).
    Proof. reflexivity. Qed.

    Lemma carried_map_when :
      forall g ts,
        carried (List.map (fun t => ljoin t (lvar g)) ts) = carried ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl List.map. rewrite !carried_cons, IH.
      unfold ljoin, lvar. simpl snd. now rewrite cmerge_nil.
    Qed.

    Lemma carries_Ewhen :
      forall P es x b a, Forall (carries P) es -> carries P (Ewhen es x b a).
    Proof.
      intros P es x b [tys ck] Hall is_control es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has
        Hgen Has' Hcar Hbnd Hlow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Ewhen_inv in Hun as (es1 & Hunn & ?); subst.
      assert (List.length es1 = List.length tys) as Hlen
          by (erewrite unnest_exps_length; eauto).
      apply unnest_exps_inv in Hunn as (ess & eqss & Hmap & ? & ?); subst.

      (** the source: the operands' types, each sampled *)
      rewrite assign_lexp_Ewhen in Has.
      eapply sec_bind_inv in Has as (tes & sa & Htes & Has).
      eapply sec_bind_inv in Has as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      apply find_env_inv in Hg as (Hg & ?); subst.

      (** the target: the same map, over the unnested operands *)
      eapply assign_lexps_unnest_when_inv in Has' as (tes'' & Htes'' & ?);
        eauto.
      subst.

      (** the sampling variable is visible -- unless there are no streams at
          all, in which case it never appears and nothing needs it.  Its
          level is already inside the source type, and the source type is
          scoped, so this is read off the premises rather than assumed. *)
      assert (tes = [] \/ In g scope) as Hgs.
      { destruct tes as [|t0 tes0]; [now left|right].
        inversion Hsts as [|z zs Hz Hzr]; subst. simpl in Hz.
        apply Hz. apply in_merge_right. now left. }

      rewrite carried_map_when in Hsc, Hcar.
      assert (Forall (fun t => st_scoped scope (fst t)) tes) as Hstes.
      { clear - Hsts. induction tes as [|t tes IH]; constructor.
        - inversion Hsts as [|z zs Hz Hzr]; subst. simpl in Hz.
          apply st_scoped_merge_inv in Hz as (Hz & _); auto.
        - apply IH. inversion Hsts as [|z zs Hz Hzr]; subst; auto. }

      edestruct (carries_list_intro P es Hall false ess eqss st st' tes sst sa
                   ce xst xst' tes'' yst yst' dlt)
        as (dlt' & Hoff & Hce & Hrel & Hscope & Hts); eauto with sec.

      exists dlt'. split; [|split; [|split; [|split]]]; auto.
      - (** the sampling rides along on both sides *)
        clear - Hrel.
        induction Hrel as [|t t'' tes tes'' Hr Hrest IH]; [constructor|].
        constructor; auto.
        unfold ljoin; simpl. apply satisfiable_merge_intro.
        + now apply satisfiable_merge_grow_l.
        + eapply satisfiable_trans; [apply satisfiable_merge_r|].
          apply satisfiable_merge_r.
      - (** and stays inside the same bound *)
        destruct Hgs as [?|Hgs]; subst.
        + inversion Hrel; subst. constructor.
        + clear - Hts Hgs.
          induction Hts as [|t'' tes'' Hz Hzr IH]; [constructor|].
          constructor; auto.
          unfold ljoin; simpl. apply st_scoped_merge.
          * eapply st_scoped_weaken; [|exact Hz]. apply incl_refl.
          * intros y Hy. destruct Hy as [|[]]; subst.
            apply in_or_app; now left.
    Qed.

    (** * The componentwise join, related on both sides

        [Emerge] and [Eite] both build their result with
        [ljoin_list (map (ljoin (lvar g)) _) _], on the source and on the
        target alike.  So the relation between the two sides is established
        once, by walking the two joins together, and the two constructors
        then differ only in how they get their operands. *)

    Lemma ljoin_list_rel_head :
      forall dlt h h' ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin h t) ts) us s1 = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin h' t) ts') us' s2 = OK (rs', s2') ->
        satisfiable dlt (fst h') (merge amb (fst h)) ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros dlt h h' ts. revert h h'.
      induction ts as [|t ts IH];
        intros h h' us rs ts' us' rs' s1 s1' s2 s2' Hj Hj' Hh Hts Hus.
      - inv Hts. destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj.
        inv Hus. simpl in Hj'. unfold ret in Hj'. inv Hj'. constructor.
      - inversion Hts as [|t0 t0' ts0 ts0' Ht Htsr]; subst.
        destruct us as [|u us]; simpl in Hj; [discriminate|].
        inversion Hus as [|u0 u0' us0 us0' Hu Husr]; subst.
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        simpl in Hj'.
        eapply sec_bind_inv in Hj' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inv Hret'.
        constructor; [|eapply IH; eauto].
        rewrite !fst_ljoin.
        apply satisfiable_merge_intro; [apply satisfiable_merge_intro|].
        + (** the head -- a sampling variable, or the scrutinee's own type *)
          apply satisfiable_merge_grow_l, satisfiable_merge_grow_l. exact Hh.
        + apply satisfiable_merge_grow_l.
          eapply satisfiable_trans; [exact Ht|].
          apply satisfiable_merge_intro.
          * apply satisfiable_merge_l.
          * eapply satisfiable_trans; [apply satisfiable_merge_r|].
            apply satisfiable_merge_r.
        + now apply satisfiable_merge_grow_r.
    Qed.

    Corollary ljoin_list_rel :
      forall dlt g ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s1
          = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts') us' s2
          = OK (rs', s2') ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros. eapply ljoin_list_rel_head; eauto.
    Qed.

    Lemma ljoin_list_scoped_head :
      forall sc h ts us rs s s',
        st_scoped sc (fst h) ->
        ljoin_list (List.map (fun t => ljoin h t) ts) us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros sc h ts. revert h.
      induction ts as [|t ts IH]; intros h us rs s s' Hh Hj Hts Hus.
      - destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj. constructor.
      - destruct us as [|u us]; simpl in Hj; [discriminate|].
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        inversion Hts as [|z zs Hz Hzr]; subst.
        inversion Hus as [|w ws Hw Hwr]; subst.
        constructor; [|eapply IH with (h := h); eauto].
        rewrite !fst_ljoin.
        apply st_scoped_merge; [apply st_scoped_merge|]; auto.
    Qed.

    Corollary ljoin_list_scoped :
      forall sc g ts us rs s s',
        In g sc ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros. eapply ljoin_list_scoped_head; eauto.
      rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst; auto.
    Qed.

    Lemma ljoin_list_scoped_head_inv :
      forall sc h ts us rs s s',
        ljoin_list (List.map (fun t => ljoin h t) ts) us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us
        /\ (ts = [] \/ st_scoped sc (fst h)).
    Proof.
      intros sc h ts. revert h.
      induction ts as [|t ts IH]; intros h us rs s s' Hj Hrs.
      - destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj. auto.
      - destruct us as [|u us]; simpl in Hj; [discriminate|].
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        inversion Hrs as [|z zs Hz Hzr]; subst.
        apply IH in Hr as (Hts & Hus & _); auto.
        rewrite !fst_ljoin in Hz.
        apply st_scoped_merge_inv in Hz as (Hz & Hu).
        apply st_scoped_merge_inv in Hz as (Hgz & Ht).
        split; [|split].
        + constructor; auto.
        + constructor; auto.
        + right; auto.
    Qed.

    Corollary ljoin_list_scoped_inv :
      forall sc g ts us rs s s',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us
        /\ (ts = [] \/ In g sc).
    Proof.
      intros sc g ts us rs s s' Hj Hrs.
      eapply ljoin_list_scoped_head_inv in Hj as (? & ? & [?|Hg]); eauto.
      rewrite fst_lvar in Hg. repeat split; auto.
      right. apply Hg. now left.
    Qed.

    Lemma carried_map_merge_l :
      forall g ts,
        carried (List.map (fun t => ljoin (lvar g) t) ts) = carried ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl List.map. rewrite !carried_cons, IH.
      unfold ljoin, lvar. simpl snd. now rewrite cmerge_nil2.
    Qed.

    Lemma map_bind2_unnest_normalized :
      forall P es es' eqs st st',
        map_bind2 (unnest_exp P true) es st = ((es', eqs), st') ->
        Forall normalized_cexp (List.concat es').
    Proof.
      induction es as [|e es IH]; intros es' eqs st st' H.
      - apply map_bind2_unnest_nil in H as (? & ? & ?); subst. constructor.
      - apply map_bind2_unnest_cons in H
          as (e' & eq1 & st1 & es'r & eqsr & H1 & H2 & ? & ?); subst.
        simpl List.concat. apply Forall_app. split.
        + eapply unnest_exp_normalized_cexp; eauto.
        + eapply IH; eauto.
    Qed.

    (** * The merge, when it does not lift

        Under [is_control] the branches are unnested in place and the sampling
        is pushed inward.  Both sides then build the result the same way, so
        the whole case is the two branch lists composed -- as in [Ebinop] --
        followed by the join lemmas above. *)

    Lemma carries_Emerge_control :
      forall P ckid es1 es2 tys cl,
        Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P true (Emerge ckid es1 es2 (tys, cl)).
    Proof.
      intros P ckid es1 es2 tys cl Hall1 Hall2
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Emerge_control_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st1) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st') as Hf2
          by (eapply map_bind2_unnest_st_follows; eauto).

      (** the source: the two branches, joined *)
      rewrite assign_lexp_Emerge in Has.
      eapply sec_bind_inv in Has as (g & sa & Hg & Has).
      eapply sec_bind_inv in Has as (tes1 & sb & Htes1 & Has).
      eapply sec_bind_inv in Has as (tes2 & sc & Htes2 & Hj).
      apply find_env_inv in Hg as (Hg & ?); subst.

      (** the target: the same join, over the unnested branches *)
      assert (Forall normalized_cexp (List.concat f1)) as Hn1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat f2)) as Hn2
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat f1) = List.length tys) as Hl1
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat f2) = List.length tys) as Hl2
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      eapply assign_lexps_unnest_merge_inv in Has'
        as (tes1'' & tes2'' & Ht1'' & Ht2'' & ? & Hj''); eauto.
      subst.

      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each branch carries, and where its names live *)
      assert (carried ts = cmerge (carried tes1) (carried tes2)) as Hct.
      { erewrite ljoin_list_carried by exact Hj.
        now rewrite carried_map_merge_l. }
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
      eapply ljoin_list_scoped_inv in Hsts as (Hsts1 & Hsts2 & Hgs);
        [|exact Hj].

      assert (Permutation (vars_defined (List.concat eqs1) ++ st_ids st)
                (st_ids st1)) as Hp1
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      edestruct (carries_list_intro P es1 Hall1 true f1 eqs1 st st1 tes1 sst sb
                   ce1 xst xst1 tes1'' yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Htes1. }
      { exact Hgen1. }
      { exact Ht1''. }
      { exact Hcar1. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      edestruct (carries_list_intro P es2 Hall2 true f2 eqs2 st1 st' tes2 sb sc
                   ce2 xst1 xst' tes2'' yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
      { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
      { exact Hsc2. }
      { exact Hsts2. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Htes2. }
      { exact Hgen2. }
      { exact Ht2''. }
      { eapply listSatisfiable_off with (xs := moved_by st st1).
        - exact Hsc2.
        - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
        - exact Hoff1.
        - exact Hcar2. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the first branch's bound survives the second's witness *)
      assert (Forall2 (fun t t'' => satisfiable dlt2 (fst t'') (merge amb (fst t)))
                tes1 tes1'') as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
        - intros x Hx Hin.
          eapply Forall_forall in Hts1; [|exact Hq]. apply Hts1 in Hx.
          apply in_app_or in Hx as [Hx|Hx].
          + eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          + exact (moved_by_disjoint st st1 st' x Hx Hin).
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          + eapply (Hmv x); [|].
            * apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            * eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1. }

      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        + eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
      - apply listSatisfiable_app. split; [|exact Hce2].
        eapply listSatisfiable_off_scope
          with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
        + exact Hscope1.
        + intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
          * eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact (moved_by_disjoint st st1 st' x Hx Hin).
        + exact Hoff2.
        + exact Hce1.
      - eapply ljoin_list_rel; eauto.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
      - destruct Hgs as [?|Hgs]; subst.
        + (** no streams: the sampling variable never appears *)
          inversion Hrel1; subst. simpl in Hj''.
          destruct tes2'' as [|? ?]; [|discriminate].
          unfold ret in Hj''. inv Hj''. constructor.
        + eapply ljoin_list_scoped; [|exact Hj''| |].
          * apply in_or_app; now left.
          * eapply Forall_impl; [|exact Hts1].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hts2].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Reading a sub-obligation out of a larger one

        [Emerge] joins a variable's level, which carries nothing, so its
        result carries exactly what its branches carry.  [Eite] joins the
        scrutinee's whole type, which may itself carry a nested call's
        obligations, so the result carries the scrutinee's as well.  Rather
        than compute that set, note that both are *contained* in it, which is
        all an obligation set is ever used for. *)

    Lemma constraints_scoped_sub :
      forall sc cs cs',
        (forall c, In c cs' -> In c cs) ->
        constraints_scoped sc cs -> constraints_scoped sc cs'.
    Proof.
      intros sc cs cs' Hin Hsc.
      unfold constraints_scoped, SymTypes.constraints_scoped in *.
      rewrite Forall_forall in *. auto.
    Qed.

    Lemma listSatisfiable_sub :
      forall dlt cs cs',
        (forall c, In c cs' -> In c cs) ->
        listSatisfiable dlt cs -> listSatisfiable dlt cs'.
    Proof.
      intros dlt cs cs' Hin Hsat.
      unfold listSatisfiable in *. rewrite Forall_forall in *. auto.
    Qed.

    Lemma carried_map_ljoin_mono :
      forall h ts c,
        In c (carried ts) ->
        In c (carried (List.map (fun t => ljoin h t) ts)).
    Proof.
      induction ts as [|t ts IH]; intros c Hc; [contradiction|].
      rewrite carried_cons in Hc. simpl List.map. rewrite carried_cons.
      apply cmerge_In in Hc as [Hc|Hc]; apply cmerge_In.
      - left. unfold ljoin. simpl snd. apply cmerge_In. now right.
      - right. now apply IH.
    Qed.

    Lemma carried_map_ljoin_head :
      forall h t ts c,
        In c (snd h) ->
        In c (carried (List.map (fun u => ljoin h u) (t :: ts))).
    Proof.
      intros h t ts c Hc. simpl List.map. rewrite carried_cons.
      apply cmerge_In. left. unfold ljoin. simpl snd.
      apply cmerge_In. now left.
    Qed.

    (** * The conditional, when it does not lift

        Three sub-expressions rather than two, and the first of them supplies
        the head that the other two are joined under.  So the witness is
        built in three steps, and the scrutinee's own bound has to survive
        both of the branches' witnesses -- which it does, because all three
        run over consecutive stretches of the fresh state. *)

    Lemma carries_Eite_control :
      forall P e0 es1 es2 tys ck,
        carries P e0 -> Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P true (Eite e0 es1 es2 (tys, ck)).
    Proof.
      intros P e0 es1 es2 tys ck IH0 Hall1 Hall2
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Eite_control_inv in Hun
        as (f0 & eqs0 & st0 & f1 & eqs1 & st1 & f2 & eqs2
            & Hun0 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st0) as Hf0
          by (eapply unnest_exp_st_follows; eauto).
      assert (st_follows st0 st1) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st') as Hf2
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st0 st') as Hf0' by (etransitivity; eauto).
      assert (st_follows st st1) as Hf01 by (etransitivity; eauto).
      assert (st_follows st st') as Hf012 by (etransitivity; eauto).

      (** the source: the scrutinee, then the two branches joined under it *)
      rewrite assign_lexp_Eite in Has.
      eapply sec_bind_inv in Has as (t0 & sa & Ht0 & Has).
      eapply sec_bind_inv in Has as (th & sb & Hth & Has).
      eapply sec_bind_inv in Has as (tes1 & sc & Htes1 & Has).
      eapply sec_bind_inv in Has as (tes2 & sd & Htes2 & Hj).
      apply single_inv in Hth as (? & ?); subst.

      (** the branches have at least one stream, so the scrutinee really is
          read back on the target side *)
      assert (List.length tes1 = List.length tys) as Hlt1.
      { erewrite assign_lexps_length with (es := es1); eauto. }
      assert (tes1 <> []) as Hne1.
      { intro; subst. simpl in Hlt1. lia. }

      (** the target: the same shape, over the unnested pieces *)
      assert (Forall normalized_lexp f0) as Hn0
          by (eapply unnest_exp_normalized_lexp; eauto).
      assert (f0 = [hd_default f0]) as Hone0
          by (eapply unnest_exp_one; eauto).
      assert (Forall normalized_cexp (List.concat f1)) as Hn1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat f2)) as Hn2
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat f1) = List.length tys) as Hl1
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat f2) = List.length tys) as Hl2
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      assert (normalized_lexp (hd_default f0)) as Hn0'
        by (rewrite Hone0 in Hn0; now inv Hn0).
      eapply assign_lexps_unnest_ite_inv in Has'
        as (? & tes1'' & tes2'' & Ht1'' & Ht2'' & Hrest);
        [|exact Hn0'|exact Hn1|exact Hn2|exact Hl1|exact Hl2].
      subst.
      assert (List.length tes1'' = List.length tys) as Hlt1''.
      { rewrite <- Hl1. eapply assign_lexps_normalized_pure; eauto. }
      destruct Hrest as [(th'' & Hth'' & Hj'')|(Hnil & _ & _)];
        [|rewrite Hnil in Hlt1''; simpl in Hlt1''; lia].

      apply generate_leqns_constraints_app in Hgen
        as (ce0 & cer & xst0 & Hgen0 & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each piece carries, and where its names live *)
      assert (carried ts
              = cmerge (carried (List.map (fun t => ljoin th t) tes1))
                  (carried tes2)) as Hct
          by (eapply ljoin_list_carried; eauto).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (HscM & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (HcarM & Hcar2).
      assert (constraints_scoped scope (carried tes1)) as Hsc1
          by (eapply constraints_scoped_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (carried tes1)) as Hcar1
          by (eapply listSatisfiable_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HcarM]).
      destruct tes1 as [|tf tes1r]; [contradiction|].
      assert (constraints_scoped scope (snd th)) as Hsc0
          by (eapply constraints_scoped_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (snd th)) as Hcar0
          by (eapply listSatisfiable_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HcarM]).
      eapply ljoin_list_scoped_head_inv in Hsts as (Hsts1 & Hsts2 & Hgs);
        [|exact Hj].
      assert (st_scoped scope (fst th)) as Hst0
          by (destruct Hgs as [Hx|Hx]; [discriminate|exact Hx]).

      (** the scrutinee *)
      assert (Permutation (vars_defined eqs0 ++ st_ids st) (st_ids st0)) as Hp0
          by (eapply unnest_exp_vars_perm with (e := e0); eauto).
      assert (NoDup (vars_defined (List.concat eqs1 ++ List.concat eqs2)
                       ++ st_ids st0)) as Hnd0
          by (eapply NoDup_vd_app_r; [exact Hp0|exact Hnd]).
      assert (Permutation (vars_defined (List.concat eqs1) ++ st_ids st0)
                (st_ids st1)) as Hp1
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      edestruct (IH0 false f0 eqs0 st st0 [th] sst sa ce0 xst xst0
                   [th''] yst yst dlt)
        as (dlt0 & Hoff0 & Hce0 & Hrel0 & Hscope0 & Hts0).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }
      { simpl. now rewrite cmerge_nil. }
      { constructor; [exact Hst0|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun0. }
      { exact Ht0. }
      { exact Hgen0. }
      { rewrite Hone0 at 1. now apply assign_lexps_single_intro. }
      { simpl. now rewrite cmerge_nil. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the true branch, on top of it *)
      edestruct (carries_list_intro P es1 Hall1 true f1 eqs1 st0 st1
                   (tf :: tes1r) sa sc ce1 xst0 xst1 tes1'' yst yst dlt0)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd0. }
      { intros x Hx. apply Hmv.
        apply (moved_by_suffix st st0 st' Hf0).
        apply (moved_by_prefix st0 st1 st' Hf2). exact Hx. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r, vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Htes1. }
      { exact Hgen1. }
      { exact Ht1''. }
      { eapply listSatisfiable_off with (xs := moved_by st st0); eauto.
        intros x Hx. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** and the false branch on top of that *)
      edestruct (carries_list_intro P es2 Hall2 true f2 eqs2 st1 st' tes2 sc sd
                   ce2 xst1 xst' tes2'' yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd0]. }
      { intros x Hx. apply Hmv.
        apply (moved_by_suffix st st1 st' Hf01). exact Hx. }
      { exact Hsc2. }
      { exact Hsts2. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r, vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Htes2. }
      { exact Hgen2. }
      { exact Ht2''. }
      { eapply listSatisfiable_off with (xs := moved_by st0 st1); eauto.
        - intros x Hx. apply Hmv.
          apply (moved_by_suffix st st0 st' Hf0).
          apply (moved_by_prefix st0 st1 st' Hf2). exact Hx.
        - eapply listSatisfiable_off with (xs := moved_by st st0); eauto.
          intros x Hx. apply Hmv.
          apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the later witnesses do not undo the earlier ones *)
      assert (agree_off (moved_by st0 st') dlt0 dlt2) as Hoff02.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        - eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto. }

      assert (forall x, In x (moved_by st0 st') ->
                        ~ In x (scope ++ moved_by st st0)) as Hsep0.
      { intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
        - eapply (Hmv x); [|exact Hx].
          apply (moved_by_suffix st st0 st' Hf0). exact Hin.
        - exact (moved_by_disjoint st st0 st' x Hx Hin). }
      assert (forall x, In x (moved_by st1 st') ->
                        ~ In x (scope ++ moved_by st0 st1)) as Hsep1.
      { intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
        - eapply (Hmv x); [|exact Hx].
          apply (moved_by_suffix st st1 st' Hf01). exact Hin.
        - exact (moved_by_disjoint st0 st1 st' x Hx Hin). }

      inversion Hrel0 as [|p q ps qs Hr0 Hrel0r]; subst.
      assert (satisfiable dlt2 (fst th'') (merge amb (fst th))) as Hr0'.
      { eapply satisfiable_off with (xs := moved_by st0 st'); eauto.
        - intros x Hx Hin. apply (Hsep0 x Hin).
          inversion Hts0 as [|z zs Hz Hzr]; subst. now apply Hz.
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st0 st' Hf0). exact Hin.
          + eapply (Hmv x); [|now apply Hst0].
            apply (moved_by_suffix st st0 st' Hf0). exact Hin. }

      assert (Forall2 (fun t t'' => satisfiable dlt2 (fst t'') (merge amb (fst t)))
                (tf :: tes1r) tes1'') as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
        - intros x Hx Hin. apply (Hsep1 x Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st1 st' Hf01). exact Hin.
          + eapply (Hmv x); [|].
            * apply (moved_by_suffix st st1 st' Hf01). exact Hin.
            * eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1. }

      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff0].
          apply (moved_by_prefix st st0 st' Hf0').
        + eapply agree_off_incl; [|exact Hoff02].
          apply (moved_by_suffix st st0 st' Hf0).
      - apply listSatisfiable_app. split; [|apply listSatisfiable_app; split].
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st0) (xs := moved_by st0 st');
            eauto.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st0 st1) (xs := moved_by st1 st');
            eauto.
        + exact Hce2.
      - eapply ljoin_list_rel_head; eauto.
      - apply Forall_app. split; [|apply Forall_app; split].
        + eapply Forall_impl; [|exact Hscope0].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st0 st' Hf0').
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. eapply incl_tran;
            [apply (moved_by_prefix st0 st1 st' Hf2)
            |apply (moved_by_suffix st st0 st' Hf0)].
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st' Hf01).
      - eapply ljoin_list_scoped_head; [|exact Hj''| |].
        + inversion Hts0 as [|z zs Hz Hzr]; subst.
          eapply st_scoped_weaken; [|exact Hz].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st0 st' Hf0').
        + eapply Forall_impl; [|exact Hts1].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. eapply incl_tran;
            [apply (moved_by_prefix st0 st1 st' Hf2)
            |apply (moved_by_suffix st st0 st' Hf0)].
        + eapply Forall_impl; [|exact Hts2].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st' Hf01).
    Qed.

    (** * Extending the witness on the names the pass minted

        Every lifting constructor ends the same way: [idents_for_anns] mints
        one variable per result, the pass returns an [Evar] for each, and it
        emits one equation per result binding that variable to the compound
        expression it replaced.  So the target's type for a result is a bare
        name, and what pins that name down is the emitted equation's own
        constraint.

        The witness is therefore *chosen* rather than inherited: give each
        minted name exactly the value its defining constraint demands, and the
        emitted constraints hold by construction.  Two things make that
        legitimate.  The names are minted in this run, so moving them is
        within the bound the statement allows; and nothing the values are
        computed from mentions them, since everything else was minted earlier
        or is visible. *)

    Definition upd (b : ident) (v : Lat.t) (dlt : ident -> Lat.t)
      : ident -> Lat.t :=
      fun x => if ident_eq_dec x b then v else dlt x.

    Fixpoint upds (bs : list ident) (vs : list Lat.t) (dlt : ident -> Lat.t)
      : ident -> Lat.t :=
      match bs, vs with
      | b :: bs', v :: vs' => upd b v (upds bs' vs' dlt)
      | _, _ => dlt
      end.

    Lemma upds_notin :
      forall bs vs dlt x, ~ In x bs -> upds bs vs dlt x = dlt x.
    Proof.
      induction bs as [|b bs IH]; intros vs dlt x Hx; simpl; auto.
      destruct vs as [|v vs]; auto.
      unfold upd. destruct (ident_eq_dec x b) as [?|?]; subst.
      - exfalso. apply Hx. now left.
      - apply IH. intro; apply Hx. now right.
    Qed.

    Corollary upds_agree_off :
      forall bs vs dlt, agree_off bs dlt (upds bs vs dlt).
    Proof. intros bs vs dlt x Hx. symmetry. now apply upds_notin. Qed.

    Lemma upds_nth :
      forall bs vs dlt b v,
        NoDup bs ->
        List.length bs = List.length vs ->
        In (b, v) (combine bs vs) ->
        upds bs vs dlt b = v.
    Proof.
      induction bs as [|b0 bs IH]; intros vs dlt b v Hnd Hlen Hin;
        [contradiction|].
      destruct vs as [|v0 vs]; simpl in Hlen; [discriminate|].
      inv Hnd. simpl in Hin. destruct Hin as [Heq|Hin].
      - inv Heq. simpl. unfold upd.
        destruct (ident_eq_dec b b) as [?|Hne]; [reflexivity|].
        now elim Hne.
      - simpl. unfold upd.
        destruct (ident_eq_dec b b0) as [?|Hne]; subst.
        + exfalso. apply H1. eapply in_combine_l; eauto.
        + eapply IH; eauto.
    Qed.

    (** And the values themselves: a type whose names the extension did not
        touch means the same before and after. *)

    Lemma hm_ext_upds :
      forall (s : ST) bs vs dlt,
        (forall x, In x s -> ~ In x bs) ->
        hm_ext (upds bs vs dlt) s = hm_ext dlt s.
    Proof.
      intros s bs vs dlt Havoid. symmetry.
      eapply hm_ext_off with (xs := bs); [apply upds_agree_off|].
      intros x Hx. now apply Havoid.
    Qed.

    (** * The shape every lifting constructor ends in

        The pass returns one [Evar] per result and emits one equation per
        result.  [Efby] and [Earrow] spell the emitted list differently --
        one maps over a [combine], the other combines two maps -- so both are
        first put in the same form, and everything after is shared. *)

    Lemma assign_lexps_evars :
      forall (xs : list (ident * ann)) ts'' st st',
        assign_lexps GL env base_ty rst_ty
          (List.map (fun '(x, a) => Evar x a) xs) st = OK (ts'', st') ->
        st' = st
        /\ Forall2 (fun xa t => exists b, Env.find (fst xa) env = Some b
                                          /\ t = lvar b) xs ts''.
    Proof.
      induction xs as [|[x a] xs IH]; intros ts'' st st' H.
      - simpl List.map in H.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in H
          as (? & _ & ?); subst.
        split; auto.
      - simpl List.map in H.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        apply assign_lexp_Evar_inv in Ht as (b & Hb & ? & ?); subst.
        apply IH in Hr as (? & Hall); subst.
        split; auto. simpl List.app.
        constructor; auto. exists b. auto.
    Qed.

    Lemma emitted_defs_map_form :
      forall (xs : list (ident * ann)) (rhss : list exp),
        List.map (fun '((x, _), e) => ([x], [e])) (combine xs rhss)
        = List.map (fun '(x, e) => ([x], [e]))
            (combine (List.map fst xs) rhss).
    Proof.
      induction xs as [|[x a] xs IH]; intros rhss; [reflexivity|].
      destruct rhss as [|e rhss]; [reflexivity|].
      simpl. f_equal. apply IH.
    Qed.

    Lemma emitted_defs_combine_form :
      forall (xs : list (ident * ann)) (rhss : list exp),
        combine (List.map (fun '(id, _) => [id]) xs)
          (List.map (fun e => [e]) rhss)
        = List.map (fun '(x, e) => ([x], [e]))
            (combine (List.map fst xs) rhss).
    Proof.
      induction xs as [|[x a] xs IH]; intros rhss; [reflexivity|].
      destruct rhss as [|e rhss]; [reflexivity|].
      simpl. f_equal. apply IH.
    Qed.

    Lemma hm_ext_single :
      forall dlt b, hm_ext dlt [b] = Lat.join (dlt b) Lat.bottom.
    Proof. reflexivity. Qed.

    Lemma upd_same : forall b v dlt, upd b v dlt b = v.
    Proof.
      intros b v dlt. unfold upd.
      destruct (ident_eq_dec b b) as [?|Hne]; [reflexivity|now elim Hne].
    Qed.

    Lemma satisfiable_singleton :
      forall dlt b X,
        Lat.order (dlt b) (hm_ext dlt X) -> satisfiable dlt [b] X.
    Proof.
      intros dlt b X H. unfold satisfiable. simpl.
      apply Lat.join_least_upper_bound; auto.
    Qed.

    Lemma sec_of_cons_In :
      forall x xs b, Env.find x env = Some b -> In b (sec_of (x :: xs)).
    Proof.
      intros x xs b Hb. unfold sec_of. apply in_flat_map.
      exists x. split; [now left|]. rewrite Hb. now left.
    Qed.

    Lemma sec_of_incl_cons :
      forall x xs, incl (sec_of xs) (sec_of (x :: xs)).
    Proof.
      intros x xs b Hb. unfold sec_of in *.
      apply in_flat_map in Hb as (y & Hy & Hb).
      apply in_flat_map. exists y. split; auto. now right.
    Qed.

    Lemma sec_of_nIn :
      forall x xs b,
        ~ In x xs -> Env.find x env = Some b -> ~ In b (sec_of xs).
    Proof.
      intros x xs b Hx Hb Hin. unfold sec_of in Hin.
      apply in_flat_map in Hin as (y & Hy & Hin).
      destruct (Env.find y env) as [c|] eqn:Ey; simpl in Hin; [|contradiction].
      destruct Hin as [|[]]; subst.
      apply Hx. replace x with y; auto. symmetry. eapply env_inj; eauto.
    Qed.

    (** A defining equation of a minted variable, reduced.  The right-hand
        sides the lifting constructors emit are never calls, so the equation
        generator takes its ordinary-definition branch. *)

    Lemma generate_leqn_constraint_def :
      forall x e,
        (match e with Eapp _ _ _ _ => False | _ => True end) ->
        generate_leqn_constraint GL env base_ty rst_ty cenv ([x], [e])
        = generate_ldef_constraint GL env base_ty rst_ty cenv x e.
    Proof. intros x e He. destruct e; try reflexivity; contradiction. Qed.

    Lemma generate_ldef_constraint_inv :
      forall x e c xst xst',
        generate_ldef_constraint GL env base_ty rst_ty cenv x e xst
          = OK (c, xst') ->
        exists ck ckty tf b xst1,
          find_clock cenv x = OK ck
          /\ assign_clk_type env base_ty ck = Some ckty
          /\ assign_lexp_type GL env base_ty rst_ty e xst = OK ([tf], xst1)
          /\ Env.find x env = Some b
          /\ xst' = xst1
          /\ c = cmerge [(merge (merge [rst_ty] ckty) (fst tf), [b])] (snd tf).
    Proof.
      intros x e c xst xst' H.
      unfold generate_ldef_constraint in H.
      eapply sec_bind_inv in H as (ckty & sa & Hck & H).
      eapply sec_bind_inv in H as (ts & sb & Hts & H).
      eapply sec_bind_inv in H as (tf & sc & Htf & H).
      eapply sec_bind_inv in H as (b & sd & Hb & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Htf as (? & ?); subst.
      apply find_env_inv in Hb as (Hb & ?); subst.
      unfold eqn_clock_type in Hck.
      eapply sec_bind_inv in Hck as (ck & se & Hckr & Hcl).
      destruct (find_clock cenv x) as [ck'|] eqn:Ecl; [|discriminate].
      unfold res_to_sec, ret in Hckr. inv Hckr.
      apply option_to_sec_inv in Hcl as (Hcl & ?); subst.
      exists ck, ckty, tf, b, sb.
      split; [first [reflexivity|exact Ecl]|].
      split; [exact Hcl|].
      split; [exact Hts|].
      split; [exact Hb|].
      split; [reflexivity|].
      unfold lconstrain, ambient.
      rewrite !fst_ljoin, fst_lvar. simpl snd.
      now rewrite cmerge_nil2.
    Qed.

    (** * The emitted definitions of a lifting constructor

        One constraint per result, and the witness is chosen to satisfy it
        exactly.  The values are computed from types that live inside
        [bound], and the names being given values are outside [bound], so
        nothing here is self-referential. *)

    Lemma lifted_defs :
      forall bound (xs : list ident) (rhss : list exp) (srcs : list LST)
             ce xst xst' dlt,
        NoDup xs ->
        List.length xs = List.length rhss ->
        (forall b, In b (sec_of xs) -> ~ In b bound) ->
        (forall x ck ckty, In x xs ->
             find_clock cenv x = OK ck ->
             assign_clk_type env base_ty ck = Some ckty ->
             incl (merge [rst_ty] ckty) amb) ->
        st_scoped bound amb ->
        Forall (fun e => (match e with Eapp _ _ _ _ => False | _ => True end)
                         /\ forall ts s s',
                              assign_lexp_type GL env base_ty rst_ty e s
                                = OK (ts, s') ->
                              s' = s /\ List.length ts = 1 /\ carried ts = [])
          rhss ->
        Forall (fun src => st_scoped bound (fst src)) srcs ->
        Forall2 (fun e src =>
            forall tf s s',
              assign_lexp_type GL env base_ty rst_ty e s = OK ([tf], s') ->
              satisfiable dlt (fst tf) (merge amb (fst src))
              /\ st_scoped bound (fst tf)) rhss srcs ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e])) (combine xs rhss)) xst
          = OK (ce, xst') ->
        exists dlt',
          agree_off (sec_of xs) dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ constraints_scoped (bound ++ sec_of xs) ce
          /\ Forall2 (fun x src => forall b, Env.find x env = Some b ->
                          satisfiable dlt' [b] (merge amb (fst src)))
               xs srcs.
    Proof.
      intros bound xs. revert bound.
      induction xs as [|x xs IH];
        intros bound rhss srcs ce xst xst' dlt
          Hnd Hlen Hsep Hamb Hambsc Hpure Hsrcsc Hrel Hgen.
      - destruct rhss; simpl in Hlen; [|discriminate].
        inv Hrel. simpl in Hgen.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. split; [apply agree_off_refl|].
        split; [constructor|split; [constructor|constructor]].
      - destruct rhss as [|e rhss]; simpl in Hlen; [discriminate|].
        inversion Hrel as [|e0 src0 rhss0 srcs0 Hr Hrelr]; subst.
        inversion Hnd as [|x0 xs0 Hxn Hndr]; subst.
        inversion Hpure as [|e1 rhss1 Hhead Hpurer]; subst.
        inversion Hsrcsc as [|s0 srcs1 Hs0 Hsrcsr]; subst.
        replace (List.map (fun '(x0, e0) => ([x0], [e0]))
                   (combine (x :: xs) (e :: rhss)))
          with (([x], [e])
                :: List.map (fun '(x0, e0) => ([x0], [e0])) (combine xs rhss))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by tauto.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        destruct Hhead as (_ & Hp).
        specialize (Hp _ _ _ Htf) as (? & _ & Hcar); subst xstm.
        rewrite carried_single in Hcar. rewrite Hcar, cmerge_nil.
        specialize (Hr _ _ _ Htf) as (Hdom & Hsc).

        (** the rest of the results *)
        edestruct (IH bound rhss srcs0 cs xst xst' dlt)
          as (dlt1 & Hoff1 & Hce1 & Hscope1 & Hrel1); auto.
        { intros b' Hb'. apply Hsep. now apply sec_of_incl_cons. }
        { intros y cky ckty' Hy. apply Hamb. now right. }

        (** this result: its name gets exactly what its constraint demands *)
        assert (~ In b (sec_of xs)) as Hbx by (eapply sec_of_nIn; eauto).
        assert (~ In b bound) as Hbb by (apply Hsep; eapply sec_of_cons_In; eauto).
        assert (forall X, st_scoped bound X ->
                          hm_ext dlt1 X = hm_ext dlt X) as Hstable.
        { intros X HX. symmetry. eapply hm_ext_off with (xs := sec_of xs); eauto.
          intros y Hy Hin. eapply Hsep; [now apply sec_of_incl_cons; exact Hin|].
          now apply HX. }
        assert (st_scoped bound (merge (merge [rst_ty] ckty) (fst tf))) as Hlsc.
        { apply st_scoped_merge; auto.
          intros y Hy. apply Hambsc. eapply Hamb; eauto. now left. }
        assert (st_scoped bound (merge amb (fst src0))) as Hmsc
            by (apply st_scoped_merge; auto).
        assert (forall X, st_scoped bound X ->
                  hm_ext (upd b (hm_ext dlt1
                                   (merge (merge [rst_ty] ckty) (fst tf)))
                            dlt1) X = hm_ext dlt1 X) as Hstable'.
        { intros X HX. symmetry.
          eapply hm_ext_off with (xs := [b]).
          - intros y Hy. unfold upd.
            destruct (ident_eq_dec y b) as [?|?];
              [exfalso; apply Hy; now left|reflexivity].
          - intros y Hy Hin. destruct Hin as [|[]]; subst. now apply Hbb, HX. }
        assert (satisfiable dlt (merge (merge [rst_ty] ckty) (fst tf))
                  (merge amb (fst src0))) as Hkey.
        { apply satisfiable_merge_intro; [|exact Hdom].
          eapply Lat.order_trans;
            [apply hm_ext_incl, (Hamb x ck ckty); auto; now left|].
          apply satisfiable_merge_l. }

        exists (upd b (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1).
        split; [|split; [|split]].
        + (** only the minted names moved *)
          intros y Hy. rewrite (Hoff1 y); [|intro; apply Hy;
                                            now apply sec_of_incl_cons].
          unfold upd. destruct (ident_eq_dec y b) as [?|?]; [|reflexivity].
          subst. exfalso. apply Hy. eapply sec_of_cons_In; eauto.
        + (** the emitted constraints hold, by construction *)
          apply listSatisfiable_app. split.
          * constructor; [|constructor].
            unfold constraintSatisfiable, satisfiable.
            rewrite hm_ext_single, upd_same, (Hstable' _ Hlsc).
            apply Lat.join_bound1.
          * eapply listSatisfiable_off_scope
              with (sc := bound ++ sec_of xs) (xs := [b]); eauto.
            -- intros y Hy Hin. destruct Hy as [|[]]; subst.
               apply in_app_or in Hin as [Hin|Hin]; [now apply Hbb|now apply Hbx].
            -- intros y Hy. unfold upd.
               destruct (ident_eq_dec y b) as [?|?];
                 [exfalso; apply Hy; now left|reflexivity].
        + (** and stay inside the bound *)
          apply Forall_app. split.
          * constructor; [|constructor].
            intros y Hy. unfold constraint_scope in Hy. simpl in Hy.
            apply in_app_or in Hy as [Hy|Hy].
            -- apply in_or_app. left. now apply Hlsc.
            -- destruct Hy as [|[]]; subst. apply in_or_app. right.
               eapply sec_of_cons_In; eauto.
          * eapply Forall_impl; [|exact Hscope1].
            intros c0 Hc0. eapply constraint_scoped_incl; [|exact Hc0].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, sec_of_incl_cons.
        + (** each result's name dominates the source it replaced *)
          constructor.
          * intros b' Hb'. rewrite Hb in Hb'. inv Hb'.
            apply satisfiable_singleton. rewrite upd_same.
            rewrite (Hstable' _ Hmsc), (Hstable _ Hlsc), (Hstable _ Hmsc).
            exact Hkey.
          * eapply Forall2_impl_In; [|exact Hrel1].
            intros y src Hy Hsrc Hyr b' Hb'.
            eapply satisfiable_off with (xs := [b]); eauto.
            -- intros z Hz. unfold upd.
               destruct (ident_eq_dec z b) as [?|?];
                 [exfalso; apply Hz; now left|reflexivity].
            -- intros z Hz Hin. destruct Hz as [|[]]; subst.
               destruct Hin as [|[]]; subst.
               apply Hbx. unfold sec_of. apply in_flat_map.
               exists y. split; auto. rewrite Hb'. now left.
            -- intros z Hz Hin. destruct Hin as [|[]]; subst.
               apply in_merge_inv in Hz as [Hz|Hz].
               ++ now apply Hbb, Hambsc.
               ++ apply Hbb. eapply Forall_forall in Hsrcsr; [|exact Hsrc].
                  now apply Hsrcsr.
    Qed.

    (** * The delay, and the initialised delay

        [Efby] and [Earrow] lift the same way: the operands are unnested, the
        pass builds one delay per result out of the i-th of each, mints a
        variable for it and emits its defining equation.  Both sides then
        build their result with the plain componentwise join -- no head -- so
        the join lemmas are reused at [lbot]. *)

    Lemma satisfiable_nil : forall dlt X, satisfiable dlt [] X.
    Proof. intros. unfold satisfiable. simpl. apply Lat.bottom_is_bottom. Qed.

    Lemma map_ljoin_lbot :
      forall ts, List.map (fun t => ljoin lbot t) ts = ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl. rewrite IH. f_equal. unfold ljoin, lbot. simpl.
      rewrite merge_nil2, cmerge_nil2. now destruct t.
    Qed.

    Corollary ljoin_list_rel_plain :
      forall dlt ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list ts us s1 = OK (rs, s1') ->
        ljoin_list ts' us' s2 = OK (rs', s2') ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros dlt ts us rs ts' us' rs' s1 s1' s2 s2' Hj Hj' Hts Hus.
      eapply ljoin_list_rel_head with (h := lbot) (h' := lbot);
        try rewrite map_ljoin_lbot; eauto.
    Qed.

    Corollary ljoin_list_scoped_plain :
      forall sc ts us rs s s',
        ljoin_list ts us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros sc ts us rs s s' Hj Hts Hus.
      eapply ljoin_list_scoped_head with (h := lbot);
        try rewrite map_ljoin_lbot; eauto.
      intros y Hy. contradiction.
    Qed.

    Corollary ljoin_list_scoped_plain_inv :
      forall sc ts us rs s s',
        ljoin_list ts us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us.
    Proof.
      intros sc ts us rs s s' Hj Hrs.
      rewrite <- (map_ljoin_lbot ts) in Hj.
      eapply ljoin_list_scoped_head_inv in Hj as (? & ? & _); eauto.
    Qed.

    Lemma assign_lexps_elementwise :
      forall es ts st st',
        Forall normalized_cexp es ->
        assign_lexps GL env base_ty rst_ty es st = OK (ts, st') ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es ts.
    Proof.
      induction es as [|e es IH]; intros ts st st' Hn H.
      - apply (assign_lexps_carried_nil GL env base_ty rst_ty) in H
          as (? & _ & ?); subst. constructor.
      - inv Hn.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        assert (sta = st /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (t, s))
          as (? & Hlt & Hc & Hs)
          by (eapply assign_lexp_normalized_cexp_pure; eauto).
        subst sta.
        destruct t as [|a [|]]; simpl in Hlt; try discriminate.
        rewrite carried_single in Hc.
        simpl List.app. constructor; [split; [exact Hs|exact Hc]|].
        eapply IH; eauto.
    Qed.

    Lemma unnest_fby_nil :
      forall es anns, unnest_fby [] es anns = [].
    Proof. reflexivity. Qed.

    Lemma unnest_fby_cons :
      forall e0 e0s e es a anns,
        unnest_fby (e0 :: e0s) (e :: es) (a :: anns)
        = Efby [e0] [e] [a] :: unnest_fby e0s es anns.
    Proof. reflexivity. Qed.

    Lemma unnest_arrow_nil :
      forall es anns, unnest_arrow [] es anns = [].
    Proof. reflexivity. Qed.

    Lemma unnest_arrow_cons :
      forall e0 e0s e es a anns,
        unnest_arrow (e0 :: e0s) (e :: es) (a :: anns)
        = Earrow [e0] [e] [a] :: unnest_arrow e0s es anns.
    Proof. reflexivity. Qed.

    Lemma assign_lexp_fby_type :
      forall e0 e a t0 t1 tf s s',
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty (Efby [e0] [e] [a]) s
          = OK ([tf], s') ->
        tf = ljoin t0 t1.
    Proof.
      intros e0 e a t0 t1 tf s s' H0 H1 H.
      rewrite assign_lexp_Efby in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht.
      rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma assign_lexp_arrow_type :
      forall e0 e a t0 t1 tf s s',
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty (Earrow [e0] [e] [a]) s
          = OK ([tf], s') ->
        tf = ljoin t0 t1.
    Proof.
      intros e0 e a t0 t1 tf s s' H0 H1 H.
      rewrite assign_lexp_Earrow in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht.
      rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma vars_defined_defs :
      forall (bs : list ident) (rhss : list exp),
        List.length bs = List.length rhss ->
        vars_defined (List.map (fun '(x, e) => ([x], [e])) (combine bs rhss))
        = bs.
    Proof.
      induction bs as [|b bs IH]; intros rhss Hlen; [reflexivity|].
      destruct rhss as [|e rhss]; simpl in Hlen; [discriminate|].
      simpl. f_equal. apply IH. congruence.
    Qed.

    Lemma assign_lexp_fby_pure :
      forall e0 e a t0 t1,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty (Efby [e0] [e] [a]) s
            = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros e0 e a t0 t1 H0 H1 Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Efby in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin. simpl snd.
      rewrite Hc0, Hc1. reflexivity.
    Qed.

    Lemma assign_lexp_arrow_pure :
      forall e0 e a t0 t1,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty (Earrow [e0] [e] [a]) s
            = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros e0 e a t0 t1 H0 H1 Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Earrow in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin. simpl snd.
      rewrite Hc0, Hc1. reflexivity.
    Qed.

    (** The delays the pass builds, typed: the i-th delay's type is the i-th
        componentwise join of the operands' types, which is the same function
        of them that the source rule is of the source operands' types. *)

    Lemma unnest_fby_types :
      forall (e0s es : list exp) (anns : list ann) ts0 us s,
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) e0s ts0 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es us ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        exists rs,
          ljoin_list ts0 us s = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_fby e0s es anns) rs.
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts0 us s H0 H1 Hl0 Hl1.
      - inv H0. destruct anns; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate]. inv H1.
        exists []. split; [reflexivity|constructor].
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inversion H0 as [|p q ps qs Hp H0r]; subst.
        inversion H1 as [|p2 q2 ps2 qs2 Hp2 H1r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct IH as (rs & Hj & Hall); eauto.
        exists (ljoin q q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_fby_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_fby_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_fby_type; eauto.
    Qed.

    Lemma unnest_arrow_types :
      forall (e0s es : list exp) (anns : list ann) ts0 us s,
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) e0s ts0 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es us ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        exists rs,
          ljoin_list ts0 us s = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_arrow e0s es anns) rs.
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts0 us s H0 H1 Hl0 Hl1.
      - inv H0. destruct anns; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate]. inv H1.
        exists []. split; [reflexivity|constructor].
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inversion H0 as [|p q ps qs Hp H0r]; subst.
        inversion H1 as [|p2 q2 ps2 qs2 Hp2 H1r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct IH as (rs & Hj & Hall); eauto.
        exists (ljoin q q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_arrow_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_arrow_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_arrow_type; eauto.
    Qed.

    (** * Recovering the operands from the emitted equations

        For [Ewhen], [Emerge] and [Eite] the operands' target typings come out
        of the target typing of the whole expression, because the target
        expression list is built from the unnested operands.  For [Efby] and
        [Earrow] it is not: the target list is the minted variables, and the
        operands appear only inside the emitted equations, as the operands of
        the delays those equations bind.  So they are recovered from the
        emitted block instead. *)

    Lemma defs_operand_types_fby :
      forall (bs : list ident) (e0s es : list exp) (anns : list ann)
             ce xst xst',
        Forall normalized_lexp e0s ->
        Forall normalized_lexp es ->
        List.length bs = List.length anns ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_fby e0s es anns))) xst = OK (ce, xst') ->
        exists ts0 us,
          assign_lexps GL env base_ty rst_ty e0s xst = OK (ts0, xst)
          /\ assign_lexps GL env base_ty rst_ty es xst = OK (us, xst).
    Proof.
      induction bs as [|b bs IH];
        intros e0s es anns ce xst xst' Hn0 Hn1 Hlb Hl0 Hl1 Hgen.
      - destruct anns; simpl in Hlb; [|discriminate].
        destruct e0s; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct anns as [|a anns]; simpl in Hlb; [discriminate|].
        destruct e0s as [|e0 e0s]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_fby_cons in Hgen.
        replace (List.map (fun '(x0, e1) => ([x0], [e1]))
                   (combine (b :: bs) (Efby [e0] [e] [a] :: unnest_fby e0s es anns)))
          with (([b], [Efby [e0] [e] [a]])
                :: List.map (fun '(x0, e1) => ([x0], [e1]))
                     (combine bs (unnest_fby e0s es anns)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Efby in Htf.
        eapply sec_bind_inv in Htf as (t & sa & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sb & Hu & Hj).
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sa = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                              = OK (t, s)) as (? & _ & _ & Hs0)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
        subst sa.
        assert (sb = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (u, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        subst sb.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH e0s es anns cs xst xst') as (ts0 & us & Hts0 & Hus);
          eauto.
        exists (t ++ ts0), (u ++ us). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs0|].
          eapply sec_bind_ok; [exact Hts0|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hus|]. reflexivity.
    Qed.

    Lemma defs_operand_types_arrow :
      forall (bs : list ident) (e0s es : list exp) (anns : list ann)
             ce xst xst',
        Forall normalized_lexp e0s ->
        Forall normalized_lexp es ->
        List.length bs = List.length anns ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_arrow e0s es anns))) xst = OK (ce, xst') ->
        exists ts0 us,
          assign_lexps GL env base_ty rst_ty e0s xst = OK (ts0, xst)
          /\ assign_lexps GL env base_ty rst_ty es xst = OK (us, xst).
    Proof.
      induction bs as [|b bs IH];
        intros e0s es anns ce xst xst' Hn0 Hn1 Hlb Hl0 Hl1 Hgen.
      - destruct anns; simpl in Hlb; [|discriminate].
        destruct e0s; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct anns as [|a anns]; simpl in Hlb; [discriminate|].
        destruct e0s as [|e0 e0s]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_arrow_cons in Hgen.
        replace (List.map (fun '(x0, e1) => ([x0], [e1]))
                   (combine (b :: bs)
                      (Earrow [e0] [e] [a] :: unnest_arrow e0s es anns)))
          with (([b], [Earrow [e0] [e] [a]])
                :: List.map (fun '(x0, e1) => ([x0], [e1]))
                     (combine bs (unnest_arrow e0s es anns)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Earrow in Htf.
        eapply sec_bind_inv in Htf as (t & sa & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sb & Hu & Hj).
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sa = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                              = OK (t, s)) as (? & _ & _ & Hs0)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
        subst sa.
        assert (sb = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (u, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        subst sb.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH e0s es anns cs xst xst') as (ts0 & us & Hts0 & Hus);
          eauto.
        exists (t ++ ts0), (u ++ us). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs0|].
          eapply sec_bind_ok; [exact Hts0|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hus|]. reflexivity.
    Qed.

    Lemma map_bind2_unnest_normalized_lexp :
      forall P es es' eqs st st',
        map_bind2 (unnest_exp P false) es st = ((es', eqs), st') ->
        Forall normalized_lexp (List.concat es').
    Proof.
      induction es as [|e es IH]; intros es' eqs st st' H.
      - apply map_bind2_unnest_nil in H as (? & ? & ?); subst. constructor.
      - apply map_bind2_unnest_cons in H
          as (e' & eq1 & st1 & es'r & eqsr & H1 & H2 & ? & ?); subst.
        simpl List.concat. apply Forall_app. split.
        + eapply unnest_exp_normalized_lexp; eauto.
        + eapply IH; eauto.
    Qed.

    Lemma Forall2_combine_via :
      forall {A B C : Type} (P : A -> C -> Prop) (Q : B -> C -> Prop)
             (R : A -> B -> Prop) (l1 : list A) (l2 : list B) (l3 : list C),
        Forall2 P l1 l3 -> Forall2 Q l2 l3 ->
        (forall a b c, P a c -> Q b c -> R a b) ->
        Forall2 R l1 l2.
    Proof.
      intros A B C P Q R l1. revert l1.
      induction l1 as [|a l1 IH]; intros l2 l3 H1 H2 Himp.
      - inv H1. inv H2. constructor.
      - inversion H1 as [|a0 c0 l1' l3' Hac H1r]; subst.
        inversion H2 as [|b0 c1 l2' l3'' Hbc H2r]; subst.
        constructor; [eapply Himp; eauto|eapply IH; eauto].
    Qed.

    Lemma Forall2_flip :
      forall {A B : Type} (R : A -> B -> Prop) l1 l2,
        Forall2 R l1 l2 -> Forall2 (fun b a => R a b) l2 l1.
    Proof.
      induction 1; constructor; auto.
    Qed.

    Lemma Forall2_map_fst :
      forall {A B C : Type} (R : A -> C -> Prop) (f : B -> A) l1 l2,
        Forall2 R (List.map f l1) l2 -> Forall2 (fun b c => R (f b) c) l1 l2.
    Proof.
      induction l1 as [|b l1 IH]; intros l2 H; simpl in H.
      - inv H. constructor.
      - inversion H as [|p q ps qs Hpq Hr]; subst.
        constructor; auto.
    Qed.

    Lemma Forall2_right_In :
      forall {A B : Type} (R : A -> B -> Prop) (Q : B -> Prop) l1 l2,
        Forall2 R l1 l2 -> (forall a b, In a l1 -> R a b -> Q b) -> Forall Q l2.
    Proof.
      intros A B R Q l1 l2 H.
      induction H as [|x y l l' Hxy Hl IH]; intros Himp; [constructor|].
      constructor.
      - apply (Himp x y); [now left|exact Hxy].
      - apply IH. intros a b Ha Hab. apply (Himp a b); [now right|exact Hab].
    Qed.

    Lemma Forall2_left :
      forall {A B : Type} (R : A -> B -> Prop) (Q : A -> Prop) l1 l2,
        Forall2 R l1 l2 -> (forall a b, R a b -> Q a) -> Forall Q l1.
    Proof.
      induction 1; intros Himp; constructor; eauto.
    Qed.

    (** * The delay, assembled

        The two operand lists compose exactly as they do in the binary
        operator, and the emitted block is [lifted_defs].  The only step
        specific to the delay is that the operands' target typings have to be
        read back off the emitted equations, because the delays are the only
        place they occur. *)

    Lemma carries_Efby :
      forall P ic e0s es anns,
        Forall (carries P) e0s -> Forall (carries P) es ->
        carries_at P ic (Efby e0s es anns).
    Proof.
      intros P ic e0s es anns Hall0 Hall1
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hun as Hunfby. pose proof Hwl as Hwlfby.
      inv Hwl. inv Hwc.
      apply unnest_exp_Efby_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & st2 & xs & Hun0 & Hun1 & Hids & ? & ?);
        subst.
      apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
      apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st2 st') as Hf2
          by (eapply idents_for_anns_st_follows; eauto).
      assert (st_follows st st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).

      (** the source: the two operand lists, joined componentwise *)
      rewrite assign_lexp_Efby in Has.
      eapply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      eapply sec_bind_inv in Has as (us & sb & Hus & Hj).

      (** the target: one variable per result *)
      apply assign_lexps_evars in Has' as (Hyst & Hevars); subst yst'.

      (** the emitted equations: the definitions, then the operands' *)
      rewrite emitted_defs_map_form in Hgen.
      apply generate_leqns_constraints_app in Hgen
        as (ced & cer & xstd & Hgend & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      (** shapes and lengths *)
      assert (Forall normalized_lexp (List.concat ess0)) as Hn0
          by (eapply map_bind2_unnest_normalized_lexp; eauto).
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1
          by (eapply map_bind2_unnest_normalized_lexp; eauto).
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (eapply Forall_impl; [|exact Hn0]; intros; now constructor).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (eapply Forall_impl; [|exact Hn1]; intros; now constructor).
      assert (List.length (List.concat ess0) = List.length anns) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := e0s); eauto).
      assert (List.length (List.concat ess1) = List.length anns) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es); eauto).
      assert (List.length xs = List.length anns) as Hlxs
          by (eapply idents_for_anns_length; eauto).

      (** what the run minted is new, and so may be moved *)
      assert (NoDup (st_ids st')) as Hndst'.
      { eapply Permutation_NoDup; [|exact Hnd].
        eapply unnest_exp_vars_perm; eauto. }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx
          by (eapply idents_for_anns_vars_perm; eauto).
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (forall x, In x (List.map fst xs) -> In x (new_ids st2 st'))
        as Hxnew.
      { intros x Hx. apply new_ids_spec. split.
        - eapply idents_for_anns_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        In b (moved_by st2 st')) as Hbnew.
      { intros b Hb. unfold sec_of, moved_by in *.
        apply in_flat_map in Hb as (x & Hx & Hb).
        apply in_flat_map. exists x. split; auto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        ~ In b (scope ++ moved_by st st2)) as Hsepx.
      { intros b Hb Hin. apply Hbnew in Hb.
        apply in_app_or in Hin as [Hin|Hin].
        - eapply (Hmv b); [|exact Hin].
          apply (moved_by_suffix st st2 st' Hf02). exact Hb.
        - exact (moved_by_disjoint st st2 st' b Hin Hb). }

      (** the operands' target typings, read back off the emitted delays *)
      assert (exists ts0x usx,
                 assign_lexps GL env base_ty rst_ty (List.concat ess0) xst
                   = OK (ts0x, xst)
                 /\ assign_lexps GL env base_ty rst_ty (List.concat ess1) xst
                   = OK (usx, xst)) as (ts0x & usx & Ht0x & Hux).
      { eapply defs_operand_types_fby
          with (bs := List.map fst xs) (anns := anns); eauto.
        rewrite map_length. exact Hlxs. }
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
                = OK (ts0x, yst)) as Ht0y
          by (eapply assign_lexps_normalized_pure; eauto).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
                = OK (usx, yst)) as Huy
          by (eapply assign_lexps_normalized_pure; eauto).

      (** what the source carries, split between the two operand lists *)
      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct
          by (eapply ljoin_list_carried; eauto).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc0 & Hsc1).
      apply listSatisfiable_cmerge in Hcar as (Hcar0 & Hcar1).
      pose proof Hsts as Hstsall.
      eapply ljoin_list_scoped_plain_inv in Hsts as (Hsts0 & Hsts1); [|exact Hj].

      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st)
                (st_ids st1)) as Hp0
          by (eapply map_bind2_unnest_vars_perm with (es := e0s); eauto).
      assert (NoDup (vars_defined (List.concat eqss0 ++ List.concat eqss1)
                       ++ st_ids st)) as Hndr
          by (eapply NoDup_vd_drop; exact Hnd).

      edestruct (carries_list_intro P e0s Hall0 false ess0 eqss0 st st1 ts0
                   sst sa ce1 xstd xstm ts0x yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hndr. }
      { intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { exact Hsc0. }
      { exact Hsts0. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hts0. }
      { exact Hgen1. }
      { exact Ht0y. }
      { exact Hcar0. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      edestruct (carries_list_intro P es Hall1 false ess1 eqss1 st1 st2 us
                   sa sb ce2 xstm xst' usx yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp0|exact Hndr]. }
      { intros y Hy. apply Hmv.
        apply (moved_by_suffix st st1 st' Hf0).
        apply (moved_by_prefix st1 st2 st' Hf2). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hus. }
      { exact Hgen2. }
      { exact Huy. }
      { eapply listSatisfiable_off with (xs := moved_by st st1); eauto.
        intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the delays the pass built, and how they relate to the source *)
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts0x) as Hew0
          by (eapply assign_lexps_elementwise; eauto).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) usx) as Hew1
          by (eapply assign_lexps_elementwise; eauto).
      edestruct (unnest_fby_types (List.concat ess0) (List.concat ess1) anns
                   ts0x usx xst) as (rs & Hjr & Hallr); eauto.

      (** the first operand's bound survives the second's witness *)
      assert (forall y, In y (moved_by st1 st2) ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix st st1 st' Hf0).
          apply (moved_by_prefix st1 st2 st' Hf2). exact Hin.
        - exact (moved_by_disjoint st st1 st2 y Hy Hin). }
      assert (Forall2 (fun t t' => satisfiable dlt2 (fst t') (merge amb (fst t)))
                ts0 ts0x) as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st2); eauto.
        - intros z Hz Hin. apply (Hsep12 z Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros z Hz Hin. apply in_merge_inv in Hz as [Hz|Hz].
          + apply (Hsep12 z Hin). apply in_or_app. left. now apply amb_scoped.
          + apply (Hsep12 z Hin). apply in_or_app. left.
            eapply Forall_forall in Hsts0; [|exact Hp]. now apply Hsts0. }

      assert (Forall2 (fun src r => satisfiable dlt2 (fst r) (merge amb (fst src)))
                ts rs) as Hrelr0
          by (eapply ljoin_list_rel_plain; eauto).
      assert (Forall (fun r => st_scoped (scope ++ moved_by st st2) (fst r)) rs)
        as Hscr.
      { eapply ljoin_list_scoped_plain; [exact Hjr| |].
        - eapply Forall_impl; [|exact Hts1].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st1 st2 Hf1).
        - eapply Forall_impl; [|exact Hts2].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st2 Hf0). }

      assert (Forall2 (fun src r =>
                satisfiable dlt2 (fst r) (merge amb (fst src))
                /\ st_scoped (scope ++ moved_by st st2) (fst r)) ts rs)
        as Hrelr.
      { clear - Hrelr0 Hscr.
        revert Hscr. induction Hrelr0 as [|src r ts0 rs0 Hq Hrest IH];
          intros Hscr; [constructor|].
        inversion Hscr as [|z zs Hz Hzr]; subst.
        constructor; [split; assumption|]. apply IH; assumption. }

      (** the emitted definitions *)
      edestruct (lifted_defs (scope ++ moved_by st st2) (List.map fst xs)
                   (unnest_fby (List.concat ess0) (List.concat ess1) anns)
                   ts ced xst xstd dlt2)
        as (dlt3 & Hoff3 & Hce3 & Hscope3 & Hrel3).
      { exact Hndfst. }
      { rewrite map_length, Hlxs. symmetry.
        apply unnest_fby_length; auto. }
      { exact Hsepx. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. left.
        rewrite emitted_defs_map_form, vars_defined_defs; [exact Hy|].
        rewrite map_length, Hlxs. symmetry.
        apply unnest_fby_length; auto. }
      { intros y Hy. apply in_or_app. left. now apply amb_scoped. }
      { eapply Forall2_left; [exact Hallr|].
        intros a0 b0 (Ha1 & Ha2 & _). split; assumption. }
      { eapply Forall_impl; [|exact Hstsall].
        intros q Hq. eapply st_scoped_weaken; [|exact Hq].
        apply incl_appl, incl_refl. }
      { eapply Forall2_combine_via; [exact Hallr|exact Hrelr|].
        intros e src r (_ & _ & Hr) (Hq & Hqs).
        intros tf s s' Htf. rewrite (Hr tf s s' Htf). split; assumption. }
      { exact Hgend. }

      (** the composite witness *)
      assert (Forall2 (fun xa src => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src))) xs ts)
        as Hrel3'.
      { clear - Hrel3. revert ts Hrel3.
        induction xs as [|xa xs IH]; intros ts H; simpl in H.
        - inv H. constructor.
        - inversion H as [|p q ps qs Hpq Hr]; subst.
          constructor; auto. }
      assert (incl (sec_of (List.map fst xs)) (moved_by st st')) as Hincx.
      { intros b Hb. apply (moved_by_suffix st st2 st' Hf02). now apply Hbnew. }
      exists dlt3. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans; [eapply agree_off_trans|].
        + eapply agree_off_incl; [|exact Hoff1].
          apply (moved_by_prefix st st1 st' Hf1').
        + eapply agree_off_incl; [|exact Hoff2].
          eapply incl_tran;
            [apply (moved_by_prefix st1 st2 st' Hf2)
            |apply (moved_by_suffix st st1 st' Hf0)].
        + eapply agree_off_incl; [|exact Hoff3]. exact Hincx.
      - apply listSatisfiable_app. split; [exact Hce3|].
        apply listSatisfiable_app. split.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1)
                 (xs := sec_of (List.map fst xs)); eauto.
          * intros y Hy Hin. apply (Hsepx y Hy).
            apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
            right. apply (moved_by_prefix st st1 st2 Hf1). exact Hin.
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st2);
              eauto.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st1 st2)
                 (xs := sec_of (List.map fst xs)); eauto.
          intros y Hy Hin. apply (Hsepx y Hy).
          apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
          right. apply (moved_by_suffix st st1 st2 Hf0). exact Hin.
      - eapply Forall2_combine_via
          with (l3 := xs)
               (P0 := fun src xa => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src)))
               (Q := fun t xa => exists b, Env.find (fst xa) env = Some b
                                           /\ t = lvar b).
        + apply Forall2_flip, Hrel3'.
        + apply Forall2_flip, Hevars.
        + intros src t xa Hp (b & Hb & ?); subst.
          rewrite fst_lvar. now apply Hp.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope3].
          intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
          apply incl_app; [|eapply incl_tran; [exact Hincx|apply incl_appr,
                                                            incl_refl]].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st2 st' Hf2).
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix st st1 st' Hf1').
          * eapply Forall_impl; [|exact Hscope2].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr. eapply incl_tran;
              [apply (moved_by_prefix st1 st2 st' Hf2)
              |apply (moved_by_suffix st st1 st' Hf0)].
      - eapply Forall2_right_In; [exact Hevars|].
        intros xa t Hxa (b & Hb & ?); subst.
        rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst.
        apply in_or_app. right. apply Hincx.
        unfold sec_of. apply in_flat_map. exists (fst xa).
        split; [now apply in_map|]. rewrite Hb. now left.
    Qed.

    (** The initialised delay, which lifts exactly as the delay does.  The
        two differ only in the constructor the pass builds and in how the
        emitted list is spelled -- one maps over a [combine], the other
        combines two maps. *)

    Lemma carries_Earrow :
      forall P ic e0s es anns,
        Forall (carries P) e0s -> Forall (carries P) es ->
        carries_at P ic (Earrow e0s es anns).
    Proof.
      intros P ic e0s es anns Hall0 Hall1
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hun as Hunarrow. pose proof Hwl as Hwlarrow.
      inv Hwl. inv Hwc.
      apply unnest_exp_Earrow_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & st2 & xs & Hun0 & Hun1 & Hids & ? & ?);
        subst.
      apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
      apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st2 st') as Hf2
          by (eapply idents_for_anns_st_follows; eauto).
      assert (st_follows st st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).

      (** the source: the two operand lists, joined componentwise *)
      rewrite assign_lexp_Earrow in Has.
      eapply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      eapply sec_bind_inv in Has as (us & sb & Hus & Hj).

      (** the target: one variable per result *)
      apply assign_lexps_evars in Has' as (? & Hevars); subst.

      (** the emitted equations: the definitions, then the operands' *)
      rewrite emitted_defs_combine_form in Hgen.
      apply generate_leqns_constraints_app in Hgen
        as (ced & cer & xstd & Hgend & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      (** shapes and lengths *)
      assert (Forall normalized_lexp (List.concat ess0)) as Hn0
          by (eapply map_bind2_unnest_normalized_lexp; eauto).
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1
          by (eapply map_bind2_unnest_normalized_lexp; eauto).
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (eapply Forall_impl; [|exact Hn0]; intros; now constructor).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (eapply Forall_impl; [|exact Hn1]; intros; now constructor).
      assert (List.length (List.concat ess0) = List.length anns) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := e0s); eauto).
      assert (List.length (List.concat ess1) = List.length anns) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es); eauto).
      assert (List.length xs = List.length anns) as Hlxs
          by (eapply idents_for_anns_length; eauto).

      (** what the run minted is new, and so may be moved *)
      assert (NoDup (st_ids st')) as Hndst'.
      { eapply Permutation_NoDup; [|exact Hnd].
        eapply unnest_exp_vars_perm; eauto. }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx
          by (eapply idents_for_anns_vars_perm; eauto).
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (forall x, In x (List.map fst xs) -> In x (new_ids st2 st'))
        as Hxnew.
      { intros x Hx. apply new_ids_spec. split.
        - eapply idents_for_anns_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        In b (moved_by st2 st')) as Hbnew.
      { intros b Hb. unfold sec_of, moved_by in *.
        apply in_flat_map in Hb as (x & Hx & Hb).
        apply in_flat_map. exists x. split; auto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        ~ In b (scope ++ moved_by st st2)) as Hsepx.
      { intros b Hb Hin. apply Hbnew in Hb.
        apply in_app_or in Hin as [Hin|Hin].
        - eapply (Hmv b); [|exact Hin].
          apply (moved_by_suffix st st2 st' Hf02). exact Hb.
        - exact (moved_by_disjoint st st2 st' b Hin Hb). }

      (** the operands' target typings, read back off the emitted delays *)
      assert (exists ts0x usx,
                 assign_lexps GL env base_ty rst_ty (List.concat ess0) xst
                   = OK (ts0x, xst)
                 /\ assign_lexps GL env base_ty rst_ty (List.concat ess1) xst
                   = OK (usx, xst)) as (ts0x & usx & Ht0x & Hux).
      { eapply defs_operand_types_arrow
          with (bs := List.map fst xs) (anns := anns); eauto.
        rewrite map_length. exact Hlxs. }
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
                = OK (ts0x, yst)) as Ht0y
          by (eapply assign_lexps_normalized_pure; eauto).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
                = OK (usx, yst)) as Huy
          by (eapply assign_lexps_normalized_pure; eauto).

      (** what the source carries, split between the two operand lists *)
      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct
          by (eapply ljoin_list_carried; eauto).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc0 & Hsc1).
      apply listSatisfiable_cmerge in Hcar as (Hcar0 & Hcar1).
      pose proof Hsts as Hstsall.
      eapply ljoin_list_scoped_plain_inv in Hsts as (Hsts0 & Hsts1); [|exact Hj].

      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st)
                (st_ids st1)) as Hp0
          by (eapply map_bind2_unnest_vars_perm with (es := e0s); eauto).
      assert (NoDup (vars_defined (List.concat eqss0 ++ List.concat eqss1)
                       ++ st_ids st)) as Hndr
          by (eapply NoDup_vd_drop; exact Hnd).

      edestruct (carries_list_intro P e0s Hall0 false ess0 eqss0 st st1 ts0
                   sst sa ce1 xstd xstm ts0x yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hndr. }
      { intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { exact Hsc0. }
      { exact Hsts0. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hts0. }
      { exact Hgen1. }
      { exact Ht0y. }
      { exact Hcar0. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      edestruct (carries_list_intro P es Hall1 false ess1 eqss1 st1 st2 us
                   sa sb ce2 xstm xst' usx yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp0|exact Hndr]. }
      { intros y Hy. apply Hmv.
        apply (moved_by_suffix st st1 st' Hf0).
        apply (moved_by_prefix st1 st2 st' Hf2). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hus. }
      { exact Hgen2. }
      { exact Huy. }
      { eapply listSatisfiable_off with (xs := moved_by st st1); eauto.
        intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the delays the pass built, and how they relate to the source *)
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts0x) as Hew0
          by (eapply assign_lexps_elementwise; eauto).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) usx) as Hew1
          by (eapply assign_lexps_elementwise; eauto).
      edestruct (unnest_arrow_types (List.concat ess0) (List.concat ess1) anns
                   ts0x usx xst) as (rs & Hjr & Hallr); eauto.

      (** the first operand's bound survives the second's witness *)
      assert (forall y, In y (moved_by st1 st2) ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix st st1 st' Hf0).
          apply (moved_by_prefix st1 st2 st' Hf2). exact Hin.
        - exact (moved_by_disjoint st st1 st2 y Hy Hin). }
      assert (Forall2 (fun t t' => satisfiable dlt2 (fst t') (merge amb (fst t)))
                ts0 ts0x) as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st2); eauto.
        - intros z Hz Hin. apply (Hsep12 z Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros z Hz Hin. apply in_merge_inv in Hz as [Hz|Hz].
          + apply (Hsep12 z Hin). apply in_or_app. left. now apply amb_scoped.
          + apply (Hsep12 z Hin). apply in_or_app. left.
            eapply Forall_forall in Hsts0; [|exact Hp]. now apply Hsts0. }

      assert (Forall2 (fun src r => satisfiable dlt2 (fst r) (merge amb (fst src)))
                ts rs) as Hrelr0
          by (eapply ljoin_list_rel_plain; eauto).
      assert (Forall (fun r => st_scoped (scope ++ moved_by st st2) (fst r)) rs)
        as Hscr.
      { eapply ljoin_list_scoped_plain; [exact Hjr| |].
        - eapply Forall_impl; [|exact Hts1].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st1 st2 Hf1).
        - eapply Forall_impl; [|exact Hts2].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st2 Hf0). }

      assert (Forall2 (fun src r =>
                satisfiable dlt2 (fst r) (merge amb (fst src))
                /\ st_scoped (scope ++ moved_by st st2) (fst r)) ts rs)
        as Hrelr.
      { clear - Hrelr0 Hscr.
        revert Hscr. induction Hrelr0 as [|src r ts0 rs0 Hq Hrest IH];
          intros Hscr; [constructor|].
        inversion Hscr as [|z zs Hz Hzr]; subst.
        constructor; [split; assumption|]. apply IH; assumption. }

      (** the emitted definitions *)
      edestruct (lifted_defs (scope ++ moved_by st st2) (List.map fst xs)
                   (unnest_arrow (List.concat ess0) (List.concat ess1) anns)
                   ts ced xst xstd dlt2)
        as (dlt3 & Hoff3 & Hce3 & Hscope3 & Hrel3).
      { exact Hndfst. }
      { rewrite map_length, Hlxs. symmetry.
        apply unnest_arrow_length; auto. }
      { exact Hsepx. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. left.
        rewrite emitted_defs_combine_form, vars_defined_defs; [exact Hy|].
        rewrite map_length, Hlxs. symmetry.
        apply unnest_arrow_length; auto. }
      { intros y Hy. apply in_or_app. left. now apply amb_scoped. }
      { eapply Forall2_left; [exact Hallr|].
        intros a0 b0 (Ha1 & Ha2 & _). split; assumption. }
      { eapply Forall_impl; [|exact Hstsall].
        intros q Hq. eapply st_scoped_weaken; [|exact Hq].
        apply incl_appl, incl_refl. }
      { eapply Forall2_combine_via; [exact Hallr|exact Hrelr|].
        intros e src r (_ & _ & Hr) (Hq & Hqs).
        intros tf s s' Htf. rewrite (Hr tf s s' Htf). split; assumption. }
      { exact Hgend. }

      (** the composite witness *)
      assert (Forall2 (fun xa src => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src))) xs ts)
        as Hrel3'.
      { clear - Hrel3. revert ts Hrel3.
        induction xs as [|xa xs IH]; intros ts H; simpl in H.
        - inv H. constructor.
        - inversion H as [|p q ps qs Hpq Hr]; subst.
          constructor; auto. }
      assert (incl (sec_of (List.map fst xs)) (moved_by st st')) as Hincx.
      { intros b Hb. apply (moved_by_suffix st st2 st' Hf02). now apply Hbnew. }
      exists dlt3. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans; [eapply agree_off_trans|].
        + eapply agree_off_incl; [|exact Hoff1].
          apply (moved_by_prefix st st1 st' Hf1').
        + eapply agree_off_incl; [|exact Hoff2].
          eapply incl_tran;
            [apply (moved_by_prefix st1 st2 st' Hf2)
            |apply (moved_by_suffix st st1 st' Hf0)].
        + eapply agree_off_incl; [|exact Hoff3]. exact Hincx.
      - apply listSatisfiable_app. split; [exact Hce3|].
        apply listSatisfiable_app. split.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1)
                 (xs := sec_of (List.map fst xs)); eauto.
          * intros y Hy Hin. apply (Hsepx y Hy).
            apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
            right. apply (moved_by_prefix st st1 st2 Hf1). exact Hin.
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st2);
              eauto.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st1 st2)
                 (xs := sec_of (List.map fst xs)); eauto.
          intros y Hy Hin. apply (Hsepx y Hy).
          apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
          right. apply (moved_by_suffix st st1 st2 Hf0). exact Hin.
      - eapply Forall2_combine_via
          with (l3 := xs)
               (P0 := fun src xa => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src)))
               (Q := fun t xa => exists b, Env.find (fst xa) env = Some b
                                           /\ t = lvar b).
        + apply Forall2_flip, Hrel3'.
        + apply Forall2_flip, Hevars.
        + intros src t xa Hp (b & Hb & ?); subst.
          rewrite fst_lvar. now apply Hp.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope3].
          intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
          apply incl_app; [|eapply incl_tran; [exact Hincx|apply incl_appr,
                                                            incl_refl]].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st2 st' Hf2).
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix st st1 st' Hf1').
          * eapply Forall_impl; [|exact Hscope2].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr. eapply incl_tran;
              [apply (moved_by_prefix st1 st2 st' Hf2)
              |apply (moved_by_suffix st st1 st' Hf0)].
      - eapply Forall2_right_In; [exact Hevars|].
        intros xa t Hxa (b & Hb & ?); subst.
        rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst.
        apply in_or_app. right. apply Hincx.
        unfold sec_of. apply in_flat_map. exists (fst xa).
        split; [now apply in_map|]. rewrite Hb. now left.
    Qed.

    (** * The merge and the conditional, when they do lift

        Same shape as the delay: one variable per result, one emitted
        equation per result, and the operands occurring only inside those
        equations.  The difference is the head -- a sampling variable's level
        for the merge, the scrutinee's whole type for the conditional -- so
        the join lemmas are used at that head rather than at [lbot]. *)

    Lemma unnest_merge_tys_nil :
      forall ckid es1 es2 cl, unnest_merge ckid es1 es2 [] cl = [].
    Proof.
      intros. unfold unnest_merge. destruct (combine es1 es2); reflexivity.
    Qed.

    Lemma assign_lexp_merge_type :
      forall ckid e1 e2 ty cl g t0 t1 tf s s',
        Env.find ckid env = Some g ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e1 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e2 s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty
          (Emerge ckid [e1] [e2] ([ty], cl)) s = OK ([tf], s') ->
        tf = ljoin (ljoin (lvar g) t0) t1.
    Proof.
      intros ckid e1 e2 ty cl g t0 t1 tf s s' Hg H0 H1 H.
      rewrite assign_lexp_Emerge in H.
      eapply sec_bind_inv in H as (g' & sa & Hg' & H).
      eapply sec_bind_inv in H as (t & sb & Ht & H).
      eapply sec_bind_inv in H as (u & sc & Hu & Hj).
      apply find_env_inv in Hg' as (Hg' & ?); subst.
      rewrite Hg in Hg'. inv Hg'.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sd & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma assign_lexp_merge_pure :
      forall ckid e1 e2 ty cl g t0 t1,
        Env.find ckid env = Some g ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e1 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e2 s = OK ([t1], s)) ->
        snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty
            (Emerge ckid [e1] [e2] ([ty], cl)) s = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros ckid e1 e2 ty cl g t0 t1 Hg H0 H1 Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Emerge in H.
      eapply sec_bind_inv in H as (g' & sa & Hg' & H).
      eapply sec_bind_inv in H as (t & sb & Ht & H).
      eapply sec_bind_inv in H as (u & sc & Hu & Hj).
      apply find_env_inv in Hg' as (Hg' & ?); subst.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sd & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin, lvar. simpl snd.
      rewrite Hc0, Hc1. reflexivity.
    Qed.

    Lemma unnest_merge_types :
      forall ckid cl g (es1 es2 : list exp) (tys : list type) ts1 ts2 s,
        Env.find ckid env = Some g ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es1 ts1 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es2 ts2 ->
        List.length es1 = List.length tys ->
        List.length es2 = List.length tys ->
        exists rs,
          ljoin_list (List.map (fun t => ljoin (lvar g) t) ts1) ts2 s
            = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_merge ckid es1 es2 tys cl) rs.
    Proof.
      intros ckid cl g es1. revert ckid cl g.
      induction es1 as [|e1 es1 IH];
        intros ckid cl g es2 tys ts1 ts2 s Hg H1 H2 Hl1 Hl2.
      - inv H1. destruct tys; simpl in Hl1; [|discriminate].
        destruct es2; simpl in Hl2; [|discriminate]. inv H2.
        exists []. split; [reflexivity|rewrite unnest_merge_nil; constructor].
      - destruct tys as [|ty tys]; simpl in Hl1; [discriminate|].
        destruct es2 as [|e2 es2]; simpl in Hl2; [discriminate|].
        inversion H1 as [|p q ps qs Hp H1r]; subst.
        inversion H2 as [|p2 q2 ps2 qs2 Hp2 H2r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct (IH ckid cl g es2 tys qs qs2 s) as (rs & Hj & Hall); eauto.
        exists (ljoin (ljoin (lvar g) q) q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_merge_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_merge_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_merge_type; eauto.
    Qed.

    Lemma defs_operand_types_merge :
      forall (bs : list ident) ckid cl (es1 es2 : list exp)
             (tys : list type) ce xst xst',
        Forall normalized_cexp es1 ->
        Forall normalized_cexp es2 ->
        List.length bs = List.length tys ->
        List.length es1 = List.length tys ->
        List.length es2 = List.length tys ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_merge ckid es1 es2 tys cl))) xst
          = OK (ce, xst') ->
        exists ts1 ts2,
          assign_lexps GL env base_ty rst_ty es1 xst = OK (ts1, xst)
          /\ assign_lexps GL env base_ty rst_ty es2 xst = OK (ts2, xst).
    Proof.
      induction bs as [|b bs IH];
        intros ckid cl es1 es2 tys ce xst xst' Hn1 Hn2 Hlb Hl1 Hl2 Hgen.
      - destruct tys; simpl in Hlb; [|discriminate].
        destruct es1; simpl in Hl1; [|discriminate].
        destruct es2; simpl in Hl2; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct tys as [|ty tys]; simpl in Hlb; [discriminate|].
        destruct es1 as [|e1 es1]; simpl in Hl1; [discriminate|].
        destruct es2 as [|e2 es2]; simpl in Hl2; [discriminate|].
        inv Hn1. inv Hn2.
        rewrite unnest_merge_cons in Hgen.
        replace (List.map (fun '(x0, e) => ([x0], [e]))
                   (combine (b :: bs)
                      (Emerge ckid [e1] [e2] ([ty], cl)
                       :: unnest_merge ckid es1 es2 tys cl)))
          with (([b], [Emerge ckid [e1] [e2] ([ty], cl)])
                :: List.map (fun '(x0, e) => ([x0], [e]))
                     (combine bs (unnest_merge ckid es1 es2 tys cl)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Emerge in Htf.
        eapply sec_bind_inv in Htf as (g & sa & Hg & Htf).
        eapply sec_bind_inv in Htf as (t & sb & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sc & Hu & Hj).
        apply find_env_inv in Hg as (Hg & ?); subst.
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sb = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e1 s
                              = OK (t, s)) as (? & _ & _ & Hs0)
          by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
        subst sb.
        assert (sc = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e2 s
                              = OK (u, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
        subst sc.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH ckid cl es1 es2 tys cs xst xst')
          as (ts1 & ts2 & Hts1 & Hts2); eauto.
        exists (t ++ ts1), (u ++ ts2). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs0|].
          eapply sec_bind_ok; [exact Hts1|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hts2|]. reflexivity.
    Qed.

    (** The merge, when it does lift.  Same skeleton as the delay, with the
        sampling variable's level as the head of both joins.  Its visibility
        is read off the source types as in the control branch, and the case
        where there are no streams at all -- which [wc_Emerge], unlike
        [wc_Eifte], does not rule out -- is handled by the same disjunction. *)

    Lemma carries_Emerge_lift :
      forall P ckid es1 es2 tys cl,
        Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P false (Emerge ckid es1 es2 (tys, cl)).
    Proof.
      intros P ckid es1 es2 tys cl Hall0 Hall1
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hun as Hunm. pose proof Hwl as Hwlm.
      inv Hwl. apply wc_Emerge_inv in Hwc as (Hwc1 & Hwc2).
      apply unnest_exp_Emerge_inv in Hun
        as (ess0 & eqss0 & st1 & ess1 & eqss1 & st2 & xs
            & Hmap0 & Hmap1 & Hids & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st2 st') as Hf2
          by (eapply idents_for_anns_st_follows; eauto).
      assert (st_follows st st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).

      (** the source *)
      rewrite assign_lexp_Emerge in Has.
      eapply sec_bind_inv in Has as (g & s0 & Hg & Has).
      eapply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      eapply sec_bind_inv in Has as (us & sb & Hus & Hj).
      apply find_env_inv in Hg as (Hgf & ?); subst.

      (** the target *)
      apply assign_lexps_evars in Has' as (? & Hevars); subst.

      rewrite emitted_defs_combine_form in Hgen.
      apply generate_leqns_constraints_app in Hgen
        as (ced & cer & xstd & Hgend & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat ess0) = List.length tys) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat ess1) = List.length tys) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      assert (List.length xs = List.length tys) as Hlxs.
      { rewrite (idents_for_anns_length _ _ _ _ Hids). apply map_length. }

      assert (NoDup (st_ids st')) as Hndst'.
      { eapply Permutation_NoDup; [|exact Hnd].
        eapply unnest_exp_vars_perm; eauto. }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx
          by (eapply idents_for_anns_vars_perm; eauto).
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        In b (moved_by st2 st')) as Hbnew.
      { intros b Hb. unfold sec_of, moved_by in *.
        apply in_flat_map in Hb as (x & Hx & Hb).
        apply in_flat_map. exists x. split; auto.
        apply new_ids_spec. split.
        - eapply idents_for_anns_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        ~ In b (scope ++ moved_by st st2)) as Hsepx.
      { intros b Hb Hin. apply Hbnew in Hb.
        apply in_app_or in Hin as [Hin|Hin].
        - eapply (Hmv b); [|exact Hin].
          apply (moved_by_suffix st st2 st' Hf02). exact Hb.
        - exact (moved_by_disjoint st st2 st' b Hin Hb). }

      (** the branches' target typings, off the emitted merges *)
      assert (exists ts1x ts2x,
                 assign_lexps GL env base_ty rst_ty (List.concat ess0) xst
                   = OK (ts1x, xst)
                 /\ assign_lexps GL env base_ty rst_ty (List.concat ess1) xst
                   = OK (ts2x, xst)) as (ts1x & ts2x & Ht1x & Ht2x).
      { eapply defs_operand_types_merge
          with (bs := List.map fst xs) (tys := tys); eauto.
        rewrite map_length. exact Hlxs. }
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
                = OK (ts1x, yst)) as Ht1y
          by (eapply assign_lexps_normalized_pure; eauto).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
                = OK (ts2x, yst)) as Ht2y
          by (eapply assign_lexps_normalized_pure; eauto).

      (** what the source carries *)
      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct.
      { erewrite ljoin_list_carried by exact Hj.
        now rewrite carried_map_merge_l. }
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc0 & Hsc1).
      apply listSatisfiable_cmerge in Hcar as (Hcar0 & Hcar1).
      pose proof Hsts as Hstsall.
      eapply ljoin_list_scoped_inv in Hsts as (Hsts0 & Hsts1 & Hgs);
        [|exact Hj].

      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st)
                (st_ids st1)) as Hp0
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      assert (NoDup (vars_defined (List.concat eqss0 ++ List.concat eqss1)
                       ++ st_ids st)) as Hndr
          by (eapply NoDup_vd_drop; exact Hnd).

      edestruct (carries_list_intro P es1 Hall0 true ess0 eqss0 st st1 ts0
                   sst sa ce1 xstd xstm ts1x yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hndr. }
      { intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { exact Hsc0. }
      { exact Hsts0. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hts0. }
      { exact Hgen1. }
      { exact Ht1y. }
      { exact Hcar0. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      edestruct (carries_list_intro P es2 Hall1 true ess1 eqss1 st1 st2 us
                   sa sb ce2 xstm xst' ts2x yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp0|exact Hndr]. }
      { intros y Hy. apply Hmv.
        apply (moved_by_suffix st st1 st' Hf0).
        apply (moved_by_prefix st1 st2 st' Hf2). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hus. }
      { exact Hgen2. }
      { exact Ht2y. }
      { eapply listSatisfiable_off with (xs := moved_by st st1); eauto.
        intros y Hy. apply Hmv.
        apply (moved_by_prefix st st1 st' Hf1'). exact Hy. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the merges the pass built *)
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts1x) as Hew0
          by (eapply assign_lexps_elementwise; eauto).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) ts2x) as Hew1
          by (eapply assign_lexps_elementwise; eauto).
      edestruct (unnest_merge_types ckid cl g (List.concat ess0)
                   (List.concat ess1) tys ts1x ts2x xst)
        as (rs & Hjr & Hallr); eauto.

      assert (forall y, In y (moved_by st1 st2) ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix st st1 st' Hf0).
          apply (moved_by_prefix st1 st2 st' Hf2). exact Hin.
        - exact (moved_by_disjoint st st1 st2 y Hy Hin). }
      assert (Forall2 (fun t t' => satisfiable dlt2 (fst t') (merge amb (fst t)))
                ts0 ts1x) as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st2); eauto.
        - intros z Hz Hin. apply (Hsep12 z Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros z Hz Hin. apply in_merge_inv in Hz as [Hz|Hz].
          + apply (Hsep12 z Hin). apply in_or_app. left. now apply amb_scoped.
          + apply (Hsep12 z Hin). apply in_or_app. left.
            eapply Forall_forall in Hsts0; [|exact Hp]. now apply Hsts0. }

      assert (Forall2 (fun src r => satisfiable dlt2 (fst r) (merge amb (fst src)))
                ts rs) as Hrelr0
          by (eapply ljoin_list_rel; eauto).

      (** where the merges' names live *)
      assert (Forall (fun r => st_scoped (scope ++ moved_by st st2) (fst r)) rs)
        as Hscr.
      { destruct Hgs as [Hnil|Hg2].
        - assert (tys = []) as ?.
          { assert (List.length ts0 = List.length tys) as Hlt
                by (erewrite assign_lexps_length with (es := es1); eauto).
            rewrite Hnil in Hlt. simpl in Hlt.
            destruct tys; simpl in Hlt; congruence. }
          subst tys. rewrite unnest_merge_tys_nil in Hallr.
          inv Hallr. constructor.
        - eapply ljoin_list_scoped; [|exact Hjr| |].
          + apply in_or_app. now left.
          + eapply Forall_impl; [|exact Hts1].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix st st1 st2 Hf1).
          + eapply Forall_impl; [|exact Hts2].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_suffix st st1 st2 Hf0). }

      assert (Forall2 (fun src r =>
                satisfiable dlt2 (fst r) (merge amb (fst src))
                /\ st_scoped (scope ++ moved_by st st2) (fst r)) ts rs)
        as Hrelr.
      { clear - Hrelr0 Hscr.
        revert Hscr. induction Hrelr0 as [|src r ts0 rs0 Hq Hrest IH];
          intros Hscr; [constructor|].
        inversion Hscr as [|z zs Hz Hzr]; subst.
        constructor; [split; assumption|]. apply IH; assumption. }

      (** the emitted definitions *)
      edestruct (lifted_defs (scope ++ moved_by st st2) (List.map fst xs)
                   (unnest_merge ckid (List.concat ess0) (List.concat ess1)
                      tys cl)
                   ts ced xst xstd dlt2)
        as (dlt3 & Hoff3 & Hce3 & Hscope3 & Hrel3).
      { exact Hndfst. }
      { rewrite map_length, Hlxs. symmetry.
        apply unnest_merge_length; auto. }
      { exact Hsepx. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. left.
        rewrite emitted_defs_combine_form, vars_defined_defs; [exact Hy|].
        rewrite map_length, Hlxs. symmetry.
        apply unnest_merge_length; auto. }
      { intros y Hy. apply in_or_app. left. now apply amb_scoped. }
      { eapply Forall2_left; [exact Hallr|].
        intros a0 b0 (Ha1 & Ha2 & _). split; assumption. }
      { eapply Forall_impl; [|exact Hstsall].
        intros q Hq. eapply st_scoped_weaken; [|exact Hq].
        apply incl_appl, incl_refl. }
      { eapply Forall2_combine_via; [exact Hallr|exact Hrelr|].
        intros e src r (_ & _ & Hr) (Hq & Hqs).
        intros tf s s' Htf. rewrite (Hr tf s s' Htf). split; assumption. }
      { exact Hgend. }

      (** the composite witness *)
      assert (Forall2 (fun xa src => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src))) xs ts)
        as Hrel3'.
      { clear - Hrel3. revert ts Hrel3.
        induction xs as [|xa xs IH]; intros ts H; simpl in H.
        - inv H. constructor.
        - inversion H as [|p q ps qs Hpq Hr]; subst.
          constructor; auto. }
      assert (incl (sec_of (List.map fst xs)) (moved_by st st')) as Hincx.
      { intros b Hb. apply (moved_by_suffix st st2 st' Hf02). now apply Hbnew. }
      exists dlt3. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans; [eapply agree_off_trans|].
        + eapply agree_off_incl; [|exact Hoff1].
          apply (moved_by_prefix st st1 st' Hf1').
        + eapply agree_off_incl; [|exact Hoff2].
          eapply incl_tran;
            [apply (moved_by_prefix st1 st2 st' Hf2)
            |apply (moved_by_suffix st st1 st' Hf0)].
        + eapply agree_off_incl; [|exact Hoff3]. exact Hincx.
      - apply listSatisfiable_app. split; [exact Hce3|].
        apply listSatisfiable_app. split.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1)
                 (xs := sec_of (List.map fst xs)); eauto.
          * intros y Hy Hin. apply (Hsepx y Hy).
            apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
            right. apply (moved_by_prefix st st1 st2 Hf1). exact Hin.
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st2);
              eauto.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st1 st2)
                 (xs := sec_of (List.map fst xs)); eauto.
          intros y Hy Hin. apply (Hsepx y Hy).
          apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
          right. apply (moved_by_suffix st st1 st2 Hf0). exact Hin.
      - eapply Forall2_combine_via
          with (l3 := xs)
               (P0 := fun src xa => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src)))
               (Q := fun t xa => exists b, Env.find (fst xa) env = Some b
                                           /\ t = lvar b).
        + apply Forall2_flip, Hrel3'.
        + apply Forall2_flip, Hevars.
        + intros src t xa Hp (b & Hb & ?); subst.
          rewrite fst_lvar. now apply Hp.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope3].
          intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
          apply incl_app; [|eapply incl_tran; [exact Hincx|apply incl_appr,
                                                            incl_refl]].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st2 st' Hf2).
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix st st1 st' Hf1').
          * eapply Forall_impl; [|exact Hscope2].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr. eapply incl_tran;
              [apply (moved_by_prefix st1 st2 st' Hf2)
              |apply (moved_by_suffix st st1 st' Hf0)].
      - eapply Forall2_right_In; [exact Hevars|].
        intros xa t Hxa (b & Hb & ?); subst.
        rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst.
        apply in_or_app. right. apply Hincx.
        unfold sec_of. apply in_flat_map. exists (fst xa).
        split; [now apply in_map|]. rewrite Hb. now left.
    Qed.

    Lemma unnest_ite_tys_nil :
      forall e0 es1 es2 ck, unnest_ite e0 es1 es2 [] ck = [].
    Proof.
      intros. unfold unnest_ite. destruct (combine es1 es2); reflexivity.
    Qed.

    Lemma assign_lexp_ite_type :
      forall e0 e1 e2 ty ck th t0 t1 tf s s',
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([th], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e1 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e2 s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty
          (Eite e0 [e1] [e2] ([ty], ck)) s = OK ([tf], s') ->
        tf = ljoin (ljoin th t0) t1.
    Proof.
      intros e0 e1 e2 ty ck th t0 t1 tf s s' Hh H0 H1 H.
      rewrite assign_lexp_Eite in H.
      eapply sec_bind_inv in H as (t0' & sa & Ht0' & H).
      eapply sec_bind_inv in H as (th' & sb & Hth' & H).
      eapply sec_bind_inv in H as (t & sc & Ht & H).
      eapply sec_bind_inv in H as (u & sd & Hu & Hj).
      rewrite Hh in Ht0'. inv Ht0'.
      apply single_inv in Hth' as (Heq & ?); subst.
      inv Heq.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & se & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma assign_lexp_ite_pure :
      forall e0 e1 e2 ty ck th t0 t1,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([th], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e1 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e2 s = OK ([t1], s)) ->
        snd th = [] -> snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty
            (Eite e0 [e1] [e2] ([ty], ck)) s = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros e0 e1 e2 ty ck th t0 t1 Hh H0 H1 Hch Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Eite in H.
      eapply sec_bind_inv in H as (t0' & sa & Ht0' & H).
      eapply sec_bind_inv in H as (th' & sb & Hth' & H).
      eapply sec_bind_inv in H as (t & sc & Ht & H).
      eapply sec_bind_inv in H as (u & sd & Hu & Hj).
      rewrite Hh in Ht0'. inv Ht0'.
      apply single_inv in Hth' as (Heq & ?); subst. inv Heq.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & se & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin. simpl snd.
      rewrite Hch, Hc0, Hc1. reflexivity.
    Qed.

    Lemma unnest_ite_types :
      forall e0 ck th (es1 es2 : list exp) (tys : list type) ts1 ts2 s,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([th], s)) ->
        snd th = [] ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es1 ts1 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es2 ts2 ->
        List.length es1 = List.length tys ->
        List.length es2 = List.length tys ->
        exists rs,
          ljoin_list (List.map (fun t => ljoin th t) ts1) ts2 s = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_ite e0 es1 es2 tys ck) rs.
    Proof.
      intros e0 ck th es1. revert e0 ck th.
      induction es1 as [|e1 es1 IH];
        intros e0 ck th es2 tys ts1 ts2 s Hh Hch H1 H2 Hl1 Hl2.
      - inv H1. destruct tys; simpl in Hl1; [|discriminate].
        destruct es2; simpl in Hl2; [|discriminate]. inv H2.
        exists []. split; [reflexivity|rewrite unnest_ite_nil; constructor].
      - destruct tys as [|ty tys]; simpl in Hl1; [discriminate|].
        destruct es2 as [|e2 es2]; simpl in Hl2; [discriminate|].
        inversion H1 as [|p q ps qs Hp H1r]; subst.
        inversion H2 as [|p2 q2 ps2 qs2 Hp2 H2r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct (IH e0 ck th es2 tys qs qs2 s) as (rs & Hj & Hall); eauto.
        exists (ljoin (ljoin th q) q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_ite_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_ite_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_ite_type; eauto.
    Qed.

    Lemma defs_operand_types_ite :
      forall (bs : list ident) e0 ck (es1 es2 : list exp)
             (tys : list type) ce xst xst',
        normalized_lexp e0 ->
        Forall normalized_cexp es1 ->
        Forall normalized_cexp es2 ->
        List.length bs = List.length tys ->
        List.length es1 = List.length tys ->
        List.length es2 = List.length tys ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_ite e0 es1 es2 tys ck))) xst
          = OK (ce, xst') ->
        exists ts1 ts2,
          assign_lexps GL env base_ty rst_ty es1 xst = OK (ts1, xst)
          /\ assign_lexps GL env base_ty rst_ty es2 xst = OK (ts2, xst)
          /\ (bs = [] \/ exists th,
                 forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                            = OK ([th], s)).
    Proof.
      induction bs as [|b bs IH];
        intros e0 ck es1 es2 tys ce xst xst' Hn0 Hn1 Hn2 Hlb Hl1 Hl2 Hgen.
      - destruct tys; simpl in Hlb; [|discriminate].
        destruct es1; simpl in Hl1; [|discriminate].
        destruct es2; simpl in Hl2; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct tys as [|ty tys]; simpl in Hlb; [discriminate|].
        destruct es1 as [|e1 es1]; simpl in Hl1; [discriminate|].
        destruct es2 as [|e2 es2]; simpl in Hl2; [discriminate|].
        inv Hn1. inv Hn2.
        rewrite unnest_ite_cons in Hgen.
        replace (List.map (fun '(x0, e) => ([x0], [e]))
                   (combine (b :: bs)
                      (Eite e0 [e1] [e2] ([ty], ck)
                       :: unnest_ite e0 es1 es2 tys ck)))
          with (([b], [Eite e0 [e1] [e2] ([ty], ck)])
                :: List.map (fun '(x0, e) => ([x0], [e]))
                     (combine bs (unnest_ite e0 es1 es2 tys ck)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck' & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Eite in Htf.
        eapply sec_bind_inv in Htf as (t0' & sa & Ht0' & Htf).
        eapply sec_bind_inv in Htf as (th & sb & Hth & Htf).
        eapply sec_bind_inv in Htf as (t & sc & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sd & Hu & Hj).
        assert (sa = xst /\ List.length t0' = 1 /\ carried t0' = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                              = OK (t0', s)) as (? & Hl0' & _ & Hs0')
          by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
        subst sa.
        apply single_inv in Hth as (? & ?); subst.
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sc = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e1 s
                              = OK (t, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
        subst sc.
        assert (sd = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e2 s
                              = OK (u, s)) as (? & _ & _ & Hs2)
          by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
        subst sd.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH e0 ck es1 es2 tys cs xst xst')
          as (ts1 & ts2 & Hts1 & Hts2 & _); eauto.
        exists (t ++ ts1), (u ++ ts2). split; [|split].
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hts1|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs2|].
          eapply sec_bind_ok; [exact Hts2|]. reflexivity.
        + right. exists th. exact Hs0'.
    Qed.

    (** The conditional, when it does lift.  The merge's proof with the
        scrutinee composed in front, and the scrutinee's own type as the head
        of both joins rather than a variable's level.  [wc_Eifte] guarantees a
        stream, so the scrutinee really does come back from the emitted
        conditionals. *)

    Lemma carries_Eite_lift :
      forall P e0 es1 es2 tys ck,
        carries P e0 -> Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P false (Eite e0 es1 es2 (tys, ck)).
    Proof.
      intros P e0 es1 es2 tys ck IHe Hall0 Hall1
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hun as Hunm. pose proof Hwl as Hwlm.
      inv Hwl. apply wc_Eifte_inv in Hwc as (Hwc0 & Hwc1 & Hwc2 & Htys).
      apply unnest_exp_Eite_inv in Hun
        as (f0 & eqs0 & st0 & ess0 & eqss0 & st1 & ess1 & eqss1 & st2 & xs
            & Hun0 & Hmap0 & Hmap1 & Hids & ? & ?); subst.
      assert (st_follows st st0) as Hfa
          by (eapply unnest_exp_st_follows; eauto).
      assert (st_follows st0 st1) as Hfb
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hfc
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st2 st') as Hfd
          by (eapply idents_for_anns_st_follows; eauto).
      assert (st_follows st0 st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st0 st') as Hf0' by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).
      assert (st_follows st st1) as Hfab by (etransitivity; eauto).
      assert (st_follows st st2) as Hfac by (etransitivity; eauto).

      (** the source *)
      rewrite assign_lexp_Eite in Has.
      eapply sec_bind_inv in Has as (t0 & s0 & Ht0 & Has).
      eapply sec_bind_inv in Has as (th & s1 & Hth & Has).
      eapply sec_bind_inv in Has as (ts1 & sa & Hsrc1 & Has).
      eapply sec_bind_inv in Has as (ts2 & sb & Hsrc2 & Hj).
      apply single_inv in Hth as (? & ?); subst.

      (** the target *)
      apply assign_lexps_evars in Has' as (? & Hevars); subst.

      rewrite emitted_defs_combine_form in Hgen.
      apply generate_leqns_constraints_app in Hgen
        as (ced & cer & xstd & Hgend & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce0 & cer2 & xste & Hgen0 & Hgenr2 & ?); subst.
      apply generate_leqns_constraints_app in Hgenr2
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      (** shapes and lengths *)
      assert (Forall normalized_lexp f0) as Hn0
          by (eapply unnest_exp_normalized_lexp; eauto).
      assert (f0 = [hd_default f0]) as Hone0
          by (eapply unnest_exp_one; eauto).
      assert (normalized_lexp (hd_default f0)) as Hn0'
          by (rewrite Hone0 in Hn0; now inv Hn0).
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat ess0) = List.length tys) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat ess1) = List.length tys) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      assert (List.length xs = List.length tys) as Hlxs.
      { rewrite (idents_for_anns_length _ _ _ _ Hids). apply map_length. }

      assert (NoDup (st_ids st')) as Hndst'.
      { eapply Permutation_NoDup; [|exact Hnd].
        eapply unnest_exp_vars_perm; [exact Hwlm|exact Hunm]. }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx
          by (eapply idents_for_anns_vars_perm; eauto).
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        In b (moved_by st2 st')) as Hbnew.
      { intros b Hb. unfold sec_of, moved_by in *.
        apply in_flat_map in Hb as (x & Hx & Hb).
        apply in_flat_map. exists x. split; auto.
        apply new_ids_spec. split.
        - eapply idents_for_anns_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (forall b, In b (sec_of (List.map fst xs)) ->
                        ~ In b (scope ++ moved_by st st2)) as Hsepx.
      { intros b Hb Hin. apply Hbnew in Hb.
        apply in_app_or in Hin as [Hin|Hin].
        - eapply (Hmv b); [|exact Hin].
          apply (moved_by_suffix st st2 st' Hfac). exact Hb.
        - exact (moved_by_disjoint st st2 st' b Hin Hb). }

      (** the scrutinee and the branches, off the emitted conditionals *)
      assert (exists ts1x ts2x,
                 assign_lexps GL env base_ty rst_ty (List.concat ess0) xst
                   = OK (ts1x, xst)
                 /\ assign_lexps GL env base_ty rst_ty (List.concat ess1) xst
                   = OK (ts2x, xst)
                 /\ (List.map fst xs = [] \/ exists thx,
                        forall s, assign_lexp_type GL env base_ty rst_ty
                                    (hd_default f0) s = OK ([thx], s)))
        as (ts1x & ts2x & Ht1x & Ht2x & Hscr).
      { eapply defs_operand_types_ite
          with (bs := List.map fst xs) (tys := tys); eauto.
        rewrite map_length. exact Hlxs. }
      assert (List.map fst xs <> []) as Hxsne.
      { intro Hx. assert (List.length (List.map fst xs) = 0) as Hz
            by (rewrite Hx; reflexivity).
        rewrite map_length, Hlxs in Hz. lia. }
      destruct Hscr as [Hx|(thx & Hthx)]; [contradiction|].
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
                = OK (ts1x, yst)) as Ht1y
          by (eapply assign_lexps_normalized_pure; eauto).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
                = OK (ts2x, yst)) as Ht2y
          by (eapply assign_lexps_normalized_pure; eauto).
      assert (snd thx = []) as Hcthx.
      { specialize (assign_lexp_normalized_lexp_pure GL env base_ty rst_ty
                      _ Hn0' [thx] xst xst (Hthx xst)) as (_ & _ & Hc & _).
        now rewrite carried_single in Hc. }

      (** what the source carries, split three ways *)
      assert (carried ts
              = cmerge (carried (List.map (fun t => ljoin th t) ts1))
                  (carried ts2)) as Hct
          by (eapply ljoin_list_carried; eauto).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (HscM & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (HcarM & Hcar2).
      assert (constraints_scoped scope (carried ts1)) as Hsc1
          by (eapply constraints_scoped_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (carried ts1)) as Hcar1
          by (eapply listSatisfiable_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HcarM]).
      assert (List.length ts1 = List.length tys) as Hlts1
          by (erewrite assign_lexps_length with (es := es1); eauto).
      destruct ts1 as [|tf1 ts1r];
        [simpl in Hlts1; destruct tys; simpl in Htys; [lia|discriminate]|].
      assert (constraints_scoped scope (snd th)) as Hsc0
          by (eapply constraints_scoped_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (snd th)) as Hcar0
          by (eapply listSatisfiable_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HcarM]).
      pose proof Hsts as Hstsall.
      eapply ljoin_list_scoped_head_inv in Hsts as (Hsts1 & Hsts2 & Hgs);
        [|exact Hj].
      assert (st_scoped scope (fst th)) as Hst0
          by (destruct Hgs as [Hx|Hx]; [discriminate|exact Hx]).

      assert (Permutation (vars_defined eqs0 ++ st_ids st) (st_ids st0)) as Hpa
          by (eapply unnest_exp_vars_perm with (e := e0); eauto).
      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st0)
                (st_ids st1)) as Hpb
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      assert (NoDup (vars_defined
                (eqs0 ++ List.concat eqss0 ++ List.concat eqss1)
                ++ st_ids st)) as Hndr
          by (eapply NoDup_vd_drop; exact Hnd).
      assert (NoDup (vars_defined (List.concat eqss0 ++ List.concat eqss1)
                       ++ st_ids st0)) as Hndr0
          by (eapply NoDup_vd_app_r; [exact Hpa|exact Hndr]).

      (** the scrutinee *)
      edestruct (IHe false f0 eqs0 st st0 [th] sst s0 ce0 xstd xste
                   [thx] yst yst dlt)
        as (dlt0 & Hoff0 & Hce0 & Hrel0 & Hscope0 & Hts0).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hndr. }
      { intros y Hy. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hy. }
      { simpl. now rewrite cmerge_nil. }
      { constructor; [exact Hst0|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hun0. }
      { exact Ht0. }
      { exact Hgen0. }
      { rewrite Hone0 at 1. apply assign_lexps_single_intro, Hthx. }
      { simpl. now rewrite cmerge_nil. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the true branch *)
      edestruct (carries_list_intro P es1 Hall0 true ess0 eqss0 st0 st1
                   (tf1 :: ts1r) s0 sa ce1 xste xstm ts1x yst yst dlt0)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hndr0. }
      { intros y Hy. apply Hmv.
        apply (moved_by_suffix st st0 st' Hfa).
        apply (moved_by_prefix st0 st1 st' Hf1'). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hsrc1. }
      { exact Hgen1. }
      { exact Ht1y. }
      { eapply listSatisfiable_off with (xs := moved_by st st0); eauto.
        intros y Hy. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hy. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }
      (** the false branch *)
      edestruct (carries_list_intro P es2 Hall1 true ess1 eqss1 st1 st2 ts2
                   sa sb ce2 xstm xst' ts2x yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hpb|exact Hndr0]. }
      { intros y Hy. apply Hmv.
        apply (moved_by_suffix st st1 st' Hfab).
        apply (moved_by_prefix st1 st2 st' Hfd). exact Hy. }
      { exact Hsc2. }
      { exact Hsts2. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. right.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hsrc2. }
      { exact Hgen2. }
      { exact Ht2y. }
      { eapply listSatisfiable_off with (xs := moved_by st0 st1).
        - exact Hsc2.
        - intros y Hy. apply Hmv.
          apply (moved_by_suffix st st0 st' Hfa).
          apply (moved_by_prefix st0 st1 st' Hf1'). exact Hy.
        - exact Hoff1.
        - eapply listSatisfiable_off with (xs := moved_by st st0).
          + exact Hsc2.
          + intros y Hy. apply Hmv.
            apply (moved_by_prefix st st0 st' Hf0'). exact Hy.
          + exact Hoff0.
          + exact Hcar2. }
      { eauto 4 with sec. }
      { eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec. }

      (** the conditionals the pass built *)
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts1x) as Hew0
          by (eapply assign_lexps_elementwise; eauto).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) ts2x) as Hew1
          by (eapply assign_lexps_elementwise; eauto).
      edestruct (unnest_ite_types (hd_default f0) ck thx (List.concat ess0)
                   (List.concat ess1) tys ts1x ts2x xst)
        as (rs & Hjr & Hallr); eauto.

      (** the earlier witnesses survive the later ones *)
      assert (agree_off (moved_by st0 st2) dlt0 dlt2) as Hoff02.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff1].
          apply (moved_by_prefix st0 st1 st2 Hfc).
        - eapply agree_off_incl; [|exact Hoff2].
          apply (moved_by_suffix st0 st1 st2 Hfb). }
      assert (forall y, In y (moved_by st0 st2) ->
                        ~ In y (scope ++ moved_by st st0)) as Hsep0.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix st st0 st' Hfa).
          apply (moved_by_prefix st0 st2 st' Hfd). exact Hin.
        - exact (moved_by_disjoint st st0 st2 y Hy Hin). }
      assert (forall y, In y (moved_by st1 st2) ->
                        ~ In y (scope ++ moved_by st0 st1)) as Hsep1.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (moved_by_suffix st st1 st' Hfab).
          apply (moved_by_prefix st1 st2 st' Hfd). exact Hin.
        - exact (moved_by_disjoint st0 st1 st2 y Hy Hin). }

      inversion Hrel0 as [|p q ps qs Hr0 Hrel0r]; subst.
      assert (satisfiable dlt2 (fst thx) (merge amb (fst th))) as Hhead.
      { eapply satisfiable_off with (xs := moved_by st0 st2); eauto.
        - intros z Hz Hin. apply (Hsep0 z Hin).
          inversion Hts0 as [|w ws Hw Hwr]; subst. now apply Hw.
        - intros z Hz Hin. apply in_merge_inv in Hz as [Hz|Hz].
          + apply (Hsep0 z Hin). apply in_or_app. left. now apply amb_scoped.
          + apply (Hsep0 z Hin). apply in_or_app. left. now apply Hst0. }
      assert (Forall2 (fun t t' => satisfiable dlt2 (fst t') (merge amb (fst t)))
                (tf1 :: ts1r) ts1x) as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p0 q0 Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st2); eauto.
        - intros z Hz Hin. apply (Hsep1 z Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros z Hz Hin. apply in_merge_inv in Hz as [Hz|Hz].
          + apply (Hsep1 z Hin). apply in_or_app. left. now apply amb_scoped.
          + apply (Hsep1 z Hin). apply in_or_app. left.
            eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1. }

      assert (Forall2 (fun src r => satisfiable dlt2 (fst r) (merge amb (fst src)))
                ts rs) as Hrelr0
          by (eapply ljoin_list_rel_head with (h := th) (h' := thx); eauto).
      assert (Forall (fun r => st_scoped (scope ++ moved_by st st2) (fst r)) rs)
        as Hscr.
      { eapply ljoin_list_scoped_head; [|exact Hjr| |].
        - inversion Hts0 as [|w ws Hw Hwr]; subst.
          eapply st_scoped_weaken; [|exact Hw].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st0 st2 Hf02).
        - eapply Forall_impl; [|exact Hts1].
          intros q0 Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. eapply incl_tran;
            [apply (moved_by_prefix st0 st1 st2 Hfc)
            |apply (moved_by_suffix st st0 st2 Hfa)].
        - eapply Forall_impl; [|exact Hts2].
          intros q0 Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st2 Hfab). }
      assert (Forall2 (fun src r =>
                satisfiable dlt2 (fst r) (merge amb (fst src))
                /\ st_scoped (scope ++ moved_by st st2) (fst r)) ts rs)
        as Hrelr.
      { clear - Hrelr0 Hscr.
        revert Hscr. induction Hrelr0 as [|src r ts0 rs0 Hq Hrest IH];
          intros Hscr; [constructor|].
        inversion Hscr as [|z zs Hz Hzr]; subst.
        constructor; [split; assumption|]. apply IH; assumption. }

      (** the emitted definitions *)
      edestruct (lifted_defs (scope ++ moved_by st st2) (List.map fst xs)
                   (unnest_ite (hd_default f0) (List.concat ess0)
                      (List.concat ess1) tys ck)
                   ts ced xst xstd dlt2)
        as (dlt3 & Hoff3 & Hce3 & Hscope3 & Hrel3).
      { exact Hndfst. }
      { rewrite map_length, Hlxs. symmetry.
        apply unnest_ite_length; auto. }
      { exact Hsepx. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. left.
        rewrite emitted_defs_combine_form, vars_defined_defs; [exact Hy|].
        rewrite map_length, Hlxs. symmetry.
        apply unnest_ite_length; auto. }
      { intros y Hy. apply in_or_app. left. now apply amb_scoped. }
      { eapply Forall2_left; [exact Hallr|].
        intros a0 b0 (Ha1 & Ha2 & _). split; assumption. }
      { eapply Forall_impl; [|exact Hstsall].
        intros q0 Hq. eapply st_scoped_weaken; [|exact Hq].
        apply incl_appl, incl_refl. }
      { eapply Forall2_combine_via; [exact Hallr|exact Hrelr|].
        intros e src r (_ & _ & Hr) (Hq & Hqs).
        intros tf s s' Htf. rewrite (Hr tf s s' Htf). split; assumption. }
      { exact Hgend. }

      (** the composite witness *)
      assert (Forall2 (fun xa src => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src))) xs ts)
        as Hrel3'.
      { clear - Hrel3. revert ts Hrel3.
        induction xs as [|xa xs IH]; intros ts H; simpl in H.
        - inv H. constructor.
        - inversion H as [|p0 q0 ps0 qs0 Hpq Hr]; subst.
          constructor; auto. }
      assert (incl (sec_of (List.map fst xs)) (moved_by st st')) as Hincx.
      { intros b Hb. apply (moved_by_suffix st st2 st' Hfac). now apply Hbnew. }
      assert (agree_off (moved_by st0 st') dlt0 dlt3) as Hoff0'.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff02].
          apply (moved_by_prefix st0 st2 st' Hfd).
        - eapply agree_off_incl; [|exact Hoff3].
          intros b Hb. apply (moved_by_suffix st0 st2 st' Hf02).
          now apply Hbnew. }
      assert (agree_off (moved_by st1 st') dlt1 dlt3) as Hoff1''.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff2].
          apply (moved_by_prefix st1 st2 st' Hfd).
        - eapply agree_off_incl; [|exact Hoff3].
          intros b Hb. apply (moved_by_suffix st1 st2 st' Hfc).
          now apply Hbnew. }
      assert (agree_off (moved_by st2 st') dlt2 dlt3) as Hoff2''.
      { eapply agree_off_incl; [|exact Hoff3].
        intros b Hb. now apply Hbnew. }

      exists dlt3. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff0].
          apply (moved_by_prefix st st0 st' Hf0').
        + eapply agree_off_incl; [|exact Hoff0'].
          apply (moved_by_suffix st st0 st' Hfa).
      - apply listSatisfiable_app. split; [exact Hce3|].
        apply listSatisfiable_app. split.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st0) (xs := moved_by st0 st');
            eauto.
          intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
          * eapply (Hmv y); [|exact Hin].
            apply (moved_by_suffix st st0 st' Hfa). exact Hy.
          * exact (moved_by_disjoint st st0 st' y Hin Hy).
        + apply listSatisfiable_app. split.
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st0 st1) (xs := moved_by st1 st');
              eauto.
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- eapply (Hmv y); [|exact Hin].
               apply (moved_by_suffix st st1 st' Hfab). exact Hy.
            -- exact (moved_by_disjoint st0 st1 st' y Hin Hy).
          * eapply listSatisfiable_off_scope
              with (sc := scope ++ moved_by st1 st2) (xs := moved_by st2 st');
              eauto.
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- eapply (Hmv y); [|exact Hin].
               apply (moved_by_suffix st st2 st' Hfac). exact Hy.
            -- exact (moved_by_disjoint st1 st2 st' y Hin Hy).
      - eapply Forall2_combine_via
          with (l3 := xs)
               (P0 := fun src xa => forall b, Env.find (fst xa) env = Some b ->
                        satisfiable dlt3 [b] (merge amb (fst src)))
               (Q := fun t xa => exists b, Env.find (fst xa) env = Some b
                                           /\ t = lvar b).
        + apply Forall2_flip, Hrel3'.
        + apply Forall2_flip, Hevars.
        + intros src t xa Hp (b & Hb & ?); subst.
          rewrite fst_lvar. now apply Hp.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope3].
          intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
          apply incl_app; [|eapply incl_tran; [exact Hincx|apply incl_appr,
                                                            incl_refl]].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st2 st' Hfd).
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope0].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (moved_by_prefix st st0 st' Hf0').
          * apply Forall_app. split.
            -- eapply Forall_impl; [|exact Hscope1].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr. eapply incl_tran;
                 [apply (moved_by_prefix st0 st1 st' Hf1')
                 |apply (moved_by_suffix st st0 st' Hfa)].
            -- eapply Forall_impl; [|exact Hscope2].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr. eapply incl_tran;
                 [apply (moved_by_prefix st1 st2 st' Hfd)
                 |apply (moved_by_suffix st st1 st' Hfab)].
      - eapply Forall2_right_In; [exact Hevars|].
        intros xa t Hxa (b & Hb & ?); subst.
        rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst.
        apply in_or_app. right. apply Hincx.
        unfold sec_of. apply in_flat_map. exists (fst xa).
        split; [now apply in_map|]. rewrite Hb. now left.
    Qed.


  End Preservation.

End SecLusUnnestingExpr.
