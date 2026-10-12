(** Leg I: putting [fby]s into normalized form preserves generated constraints.

    This is the leg the two-operand [fby] rule exists for.  [fby_equation]
    rewrites only at the *top* of an equation -- it never descends into a
    subexpression -- so unlike unnesting there is no expression induction here
    at all: the operands [e0] and [e] are carried over verbatim, and what has
    to be shown is an entailment between a handful of constraint shapes.

    Two of the four shapes leave the equation alone.  The other two replace
    one delayed definition by an [ite] over a fresh initialisation flag
    together with a delayed definition of a fresh variable, and it is exactly
    there that typing *both* operands of an [fby] pays: the source constraint
    already mentions the initial value's type, which is what the [ite]'s first
    branch needs, and the fresh variables are locals, so the witness valuation
    is free to give them the levels the new equations ask for.

    Everything above the equation level is shared with Leg U: [call_weakens],
    [generate_leqns_constraints_entails_G], [preserves_on_simplify] and the
    program-level lockstep [generate_all_lsignatures_weakens'] say nothing
    about which pass is being run. *)

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
From Velus Require Import Lustre.Normalization.NormFby.
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
From Velus Require Import SIF.SecLusUnnestingNodes.

Module SecLusNormFby
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
  (Import NF      : NORMFBY Ids Op OpAux LSyn UNN)
.

Module NODES := SecLusUnnestingNodes Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include NODES.

Import SECMONADNotations.
Import UNN.Fresh.Facts.
Import UNN.Fresh.Tactics.

  (** * The node lists the two drivers walk

      As on Leg U, and for the same reason: the drivers generate over
      [rev nodes], so the relation is a [Forall2], which reverses where a
      [normfby_global] run does not.  The pass's arguments are part of the
      relation because [normfby_node]'s result mentions them. *)

  Definition normfbyed_nodes (ns nt : list node) : Prop :=
    Forall2 (fun n m =>
               exists Q c (Hunt : unnested_node Q n)
                        (Hpref : n_prefixes n = norm1_prefs),
                 m = normfby_node Q c n Hunt Hpref) ns nt.

  Lemma normfby_global_normfbyed_nodes :
    forall G Hunt Hprefs, normfbyed_nodes G (normfby_global G Hunt Hprefs).
  Proof.
    induction G as [|n G IH]; intros Hunt Hprefs; simpl.
    - constructor.
    - constructor; [|apply IH].
      eexists. eexists. eexists. eexists. reflexivity.
  Qed.

  Lemma normfbyed_nodes_rev :
    forall ns nt, normfbyed_nodes ns nt -> normfbyed_nodes (rev ns) (rev nt).
  Proof.
    unfold normfbyed_nodes. induction 1; simpl; [constructor|].
    apply Forall2_app_both; [assumption|constructor; [assumption|constructor]].
  Qed.

  (** [inversion] on an [OK] equality simplifies under the hood, and what it
      simplifies is [merge] -- into its inner [fix], on one side of the goal
      only, after which the algebraic lemmas stop matching.  Projecting through
      a lemma stated on abstract components keeps the terms intact. *)
  Lemma OK_pair_inv :
    forall {A B : Type} (a a' : A) (s s' : B),
      OK (a, s) = OK (a', s') -> a' = a /\ s' = s.
  Proof.
    intros A B a a' s s' H. inversion H. split; reflexivity.
  Qed.

  Section NormFbyNode.

    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable scope   : list ident.

    (** * What the pass does to a node's record

        The same three facts as [unnest_node_fields], and they hold for the
        same reason: the pass copies the interface and extends [n_vars] on the
        right with the variables its run created. *)
    Lemma normfby_node_fields :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs),
        (normfby_node Q c n Hunt Hpref).(n_eqs)
          = fst (fby_equations
                   (PS.union c (ps_from_list (List.map fst (n_out n))))
                   n.(n_eqs) init_st)
        /\ (normfby_node Q c n Hunt Hpref).(n_vars)
             = n.(n_vars)
                 ++ idty (st_anns
                            (snd (fby_equations
                                    (PS.union c
                                       (ps_from_list (List.map fst (n_out n))))
                                    n.(n_eqs) init_st)))
        /\ (normfby_node Q c n Hunt Hpref).(n_in) = n.(n_in)
        /\ (normfby_node Q c n Hunt Hpref).(n_out) = n.(n_out)
        /\ (normfby_node Q c n Hunt Hpref).(n_name) = n.(n_name).
    Proof.
      intros Q c n Hunt Hpref. unfold normfby_node.
      repeat split; reflexivity.
    Qed.

    (** * The clocks the fby run records are the node's own

        Leg I's counterpart of [unnest_node_state_clocks_found], and the first
        of the three run facts [normfby_node_step] was given.  [normfby_node]
        puts the fresh state's annotations into its local variables (dropping
        only the cut flag), so a variable the run created is found at exactly
        the clock the run stored. *)

    Lemma normfby_node_state_clocks :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs) eqs' stf y a,
        map_bind (fby_equation
                    (PS.union c (ps_from_list (List.map fst (n_out n)))))
          n.(n_eqs) init_st = (eqs', stf) ->
        In (y, a) (st_anns stf) ->
        find_clock (lnode_clock_env (normfby_node Q c n Hunt Hpref)) y
        = OK (snd (fst a)).
    Proof.
      intros Q c n Hunt Hpref eqs' stf y a Hrun Hin.
      assert (fby_equations
                (PS.union c (ps_from_list (List.map fst (n_out n))))
                n.(n_eqs) init_st = (List.concat eqs', stf)) as Hfbys.
      { unfold fby_equations. apply bind_spec.
        exists eqs', stf. split; [exact Hrun|apply ret_spec]. }
      apply (lnode_clock_env_vars _ y (fst a)).
      destruct (normfby_node_fields Q c n Hunt Hpref) as (_ & Hv & _).
      rewrite Hv, Hfbys. cbn [snd].
      apply in_or_app. right.
      unfold idty. apply in_map_iff. exists (y, a).
      split; [reflexivity|exact Hin].
    Qed.

    (** And the second run fact: the state's identifiers are distinct.  This
        is Velus's own [st_valid_after] invariant, which [fby_equations]
        preserves and [init_st] starts in; taking the "after" set empty makes
        it exactly [NoDup (st_ids stf)]. *)

    Lemma fby_run_st_ids_NoDup :
      forall to_cut (eqs : list equation) eqs' stf,
        map_bind (fby_equation to_cut) eqs init_st = (eqs', stf) ->
        NoDup (st_ids stf).
    Proof.
      intros to_cut eqs eqs' stf Hrun.
      assert (fby_equations to_cut eqs init_st = (List.concat eqs', stf))
        as Hfbys.
      { unfold fby_equations. apply bind_spec.
        exists eqs', stf. split; [exact Hrun|apply ret_spec]. }
      assert (st_valid_after
                (init_st : fresh_st ((type * clock) * bool)) PS.empty)
        as Hinit.
      { apply (UNN.Fresh.init_st_valid norm2 PS.empty PS.empty).
        - intro Hc. now apply PSF.empty_iff in Hc.
        - intros z Hz. exfalso. now apply PSF.empty_iff in Hz. }
      pose proof (fby_equations_st_valid to_cut eqs (List.concat eqs')
                    init_st stf PS.empty Hfbys Hinit) as Hvalid.
      apply UNN.Fresh.st_valid_NoDup in Hvalid.
      assert (PSP.to_list PS.empty = []) as Hemp by apply PSP.elements_empty.
      rewrite Hemp, app_nil_r in Hvalid. exact Hvalid.
    Qed.

    (** * Five of a signature's six fields are equal on the nose

        [generate_lnode_sig] reads the interface fields off [n_name], [n_in],
        [n_out] and the one naming environment, all four of which the pass
        copies.  So only [s_constraints] can differ -- which is exactly what
        [preserves_on] speaks about. *)
    Corollary normfby_node_sig_interface :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (G G' : secglobal) (aux : list node_aux_names)
             st0 st0' sg st1 sg' st1',
        generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
        generate_lnode_sig G' (normfby_node Q c n Hunt Hpref) env aux st0'
          = OK (sg', st1') ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg.
    Proof.
      intros Q c n Hunt Hpref G G' aux st0 st0' sg st1 sg' st1' H H'.
      apply (lnode_sig_inv env) in H
        as (c1 & r1 & ct1 & rt1 & i1 & o1 & l1 & cs1
            & Ha1 & Hc1 & Hr1 & Hi1 & Ho1 & _ & _ & ?); subst sg.
      apply (lnode_sig_inv env) in H'
        as (c2 & r2 & ct2 & rt2 & i2 & o2 & l2 & cs2
            & Ha2 & Hc2 & Hr2 & Hi2 & Ho2 & _ & _ & ?); subst sg'.
      cbn [n_name n_in n_out normfby_node] in Ha2, Hi2, Ho2.
      rewrite Ha1 in Ha2. inversion Ha2; subst c2 r2.
      rewrite Hc1 in Hc2. inversion Hc2; subst ct2.
      rewrite Hr1 in Hr2. inversion Hr2; subst rt2.
      rewrite Hi1 in Hi2. inversion Hi2; subst i2.
      rewrite Ho1 in Ho2. inversion Ho2; subst o2.
      cbn [s_name s_in s_out s_clk s_reset].
      repeat split; reflexivity.
    Qed.

    (** * The clock environments agree where the generator looks

        [find_clock_node_ext_defd] takes no account of which pass extended the
        variables, so this is a quotation. *)
    Corollary generate_leqns_normfby_node_cenv :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs) (G : secglobal) s,
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env (normfby_node Q c n Hunt Hpref)) n.(n_eqs) s
        = generate_leqns_constraints G env base_ty rst_ty
            (lnode_clock_env n) n.(n_eqs) s.
    Proof.
      intros Q c n Hunt Hpref G s.
      apply EQ.generate_leqns_constraints_cenv_ext.
      intros x Hx.
      destruct (normfby_node_fields Q c n Hunt Hpref) as (_ & Hv & Hi & Ho & _).
      exact (find_clock_node_ext_defd n (normfby_node Q c n Hunt Hpref) _ x
               Hi Ho Hv Hx).
    Qed.


    (** * Moving a valuation at one name

        The whole semantic content of this leg is a choice of level for the
        variables the pass creates, and the choice is the same in all three
        interesting cases: give a fresh variable exactly the level of the
        left-hand side of the equation it was created for.  Both new equations
        then hold -- the one that *defines* the fresh variable because that is
        its own bound, and the one that *uses* it because the source equation
        already bounded that level by the variable it defines.

        [upds] and its lemmas are already in [SecLusUnnestingExpr.v], where the
        call case needed the same move for a call's minted result names. *)

    Variable G   : secglobal.
    Variable cenv : Env.t (type * clock).

    (** * The expression shapes the pass produces, typed

        Each is one layer of [assign_lexp_type], read forwards.  The operands
        are carried over verbatim from the source equation, so their types are
        literally the same terms on both sides; only the wrapper differs. *)

    Lemma assign_lexp_Efby_pair :
      forall e0 e ann s0 s1 st,
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e st = OK ([(s1, [])], st) ->
        assign_lexp_type G env base_ty rst_ty (Efby [e0] [e] [ann]) st
          = OK ([(merge s0 s1, [])], st).
    Proof.
      intros e0 e ann s0 s1 st H0 H1.
      rewrite assign_lexp_Efby.
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact H0|].
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact H1|].
      reflexivity.
    Qed.

    Lemma assign_lexp_Earrow_pair :
      forall e0 e ann s0 s1 st,
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e st = OK ([(s1, [])], st) ->
        assign_lexp_type G env base_ty rst_ty (Earrow [e0] [e] [ann]) st
          = OK ([(merge s0 s1, [])], st).
    Proof.
      intros e0 e ann s0 s1 st H0 H1.
      rewrite assign_lexp_Earrow.
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact H0|].
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact H1|].
      reflexivity.
    Qed.

    Lemma assign_lexp_Evar_type :
      forall x a b st,
        Env.find x env = Some b ->
        assign_lexp_type G env base_ty rst_ty (Evar x a) st
          = OK ([(([b] : ST), [])], st).
    Proof.
      intros x a b st Hb.
      rewrite assign_lexp_Evar.
      eapply sec_bind_ok; [apply find_env_OK; exact Hb|reflexivity].
    Qed.

    Lemma assign_lexp_Eite_var :
      forall i ia e0 ef ann bi s0 sf st,
        Env.find i env = Some bi ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty ef st = OK ([(sf, [])], st) ->
        assign_lexp_type G env base_ty rst_ty
          (Eite (Evar i ia) [e0] [ef] ann) st
          = OK ([(merge (merge [bi] s0) sf, [])], st).
    Proof.
      intros i ia e0 ef ann bi s0 sf st Hi H0 Hf.
      rewrite assign_lexp_Eite.
      eapply sec_bind_ok; [apply (assign_lexp_Evar_type i ia bi st Hi)|].
      eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|].
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact H0|].
      eapply sec_bind_ok; [apply assign_lexps_single_intro; exact Hf|].
      reflexivity.
    Qed.

    (** A constant under [when]s mentions exactly the samplers of the clock it
        is written on, and [assign_clk_type] of that clock mentions those and
        the base.  So the initial values the pass invents carry nothing the
        ambient of the equation does not already carry -- which is why they
        cost nothing in the entailment. *)
    Lemma add_whens_const_type :
      forall cst ty ck ckty st,
        assign_clk_type env base_ty ck = Some ckty ->
        exists sa,
          assign_lexp_type G env base_ty rst_ty
            (add_whens (Econst cst) ty ck) st = OK ([(sa, [])], st)
          /\ (forall z, In z sa -> In z ckty).
    Proof.
      intros cst ty ck. induction ck as [|ck IH x b];
        intros ckty st Hck.
      - cbn in Hck. inversion Hck; subst ckty.
        exists ([] : ST). split; [|intros z []].
        cbn [add_whens]. rewrite assign_lexp_Econst. reflexivity.
      - cbn [assign_clk_type] in Hck.
        destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:E;
          [|discriminate Hck].
        destruct (Env.find x env) as [g|] eqn:Eg; [|discriminate Hck].
        cbn in Hck. inversion Hck; subst ckty.
        assert (Hrefl : Some ckty' = Some ckty') by reflexivity.
        destruct (IH ckty' st Hrefl) as (sa & Ha & Hincl).
        exists (merge sa [g]). split.
        + cbn [add_whens]. rewrite assign_lexp_Ewhen.
          eapply sec_bind_ok; [apply assign_lexps_single_intro; exact Ha|].
          eapply sec_bind_ok; [apply find_env_OK; exact Eg|].
          reflexivity.
        + apply merge_incl_mono; [exact Hincl|intros z Hz; exact Hz].
    Qed.


    (** * The entailment, one equation shape at a time

        Two of [fby_equation]'s four shapes leave the equation alone, so there
        is nothing to prove for them.  The other two are below.  In both, the
        move is the same: give each variable the pass created exactly the level
        of the left-hand side of the equation it was created for.  The equation
        that *defines* the fresh variable then holds because that level is its
        own bound, and the equation that *uses* it holds because the source
        equation already bounded that level by the variable it defines. *)

    Lemma satisfiable_singleton_bound :
      forall dlt lhs b,
        (forall z, In z lhs -> dlt z ⊑ hm_ext dlt [b]) ->
        constraintSatisfiable dlt (lhs, [b]).
    Proof.
      intros dlt lhs b H. unfold constraintSatisfiable, satisfiable.
      apply hm_ext_bound_from_members. exact H.
    Qed.

    (** * The move, once

        Every name a target constraint mentions is either one the source
        constraint already mentioned -- so its level is below the source's
        left-hand side -- or one the pass created, which was *given* that very
        level.  And every target constraint's right-hand side is either a
        created name, which therefore holds that level, or the variable the
        source equation already bounded by it.  So all of them hold, and this
        is the only semantic content of the leg. *)

    (** All the created names are given the *same* level, so a duplicate in
        the list is harmless and no [NoDup] is needed -- which is what spares
        the caller from having to show that the pass's two fresh identifiers are
        distinct. *)
    Lemma upds_const_val :
      forall (news : list ident) (v : Lat.t) dlt b,
        In b news ->
        upds news (List.map (fun _ : ident => v) news) dlt b = v.
    Proof.
      induction news as [|z news IH]; intros v dlt b Hb; [contradiction|].
      cbn [List.map upds]. unfold upd.
      destruct (ident_eq_dec b z) as [?|Hne]; [reflexivity|].
      apply IH. destruct Hb as [Hz|Hb];
        [subst z; now elim Hne|exact Hb]. 
    Qed.

    Lemma upds_const_off :
      forall (news : list ident) (v : Lat.t) dlt z,
        ~ In z news ->
        upds news (List.map (fun _ : ident => v) news) dlt z = dlt z.
    Proof. intros news v dlt z Hz. now apply upds_notin. Qed.

    Lemma fresh_names_entail :
      forall dlt (news : list ident) L cs,
        (forall z, In z news -> ~ In z L) ->
        Forall (fun c =>
                  (forall z, In z (fst c) -> In z L \/ In z news)
                  /\ exists d, snd c = [d]
                       /\ (In d news
                           \/ (~ In d news
                               /\ hm_ext dlt L ⊑ hm_ext dlt [d]))) cs ->
        listSatisfiable
          (upds news (List.map (fun _ : ident => hm_ext dlt L) news) dlt) cs.
    Proof.
      intros dlt news L cs HnL Hall.
      unfold listSatisfiable. eapply Forall_impl; [|exact Hall].
      intros (lhs, rhs) (Hlhs & d & Hrhs & Hd).
      cbn [fst snd] in Hlhs, Hrhs. subst rhs.
      apply satisfiable_singleton_bound. intros z Hz.
      assert (Hzv : upds news (List.map (fun _ : ident => hm_ext dlt L) news)
                      dlt z ⊑ hm_ext dlt L).
      { destruct (Hlhs z Hz) as [HzL|Hzn];
          [ rewrite upds_const_off by (intro Hc; exact (HnL z Hc HzL));
            exact (hm_ext_list_in1 dlt L z HzL)
          | rewrite (upds_const_val news (hm_ext dlt L) dlt z Hzn);
            exact (order_refl _ _ (Lat.eq_refl _)) ]. }
      destruct Hd as [Hdn|(Hdn & Hdb)].
      - (** the target is a created name, which holds exactly that level *)
        cbn [hm_ext].
        rewrite (upds_const_val news (hm_ext dlt L) dlt d Hdn).
        eapply order_trans; [exact Hzv|apply join_bound1].
      - (** or the source equation already bounded that level by it *)
        cbn [hm_ext].
        rewrite (upds_const_off news (hm_ext dlt L) dlt d Hdn).
        eapply order_trans; [exact Hzv|exact Hdb].
    Qed.

    Lemma Forall_and :
      forall {A : Type} (P Q : A -> Prop) l,
        Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
    Proof.
      induction 1 as [|a l Ha Hl IH]; intros HQ; [constructor|].
      inversion HQ as [|a0 l0 Hqa Hql]; subst.
      constructor; [split; [exact Ha|exact Hqa]|exact (IH Hql)].
    Qed.

    (** The move, and the scopedness that comes with it.

        The shape facts are stated *outside* the valuation, because the target
        chunk has to be shown scoped whether or not the source is satisfiable
        at all -- and it is that scopedness, together with the created names
        being new, that [preserves_on_concat_list] asks for when the chunks are
        assembled into a whole body. *)
    Lemma preserves_on_fresh_names :
      forall (news : list ident) L ce cet,
        (forall z, In z L -> In z scope) ->
        (forall z, In z news -> ~ In z scope) ->
        (** what each target constraint mentions, and what it bounds *)
        Forall (fun c =>
                  (forall z, In z (fst c) -> In z L \/ In z news)
                  /\ exists d, snd c = [d] /\ (In d news \/ In d scope)) cet ->
        (** and, for the ones bounding a visible name, that the source did too *)
        (forall dlt, listSatisfiable dlt ce ->
           Forall (fun c => forall d, snd c = [d] -> In d scope ->
                     hm_ext dlt L ⊑ hm_ext dlt [d]) cet) ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ news) cet.
    Proof.
      intros news L ce cet HLs Hns Hshape Hbound.
      assert (HnL : forall z, In z news -> ~ In z L)
        by (intros z Hz Hc; exact (Hns z Hz (HLs z Hc))).
      split.
      - intros dlt Hsat.
        exists (upds news (List.map (fun _ : ident => hm_ext dlt L) news) dlt).
        split.
        + intros z Hz. symmetry. apply upds_const_off.
          intro Hc. exact (Hns z Hc Hz).
        + apply fresh_names_entail; [exact HnL|].
          eapply Forall_impl; [|exact (Forall_and _ _ _ Hshape (Hbound dlt Hsat))].
          intros c ((Hlhs & d & Hd & Hdc) & Hb).
          split; [exact Hlhs|exists d; split; [exact Hd|]].
          destruct Hdc as [Hdn|Hds]; [now left|].
          right. split;
            [intro Hc'; exact (Hns d Hc' Hds)|exact (Hb d Hd Hds)].
      - unfold constraints_scoped, SymTypes.constraints_scoped.
        eapply Forall_impl; [|exact Hshape].
        intros (lhs, rhs) (Hlhs & d & Hd & Hdc).
        cbn [fst snd] in Hlhs, Hd. subst rhs.
        intros y Hy.
        unfold SymTypes.constraint_scope in Hy. cbn [fst snd] in Hy.
        apply in_app_iff in Hy as [Hy|Hy].
        + destruct (Hlhs y Hy) as [HyL|Hyn];
            [apply in_or_app; left; exact (HLs y HyL)
            |apply in_or_app; now right].
        + destruct Hy as [Hy|[]]; subst y.
          destruct Hdc as [Hdn|Hds];
            [apply in_or_app; now right|apply in_or_app; now left].
    Qed.

    (** The source equation's own constraint, and the three ways a name can
        reach the left-hand side it bounds. *)
    Lemma source_lhs_members :
      forall rst ckty s0 s1 z,
        In z (merge [rst] ckty) \/ In z s0 \/ In z s1 ->
        In z (merge (merge [rst] ckty) (merge s0 s1)).
    Proof.
      intros rst ckty s0 s1 z [Hz|[Hz|Hz]];
        [apply in_merge_left; exact Hz
        |apply in_merge_right, in_merge_left; exact Hz
        |apply in_merge_right, in_merge_right; exact Hz].
    Qed.

    (** The initialisation equation the pass may add: its own constraint puts
        the flag below the ambient of the clock it is written on, and nothing
        else, because a constant under [when]s mentions only that clock's
        samplers. *)
    Lemma init_eq_constraint :
      forall i ck ckty bi st c u,
        find_clock cenv i = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find i env = Some bi ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([i], [Efby [add_whens (Econst true_const) bool_type ck]
                      [add_whens (Econst false_const) bool_type ck]
                      [(bool_type, (ck, None))]]) st = OK (c, u) ->
        exists sw,
          c = [(merge (merge [rst_ty] ckty) sw, [bi])]
          /\ (forall z, In z sw -> In z ckty)
          /\ u = st.
    Proof.
      intros i ck ckty bi st c u Hcki Hckty Hbi Hgen.
      destruct (add_whens_const_type true_const bool_type ck ckty st Hckty)
        as (swt & Ht & Hit).
      destruct (add_whens_const_type false_const bool_type ck ckty st Hckty)
        as (swf & Hf & Hif).
      rewrite generate_leqn_constraint_def in Hgen by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv i
                 (Efby [add_whens (Econst true_const) bool_type ck]
                       [add_whens (Econst false_const) bool_type ck]
                       [(bool_type, (ck, None))])
                 ck ckty (merge swt swf) bi st Hcki Hckty
                 (assign_lexp_Efby_pair _ _ _ swt swf st Ht Hf) Hbi) in Hgen.
      apply OK_pair_inv in Hgen as (? & ?); subst c u.
      exists (merge swt swf). split; [reflexivity|split; [|reflexivity]].
      intros z Hz. apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
        [exact (Hit z Hz)|exact (Hif z Hz)].
    Qed.

    Lemma generate_leqns_cons_inv :
      forall eq eqs cs st u,
        generate_leqns_constraints G env base_ty rst_ty cenv (eq :: eqs) st
          = OK (cs, u) ->
        exists c1 v1 c2,
          generate_leqn_constraint G env base_ty rst_ty cenv eq st = OK (c1, v1)
          /\ generate_leqns_constraints G env base_ty rst_ty cenv eqs v1
             = OK (c2, u)
          /\ cs = c1 ++ c2.
    Proof.
      intros eq eqs cs st u H.
      rewrite generate_leqns_constraints_cons in H.
      apply sec_bind_inv in H as (c1 & v1 & Hc1 & H).
      apply sec_bind_inv in H as (c2 & v2 & Hc2 & Hret).
      unfold SC.ret in Hret. inversion Hret; subst cs v2.
      exists c1, v1, c2. split; [exact Hc1|split; [exact Hc2|reflexivity]].
    Qed.

    (** The [ite] the pass writes mentions the flag, the initial value and the
        variable holding the delayed one -- and nothing else -- so every name
        in it is either one the source equation mentioned or one of the two the
        pass created. *)
    Lemma ite_lhs_members :
      forall ckty s0 sf news z,
        (forall y, In y sf -> In y news \/
                              In y (merge (merge [rst_ty] ckty) (merge s0 sf))) ->
        In z (merge (merge [rst_ty] ckty) (merge (merge news s0) sf)) ->
        In z (merge (merge [rst_ty] ckty) (merge s0 sf)) \/ In z news.
    Proof.
      intros ckty s0 sf news z Hsf Hz.
      apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
      { left. apply in_merge_left. exact Hz. }
      apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
      - apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
          [now right
          |left; apply in_merge_right, in_merge_left; exact Hz].
      - destruct (Hsf z Hz) as [Hc|Hc]; [now right|now left].
    Qed.

    (** Cutting a delayed definition at an output: the pass introduces a fresh
        variable [x'] carrying the [fby] and reads it back through an [Evar].
        [x'] gets the level of the source equation's right-hand side, which is
        both what its own new equation bounds and what the source equation
        already put below [x]. *)
    Lemma fby_cut_entails :
      forall x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u',
        find_clock cenv x  = OK ck ->
        find_clock cenv x' = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find x' env = Some b' ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (** what the source constraint mentions is visible, and the created
            variable's security name is not *)
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        ~ In b' scope ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [ann]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] st
          = OK (cet, u') ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ [b']) cet.
    Proof.
      intros x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u'
        Hckx Hckx' Hckty Hb Hb' H0 H1 HLs Hbs Hsc Hsrc Htgt.
      pose proof (assign_lexp_Efby_pair e0 e ann s0 s1 st H0 H1) as Hfby.
      (** the source's single constraint *)
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b st
                 Hckx Hckty Hfby Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      (** the target's two *)
      apply generate_leqns_cons_inv in Htgt as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Evar x' ann) ck ckty ([b'] : ST) b st Hckx Hckty
                 (assign_lexp_Evar_type x' ann b' st Hb') Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      apply generate_leqns_cons_inv in Hc2 as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
      rewrite generate_leqn_constraint_def in Hd1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x'
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b' st
                 Hckx' Hckty Hfby Hb') in Hd1.
      apply OK_pair_inv in Hd1 as (? & ?); subst d1 w1.
      apply generate_leqns_constraints_nil in Hd2 as (? & _); subst d2.
      subst c2 cet. rewrite app_nil_r.
      (** the move *)
      eapply preserves_on_fresh_names
        with (news := [b'])
             (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      - exact HLs.
      - intros z [Hz|[]]; subst z. exact Hsc.
      - (** what each of the two mentions *)
        cbn [app]. constructor; [|constructor; [|constructor]].
        + split.
          * cbn [fst]. intros z Hz.
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
              [left; apply in_merge_left; exact Hz|right; exact Hz].
          * exists b. split; [reflexivity|right; exact Hbs].
        + split.
          * cbn [fst]. intros z Hz. now left.
          * exists b'. split; [reflexivity|left; now left].
      - (** and what the source already bounded *)
        intros dlt Hsat.
        assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                      ⊑ hm_ext dlt [b]).
        { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
          exact (Hsat _ (in_eq _ _)). }
        cbn [app]. constructor; [|constructor; [|constructor]].
        + cbn [snd]. intros d Hd _.
          inversion Hd; subst d. exact Hc0.
        + cbn [snd]. intros d Hd Hds.
          inversion Hd; subst d. contradiction.
    Qed.

    (** * An arrow becomes an [ite] on a fresh initialisation flag

        The flag is given the level of the source equation's right-hand side.
        The [ite] then holds because the source equation already put that level
        below the variable it defines, and the flag's own equation -- when the
        pass had to create one -- holds because a constant under [when]s
        mentions only the samplers of its clock, which the ambient already
        carries. *)
    Lemma arrow_entails :
      forall x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs,
        find_clock cenv x = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x env = Some b ->
        Env.find i env = Some bi ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        ~ In bi scope ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name))]) :: eqs) st = OK (cet, u') ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ [bi]) cet.
    Proof.
      intros x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs
        Hckx Hckty Hb Hbi H0 H1 HLs Hbs Hsc Heqs Hsrc Htgt.
      (** the source's single constraint *)
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Earrow [e0] [e] [(ty, (ck, name))]) ck ckty (merge s0 s1) b st
                 Hckx Hckty
                 (assign_lexp_Earrow_pair e0 e (ty, (ck, name)) s0 s1 st H0 H1)
                 Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      (** the target's [ite], and whatever the flag needed *)
      apply generate_leqns_cons_inv in Htgt as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name)))
                 ck ckty (merge (merge [bi] s0) s1) b st Hckx Hckty
                 (assign_lexp_Eite_var i (bool_type, (ck, Some i)) e0 e
                    ([ty], (ck, name)) bi s0 s1 st Hbi H0 H1) Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      (** the flag's own equation, computed once for both halves *)
      assert (Hinit :
                c2 = []
                \/ exists sw, c2 = [(merge (merge [rst_ty] ckty) sw, [bi])]
                              /\ (forall z, In z sw -> In z ckty)).
      { destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
        - apply generate_leqns_constraints_nil in Hc2 as (? & _); subst c2.
          now left.
        - apply generate_leqns_cons_inv in Hc2
            as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
          destruct (init_eq_constraint i ck ckty bi _ d1 w1 Hcki Hckty Hbi Hd1)
            as (sw & ? & Hsw & ?); subst d1 w1.
          apply generate_leqns_constraints_nil in Hd2 as (? & _); subst d2.
          right. exists sw. split; [rewrite Hc2e, app_nil_r; reflexivity
                                   |exact Hsw]. }
      subst cet.
      (** the move *)
      eapply preserves_on_fresh_names
        with (news := [bi])
             (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      - exact HLs.
      - intros z [Hz|[]]; subst z. exact Hsc.
      - rewrite Forall_app. split.
        + constructor; [|constructor]. split.
          * cbn [fst]. intros z Hz.
            apply (ite_lhs_members ckty s0 s1 [bi] z);
              [intros y Hy; right; apply in_merge_right, in_merge_right; exact Hy
              |exact Hz].
          * exists b. split; [reflexivity|right; exact Hbs].
        + destruct Hinit as [Hc2e|(sw & Hc2e & Hsw)]; subst c2;
            [constructor|].
          constructor; [|constructor]. split.
          * cbn [fst]. intros z Hz.
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
              [left; apply in_merge_left; exact Hz
              |left; apply in_merge_left, in_merge_right; exact (Hsw z Hz)].
          * exists bi. split; [reflexivity|left; now left].
      - intros dlt Hsat.
        assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                      ⊑ hm_ext dlt [b]).
        { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
          exact (Hsat _ (in_eq _ _)). }
        rewrite Forall_app. split.
        + constructor; [|constructor]. cbn [snd]. intros d Hd _.
          inversion Hd; subst d. exact Hc0.
        + destruct Hinit as [Hc2e|(sw & Hc2e & _)]; subst c2;
            [constructor|].
          constructor; [|constructor]. cbn [snd]. intros d Hd Hds.
          inversion Hd; subst d. contradiction.
    Qed.

    (** * A delayed definition with a non-constant initial value

        The shape the leg exists for.  The pass cannot leave [e0 fby e] alone
        when [e0] is not a constant, so it writes instead an [ite] on a fresh
        flag between [e0] and a fresh variable [px] carrying [0 fby e].  Both
        fresh variables are given the level of the source equation's right-hand
        side.

        [px]'s own equation then holds because that level already bounds [e]'s;
        and the [ite] holds because the source equation bounded that level by
        the variable it defines -- which it does *only* because the [fby] rule
        types both operands.  Typing just the delayed one, as the NLustre rule
        legitimately does, would leave [e0]'s level out of the source
        constraint, and the [ite]'s first branch would have nothing to be
        below. *)
    Lemma fby_ite_entails :
      forall x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs,
        find_clock cenv x  = OK ck ->
        find_clock cenv px = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find i  env = Some bi ->
        Env.find px env = Some bp ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        ~ In bi scope ->
        ~ In bp scope ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
           :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                        [(ty, (ck, name))]])
           :: eqs) st = OK (cet, u') ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ [bp; bi]) cet.
    Proof.
      intros x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs
        Hckx Hckpx Hckty Hb Hbi Hbp H0 H1 HLs Hbs Hsci Hscp Heqs Hsrc Htgt.
      (** the source's single constraint *)
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Efby [e0] [e] [(ty, (ck, name))]) ck ckty (merge s0 s1) b st
                 Hckx Hckty
                 (assign_lexp_Efby_pair e0 e (ty, (ck, name)) s0 s1 st H0 H1)
                 Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      (** the [ite] *)
      apply generate_leqns_cons_inv in Htgt as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name)))
                 ck ckty (merge (merge [bi] s0) [bp]) b st Hckx Hckty
                 (assign_lexp_Eite_var i (bool_type, (ck, Some i)) e0
                    (Evar px (ty, (ck, Some px))) ([ty], (ck, name)) bi s0
                    ([bp] : ST) st Hbi H0
                    (assign_lexp_Evar_type px (ty, (ck, Some px)) bp st Hbp))
                 Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      (** the fresh variable's own delayed definition *)
      apply generate_leqns_cons_inv in Hc2 as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
      destruct (add_whens_const_type (init_type ty) ty ck ckty st Hckty)
        as (sw & Hw & Hsw).
      rewrite generate_leqn_constraint_def in Hd1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv px
                 (Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                    [(ty, (ck, name))])
                 ck ckty (merge sw s1) bp st Hckpx Hckty
                 (assign_lexp_Efby_pair _ e (ty, (ck, name)) sw s1 st Hw H1)
                 Hbp) in Hd1.
      apply OK_pair_inv in Hd1 as (? & ?); subst d1 w1.
      (** and the flag's, if the pass created one *)
      assert (Hinit :
                d2 = []
                \/ exists swi, d2 = [(merge (merge [rst_ty] ckty) swi, [bi])]
                               /\ (forall z, In z swi -> In z ckty)).
      { destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
        - apply generate_leqns_constraints_nil in Hd2 as (? & _); subst d2.
          now left.
        - apply generate_leqns_cons_inv in Hd2
            as (f1 & y1 & f2 & Hf1 & Hf2 & Hd2e).
          destruct (init_eq_constraint i ck ckty bi _ f1 y1
                      Hcki Hckty Hbi Hf1) as (swi & ? & Hswi & ?);
            subst f1 y1.
          apply generate_leqns_constraints_nil in Hf2 as (? & _); subst f2.
          right. exists swi. split; [rewrite Hd2e, app_nil_r; reflexivity
                                    |exact Hswi]. }
      subst c2 cet.
      (** the move *)
      eapply preserves_on_fresh_names
        with (news := [bp; bi])
             (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      - exact HLs.
      - intros z [Hz|[Hz|[]]]; subst z; [exact Hscp|exact Hsci].
      - rewrite Forall_app. split.
        + (** the [ite] *)
          constructor; [|constructor]. split.
          * cbn [fst]. intros z Hz.
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
              [left; apply in_merge_left; exact Hz|].
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
            -- apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [destruct Hz as [Hz|[]]; subst z; right; right; now left
                 |left; apply in_merge_right, in_merge_left; exact Hz].
            -- destruct Hz as [Hz|[]]; subst z. right. now left.
          * exists b. split; [reflexivity|right; exact Hbs].
        + rewrite Forall_app. split.
          * (** the fresh variable's own equation *)
            constructor; [|constructor]. split.
            -- cbn [fst]. intros z Hz. left.
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [apply in_merge_left; exact Hz|].
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [apply in_merge_left, in_merge_right; exact (Hsw z Hz)
                 |apply in_merge_right, in_merge_right; exact Hz].
            -- exists bp. split; [reflexivity|left; now left].
          * destruct Hinit as [Hd2e|(swi & Hd2e & Hswi)]; subst d2;
              [constructor|].
            constructor; [|constructor]. split.
            -- cbn [fst]. intros z Hz. left.
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [apply in_merge_left; exact Hz
                 |apply in_merge_left, in_merge_right; exact (Hswi z Hz)].
            -- exists bi. split; [reflexivity|left; right; now left].
      - intros dlt Hsat.
        assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                      ⊑ hm_ext dlt [b]).
        { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
          exact (Hsat _ (in_eq _ _)). }
        rewrite Forall_app. split.
        + constructor; [|constructor]. cbn [snd]. intros d Hd _.
          inversion Hd; subst d. exact Hc0.
        + rewrite Forall_app. split.
          * constructor; [|constructor]. cbn [snd]. intros d Hd Hds.
            inversion Hd; subst d. contradiction.
          * destruct Hinit as [Hd2e|(swi & Hd2e & _)]; subst d2;
              [constructor|].
            constructor; [|constructor]. cbn [snd]. intros d Hd Hds.
            inversion Hd; subst d. contradiction.
    Qed.

    (** * What the pass creates, and where it records it

        Every identifier [fby_equation] invents is recorded in the fresh state
        with the annotation it was given, and the clock in that annotation is
        the clock of the equation it was invented for.  That is what lets the
        node level say what its declared clock is: the node the pass builds has
        [idty (st_anns _)] among its variables. *)

    Lemma init_var_for_clock_eqs :
      forall ck i eqsi st st',
        init_var_for_clock ck st = (i, eqsi, st') ->
        eqsi = []
        \/ eqsi = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                               [add_whens (Econst false_const) bool_type ck]
                               [(bool_type, (ck, None))]])].
    Proof.
      intros ck i eqsi st st' H. unfold init_var_for_clock in H.
      destruct (find (fun '(_, (ty, cl', isinit)) =>
                        isinit && (cl' ==b ck) && (ty ==b bool_type))
                  (st_anns st)) as [(y & a)|].
      - inversion H; subst. now left.
      - destruct (fresh_ident norm2 ((bool_type, ck), true) st) as (y, sty).
        inversion H; subst. now right.
    Qed.

    Lemma fby_iteexp_created :
      forall e0 e ty ck name e' eqs' st st',
        fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        exists i px eqsi,
          In (i, ((bool_type, ck), true)) (st_anns st')
          /\ In (px, ((ty, ck), false)) (st_anns st')
          /\ e' = Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))
          /\ eqs' = ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                              [(ty, (ck, name))]]) :: eqsi
          /\ (eqsi = []
              \/ eqsi = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                     [add_whens (Econst false_const) bool_type ck]
                                     [(bool_type, (ck, None))]])]).
    Proof.
      intros e0 e ty ck name e' eqs' st st' H.
      unfold fby_iteexp in H.
      apply bind2_spec in H as (i & eqsi & s1 & Ei & H).
      apply bind_spec in H as (px & s2 & Ep & H).
      rewrite ret_spec in H. inversion H; subst e' eqs' st'.
      exists i, px, eqsi.
      split; [|split; [|split; [reflexivity|split; [reflexivity|]]]].
      - apply (st_follows_incl s1 s2 (fresh_ident_st_follows _ _ _ _ _ Ep)).
        eapply init_var_for_clock_In; exact Ei.
      - eapply fresh_ident_In; exact Ep.
      - eapply init_var_for_clock_eqs; exact Ei.
    Qed.

    Lemma arrow_iteexp_created :
      forall e0 e ty ck name e' eqs' st st',
        arrow_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        exists i,
          In (i, ((bool_type, ck), true)) (st_anns st')
          /\ e' = Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name))
          /\ (eqs' = []
              \/ eqs' = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                     [add_whens (Econst false_const) bool_type ck]
                                     [(bool_type, (ck, None))]])]).
    Proof.
      intros e0 e ty ck name e' eqs' st st' H.
      unfold arrow_iteexp in H.
      apply bind2_spec in H as (i & eqsi & s1 & Ei & H).
      rewrite ret_spec in H. inversion H; subst e' eqs' st'.
      exists i. split; [|split; [reflexivity|]].
      - eapply init_var_for_clock_In; exact Ei.
      - eapply init_var_for_clock_eqs; exact Ei.
    Qed.


    (** * One equation, whatever shape it has

        [fby_equation_spec] splits the pass into its four shapes; two of them
        return the equation unchanged, so the two runs are the same run and
        [preserves_on_refl] closes them.  The other two are the case lemmas
        above, and all that is left is to read the created variables' clocks
        and names off the fresh state.

        The node's data enters as one hypothesis, quantified over the shape, so
        it is vacuous exactly on the shapes that need nothing.  What comes back
        is the chunk's own [extras] -- the created security names, which are the
        only ones its witness moves -- together with the chunk's scopedness to
        them.  That is exactly the package [preserves_on_concat_list] consumes
        when the chunks are assembled into a body. *)
    Theorem fby_equation_entails :
      forall to_cut xs es eqs' st st' ce cet s u u',
        fby_equation to_cut (xs, es) st = (eqs', st') ->
        (** what the node says about this equation *)
        (forall x e0 e ty ck name,
            xs = [x] ->
            (es = [Efby [e0] [e] [(ty, (ck, name))]]
             \/ es = [Earrow [e0] [e] [(ty, (ck, name))]]) ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ assign_lexp_type G env base_ty rst_ty e0 s = OK ([(s0, [])], s)
              /\ assign_lexp_type G env base_ty rst_ty e  s = OK ([(s1, [])], s)
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        (** and about the variables the pass created *)
        (forall y a, In (y, a) (st_anns st') ->
            find_clock cenv y = OK (snd (fst a))
            /\ exists c, Env.find y env = Some c /\ ~ In c scope) ->
        (** the source's own constraints are visible *)
        constraints_scoped scope ce ->
        generate_leqn_constraint G env base_ty rst_ty cenv (xs, es) s
          = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv eqs' s
          = OK (cet, u') ->
        exists extras,
          (forall y, In y extras -> ~ In y scope)
          /\ preserves_on scope ce cet
          /\ constraints_scoped (scope ++ extras) cet.
    Proof.
      intros to_cut xs es eqs' st st' ce cet s u u'
        Hrun Hdata Hnew Hcesc Hsrc Htgt.
      (** the shapes the pass leaves alone: one run, read twice *)
      assert (Hsame : eqs' = [(xs, es)] ->
                exists extras,
                  (forall y, In y extras -> ~ In y scope)
                  /\ preserves_on scope ce cet
                  /\ constraints_scoped (scope ++ extras) cet).
      { intro He. subst eqs'.
        apply generate_leqns_cons_inv in Htgt
          as (c1 & v1 & c2 & Hc1 & Hc2 & Hce).
        rewrite Hsrc in Hc1. apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
        apply generate_leqns_constraints_nil in Hc2 as (? & _); subst c2.
        subst cet. rewrite app_nil_r.
        exists []. split; [intros y []|].
        split; [apply preserves_on_refl|rewrite app_nil_r; exact Hcesc]. }
      destruct (fby_equation_spec to_cut xs es)
        as [(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
           |[(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
            |[(x & e0 & e & ann & Hxs & Hes & Heq)
             |Heq]]].
      - (** a constant initial value: cut at an output, or left alone *)
        subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun. cbv beta iota in Hrun.
        destruct (PS.mem x to_cut).
        + apply bind_spec in Hrun as (x' & s2 & Ex & Hrun).
          rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
          destruct (Hdata x e0 e ty ck name
                      (@Coq.Init.Logic.eq_refl _ _)
                      (or_introl (@Coq.Init.Logic.eq_refl _ _)))
            as (ckty & s0 & s1 & b & Hckx & Hckty & Hb & Hbs & H0 & H1 & HL).
          destruct (Hnew x' ((ty, ck), false)
                      (fresh_ident_In norm2 ((ty, ck), false) x' _ _ Ex))
            as (Hckx' & c & Hc & Hcs).
          cbn [fst snd] in Hckx'.
          exists [c]. split; [intros y [Hy|[]]; subst y; exact Hcs|].
          eapply fby_cut_entails;
            [exact Hckx|exact Hckx'|exact Hckty|exact Hb|exact Hc|exact H0
            |exact H1|exact HL|exact Hbs|exact Hcs|exact Hsrc|exact Htgt].
        + rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
          apply Hsame. reflexivity.
      - (** a non-constant initial value: the [ite] *)
        subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun.
        apply bind2_spec in Hrun as (fby & eqsa & s1 & Hfby & Hrun).
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
        destruct (fby_iteexp_created e0 e ty ck name fby eqsa st s1 Hfby)
          as (i & px & eqsi & Hi & Hpx & Hfbye & Heqsa & Heqsi).
        destruct (Hdata x e0 e ty ck name
                    (@Coq.Init.Logic.eq_refl _ _)
                    (or_introl (@Coq.Init.Logic.eq_refl _ _)))
          as (ckty & s0 & s1' & b & Hckx & Hckty & Hb & Hbs & H0 & H1 & HL).
        destruct (Hnew i ((bool_type, ck), true) Hi) as (Hcki & bi & Hbi & Hbis).
        destruct (Hnew px ((ty, ck), false) Hpx) as (Hckpx & bp & Hbp & Hbps).
        cbn [fst snd] in Hcki, Hckpx.
        subst fby eqsa.
        exists [bp; bi].
        split; [intros y [Hy|[Hy|[]]]; subst y; [exact Hbps|exact Hbis]|].
        eapply fby_ite_entails;
          [exact Hckx|exact Hckpx|exact Hckty|exact Hb|exact Hbi|exact Hbp
          |exact H0|exact H1|exact HL|exact Hbs|exact Hbis|exact Hbps
          | |exact Hsrc|exact Htgt].
        destruct Heqsi as [Heqsi|Heqsi];
          [now left|right; split; [exact Hcki|exact Heqsi]].
      - (** an arrow *)
        subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun.
        apply bind2_spec in Hrun as (ite & eqsa & s1 & Hite & Hrun).
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
        destruct (arrow_iteexp_created e0 e ty ck name ite eqsa st s1 Hite)
          as (i & Hi & Hite' & Heqsi).
        destruct (Hdata x e0 e ty ck name
                    (@Coq.Init.Logic.eq_refl _ _)
                    (or_intror (@Coq.Init.Logic.eq_refl _ _)))
          as (ckty & s0 & s1' & b & Hckx & Hckty & Hb & Hbs & H0 & H1 & HL).
        destruct (Hnew i ((bool_type, ck), true) Hi) as (Hcki & bi & Hbi & Hbis).
        cbn [fst snd] in Hcki.
        subst ite.
        exists [bi]. split; [intros y [Hy|[]]; subst y; exact Hbis|].
        eapply arrow_entails;
          [exact Hckx|exact Hckty|exact Hb|exact Hbi|exact H0|exact H1
          |exact HL|exact Hbs|exact Hbis
          | |exact Hsrc|exact Htgt].
        destruct Heqsi as [Heqsi|Heqsi];
          [now left|right; split; [exact Hcki|exact Heqsi]].
      - (** anything else, untouched *)
        rewrite Heq in Hrun. rewrite ret_spec in Hrun.
        inversion Hrun; subst eqs' st'.
        apply Hsame. reflexivity.
    Qed.

    (** ** What one target constraint does *)

    Inductive target_role : Type :=
    (** it defines a name the pass created *)
    | Defines (d : ident)
    (** it bounds a visible name, and [M] is the source level bounding it *)
    | Bounds (d : ident) (M : ST)
    (** it is an unchanged constraint whose entire scope is visible *)
    | Keeps.

    (** A created name's level has to be big enough for every constraint that
        defines it, and small enough for every constraint that uses it.  Hence
        containment in both clauses rather than equality: the flag's canonical
        level is its clock's ambient, which *contains* the left-hand side of
        its own equation (a constant under [when]s adds only samplers) and is
        *contained* in the ambient of every equation that mentions it. *)
    Definition role_shape (pairs : list (ident * ST))
      (c : constraint) (r : target_role) : Prop :=
      match r with
      | Defines d =>
          snd c = [d]
          /\ exists L, In (d, L) pairs /\ (forall z, In z (fst c) -> In z L)
      | Bounds d M =>
          snd c = [d]
          /\ In d scope
          /\ (forall z, In z M -> In z scope)
          /\ (forall z, In z (fst c) ->
                In z M
                \/ exists L, In (z, L) pairs /\ (forall w, In w L -> In w M))
      | Keeps => constraint_scoped scope c
      end.

    Definition role_bound (dlt : ident -> Lat.t)
      (c : constraint) (r : target_role) : Prop :=
      match r with
      | Defines _ => True
      | Bounds d M => hm_ext dlt M ⊑ hm_ext dlt [d]
      | Keeps => constraintSatisfiable dlt c
      end.

    Definition created_hidden (pairs : list (ident * ST)) : Prop :=
      forall y L, In (y, L) pairs -> ~ In y scope.

    Definition levels_visible (pairs : list (ident * ST)) : Prop :=
      forall y L z, In (y, L) pairs -> In z L -> In z scope.

    (** The non-uniform created variables are tied to the run that creates
        them.  A cut variable gets the whole source right-hand side; the [px]
        of a non-constant [fby] gets only the clock ambient and delayed
        operand.  Referring to the creating run avoids accidentally assigning
        every earlier variable with the same type and clock to this equation's
        level. *)
    (** The entries the variables THIS RUN created need.

        Keyed on the run's actual output, which is the whole point: keyed
        instead on a *description* of what the pass might produce -- a recorded
        annotation, or a run at an arbitrary state -- it speaks about
        identifiers the pass never created, and demands this equation's level
        for another equation's variable.  See
        work_docs/LegI_audit_2026_09_29.v.

        The two clauses are mutually exclusive by shape: a cut output binds
        through an [Evar], an [ite] output begins with an [Eite].  So no guard
        on [is_constant] is needed either. *)
    Definition fby_created_pairs
      (pairs : list (ident * ST)) (eqs' : list equation)
      (x : ident) (e0 e : exp) (ty : type) (ck : clock)
      (name : option ident) (ckty s0 s1 : ST) : Prop :=
      (forall x' ann bp,
          eqs' = [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] ->
          Env.find x' env = Some bp ->
          In (bp, merge (merge [rst_ty] ckty) (merge s0 s1)) pairs)
      /\
      (forall i px eqsi bp,
          eqs' = ([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                          [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
                 :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                              [(ty, (ck, name))]]) :: eqsi ->
          Env.find px env = Some bp ->
          In (bp, merge (merge [rst_ty] ckty) s1) pairs).

    (** ** The move, once, for a whole body *)

    (** The update does not need the created names to be pairwise distinct; it
        needs the assignment to be *functional*.  That distinction matters:
        when each equation contributes the entries for the variables it created,
        an initialisation flag shared between two equations on the same clock
        contributes twice -- at the same level both times, since a flag's level
        is its clock's ambient.  [NoDup] would reject that; functionality
        accepts it, and is all [upds] needs. *)
    Definition levels_functional (pairs : list (ident * ST)) : Prop :=
      forall y L1 L2, In (y, L1) pairs -> In (y, L2) pairs -> L1 = L2.

    Lemma upds_pairs_val :
      forall (pairs : list (ident * ST)) dlt y L,
        levels_functional pairs ->
        In (y, L) pairs ->
        upds (List.map fst pairs)
             (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt y
        = hm_ext dlt L.
    Proof.
      intros pairs dlt y L Hfun Hin.
      induction pairs as [|(z, M) pairs IH]; [contradiction|].
      cbn [List.map upds]. unfold upd. cbn [fst snd].
      destruct (ident_eq_dec y z) as [Hyz|Hyz].
      - (** the first entry for [y]: functionality says it is the right one *)
        subst z.
        assert (HLM : L = M) by (eapply Hfun; [exact Hin|now left]).
        rewrite HLM. reflexivity.
      - (** not this one, so [y] is further down *)
        apply IH.
        + intros w L1 L2 H1 H2.
          exact (Hfun w L1 L2 (or_intror H1) (or_intror H2)).
        + destruct Hin as [Hin|Hin]; [|exact Hin].
          inversion Hin; subst. now elim Hyz.
    Qed.

    Lemma upds_pairs_off :
      forall (pairs : list (ident * ST)) dlt z,
        ~ In z (List.map fst pairs) ->
        upds (List.map fst pairs)
             (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt z
        = dlt z.
    Proof.
      intros pairs dlt z Hz.
      apply (upds_notin (List.map fst pairs)
               (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt z).
      exact Hz.
    Qed.

    (** The witness is [upds (map fst pairs) (map (hm_ext dlt o snd) pairs) dlt].
        [levels_visible] is what makes that well defined: a level mentions no
        created name, so its value is the same before and after the update.

        This replaces [preserves_on_fresh_names], and is applied ONCE, at the
        node -- not per equation. *)
    Lemma preserves_on_created :
      forall (pairs : list (ident * ST)) (roles : list target_role) ce cet,
        levels_functional pairs ->
        created_hidden pairs ->
        levels_visible pairs ->
        Forall2 (role_shape pairs) cet roles ->
        (forall dlt, listSatisfiable dlt ce ->
           Forall2 (role_bound dlt) cet roles) ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ List.map fst pairs) cet.
    Proof.
      intros pairs roles ce cet Hnd Hhidden Hvisible Hshape Hbound.
      split.
      - intros dlt Hsat.
        set (dlt' :=
          upds (List.map fst pairs)
            (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt).
        assert (Hoff_scope :
            forall z, In z scope -> dlt' z = dlt z).
        { intros z Hz.
          unfold dlt'. apply (upds_pairs_off pairs dlt z).
          intro Hkey. apply in_map_iff in Hkey as ([y L] & Hy & Hin).
          cbn [fst] in Hy. subst y.
          exact (Hhidden z L Hin Hz). }
        assert (Hoff_type :
            forall T, (forall z, In z T -> In z scope) ->
              hm_ext dlt' T = hm_ext dlt T).
        { intros T HT. unfold dlt'.
          apply (hm_ext_upds T (List.map fst pairs)
                   (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt).
          intros z Hz Hkey.
          apply in_map_iff in Hkey as ([y L] & Hy & Hin).
          cbn [fst] in Hy. subst y.
          exact (Hhidden z L Hin (HT z Hz)). }
        exists dlt'. split.
        + intros z Hz. symmetry. exact (Hoff_scope z Hz).
        + unfold listSatisfiable.
          specialize (Hbound dlt Hsat).
          induction Hshape as [|c r cet roles Hcr Hshape IH];
            inversion Hbound as [|c0 r0 cet0 roles0 Hbr Hbounds]; subst.
          * constructor.
          * constructor; [|exact (IH Hbounds)].
            destruct c as [lhs rhs]. destruct r as [d|d M|].
            -- cbn [role_shape fst snd] in Hcr.
               destruct Hcr as (Hrhs & L & Hin & Hlhs). subst rhs.
               apply (satisfiable_singleton_bound dlt' lhs d).
               intros z Hz.
               rewrite (Hoff_scope z (Hvisible d L z Hin (Hlhs z Hz))).
               apply order_trans with (y := hm_ext dlt L).
               ++ apply (hm_ext_list_in1 dlt L z (Hlhs z Hz)).
               ++ cbn [hm_ext].
                  unfold dlt'.
                  rewrite (upds_pairs_val pairs dlt d L Hnd Hin).
                  apply join_bound1.
            -- cbn [role_shape fst snd] in Hcr.
               destruct Hcr as (Hrhs & Hd & HM & Hlhs). subst rhs.
               cbn [role_bound] in Hbr.
               apply (satisfiable_singleton_bound dlt' lhs d).
               intros z Hz. rewrite (Hoff_type [d]);
                 [|intros w [Hw|[]]; subst w; exact Hd].
               destruct (Hlhs z Hz) as [HzM|(L & Hin & HLM)].
               ++ rewrite (Hoff_scope z (HM z HzM)).
                  apply order_trans with (y := hm_ext dlt M).
                  ** apply (hm_ext_list_in1 dlt M z HzM).
                  ** exact Hbr.
               ++ unfold dlt'.
                  rewrite (upds_pairs_val pairs dlt z L Hnd Hin).
                  apply order_trans with (y := hm_ext dlt M).
                  ** apply (hm_ext_incl dlt L M HLM).
                  ** exact Hbr.
            -- cbn [role_shape] in Hcr. cbn [role_bound] in Hbr.
               apply (constraintSatisfiable_ext (lhs, rhs) scope dlt dlt').
               ++ exact Hcr.
               ++ intros z Hz. symmetry. exact (Hoff_scope z Hz).
               ++ exact Hbr.
      - unfold constraints_scoped, SymTypes.constraints_scoped.
        clear Hbound ce.
        induction Hshape as [|c r cet roles Hcr Hshape IH].
        + constructor.
        + constructor; [|exact IH].
          destruct c as [lhs rhs]. destruct r as [d|d M|].
          * cbn [role_shape fst snd] in Hcr.
            destruct Hcr as (Hrhs & L & Hin & Hlhs). subst rhs.
            intros z Hz. unfold SymTypes.constraint_scope in Hz.
            cbn [fst snd] in Hz. apply in_app_iff in Hz as [Hz|[Hz|[]]].
            -- apply in_or_app. left.
               exact (Hvisible d L z Hin (Hlhs z Hz)).
            -- subst z. apply in_or_app. right.
               apply in_map_iff. exists (d, L). split; [reflexivity|exact Hin].
          * cbn [role_shape fst snd] in Hcr.
            destruct Hcr as (Hrhs & Hd & HM & Hlhs). subst rhs.
            intros z Hz. unfold SymTypes.constraint_scope in Hz.
            cbn [fst snd] in Hz. apply in_app_iff in Hz as [Hz|[Hz|[]]].
            -- destruct (Hlhs z Hz) as [HzM|(L & Hin & HLM)].
               ++ apply in_or_app. left. exact (HM z HzM).
               ++ apply in_or_app. right. apply in_map_iff.
                  exists (z, L). split; [reflexivity|exact Hin].
            -- subst z. apply in_or_app. left. exact Hd.
          * cbn [role_shape] in Hcr.
            apply (constraint_scoped_incl scope
                     (scope ++ List.map fst pairs) (lhs, rhs)).
            -- intros z Hz. apply in_or_app. left. exact Hz.
            -- exact Hcr.
    Qed.

    (** ** The three shapes, repackaged

        Each keeps the premises of the corresponding [_entails] lemma and adds
        one membership fact per created name: its entry in the global
        assignment.  The proofs are the existing ones with the final
        [eapply preserves_on_fresh_names] replaced by an [exists roles]. *)

    Lemma fby_cut_roles :
      forall pairs x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u',
        find_clock cenv x  = OK ck ->
        find_clock cenv x' = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find x' env = Some b' ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        (** the cut variable carries the source equation's own right-hand side,
            which is exactly what its new equation bounds *)
        In (b', merge (merge [rst_ty] ckty) (merge s0 s1)) pairs ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [ann]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] st
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles)
          /\ u' = u.
    Proof.
      intros pairs x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u'
        Hckx Hckx' Hckty Hb Hb' H0 H1 HLs Hbs Hpair Hsrc Htgt.
      pose proof (assign_lexp_Efby_pair e0 e ann s0 s1 st H0 H1) as Hfby.
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b st
                 Hckx Hckty Hfby Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      apply generate_leqns_cons_inv in Htgt
        as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Evar x' ann) ck ckty ([b'] : ST) b st Hckx Hckty
                 (assign_lexp_Evar_type x' ann b' st Hb') Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      apply generate_leqns_cons_inv in Hc2
        as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
      rewrite generate_leqn_constraint_def in Hd1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x'
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b' st
                 Hckx' Hckty Hfby Hb') in Hd1.
      apply OK_pair_inv in Hd1 as (? & ?); subst d1 w1.
      apply generate_leqns_constraints_nil in Hd2 as (? & ?); subst d2 u'.
      subst c2 cet. rewrite app_nil_r.
      set (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      exists [Bounds b L; Defines b']. split.
      - constructor.
        + cbn [role_shape fst snd]. repeat split.
          * exact Hbs.
          * exact HLs.
          * intros z Hz. apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
            -- left. unfold L. apply in_merge_left. exact Hz.
            -- right. exists L. split; [|intros w Hw; exact Hw].
               destruct Hz as [Hz|[]]. subst z. exact Hpair.
        + constructor.
          * cbn [role_shape fst snd]. split; [reflexivity|].
            exists L. split; [exact Hpair|intros z Hz; exact Hz].
          * constructor.
      - split.
        + intros dlt Hsat.
          assert (Hc0 : hm_ext dlt L ⊑ hm_ext dlt [b]).
          { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
            exact (Hsat _ (in_eq _ _)). }
          constructor; [exact Hc0|constructor; [exact I|constructor]].
        + reflexivity.
    Qed.

    Lemma arrow_roles :
      forall pairs x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs,
        find_clock cenv x = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x env = Some b ->
        Env.find i env = Some bi ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        (** the flag's entry is its clock's ambient -- the same whichever
            equation created it, which is what makes sharing harmless *)
        In (bi, merge [rst_ty] ckty) pairs ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name))]) :: eqs) st = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles)
          /\ u' = u.
    Proof.
      intros pairs x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs
        Hckx Hckty Hb Hbi H0 H1 HLs Hbs Hpair Heqs Hsrc Htgt.
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Earrow [e0] [e] [(ty, (ck, name))]) ck ckty
                 (merge s0 s1) b st Hckx Hckty
                 (assign_lexp_Earrow_pair e0 e (ty, (ck, name)) s0 s1 st H0 H1)
                 Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      apply generate_leqns_cons_inv in Htgt
        as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name)))
                 ck ckty (merge (merge [bi] s0) s1) b st Hckx Hckty
                 (assign_lexp_Eite_var i (bool_type, (ck, Some i)) e0 e
                    ([ty], (ck, name)) bi s0 s1 st Hbi H0 H1) Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      assert (Hinit :
                (c2 = [] /\ u' = st)
                \/ exists sw, c2 = [(merge (merge [rst_ty] ckty) sw, [bi])]
                              /\ (forall z, In z sw -> In z ckty)
                              /\ u' = st).
      { destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
        - apply generate_leqns_constraints_nil in Hc2
            as (Hnil & Hstate); subst c2.
          left. split; [reflexivity|exact Hstate].
        - apply generate_leqns_cons_inv in Hc2
            as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
          destruct (init_eq_constraint i ck ckty bi st d1 w1
                      Hcki Hckty Hbi Hd1) as (sw & Hd1' & Hsw & Hw1).
          subst d1 w1.
          apply generate_leqns_constraints_nil in Hd2
            as (Hnil & Hstate); subst d2.
          right. exists sw. repeat split.
          + rewrite Hc2e, app_nil_r. reflexivity.
          + exact Hsw.
          + exact Hstate. }
      subst cet.
      set (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      set (Li := merge [rst_ty] ckty).
      destruct Hinit as [(Hnil & Hu')|(sw & Hswc & Hsw & Hu')];
        subst c2 u'.
      - rewrite app_nil_r. exists [Bounds b L]. split.
        + constructor; [|constructor].
          cbn [role_shape fst snd]. repeat split.
          * exact Hbs.
          * exact HLs.
          * intros z Hz.
            assert (Hz' : In z L \/ In z [bi]).
            { unfold L. apply (ite_lhs_members ckty s0 s1 [bi] z).
              - intros y Hy. right.
                apply in_merge_right, in_merge_right. exact Hy.
              - exact Hz. }
            destruct Hz' as [HzL|Hzbi]; [left; exact HzL|].
            right. exists Li. split; [|].
            -- destruct Hzbi as [Hzbi|[]]. subst z. exact Hpair.
            -- intros w Hw. unfold Li in Hw. unfold L.
               apply in_merge_left. exact Hw.
        + split.
          * intros dlt Hsat.
            assert (Hc0 : hm_ext dlt L ⊑ hm_ext dlt [b]).
            { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
              exact (Hsat _ (in_eq _ _)). }
            constructor; [exact Hc0|constructor].
          * reflexivity.
      - exists [Bounds b L; Defines bi]. split.
        + constructor.
          * cbn [role_shape fst snd]. repeat split.
            -- exact Hbs.
            -- exact HLs.
            -- intros z Hz.
               assert (Hz' : In z L \/ In z [bi]).
               { unfold L. apply (ite_lhs_members ckty s0 s1 [bi] z).
                 - intros y Hy. right.
                   apply in_merge_right, in_merge_right. exact Hy.
                 - exact Hz. }
               destruct Hz' as [HzL|Hzbi]; [left; exact HzL|].
               right. exists Li. split; [|].
               ++ destruct Hzbi as [Hzbi|[]]. subst z. exact Hpair.
               ++ intros w Hw. unfold Li in Hw. unfold L.
                  apply in_merge_left. exact Hw.
          * constructor.
            -- cbn [role_shape fst snd]. split; [reflexivity|].
               exists Li. split; [exact Hpair|].
               intros z Hz. apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
               ++ exact Hz.
               ++ unfold Li. apply in_merge_right. exact (Hsw z Hz).
            -- constructor.
        + split.
          * intros dlt Hsat.
            assert (Hc0 : hm_ext dlt L ⊑ hm_ext dlt [b]).
            { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
              exact (Hsat _ (in_eq _ _)). }
            constructor; [exact Hc0|constructor; [exact I|constructor]].
          * reflexivity.
    Qed.

    Lemma fby_ite_roles :
      forall pairs x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs,
        find_clock cenv x  = OK ck ->
        find_clock cenv px = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find i  env = Some bi ->
        Env.find px env = Some bp ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        In (bi, merge [rst_ty] ckty) pairs ->
        (** [px] carries the ambient joined with the *delayed* operand's type:
            enough for its own equation, and inside the ambient of the [ite]
            that uses it -- the latter only because the source [fby] rule types
            both operands *)
        In (bp, merge (merge [rst_ty] ckty) s1) pairs ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
           :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                        [(ty, (ck, name))]])
           :: eqs) st = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles)
          /\ u' = u.
    Proof.
      intros pairs x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs
        Hckx Hckpx Hckty Hb Hbi Hbp H0 H1 HLs Hbs Hpairi Hpairp Heqs
        Hsrc Htgt.
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Efby [e0] [e] [(ty, (ck, name))]) ck ckty
                 (merge s0 s1) b st Hckx Hckty
                 (assign_lexp_Efby_pair e0 e (ty, (ck, name)) s0 s1 st H0 H1)
                 Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      apply generate_leqns_cons_inv in Htgt
        as (c1 & v1 & c2 & Hc1 & Hc2 & Hcet).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name)))
                 ck ckty (merge (merge [bi] s0) [bp]) b st Hckx Hckty
                 (assign_lexp_Eite_var i (bool_type, (ck, Some i)) e0
                    (Evar px (ty, (ck, Some px))) ([ty], (ck, name)) bi s0
                    ([bp] : ST) st Hbi H0
                    (assign_lexp_Evar_type px (ty, (ck, Some px)) bp st Hbp))
                 Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      apply generate_leqns_cons_inv in Hc2
        as (d1 & w1 & d2 & Hd1 & Hd2 & Hc2e).
      destruct (add_whens_const_type (init_type ty) ty ck ckty st Hckty)
        as (sw & Hw & Hsw).
      rewrite generate_leqn_constraint_def in Hd1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv px
                 (Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                    [(ty, (ck, name))])
                 ck ckty (merge sw s1) bp st Hckpx Hckty
                 (assign_lexp_Efby_pair
                    (add_whens (Econst (init_type ty)) ty ck) e
                    (ty, (ck, name)) sw s1 st Hw H1) Hbp) in Hd1.
      apply OK_pair_inv in Hd1 as (? & ?); subst d1 w1.
      assert (Hinit :
                (d2 = [] /\ u' = st)
                \/ exists swi, d2 = [(merge (merge [rst_ty] ckty) swi, [bi])]
                               /\ (forall z, In z swi -> In z ckty)
                               /\ u' = st).
      { destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
        - apply generate_leqns_constraints_nil in Hd2
            as (Hnil & Hstate); subst d2.
          left. split; [reflexivity|exact Hstate].
        - apply generate_leqns_cons_inv in Hd2
            as (f1 & y1 & f2 & Hf1 & Hf2 & Hd2e).
          destruct (init_eq_constraint i ck ckty bi st f1 y1
                      Hcki Hckty Hbi Hf1) as (swi & Hf1' & Hswi & Hy1).
          subst f1 y1.
          apply generate_leqns_constraints_nil in Hf2
            as (Hnil & Hstate); subst f2.
          right. exists swi. repeat split.
          + rewrite Hd2e, app_nil_r. reflexivity.
          + exact Hswi.
          + exact Hstate. }
      subst c2 cet.
      set (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      set (Li := merge [rst_ty] ckty).
      set (Lp := merge (merge [rst_ty] ckty) s1).
      assert (Hite_shape :
          role_shape pairs
            (merge (merge [rst_ty] ckty) (merge (merge [bi] s0) [bp]), [b])
            (Bounds b L)).
      { cbn [role_shape fst snd]. repeat split.
        - exact Hbs.
        - exact HLs.
        - intros z Hz. apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
          + left. unfold L. apply in_merge_left. exact Hz.
          + apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
            * apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
              -- destruct Hz as [Hz|[]]. subst z. right. exists Li.
                 split; [exact Hpairi|]. intros w Hwin. unfold Li in Hwin.
                 unfold L. apply in_merge_left. exact Hwin.
              -- left. unfold L. apply in_merge_right, in_merge_left. exact Hz.
            * destruct Hz as [Hz|[]]. subst z. right. exists Lp.
              split; [exact Hpairp|]. intros w Hwin. unfold Lp in Hwin.
              apply SymTypes.in_merge_inv in Hwin as [Hwin|Hwin].
              -- unfold L. apply in_merge_left. exact Hwin.
              -- unfold L. apply in_merge_right, in_merge_right. exact Hwin. }
      assert (Hpx_shape :
          role_shape pairs
            (merge (merge [rst_ty] ckty) (merge sw s1), [bp])
            (Defines bp)).
      { cbn [role_shape fst snd]. split; [reflexivity|].
        exists Lp. split; [exact Hpairp|]. intros z Hz.
        apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
        - unfold Lp. apply in_merge_left. exact Hz.
        - apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
          + unfold Lp. apply in_merge_left, in_merge_right. exact (Hsw z Hz).
          + unfold Lp. apply in_merge_right. exact Hz. }
      destruct Hinit as [(Hnil & Hu')|(swi & Hswic & Hswi & Hu')];
        subst d2 u'.
      - rewrite !app_nil_r. exists [Bounds b L; Defines bp]. split.
        + constructor; [exact Hite_shape|constructor; [exact Hpx_shape|constructor]].
        + split.
          * intros dlt Hsat.
            assert (Hc0 : hm_ext dlt L ⊑ hm_ext dlt [b]).
            { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
              exact (Hsat _ (in_eq _ _)). }
            constructor; [exact Hc0|constructor; [exact I|constructor]].
          * reflexivity.
      - exists [Bounds b L; Defines bp; Defines bi]. split.
        + constructor; [exact Hite_shape|]. constructor; [exact Hpx_shape|].
          constructor.
          * cbn [role_shape fst snd]. split; [reflexivity|].
            exists Li. split; [exact Hpairi|]. intros z Hz.
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
            -- exact Hz.
            -- unfold Li. apply in_merge_right. exact (Hswi z Hz).
          * constructor.
        + split.
          * intros dlt Hsat.
            assert (Hc0 : hm_ext dlt L ⊑ hm_ext dlt [b]).
            { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
              exact (Hsat _ (in_eq _ _)). }
            constructor; [exact Hc0|]. constructor; [exact I|].
            constructor; [exact I|constructor].
          * reflexivity.
    Qed.

    (** ** One equation, whatever shape it has

        The dispatch, as [fby_equation_entails] already does it: split with
        [fby_equation_spec], read the created variables off the fresh state with
        [fby_iteexp_created] / [arrow_iteexp_created], and quote the case
        lemma.  On the two shapes the pass leaves alone the two runs are the
        same run, and every constraint takes a [Bounds] role with [M] its own
        left-hand side. *)
    Theorem fby_equation_roles :
      forall pairs to_cut xs es eqs' st st' ce cet s u u',
        fby_equation to_cut (xs, es) st = (eqs', st') ->
        (** what the node says about this equation, and the entry its [px]
            needs; vacuous on the shapes that create nothing *)
        (forall x e0 e ty ck name,
            xs = [x] ->
            (es = [Efby [e0] [e] [(ty, (ck, name))]]
             \/ es = [Earrow [e0] [e] [(ty, (ck, name))]]) ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ assign_lexp_type G env base_ty rst_ty e0 s = OK ([(s0, [])], s)
              /\ assign_lexp_type G env base_ty rst_ty e  s = OK ([(s1, [])], s)
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)
              /\ (es = [Efby [e0] [e] [(ty, (ck, name))]] ->
                    fby_created_pairs pairs eqs' x e0 e ty ck name
                      ckty s0 s1)) ->
        (** and about every flag: its clock, its name, and its entry *)
        (forall y a, In (y, a) (st_anns st') ->
            find_clock cenv y = OK (snd (fst a))
            /\ exists c, Env.find y env = Some c /\ ~ In c scope) ->
        (forall i cki ckti bi,
            In (i, ((bool_type, cki), true)) (st_anns st') ->
            assign_clk_type env base_ty cki = Some ckti ->
            Env.find i env = Some bi ->
            In (bi, merge [rst_ty] ckti) pairs) ->
        (** the source's own constraints are visible, for the unchanged shapes *)
        constraints_scoped scope ce ->
        generate_leqn_constraint G env base_ty rst_ty cenv (xs, es) s
          = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv eqs' s
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles)
          /\ u' = u.
    Proof.
      intros pairs to_cut xs es eqs' st st' ce cet s u u'
        Hrun Hdata Hnew Hflags Hcesc Hsrc Htgt.
      assert (Hsame : eqs' = [(xs, es)] ->
          exists roles,
            Forall2 (role_shape pairs) cet roles
            /\ (forall dlt, listSatisfiable dlt ce ->
                  Forall2 (role_bound dlt) cet roles)
            /\ u' = u).
      { intro He. subst eqs'.
        apply generate_leqns_cons_inv in Htgt
          as (c1 & v1 & c2 & Hc1 & Hc2 & Hce).
        rewrite Hsrc in Hc1. apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
        apply generate_leqns_constraints_nil in Hc2 as (? & ?); subst c2 u'.
        subst cet. rewrite app_nil_r.
        clear Hsrc.
        exists (List.map (fun _ => Keeps) ce). split.
        - induction Hcesc as [|c ce Hc Hcs IH]; simpl.
          + constructor.
          + constructor; [exact Hc|exact IH].
        - split.
          + clear Hcesc. intros dlt Hsat. unfold listSatisfiable in Hsat.
            induction Hsat as [|c ce Hc Hcs IH]; simpl.
            * constructor.
            * constructor; [exact Hc|exact IH].
          + reflexivity. }
      destruct (fby_equation_spec to_cut xs es)
        as [(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
           |[(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
            |[(x & e0 & e & ann & Hxs & Hes & Heq)
             |Heq]]].
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun. cbv beta iota in Hrun.
        destruct (PS.mem x to_cut) eqn:Hmem.
        + apply bind_spec in Hrun as (x' & s2 & Ex & Hrun).
          rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
          destruct (Hdata x e0 e ty ck name
                      (@Coq.Init.Logic.eq_refl _ [x])
                      (or_introl (@Coq.Init.Logic.eq_refl _
                        [Efby [e0] [e] [(ty, (ck, name))]])))
            as (ckty & s0 & s1 & b & Hckx & Hckty & Hb & Hbs & H0 & H1
                & HL & Hcreated).
          pose proof (fresh_ident_In norm2 ((ty, ck), false) x' st s2 Ex)
            as Hx'in.
          destruct (Hnew x' ((ty, ck), false) Hx'in)
            as (Hckx' & b' & Hb' & Hfresh).
          cbn [fst snd] in Hckx'.
          apply (fby_cut_roles pairs x x' e0 e (ty, (ck, name)) ck ckty
                   s0 s1 b b' s ce cet u u').
          * exact Hckx.
          * exact Hckx'.
          * exact Hckty.
          * exact Hb.
          * exact Hb'.
          * exact H0.
          * exact H1.
          * exact HL.
          * exact Hbs.
          * destruct (Hcreated (@Coq.Init.Logic.eq_refl _
                         [Efby [e0] [e] [(ty, (ck, name))]]))
              as (Hcut & Hpxdata).
            eapply Hcut; [reflexivity|exact Hb'].
          * exact Hsrc.
          * exact Htgt.
        + rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
          apply Hsame. reflexivity.
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun.
        apply bind2_spec in Hrun as (fby & eqsa & s2 & Hfby & Hrun).
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
        destruct (fby_iteexp_created e0 e ty ck name fby eqsa st s2 Hfby)
          as (i & px & eqsi & Hi & Hpx & Hfbye & Heqsa & Heqsi).
        destruct (Hdata x e0 e ty ck name
                    (@Coq.Init.Logic.eq_refl _ [x])
                    (or_introl (@Coq.Init.Logic.eq_refl _
                      [Efby [e0] [e] [(ty, (ck, name))]])))
          as (ckty & s0 & s1 & b & Hckx & Hckty & Hb & Hbs & H0 & H1
              & HL & Hcreated).
        destruct (Hnew i ((bool_type, ck), true) Hi)
          as (Hcki & bi & Hbi & Hfreshi).
        destruct (Hnew px ((ty, ck), false) Hpx)
          as (Hckpx & bp & Hbp & Hfreshp).
        cbn [fst snd] in Hcki, Hckpx.
        subst fby eqsa.
        destruct (Hcreated (@Coq.Init.Logic.eq_refl _
                       [Efby [e0] [e] [(ty, (ck, name))]]))
          as (Hcutdata & Hpxdata).
        apply (fby_ite_roles pairs x i px e0 e ty ck name ckty s0 s1 b bi bp
                 s ce cet u u' eqsi).
        + exact Hckx.
        + exact Hckpx.
        + exact Hckty.
        + exact Hb.
        + exact Hbi.
        + exact Hbp.
        + exact H0.
        + exact H1.
        + exact HL.
        + exact Hbs.
        + exact (Hflags i ck ckty bi Hi Hckty Hbi).
        + eapply Hpxdata; [reflexivity|exact Hbp].
        + destruct Heqsi as [Heqsi|Heqsi].
          * left. exact Heqsi.
          * right. split; [exact Hcki|exact Heqsi].
        + exact Hsrc.
        + exact Htgt.
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in Hrun.
        apply bind2_spec in Hrun as (ite & eqsa & s2 & Hite & Hrun).
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
        destruct (arrow_iteexp_created e0 e ty ck name ite eqsa st s2 Hite)
          as (i & Hi & Hite' & Heqsi).
        destruct (Hdata x e0 e ty ck name
                    (@Coq.Init.Logic.eq_refl _ [x])
                    (or_intror (@Coq.Init.Logic.eq_refl _
                      [Earrow [e0] [e] [(ty, (ck, name))]])))
          as (ckty & s0 & s1 & b & Hckx & Hckty & Hb & Hbs & H0 & H1
              & HL & Hcreated).
        destruct (Hnew i ((bool_type, ck), true) Hi)
          as (Hcki & bi & Hbi & Hfreshi).
        cbn [fst snd] in Hcki.
        subst ite.
        apply (arrow_roles pairs x i e0 e ty ck name ckty s0 s1 b bi
                 s ce cet u u' eqsa).
        + exact Hckx.
        + exact Hckty.
        + exact Hb.
        + exact Hbi.
        + exact H0.
        + exact H1.
        + exact HL.
        + exact Hbs.
        + exact (Hflags i ck ckty bi Hi Hckty Hbi).
        + destruct Heqsi as [Heqsi|Heqsi].
          * left. exact Heqsi.
          * right. split; [exact Hcki|exact Heqsi].
        + exact Hsrc.
        + exact Htgt.
      - rewrite Heq in Hrun. rewrite ret_spec in Hrun.
        inversion Hrun; subst eqs' st'.
        apply Hsame. reflexivity.
    Qed.

    (** ** A node's equation list

        The per-equation data is a [Forall2] against the run's OWN output, one
        chunk per equation.  That is what pins each created variable to the
        equation that created it -- keyed instead on a description of the
        equation (its annotation, or its run at an arbitrary state) the premise
        demands this equation's level for another equation's variable, and is
        then unsatisfiable; see work_docs/LegI_audit_2026_09_29.v.

        With that, the induction needs no disjointness bookkeeping at all: the
        two [Forall2]s compose with [Forall2_app] and the source's satisfaction
        splits with [Forall_app].  The operand types are given at *any* state,
        which [assign_lexp_normalized_pure] supplies for normalized operands,
        so the induction never has to track them; [map_bind_st_follows] weakens
        the [st_anns st'] premises from the whole run to each step. *)

    Definition fby_eqn_data (pairs : list (ident * ST))
      (eq : equation) (eqk : list equation) : Prop :=
      forall x e0 e ty ck name,
        eq = ([x], [Efby [e0] [e] [(ty, (ck, name))]])
        \/ eq = ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) ->
        exists ckty s0 s1 b,
          find_clock cenv x = OK ck
          /\ assign_clk_type env base_ty ck = Some ckty
          /\ Env.find x env = Some b
          /\ In b scope
          /\ (forall q, assign_lexp_type G env base_ty rst_ty e0 q
                        = OK ([(s0, [])], q))
          /\ (forall q, assign_lexp_type G env base_ty rst_ty e q
                        = OK ([(s1, [])], q))
          /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                        In z scope)
          /\ (eq = ([x], [Efby [e0] [e] [(ty, (ck, name))]]) ->
                fby_created_pairs pairs eqk x e0 e ty ck name ckty s0 s1).

    Theorem fby_equations_roles :
      forall pairs to_cut eqs eqs' st st' ce cet s u u',
        map_bind (fby_equation to_cut) eqs st = (eqs', st') ->
        Forall2 (fby_eqn_data pairs) eqs eqs' ->
        (forall y a, In (y, a) (st_anns st') ->
            find_clock cenv y = OK (snd (fst a))
            /\ exists c, Env.find y env = Some c /\ ~ In c scope) ->
        (forall i cki ckti bi,
            In (i, ((bool_type, cki), true)) (st_anns st') ->
            assign_clk_type env base_ty cki = Some ckti ->
            Env.find i env = Some bi ->
            In (bi, merge [rst_ty] ckti) pairs) ->
        constraints_scoped scope ce ->
        generate_leqns_constraints G env base_ty rst_ty cenv eqs s = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv (List.concat eqs') s
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Proof.
      intros pairs to_cut eqs.
      induction eqs as [|[xs es] eqs IH];
        intros eqs' st st' ce cet s u u' Hrun Hdata Hnew Hflags
          Hscoped Hsrc Htgt.
      - change (ret [] st = (eqs', st')) in Hrun.
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' st'.
        apply generate_leqns_constraints_nil in Hsrc as (? & ?); subst ce u.
        cbn [List.concat] in Htgt.
        apply generate_leqns_constraints_nil in Htgt as (? & ?); subst cet u'.
        exists []. split; [constructor|].
        intros dlt Hsat. constructor.
      - change
          (bind (fby_equation to_cut (xs, es))
             (fun eq1 =>
                bind (map_bind (fby_equation to_cut) eqs)
                  (fun eqsr => ret (eq1 :: eqsr))) st = (eqs', st'))
          in Hrun.
        apply bind_spec in Hrun as (eq1 & fst1 & Hrun1 & Hrun).
        apply bind_spec in Hrun as (eqsr & fst2 & Hrunr & Hret).
        rewrite ret_spec in Hret. inversion Hret; subst eqs' st'.
        (** the data splits with the run *)
        inversion Hdata as [|eqh eqkh eqt eqkt Hd1 Hdr]; subst.
        apply generate_leqns_cons_inv in Hsrc
          as (ce1 & sv1 & ce2 & Hsrc1 & Hsrc2 & Hce).
        subst ce.
        cbn [List.concat] in Htgt.
        apply generate_leqns_constraints_app in Htgt
          as (cet1 & cet2 & tv1 & Htgt1 & Htgt2 & Hcet).
        subst cet.
        apply Forall_app in Hscoped as (Hsc1 & Hsc2).
        assert (Hfollow : st_follows fst1 fst2).
        { apply (@map_bind_st_follows equation (list equation)
                   (type * clock * bool) (fby_equation to_cut)
                   eqs eqsr fst1 fst2 Hrunr).
          rewrite Forall_forall. intros eq Hin out q q' Hq.
          exact (fby_equation_st_follows to_cut eq out q q' Hq). }
        destruct (fby_equation_roles pairs to_cut xs es eq1 st fst1
                    ce1 cet1 s sv1 tv1 Hrun1)
          as (roles1 & Hroles1 & Hbounds1 & Hstate1).
        + intros x e0 e ty ck name Hxs Hshape.
          assert (Hshape' :
              (xs, es) = ([x], [Efby [e0] [e] [(ty, (ck, name))]])
              \/ (xs, es) = ([x], [Earrow [e0] [e] [(ty, (ck, name))]])).
          { destruct Hshape as [Hfby|Harrow];
              [left|right]; rewrite Hxs; [rewrite Hfby|rewrite Harrow];
              reflexivity. }
          destruct (Hd1 x e0 e ty ck name Hshape')
            as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs
                & H0 & H1 & HL & Hcreated).
          exists ckty, s0, s1, b.
          split; [exact Hck|].
          split; [exact Hckty|].
          split; [exact Hb|].
          split; [exact Hbs|].
          split; [exact (H0 s)|].
          split; [exact (H1 s)|].
          split; [exact HL|].
          intro Hes. apply Hcreated.
          rewrite Hxs, Hes. reflexivity.
        + intros y a Hy.
          apply Hnew.
          exact (st_follows_incl fst1 fst2 Hfollow (y, a) Hy).
        + intros i cki ckti bi Hi Hckti Hbi.
          apply (Hflags i cki ckti bi).
          * exact (st_follows_incl fst1 fst2 Hfollow
                     (i, ((bool_type, cki), true)) Hi).
          * exact Hckti.
          * exact Hbi.
        + exact Hsc1.
        + exact Hsrc1.
        + exact Htgt1.
        + subst tv1.
          destruct (IH eqsr fst1 fst2 ce2 cet2 sv1 u u' Hrunr Hdr
                      Hnew Hflags Hsc2 Hsrc2 Htgt2)
            as (roles2 & Hroles2 & Hbounds2).
          exists (roles1 ++ roles2). split.
          * apply Forall2_app; [exact Hroles1|exact Hroles2].
          * intros dlt Hsat. unfold listSatisfiable in Hsat.
            apply Forall_app in Hsat as (Hsat1 & Hsat2).
            apply Forall2_app.
            -- exact (Hbounds1 dlt Hsat1).
            -- exact (Hbounds2 dlt Hsat2).
    Qed.

    (** ** The equation-level entailment, for a node

        [fby_equations_roles] followed by [preserves_on_created], with
        [normfby_node_fields] to identify the target equation list with
        [concat eqs'] and [generate_leqns_normfby_node_cenv] to read the source
        equations against the target's clock environment. *)
    Corollary normfby_node_entailment :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             pairs st0 ce cet ct1 ct1',
        cenv = lnode_clock_env (normfby_node Q c n Hunt Hpref) ->
        levels_functional pairs ->
        created_hidden pairs ->
        levels_visible pairs ->
        (** the per-equation and per-created-variable data, for this node's run.
            The data is paired with the run's own output, which is what ties each
            created variable to the equation that created it; [map_bind] is
            deterministic, so quantifying over the run names the actual one. *)
        (forall eqs' stf,
            map_bind (fby_equation
                        (PS.union c (ps_from_list (List.map fst (n_out n)))))
              n.(n_eqs) init_st = (eqs', stf) ->
            Forall2 (fby_eqn_data pairs) n.(n_eqs) eqs'
            /\ (forall y a, In (y, a) (st_anns stf) ->
                   find_clock cenv y = OK (snd (fst a))
                   /\ exists d, Env.find y env = Some d /\ ~ In d scope)
            /\ (forall i cki ckti bi,
                   In (i, ((bool_type, cki), true)) (st_anns stf) ->
                   assign_clk_type env base_ty cki = Some ckti ->
                   Env.find i env = Some bi ->
                   In (bi, merge [rst_ty] ckti) pairs)) ->
        constraints_scoped scope ce ->
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env n) n.(n_eqs) st0 = OK (ce, ct1) ->
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env (normfby_node Q c n Hunt Hpref))
          (normfby_node Q c n Hunt Hpref).(n_eqs) st0 = OK (cet, ct1') ->
        preserves_on scope ce cet.
    Proof.
      intros Q c n Hunt Hpref pairs st0 ce cet ct1 ct1' Hcenv Hnd Hhidden
        Hvisible Hdata Hscoped Hsrc Htgt.
      remember (map_bind
                  (fby_equation
                    (PS.union c (ps_from_list (List.map fst (n_out n)))))
                  n.(n_eqs) init_st) as run eqn:Hrun.
      destruct run as [eqs' stf].
      assert (Hrun' :
          map_bind
            (fby_equation
              (PS.union c (ps_from_list (List.map fst (n_out n)))))
            n.(n_eqs) init_st = (eqs', stf)).
      { symmetry. exact Hrun. }
      assert (Heqs :
          (normfby_node Q c n Hunt Hpref).(n_eqs) = List.concat eqs').
      { destruct (normfby_node_fields Q c n Hunt Hpref)
          as (He & _ & _ & _ & _).
        rewrite He.
        assert (Hfbys :
            fby_equations
              (PS.union c (ps_from_list (List.map fst (n_out n))))
              n.(n_eqs) init_st = (List.concat eqs', stf)).
        { unfold fby_equations. apply bind_spec.
          exists eqs', stf. split; [exact Hrun'|apply ret_spec]. }
        rewrite Hfbys. reflexivity. }
      assert (Hsrc' :
          generate_leqns_constraints G env base_ty rst_ty cenv n.(n_eqs) st0
            = OK (ce, ct1)).
      { rewrite Hcenv.
        rewrite (generate_leqns_normfby_node_cenv Q c n Hunt Hpref G st0).
        exact Hsrc. }
      assert (Htgt' :
          generate_leqns_constraints G env base_ty rst_ty cenv
            (List.concat eqs') st0 = OK (cet, ct1')).
      { rewrite Hcenv, <- Heqs. exact Htgt. }
      destruct (Hdata eqs' stf
                  (@Coq.Init.Logic.eq_refl _ (eqs', stf)))
        as (Heqdata & Hnew & Hflags).
      destruct (fby_equations_roles pairs
                  (PS.union c (ps_from_list (List.map fst (n_out n))))
                  n.(n_eqs) eqs' init_st stf ce cet st0 ct1 ct1'
                  Hrun' Heqdata Hnew Hflags Hscoped Hsrc' Htgt')
        as (roles & Hroles & Hbounds).
      exact (proj1
        (preserves_on_created pairs roles ce cet Hnd Hhidden Hvisible
           Hroles Hbounds)).
    Qed.

    (** ** Signature preservation for one node, two accumulators, two states

        A near-copy of Leg U's [unnest_node_signatures_preserved_decoupled]:
        [normfby_node_sig_interface] for the five interface fields,
        [generate_leqns_constraints_weaken] for the intermediate run against the
        target accumulator, [state_pure_generate_leqns] to restart the target
        run at the source's state, and [preserves_on_simplify] through both
        eliminations. *)
    Theorem normfby_node_signatures_preserved_decoupled :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (Q' : global) (G1 G2 : secglobal) (aux : list node_aux_names)
             (lo : sec_state) stS stT sg stS1 sg' stT1,
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        (** the pass's output is unnested, which is what makes it state-pure *)
        Forall (unnested_equation Q')
          (normfby_node Q c n Hunt Hpref).(n_eqs) ->
        call_weakens G1 G2 ->
        eapp_fresh_prop G1 env base_ty rst_ty lo ->
        lcall_fresh_prop G1 env base_ty rst_ty lo ->
        sec_le lo stS ->
        (forall ce cet ct1 ct1',
            generate_leqns_constraints G2 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (ce, ct1) ->
            generate_leqns_constraints G2 env base_ty rst_ty
              (lnode_clock_env (normfby_node Q c n Hunt Hpref))
              (normfby_node Q c n Hunt Hpref).(n_eqs) stS = OK (cet, ct1') ->
            preserves_on scope ce cet) ->
        (forall ce ct1,
            generate_leqns_constraints G1 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (ce, ct1) ->
            Forall (fun c => List.length (snd c) = 1%nat) ce) ->
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints G1 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (cns, ct1) ->
            forall x, In x (locals ++ minted stS ct1) -> ~ In x scope) ->
        generate_lnode_sig G1 n env aux stS = OK (sg, stS1) ->
        generate_lnode_sig G2 (normfby_node Q c n Hunt Hpref) env aux stT
          = OK (sg', stT1) ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg
        /\ preserves_on scope sg.(s_constraints) sg'.(s_constraints).
    Proof.
      intros Q c n Hunt Hpref Q' G1 G2 aux lo stS stT sg stS1 sg' stT1
        Haux Hun Hweak Hef Hlf Hlo Hpres Hwf Hdisj HgenS HgenT.
      assert (Hiface :
          s_name sg' = s_name sg
          /\ s_in sg' = s_in sg
          /\ s_out sg' = s_out sg
          /\ s_clk sg' = s_clk sg
          /\ s_reset sg' = s_reset sg).
      { exact (normfby_node_sig_interface Q c n Hunt Hpref G1 G2 aux
                 stS stT sg stS1 sg' stT1 HgenS HgenT). }
      destruct Hiface as (Hn & Hi & Ho & Hc & Hr).
      repeat split; try assumption.
      apply (lnode_sig_inv env) in HgenS
        as (c1 & r1 & ct1 & rt1 & i1 & o1 & l1 & cs1
            & Ha1 & Hc1 & Hr1 & _ & _ & Hl1 & Hcs1 & ?); subst sg.
      apply (lnode_sig_inv env) in HgenT
        as (c2 & r2 & ct2 & rt2 & i2 & o2 & l2 & cs2
            & Ha2 & Hc2 & Hr2 & _ & _ & Hl2 & Hcs2 & ?); subst sg'.
      destruct (Haux c1 r1 Ha1) as (Hb1 & Hbr1).
      rewrite Hc1 in Hb1. apply option_Some_inj in Hb1; subst ct1.
      rewrite Hr1 in Hbr1. apply option_Some_inj in Hbr1; subst rt1.
      cbn [n_name normfby_node] in Ha2.
      destruct (Haux c2 r2 Ha2) as (Hb2 & Hbr2).
      rewrite Hc2 in Hb2. apply option_Some_inj in Hb2; subst ct2.
      rewrite Hr2 in Hbr2. apply option_Some_inj in Hbr2; subst rt2.
      cbn [s_constraints].
      destruct (state_pure_generate_leqns G2 env base_ty rst_ty
                  (lnode_clock_env (normfby_node Q c n Hunt Hpref)) Q'
                  (normfby_node Q c n Hunt Hpref).(n_eqs) Hun
                  stT stS cs2 stT1 Hcs2) as (_ & Hcs2s).
      destruct (generate_leqns_constraints_weaken G1 G2 env base_ty rst_ty
                  (lnode_clock_env n) n.(n_eqs) cs1 stS stS1 lo Hweak Hef Hlf
                  (NoDup_vars_defined_n_eqs n) Hlo Hcs1)
        as (cs1' & Hcs1' & Hentails).
      apply (preserves_on_simplify scope (collapse cs1) (collapse cs2)
               (l1 ++ minted stS stS1) (l2 ++ minted stT stT1)).
      - apply collapse_wf. exact (Hwf cs1 stS1 Hcs1).
      - exact (Hdisj l1 cs1 stS1 Hl1 Hcs1).
      - apply preserves_on_collapse2.
        apply (preserves_on_trans scope cs1 cs1' cs2).
        + apply (preserves_on_from_entailment scope cs1 cs1').
          exact Hentails.
        + exact (Hpres cs1' cs2 stS1 stS Hcs1' Hcs2s).
    Qed.

    (** ** The per-node step the shared lockstep consumes

        [sig_call_weakens_from_good] turns the interface equality and the
        entailment into [sig_call_weakens].  The goodness and scopedness of the
        two *published* signatures are the Lustre analogue of what
        [SecNLusTypingCorrectness.v] proves for NLustre; they live after
        [SecLusUnnesting.v] in the build order, so they enter here as
        hypotheses, exactly as Leg A's [node_step_entails] leaves its own. *)
    Corollary normfby_node_step_weakens :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (envs : node_scoped_env) (aux : list node_aux_names)
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        find_node_env n.(n_name) envs = Some env ->
        call_weakens accS accT ->
        (** what this node's two runs give, from the theorem above *)
        (s_name sgT = s_name sgS
         /\ s_in sgT = s_in sgS
         /\ s_out sgT = s_out sgS
         /\ s_clk sgT = s_clk sgS
         /\ s_reset sgT = s_reset sgS
         /\ preserves_on scope sgS.(s_constraints) sgT.(s_constraints)) ->
        (** and what the program level knows about the published pair *)
        signature_good sgS ->
        NoDup (signature_scope sgS) ->
        signature_good sgT ->
        signature_scoped sgT ->
        (forall z, In z (signature_scope sgS) -> In z scope) ->
        generate_lnode_sig_scoped_env accS n envs aux stS0 = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT (normfby_node Q c n Hunt Hpref)
          envs aux stT0 = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
    Proof.
      intros Q c n Hunt Hpref envs aux accS accT sgS stS0 stS1 sgT stT0 stT1
        Henv Hacc Hfields HgoodS HndS HgoodT HscT Hscope HrunS HrunT.
      clear Henv Hacc HrunS HrunT.
      destruct Hfields as
        (Hname & Hin & Hout & Hclk & Hreset & Hpres).
      assert (Hsp : SIGPROOFS.signatures_preserved sgS sgT).
      { split.
        - repeat split; symmetry; assumption.
        - intros dlt Hsat.
          destruct (Hpres dlt Hsat) as (dlt' & Hagree & Hsat').
          exists dlt'. split; [|exact Hsat'].
          intros z Hz. apply Hagree. exact (Hscope z Hz). }
      split; [symmetry; exact Hname|].
      split; [exact Hsp|].
      exact (sig_call_weakens_from_good sgS sgT HgoodS HndS HgoodT HscT Hsp).
    Qed.

    (** ** The whole program

        This one should follow directly, with nothing new:
        [generate_all_lsignatures_weakens] instantiated at
        [R := fun n m => exists Q c Hunt Hpref, m = normfby_node Q c n Hunt Hpref],
        with [normfby_global_normfbyed_nodes] and [normfbyed_nodes_rev] for the
        node lists and [normfby_node_step_weakens] for the step. *)
    Corollary normfby_global_signatures_weaken :
      forall (P : global) Hunt Hprefs (envs : node_scoped_env)
             (aux : list node_aux_names) stS stT GSout GTout,
        (forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
            (exists Q c (Hu : unnested_node Q nS)
                      (Hp : n_prefixes nS = norm1_prefs),
                nT = normfby_node Q c nS Hu Hp) ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envs aux stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nT envs aux stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        generate_all_lsignatures_scoped_env (rev P) envs aux stS = OK GSout ->
        generate_all_lsignatures_scoped_env
          (rev (normfby_global P Hunt Hprefs)) envs aux stT = OK GTout ->
        call_weakens GSout GTout /\ sigs_preserved GSout GTout.
    Proof.
      intros P Hunt Hprefs envs aux stS stT GSout GTout Hstep Hsrc Htgt.
      set (R := fun n m =>
        exists Q c (Hu : unnested_node Q n)
               (Hp : n_prefixes n = norm1_prefs),
          m = normfby_node Q c n Hu Hp).
      assert (HR : Forall2 R (rev P) (rev (normfby_global P Hunt Hprefs))).
      { unfold R. apply normfbyed_nodes_rev.
        apply (normfby_global_normfbyed_nodes P Hunt Hprefs). }
      assert (HS :
        forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
          R nS nT ->
          call_weakens accS accT ->
          generate_lnode_sig_scoped_env accS nS envs aux stS0
            = OK (sgS, stS1) ->
          generate_lnode_sig_scoped_env accT nT envs aux stT0
            = OK (sgT, stT1) ->
          sig_head_weakens sgS sgT).
      { intros accS accT nS nT sgS stS0 stS1 sgT stT0 stT1
          Hnodes Hweak HgenS HgenT.
        exact (Hstep accS accT nS nT sgS stS0 stS1 sgT stT0 stT1
                 Hnodes Hweak HgenS HgenT). }
      exact (generate_all_lsignatures_weakens R envs aux
               (rev P) (rev (normfby_global P Hunt Hprefs)) HR HS
               stS stT GSout GTout Hsrc Htgt).
    Qed.


    (** ** Unnesting, at the program level

        The mirror of [normfby_global_signatures_weaken], and equally direct:
        the shared lockstep instantiated at the relation [unnest_global]
        establishes. *)
    Corollary unnest_global_signatures_weaken :
      forall (P : global) Hwl Hprefs (envs : node_scoped_env)
             (aux : list node_aux_names) stS stT GSout GTout,
        (forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
            (exists Pt (Hw : wl_node Pt nS)
                       (Hp : n_prefixes nS = elab_prefs),
                nT = unnest_node Pt nS Hw Hp) ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envs aux stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nT envs aux stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        generate_all_lsignatures_scoped_env (rev P) envs aux stS = OK GSout ->
        generate_all_lsignatures_scoped_env
          (rev (unnest_global P Hwl Hprefs)) envs aux stT = OK GTout ->
        call_weakens GSout GTout /\ sigs_preserved GSout GTout.
    Proof.
      intros P Hwl Hprefs envs aux stS stT GSout GTout Hstep Hsrc Htgt.
      eapply generate_all_lsignatures_weakens;
        [apply unnested_nodes_rev;
         exact (unnest_global_unnested_nodes P Hwl Hprefs)
        |exact Hstep|exact Hsrc|exact Htgt].
    Qed.

    (** ** The two legs composed

        [call_weakens] is transitive, so the two phases compose with nothing
        new.  This is preservation across normalisation as the pipeline performs
        it: [normalize_global] is exactly [normfby_global] after
        [unnest_global], with a causality check between them that does not touch
        the program.

        The middle signature global is named once and used on both sides, which
        is what makes the two legs meet.  It is generated from the unnested
        program, so the state it starts at is immaterial -- that program is
        unnested, hence the generator is state-pure on it -- but nothing here
        needs that, since the caller supplies the one run. *)
    Lemma call_weakens_trans :
      forall G1 G2 G3,
        call_weakens G1 G2 -> call_weakens G2 G3 -> call_weakens G1 G3.
    Proof.
      intros G1 G2 G3 H12 H23 f sg1 inp ck rst outs cs1 st st1 Hf1 Hfr Hnd Hg1.
      destruct (H12 f sg1 inp ck rst outs cs1 st st1 Hf1 Hfr Hnd Hg1)
        as (sg2 & cs2 & Hf2 & Hs12 & Hg2 & Hce12).
      assert (call_subst_fresh sg2 inp ck rst outs) as Hfr2
          by (unfold call_subst_fresh in *; rewrite Hs12; exact Hfr).
      destruct (H23 f sg2 inp ck rst outs cs2 st st Hf2 Hfr2 Hnd Hg2)
        as (sg3 & cs3 & Hf3 & Hs23 & Hg3 & Hce23).
      exists sg3, cs3. split; [exact Hf3|split; [rewrite Hs23; exact Hs12|]].
      split; [exact Hg3|].
      exact (cs_entails_trans _ _ _ Hce12 Hce23).
    Qed.

    Theorem normalize_signatures_weaken :
      forall (P : global) Hwl Hprefs Hunt Hprefs'
             (envs : node_scoped_env) (aux : list node_aux_names)
             stS stM stT GS GM GT,
        (** the unnesting step, node by node *)
        (forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
            (exists Pt (Hw : wl_node Pt nS)
                       (Hp : n_prefixes nS = elab_prefs),
                nT = unnest_node Pt nS Hw Hp) ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envs aux stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nT envs aux stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        (** and the [fby] step *)
        (forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
            (exists Q c (Hu : unnested_node Q nS)
                       (Hp : n_prefixes nS = norm1_prefs),
                nT = normfby_node Q c nS Hu Hp) ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envs aux stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nT envs aux stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        generate_all_lsignatures_scoped_env (rev P) envs aux stS = OK GS ->
        generate_all_lsignatures_scoped_env
          (rev (unnest_global P Hwl Hprefs)) envs aux stM = OK GM ->
        generate_all_lsignatures_scoped_env
          (rev (normfby_global (unnest_global P Hwl Hprefs) Hunt Hprefs'))
          envs aux stT = OK GT ->
        call_weakens GS GT /\ sigs_preserved GS GT.
    Proof.
      intros P Hwl Hprefs Hunt Hprefs' envs aux stS stM stT GS GM GT
        Hstepu Hstepn Hsrc Hmid Htgt.
      destruct (unnest_global_signatures_weaken P Hwl Hprefs envs aux stS stM
                  GS GM Hstepu Hsrc Hmid) as (Hc1 & Hp1).
      destruct (normfby_global_signatures_weaken
                  (unnest_global P Hwl Hprefs) Hunt Hprefs' envs aux stM stT
                  GM GT Hstepn Hmid Htgt) as (Hc2 & Hp2).
      split.
      - exact (call_weakens_trans _ _ _ Hc1 Hc2).
      - exact (sigs_preserved_trans _ _ _ Hp1 Hp2).
    Qed.




    (** * The assignment a node's run needs, built

        The last thing Leg I owes.  [normfby_node_entailment] takes the level
        assignment as a parameter; what follows is that a good one exists for
        the run [normfby_node] performs.

        Two constructions, because the two kinds of created variable are
        different in exactly the way that matters.  A *flag* is shared -- two
        equations on the same clock use one -- so its entry is built once, from
        the state, at a level that is a function of its clock, which is why
        sharing costs nothing.  A *delayed variable* is private to the equation
        that created it, and its level mentions that equation's delayed
        operand, so its entry is built by walking the run. *)

    (** [inversion] on a pair equation simplifies [merge] into its inner [fix],
        as it does on an [OK] equation; project through abstract components. *)
    Lemma pair_inv :
      forall {A B : Type} (a a' : A) (b b' : B),
        (a, b) = (a', b') -> a' = a /\ b' = b.
    Proof. intros A B a a' b b' H. inversion H. split; reflexivity. Qed.

    (** ** How the state grows

        [fresh_ident] prepends, and nothing else touches the annotations, so a
        step only ever extends them on the left.  That is what makes the ids
        created by two different steps disjoint, given [NoDup] of the whole. *)

    Lemma init_var_for_clock_anns :
      forall ck i eqsi q q',
        init_var_for_clock ck q = (i, eqsi, q') ->
        st_anns q' = st_anns q
        \/ st_anns q' = (i, ((bool_type, ck), true)) :: st_anns q.
    Proof.
      intros ck i eqsi q q' H. unfold init_var_for_clock in H.
      destruct (find (fun '(_, (ty, cl', isinit)) =>
                        isinit && (cl' ==b ck) && (ty ==b bool_type))
                  (st_anns q)) as [(y & a)|].
      - inversion H; subst. now left.
      - destruct (fresh_ident norm2 ((bool_type, ck), true) q) as (y, sy) eqn:Ey.
        inversion H; subst. right.
        exact (fresh_ident_anns _ _ _ _ _ Ey).
    Qed.

    Lemma fby_equation_anns :
      forall to_cut eq out q q',
        fby_equation to_cut eq q = (out, q') ->
        exists new,
          st_anns q' = new ++ st_anns q
          (** and the delayed variable the output defines, when there is one,
              is among what this step added.  Both clauses are guarded by the
              equation being a delayed definition, exactly as
              [fby_eqn_data]'s is: on an arrow the pass creates no delayed
              variable, and the [ite] pattern could otherwise be matched by the
              flag's own equation. *)
          /\ (forall x x' ann e0 e,
                 eq = ([x], [Efby [e0] [e] [ann]]) ->
                 out = [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] ->
                 In x' (List.map fst new))
          /\ (forall x i px eqsi e0 e ty ck name ann,
                 eq = ([x], [Efby [e0] [e] [ann]]) ->
                 out = ([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                                [Evar px (ty, (ck, Some px))]
                                ([ty], (ck, name))])
                       :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck]
                                    [e] [(ty, (ck, name))]]) :: eqsi ->
                 In px (List.map fst new)).
    Proof.
      intros to_cut (xs, es) out q q' H.
      destruct (fby_equation_spec to_cut xs es)
        as [(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
           |[(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
            |[(x & e0 & e & ann & Hxs & Hes & Heq)
             |Heq]]].
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in H. cbv beta iota in H.
        destruct (PS.mem x to_cut).
        + apply bind_spec in H as (x' & s2 & Ex & H).
          rewrite ret_spec in H. inversion H; subst out q'.
          exists [(x', ((ty, ck), false))].
          split; [exact (fresh_ident_anns _ _ _ _ _ Ex)|].
          split.
          * intros z z' annq f0 f Heqq Houtq.
            inversion Houtq; subst. cbn [List.map fst]. now left.
          * intros z j px eqsj f0 f tq ckq nameq annq Heqq Houtq.
            inversion Houtq.
        + rewrite ret_spec in H. inversion H; subst out q'.
          exists []. split; [reflexivity|].
          split; [intros z z' annq f0 f Heqq Houtq; inversion Houtq
                 |intros z j px eqsj f0 f tq ckq nameq annq Heqq Houtq;
                  inversion Houtq].
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in H.
        apply bind2_spec in H as (fby & eqsa & s1 & Hfby & H).
        rewrite ret_spec in H. inversion H; subst out q'.
        unfold fby_iteexp in Hfby.
        apply bind2_spec in Hfby as (i & eqsi & s2 & Ei & Hfby).
        apply bind_spec in Hfby as (px & s3 & Ep & Hfby).
        rewrite ret_spec in Hfby. inversion Hfby; subst fby eqsa s1.
        destruct (init_var_for_clock_anns ck i eqsi q s2 Ei) as [Ha|Ha].
        + exists [(px, ((ty, ck), false))].
          split;
            [rewrite (fresh_ident_anns _ _ _ _ _ Ep), Ha; reflexivity|].
          split.
          * intros z z' annq f0 f Heqq Houtq. inversion Houtq.
          * intros z j py eqsj f0 f tq ckq nameq annq Heqq Houtq.
            inversion Houtq; subst. cbn [List.map fst]. now left.
        + exists [(px, ((ty, ck), false)); (i, ((bool_type, ck), true))].
          split;
            [rewrite (fresh_ident_anns _ _ _ _ _ Ep), Ha; reflexivity|].
          split.
          * intros z z' annq f0 f Heqq Houtq. inversion Houtq.
          * intros z j py eqsj f0 f tq ckq nameq annq Heqq Houtq.
            inversion Houtq; subst. cbn [List.map fst]. now left.
      - subst xs es. destruct ann as (ty, (ck, name)).
        rewrite Heq in H.
        apply bind2_spec in H as (ite & eqsa & s1 & Hite & H).
        rewrite ret_spec in H. inversion H; subst out q'.
        unfold arrow_iteexp in Hite.
        apply bind2_spec in Hite as (i & eqsi & s2 & Ei & Hite).
        rewrite ret_spec in Hite. inversion Hite; subst ite eqsa s1.
        destruct (init_var_for_clock_anns ck i eqsi q s2 Ei) as [Ha|Ha].
        + exists []. split; [exact Ha|].
          split; intros; discriminate.
        + exists [(i, ((bool_type, ck), true))]. split; [exact Ha|].
          split; intros; discriminate.
      - rewrite Heq in H. rewrite ret_spec in H.
        inversion H; subst out q'.
        exists []. split; [reflexivity|].
        split.
        + intros z z' annq f0 f Heqq Houtq. subst. inversion Houtq.
        + intros z j py eqsj f0 f tq ckq nameq annq Heqq Houtq.
          subst. inversion Houtq.
    Qed.

    (** ** The flags' entries

        One per flag the run created, at its clock's ambient.  Functional
        because the level is a function of the flag: the same security name is
        the same variable ([env] injective), hence the same entry of the state
        ([NoDup] of its identifiers), hence the same clock. *)
    Lemma flag_pairs_exists :
      forall (l : list (ident * ((type * clock) * bool))),
        NoDup (List.map fst l) ->
        env_injective env ->
        In rst_ty scope ->
        (forall v a, In (v, a) l ->
            exists b, Env.find v env = Some b /\ ~ In b scope) ->
        (forall v a, In (v, a) l ->
            exists ckty, assign_clk_type env base_ty (snd (fst a)) = Some ckty
                         /\ (forall z, In z ckty -> In z scope)) ->
        exists fp,
          created_hidden fp
          /\ levels_visible fp
          /\ levels_functional fp
          /\ (forall y L, In (y, L) fp ->
                 exists v a, In (v, a) l /\ Env.find v env = Some y
                             /\ snd a = true)
          /\ (forall i cki ckti bi,
                 In (i, ((bool_type, cki), true)) l ->
                 assign_clk_type env base_ty cki = Some ckti ->
                 Env.find i env = Some bi ->
                 In (bi, merge [rst_ty] ckti) fp).
    Proof.
      induction l as [|(v, a) l IH];
        intros Hnd Hinj Hrst Hnames Hclocks.
      - exists []. repeat split;
          [intros y L []|intros y L z []|intros y L1 L2 []
          |intros y L []|intros i cki ckti bi []].
      - cbn [List.map] in Hnd.
        inversion Hnd as [|z0 l0 Hvnot Hndl]; subst.
        destruct (IH Hndl Hinj Hrst
                    (fun w b Hw => Hnames w b (or_intror Hw))
                    (fun w b Hw => Hclocks w b (or_intror Hw)))
          as (fp & Hhid & Hvis & Hfun & Hfrom & Hflags).
        destruct (snd a) eqn:Ea.
        + (** a flag: it gets its clock's ambient *)
          destruct (Hnames v a (or_introl (@Coq.Init.Logic.eq_refl _ _)))
            as (b & Hb & Hbs).
          destruct (Hclocks v a (or_introl (@Coq.Init.Logic.eq_refl _ _)))
            as (ckty & Hckty & Hcks).
          exists ((b, merge [rst_ty] ckty) :: fp).
          (** the new name is not one of the old ones *)
          assert (Hnew : forall L, ~ In (b, L) fp).
          { intros L Hc.
            destruct (Hfrom b L Hc) as (w & aw & Hw & Hfw & _).
            assert (v = w) as ?
                by (exact (Hinj v w b b Hb Hfw
                             (@Coq.Init.Logic.eq_refl ident b))); subst w.
            apply Hvnot. apply in_map_iff. exists (v, aw).
            split; [reflexivity|exact Hw]. }
          repeat split.
          * intros y L [Hy|Hy];
              [inversion Hy; subst y L; exact Hbs|exact (Hhid y L Hy)].
          * intros y L z [Hy|Hy] Hz;
              [|exact (Hvis y L z Hy Hz)].
            apply pair_inv in Hy as (? & ?); subst y L.
            apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
              [destruct Hz as [Hz|[]]; subst z; exact Hrst
              |exact (Hcks z Hz)].
          * intros y L1 L2 [H1|H1] [H2|H2].
            -- inversion H1; inversion H2; subst; reflexivity.
            -- inversion H1; subst y L1. now elim (Hnew L2).
            -- inversion H2; subst y L2. now elim (Hnew L1).
            -- exact (Hfun y L1 L2 H1 H2).
          * intros y L [Hy|Hy].
            -- inversion Hy; subst y L.
               exists v, a. split; [now left|split; [exact Hb|exact Ea]].
            -- destruct (Hfrom y L Hy) as (w & aw & Hw & Hfw & Haw).
               exists w, aw. split; [now right|split; [exact Hfw|exact Haw]].
          * intros i cki ckti bi [Hi|Hi] Hckti Hbi.
            -- inversion Hi; subst i a.
               cbn [fst snd] in Hckty. rewrite Hckty in Hckti.
               apply option_Some_inj in Hckti; subst ckti.
               rewrite Hb in Hbi. apply option_Some_inj in Hbi; subst bi.
               now left.
            -- right. exact (Hflags i cki ckti bi Hi Hckti Hbi).
        + (** not a flag: nothing to add *)
          exists fp. repeat split;
            [exact Hhid|exact Hvis|exact Hfun
            |intros y L Hy; destruct (Hfrom y L Hy) as (w & aw & Hw & Hfw & Haw);
             exists w, aw; split; [now right|split; [exact Hfw|exact Haw]]
            |].
          intros i cki ckti bi [Hi|Hi] Hckti Hbi.
          * inversion Hi; subst i a. cbn [snd] in Ea. discriminate Ea.
          * exact (Hflags i cki ckti bi Hi Hckti Hbi).
    Qed.


    (** ** The delayed variables' entries

        One per equation that created one, at the ambient of its clock joined
        with its own delayed operand's type.  Unlike a flag, a delayed variable
        belongs to exactly one equation, so these are built by walking the run.

        Functionality is where the walk earns its keep: the head's variable is
        among the annotations that step added, the tail's among those the later
        steps added, and [NoDup] of the whole separates them.  [env] injective
        then separates the names. *)

    Lemma fby_eqn_data_mono :
      forall pairs pairs' eq eqk,
        (forall p, In p pairs -> In p pairs') ->
        fby_eqn_data pairs eq eqk -> fby_eqn_data pairs' eq eqk.
    Proof.
      intros pairs pairs' eq eqk Hincl Hd x e0 e ty ck name Hshape.
      destruct (Hd x e0 e ty ck name Hshape)
        as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs & H0 & H1 & HL & Hcr).
      exists ckty, s0, s1, b.
      split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
      split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
      split; [exact HL|].
      intro Hfby. destruct (Hcr Hfby) as (Hc1 & Hc2). split.
      - intros x' ann bp Ho Hbp. exact (Hincl _ (Hc1 x' ann bp Ho Hbp)).
      - intros i px eqsi bp Ho Hbp. exact (Hincl _ (Hc2 i px eqsi bp Ho Hbp)).
    Qed.

    Lemma Forall2_impl' :
      forall {A B : Type} (P Q : A -> B -> Prop) l l',
        (forall a b, P a b -> Q a b) ->
        Forall2 P l l' -> Forall2 Q l l'.
    Proof.
      intros A B P Q l l' Himp HF.
      induction HF as [|a b l1 l2 Hab Hr IH]; constructor;
        [exact (Himp a b Hab)|exact IH].
    Qed.

    Lemma delayed_pairs_exists :
      forall to_cut eqs eqs' q qf,
        map_bind (fby_equation to_cut) eqs q = (eqs', qf) ->
        (forall v a, In (v, a) (st_anns qf) ->
            exists b, Env.find v env = Some b /\ ~ In b scope) ->
        env_injective env ->
        NoDup (st_ids qf) ->
        (forall x e0 e ty ck name,
            In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) eqs
            \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) eqs ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e r
                            = OK ([(s1, [])], r))
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        exists dp new,
          st_anns qf = new ++ st_anns q
          /\ (forall y L, In (y, L) dp ->
                 exists v a, Env.find v env = Some y
                             /\ In (v, a) (st_anns qf)
                             /\ snd a = false
                             /\ In v (List.map fst new))
          /\ created_hidden dp
          /\ levels_visible dp
          /\ levels_functional dp
          /\ Forall2 (fby_eqn_data dp) eqs eqs'.
    Proof.
      intros to_cut eqs. induction eqs as [|eq eqs IH];
        intros eqs' q qf Hrun Hnames Hinj Hnd Hdata.
      - change (ret ([] : list (list equation)) q = (eqs', qf)) in Hrun.
        rewrite ret_spec in Hrun. inversion Hrun; subst eqs' qf.
        exists [], []. split; [reflexivity|].
        split; [intros y L []|].
        split; [intros y L []|].
        split; [intros y L z []|].
        split; [intros y L1 L2 []|constructor].
      - change
          (bind (fby_equation to_cut eq)
             (fun e1 =>
                bind (map_bind (fby_equation to_cut) eqs)
                  (fun er => ret (e1 :: er))) q = (eqs', qf))
          in Hrun.
        apply bind_spec in Hrun as (eq1 & q1 & Hrun1 & Hrun).
        apply bind_spec in Hrun as (eqsr & q2 & Hrunr & Hret).
        rewrite ret_spec in Hret. inversion Hret; subst eqs' qf.
        destruct (fby_equation_anns to_cut eq eq1 q q1 Hrun1)
          as (new1 & Hanns1 & Hcut1 & Hite1).
        destruct (IH eqsr q1 q2 Hrunr Hnames Hinj Hnd
                    (fun x e0 e ty ck name Hin =>
                       Hdata x e0 e ty ck name
                         match Hin with
                         | or_introl h => or_introl (or_intror h)
                         | or_intror h => or_intror (or_intror h)
                         end))
          as (dp & newt & Hannst & Hfrom & Hhid & Hvis & Hfun & Hforall).
        assert (Hall : st_anns q2 = (newt ++ new1) ++ st_anns q)
          by (rewrite <- app_assoc, <- Hanns1; exact Hannst).
        (** the head's variables and the tail's are disjoint *)
        assert (Hdisj : forall v, In v (List.map fst newt) ->
                        ~ In v (List.map fst new1)).
        { intros v Hvt Hv1.
          unfold st_ids in Hnd. rewrite Hall, <- app_assoc in Hnd.
          rewrite !List.map_app in Hnd.
          eapply NoDup_app_In; [exact Hnd|exact Hvt|].
          apply in_or_app. now left. }
        (** a name already used by the tail is not a fresh head variable *)
        assert (Hfresh : forall v b, Env.find v env = Some b ->
                    In v (List.map fst new1) -> forall L, ~ In (b, L) dp).
        { intros v b Hb Hv1 L Hc.
          destruct (Hfrom b L Hc) as (w & aw & Hw & _ & _ & Hwt).
          assert (v = w) as ?
              by (exact (Hinj v w b b Hb Hw
                           (@Coq.Init.Logic.eq_refl ident b))); subst w.
          exact (Hdisj v Hwt Hv1). }
        destruct eq as (xs, es).
        destruct (fby_equation_spec to_cut xs es)
          as [(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
             |[(x & e0 & e & ann & Hxs & Hes & Hconst & Heq)
              |[(x & e0 & e & ann & Hxs & Hes & Heq)
               |Heq]]].
        + (** a constant initial value *)
          subst xs es. destruct ann as (ty, (ck, name)).
          rewrite Heq in Hrun1. cbv beta iota in Hrun1.
          destruct (Hdata x e0 e ty ck name
                      (or_introl (in_eq _ _)))
            as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs & H0 & H1 & HL).
          destruct (PS.mem x to_cut).
          * apply bind_spec in Hrun1 as (x' & s2 & Ex & Hrun1).
            rewrite ret_spec in Hrun1. inversion Hrun1; subst eq1 q1.
            assert (Hin2 : In (x', ((ty, ck), false)) (st_anns q2)).
            { rewrite Hannst. apply in_or_app. right.
              exact (fresh_ident_In _ _ _ _ _ Ex). }
            destruct (Hnames x' ((ty, ck), false) Hin2) as (b' & Hb' & Hb's).
            assert (Hx'1 : In x' (List.map fst new1))
              by (eapply Hcut1; reflexivity).
            exists ((b', merge (merge [rst_ty] ckty) (merge s0 s1)) :: dp),
                   (newt ++ new1).
            split; [exact Hall|].
            split.
            { intros y L [Hy|Hy].
              - apply pair_inv in Hy as (? & ?); subst y L.
                exists x', ((ty, ck), false).
                split; [exact Hb'|]. split; [exact Hin2|].
                split; [reflexivity|].
                rewrite List.map_app. apply in_or_app. now right.
              - destruct (Hfrom y L Hy) as (w & aw & Hw & Hwin & Haw & Hwt).
                exists w, aw. split; [exact Hw|]. split; [exact Hwin|].
                split; [exact Haw|].
                rewrite List.map_app. apply in_or_app. now left. }
            split.
            { intros y L [Hy|Hy];
                [apply pair_inv in Hy as (? & ?); subst y L; exact Hb's
                |exact (Hhid y L Hy)]. }
            split.
            { intros y L z [Hy|Hy] Hz;
                [|exact (Hvis y L z Hy Hz)].
              apply pair_inv in Hy as (? & ?); subst y L. exact (HL z Hz). }
            split.
            { intros y L1 L2 [K1|K1] [K2|K2].
              - apply pair_inv in K1 as (? & ?);
                  apply pair_inv in K2 as (? & ?); subst; reflexivity.
              - apply pair_inv in K1 as (? & ?); subst y L1.
                now elim (Hfresh x' b' Hb' Hx'1 L2).
              - apply pair_inv in K2 as (? & ?); subst y L2.
                now elim (Hfresh x' b' Hb' Hx'1 L1).
              - exact (Hfun y L1 L2 K1 K2). }
            constructor.
            -- intros z f0 f tq ckq nameq Hshape.
               assert (Hz : z = x /\ f0 = e0 /\ f = e /\ tq = ty
                            /\ ckq = ck /\ nameq = name).
               { destruct Hshape as [Hs|Hs]; inversion Hs; subst;
                   repeat split; reflexivity. }
               destruct Hz as (? & ? & ? & ? & ? & ?); subst.
               exists ckty, s0, s1, b.
               split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
               split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
               split; [exact HL|].
               intros _. split.
               ++ intros y annq bp Ho Hbp.
                  inversion Ho; subst y annq.
                  rewrite Hb' in Hbp. apply option_Some_inj in Hbp; subst bp.
                  now left.
               ++ intros j py eqsj bp Ho Hbp. inversion Ho.
            -- eapply Forall2_impl'; [|exact Hforall].
               intros a1 a2 Ha. eapply fby_eqn_data_mono; [|exact Ha].
               intros pq Hpq. now right.
          * rewrite ret_spec in Hrun1. inversion Hrun1; subst eq1 q1.
            exists dp, (newt ++ new1).
            split; [exact Hall|].
            split.
            { intros y L Hy.
              destruct (Hfrom y L Hy) as (w & aw & Hw & Hwin & Haw & Hwt).
              exists w, aw. split; [exact Hw|]. split; [exact Hwin|].
              split; [exact Haw|].
              rewrite List.map_app. apply in_or_app. now left. }
            split; [exact Hhid|]. split; [exact Hvis|]. split; [exact Hfun|].
            constructor.
            -- intros z f0 f tq ckq nameq Hshape.
               assert (Hz : z = x /\ f0 = e0 /\ f = e /\ tq = ty
                            /\ ckq = ck /\ nameq = name).
               { destruct Hshape as [Hs|Hs]; inversion Hs; subst;
                   repeat split; reflexivity. }
               destruct Hz as (? & ? & ? & ? & ? & ?); subst.
               exists ckty, s0, s1, b.
               split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
               split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
               split; [exact HL|].
               intros _. split;
                 [intros y annq bp Ho Hbp; inversion Ho
                 |intros j py eqsj bp Ho Hbp; inversion Ho].
            -- exact Hforall.
        + (** a non-constant initial value *)
          subst xs es. destruct ann as (ty, (ck, name)).
          rewrite Heq in Hrun1.
          apply bind2_spec in Hrun1 as (fby & eqsa & s1' & Hfby & Hrun1).
          rewrite ret_spec in Hrun1. inversion Hrun1; subst eq1 q1.
          destruct (fby_iteexp_created e0 e ty ck name fby eqsa q s1' Hfby)
            as (i & px & eqsi & Hi & Hpx & Hfbye & Heqsa & Heqsi).
          subst fby eqsa.
          destruct (Hdata x e0 e ty ck name (or_introl (in_eq _ _)))
            as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs & H0 & H1 & HL).
          assert (Hin2 : In (px, ((ty, ck), false)) (st_anns q2)).
          { rewrite Hannst. apply in_or_app. now right. }
          destruct (Hnames px ((ty, ck), false) Hin2) as (bp & Hbp & Hbps).
          assert (Hpx1 : In px (List.map fst new1))
            by (eapply Hite1; [reflexivity|reflexivity]).
          exists ((bp, merge (merge [rst_ty] ckty) s1) :: dp), (newt ++ new1).
          split; [exact Hall|].
          split.
          { intros y L [Hy|Hy].
            - apply pair_inv in Hy as (? & ?); subst y L.
              exists px, ((ty, ck), false).
              split; [exact Hbp|]. split; [exact Hin2|].
              split; [reflexivity|].
              rewrite List.map_app. apply in_or_app. now right.
            - destruct (Hfrom y L Hy) as (w & aw & Hw & Hwin & Haw & Hwt).
              exists w, aw. split; [exact Hw|]. split; [exact Hwin|].
              split; [exact Haw|].
              rewrite List.map_app. apply in_or_app. now left. }
          split.
          { intros y L [Hy|Hy];
              [apply pair_inv in Hy as (? & ?); subst y L; exact Hbps
              |exact (Hhid y L Hy)]. }
          split.
          { intros y L z [Hy|Hy] Hz; [|exact (Hvis y L z Hy Hz)].
            apply pair_inv in Hy as (? & ?); subst y L.
            apply HL. eapply merge_incl_mono;
              [intros w Hw; exact Hw
              |intros w Hw; apply in_merge_right; exact Hw
              |exact Hz]. }
          split.
          { intros y L1 L2 [K1|K1] [K2|K2].
            - apply pair_inv in K1 as (? & ?);
                apply pair_inv in K2 as (? & ?); subst; reflexivity.
            - apply pair_inv in K1 as (? & ?); subst y L1.
              now elim (Hfresh px bp Hbp Hpx1 L2).
            - apply pair_inv in K2 as (? & ?); subst y L2.
              now elim (Hfresh px bp Hbp Hpx1 L1).
            - exact (Hfun y L1 L2 K1 K2). }
          constructor.
          -- intros z f0 f tq ckq nameq Hshape.
             assert (Hz : z = x /\ f0 = e0 /\ f = e /\ tq = ty
                          /\ ckq = ck /\ nameq = name).
             { destruct Hshape as [Hs|Hs]; inversion Hs; subst;
                 repeat split; reflexivity. }
             destruct Hz as (? & ? & ? & ? & ? & ?); subst.
             exists ckty, s0, s1, b.
             split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
             split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
             split; [exact HL|].
             intros _. split.
             ++ intros y annq bq Ho Hbq. inversion Ho.
             ++ intros j py eqsj bq Ho Hbq.
                inversion Ho; subst j py eqsj.
                rewrite Hbp in Hbq. apply option_Some_inj in Hbq; subst bq.
                now left.
          -- eapply Forall2_impl'; [|exact Hforall].
             intros a1 a2 Ha. eapply fby_eqn_data_mono; [|exact Ha].
             intros pq Hpq. now right.
        + (** an arrow: no delayed variable is created *)
          subst xs es. destruct ann as (ty, (ck, name)).
          rewrite Heq in Hrun1.
          apply bind2_spec in Hrun1 as (ite & eqsa & s1' & Hite & Hrun1).
          rewrite ret_spec in Hrun1. inversion Hrun1; subst eq1 q1.
          destruct (Hdata x e0 e ty ck name (or_intror (in_eq _ _)))
            as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs & H0 & H1 & HL).
          exists dp, (newt ++ new1).
          split; [exact Hall|].
          split.
          { intros y L Hy.
            destruct (Hfrom y L Hy) as (w & aw & Hw & Hwin & Haw & Hwt).
            exists w, aw. split; [exact Hw|]. split; [exact Hwin|].
            split; [exact Haw|].
            rewrite List.map_app. apply in_or_app. now left. }
          split; [exact Hhid|]. split; [exact Hvis|]. split; [exact Hfun|].
          constructor.
          -- intros z f0 f tq ckq nameq Hshape.
             assert (Hz : z = x /\ f0 = e0 /\ f = e /\ tq = ty
                          /\ ckq = ck /\ nameq = name).
             { destruct Hshape as [Hs|Hs]; inversion Hs; subst;
                 repeat split; reflexivity. }
             destruct Hz as (? & ? & ? & ? & ? & ?); subst.
             exists ckty, s0, s1, b.
             split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
             split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
             split; [exact HL|].
             intro Hfby. inversion Hfby.
          -- exact Hforall.
        + (** anything else, untouched *)
          rewrite Heq in Hrun1. rewrite ret_spec in Hrun1.
          inversion Hrun1; subst eq1 q1.
          exists dp, (newt ++ new1).
          split; [exact Hall|].
          split.
          { intros y L Hy.
            destruct (Hfrom y L Hy) as (w & aw & Hw & Hwin & Haw & Hwt).
            exists w, aw. split; [exact Hw|]. split; [exact Hwin|].
            split; [exact Haw|].
            rewrite List.map_app. apply in_or_app. now left. }
          split; [exact Hhid|]. split; [exact Hvis|]. split; [exact Hfun|].
          constructor.
          -- intros z f0 f tq ckq nameq Hshape.
             destruct (Hdata z f0 f tq ckq nameq
                         match Hshape with
                         | or_introl h => or_introl (or_introl h)
                         | or_intror h => or_intror (or_introl h)
                         end)
               as (ckty & s0 & s1 & b & Hck & Hckty & Hb & Hbs & H0 & H1 & HL).
             exists ckty, s0, s1, b.
             split; [exact Hck|]. split; [exact Hckty|]. split; [exact Hb|].
             split; [exact Hbs|]. split; [exact H0|]. split; [exact H1|].
             split; [exact HL|].
             intros _. split;
               [intros y annq bp Ho Hbp; inversion Ho
               |intros j py eqsj bp Ho Hbp; inversion Ho].
          -- exact Hforall.
    Qed.


    Lemma nodup_fst_unique :
      forall {A : Type} (l : list (ident * A)) y v w,
        NoDup (List.map fst l) -> In (y, v) l -> In (y, w) l -> v = w.
    Proof.
      induction l as [|(z, a) l IH]; intros y v w Hnd Hv Hw; [contradiction|].
      cbn [List.map] in Hnd. inversion Hnd as [|z0 l0 Hz Hnd']; subst.
      destruct Hv as [Hv|Hv]; destruct Hw as [Hw|Hw].
      - apply pair_inv in Hv as (? & ?); apply pair_inv in Hw as (? & ?);
          subst; reflexivity.
      - apply pair_inv in Hv as (? & ?); subst y v. exfalso. apply Hz.
        apply in_map_iff. exists (z, w). split; [reflexivity|exact Hw].
      - apply pair_inv in Hw as (? & ?); subst y w. exfalso. apply Hz.
        apply in_map_iff. exists (z, v). split; [reflexivity|exact Hv].
      - exact (IH y v w Hnd' Hv Hw).
    Qed.

    (** ** The assignment, assembled

        The flags' entries and the delayed variables' entries, concatenated.
        Functionality across the two is the only thing left to see, and the
        state settles it: a name shared between them would be one variable, by
        [env] injectivity, recorded once, by [NoDup] of the identifiers -- and a
        flag's record carries [true] where a delayed variable's carries
        [false]. *)
    Lemma node_pairs_exists :
      forall to_cut (eqs : list equation) eqs' stf,
        map_bind (fby_equation to_cut) eqs init_st = (eqs', stf) ->
        (forall v a, In (v, a) (st_anns stf) ->
            exists b, Env.find v env = Some b /\ ~ In b scope) ->
        env_injective env ->
        NoDup (st_ids stf) ->
        In rst_ty scope ->
        (forall v a, In (v, a) (st_anns stf) ->
            exists ckty, assign_clk_type env base_ty (snd (fst a)) = Some ckty
                         /\ (forall z, In z ckty -> In z scope)) ->
        (forall x e0 e ty ck name,
            In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) eqs
            \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) eqs ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e r
                            = OK ([(s1, [])], r))
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        exists pairs,
          levels_functional pairs
          /\ created_hidden pairs
          /\ levels_visible pairs
          /\ Forall2 (fby_eqn_data pairs) eqs eqs'
          /\ (forall i cki ckti bi,
                 In (i, ((bool_type, cki), true)) (st_anns stf) ->
                 assign_clk_type env base_ty cki = Some ckti ->
                 Env.find i env = Some bi ->
                 In (bi, merge [rst_ty] ckti) pairs).
    Proof.
      intros to_cut eqs eqs' stf Hrun Hnames Hinj Hnd Hrst Hclocks Hdata.
      unfold st_ids in Hnd.
      destruct (flag_pairs_exists (st_anns stf) Hnd Hinj Hrst Hnames Hclocks)
        as (fp & Hfhid & Hfvis & Hffun & Hffrom & Hflags).
      destruct (delayed_pairs_exists to_cut eqs eqs' init_st stf
                  Hrun Hnames Hinj Hnd Hdata)
        as (dp & new & Hanns & Hfrom & Hdhid & Hdvis & Hdfun & Hforall).
      exists (fp ++ dp).
      (** a flag and a delayed variable are never the same name *)
      assert (Hsep : forall y L1 L2, In (y, L1) fp -> In (y, L2) dp -> False).
      { intros y L1 L2 H1 H2.
        destruct (Hffrom y L1 H1) as (v & a & Hvin & Hv & Hva).
        destruct (Hfrom y L2 H2) as (w & b & Hw & Hwin & Hwb & _).
        assert (v = w) as ?
            by (exact (Hinj v w y y Hv Hw
                         (@Coq.Init.Logic.eq_refl ident y))); subst w.
        assert (a = b) as ?
            by (exact (nodup_fst_unique (st_anns stf) v a b Hnd Hvin Hwin));
          subst b.
        rewrite Hva in Hwb. discriminate Hwb. }
      split.
      - intros y L1 L2 H1 H2.
        apply in_app_or in H1 as [H1|H1]; apply in_app_or in H2 as [H2|H2].
        + exact (Hffun y L1 L2 H1 H2).
        + exfalso. exact (Hsep y L1 L2 H1 H2).
        + exfalso. exact (Hsep y L2 L1 H2 H1).
        + exact (Hdfun y L1 L2 H1 H2).
      - split.
        { intros y L Hy. apply in_app_or in Hy as [Hy|Hy];
            [exact (Hfhid y L Hy)|exact (Hdhid y L Hy)]. }
        split.
        { intros y L z Hy Hz. apply in_app_or in Hy as [Hy|Hy];
            [exact (Hfvis y L z Hy Hz)|exact (Hdvis y L z Hy Hz)]. }
        split.
        + eapply Forall2_impl'; [|exact Hforall].
          intros a1 a2 Ha. eapply fby_eqn_data_mono; [|exact Ha].
          intros pq Hpq. apply in_or_app. now right.
        + intros i cki ckti bi Hi Hckti Hbi.
          apply in_or_app. left.
          exact (Hflags i cki ckti bi Hi Hckti Hbi).
    Qed.


    (** * Leg I's per-node step

        The counterpart of Leg U's, assembled the same way:
        [normfby_node_entailment] supplies the entailment,
        [normfby_node_signatures_preserved_decoupled] the interface equality and
        the transport through [simplify], and [sig_call_weakens_from_good]
        converts the pair into [sig_head_weakens].  The target accumulator is
        the section's [G], since that is the one [normfby_node_entailment]
        speaks about.

        The level assignment enters as a hypothesis -- that a good one exists
        for this node's run -- because that is the one thing Leg I still owes;
        it is [node_pairs_exists] in work_docs/Next_remaining.v.  Everything
        else here is the program-level facts, which are not phase-specific. *)
    Corollary normfby_node_step :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs) (Q' : global)
             (envs : node_scoped_env) (aux : list node_aux_names)
             (lo : sec_state) accS sgS stS0 stS1 sgT stT0 stT1,
        find_node_env n.(n_name) envs = Some env ->
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        cenv = lnode_clock_env (normfby_node Q c n Hunt Hpref) ->
        Forall (unnested_equation Q')
          (normfby_node Q c n Hunt Hpref).(n_eqs) ->
        (** what the run created, as the node records it; [node_pairs_exists]
            turns this into the level assignment *)
        env_injective env ->
        In rst_ty scope ->
        (forall eqs' stf,
            map_bind (fby_equation
                        (PS.union c (ps_from_list (List.map fst (n_out n)))))
              n.(n_eqs) init_st = (eqs', stf) ->
            (forall y a, In (y, a) (st_anns stf) ->
                exists d, Env.find y env = Some d /\ ~ In d scope)
            /\ (forall v a, In (v, a) (st_anns stf) ->
                   exists ckty,
                     assign_clk_type env base_ty (snd (fst a)) = Some ckty
                     /\ (forall z, In z ckty -> In z scope))) ->
        (** and what it says about each delayed equation *)
        (forall x e0 e ty ck name,
            In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) n.(n_eqs)
            \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) n.(n_eqs) ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
              /\ (forall r, assign_lexp_type G env base_ty rst_ty e r
                            = OK ([(s1, [])], r))
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        (** the run against the target accumulator is scoped *)
        (forall ce ct1,
            generate_leqns_constraints G env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, ct1) ->
            constraints_scoped scope ce) ->
        (** and the source run's own hygiene *)
        (forall ce ct1,
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, ct1) ->
            Forall (fun c => List.length (snd c) = 1%nat) ce) ->
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (cns, ct1) ->
            forall y, In y (locals ++ minted stS0 ct1) -> ~ In y scope) ->
        (** the program-level facts about the published pair *)
        signature_good sgS ->
        NoDup (signature_scope sgS) ->
        signature_good sgT ->
        signature_scoped sgT ->
        (forall z, In z (signature_scope sgS) -> In z scope) ->
        eapp_fresh_prop accS env base_ty rst_ty lo ->
        lcall_fresh_prop accS env base_ty rst_ty lo ->
        sec_le lo stS0 ->
        call_weakens accS G ->
        generate_lnode_sig_scoped_env accS n envs aux stS0 = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env G (normfby_node Q c n Hunt Hpref)
          envs aux stT0 = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
    Proof.
      intros Q c n Hunt Hpref Q' envs aux lo accS sgS stS0 stS1 sgT stT0 stT1
        Hfind Haux Hcenv Hun Hinj Hrst Hstate Heqdat Htgtsc Hwf Hdisj
        Hgood1 Hnd1 Hgood2 Hsc2 Hincl Hef Hlf Hlo0 Hw HS HT.
      (** the assignment, from the run *)
      assert (Hpairs : forall eqs' stf,
                 map_bind (fby_equation
                             (PS.union c
                                (ps_from_list (List.map fst (n_out n)))))
                   n.(n_eqs) init_st = (eqs', stf) ->
                 exists pairs,
                   levels_functional pairs
                   /\ created_hidden pairs
                   /\ levels_visible pairs
                   /\ Forall2 (fby_eqn_data pairs) n.(n_eqs) eqs'
                   /\ (forall y a, In (y, a) (st_anns stf) ->
                          find_clock cenv y = OK (snd (fst a))
                          /\ exists d, Env.find y env = Some d
                                       /\ ~ In d scope)
                   /\ (forall i cki ckti bi,
                          In (i, ((bool_type, cki), true)) (st_anns stf) ->
                          assign_clk_type env base_ty cki = Some ckti ->
                          Env.find i env = Some bi ->
                          In (bi, merge [rst_ty] ckti) pairs)).
      { intros eqs' stf Hrun.
        destruct (Hstate eqs' stf Hrun) as (Hnew0 & Hclocks).
        (** the two run facts the pass itself supplies *)
        assert (forall y a, In (y, a) (st_anns stf) ->
                   find_clock cenv y = OK (snd (fst a))
                   /\ exists d, Env.find y env = Some d /\ ~ In d scope)
          as Hnew.
        { intros y a Hya. split; [|exact (Hnew0 y a Hya)].
          rewrite Hcenv.
          exact (normfby_node_state_clocks Q c n Hunt Hpref eqs' stf y a
                   Hrun Hya). }
        assert (NoDup (st_ids stf)) as Hndst
            by exact (fby_run_st_ids_NoDup
                        (PS.union c (ps_from_list (List.map fst (n_out n))))
                        n.(n_eqs) eqs' stf Hrun).
        destruct (node_pairs_exists
                    (PS.union c (ps_from_list (List.map fst (n_out n))))
                    n.(n_eqs) eqs' stf Hrun
                    (fun v a Hva => match Hnew v a Hva with
                                    | conj _ h => h
                                    end)
                    Hinj Hndst Hrst Hclocks Heqdat)
          as (pairs & Hfun & Hhid & Hvis & Hforall & Hflags).
        exists pairs.
        split; [exact Hfun|]. split; [exact Hhid|]. split; [exact Hvis|].
        split; [exact Hforall|]. split; [exact Hnew|exact Hflags]. }
      unfold generate_lnode_sig_scoped_env in HS, HT.
      rewrite Hfind in HS.
      cbn [n_name normfby_node] in HT. rewrite Hfind in HT.
      destruct (normfby_node_signatures_preserved_decoupled Q c n Hunt Hpref
                  Q' accS G aux lo stS0 stT0 sgS stS1 sgT stT1
                  Haux Hun Hw Hef Hlf Hlo0)
        as (Hn & Hi & Ho & Hc & Hr & Hpres).
      - intros ce cet ct1 ct1' Hsrc Htgt.
        remember (map_bind
                    (fby_equation
                      (PS.union c (ps_from_list (List.map fst (n_out n)))))
                    n.(n_eqs) init_st) as run eqn:Hrun.
        destruct run as [eqs' stf].
        destruct (Hpairs eqs' stf
                    (@Coq.Init.Logic.eq_refl _ (eqs', stf)))
          as (pairs & Hfun & Hhid & Hvis & Hdata & Hnew & Hflags).
        eapply normfby_node_entailment;
          [exact Hcenv|exact Hfun|exact Hhid|exact Hvis
          | |exact (Htgtsc ce ct1 Hsrc)|exact Hsrc|exact Htgt].
        intros eqs'' stf' Hrun'.
        rewrite <- Hrun in Hrun'. inversion Hrun'; subst.
        exact (conj Hdata (conj Hnew Hflags)).
      - exact Hwf.
      - exact Hdisj.
      - exact HS.
      - exact HT.
      - assert (Hsp : SIGPROOFS.signatures_preserved sgS sgT).
        { split.
          - repeat split;
              [exact (@Coq.Init.Logic.eq_sym _ _ _ Hi)
              |exact (@Coq.Init.Logic.eq_sym _ _ _ Ho)
              |exact (@Coq.Init.Logic.eq_sym _ _ _ Hr)
              |exact (@Coq.Init.Logic.eq_sym _ _ _ Hc)].
          - eapply preserves_on_weaken; [exact Hincl|exact Hpres]. }
        split; [exact (@Coq.Init.Logic.eq_sym _ _ _ Hn)|].
        split; [exact Hsp|].
        eapply sig_call_weakens_from_good;
          [exact Hgood1|exact Hnd1|exact Hgood2|exact Hsc2|exact Hsp].
    Qed.
  End NormFbyNode.

End SecLusNormFby.
