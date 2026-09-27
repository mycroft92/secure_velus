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

    Lemma upds_const_val :
      forall (news : list ident) (v : Lat.t) dlt b,
        NoDup news -> In b news ->
        upds news (List.map (fun _ : ident => v) news) dlt b = v.
    Proof.
      intros news v dlt b Hnd Hb. apply upds_nth; [exact Hnd| |].
      - now rewrite map_length.
      - clear Hnd. induction news as [|z news IH]; [contradiction|].
        cbn [List.map combine In]. destruct Hb as [Hz|Hb];
          [subst z; now left|right; exact (IH Hb)].
    Qed.

    Lemma upds_const_off :
      forall (news : list ident) (v : Lat.t) dlt z,
        ~ In z news ->
        upds news (List.map (fun _ : ident => v) news) dlt z = dlt z.
    Proof. intros news v dlt z Hz. now apply upds_notin. Qed.

    Lemma fresh_names_entail :
      forall dlt (news : list ident) L cs,
        NoDup news ->
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
      intros dlt news L cs Hnd HnL Hall.
      unfold listSatisfiable. eapply Forall_impl; [|exact Hall].
      intros (lhs, rhs) (Hlhs & d & Hrhs & Hd).
      cbn [fst snd] in Hlhs, Hrhs. subst rhs.
      apply satisfiable_singleton_bound. intros z Hz.
      assert (Hzv : upds news (List.map (fun _ : ident => hm_ext dlt L) news)
                      dlt z ⊑ hm_ext dlt L).
      { destruct (Hlhs z Hz) as [HzL|Hzn];
          [ rewrite upds_const_off by (intro Hc; exact (HnL z Hc HzL));
            exact (hm_ext_list_in1 dlt L z HzL)
          | rewrite (upds_const_val news (hm_ext dlt L) dlt z Hnd Hzn);
            exact (order_refl _ _ (Lat.eq_refl _)) ]. }
      destruct Hd as [Hdn|(Hdn & Hdb)].
      - (** the target is a created name, which holds exactly that level *)
        cbn [hm_ext].
        rewrite (upds_const_val news (hm_ext dlt L) dlt d Hnd Hdn).
        eapply order_trans; [exact Hzv|apply join_bound1].
      - (** or the source equation already bounded that level by it *)
        cbn [hm_ext].
        rewrite (upds_const_off news (hm_ext dlt L) dlt d Hdn).
        eapply order_trans; [exact Hzv|exact Hdb].
    Qed.

    Lemma preserves_on_fresh_names :
      forall (news : list ident) L ce cet,
        NoDup news ->
        (forall z, In z news -> ~ In z L) ->
        (forall z, In z news -> ~ In z scope) ->
        (forall dlt, listSatisfiable dlt ce ->
          Forall (fun c =>
                    (forall z, In z (fst c) -> In z L \/ In z news)
                    /\ exists d, snd c = [d]
                         /\ (In d news
                             \/ (~ In d news
                                 /\ hm_ext dlt L ⊑ hm_ext dlt [d]))) cet) ->
        preserves_on scope ce cet.
    Proof.
      intros news L ce cet Hnd HnL Hns Hall dlt Hsat.
      exists (upds news (List.map (fun _ : ident => hm_ext dlt L) news) dlt).
      split.
      - intros z Hz. symmetry. apply upds_const_off.
        intro Hc. exact (Hns z Hc Hz).
      - apply fresh_names_entail; [exact Hnd|exact HnL|exact (Hall dlt Hsat)].
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
        (** the created variable's security name is new *)
        ~ In b' scope ->
        ~ In b' (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
        b <> b' ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [ann]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] st
          = OK (cet, u') ->
        preserves_on scope ce cet.
    Proof.
      intros x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u'
        Hckx Hckx' Hckty Hb Hb' H0 H1 Hsc Hfr Hne Hsrc Htgt.
      pose proof (assign_lexp_Efby_pair e0 e ann s0 s1 st H0 H1) as Hfby.
      (** the source's single constraint *)
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b st
                 Hckx Hckty Hfby Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      (** the target's two *)
      rewrite generate_leqns_constraints_cons in Htgt.
      apply sec_bind_inv in Htgt as (c1 & v1 & Hc1 & Htgt).
      apply sec_bind_inv in Htgt as (c2 & v2 & Hc2 & Hret).
      unfold SC.ret in Hret. inversion Hret; subst cet u'. clear Hret.
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Evar x' ann) ck ckty ([b'] : ST) b st Hckx Hckty
                 (assign_lexp_Evar_type x' ann b' st Hb') Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      rewrite generate_leqns_constraints_cons in Hc2.
      apply sec_bind_inv in Hc2 as (d1 & w1 & Hd1 & Hc2).
      apply sec_bind_inv in Hc2 as (d2 & w2 & Hd2 & Hret2).
      unfold SC.ret in Hret2. inversion Hret2; subst c2 v2. clear Hret2.
      rewrite generate_leqn_constraint_def in Hd1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x'
                 (Efby [e0] [e] [ann]) ck ckty (merge s0 s1) b' st
                 Hckx' Hckty Hfby Hb') in Hd1.
      apply OK_pair_inv in Hd1 as (? & ?); subst d1 w1.
      apply generate_leqns_constraints_nil in Hd2 as (? & ?); subst d2 w2.
      (** and the valuation that makes both hold *)
      intros dlt Hsat.
      assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                    ⊑ hm_ext dlt [b]).
      { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
        exact (Hsat _ (in_eq _ _)). }
      exists (upds [b']
                [hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))] dlt).
      assert (Hnot : forall z : ident, z <> b' -> ~ In z ([b'] : list ident))
        by (intros z Hz [Hc|[]]; exact (Hz (@Coq.Init.Logic.eq_sym _ _ _ Hc))).
      assert (Hb'v :
                upds [b'] [hm_ext dlt (merge (merge [rst_ty] ckty)
                                         (merge s0 s1))] dlt b'
                = hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1)))
        by (apply upds_nth;
            [constructor; [intros []|constructor]|reflexivity|now left]).
      assert (Hoff : forall z, z <> b' ->
                 upds [b'] [hm_ext dlt (merge (merge [rst_ty] ckty)
                                          (merge s0 s1))] dlt z = dlt z)
        by (intros z Hz; apply upds_notin; exact (Hnot z Hz)).
      assert (Hbx : hm_ext (upds [b']
                              [hm_ext dlt (merge (merge [rst_ty] ckty)
                                             (merge s0 s1))] dlt) [b]
                    = hm_ext dlt [b])
        by (cbn [hm_ext]; rewrite (Hoff b Hne); reflexivity).
      split.
      - intros z Hz. symmetry. apply Hoff. intro Hc. subst z. exact (Hsc Hz).
      - cbn [app]. constructor; [|constructor; [|constructor]].
        + (** [x] reads the fresh variable *)
          apply satisfiable_singleton_bound. intros z Hz. rewrite Hbx.
          apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
          * (** an ambient name: below the source's left-hand side *)
            assert (Hzl : In z (merge (merge [rst_ty] ckty) (merge s0 s1)))
              by (apply in_merge_left; exact Hz).
            rewrite Hoff by (intro Hc; subst z; exact (Hfr Hzl)).
            eapply order_trans; [|exact Hc0]. apply hm_ext_list_in1, Hzl.
          * (** the fresh variable itself, which is what it was chosen for *)
            destruct Hz as [Hz|[]]; subst z. rewrite Hb'v. exact Hc0.
        + (** and the fresh variable carries the source's right-hand side *)
          apply satisfiable_singleton_bound. intros z Hz.
          rewrite Hoff by (intro Hc; subst z; exact (Hfr Hz)).
          cbn [hm_ext]. rewrite Hb'v.
          eapply order_trans; [|apply join_bound1].
          apply hm_ext_list_in1, Hz.
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
        ~ In bi scope ->
        ~ In bi (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
        b <> bi ->
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
        preserves_on scope ce cet.
    Proof.
      intros x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs
        Hckx Hckty Hb Hbi H0 H1 Hsc Hfr Hne Heqs Hsrc Htgt.
      (** the source's single constraint *)
      rewrite generate_leqn_constraint_def in Hsrc by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Earrow [e0] [e] [(ty, (ck, name))]) ck ckty (merge s0 s1) b st
                 Hckx Hckty
                 (assign_lexp_Earrow_pair e0 e (ty, (ck, name)) s0 s1 st H0 H1)
                 Hb) in Hsrc.
      apply OK_pair_inv in Hsrc as (? & ?); subst ce u.
      (** the target's [ite], and whatever the flag needed *)
      apply generate_leqns_cons_inv in Htgt as (c1 & v1 & c2 & Hc1 & Hc2 & ?).
      rewrite generate_leqn_constraint_def in Hc1 by exact I.
      rewrite (generate_ldef_constraint_eq G env base_ty rst_ty cenv x
                 (Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name)))
                 ck ckty (merge (merge [bi] s0) s1) b st Hckx Hckty
                 (assign_lexp_Eite_var i (bool_type, (ck, Some i)) e0 e
                    ([ty], (ck, name)) bi s0 s1 st Hbi H0 H1) Hb) in Hc1.
      apply OK_pair_inv in Hc1 as (? & ?); subst c1 v1.
      (** the move *)
      subst cet.
      eapply preserves_on_fresh_names
        with (news := [bi])
             (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      - constructor; [intros []|constructor].
      - intros z [Hz|[]]; subst z. exact Hfr.
      - intros z [Hz|[]]; subst z. exact Hsc.
      - intros dlt Hsat.
        assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                      ⊑ hm_ext dlt [b]).
        { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
          exact (Hsat _ (in_eq _ _)). }
        rewrite Forall_app. split.
        + constructor; [|constructor]. split.
          * cbn [fst]. intros z Hz.
            apply (ite_lhs_members ckty s0 s1 [bi] z);
              [intros y Hy; right; apply in_merge_right, in_merge_right; exact Hy
              |exact Hz].
          * exists b. split; [reflexivity|]. right. split; [|exact Hc0].
            intros [Hc|[]]. exact (Hne (@Coq.Init.Logic.eq_sym _ _ _ Hc)).
        + (** the flag's own equation, if there is one *)
          destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
          * apply generate_leqns_constraints_nil in Hc2 as (? & _); subst c2.
            constructor.
          * apply generate_leqns_cons_inv in Hc2 as (d1 & w1 & d2 & Hd1 & Hd2 & ?).
            destruct (init_eq_constraint i ck ckty bi _ d1 w1 Hcki Hckty Hbi Hd1)
              as (sw & ? & Hsw & ?); subst d1 w1.
            apply generate_leqns_constraints_nil in Hd2 as (? & _); subst d2.
            subst c2. rewrite app_nil_r. constructor; [|constructor]. split.
            -- cbn [fst]. intros z Hz.
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [left; apply in_merge_left; exact Hz
                 |left; apply in_merge_left, in_merge_right; exact (Hsw z Hz)].
            -- exists bi. split; [reflexivity|]. left. now left.
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
        constraint, and the [ite]'s first branch would have nothing to be below. *)
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
        ~ In bi scope ->
        ~ In bp scope ->
        ~ In bi (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
        ~ In bp (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
        b <> bi -> b <> bp -> bp <> bi ->
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
        preserves_on scope ce cet.
    Proof.
      intros x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs
        Hckx Hckpx Hckty Hb Hbi Hbp H0 H1 Hsci Hscp Hfri Hfrp
        Hnei Hnep Hpi Heqs Hsrc Htgt.
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
      (** the move *)
      subst c2 cet.
      eapply preserves_on_fresh_names
        with (news := [bp; bi])
             (L := merge (merge [rst_ty] ckty) (merge s0 s1)).
      - constructor; [intros [Hc|[]]; exact (Hpi (@Coq.Init.Logic.eq_sym _ _ _ Hc))
                     |constructor; [intros []|constructor]].
      - intros z [Hz|[Hz|[]]]; subst z; [exact Hfrp|exact Hfri].
      - intros z [Hz|[Hz|[]]]; subst z; [exact Hscp|exact Hsci].
      - intros dlt Hsat.
        assert (Hc0 : hm_ext dlt (merge (merge [rst_ty] ckty) (merge s0 s1))
                      ⊑ hm_ext dlt [b]).
        { unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
          exact (Hsat _ (in_eq _ _)). }
        rewrite Forall_app. split.
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
          * exists b. split; [reflexivity|]. right. split; [|exact Hc0].
            intros [Hc|[Hc|[]]];
              [exact (Hnep (@Coq.Init.Logic.eq_sym _ _ _ Hc))
              |exact (Hnei (@Coq.Init.Logic.eq_sym _ _ _ Hc))].
        + rewrite Forall_app. split.
          * (** the fresh variable's own equation *)
            constructor; [|constructor]. split.
            -- cbn [fst]. intros z Hz. left.
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [apply in_merge_left; exact Hz|].
               apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                 [apply in_merge_left, in_merge_right; exact (Hsw z Hz)
                 |apply in_merge_right, in_merge_right; exact Hz].
            -- exists bp. split; [reflexivity|]. left. now left.
          * (** and the flag's, if the pass created one *)
            destruct Heqs as [Heqs|(Hcki & Heqs)]; subst eqs.
            -- apply generate_leqns_constraints_nil in Hd2 as (? & _); subst d2.
               constructor.
            -- apply generate_leqns_cons_inv in Hd2
                 as (f1 & y1 & f2 & Hf1 & Hf2 & ?).
               destruct (init_eq_constraint i ck ckty bi _ f1 y1
                           Hcki Hckty Hbi Hf1) as (swi & ? & Hswi & ?);
                 subst f1 y1.
               apply generate_leqns_constraints_nil in Hf2 as (? & _); subst f2.
               subst d2. rewrite app_nil_r. constructor; [|constructor]. split.
               ++ cbn [fst]. intros z Hz. left.
                  apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
                    [apply in_merge_left; exact Hz
                    |apply in_merge_left, in_merge_right; exact (Hswi z Hz)].
               ++ exists bi. split; [reflexivity|]. left. right. now left.
    Qed.

  End NormFbyNode.

End SecLusNormFby.
