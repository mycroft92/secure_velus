(* Indexed-semantics observation layer for NLustre noninterference.

   This file starts the thesis-specific noninterference development on the
   source language side.  The first step is to formalise the paper's
   [(⊑ t)-projected Stream] notion directly over the indexed semantics used by
   Vélus:

   - raw program variables are observed through a generated local security env;
   - a ground instantiation assigns lattice classes to generated security ids;
   - projection keeps exactly those raw variables whose security class is at
     most the observation level [t].

   The later semantic theorems should be stated against the relational form
   [history_low_eq], while the concrete projector [project_history_le_t] keeps a
   paper-facing version of the same notion. *)

From Coq Require Import List Sorting.Permutation Lia Wf_nat PArith.BinPos Arith.PeanoNat.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSNONINTERFERENCE
  (Import Ids    : IDS)
  (Import Lat    : Lattice)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import SecT   : SECTYPES Lat)
  (Import CESyn  : CESYNTAX Op)
  (Import SynNL  : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (NLCaus        : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING
       CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING).

  (** Vocabulary alignment with the papers.

      The noninterference papers use:
      - [s] for a ground instantiation of symbolic security variables;
      - [ρ] for the generated constraints attached to a node signature.

      In the Coq development we standardise this as follows:
      - [dlt] is the ground instantiation used throughout [SecTypes] and
        [SIFSignature];
      - [sig.(s_constraints)] is exactly the paper's [ρ];
      - "ρ is satisfied by s" is formalised as [signature_satisfied dlt sig].

      Keeping this translation explicit avoids introducing parallel notation in
      the noninterference proof. *)
  Definition ground_instantiation : Type := ident -> Lat.t.

  Definition signature_constraints (sig : signature) : list constraint :=
    sig.(s_constraints).

  Definition signature_satisfied
    (dlt : ground_instantiation) (sig : signature) : Prop :=
    SecT.listSatisfiable dlt (signature_constraints sig).

  (** The paper's [Γ] is not an arbitrary map in this development.  It is the
      node-local security environment produced by [NameInterface] for the
      current node and then consumed by [SecNLusTyping]. *)
  Section GENERATED_LOW_OBSERVATION.
    Variable all_nodes : global.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.
    Variable n : node.
    Variable ty_env : local_sec_env.
    Variable dlt : ground_instantiation.
    Variable t : Lat.t.

    Hypothesis Henvsgen :
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names).
    Hypothesis Hfindenv :
      find_node_env n.(n_name) envs = Some ty_env.

    (** One raw variable is observable at level [t] when its generated security
        identifier is mapped by the ground instantiation below [t].

        Relation to the paper:
        this is the pointwise membership test behind the set [X⊑t], where the
        source-side [Γ] is represented here by the generated local typing
        environment [ty_env] for node [n]. *)
    Definition low_var (x : ident) : Prop :=
      exists α, Env.find x ty_env = Some α /\ dlt α ⊑ t.

    Definition low_var_dec (x : ident) : {low_var x} + {~ low_var x}.
    Proof.
      unfold low_var.
      destruct (Env.find x ty_env) as [α|] eqn:Hfind.
      - destruct (Lat.order_dec (dlt α) t) as [Hle|Hnle].
        + left. now exists α.
        + right. intros (α' & Hfind' & Hle').
          inv Hfind'. contradiction.
      - right. intros (α & Hfind' & _).
        discriminate Hfind'.
    Defined.

    Definition low_var_b (x : ident) : bool :=
      if low_var_dec x then true else false.

    (** Boolean reflection of [low_var].

        Relation to the paper:
        this is the decidable form of the judgment [x ∈ X⊑t]. *)
    Lemma low_var_b_spec:
      forall x,
        low_var_b x = true <-> low_var x.
    Proof.
      intros x.
      unfold low_var_b.
      destruct (low_var_dec x); split; intro H; auto; discriminate.
    Qed.

    (** List-based representative of the paper's low-observation set [X⊑t].

        Since the mechanisation uses finite lists of raw variables, we realise
        the paper's set notation by filtering [X] with [low_var]. *)
    Definition vars_le_t (X : list ident) : list ident :=
      filter low_var_b X.

    (** Membership characterisation for [vars_le_t].

        Relation to the paper:
        this is the formal link between the paper's set notation [X⊑t] and the
        finite list representation used in Coq. *)
    Lemma vars_le_t_spec:
      forall X x,
        In x (vars_le_t X) <-> In x X /\ low_var x.
    Proof.
      intros X x.
      unfold vars_le_t.
      rewrite filter_In.
      rewrite low_var_b_spec.
      tauto.
    Qed.

    (** Generic projector on one semantic instant environment.

        This helper is independent of security: it keeps exactly the bindings
        of one semantic snapshot whose keys lie in [xs].  The security-specific
        projector below instantiates it with [vars_le_t X]. *)
    Definition project_env_on (xs : list ident) (R : env) : env :=
      fold_right
        (fun x acc =>
           match Env.find x R with
           | Some v => Env.add x v acc
           | None => acc
           end)
        (Env.empty _)
        xs.

    (** Pointwise behaviour of the generic projector.

        Relation to the paper:
        this is the finite-map form of "projection keeps exactly the chosen
        observable variables and drops the rest". *)
    Lemma project_env_on_find:
      forall xs R x,
        Env.find x (project_env_on xs R) =
        if in_dec ident_eq_dec x xs then Env.find x R else None.
    Proof.
      induction xs as [|y xs IH]; intros R x; simpl.
      - destruct (in_dec ident_eq_dec x []); [contradiction|apply Env.gempty].
      - destruct (Env.find y R) as [v|] eqn:Hy.
        + destruct (ident_eq_dec x y) as [Heq|Hneq].
          * subst x.
            rewrite Env.gss.
            rewrite Hy.
            destruct (ident_eq_dec y y) as [_|Hneq']; [reflexivity|contradiction].
          * rewrite Env.gso by exact Hneq.
            rewrite IH.
            destruct (in_dec ident_eq_dec x (y :: xs)) as [Hin|Hin].
            -- simpl in Hin. destruct Hin as [Heq|Hin'].
               ++ subst. contradiction.
               ++ destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hin''].
                  ** destruct (ident_eq_dec y x) as [Heq'|Hneq'].
                     --- exfalso. apply Hneq. symmetry. exact Heq'.
                     --- reflexivity.
                  ** contradiction.
            -- destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hinxs'].
               ++ exfalso. apply Hin. right. exact Hinxs.
               ++ destruct (ident_eq_dec y x) as [Heq'|Hneq'].
                  ** exfalso. apply Hneq. symmetry. exact Heq'.
                  ** reflexivity.
        + rewrite IH.
          destruct (in_dec ident_eq_dec x (y :: xs)) as [Hin|Hin].
          * simpl in Hin. destruct Hin as [Heq|Hin'].
            -- subst x.
               rewrite Hy.
               destruct (in_dec ident_eq_dec y xs) as [Hinxs|Hinxs'].
               ++ destruct (ident_eq_dec y y) as [Heq|Hneq']; [reflexivity|contradiction].
               ++ destruct (ident_eq_dec y y) as [Heq|Hneq']; [reflexivity|contradiction].
            -- destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hin''].
               ++ destruct (ident_eq_dec y x) as [Heq|Hneq]; [reflexivity|reflexivity].
               ++ contradiction.
          * destruct (in_dec ident_eq_dec x xs) as [Hin'|Hin''].
            -- exfalso. apply Hin. right. exact Hin'.
            -- destruct (ident_eq_dec y x) as [Heq|Hneq].
               ++ subst x. exfalso. apply Hin. now left.
               ++ reflexivity.
    Qed.

    (** Paper-style [(⊑ t)] projection for one indexed environment snapshot.

        It keeps exactly the bindings for raw variables in the low-observation
        set [X⊑t]. *)
    Definition project_env_le_t (X : list ident) (R : env) : env :=
      project_env_on (vars_le_t X) R.

    (** Paper-style [(⊑ t)] projection for an indexed history.

        Relation to the paper:
        this is the direct indexed-semantics counterpart of [H|X⊑t]. *)
    Definition project_history_le_t (X : list ident) (H : history) : history :=
      fun k => project_env_le_t X (H k).

    (** Relational low-equivalence for one indexed environment snapshot.

        This is the proof-oriented version of the paper's projection notion:
        two snapshots are low-equivalent when they agree on every variable in
        [X⊑t]. *)
    Definition env_low_eq (X : list ident) (R R' : env) : Prop :=
      forall x,
        In x X ->
        low_var x ->
        Env.find x R = Env.find x R'.

    (** Relational low-equivalence for indexed histories.

        The later noninterference theorem should quantify over this relation,
        since the semantic switching lemmas are pointwise over instants. *)
    Definition history_low_eq (X : list ident) (H H' : history) : Prop :=
      forall k,
        env_low_eq X (H k) (H' k).

    (** Prefix-bounded low-equivalence for indexed histories.

        Relation to the paper:
        the public theorem talks about whole-stream equality on low
        observations, but the internal proof for [EqFby] and recursive calls
        proceeds by induction on the current instant.  This prefix form is the
        proof-oriented notion of "the two runs agree on all low observations
        up to time [k]". *)
    Definition history_low_eq_upto (X : list ident) (H H' : history) (k : nat) : Prop :=
      forall j,
        j <= k ->
        env_low_eq X (H j) (H' j).

    (** Equality of the concrete projected environments.

        This keeps the paper-facing projection operator available while the
        semantic proofs work with [env_low_eq]. *)
    Definition projected_env_eq (X : list ident) (R R' : env) : Prop :=
      forall x,
        Env.find x (project_env_le_t X R) =
        Env.find x (project_env_le_t X R').

    Definition projected_history_eq (X : list ident) (H H' : history) : Prop :=
      forall k x,
        Env.find x (project_history_le_t X H k) =
        Env.find x (project_history_le_t X H' k).

    (** Low observable bindings survive the concrete projection unchanged.

        Relation to the paper:
        this is the finite-map reading of "the projection keeps all low
        variables in [X⊑t]". *)
    Lemma project_env_le_t_find_low:
      forall X R x,
        In x X ->
        low_var x ->
        Env.find x (project_env_le_t X R) = Env.find x R.
    Proof.
      intros X R x Hin Hlow.
      unfold project_env_le_t.
      rewrite project_env_on_find.
      destruct (in_dec ident_eq_dec x (vars_le_t X)) as [Hin'|Hin']; [reflexivity|].
      exfalso.
      apply Hin'.
      apply vars_le_t_spec.
      now split.
    Qed.

    (** Non-observable bindings are removed by the concrete projection.

        Relation to the paper:
        this is the finite-map reading of "variables outside [X⊑t] are not
        observable in the projection". *)
    Lemma project_env_le_t_find_excluded:
      forall X R x,
        ~ In x X \/ ~ low_var x ->
        Env.find x (project_env_le_t X R) = None.
    Proof.
      intros X R x Hexcl.
      unfold project_env_le_t.
      rewrite project_env_on_find.
      destruct (in_dec ident_eq_dec x (vars_le_t X)) as [Hin|Hin]; [|reflexivity].
      exfalso.
      apply vars_le_t_spec in Hin.
      tauto.
    Qed.

    (** Relational low-equivalence implies equality of concrete projections.

        Relation to the paper:
        this is the "if two runs agree on low variables, then their projected
        observations are equal" direction. *)
    Lemma env_low_eq_projected_env_eq:
      forall X R R',
        env_low_eq X R R' ->
        projected_env_eq X R R'.
    Proof.
      intros X R R' Hlow x.
      destruct (in_dec ident_eq_dec x X) as [Hin|Hnin].
      - destruct (low_var_dec x) as [Hobs|Hnobs].
        + rewrite !project_env_le_t_find_low by assumption.
          now apply Hlow.
        + rewrite !project_env_le_t_find_excluded by now right.
          reflexivity.
      - rewrite !project_env_le_t_find_excluded by now left.
        reflexivity.
    Qed.

    (** Equality of concrete projections recovers relational low-equivalence.

        Relation to the paper:
        this is the converse direction saying that the concrete projected
        histories carry exactly the same low-observation information as
        [env_low_eq]. *)
    Lemma projected_env_eq_env_low_eq:
      forall X R R',
        projected_env_eq X R R' ->
        env_low_eq X R R'.
    Proof.
      intros X R R' Hproj x Hin Hlow.
      specialize (Hproj x).
      rewrite !project_env_le_t_find_low in Hproj; auto.
    Qed.

    (** Pointwise lifting from relational low-equivalence of histories to
        equality of their projected observations.

        Relation to the paper:
        this is the indexed-history form of equality of projected streams. *)
    Lemma history_low_eq_projected_history_eq:
      forall X H H',
        history_low_eq X H H' ->
        projected_history_eq X H H'.
    Proof.
      intros X H H' Hlow k x.
      apply env_low_eq_projected_env_eq.
      apply Hlow.
    Qed.

    (** Pointwise lifting from equality of projected observations back to the
        relational low-equivalence used in later proofs.

        Relation to the paper:
        this shows that the relational and concrete projector views of
        [H|X⊑t] are equivalent in the indexed setting. *)
    Lemma projected_history_eq_history_low_eq:
      forall X H H',
        projected_history_eq X H H' ->
        history_low_eq X H H'.
    Proof.
      intros X H H' Hproj k.
      apply projected_env_eq_env_low_eq.
      intros x.
      apply Hproj.
    Qed.

    (** Whole-history low-equivalence implies every finite prefix.

        Relation to the paper:
        this is the trivial restriction step used when a global semantic
        hypothesis is fed into an induction on the current instant. *)
    Lemma history_low_eq_upto_of_history_low_eq:
      forall X H H' k,
        history_low_eq X H H' ->
        history_low_eq_upto X H H' k.
    Proof.
      intros X H H' k Hlow j _.
      apply Hlow.
    Qed.

    (** Prefix low-equivalence weakens along the observed variable set.

        Relation to the paper:
        once a prefix proof is established on a larger visible set, it can be
        restricted immediately to any smaller interface such as the node
        outputs. *)
    Lemma history_low_eq_upto_weaken:
      forall X Y H H' k,
        (forall x, In x Y -> In x X) ->
        history_low_eq_upto X H H' k ->
        history_low_eq_upto Y H H' k.
    Proof.
      intros X Y H H' k Hsub Hlow j Hj x Hin Hobs.
      eapply Hlow; eauto.
    Qed.

    (** Prefix low-equivalence is monotone in the prefix bound.

        Relation to the paper:
        the delayed proof repeatedly reuses an already-established prefix fact
        at strictly earlier instants. *)
    Lemma history_low_eq_upto_monotone:
      forall X H H' k1 k2,
        k1 <= k2 ->
        history_low_eq_upto X H H' k2 ->
        history_low_eq_upto X H H' k1.
    Proof.
      intros X H H' k1 k2 Hle Hlow j Hj.
      eapply Hlow; lia.
    Qed.

    (** Repackage pointwise prefix equalities as prefix low-equivalence.

        Relation to the paper:
        the causal proof naturally produces one low-equality obligation per
        variable, but the recursive node theorems consume the relational
        history view.  This lemma is the prefix-bounded version of that
        repackaging step. *)
    Lemma history_low_eq_upto_from_Forall_pointwise:
      forall X H H' k,
        Forall
          (fun x =>
             low_var x ->
             forall j, j <= k -> Env.find x (H j) = Env.find x (H' j))
          X ->
        history_low_eq_upto X H H' k.
    Proof.
      intros X H H' k Hpts j Hj x Hin Hlow.
      eapply Forall_forall in Hpts; [|exact Hin].
      eapply Hpts; eauto.
    Qed.

    (** Build one larger prefix from the previous prefix plus the current instant.

        Relation to the paper:
        the successor step of the indexed proof splits naturally into:

        - equality already known on the earlier prefix; and
        - one fresh equality proof at the current instant.

        This lemma packages exactly that reconstruction back into
        [history_low_eq_upto]. *)
    Lemma history_low_eq_upto_succ_intro:
      forall X H H' k,
        history_low_eq_upto X H H' k ->
        (forall x, In x X -> low_var x ->
           Env.find x (H (S k)) = Env.find x (H' (S k))) ->
        history_low_eq_upto X H H' (S k).
    Proof.
      intros X H H' k Hprev Hcur j Hj x Hin Hlow.
      destruct (Nat.eq_dec j (S k)) as [Heq|Hneq].
      - subst j. eapply Hcur; eauto.
      - eapply Hprev; eauto. lia.
    Qed.

    (** Free-variable bounds for generated symbolic types.

        Relation to the paper:
        these lemmas connect the syntax-directed symbolic type assigners from
        [SecCETyping] to the low-observation proof.  They show that whenever a
        raw source variable is free in a clock or expression, the security
        identifier looked up for that variable contributes to the generated
        symbolic type, hence its instantiated lattice class is bounded by the
        interpretation of that type. *)

    Lemma singleton_type_bound:
      forall alpha,
        dlt alpha ⊑ SecT.hm_ext dlt [alpha].
    Proof.
      intro alpha.
      simpl.
      apply join_bound1.
    Qed.

    Lemma left_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st1 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      eapply order_trans.
      - apply SecT.hm_ext_concat_l.
      - apply SecT.hm_ext_concat_l.
    Qed.

    Lemma middle_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st2 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      eapply order_trans.
      - apply SecT.hm_ext_concat_r.
      - apply SecT.hm_ext_concat_l.
    Qed.

    Lemma right_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st3 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      apply SecT.hm_ext_concat_r.
    Qed.

    Lemma assign_clk_type_free_bound:
      forall base ck st x,
        Is_free_in_clock x ck ->
        SECCETYPING.assign_clk_type ty_env base ck = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros base ck.
      induction ck as [|ck IH y b]; intros st x Hfree Hassign.
      - inversion Hfree.
      - eapply SECCETYPING.assign_clk_inv in Hassign as
            (st' & yty & Hst & Hck & Hfindy).
        apply CEIsF.Is_free_in_clock_disj in Hfree as [Heq|Hfree].
        + subst x.
          exists yty.
          split; [exact Hfindy|].
          subst st.
          eapply order_trans.
          * apply singleton_type_bound.
          * apply SecT.hm_ext_concat_r.
        + edestruct IH as (alpha & Hfind & Hbound); eauto.
          exists alpha.
          split; [exact Hfind|].
          subst st.
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
    Qed.

    Lemma assign_exp_type_free_bound:
      forall e st x,
        Is_free_in_exp x e ->
        SECCETYPING.assign_exp_type ty_env e = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros e.
      induction e as [c|y ty|e IHe y b|op e IHe ty|op e1 IHe1 e2 IHe2 ty];
        intros st x Hfree Hassign; simpl in Hassign.
      - inversion Hfree.
      - inversion Hfree; subst.
        destruct (Env.find y ty_env) as [yty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst st.
        exists yty.
        split; [reflexivity|].
        apply singleton_type_bound.
      - apply CEIsF.Is_free_in_when_disj in Hfree as [Heq|Hfree].
        + destruct (SECCETYPING.assign_exp_type ty_env e) as [ety|] eqn:He; try discriminate.
          destruct (Env.find y ty_env) as [yty|] eqn:Hfindy; try discriminate.
          inversion Hassign; subst st.
          subst x.
          exists yty.
          split; [exact Hfindy|].
          eapply order_trans.
          * apply singleton_type_bound.
          * apply SecT.hm_ext_concat_r.
        + destruct (SECCETYPING.assign_exp_type ty_env e) as [ety|] eqn:He; try discriminate.
          destruct (Env.find y ty_env) as [yty|] eqn:Hfindy; try discriminate.
          assert (Hsame : Some ety = Some ety) by reflexivity.
          destruct (IHe ety _ Hfree Hsame) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
      - inversion Hfree; subst.
        eauto.
      - destruct (SECCETYPING.assign_exp_type ty_env e1) as [e1ty|] eqn:He1; try discriminate.
        destruct (SECCETYPING.assign_exp_type ty_env e2) as [e2ty|] eqn:He2; try discriminate.
        inversion Hfree as [| | | |x' op' e1' e2' ty' Hdisj]; subst; clear Hfree.
        destruct Hdisj as [Hfree1|Hfree2].
        + assert (Hsame1 : Some e1ty = Some e1ty) by reflexivity.
          destruct (IHe1 e1ty _ Hfree1 Hsame1) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
        + assert (Hsame2 : Some e2ty = Some e2ty) by reflexivity.
          destruct (IHe2 e2ty _ Hfree2 Hsame2) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_r.
    Qed.

    Lemma assign_cexp_type_free_bound:
      forall ce st x,
        Is_free_in_cexp x ce ->
        SECCETYPING.assign_cexp_type ty_env ce = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros ce st x Hfree.
      revert st.
      induction Hfree as
          [i ce_t ce_f
          |i ce_t ce_f y Hfree_t IHt
          |i ce_t ce_f y Hfree_f IHf
          |y b ce_t ce_f Hfree_b
          |y b ce_t ce_f Hfree_t IHt
          |y b ce_t ce_f Hfree_f IHf
          |e y Hfree_e];
        intros st Hassign; simpl in Hassign.
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        exists ity.
        split; [reflexivity|].
        eapply order_trans.
        + apply singleton_type_bound.
        + apply left_triple_type_bound.
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_t : Some tty = Some tty) by reflexivity.
        destruct (IHt tty Hsame_t) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (middle_triple_type_bound [ity] tty fty).
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_f : Some fty = Some fty) by reflexivity.
        destruct (IHf fty Hsame_f) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (right_triple_type_bound [ity] tty fty).
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        destruct (assign_exp_type_free_bound b bty y Hfree_b Hb) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply left_triple_type_bound.
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_t : Some tty = Some tty) by reflexivity.
        destruct (IHt tty Hsame_t) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (middle_triple_type_bound bty tty fty).
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_f : Some fty = Some fty) by reflexivity.
        destruct (IHf fty Hsame_f) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (right_triple_type_bound bty tty fty).
      - eapply assign_exp_type_free_bound; eauto.
    Qed.

    Lemma assign_aexp_type_free_bound:
      forall base ck e ckty ety x,
        Is_free_in_aexp x ck e ->
        SECCETYPING.assign_clk_type ty_env base ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt (ckty ⊔ ety).
    Proof.
      intros base ck e ckty ety x Hfree Hck He.
      inversion Hfree; subst.
      - match goal with
        | Hexp : Is_free_in_exp x e |- _ =>
            destruct (assign_exp_type_free_bound e ety x Hexp He)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_r.
      - match goal with
        | Hckfree : Is_free_in_clock x ck |- _ =>
            destruct (assign_clk_type_free_bound base ck ckty x Hckfree Hck)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_l.
    Qed.

    Lemma assign_caexp_type_free_bound:
      forall base ck ce ckty cety x,
        Is_free_in_caexp x ck ce ->
        SECCETYPING.assign_clk_type ty_env base ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt (ckty ⊔ cety).
    Proof.
      intros base ck ce ckty cety x Hfree Hck Hce.
      inversion Hfree; subst.
      - match goal with
        | Hcefree : Is_free_in_cexp x ce |- _ =>
            destruct (assign_cexp_type_free_bound ce cety x Hcefree Hce)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_r.
      - match goal with
        | Hckfree : Is_free_in_clock x ck |- _ =>
            destruct (assign_clk_type_free_bound base ck ckty x Hckfree Hck)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_l.
    Qed.

    (** Paper-style simple security step.

        Relation to the paper:
        this is the lattice-level core of the paper's "simple security"
        argument for simple equations.  If a defined variable [x] is low at
        observation level [t], and the current typing constraints show that a
        contributor [y] flows into the symbolic left-hand side [lhs] that is
        bounded by [x]'s security identifier, then [y] is low as well. *)
    Lemma simple_security:
      forall lhs x y xty alpha,
        Env.find x ty_env = Some xty ->
        Env.find y ty_env = Some alpha ->
        dlt alpha ⊑ SecT.hm_ext dlt lhs ->
        SecT.satisfiable dlt lhs [xty] ->
        low_var x ->
        low_var y.
    Proof.
      intros lhs x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx.
      destruct Hlowx as (alpha_x & Hfindx' & Hlowx).
      rewrite Hfindx in Hfindx'.
      inversion Hfindx'; subst alpha_x.
      exists alpha.
      split; [exact Hfindy|].
      eapply order_trans; [exact Hbound|].
      eapply order_trans; [exact Hsat|].
      simpl.
      apply join_least_upper_bound.
      - exact Hlowx.
      - apply bottom_is_bottom.
    Qed.

    (** Low-dependency propagation for [EqDef] right-hand sides.

        Relation to the paper:
        this is the simple-security instantiation for NLustre [EqDef]:
        when the defined variable is low, every free variable of the guarded
        combinational expression on the right-hand side is low as well. *)
    Lemma simple_security_caexp:
      forall base_ty rst_ty x ck ce xty ckty cety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        Is_free_in_caexp y ck ce ->
        low_var y.
    Proof.
      intros base_ty rst_ty x ck ce xty ckty cety y
             Hfindx Hck Hce Hsat Hlowx Hfree.
      destruct (assign_caexp_type_free_bound base_ty ck ce ckty cety y Hfree Hck Hce)
        as (alpha & Hfindy & Hbound).
      assert (Hbound' : dlt alpha ⊑ SecT.hm_ext dlt ((([rst_ty] ⊔ ckty) ⊔ cety))).
      { eapply order_trans; [exact Hbound|].
        rewrite SymTypes.MergeFacts.merge_assoc.
        apply SecT.hm_ext_concat_r. }
      apply (simple_security ((([rst_ty] ⊔ ckty) ⊔ cety)) x y xty alpha
               Hfindx Hfindy Hbound' Hsat Hlowx).
    Qed.

    (** Low-dependency propagation for [EqFby] right-hand sides.

        Relation to the paper:
        this is the simple-security instantiation for NLustre [EqFby]:
        when the defined memory variable is low, every free variable of the
        guarded source expression feeding the delay is low as well. *)
    Lemma simple_security_aexp:
      forall base_ty rst_ty x ck e xty ckty ety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        Is_free_in_aexp y ck e ->
        low_var y.
    Proof.
      intros base_ty rst_ty x ck e xty ckty ety y
             Hfindx Hck He Hsat Hlowx Hfree.
      destruct (assign_aexp_type_free_bound base_ty ck e ckty ety y Hfree Hck He)
        as (alpha & Hfindy & Hbound).
      assert (Hbound' : dlt alpha ⊑ SecT.hm_ext dlt ((([rst_ty] ⊔ ckty) ⊔ ety))).
      { eapply order_trans; [exact Hbound|].
        rewrite SymTypes.MergeFacts.merge_assoc.
        apply SecT.hm_ext_concat_r. }
      apply (simple_security ((([rst_ty] ⊔ ckty) ⊔ ety)) x y xty alpha
               Hfindx Hfindy Hbound' Hsat Hlowx).
    Qed.

    (** Low-dependency propagation for plain call arguments.

        Relation to the paper:
        node calls evaluate plain source expressions as actual arguments.
        This is the non-clocked counterpart of [simple_security_aexp], used
        to transport low observability from a low call input formal back to
        the free variables of the matching caller-side actual expression. *)
    Lemma simple_security_exp:
      forall x e xty ety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ety [xty] ->
        low_var x ->
        Is_free_in_exp y e ->
        low_var y.
    Proof.
      intros x e xty ety y
             Hfindx He Hsat Hlowx Hfree.
      destruct (assign_exp_type_free_bound e ety y Hfree He)
        as (alpha & Hfindy & Hbound).
      apply (simple_security ety x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx).
    Qed.

    (** Switching a guarded combinational expression across low-equivalent
        indexed histories.

        Relation to the paper:
        this is the indexed-history counterpart of the paper step saying that a
        simple RHS computes the same stream in both runs when all of its low
        dependencies agree. *)
    Lemma sem_caexp_switch_history_low:
      forall X bk H H' ck ce xs,
        history_low_eq X H H' ->
        (forall y, Is_free_in_caexp y ck ce -> In y X /\ low_var y) ->
        sem_caexp bk H ck ce xs ->
        sem_caexp bk H' ck ce xs.
    Proof.
      intros X bk H H' ck ce xs Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_caexp_instant_switch_env
              (bk k) (H k) (H' k) ck ce (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck =>
                     let Hdep := Hfree y (FreeCAexp2 _ _ _ Hyck) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 | or_intror Hyce =>
                     let Hdep := Hfree y (FreeCAexp1 _ _ _ Hyce) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 end))).
      exact Hsem.
    Qed.

    (** Switching a guarded source expression across low-equivalent indexed
        histories.

        Relation to the paper:
        this is the indexed-history counterpart of the [fby] simple case: the
        stream feeding the delay is preserved across the two low-equivalent
        runs once all low dependencies agree. *)
    Lemma sem_aexp_switch_history_low:
      forall X bk H H' ck e xs,
        history_low_eq X H H' ->
        (forall y, Is_free_in_aexp y ck e -> In y X /\ low_var y) ->
        sem_aexp bk H ck e xs ->
        sem_aexp bk H' ck e xs.
    Proof.
      intros X bk H H' ck e xs Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_aexp_instant_switch_env
              (bk k) (H k) (H' k) ck e (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck =>
                     let Hdep := Hfree y (freeAexp2 _ _ _ Hyck) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 | or_intror Hyexp =>
                     let Hdep := Hfree y (freeAexp1 _ _ _ Hyexp) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 end))).
      exact Hsem.
    Qed.

    (** Switching a list of actual arguments across low-equivalent indexed
        histories.

        Relation to the paper:
        this is the list-valued version of the simple semantic switching step
        used for call equations: if every free variable of every actual
        argument is low and agrees across the two runs, then the actual
        argument tuple evaluates to the same stream of values. *)
    Lemma sem_exps_switch_history_low:
      forall X bk H H' es ls,
        history_low_eq X H H' ->
        (forall y, Exists (Is_free_in_exp y) es -> In y X /\ low_var y) ->
        sem_exps bk H es ls ->
        sem_exps bk H' es ls.
    Proof.
      intros X bk H H' es ls Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_exps_instant_switch_env
              (bk k) (H k) (H' k) es (ls k)
              (fun y Hy =>
                 let Hdep := Hfree y Hy in
                 let Hin := proj1 Hdep in
                 let Hobs := proj2 Hdep in
                 Hlow k y Hin Hobs))).
      exact Hsem.
    Qed.

    (** Recover one component of a semantic variable tuple.

        Relation to the paper:
        call equations and output-facing corollaries need to move between the
        tuple semantics [sem_vars_instant] and one concrete variable position.
        This lemma is the finite-list bridge for that extraction step. *)
    Lemma sem_vars_instant_nth_error:
      forall R xs vs i x v,
        sem_vars_instant R xs vs ->
        nth_error xs i = Some x ->
        nth_error vs i = Some v ->
        sem_var_instant R x v.
    Proof.
      intros R xs vs i x v Hvars Hnthx Hnthv.
      destruct
        (SecT.Forall2_nth_error_inv
           _ _ (sem_var_instant R) xs vs i x Hvars Hnthx)
        as (v' & Hnthv' & Hvar).
        rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. exact Hvar.
    Qed.

    (** Recover one component of a semantic actual-argument tuple.

        Relation to the paper:
        the call case reasons about one low formal input at a time, and thus
        needs the corresponding one actual expression/value pair extracted
        from the list semantics [sem_exps_instant]. *)
    Lemma sem_exps_instant_nth_error:
      forall b R es vs i e v,
        sem_exps_instant b R es vs ->
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        sem_exp_instant b R e v.
    Proof.
      intros b R es vs i e v Hexp Hnthe Hnthv.
      destruct
        (SecT.Forall2_nth_error_inv
           _ _ (sem_exp_instant b R) es vs i e Hexp Hnthe)
        as (v' & Hnthv' & Hv).
      rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. exact Hv.
    Qed.

    (** Lift one free variable at a concrete actual-argument position into
        the NLustre call-dependency predicate.

        Relation to the paper:
        call causality is recorded over the whole actual-argument list.  The
        noninterference proof often isolates one list position first, then
        needs to repackage that pointwise free-variable fact back into
        [Is_free_in_aexps] to invoke the node-level dependency hypothesis. *)
    Lemma nth_error_free_in_aexps:
      forall es i e y ck,
        nth_error es i = Some e ->
        Is_free_in_exp y e ->
        Is_free_in_aexps y ck es.
    Proof.
      intros es i e y ck Hnth Hfree.
      apply freeAexps1.
      revert i e Hnth Hfree.
      induction es as [|e0 es IH]; intros i e Hnth Hfree.
      - destruct i; inversion Hnth.
      - destruct i as [|i].
        + simpl in Hnth. inversion Hnth; subst e.
          constructor. exact Hfree.
        + simpl in Hnth.
          constructor 2.
          eapply IH; eauto.
    Qed.

    (** Repackage tuple-stream equality as low-equivalence on the underlying
        semantic histories.

        Relation to the paper:
        recursive call proofs often obtain equality of the caller-produced
        argument tuples directly.  This lemma turns that extensional stream
        equality into the history-based observation relation consumed by the
        recursive output theorem. *)
    Lemma history_low_eq_upto_of_sem_vars_eq:
      forall xs H H' vs vs' k,
        sem_vars H xs vs ->
        sem_vars H' xs vs' ->
        (forall j, j <= k -> vs j = vs' j) ->
        history_low_eq_upto xs H H' k.
    Proof.
      intros xs H H' vs vs' k Hvars Hvars' Heq j Hj x Hin _.
      destruct (SecT.In_nth_error_ex _ _ _ Hin) as [i Hnthx].
      specialize (Hvars j).
      specialize (Hvars' j).
      pose proof (Heq j Hj) as Hvals.
      destruct (nth_error (vs j) i) as [v|] eqn:Hnthv.
      - eapply sem_vars_instant_nth_error in Hvars; eauto.
        pose proof Hnthv as Hnthv'.
        rewrite Hvals in Hnthv'.
        eapply sem_vars_instant_nth_error in Hvars'; eauto.
        unfold sem_var_instant in Hvars, Hvars'.
        rewrite Hvars, Hvars'.
        reflexivity.
      - assert (Hi : i < List.length xs).
        {
          apply nth_error_Some.
          rewrite Hnthx.
          discriminate.
        }
        pose proof (Forall2_length _ _ _ Hvars) as Hlen.
        assert (Hi_vs : i < List.length (vs j)).
        { rewrite <- Hlen. exact Hi. }
        pose proof (nth_error_nth' (vs j) i absent Hi_vs) as Hsome.
        rewrite Hnthv in Hsome.
        discriminate.
    Qed.

    (** Prefix preservation for lists of source expressions.

        Relation to the paper:
        call equations do not need equality of the whole actual-argument tuple
        a priori.  They only need agreement on the prefix up to the current
        instant, so that low callee inputs can be related pointwise to the two
        caller runs. *)
    Lemma sem_exps_prefix_eq:
      forall bk H H' es ls ls' k,
        (forall y, Exists (Is_free_in_exp y) es ->
             forall j, j <= k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_exps bk H es ls ->
        sem_exps bk H' es ls' ->
        forall j, j <= k -> ls j = ls' j.
    Proof.
      intros bk H H' es ls ls' k Hdep Hsem Hsem' j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
      assert (Hsw : sem_exps_instant (bk j) (H' j) es (ls j)).
      {
        apply
          (proj1
             (sem_exps_instant_switch_env
                (bk j) (H j) (H' j) es (ls j)
                (fun y Hy => Hdep y Hy j Hj))).
        exact Hsem.
      }
      eapply sem_exps_instant_det; eauto.
    Qed.

    (** Invert one plain NLustre call equation semantically.

        Relation to the paper:
        the call case repeatedly needs the actual-argument stream, the caller
        output tuple, and the callee semantic run exposed separately.  This
        is the semantic unpacking step for a non-reset call. *)
    Lemma sem_eqapp_inv:
      forall bk H xs ck f exps,
        Indexed.sem_equation all_nodes bk H (EqApp xs ck f exps None) ->
        exists ls ys,
          sem_exps bk H exps ls /\
          sem_vars H xs ys /\
          sem_clock bk H ck (clock_of ls) /\
          Indexed.sem_node all_nodes f ls ys.
    Proof.
      intros bk H xs ck f exps Hsem.
      inversion Hsem; subst; clear Hsem.
      exists ls, xs0.
      repeat split; assumption.
    Qed.

    (** Invert one resettable NLustre call equation semantically.

        Relation to the paper:
        reset calls add one reset stream and one masked recursive callee
        hypothesis to the plain call case.  The noninterference proof uses
        this wrapper to expose those components explicitly. *)
    Lemma sem_eqreset_inv:
      forall bk H xs ck f exps r ckr,
        Indexed.sem_equation all_nodes bk H (EqApp xs ck f exps (Some (r, ckr))) ->
        exists ys rs ls outs,
          sem_exps bk H exps ls /\
          sem_vars H xs outs /\
          sem_clock bk H ck (clock_of ls) /\
          sem_var H r ys /\
          bools_of ys rs /\
          (forall k, Indexed.sem_node all_nodes f (mask k rs ls) (mask k rs outs)).
    Proof.
      intros bk H xs ck f exps r ckr Hsem.
      inversion Hsem; subst; clear Hsem.
      exists ys, rs, ls, xs0.
      repeat split; assumption.
    Qed.

    (** Invert one indexed NLustre node run.

        Relation to the paper:
        recursive call reasoning is stated semantically on one callee run.
        This lemma exposes the internal callee history and local equations
        from the indexed [SNode] constructor. *)
    Lemma sem_node_inv:
      forall f xss yss,
        Indexed.sem_node all_nodes f xss yss ->
        exists bk H nd,
          bk = clock_of xss /\
          find_node f all_nodes = Some nd /\
          sem_vars H (map fst nd.(n_in)) xss /\
          sem_vars H (map fst nd.(n_out)) yss /\
          sem_clocked_vars bk H (idck nd.(n_in)) /\
          Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs).
    Proof.
      intros f xss yss Hsem.
      destruct Hsem
        as [bk0 H0 f0 xss0 yss0 n0 Hbk Hfind Hin Hout Hclock Heqs].
      exists bk0, H0, n0.
      repeat split; assumption.
    Qed.

    (** Well-clocked reset calls expose their reset source in the caller vars.

        Relation to the paper:
        resettable calls add one extra current dependency carried by the reset
        variable.  The noninterference proof uses the clocking judgment only to
        recover that this reset source is already part of the caller typing
        environment. *)
    Lemma wc_reset_in_call_vars:
      forall P vars xs ck f exps rx rck,
        Clo.wc_equation P vars (EqApp xs ck f exps (Some (rx, rck))) ->
        In (rx, rck) vars.
    Proof.
      intros P vars xs ck f exps rx rck Hwc.
      inversion Hwc as [|xs' ck' f' exps' r' nd sub Hfind Hins Houts Hr|]; subst.
      eapply Hr. reflexivity.
    Qed.

    (** The active reset segment exposes the underlying list unchanged.

        Relation to the paper:
        reset calls reason on one masked callee run.  At the currently active
        reset segment, the mask is transparent, so tuple-position arguments
        can be pushed back to the original actual/output list. *)
    Lemma nth_error_mask_count_self:
      forall rs xss k i v,
        nth_error (mask (count rs k) rs xss k) i = Some v ->
        nth_error (xss k) i = Some v.
    Proof.
      intros rs xss k i v Hnth.
      unfold mask in Hnth.
      rewrite Nat.eqb_refl in Hnth.
      exact Hnth.
    Qed.

    (** An opaque mask exposes only absent values.

        Relation to the paper:
        reset-call prefix proofs split into the active reset segment, where
        the mask is transparent, and earlier segments, where the mask is
        opaque.  In the opaque case, every tuple position is immediately
        absent, which is the only semantic fact needed to close the branch. *)
    Lemma nth_error_all_absent_absent:
      forall (A : Type) (xs : list A) i v,
        nth_error (all_absent xs) i = Some v ->
        v = absent.
    Proof.
      intros A xs.
      induction xs as [|x xs IH]; intros i v Hnth.
      - destruct i; inversion Hnth.
      - destruct i as [|i].
        + simpl in Hnth. inversion Hnth. reflexivity.
        + simpl in Hnth. eapply IH; eauto.
    Qed.

    (** Low instantiated expression types make all free variables low.

        Relation to the paper:
        call inputs are typed by symbolic sets rather than by one caller
        output identifier.  For the recursive call proof, the relevant fact is
        therefore: if the instantiated symbolic type of one actual expression
        is already below the observation level, then every free variable of
        that actual expression is low as well. *)
    Lemma exp_type_low:
      forall e ety y,
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.hm_ext dlt ety ⊑ t ->
        Is_free_in_exp y e ->
        low_var y.
    Proof.
      intros e ety y He Hlow Hfree.
      destruct (assign_exp_type_free_bound e ety y Hfree He)
        as (alpha & Hfind & Hbound).
      exists alpha.
      split; [exact Hfind|].
      eapply order_trans; eauto.
    Qed.

    (** Prefix extensionality of [hold].

        Relation to the paper:
        [fby] is the only NLustre simple case whose current value may depend
        on earlier values of its feeding stream.  This lemma isolates that
        time-shifted dependency: agreement of the feeding stream on all
        instants strictly before [n] is enough to make [hold] agree at [n]. *)
    Lemma hold_eq_prefix:
      forall v0 xs xs' k,
        (forall j, j < k -> xs j = xs' j) ->
        Indexed.hold v0 xs k = Indexed.hold v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix.
      induction k as [|m IH]; [reflexivity|].
      simpl.
      assert (Hm : m < S m) by lia.
      pose proof (Hprefix m Hm) as Hm_eq.
      rewrite Hm_eq.
      destruct (xs' m) eqn:Hn; auto.
    Qed.

    (** Prefix extensionality of [fby].

        Relation to the paper:
        once the feeding stream agrees on all instants up to [n], the delayed
        stream produced by [fby] also agrees at [n].  This is the basic
        time-induction ingredient needed by the delayed noninterference case. *)
    Lemma fby_eq_prefix:
      forall v0 xs xs' k,
        (forall j, j <= k -> xs j = xs' j) ->
        Indexed.fby v0 xs k = Indexed.fby v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix.
      unfold Indexed.fby.
      pose proof (Hprefix k (le_n k)) as Hk_eq.
      rewrite Hk_eq.
      destruct (xs' k) eqn:Hn; auto.
      f_equal.
      apply hold_eq_prefix.
      intros j Hj.
      apply Hprefix.
      lia.
    Qed.

    (** Delayed extensionality of [fby].

        Relation to the paper:
        the current output of a delay depends on the past payload of its
        feeding stream and only on the current presence/absence bit.  This
        is the exact semantic shape needed in the [EqFby] case of the
        indexed noninterference proof. *)
    Lemma fby_eq_delay_prefix:
      forall v0 xs xs' k,
        (forall j, j < k -> xs j = xs' j) ->
        (xs k = absent <-> xs' k = absent) ->
        Indexed.fby v0 xs k = Indexed.fby v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix Habs.
      unfold Indexed.fby.
      destruct (xs k) eqn:Hk.
      - destruct (xs' k) eqn:Hk'; simpl.
        + reflexivity.
        + exfalso.
          assert (Hab0 : absent = absent) by reflexivity.
          pose proof (proj1 Habs Hab0) as Hab.
          congruence.
      - destruct (xs' k) eqn:Hk'; simpl.
        + exfalso.
          assert (Hab0 : absent = absent) by reflexivity.
          pose proof (proj2 Habs Hab0) as Hab.
          congruence.
        + f_equal.
          eapply hold_eq_prefix; eauto.
    Qed.

    (** Prefix preservation for guarded source expressions.

        Relation to the paper:
        this is the time-indexed bridge needed by the delayed case: if all
        free variables of an annotated expression agree on the earlier
        instants, then its semantic stream agrees on that earlier prefix as
        well. *)
    Lemma sem_aexp_prefix_eq:
      forall bk H H' ck e ls ls' k,
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk H' ck e ls' ->
        forall j, j < k -> ls j = ls' j.
    Proof.
      intros bk H H' ck e ls ls' k Hdep Hsem Hsem' j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
      assert (Hsw : sem_aexp_instant (bk j) (H' j) ck e (ls j)).
      {
        apply
          (proj1
             (sem_aexp_instant_switch_env
                (bk j) (H j) (H' j) ck e (ls j)
                (fun y Hy =>
                   match Hy with
                   | or_introl Hyck => Hdep y (freeAexp2 _ _ _ Hyck) j Hj
                   | or_intror Hye => Hdep y (freeAexp1 _ _ _ Hye) j Hj
                   end))).
        - exact Hsem.
      }
      eapply sem_aexp_instant_det; eauto.
    Qed.

    (** Absent annotated expressions force a false clock at the same instant.

        Relation to the paper:
        this isolates the current-time control fact used in the delayed case:
        when the feeding annotated expression is absent, its clock must be
        false at that instant. *)
    Lemma sem_aexp_instant_absent_clock_false:
      forall b R ck e,
        sem_aexp_instant b R ck e absent ->
        sem_clock_instant b R ck false.
    Proof.
      intros b R ck e Hsem.
      inversion Hsem; subst; auto; discriminate.
    Qed.

    (** Present annotated expressions force a true clock at the same instant.

        Relation to the paper:
        together with the absent case, this turns current clock equality into
        current presence equality for the feeding stream of an [EqFby]. *)
    Lemma sem_aexp_instant_present_clock_true:
      forall b R ck e v,
        sem_aexp_instant b R ck e (present v) ->
        sem_clock_instant b R ck true.
    Proof.
      intros b R ck e v Hsem.
      inversion Hsem; subst; auto; discriminate.
    Qed.

    (** Current-presence preservation for guarded source expressions.

        Relation to the paper:
        in the delayed case, the current instant only needs the clock side of
        the feeding expression.  This lemma isolates that fact: equality of
        the clock dependencies at one instant forces the annotated expression
        to be absent in one run iff it is absent in the other. *)
    Lemma sem_aexp_same_presence_from_clock:
      forall bk H H' ck e ls ls' k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk H' ck e ls' ->
        (ls k = absent <-> ls' k = absent).
    Proof.
      intros bk H H' ck e ls ls' k Hdep Hsem Hsem'.
      assert (Hclk_sw :
                forall b,
                  sem_clock_instant (bk k) (H k) ck b
                  <-> sem_clock_instant (bk k) (H' k) ck b).
      {
        intro b.
        apply sem_clock_instant_switch_env.
        exact Hdep.
      }
      destruct (ls k) eqn:Hlk, (ls' k) eqn:Hlk'; split; intro Hab; try reflexivity;
        try congruence.
      - specialize (Hsem k). rewrite Hlk in Hsem.
        specialize (Hsem' k). rewrite Hlk' in Hsem'.
        pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem) as Hf.
        pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem') as Ht.
        pose proof (proj1 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
      - specialize (Hsem k). rewrite Hlk in Hsem.
        specialize (Hsem' k). rewrite Hlk' in Hsem'.
        pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem) as Ht.
        pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem') as Hf.
        pose proof (proj2 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
    Qed.

    (** Repackage pointwise low-equality facts as a history-level relation.

        Relation to the paper:
        the causality induction naturally produces one proof obligation per
        variable.  This lemma folds those pointwise obligations back into the
        relational form [history_low_eq] used by the noninterference theorem
        statements. *)
    Lemma history_low_eq_from_Forall_pointwise:
      forall X H H',
        Forall (fun x => low_var x -> forall k, Env.find x (H k) = Env.find x (H' k)) X ->
        history_low_eq X H H'.
    Proof.
      intros X H H' Hpts k x Hin Hlow.
      eapply Forall_forall in Hpts; [|exact Hin].
      eapply Hpts; eauto.
    Qed.

    (** Simple [EqDef] noninterference step.

        Relation to the paper:
        this is the indexed semantic proof step for a single non-call
        definition equation.  Once the raw typing constraint shows that every
        free dependency of the RHS is low, low-equivalence of those
        dependencies forces equality of the defined stream. *)
    Lemma eqdef_noninterference:
      forall X bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_caexp y ck ce -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety
             Hlow HX Hfindx Hck Hce Hsat Hlowx Hvar Hrhs Hvar' Hrhs' k.
      assert (Hfree :
                forall y, Is_free_in_caexp y ck ce -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_caexp base_ty rst_ty x ck ce xty ckty cety y
                   Hfindx Hck Hce Hsat Hlowx Hy). }
      assert (Hrhs_switched : sem_caexp bk H' ck ce xs).
      { eapply sem_caexp_switch_history_low; eauto. }
      assert (Hxs : xs = xs').
      { eapply sem_caexp_det; eauto. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Simple [EqFby] noninterference step.

        Relation to the paper:
        this is the indexed semantic proof step for one delay equation.  The
        proof reduces to equality of the feeding stream, then transports that
        through the deterministic [fby] construction. *)
    Lemma eqfby_noninterference:
      forall X bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_aexp y ck e -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety
             Hlow HX Hfindx Hck He Hsat Hlowx Hvar Hrhs Hfby
             Hvar' Hrhs' Hfby' k.
      assert (Hfree :
                forall y, Is_free_in_aexp y ck e -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_aexp base_ty rst_ty x ck e xty ckty ety y
                   Hfindx Hck He Hsat Hlowx Hy). }
      assert (Hrhs_switched : sem_aexp bk H' ck e ls).
      { eapply sem_aexp_switch_history_low; eauto. }
      assert (Hls : ls = ls').
      { eapply sem_aexp_det; eauto. }
      assert (Hxs : xs = xs').
      { rewrite Hfby.
        rewrite <- Hls in Hfby'.
        rewrite Hfby'.
        reflexivity. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Switching a guarded combinational expression from direct pointwise
        dependency equality.

        Relation to the paper:
        the causal step theorem does not naturally produce a global
        low-equivalence relation over a chosen observation set.  It produces
        one equality fact per immediate dependency.  This lemma is the direct
        semantic bridge from those pointwise equalities to RHS preservation. *)
    Lemma sem_caexp_switch_pointwise:
      forall bk H H' ck ce xs,
        (forall y, Is_free_in_caexp y ck ce ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        sem_caexp bk H ck ce xs ->
        sem_caexp bk H' ck ce xs.
    Proof.
      intros bk H H' ck ce xs Hdep Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_caexp_instant_switch_env
              (bk k) (H k) (H' k) ck ce (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck => Hdep y (FreeCAexp2 _ _ _ Hyck) k
                 | or_intror Hyce => Hdep y (FreeCAexp1 _ _ _ Hyce) k
                 end))).
      exact Hsem.
    Qed.

    (** Switching a guarded source expression from direct pointwise dependency
        equality.

        Relation to the paper:
        this is the direct-pointwise version of the semantic [fby] step used
        inside the causality induction. *)
    Lemma sem_aexp_switch_pointwise:
      forall bk H H' ck e xs,
        (forall y, Is_free_in_aexp y ck e ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        sem_aexp bk H ck e xs ->
        sem_aexp bk H' ck e xs.
    Proof.
      intros bk H H' ck e xs Hdep Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_aexp_instant_switch_env
              (bk k) (H k) (H' k) ck e (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck => Hdep y (freeAexp2 _ _ _ Hyck) k
                 | or_intror Hye => Hdep y (freeAexp1 _ _ _ Hye) k
                 end))).
      exact Hsem.
    Qed.

    (** Simple [EqDef] noninterference from direct dependency equality.

        Relation to the paper:
        this is the equation-local form needed by the causality induction:
        once every immediate dependency of the RHS is known equal across the
        two runs, the defined low variable is equal as well. *)
    Lemma eqdef_noninterference_pointwise:
      forall bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety,
        (forall y, Is_free_in_caexp y ck ce ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety
             Hdep Hfindx Hck Hce Hsat Hlowx Hvar Hrhs Hvar' Hrhs' k.
      assert (Hrhs_switched : sem_caexp bk H' ck ce xs).
      { eapply sem_caexp_switch_pointwise; eauto. }
      assert (Hxs : xs = xs').
      { eapply sem_caexp_det; eauto. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Instantaneous [EqDef] noninterference from current dependency
        equality.

        Relation to the paper:
        once the main theorem is rephrased around an outer induction on the
        instant, the simple definition case only needs equality of its
        dependencies at that one instant.  This lemma is the exact local step
        for that fixed-time form. *)
    Lemma eqdef_noninterference_instant_pointwise:
      forall bk H H' x xs xs' ck ce k,
        (forall y, Is_free_in_caexp y ck ce ->
             Env.find y (H k) = Env.find y (H' k)) ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ck ce k
             Hdep Hvar Hrhs Hvar' Hrhs'.
      specialize (Hvar k).
      specialize (Hrhs k).
      specialize (Hvar' k).
      specialize (Hrhs' k).
      assert (Hrhs_sw : sem_caexp_instant (bk k) (H' k) ck ce (xs k)).
      {
        apply
          (proj1
             (sem_caexp_instant_switch_env
                (bk k) (H k) (H' k) ck ce (xs k)
                (fun y Hy =>
                   match Hy with
                   | or_introl Hyck => Hdep y (FreeCAexp2 _ _ _ Hyck)
                   | or_intror Hyce => Hdep y (FreeCAexp1 _ _ _ Hyce)
                   end))).
        exact Hrhs.
      }
      assert (Hxs : xs k = xs' k).
      { eapply sem_caexp_instant_det; eauto. }
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Simple [EqFby] noninterference from direct dependency equality.

        Relation to the paper:
        this is the pointwise-dependency form of the delay case used by the
        causality induction. *)
    Lemma eqfby_noninterference_pointwise:
      forall bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety,
        (forall y, Is_free_in_aexp y ck e ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety
             Hdep Hfindx Hck He Hsat Hlowx Hvar Hrhs Hfby
             Hvar' Hrhs' Hfby' k.
      assert (Hrhs_switched : sem_aexp bk H' ck e ls).
      { eapply sem_aexp_switch_pointwise; eauto. }
      assert (Hls : ls = ls').
      { eapply sem_aexp_det; eauto. }
      assert (Hxs : xs = xs').
      { rewrite Hfby.
        rewrite <- Hls in Hfby'.
        rewrite Hfby'.
        reflexivity. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Delayed [EqFby] noninterference from current-clock and past-data
        equality.

        Relation to the paper:
        this is the precise indexed delayed step needed by the causal proof.
        The current instant only needs clock agreement, while the payload of
        the delay is recovered from equality of the feeding expression on the
        earlier prefix. *)
    Lemma eqfby_noninterference_delayed_pointwise:
      forall bk H H' x xs xs' ls ls' ck c0 e k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ls ls' ck c0 e k
             Hclock Hpast
             Hvar Hrhs Hfby Hvar' Hrhs' Hfby'.
      assert (Hls_prefix : forall j, j < k -> ls j = ls' j).
      { eapply sem_aexp_prefix_eq; eauto. }
      assert (Hls_abs : ls k = absent <-> ls' k = absent).
      { eapply sem_aexp_same_presence_from_clock; eauto. }
      assert (Hxs_k : xs k = xs' k).
      {
        rewrite Hfby, Hfby'.
        eapply fby_eq_delay_prefix; eauto.
      }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs_k in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

  End GENERATED_LOW_OBSERVATION.

  Section GENERATED_NODE_SECURITY.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Recover the local clocking premise for one found source node.

        Relation to the paper:
        the final theorem is stated against the exact generated source program,
        but the replay lemma only needs the local [wc_node] fact for the
        current node.  This lemma extracts that local premise from the global
        well-clockedness assumption without changing the theorem statement. *)
    Lemma wc_global_find_node:
      forall n,
        Clo.wc_global all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        exists P, Clo.wc_node P n.
    Proof.
      intros n Hwc Hfind.
      pose proof (find_node_In _ _ _ Hfind) as (_ & Hin).
      apply in_split in Hin as (prefix & suffix & Hall).
      subst all_nodes.
      exists suffix.
      clear Hfind.
      revert suffix Hwc.
      induction prefix as [|m prefix IH]; intros suffix Hwc.
      - simpl in Hwc.
        inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        exact Hwc_head.
      - simpl in Hwc.
        inversion Hwc as [|m' ms Hwc_tail Hwc_head]; subst m' ms.
        eapply IH; eauto.
    Qed.

    (** Free variables of a well-clocked clock belong to the current node
        environment.

        Relation to the paper:
        the delayed case needs to classify the free variables of a source
        expression as inputs or already-defined node variables.  This helper
        starts that bridge on the clock side. *)
    Lemma Is_free_in_wc_clock:
      forall vars x ck,
        wc_clock vars ck ->
        Is_free_in_clock x ck ->
        InMembers x vars.
    Proof.
      intros vars x ck Hwc.
      induction Hwc; intros Hfree.
      - inversion Hfree.
      - inversion Hfree; subst; eauto.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
    Qed.

    (** Free variables of a well-clocked expression belong to the current
        node environment.

        Relation to the paper:
        this is the expression-side membership fact used when the delayed
        proof moves from "low free variable" to "input or defined variable". *)
    Lemma Is_free_in_wc_exp:
      forall vars x e ck,
        wc_exp vars e ck ->
        Is_free_in_exp x e ->
        InMembers x vars.
    Proof.
      intros vars x e ck Hwc.
      induction Hwc; intros Hfree.
      - inversion Hfree.
      - inversion Hfree; subst.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
      - inversion Hfree; subst; eauto.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
      - inversion Hfree; subst; eauto.
      - inversion Hfree; subst; eauto.
        destruct H1; eauto.
    Qed.

    (** Free variables of a well-clocked annotated expression belong to the
        current node environment.

        Relation to the paper:
        the delayed proof reasons about whole annotated expressions [ck, e],
        so the free-variable membership fact must cover both the data and the
        clock side together. *)
    Lemma Is_free_in_wc_aexp:
      forall vars x ck e,
        wc_env vars ->
        Is_free_in_aexp x ck e ->
        wc_exp vars e ck ->
        InMembers x vars.
    Proof.
      intros vars x ck e Hwcenv Hfree Hwc.
      inversion Hfree; subst.
      - eapply Is_free_in_wc_exp; eauto.
      - eapply Is_free_in_wc_clock.
        + eapply wc_clock_exp; eauto.
        + exact H.
    Qed.

    (** Classify delayed free variables as inputs or defined variables.

        Relation to the paper:
        the delayed proof needs to know that every source dependency of an
        [EqFby] right-hand side comes either from the node inputs or from a
        variable defined elsewhere in the node.  This is the exact source-side
        classification step extracted from well-clockedness. *)
    Lemma free_aexp_in_inputs_or_defined:
      forall P n x ck c0 e y,
        Clo.wc_node P n ->
        In (EqFby x ck c0 e) n.(n_eqs) ->
        Is_free_in_aexp y ck e ->
        In y (map fst n.(n_in)) \/ In y (vars_defined n.(n_eqs)).
    Proof.
      intros P n x ck c0 e y
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin Hfree.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      assert (Hy_mem : InMembers y (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { eapply Is_free_in_wc_aexp; eauto. }
      rewrite InMembers_idck in Hy_mem.
      rewrite InMembers_app in Hy_mem.
      destruct Hy_mem as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app.
            apply in_or_app.
            now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app.
            apply in_or_app.
            now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    (** Past low-equality for delayed free variables from inputs or already-defined vars.

        Relation to the paper:
        in the successor [EqFby] case, the current instant only depends on the
        clock, but the delayed payload may read earlier values of the source
        expression. This lemma packages the source-side classification step:
        every such free variable comes either from the inputs, where low
        equality is assumed, or from a variable already defined in the node,
        where low equality is supplied by the previous prefix induction. *)
    Lemma free_aexp_low_eq_prefix_from_inputs_or_defined:
      forall P n ty_env dlt t H H' x ck c0 e y k,
        Clo.wc_node P n ->
        In (EqFby x ck c0 e) n.(n_eqs) ->
        Is_free_in_aexp y ck e ->
        low_var ty_env dlt t y ->
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' (S k) ->
        history_low_eq_upto ty_env dlt t (vars_defined n.(n_eqs)) H H' k ->
        forall j, j < S k -> Env.find y (H j) = Env.find y (H' j).
    Proof.
      intros P n ty_env dlt t H H' x ck c0 e y k
             Hwcnode Heqin Hfree Hlowy Hlowin Hprev j Hj.
      destruct (free_aexp_in_inputs_or_defined P n x ck c0 e y Hwcnode Heqin Hfree)
        as [Hin|Hdef].
      - eapply Hlowin; eauto.
        lia.
      - eapply Hprev; eauto.
        lia.
    Qed.

    (** Classify free actual-argument variables as inputs or defined variables.

        Relation to the paper:
        the successor [EqApp] proof needs prefix equality for the free
        variables of actual arguments.  This is the call-side analogue of
        [free_aexp_in_inputs_or_defined]: every free actual-argument variable
        comes either from the node inputs or from one of the variables already
        defined by the node equations. *)
    Lemma free_exp_in_inputs_or_defined:
      forall P n xs ck f exps r y,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        Exists (Is_free_in_exp y) exps ->
        In y (map fst n.(n_in)) \/ In y (vars_defined n.(n_eqs)).
    Proof.
      intros P n xs ck f exps r y
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin Hfree.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      match goal with
      | Hins : Forall2 _ _ exps |- _ => rename Hins into Hwcins
      end.
      apply Exists_exists in Hfree as (e & Hine & Hfree_e).
      destruct (SecT.In_nth_error_ex _ _ _ Hine) as [i Hnthe].
      assert (Hi_in : i < List.length n0.(n_in)).
      {
        pose proof (Forall2_length _ _ _ Hwcins) as Hlen.
        assert (Hi_exp : i < List.length exps).
        {
          apply nth_error_Some.
          rewrite Hnthe.
          discriminate.
        }
        rewrite Hlen.
        exact Hi_exp.
      }
      destruct (nth_error n0.(n_in) i) as [in_pair|] eqn:Hnthin.
      2:{
        apply nth_error_None in Hnthin.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun '(x, (_, xck)) le =>
              SameVar (sub x) le
              /\ exists lck, wc_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) le lck
                       /\ instck ck sub xck = Some lck)
           n0.(n_in) exps i in_pair
           Hwcins Hnthin)
        as (e' & Hnthe' & Hwc_pair).
      rewrite Hnthe in Hnthe'.
      inversion Hnthe'; subst e'; clear Hnthe'.
      destruct in_pair as [xin [xty xck]].
      cbn in Hwc_pair.
      destruct Hwc_pair as [_ (lck & Hwc_e & _)].
      assert (Hy_mem : InMembers y (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { eapply Is_free_in_wc_exp; eauto. }
      rewrite InMembers_idck in Hy_mem.
      rewrite InMembers_app in Hy_mem.
      destruct Hy_mem as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    (** Classify the reset source of a resettable call as input or defined variable.

        Relation to the paper:
        the reset-control prefix proof for [EqApp ... (Some ...)] needs to
        transport equality of the reset source stream from either the input
        hypothesis or the already-established previous-prefix equality on
        defined variables. *)
    Lemma reset_var_in_inputs_or_defined:
      forall P n xs ck f exps r ckr,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
        In r (map fst n.(n_in)) \/ In r (vars_defined n.(n_eqs)).
    Proof.
      intros P n xs ck f exps r ckr
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      match goal with
      | Hrst : forall yck, _ = Some yck -> In yck _ |- _ => rename Hrst into Hwcrst
      end.
      assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      {
        eapply Hwcrst.
        reflexivity.
      }
      apply In_InMembers in Hinr.
      rewrite InMembers_idck in Hinr.
      rewrite InMembers_app in Hinr.
      destruct Hinr as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In r (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In r (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    (** Prefix equality of one semantic source stream from low-equivalent histories.

        Relation to the paper:
        reset calls introduce one explicit source variable whose semantic value
        stream is later converted to a Boolean reset stream. This lemma is the
        first step in that bridge: if the raw variable is low and the two
        histories agree on it up to a prefix, then the semantic source streams
        selected by [sem_var] are equal on that prefix. *)
    Lemma sem_var_low_eq_upto:
      forall H H' x ys ys' k,
        sem_var H x ys ->
        sem_var H' x ys' ->
        (forall j, j <= k -> Env.find x (H j) = Env.find x (H' j)) ->
        forall j, j <= k -> ys j = ys' j.
    Proof.
      intros H H' x ys ys' k Hvar Hvar' Heq j Hj.
      specialize (Hvar j).
      specialize (Hvar' j).
      unfold sem_var_instant in Hvar, Hvar'.
      pose proof (Heq j Hj) as Hfind_eq.
      rewrite Hvar in Hfind_eq.
      rewrite Hvar' in Hfind_eq.
      inversion Hfind_eq.
      reflexivity.
    Qed.

    (** Prefix equality of reset booleans from equality of their source values.

        Relation to the paper:
        after showing that the reset source stream is equal across the two
        runs, the proof needs the same fact for the Boolean reset stream used
        by [mask]. This is the direct [bools_of] transport step. *)
    Lemma bools_of_eq_upto:
      forall ys ys' rs rs' k,
        bools_of ys rs ->
        bools_of ys' rs' ->
        (forall j, j <= k -> ys j = ys' j) ->
        forall j, j <= k -> rs j = rs' j.
    Proof.
      intros ys ys' rs rs' k Hbool Hbool' Heq j Hj.
      specialize (Hbool j).
      specialize (Hbool' j).
      rewrite (Heq j Hj) in Hbool.
      rewrite Hbool in Hbool'.
      inversion Hbool'.
      reflexivity.
    Qed.

    (** Prefix equality of reset counts from prefix equality of reset booleans.

        Relation to the paper:
        the masked indexed semantics separates reset segments using [count].
        To align the masked histories of the two runs, it is enough to know
        that the Boolean reset streams agree on the whole prefix. *)
    Lemma count_eq_upto:
      forall rs rs' k,
        (forall j, j <= k -> rs j = rs' j) ->
        forall j, j <= k -> count rs j = count rs' j.
    Proof.
      intros rs rs' k Heq.
      induction j as [|j IH]; intros Hj.
      - simpl.
        rewrite (Heq 0 Hj).
        reflexivity.
      - simpl.
        rewrite (Heq (S j) Hj).
        rewrite (IH (Nat.le_trans _ _ _ (Nat.le_succ_diag_r j) Hj)).
        reflexivity.
    Qed.

    (** Upper bounds for one generated caller scope.

        Relation to the paper:
        recursive call proofs need to know that the current caller's symbolic
        identifiers live strictly below the naming state reached after
        generating that caller environment.  Combined later with lower bounds
        for another node, this gives the required cross-node freshness. *)
    Lemma node_scope_upper_bounded_from_local_env:
      forall n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals ty,
        NAMEGEN.generate_local_env_for_node n st = OK ((env, rec), st') ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
        exists m, ty = Ids.gensym Ids.sec m /\ (m < st')%positive.
    Proof.
      intros n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals ty
             Hlocal Hclk Hrst Hinp Hout Hlocals Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
          as (xinp & ainp & _ & Hfindinp).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindinp) as (m & Hm & Hlt).
        exists m. split; assumption.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
          as (xout & aout & _ & Hfindout).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindout) as (m & Hm & Hlt).
        exists m. split; assumption.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin)
          as (xlocal & alocal & _ & Hfindlocal).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindlocal) as (m & Hm & Hlt).
        exists m. split; assumption.
      - subst ty.
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hclk) as (m & Hm & Hlt).
        exists m. split; assumption.
      - subst ty.
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hrst) as (m & Hm & Hlt).
        exists m. split; assumption.
    Qed.

    (** Paired node security for generated NLustre nodes.

        Relation to the paper:
        the paper states node security over one canonical signature valuation.
        The current mechanization strengthens that notion to carry, together:

        - the canonical signature valuation [dlt_sig];
        - a replayed raw valuation [dlt_raw] that agrees with [dlt_sig] on the
          visible signature scope of the current node; and
        - the generated raw constraint witnesses for the current node, together
          with satisfiability of those raw constraints under [dlt_raw].

        This paired form is the active proof route because the [EqApp] case
        for caller locals needs recursive callee noninterference under both
        the canonical call-site instantiation and the replayed raw one.
        Threading both valuations directly through [node_security] keeps that
        bridge explicit and avoids reopening a separate replay/agreement
        argument at every recursive call.  The definition is still phrased
        entirely through the generated local typing environment from
        [NameInterface] and the generated signatures from [SecNLusTyping];
        it does not introduce a second typing judgment, but it now also stores
        the current node's raw generation data explicitly so recursive proofs
        can reuse it without replaying from scratch. *)

    (** Why just signature satisfiability is not sufficient.

        It is tempting to define node security only by requiring that the
        current node's generated signature constraints [ρ] are satisfied by the
        chosen ground instantiation [dlt].  That local condition is enough for
        the non-call equation cases:

        - [EqDef], where the current node's constraint directly bounds the
          clock and expression dependencies of one defined variable;
        - [EqFby], where the current node's constraint directly bounds the
          clock, reset, and expression dependencies of one memory variable.

        It is not enough for [EqApp] and resettable [EqApp], because in those
        cases the current node's satisfiable constraints only establish that
        the call site is well instantiated.  Using the existing signature
        metatheory, we can replay that into satisfiability of the callee
        signature under the call-specific instantiated valuation.  However,
        satisfiability of the callee signature is still only a typing fact.

        To conclude low-equivalence of the callee outputs across two semantic
        runs, the noninterference proof needs a semantic induction hypothesis
        for the callee itself.  In the active proof route, that recursive
        hypothesis must be available under both the canonical signature
        valuation and the replayed raw valuation induced at the call site.
        That is why [node_security] now recursively carries both valuations
        for each direct callee. *)

    Inductive node_security
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
    | SecureNode :
        forall ty_env sig
               clk_id rst_id clk_type rst_type inp out locals raw st_n,
          find_node nd.(n_name) all_nodes = Some nd ->
          find_node_env nd.(n_name) envs = Some ty_env ->
          SIG.find_signature nd.(n_name) G = Some sig ->
          SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
          get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
          Env.find clk_id ty_env = Some clk_type ->
          Env.find rst_id ty_env = Some rst_type ->
          get_mappings_from_node nd.(n_in) ty_env = Some inp ->
          get_mappings_from_node nd.(n_out) ty_env = Some out ->
          get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
          generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
          sig = {| s_name := nd.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |} ->
          signature_satisfied dlt_sig sig ->
          SecT.agree_on (signature_scope sig) dlt_sig dlt_raw ->
          SecT.listSatisfiable dlt_raw raw ->
          (* normal call security *)
          (forall xs ck f exps callee callee_sig
                  ckty inptyp outtyp st_clk st_inp,
              In (EqApp xs ck f exps None) nd.(n_eqs) ->
              find_node f all_nodes = Some callee ->
              SIG.find_signature f G = Some callee_sig ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
                SC.init_state = OK (ckty, st_clk) ->
              SC.mmap
                (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                exps st_clk = OK (inptyp, st_inp) ->
              get_mappings xs ty_env = Some outtyp ->
              node_security callee
                (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                   [sig.(s_reset)] outtyp)
                (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                   [sig.(s_reset)] outtyp)) ->
          (*reset call security*)
          (forall xs ck f exps r ckr callee callee_sig
                  ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
              In (EqApp xs ck f exps (Some (r, ckr))) nd.(n_eqs) ->
              find_node f all_nodes = Some callee ->
              SIG.find_signature f G = Some callee_sig ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
                SC.init_state = OK (ckty, st_clk) ->
              Env.find r ty_env = Some rty ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_reset) ckr)
                st_clk = OK (rstty, st_rst) ->
              SC.mmap
                (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                exps st_rst = OK (inptyp, st_inp) ->
              get_mappings xs ty_env = Some outtyp ->
              node_security callee
                (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                   ([rty] ⊔ rstty) outtyp)
                (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                   ([rty] ⊔ rstty) outtyp)) ->
          node_security nd dlt_sig dlt_raw.

  End GENERATED_NODE_SECURITY.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Reset control low-equality on a finite prefix.

        Relation to the paper:
        reset is not a plain NLustre source input carried in
        [map fst n.(n_in)].  In indexed semantics it appears as a Boolean
        control stream extracted by [bools_of] and consumed through [count]
        and [mask].  This definition is therefore the reset-aware analogue of
        low input equality: if the reset source variable is low, then the
        induced reset segment counters agree on the whole prefix. *)
    Definition reset_control_low_eq_upto
      (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
      (r : ident) (H H' : history) (k : nat) : Prop :=
      forall ys ys' rs rs',
        sem_var H r ys ->
        sem_var H' r ys' ->
        bools_of ys rs ->
        bools_of ys' rs' ->
        low_var ty_env dlt t r ->
        forall j, j <= k -> count rs j = count rs' j.

    (** Build reset-control equality from prefix equality of the reset source.

        Relation to the paper:
        resettable calls consume reset through the Boolean/masked semantics,
        but the causality theorem naturally provides equality first at the
        source variable level.  This lemma is the semantic bridge from low
        equality of the reset source stream to equality of reset segment
        counters on the observed prefix. *)
    Lemma reset_control_low_eq_upto_of_sem_var_eq :
      forall ty_env dlt t r H H' k,
        (low_var ty_env dlt t r ->
         forall j, j <= k -> Env.find r (H j) = Env.find r (H' j)) ->
        reset_control_low_eq_upto ty_env dlt t r H H' k.
    Proof.
      intros ty_env dlt t r H H' k Heq ys ys' rs rs'
             Hsemr Hsemr' Hbool Hbool' Hlowr j Hj.
      assert (Hys_eq : forall j0, j0 <= k -> ys j0 = ys' j0).
      {
        eapply sem_var_low_eq_upto; eauto.
      }
      assert (Hrs_eq : forall j0, j0 <= k -> rs j0 = rs' j0).
      {
        eapply bools_of_eq_upto; eauto.
      }
      exact (count_eq_upto rs rs' k Hrs_eq j Hj).
    Qed.

    (** Agreement on a symbolic scope is symmetric.

        Relation to the paper:
        replay from simplified signatures to raw constraints gives an
        agreement fact between the canonical valuation and the replayed one.
        The final noninterference corollary needs to use that agreement in
        both directions when transporting low-observation facts between the
        two valuations. *)
    Lemma agree_on_sym:
      forall scope dlt1 dlt2,
        SecT.agree_on scope dlt1 dlt2 ->
        SecT.agree_on scope dlt2 dlt1.
    Proof.
      intros scope dlt1 dlt2 Hagree x Hin.
      symmetry. exact (Hagree x Hin).
    Qed.

    (** Low observability is preserved under scope agreement.

        Relation to the paper:
        if two ground instantiations agree on the symbolic identifiers that
        classify one raw variable, then that variable has the same
        low-observability status under both instantiations.  This is the
        valuation-transport step needed after replay. *)
    Lemma low_var_agree_on_scope:
      forall ty_env t scope dlt1 dlt2 x alpha,
        Env.find x ty_env = Some alpha ->
        In alpha scope ->
        SecT.agree_on scope dlt1 dlt2 ->
        low_var ty_env dlt1 t x ->
        low_var ty_env dlt2 t x.
    Proof.
      intros ty_env t scope dlt1 dlt2 x alpha Hfind Hinscope Hagree Hlow.
      destruct Hlow as (alpha' & Hfind' & Hle).
      rewrite Hfind in Hfind'.
      inversion Hfind'. subst alpha'. clear Hfind'.
      exists alpha.
      split; [exact Hfind|].
      rewrite <- (Hagree alpha Hinscope).
      exact Hle.
    Qed.

    (** Transport low-equivalence across agreeing valuations.

        Relation to the paper:
        replay changes the valuation used to interpret symbolic security
        identifiers, but it keeps the visible signature scope unchanged.
        This lemma lifts that scope agreement from individual variables to the
        relational history observation [history_low_eq]. *)
    Lemma history_low_eq_agree_on_scope:
      forall ty_env t X scope dlt1 dlt2 H H',
        (forall x, In x X -> exists alpha, Env.find x ty_env = Some alpha /\ In alpha scope) ->
        SecT.agree_on scope dlt1 dlt2 ->
        history_low_eq ty_env dlt1 t X H H' ->
        history_low_eq ty_env dlt2 t X H H'.
    Proof.
      intros ty_env t X scope dlt1 dlt2 H H' Hscope Hagree Hlow k x Hin Hobs.
      apply Hlow; [exact Hin|].
      destruct (Hscope x Hin) as (alpha & Hfind & Hinscope).
      eapply low_var_agree_on_scope; eauto.
      eapply agree_on_sym; eauto.
    Qed.

    (** Low-equivalence weakens along observation-set inclusion.

        Relation to the paper:
        once the proof establishes agreement on a larger visible set, it may
        immediately be restricted to any smaller observed interface such as the
        node outputs. *)
    Lemma history_low_eq_weaken:
      forall ty_env dlt t X Y H H',
        (forall x, In x Y -> In x X) ->
        history_low_eq ty_env dlt t X H H' ->
        history_low_eq ty_env dlt t Y H H'.
    Proof.
      intros ty_env dlt t X Y H H' Hsub Hlow k x Hin Hobs.
      eapply Hlow; eauto.
    Qed.

    (** Replaying the stored node signature back to raw equation constraints.

        Relation to the paper:
        the paper-level node security hypothesis only stores the simplified
        node constraints [ρ].  The indexed noninterference proof for
        [vars_defined] must reason about the raw per-equation constraints
        before local variables are eliminated.  This lemma is the source-side
        bridge from the stored satisfiability fact [signature_satisfied dlt sig]
        to a completed ground instantiation that satisfies the raw
        constraints and still agrees with the original [dlt] on the visible
        signature scope.

        Concretely, the lemma states that whenever the generated scoped node
        signature [sig] is satisfied by [dlt], one can recover:

        - the exact raw equation-constraint generation data for the current
          node (clock/reset security ids, input/output/local mappings, and the
          raw constraint list [raw]); and
        - a completed valuation [dlt_raw] such that:
          [SecT.agree_on (signature_scope sig) dlt dlt_raw] and
          [SecT.listSatisfiable dlt_raw raw].

        So this lemma is precisely what lets the later proof move from the
        stored simplified signature back to the unsimplified per-equation
        constraints without losing agreement on the externally visible
        interface. *)
    Lemma signature_satisfied_replays_raw:
      forall P n ty_env sig dlt,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Clo.wc_node P n ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        signature_satisfied dlt sig ->
        exists dlt_raw clk_id rst_id clk_type rst_type inp out locals raw st_n,
          get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id ty_env = Some clk_type
          /\ Env.find rst_id ty_env = Some rst_type
          /\ get_mappings_from_node n.(n_in) ty_env = Some inp
          /\ get_mappings_from_node n.(n_out) ty_env = Some out
          /\ get_mappings_from_node n.(n_vars) ty_env = Some locals
          /\ generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n)
          /\ sig = {| s_name := n.(n_name);
                      s_in := inp;
                      s_out := out;
                      s_reset := rst_type;
                      s_clk := clk_type;
                      s_constraints := SymTypes.simplify raw locals |}
          /\ SecT.agree_on (signature_scope sig) dlt dlt_raw
          /\ SecT.listSatisfiable dlt_raw raw.
    Proof.
      intros P n ty_env sig dlt
             Henvsgen Hwc Hfindnode Hfindenv Hsigsc Hsatsig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigsc.
      rewrite Hfindenv in Hsigsc.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv
           G n ty_env aux_names sig Hsigsc)
        as Hinv.
      destruct Hinv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef).
      pose proof (find_node_In _ _ _ Hfindnode) as [_ Hin].
      apply in_split in Hin as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'. clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node as
          (envs_pref & aux_pref & st_pref & local_env & rec & st_local
           & envs_cur & st_cur & Hpref & Hlocalgen & Hins & Htail);
        eauto.
      assert (Hcurfind : find_node_env n.(n_name) envs_cur = Some local_env).
      { eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto. }
      assert (Hlocalfind : find_node_env n.(n_name) envs = Some local_env).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto. }
      rewrite Hfindenv in Hlocalfind.
      inversion Hlocalfind.
      assert (Hauxhead :
                get_node_aux n.(n_name) (rec :: aux_pref) =
                Some (rec.(nclk), rec.(nrst))).
      {
        pose proof Hlocalgen as Hlocalshape.
        unfold NAMEGEN.generate_local_env_for_node in Hlocalshape.
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (clk_name & stc & Hclkgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (rst_name & str & Hrstgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (env0 & ste & Henvgen & Hret0).
        unfold NAMEGEN.NMret in Hret0.
        inversion Hret0; subst rec st_local.
        unfold get_node_aux. simpl.
        rewrite ident_eqb_refl. reflexivity.
      }
      assert (Hauxrec :
                get_node_aux n.(n_name) aux_names =
                Some (rec.(nclk), rec.(nrst))).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto. }
      rewrite Haux in Hauxrec.
      inversion Hauxrec; subst clk_id rst_id.
      assert (Hsigshape :
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}
                =
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}).
      { reflexivity. }
      subst ty_env sig.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_from_local_env
           G n
           {| s_name := n.(n_name);
              s_in := inp;
              s_out := out;
              s_reset := rst_type;
              s_clk := clk_type;
              s_constraints := SymTypes.simplify raw locals |}
           local_env rec aux_names st_pref st_local
           clk_type rst_type inp out locals raw st_n
           Hlocalgen Hsigsc Hclk Hrst Hinp Hout Hlocals Hraw Hsigshape)
        as Hready.
      destruct Hready as [Hwfraw Hlocalsdisj].
      edestruct (SecT.simplify_complete
                   raw locals
                   (signature_scope
                      {| s_name := n.(n_name);
                         s_in := inp;
                         s_out := out;
                         s_reset := rst_type;
                         s_clk := clk_type;
                         s_constraints := SymTypes.simplify raw locals |})
                   dlt)
        as (dlt_raw & Hagree & Hsatraw); eauto. 
        exists dlt_raw, rec.(nclk), rec.(nrst), clk_type, rst_type, inp, out, locals, raw, st_n.
        repeat split; auto.
    Qed.

    (** Restrict the NLustre causality induction to defined variables.

        Relation to the paper:
        the source causality proof naturally propagates a pointwise property
        over the whole node variable set (inputs, locals, outputs).  The
        internal noninterference theorem only needs the conclusion on
        [vars_defined n.(n_eqs)], because that is the exact set tracked by the
        generated raw constraints.  This lemma is the packaging step from the
        full node-level causality induction back down to the defined-variable
        view used in the theorem statement. *)
    Lemma nl_node_causal_ind_defined:
      forall (n : node) (P_var : ident -> Prop),
        (forall eq x,
            In eq n.(n_eqs) ->
            In x (var_defined eq) ->
            (forall y, NLCaus.nl_depends_on_eq eq x y -> P_var y) ->
            P_var x) ->
        Forall P_var (map fst n.(n_in)) ->
        NLCaus.nl_node_causal n ->
        Forall P_var (vars_defined n.(n_eqs)).
    Proof.
      intros n P_var Heqcase Hinputs Hcaus.
      pose proof
        (NLCaus.nl_node_causal_ind
           n P_var Heqcase Hinputs Hcaus)
        as Hall.
      rewrite map_app in Hall.
      apply Forall_app in Hall as [_ Hdefd].
      rewrite n.(n_defd).
      exact Hdefd.
    Qed.

    (** Turn input low-equivalence into the pointwise input property used by
        the causality induction.

        Relation to the paper:
        the base case of the node-level causality induction is agreement on
        low inputs.  The semantic hypothesis is stated relationally as
        [history_low_eq], while the induction consumes one pointwise property
        per input variable. *)
    Lemma history_low_eq_inputs_pointwise:
      forall (n : node) ty_env dlt t H H',
        history_low_eq ty_env dlt t (map fst n.(n_in)) H H' ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall k, Env.find x (H k) = Env.find x (H' k))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' Hlow.
      apply Forall_forall.
      intros x Hin Hobs k.
      eapply Hlow; eauto.
    Qed.

    (** Turn prefix input low-equivalence into the pointwise input property
        consumed by the prefix step theorem.

        Relation to the paper:
        the time-indexed node proof reasons about one finite prefix at a time.
        This is the prefix counterpart of the basic input-agreement
        initialisation. *)
    Lemma history_low_eq_upto_inputs_pointwise:
      forall (n : node) ty_env dlt t H H' k,
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' k ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall j, j <= k -> Env.find x (H j) = Env.find x (H' j))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' k Hlow.
      apply Forall_forall.
      intros x Hin Hobs j Hj.
      eapply Hlow; eauto.
    Qed.

    (** Extract one equation's raw constraint block from the node-wide
        generation result.

        Relation to the paper:
        the node proof proceeds equation by equation, but the generated source
        typing stores all raw constraints in one concatenated list.  This
        lemma is the bookkeeping step that recovers the exact sublist produced
        by one equation. *)
        (*Move this to SecNLusTyping.v later after proofs are done*)
    Lemma generate_eqns_constraints_member:
      forall ty_env clk_type rst_type eqs raw st st' eq,
        In eq eqs ->
        generate_eqns_constraints G ty_env clk_type rst_type eqs st = OK (raw, st') ->
        exists ceq pre post steq stceq,
          raw = pre ++ ceq ++ post
          /\ generate_eqn_constraint G ty_env clk_type rst_type eq steq = OK (ceq, stceq).
    Proof.
      intros ty_env clk_type rst_type eqs.
      induction eqs as [|eq0 eqs IH]; intros raw st st' eq Hin Hgen.
      - inversion Hin.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c0 & st1 & Hc0 & Hgen).
        eapply sec_bind_inv in Hgen as (cs0 & st2 & Hcs0 & Hret).
        unfold ret in Hret. inversion Hret; subst raw st'. clear Hret.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst eq.
          exists c0, [], cs0, st, st1.
          split; [reflexivity|exact Hc0].
        + destruct (IH cs0 st1 st2 eq Hin Hcs0)
            as (ceq & pre & post & steq & stceq & Hraw & Hgeq).
          exists ceq, (c0 ++ pre), post, steq, stceq.
          split.
          * rewrite Hraw. now rewrite app_assoc.
          * exact Hgeq.
    Qed.

    (** Recover satisfiability of one extracted raw block.

        Relation to the paper:
        once an equation's raw constraint sublist is isolated, the local
        noninterference cases only need satisfiability of that one block. *)
    Lemma listSatisfiable_app_middle:
      forall dlt pre mid post,
        SecT.listSatisfiable dlt (pre ++ mid ++ post) ->
        SecT.listSatisfiable dlt mid.
    Proof.
      intros dlt pre mid post Hsat.
      unfold SecT.listSatisfiable in *.
      repeat rewrite Forall_app in Hsat.
      destruct Hsat as [_ [Hmid _]].
      exact Hmid.
    Qed.

    (** Invert the actual-argument typing map produced at a call site.

        Relation to the paper:
        the call case needs to connect each actual expression with the
        generated symbolic type used in the instantiated callee valuation.
        This lemma extracts that pointwise correspondence from the monadic
        [mmap] returned by [generate_eqn_constraint]. *)
    Lemma mmap_assign_exp_type_inv:
      forall ty_env es tys st st',
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        st' = st
        /\ Forall2
             (fun e ty => SECCETYPING.assign_exp_type ty_env e = Some ty)
             es tys.
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' Hmap.
      - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst.
        split; [reflexivity|constructor].
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ Htl) as [Hst Htys].
        subst st2.
        unfold ret in Hret. inversion Hret; subst tys st'.
        split; [reflexivity|].
        constructor; auto.
    Qed.

    (** [option_to_sec] on clock typing is state-irrelevant.

        Relation to the paper:
        extracted raw call constraints are located at some intermediate
        monadic state inside [generate_eqns_constraints], but the underlying
        symbolic clock assignment is pure.  This helper normalises such
        premises back to an arbitrary starting state when replaying the call
        theorem. *)
    Lemma option_to_sec_assign_clk_state_irrel:
      forall ty_env base ck st st' ckty st0,
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st = OK (ckty, st') ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st0 = OK (ckty, st0).
    Proof.
      intros ty_env base ck st st' ckty st0 Hck.
      unfold SC.option_to_sec in *.
      destruct (SECCETYPING.assign_clk_type ty_env base ck) as [ckty'|] eqn:Hassign;
        try discriminate.
      inversion Hck; subst.
      reflexivity.
    Qed.

    (** [mmap] of pure expression typings is state-irrelevant.

        Relation to the paper:
        actual-argument typing at a call site depends only on the expressions
        and the caller environment, not on the surrounding monadic state.
        This lets the local noninterference proof replay the extracted raw
        argument typings at the canonical initial state expected by the
        recursive call theorem. *)
    Lemma mmap_assign_exp_type_state_irrel:
      forall ty_env es tys st st' st0,
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st0 = OK (tys, st0).
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' st0 Hmap.
      - simpl in Hmap. unfold SC.ret in Hmap. inversion Hmap; subst.
        reflexivity.
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ st0 Htl).
        unfold SC.ret in Hret. inversion Hret; subst tys st'.
        cbn [SC.mmap].
        cbn [SC.option_to_sec].
        rewrite Heq.
        unfold SC.bind, SC.ret.
        simpl.
        destruct
          (SC.mmap
             (fun e0 : exp => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e0))
             es st0)
          as [[tys0 st0']|err] eqn:Hm.
        + inversion IH; subst. reflexivity.
        + discriminate.
    Qed.

    (** One non-reset call input is low-equal at a chosen instant.

        Relation to the paper:
        in the [EqApp] case, the first reusable semantic step is to show that
        one low callee input variable receives the same value in both runs at a
        fixed instant. This isolates the transport from low-equal caller free
        variables, through actual-expression semantics, into the callee input
        history. *)
    Lemma eqapp_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
             k ii y ity e ety,
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
             k ii y ity e ety
             Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hnthv in Hnthvin.
      inversion Hnthvin; subst vin; clear Hnthvin.
      rewrite Hnthv' in Hnthvin'.
      inversion Hnthvin'; subst vin'; clear Hnthvin'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** Transport one low callee output back to the caller-defined variable.

        Relation to the paper:
        after the recursive call theorem gives low-equivalence on the callee
        outputs, the [EqApp] case still has to reconnect that fact to the
        caller-visible variable defined by the call tuple. This is the
        position-based semantic transport step for one output slot. *)
    Lemma eqapp_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    (** One low reset-call input is low-equal at a chosen instant.

        Relation to the paper:
        this is the reset-aware companion of the plain [EqApp] input transport
        step. The actual expressions are still evaluated in the caller, but
        the callee sees them through the masked reset stream. The proof
        therefore adds exactly one extra bridge: at the current reset segment,
        the masked tuple position agrees with the underlying actual-argument
        tuple position. *)
    Lemma eqapp_reset_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety
             Hkr Hkr' Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (mask kr rs ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (mask kr' rs' ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hkr in Hnthvin.
      rewrite Hkr' in Hnthvin'.
      pose proof
        (nth_error_mask_count_self rs ls k ii vin Hnthvin)
        as Hnthvin0.
      pose proof
        (nth_error_mask_count_self rs' ls' k ii vin' Hnthvin')
        as Hnthvin0'.
      rewrite Hnthv in Hnthvin0.
      inversion Hnthvin0; subst vin; clear Hnthvin0.
      rewrite Hnthv' in Hnthvin0'.
      inversion Hnthvin0'; subst vin'; clear Hnthvin0'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** Transport one low reset-call output back to the caller-defined variable.

        Relation to the paper:
        this is the reset-aware output-slot transport for [EqApp]. The
        recursive theorem gives low-equivalence on the callee outputs under
        the masked run, and this lemma reconnects that masked equality to the
        caller-visible output variable at the same tuple position. *)
    Lemma eqapp_reset_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) (mask kr rs ys) ->
        sem_vars Hc' (map fst callee.(n_out)) (mask kr' rs' ys') ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo
             Hkr Hkr' Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (mask kr rs ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (mask kr' rs' ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      rewrite Hkr in Hnthvo.
      rewrite Hkr' in Hnthvo'.
      pose proof
        (nth_error_mask_count_self rs ys k i vo Hnthvo)
        as Hnthvo0.
      pose proof
        (nth_error_mask_count_self rs' ys' k i vo' Hnthvo')
        as Hnthvo0'.
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo0 in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo0' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    (** Recover the symbolic type at one position of a [get_mappings] result.

        Relation to the paper:
        call equations define several caller variables at once.  The
        noninterference proof needs to relate one chosen caller variable [x]
        with the matching symbolic output type in [outtyp].  This lemma is the
        finite-list position bridge for that lookup. *)
    Lemma get_mappings_nth_error_inv:
      forall xs ty_env tys i x,
        get_mappings xs ty_env = Some tys ->
        nth_error xs i = Some x ->
        exists ty,
          nth_error tys i = Some ty
          /\ Env.find x ty_env = Some ty.
    Proof.
      induction xs as [|y ys IH]; intros ty_env tys i x Hmap Hnth.
      - destruct i; inversion Hnth.
      - simpl in Hmap.
        destruct (Env.find y ty_env) as [yty|] eqn:Hyfind; try discriminate.
        destruct (get_mappings ys ty_env) as [tys'|] eqn:Hys; try discriminate.
        inversion Hmap; subst tys.
        destruct i as [|i].
        + simpl in Hnth. inversion Hnth; subst x.
          exists yty. split; [reflexivity|exact Hyfind].
        + simpl in Hnth.
          specialize (IH ty_env tys' i x Hys Hnth) as (ty & Hnthty & Hfindty).
          exists ty.
          split.
          * exact Hnthty.
          * exact Hfindty.
    Qed.

    (** Successful [get_mappings] preserves list length.

        Relation to the paper:
        call proofs repeatedly move between the syntactic output tuple, its
        generated symbolic mapping, and semantic tuples.  This is the basic
        length bridge behind those position arguments. *)
    Lemma get_mappings_length:
      forall xs ty_env tys,
        get_mappings xs ty_env = Some tys ->
        List.length xs = List.length tys.
    Proof.
      induction xs as [|x xs IH]; intros ty_env tys Hmap.
      - simpl in Hmap. inversion Hmap. reflexivity.
      - simpl in Hmap.
        destruct (Env.find x ty_env) as [xty|] eqn:Hfind; try discriminate.
        destruct (get_mappings xs ty_env) as [tys'|] eqn:Htl; try discriminate.
        inversion Hmap; subst tys.
        simpl. f_equal.
        eapply IH; eauto.
    Qed.

    (** Prefix low-equivalence on plain call inputs from caller-side argument equality.

        Relation to the paper:
        recursive noninterference for a plain [EqApp] call is driven by
        low-equivalence of the callee inputs on the whole prefix considered so
        far. This lemma packages that bridge directly: if every actual
        argument is semantically equal across the two caller runs on the
        prefix, then the instantiated callee input history is low-equivalent
        on that same prefix. *)
    Lemma eqapp_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k,
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k
             Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthinpty & Heqexp).
      eapply
        (eqapp_input_var_low_eq_pointwise
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt rstty ckty t
           bk H H' Hc Hc' exps ls ls'
           j ii y ity e ety); eauto.
      intros z Hz.
      eapply Hfree_eqs.
      - eapply Exists_exists.
        exists e.
        split.
        + eapply nth_error_In.
          exact Hnthe.
        + exact Hz.
      - exact Hj.
    Qed.

    (** Prefix low-equivalence on reset-call inputs for one fixed reset segment.

        Relation to the paper:
        the recursive reset-call theorem is applied to one concrete reset
        segment [kr = count rs k].  This lemma packages the corresponding
        caller-to-callee input transport on the whole prefix: inside the
        active segment the mask is transparent and the proof reduces to the
        ordinary actual-expression argument equality, while outside that
        segment both masked tuples are uniformly absent. *)
    Lemma eqapp_reset_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k,
        kr = count rs k ->
        kr' = count rs' k ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        (forall j, j <= k -> count rs j = count rs' j) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k
             Hkr Hkr' Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs Hcount_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof (get_mappings_from_node_eq _ _ _ _ Hinp_c) as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthinpty & Heqexp).
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        eapply
          (eqapp_reset_input_var_low_eq_pointwise
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety); eauto.
        intros z Hz.
        eapply Hfree_eqs.
        + eapply Exists_exists.
          exists e.
          split.
          * eapply nth_error_In.
            exact Hnthe.
          * exact Hz.
        + exact Hj.
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
          apply Hopaque.
          rewrite Hcntj.
          rewrite Heq.
          rewrite Hkr'.
          rewrite <- Hcntk.
          symmetry.
          exact Hkr.
        }
        specialize (Hsem_vars_in_c j).
        specialize (Hsem_vars_in_c' j).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc j))
             (map fst callee.(n_in)) (mask kr rs ls j) ii y
             Hsem_vars_in_c Hnthy)
          as (vin & Hnthvin & Hsem_y).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc' j))
             (map fst callee.(n_in)) (mask kr' rs' ls' j) ii y
             Hsem_vars_in_c' Hnthy)
          as (vin' & Hnthvin' & Hsem_y').
        rewrite (mask_opaque ls kr rs j Hopaque) in Hnthvin.
        rewrite (mask_opaque ls' kr' rs' j Hopaque') in Hnthvin'.
        pose proof (nth_error_all_absent_absent _ (ls 0) _ _ Hnthvin) as Hvin.
        pose proof (nth_error_all_absent_absent _ (ls' 0) _ _ Hnthvin') as Hvin'.
        unfold sem_var_instant in Hsem_y, Hsem_y'.
        subst vin vin'.
        rewrite Hsem_y, Hsem_y'.
        reflexivity.
    Qed.

    (** Prefix low-equivalence on plain call outputs transported back to the caller.

        Relation to the paper:
        after the recursive callee theorem establishes prefix low-equivalence
        on the callee outputs, the caller proof still has to reconnect that
        prefix fact to the caller-defined output variable at the matching
        tuple position. This is the prefix-level version of that transport. *)
    Lemma eqapp_outputs_low_eq_upto:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        forall j, j <= k -> Env.find x (H j) = Env.find x (H' j).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'
             j Hj.
      eapply
        (eqapp_output_transport_pointwise
           ty_env_c dlt_raw_c t
           H H' Hc Hc' callee
           xs ys ys' j i x yo); eauto.
      eapply history_low_eq_upto_monotone; eauto.
    Qed.

    (** Symbolic types of defined caller variables come from outputs or locals.

        Relation to the paper:
        in a call equation, the generated symbolic output tuple [outtyp]
        belongs to the current node interface of defined variables.  The
        recursive call proof uses this helper to reclassify one chosen caller
        output type as coming from the current node outputs or locals, which
        is exactly the scope later shown fresh from the callee signature. *)
    Lemma defined_var_type_in_out_or_locals:
      forall n ty_env out locals x ty,
        Env.find x ty_env = Some ty ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In x (vars_defined n.(n_eqs)) ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals x ty Hfind Hout Hlocals Hdef.
      assert (Hin_vo : In x (map fst (n.(n_vars) ++ n.(n_out)))).
      {
        eapply Permutation_in; [apply n.(n_defd)|exact Hdef].
      }
      rewrite map_app, in_app_iff in Hin_vo.
      destruct Hin_vo as [Hin_local|Hin_out].
      - apply in_map_iff in Hin_local as ((xlocal, alocal) & Heq & Hin_local).
        simpl in Heq. subst xlocal.
        apply In_InMembers in Hin_local.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_local Hlocals)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. right. exact Hin'.
      - apply in_map_iff in Hin_out as ((xout, aout) & Heq & Hin_out).
        simpl in Heq. subst xout.
        apply In_InMembers in Hin_out.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_out Hout)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. left. exact Hin'.
    Qed.

    (** Two distinct named nodes appear in one linear order in the program list.

        Relation to the paper:
        the call-site freshness argument only needs the source program order
        induced by the generated naming pass.  This lemma packages the pure
        list decomposition step under the standard [NoDup] node-name
        hypothesis. *)
    Lemma find_nodes_linear_order:
      forall n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node n1.(n_name) all_nodes = Some n1 ->
        find_node n2.(n_name) all_nodes = Some n2 ->
        n1.(n_name) <> n2.(n_name) ->
        (exists prefix mid suffix,
            all_nodes = prefix ++ n1 :: mid ++ n2 :: suffix)
        \/ (exists prefix mid suffix,
            all_nodes = prefix ++ n2 :: mid ++ n1 :: suffix).
    Proof.
      intros n1 n2 Hndnames Hfind1 Hfind2 Hneq.
      pose proof (find_node_In _ _ _ Hfind1) as [_ Hin1].
      pose proof (find_node_In _ _ _ Hfind2) as [_ Hin2].
      apply in_split in Hin1 as (prefix1 & suffix1 & Hall1).
      subst all_nodes.
      simpl in Hin2.
      rewrite in_app_iff in Hin2.
      simpl in Hin2.
      destruct Hin2 as [Hin2|[Heq12|Hin2]].
      - apply in_split in Hin2 as (prefix2 & suffix2 & Hprefix2).
        right.
        exists prefix2, suffix2, suffix1.
        rewrite Hprefix2. repeat rewrite <- app_assoc. reflexivity.
      - subst n2.
        exfalso. apply Hneq. reflexivity.
      - apply in_split in Hin2 as (mid & suffix2 & Hsuffix2).
        left.
        exists prefix1, mid, suffix2.
        rewrite Hsuffix2. repeat rewrite <- app_assoc. reflexivity.
    Qed.

    (** Unique lookup of one source node under unique node names.

        Relation to the paper:
        recursive call proofs extract one semantic node witness from each run.
        Under the standard source assumption that node names are unique, both
        witnesses for the same callee name must coincide.  This is the exact
        source-side canonicalisation step used before applying the recursive
        raw-output theorem. *)
    Lemma find_node_unique_nodup:
      forall f n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node f all_nodes = Some n1 ->
        find_node f all_nodes = Some n2 ->
        n1 = n2.
    Proof.
      intros f n1 n2 _ Hfind1 Hfind2.
      revert f n1 n2 Hfind1 Hfind2.
      induction all_nodes as [|nd nds IH]; intros f n1 n2 Hfind1 Hfind2.
      - discriminate.
      - simpl in Hfind1, Hfind2.
        destruct (ident_eqb nd.(n_name) f) eqn:Hname.
        + inversion Hfind1; inversion Hfind2; subst; reflexivity.
        + eapply IH; eauto.
    Qed.

    (** Ordered source nodes already have unique names.

        Relation to the paper:
        the recursive source proof is naturally stated over [Ordered_nodes].
        Whenever the naming-layer helpers need explicit uniqueness of source
        node names, this lemma is the bridge back to the [NoDup] list form. *)
    Lemma Ordered_nodes_nodup_names:
      forall nodes,
        Ordered_nodes nodes ->
        NoDup (map n_name nodes).
    Proof.
      intros nodes Hord.
      induction Hord as [|nd nds Hord IH Hcalls Hfresh].
      - constructor.
      - simpl. constructor.
        + intro Hin.
          apply in_map_iff in Hin as (nd' & Heq & Hin').
          rewrite Forall_forall in Hfresh.
          specialize (Hfresh _ Hin').
          simpl in Heq.
          apply Hfresh.
          symmetry.
          exact Heq.
        + exact IH.
    Qed.

    (** Generated node interfaces have pairwise distinct visible symbolic
        identifiers.

        Relation to the paper:
        recursive call proofs instantiate input/output substitution lemmas
        from [SIFSignature], which require [NoDup] on the callee visible
        signature scope.  For generated NLustre signatures this is a pure
        naming-side fact, recovered here directly from the successful
        node-scoped environment generation. *)
    Lemma generated_sig_scope_nodup_scoped_env:
      forall n ty_env clk_id rst_id clk_type rst_type inp out,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        NoDup
          (SIG.signature_scope
             {| s_name := n.(n_name);
                s_in := inp;
                s_out := out;
                s_reset := rst_type;
                s_clk := clk_type;
                s_constraints := nil |}).
    Proof.
      intros n ty_env clk_id rst_id clk_type rst_type inp out
             Henvsgen Hfindnode Hfindenv Haux Hclk Hrst Hinp Hout.
      pose proof (find_node_In _ _ _ Hfindnode) as (_ & Hinnode).
      apply in_split in Hinnode as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref & aux_pref & st_pref
            & local_env & rec & st_local
            & envs_cur & st_cur
            & Hpref & Hlocal & Hins & Htail);
        eauto.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof
          (NAMEGEN.generate_node_scoped_env'_preserves_find
             _ _ _ _ _ _ _ _ _ Htail Hfind_cur)
          as Hfind_final.
        exact Hfind_final.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrec_name.
        assert (Haux_cur : get_node_aux n.(n_name) (rec :: aux_pref) = Some (rec.(nclk), rec.(nrst))).
        {
          unfold get_node_aux.
          simpl.
          rewrite <- Hrec_name.
          rewrite ident_eqb_refl.
          reflexivity.
        }
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
      }
      rewrite Hfindenv in Hfindlocal.
      inversion Hfindlocal; subst local_env.
      rewrite Haux in Hauxlocal.
      inversion Hauxlocal; subst clk_id rst_id.
      eapply SECNLUSTYPINGCORRECTNESS.generate_node_sig_scope_nodup_from_local_env;
        eauto.
    Qed.

    (** Fresh insertion into the node-scoped naming table does not advance
        the name-generation state.

        Relation to the paper:
        the node-scoped naming pass only uses the global state when it
        allocates fresh security identifiers inside one node-local
        environment.  Inserting that finished local env into the outer
        node-indexed table is pure bookkeeping.  The later cross-node
        separation proof relies on this to compare the numeric ranges of two
        generated node scopes precisely. *)
    Lemma fresh_insert_node_env_state:
      forall envs0 name local_env st envs' st',
        NAMEGEN.fresh_insert_node_env envs0 name local_env st = OK (envs', st') ->
        st' = st.
    Proof.
      intros envs0 name local_env st envs' st' Hins.
      unfold NAMEGEN.fresh_insert_node_env in Hins.
      destruct (Env.mem name envs0) eqn:Hmem; try discriminate.
      unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
      inversion Hins; reflexivity.
    Qed.

    (** Freshness from caller-upper versus callee-lower bounds.

        Relation to the paper:
        one direct call proof case needs the opposite orientation from the
        standard accumulator freshness theorem.  If every symbolic identifier
        in the current caller scope is strictly below some pivot [st], and
        every visible identifier in the callee signature is at least [st],
        then the two scopes are disjoint. *)
    Lemma scope_fresh_from_upper_lower_bounds:
      forall scope sig st,
        (forall ty,
            In ty scope ->
            exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive) ->
        (forall ty,
            In ty (signature_scope sig) ->
            exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive) ->
        SIG.scope_fresh scope sig.
    Proof.
      intros scope sig st Hupper Hlower ty Hinscope Hinsig.
      destruct (Hupper ty Hinscope) as (n1 & Hty1 & Hlt1).
      destruct (Hlower ty Hinsig) as (n2 & Hty2 & Hle2).
      rewrite Hty1 in Hty2.
      apply gensym_injective in Hty2 as [_ Heq]. subst n2.
      eapply Pos.lt_irrefl.
      eapply Pos.lt_le_trans; eauto.
    Qed.

    (** Every mapped call output type belongs to the current caller scope.

        Relation to the paper:
        the NLustre call proof needs the symbolic output tuple produced for a
        call equation to be recognised as part of the current caller-visible
        scope.  This is the source-side bridge from the tuple mapping
        [get_mappings xs ty_env] back to the generated raw variable scope of
        the surrounding node. *)
    Lemma eqapp_outtyp_in_out_or_locals:
      forall n ty_env out locals xs ck f exps r outtyp ty,
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        get_mappings xs ty_env = Some outtyp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In ty outtyp ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals xs ck f exps r outtyp ty
             Heqin Hmap Hout Hlocals Hin.
      destruct (get_mappings_In _ _ _ _ Hmap Hin) as (x & Hinx & Hfindx).
      assert (Hxdef : In x (vars_defined n.(n_eqs))).
      {
        unfold vars_defined.
        apply in_flat_map.
        exists (EqApp xs ck f exps r).
        split; [exact Heqin|exact Hinx].
      }
      eapply defined_var_type_in_out_or_locals; eauto.
    Qed.

    (** Caller scope freshness against a distinct generated callee signature.

        Relation to the paper:
        ordinary and resettable call proofs both instantiate the callee
        signature with symbolic types coming from the current caller node.
        To use the standard signature substitution lemmas, those caller-side
        identifiers must be disjoint from the visible callee signature scope.
        In the node-scoped naming discipline this follows purely from the
        relative generation order of the two nodes: two distinct node-local
        scopes live in disjoint numeric [sec] ranges. *)
    Lemma generated_caller_scope_fresh_scoped_env:
      forall caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        NoDup (map n_name all_nodes) ->
        find_node caller.(n_name) all_nodes = Some caller ->
        find_node callee.(n_name) all_nodes = Some callee ->
        caller.(n_name) <> callee.(n_name) ->
        find_node_env caller.(n_name) envs = Some caller_env ->
        find_node_env callee.(n_name) envs = Some callee_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G callee envs aux_names = OK callee_sig ->
        get_node_aux caller.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id caller_env = Some clk_type ->
        Env.find rst_id caller_env = Some rst_type ->
        get_mappings_from_node caller.(n_in) caller_env = Some inp ->
        get_mappings_from_node caller.(n_out) caller_env = Some out ->
        get_mappings_from_node caller.(n_vars) caller_env = Some locals ->
        SIG.scope_fresh
          (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
          callee_sig.
    Proof.
      intros caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals
             Henvsgen Hndnames Hfindcaller Hfindcallee Hneq
             Hfindenvcaller Hfindenvcallee Hsiggencallee
             Hauxcaller Hclkcaller Hrstcaller
             Hinpcaller Houtcaller Hlocalscaller.
      pose proof
        (find_nodes_linear_order
           caller callee Hndnames Hfindcaller Hfindcallee Hneq)
        as Hord.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           all_nodes (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st_final]|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsiggencallee.
      rewrite Hfindenvcallee in Hsiggencallee.
      destruct Hord as
          [(prefix & mid & suffix & Hall)
          |(prefix & mid & suffix & Hall)];
        subst all_nodes.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_call) as Hcall_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_call Hfind_call_cur)
            as Hfind_call_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_call Hfind_call_pref)
            as Hfind_call_after_cal.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_call_after_cal)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_cal_cur)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_upper :
                  forall ty,
                    In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (m < st_pref_call)%positive).
        {
          intros ty Hin.
          destruct
            (node_scope_upper_bounded_from_local_env
               caller st_pref_cal local_env_cal rec_cal st_local_cal
               clk_id rst_id clk_type rst_type inp out locals ty
               Hlocal_cal Hclkcaller Hrstcaller Hinpcaller Houtcaller Hlocalscaller Hin)
            as (m & Hm & Hlt).
          exists m. split; auto.
          eapply Pos.lt_le_trans; eauto.
          rewrite <- Hcur_cal. exact Hcall_mid_le.
        }
        assert (Hcallee_lower :
                  forall ty,
                    In ty (signature_scope callee_sig) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (st_pref_call <= m)%positive).
        {
          intros ty Hin.
          destruct
            (SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_lower_bound_from_local_env
               G callee local_env_call aux_names callee_sig
               st_pref_call rec_call st_local_call ty
               Hlocal_call Hsiggencallee Hin)
            as (m & Hm & Hlo).
          exists m. split; auto.
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
        }
        eapply scope_fresh_from_upper_lower_bounds; eauto.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_cal) as Hcal_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_call_cur)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_cal Hfind_cal_cur)
            as Hfind_cal_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_cal Hfind_cal_pref)
            as Hfind_cal_after_call.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_cal_after_call)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_lower :
                  SIG.scope_lower_bounded
                    (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                    st_pref_cal).
        {
          eapply SECNLUSTYPINGCORRECTNESS.node_scope_lower_bounded_from_local_env; eauto.
        }
        assert (Hcallee_upper0 :
                  SIG.signature_scope_bounded_above callee_sig st_local_call).
        {
          intros ty Hin.
          eapply SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_upper_bound_from_local_env
            with (rec := rec_call) (st := st_pref_call) (st' := st_local_call)
                 (aux_names := aux_names); eauto.
        }
        assert (Hcallee_upper :
                  SIG.signature_scope_bounded_above callee_sig st_pref_cal).
        {
          eapply SIG.signature_scope_bounded_above_monotone; eauto.
          rewrite <- Hcur_call. exact Hcal_mid_le.
        }
        eapply SIG.scope_fresh_from_bounds; eauto.
    Qed.

    (** Invert the generated raw block for one [EqDef].

        Relation to the paper:
        this exposes the exact symbolic typing data behind the simple
        combinational case, so the semantic branch can invoke the already
        proved simple-security lemmas without re-running ad hoc monadic
        analysis. *)
    Lemma generate_eqdef_constraint_inv:
      forall ty_env base_ty rst_ty x ck ce cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqDef x ck ce) st =
        OK (cns, st') ->
        exists ckty cety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ cety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_cexp_type ty_env ce = Some cety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck ce cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (cety & st2 & Hce & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in Hce.
      destruct (SECCETYPING.assign_cexp_type ty_env ce) as [cety'|] eqn:Hce';
        try discriminate.
      inversion Hce; subst cety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', cety', xty'.
      repeat split; reflexivity.
    Qed.

    (** Invert the generated raw block for one [EqFby].

        Relation to the paper:
        this is the delay-side counterpart of
        [generate_eqdef_constraint_inv].  It exposes the exact symbolic
        clock, source-expression, and target-variable types used by the raw
        typing constraint. *)
    Lemma generate_eqfby_constraint_inv:
      forall ty_env base_ty rst_ty x ck c0 e cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqFby x ck c0 e) st =
        OK (cns, st') ->
        exists ckty ety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ ety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_exp_type ty_env e = Some ety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck c0 e cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (ety & st2 & He & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in He.
      destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:He';
        try discriminate.
      inversion He; subst ety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', ety', xty'.
      repeat split; reflexivity.
    Qed.

    (** Invert the generated raw block for one non-reset node call.

        Relation to the paper:
        the call case is the first point where the local NLustre proof stops
        working directly on simple expressions and must recover the full
        call-site instantiation data used to build the callee constraints. *)
    Lemma generate_eqapp_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps None) st = OK (cns, st') ->
        exists callee_sig ckty inptyp outtyp st_clk st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_clk = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty [rst_ty] outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      exists callee_sig, ckty, inptyp, (xty' :: tys'), st_clk, st_inp.
      repeat split; auto.
    Qed.

    (** Invert the generated raw block for one resettable node call.

        Relation to the paper:
        this is the reset-aware companion of
        [generate_eqapp_constraint_inv].  It exposes the reset guard typing
        and the instantiated reset type passed to the callee signature. *)
    Lemma generate_eqreset_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps r ckr cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps (Some (r, ckr))) st = OK (cns, st') ->
        exists callee_sig ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ Env.find r ty_env = Some rty
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env rst_ty ckr) st_clk =
               OK (rstty, st_rst)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_rst = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty ([rty] ⊔ rstty) outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps r ckr cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (rty & st_rty & Hrty & Hgen).
      eapply sec_bind_inv in Hgen as (rstty & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      unfold SC.find_env in Hrty.
      destruct (Env.find r ty_env) as [rty'|] eqn:Hrfind; try discriminate.
      unfold SC.ret in Hrty. inversion Hrty; subst rty st_rty.
      exists callee_sig, ckty, rty', rstty, inptyp, (xty' :: tys'), st_clk, st_rst, st_inp.
      repeat split; auto.
    Qed.

    (** Recover the interface lengths of an instantiated call block.

        Relation to the paper:
        call-site transport lemmas use positional correspondence between the
        stored signature interface and the caller actuals.  Those list-length
        equalities are already forced by [generate_constraints], and this
        lemma exposes them once so the call proof can reuse them directly. *)
    Lemma generate_constraints_lengths:
      forall sig inp clk rst out cns st st',
        SIG.generate_constraints sig inp clk rst out st = OK (cns, st') ->
        List.length sig.(s_in) = List.length inp
        /\ List.length sig.(s_out) = List.length out.
    Proof.
      intros sig inp clk rst out cns st st' Hgen.
      unfold SIG.generate_constraints in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
      eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
      eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hgen).
      split.
      - eapply SIGPROOFS.subst_constraints_inp_map_length; eauto.
      - eapply SIGPROOFS.subst_constraints_out_map_length; eauto.
    Qed.

    (** Weakening list membership across an appended suffix.

        Relation to the paper:
        this is a pure list-bookkeeping lemma used in the call proof to lift
        caller output/local scope membership into the larger generated caller
        scope that also includes clock/reset identifiers. *)
    Lemma In_app_weaken_right:
      forall (A : Type) (x : A) a b ,
        In x a ->
        In x (a ++ b).
    Proof.
      intros A x a b Hin.
      apply in_or_app.
      left.
      exact Hin.
    Qed.

    (** Output-formal lookup under instantiated valuations with only output freshness.

        Relation to the paper:
        the NLustre call proof only needs the output part of the standard
        call-substitution equality theorem.  Keeping the premise focused on
        actual output freshness avoids re-proving irrelevant input-side facts
        at each call site. *)
    Lemma inst_valuation_outputs_eq_outputs_fresh:
      forall dlt sig inp clk rst out,
        SIG.outputs_fresh (signature_scope sig) out ->
        NoDup (signature_scope sig) ->
        List.length sig.(s_out) = List.length out ->
        Forall2
          (fun x v =>
             SIGPROOFS.inst_valuation dlt sig inp clk rst out v =
             SIGPROOFS.inst_valuation dlt sig inp clk rst out x)
          sig.(s_out) out.
    Proof.
      intros dlt sig inp clk rst out Houtfresh Hndscope Hlen.
      destruct sig as [sname sin sout sreset sclk sconstraints].
      simpl in *.
      set (sigfull :=
             {| s_name := sname;
                s_in := sin;
                s_out := sout;
                s_reset := sreset;
                s_clk := sclk;
                s_constraints := sconstraints |}).
      set (ival := SIGPROOFS.inst_valuation dlt sigfull inp clk rst out).
      destruct (SIGPROOFS.sig_scope_nodup_decomp sigfull Hndscope)
        as [_ [Hnout [Hfreshin [Houtnotin _]]]].
      assert (Htail :
                Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v)
                        sout out).
      {
        eapply SIGPROOFS.upd_idents_rev_eq_on_pairs.
        - intros x Hin. unfold signature_scope. apply in_or_app. right.
          apply in_or_app. left. exact Hin.
        - exact Houtfresh.
        - exact Hnout.
        - exact Hlen.
      }
      assert (Houtsafe :
                forall x,
                  In x sout ->
                  ~ In x sin /\ ~ In x [sclk; sreset]).
      {
        intros x Hinout.
        split.
        - intro Hinin.
          rewrite Forall_forall in Hfreshin.
          specialize (Hfreshin _ Hinin).
          apply Hfreshin.
          apply in_app_iff. left. exact Hinout.
        - rewrite Forall_forall in Houtnotin.
          exact (Houtnotin _ Hinout).
      }
      assert (Hformal :
                forall x,
                  In x sout ->
                  ival x = upd_idents_rev dlt sout out x).
      {
        intros x Hinout.
        unfold ival, SIGPROOFS.inst_valuation.
        rewrite upd_types_rev_outside.
        2:{
          destruct (Houtsafe x Hinout) as [Hxin _].
          exact Hxin.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now left; symmetry.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now right; left; symmetry.
        }
        reflexivity.
      }
      assert (Hactual :
                forall v,
                  In v out ->
                  ival v = dlt v).
      {
        intros v Hinout.
        unfold ival.
        eapply SIGPROOFS.inst_valuation_outside_sig_scope.
        unfold SIG.outputs_fresh in Houtfresh.
        rewrite Forall_forall in Houtfresh.
        exact (Houtfresh _ Hinout).
      }
      assert (HformalF : Forall (fun x => ival x = upd_idents_rev dlt sout out x) sout).
      {
        rewrite Forall_forall.
        intros x Hin.
        exact (Hformal x Hin).
      }
      assert (HactualF : Forall (fun v => ival v = dlt v) out).
      {
        rewrite Forall_forall.
        intros v Hin.
        exact (Hactual v Hin).
      }
      assert
        (Hconv :
           forall xs ys,
             Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v) xs ys ->
             Forall (fun x => ival x = upd_idents_rev dlt sout out x) xs ->
             Forall (fun v => ival v = dlt v) ys ->
             Forall2 (fun x v => ival v = ival x) xs ys).
      {
        intros xs ys Hrel.
        induction Hrel; intros Hf1 Hf2.
        - constructor.
        - inversion Hf1 as [|x' xs' Hx Hxs]; subst.
          inversion Hf2 as [|y' ys' Hy Hys]; subst.
          constructor.
          + transitivity (dlt y).
            * exact Hy.
            * rewrite Hx. symmetry. exact H.
          + eapply IHHrel; eauto.
      }
      eapply Hconv; eauto.
    Qed.

    (** Internal prefix raw-output specification for one generated node.

        Relation to the paper:
        this is a proof-internal target only.  The public theorem talks about
        whole output streams, but the proof of [EqFby] and recursive calls is
        naturally by induction on the current instant.  This internal spec
        therefore records output noninterference only up to a chosen prefix
        bound [k].  It is the exact recursive shape consumed by the local
        step theorem. *)
    Definition node_outputs_raw_spec
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
      forall k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node nd.(n_name) all_nodes = Some nd ->
        find_node_env nd.(n_name) envs = Some ty_env ->
        SIG.find_signature nd.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
        get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node nd.(n_in) ty_env = Some inp ->
        get_mappings_from_node nd.(n_out) ty_env = Some out ->
        get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := nd.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names nd dlt_sig dlt_raw ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') nd.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_out)) H H' k.

    (** Internal prefix step theorem on all defined variables.

        Relation to the paper:
        this is the local heart of the indexed proof.  It propagates
        low-equivalence from inputs to [vars_defined n.(n_eqs)] on a finite
        time prefix, using:

        - source causality for instantaneous dependencies;
        - a time induction for delayed [EqFby] dependencies; and
        - the internal raw-output prefix spec recursively on direct callees.

        The output-facing raw theorem below should only be a weakening
        corollary of this step result. *)
    Theorem node_noninterference_vars_defined_step:
      forall n dlt_sig dlt_raw k
             ty_env sig t bk H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SIG.find_signature n.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := n.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        (forall xs ck f exps callee callee_sig
                ckty inptyp outtyp st_clk st_inp,
            In (EqApp xs ck f exps None) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_clk = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            node_outputs_raw_spec callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)) ->
        (forall xs ck f exps r ckr callee callee_sig
                ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
            In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            Env.find r ty_env = Some rty ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_reset) ckr)
              st_clk = OK (rstty, st_rst) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_rst = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            forall k_reset,
              reset_control_low_eq_upto ty_env dlt_raw t r H H' k_reset ->
            node_outputs_raw_spec callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)) ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst n.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' k.
    Proof.
      intros n dlt_sig dlt_raw k.
      induction k as [|k IHk];
        intros ty_env sig t bk H H'
               clk_id rst_id clk_type rst_type inp out locals raw st_n
               Henvsgen Hord Hwcglob Hallsig Hcaus Hfindnode Hfindenv
               Hfindsig Hsiggen Haux Hclk Hrst Hinp Hout Hlocals Hraw
               Hsigdef Hsecure Hcallout Hresetout Hsatraw Hsem Hsem' Hlowin.
      - assert
          (Hpts :
             Forall
               (fun x =>
                  low_var ty_env dlt_raw t x ->
                  forall j, j <= 0 -> Env.find x (H j) = Env.find x (H' j))
               (vars_defined n.(n_eqs))).
        {
          pose proof (Ordered_nodes_nodup_names _ Hord) as Hndnames.
          destruct Hsecure as
              [ty_env_sec sig_sec
               clk_id_sec rst_id_sec clk_type_sec rst_type_sec
               inp_sec out_sec locals_sec raw_sec st_n_sec
               Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
               Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
               Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
               Hcallsec_cur Hresetsec_cur].
          rewrite Hfindenv in Hfindenv_sec.
          inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
          rewrite Hfindsig in Hfindsig_sec.
          inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
          rewrite <- H1 in Hcallsec_cur, Hresetsec_cur, Hsatsig_sec, Hagree_sec.
          rewrite Hsigdef in Hcallsec_cur, Hresetsec_cur, Hcallout, Hresetout.
          pose proof Hcallsec_cur as Hcallsec_node.
          pose proof Hresetsec_cur as Hresetsec_node.
          eapply nl_node_causal_ind_defined.
          + intros eq x Heqin Hxdef Hdeps Hlowx j Hj.
            assert (Hj0 : j = 0) by lia.
            subst j.
            destruct eq as [x0 ck ce|xs ck f exps r|x0 ck c0 e];
              simpl in Hxdef.
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqDef x0 ck ce) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqdef_constraint_inv
                   ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
                as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqdef_noninterference_instant_pointwise; eauto.
              intros y Hfree.
              assert (Hlowy : low_var ty_env dlt_raw t y).
              {
                eapply simple_security_caexp; eauto.
              }
              assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
              { split; [reflexivity|exact Hfree]. }
              specialize (Hdeps y Hdep_xy Hlowy 0 (le_n 0)).
              exact Hdeps.
            * destruct xs as [|xh xt].
              { simpl in Hxdef. contradiction. }
              destruct r as [[r ckr]|].
              2:{
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqapp_constraint_inv
                      ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                       & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                   as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
                 destruct (sem_eqapp_inv all_nodes bk H' (xh :: xt) ck f exps Hsem_eq')
                   as (ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock' & Hsem_node_c').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup;
                       [eapply Ordered_nodes_nodup_names; exact Hord
                       |exact Hfindcallee'
                       |exact Hfindcallee]).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps None).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                  (Hcallsec_node
                      (xh :: xt) ck f exps callee nsig_c
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
                   as [P Hwcnode].
                 destruct Hwcnode as [_ [_ [Hwcenv Hwc_eqs]]].
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps None)).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope [rst_type]).
                 {
                   simpl.
                   apply SecT.st_scoped_singleton.
                   repeat (apply in_or_app; right).
                   simpl. now right; left.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps None outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right. 
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_clk0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' 0).
                 {
                   intros j Hj_le y Hiny Hlowy.
                   assert (Hj0 : j = 0) by lia.
                   subst j.
                   pose proof
                     (get_mappings_from_node_eq _ _ _ _ Hinp_c)
                     as Hinp_c_eq.
                   destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
                   destruct
                     (get_mappings_nth_error_inv
                        (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
                     as (ity & Hnthity & Hfindy).
                   assert (Hii_exps : ii < List.length exps).
                   {
                     pose proof (Forall2_length _ _ _ Hforinp0) as Hlen_exps.
                     unfold callee_sig_cur in Hlen_in_c.
                     simpl in Hlen_in_c.
                     rewrite Hlen_exps.
                     rewrite <- Hlen_in_c.
                     apply nth_error_Some.
                     rewrite Hnthity.
                     discriminate.
                   }
                   destruct (nth_error exps ii) as [e|] eqn:Hnthe.
                   2:{
                     apply nth_error_None in Hnthe.
                     lia.
                   }
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
                        exps inptyp0 ii e
                        Hforinp0 Hnthe)
                     as (ety & Hnthety & Heqexp).
                   assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ t).
                   {
                     destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
                     rewrite Hfindy in Hfindalpha.
                     inversion Hfindalpha; subst alpha; clear Hfindalpha.
                     destruct
                       (SecT.Forall2_nth_error_inv
                          _ _
                          (fun x0 ty =>
                             SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                               [rst_type] outtyp0 x0 = SecT.hm_ext dlt_raw ty)
                          (s_in callee_sig_cur) inptyp0 ii ity
                          Hinst_in_eq Hnthity)
                       as (ety' & Hnthety' & Hinsteq).
                     unfold callee_sig_cur in Hnthity.
                     simpl in Hnthity.
                     change (nth_error inptyp0 ii = Some ety) in Hnthety.
                     change (nth_error inptyp0 ii = Some ety') in Hnthety'.
                     rewrite Hnthety in Hnthety'.
                     inversion Hnthety'; subst ety'; clear Hnthety'.
                     rewrite <- Hinsteq.
                     exact Halpha_low.
                   }
                   assert (Hfree_eq :
                             forall z,
                               Is_free_in_exp z e ->
                               Env.find z (H 0) = Env.find z (H' 0)).
                   {
                     intros z Hz.
                     assert (Hlowz : low_var ty_env dlt_raw t z).
                     {
                       eapply exp_type_low; eauto.
                     }
                     assert (Hdep_xz :
                               NLCaus.nl_depends_on_eq
                                 (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
                     {
                       split; [exact Hxdef|].
                       eapply nth_error_free_in_aexps; eauto.
                     }
                     exact (Hdeps z Hdep_xz Hlowz 0 (le_n 0)).
                   }
                   eapply
                     (eqapp_input_var_low_eq_pointwise
                        ty_env ty_env_c callee callee_sig_cur
                        inptyp0 outtyp0 dlt_raw [rst_type] ckty0 t
                        bk H H' Hc Hc' exps ls ls' 0 ii y ity e ety); eauto.
                 }
                 pose proof
                   (Hcallout
                      (xh :: xt) ck callee.(n_name) exps callee callee_sig_cur
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      0 ty_env_c callee_sig_cur t (clock_of ls) (clock_of ls') Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur
                      (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                         ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                         inp_c out_c locals_c raw_c st_n_c
                         Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                         Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                         Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty & Hnthyty & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty.
                   simpl in Hnthyty.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x)
                        (s_out callee_sig_cur) outtyp0 i yty
                        Hinst_out_eq Hnthyty)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 eapply
                   (eqapp_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' 0 i x yo); eauto.
              }
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqreset_constraint_inv
                      ty_env clk_type rst_type xh xt ck f exps r ckr ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & rty0 & rstty0 & inptyp0 & outtyp0
                       & st_clk0 & st_rst0 & st_inp0
                       & Hfindsigc & Hck0 & Hr0 & Hrst0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct
                   (sem_eqreset_inv all_nodes bk H (xh :: xt) ck f exps r ckr Hsem_eq)
                   as (rys & rs & ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock
                       & Hsem_var_r & Hbools_r & Hsem_node_masked).
                 destruct
                   (sem_eqreset_inv all_nodes bk H' (xh :: xt) ck f exps r ckr Hsem_eq')
                   as (rys' & rs' & ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock'
                       & Hsem_var_r' & Hbools_r' & Hsem_node_masked').
                 set (kr := count rs 0).
                 set (kr' := count rs' 0).
                 specialize (Hsem_node_masked kr).
                 specialize (Hsem_node_masked' kr').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup;
                       [eapply Ordered_nodes_nodup_names; exact Hord
                       |exact Hfindcallee'
                       |exact Hfindcallee]).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps (Some (r, ckr))).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hrst0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env rst_type ckr)
                             SC.init_state = OK (rstty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hrst0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                  (Hresetsec_node
                      (xh :: xt) ck f exps r ckr callee nsig_c
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
                   as [P Hwcnode].
                 destruct Hwcnode as [_ [_ [Hwcenv Hwc_eqs]]].
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hins Hwcouts Hreset|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hr_scope : SecT.st_scoped caller_scope [rty0]).
                 {
                   apply SecT.st_scoped_singleton.
                   assert (Hinr_pair :
                             In (r, ckr)
                               (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   destruct (Hvars_scoped r) as (ty0 & Hfindr & Hinscope).
                   - eapply In_InMembers. exact Hinr_pair.
                   - rewrite Hr0 in Hfindr.
                     inversion Hfindr; subst ty0.
                     exact Hinscope.
                 }
                 assert
                   (Hfree_rclock_scope :
                      forall z,
                        Is_free_in_clock z ckr ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   assert (Hwr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ckr).
                   { eapply wc_env_var; eauto. }
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   - eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto.
                   - exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_rst :
                      SECCETYPING.assign_clk_type ty_env rst_type ckr = Some rstty0).
                 {
                   unfold SC.option_to_sec in Hrst0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env rst_type ckr) as [rstty'|]
                     eqn:Hassign; simpl in Hrst0_init; try discriminate.
                   inversion Hrst0_init; now subst rstty'.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope rstty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_type) (ck := ckr).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now right; left.
                   - exact Hfree_rclock_scope.
                   - exact Hassign_rst.
                 }
                 assert (Hrst_join_scope : SecT.st_scoped caller_scope ([rty0] ⊔ rstty0)).
                 {
                   eapply SecT.st_scoped_merge; eauto.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right.
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_rst0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' 0).
                 {
                   intros j Hj_le y Hiny Hlowy.
                   assert (Hj0 : j = 0) by lia.
                   subst j.
                   pose proof
                     (get_mappings_from_node_eq _ _ _ _ Hinp_c)
                     as Hinp_c_eq.
                   destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
                   destruct
                     (get_mappings_nth_error_inv
                        (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
                     as (ity & Hnthity & Hfindy).
                   assert (Hii_exps : ii < List.length exps).
                   {
                     pose proof (Forall2_length _ _ _ Hforinp0) as Hlen_exps.
                     unfold callee_sig_cur in Hlen_in_c.
                     simpl in Hlen_in_c.
                     rewrite Hlen_exps.
                     rewrite <- Hlen_in_c.
                     apply nth_error_Some.
                     rewrite Hnthity.
                     discriminate.
                   }
                   destruct (nth_error exps ii) as [e|] eqn:Hnthe.
                   2:{
                     apply nth_error_None in Hnthe.
                     lia.
                   }
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
                        exps inptyp0 ii e
                        Hforinp0 Hnthe)
                     as (ety & Hnthety & Heqexp).
                   assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ t).
                   {
                     destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
                     rewrite Hfindy in Hfindalpha.
                     inversion Hfindalpha; subst alpha; clear Hfindalpha.
                     destruct
                       (SecT.Forall2_nth_error_inv
                          _ _
                          (fun x0 ty =>
                             SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                               ([rty0] ⊔ rstty0) outtyp0 x0 = SecT.hm_ext dlt_raw ty)
                          (s_in callee_sig_cur) inptyp0 ii ity
                          Hinst_in_eq Hnthity)
                       as (ety' & Hnthety' & Hinsteq).
                     unfold callee_sig_cur in Hnthity.
                     simpl in Hnthity.
                     change (nth_error inptyp0 ii = Some ety) in Hnthety.
                     change (nth_error inptyp0 ii = Some ety') in Hnthety'.
                     rewrite Hnthety in Hnthety'.
                     inversion Hnthety'; subst ety'; clear Hnthety'.
                     rewrite <- Hinsteq.
                     exact Halpha_low.
                   }
                   assert (Hfree_eq :
                             forall z,
                               Is_free_in_exp z e ->
                               Env.find z (H 0) = Env.find z (H' 0)).
                   {
                     intros z Hz.
                     assert (Hlowz : low_var ty_env dlt_raw t z).
                     {
                       eapply exp_type_low; eauto.
                     }
                     assert (Hdep_xz :
                               NLCaus.nl_depends_on_eq
                                 (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
                     {
                       split; [exact Hxdef|].
                       left.
                       eapply nth_error_free_in_aexps; eauto.
                     }
                     exact (Hdeps z Hdep_xz Hlowz 0 (le_n 0)).
                   }
                 eapply
                     (eqapp_reset_input_var_low_eq_pointwise
                        ty_env ty_env_c callee callee_sig_cur
                        inptyp0 outtyp0 dlt_raw ([rty0] ⊔ rstty0) ckty0 t
                        bk H H' Hc Hc' exps rs rs' kr kr' ls ls' 0 ii y ity e ety); eauto.
                 }
                 assert (Hreset_ctrl0 :
                           reset_control_low_eq_upto ty_env dlt_raw t r H H' 0).
                 {
                   eapply reset_control_low_eq_upto_of_sem_var_eq.
                   intros Hlowr j0 Hj0.
                   assert (Hdep_xr :
                             NLCaus.nl_depends_on_eq
                               (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x r).
                   {
                     split; [exact Hxdef|].
                     right. left. reflexivity.
                   }
                   exact (Hdeps r Hdep_xr Hlowr j0 Hj0).
                 }
                 pose proof
                   (Hresetout
                      (xh :: xt) ck callee.(n_name) exps r ckr callee callee_sig_cur
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0
                      0
                      Hreset_ctrl0)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      0 ty_env_c callee_sig_cur t
                      (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur
                      (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                         ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                         inp_c out_c locals_c raw_c st_n_c
                         Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                         Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                         Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty & Hnthyty & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty.
                   simpl in Hnthyty.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty
                        Hinst_out_eq Hnthyty)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 assert (Hkr_eq : kr = count rs 0).
                 { unfold kr. reflexivity. }
                 assert (Hkr'_eq : kr' = count rs' 0).
                 { unfold kr'. reflexivity. }
                 eapply
                   (eqapp_reset_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' rs rs' kr kr' 0 i x yo); eauto.
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqFby x0 ck c0 e) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqfby_constraint_inv
                   ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
                as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqfby_noninterference_delayed_pointwise; eauto.
              -- intros y Hclock.
                 assert (Hlowy : low_var ty_env dlt_raw t y).
                 {
                   eapply simple_security_aexp; eauto using freeAexp2.
                 }
                 assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqFby x0 ck c0 e) x0 y).
                 { split; [reflexivity|exact Hclock]. }
                 specialize (Hdeps y Hdep_xy Hlowy 0 (le_n 0)).
                 exact Hdeps.
              -- intros y Hfree j Hjlt.
                 exfalso. lia.
          + eapply history_low_eq_upto_inputs_pointwise; eauto.
          + eapply NLCaus.nl_global_causal_find; eauto.
        }
        eapply history_low_eq_upto_from_Forall_pointwise; eauto.
      - set (m := S k).
        destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
          as [P Hwcnode].
        pose proof Hwcnode as Hwcnode_full.
        destruct Hwcnode_full as [_ [_ [Hwcenv Hwc_eqs]]].
        assert (Hprev :
                  history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' k).
        {
          eapply IHk with
              (ty_env := ty_env) (sig := sig) (t := t) (bk := bk) (H := H) (H' := H')
              (clk_id := clk_id) (rst_id := rst_id)
              (clk_type := clk_type) (rst_type := rst_type)
              (inp := inp) (out := out) (locals := locals)
              (raw := raw) (st_n := st_n).
          - exact Henvsgen.
          - exact Hord.
          - exact Hwcglob.
          - exact Hallsig.
          - exact Hcaus.
          - exact Hfindnode.
          - exact Hfindenv.
          - exact Hfindsig.
          - exact Hsiggen.
          - exact Haux.
          - exact Hclk.
          - exact Hrst.
          - exact Hinp.
          - exact Hout.
          - exact Hlocals.
          - exact Hraw.
          - exact Hsigdef.
          - exact Hsecure.
          - intros xs ck f exps callee callee_sig
                   ckty inptyp outtyp st_clk st_inp
                   Heqin Hfindcallee Hfindsigc Hck0 Hinp0 Hout0.
            eapply Hcallout; eauto.
          - intros xs ck f exps r ckr callee callee_sig
                   ckty rty rstty inptyp outtyp st_clk st_rst st_inp
                   Heqin Hfindcallee Hfindsigc Hck0 Hr0 Hrst0 Hinp0 Hout0
                   k_reset Hreset_ctrl.
            eapply Hresetout; eauto.
          - exact Hsatraw.
          - exact Hsem.
          - exact Hsem'.
          - unfold m.
            eapply history_low_eq_upto_monotone.
            + apply Nat.le_succ_diag_r.
            + exact Hlowin.
        }
        pose proof (Ordered_nodes_nodup_names _ Hord) as Hndnames.
        destruct Hsecure as
            [ty_env_sec sig_sec
             clk_id_sec rst_id_sec clk_type_sec rst_type_sec
             inp_sec out_sec locals_sec raw_sec st_n_sec
             Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
             Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
             Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
             Hcallsec_cur Hresetsec_cur].
        rewrite Hfindenv in Hfindenv_sec.
        inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
        rewrite Hfindsig in Hfindsig_sec.
        inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
        rewrite <- H1 in Hcallsec_cur, Hresetsec_cur, Hsatsig_sec, Hagree_sec.
        rewrite Hsigdef in Hcallsec_cur, Hresetsec_cur, Hcallout, Hresetout.
        pose proof Hcallsec_cur as Hcallsec_node.
        pose proof Hresetsec_cur as Hresetsec_node.
        assert
          (Hpts_cur :
             Forall
               (fun x =>
                  low_var ty_env dlt_raw t x ->
                  Env.find x (H m) = Env.find x (H' m))
               (vars_defined n.(n_eqs))).
        {
          eapply nl_node_causal_ind_defined.
          + intros eq x Heqin Hxdef Hdeps Hlowx.
            destruct eq as [x0 ck ce|xs ck f exps r|x0 ck c0 e];
              simpl in Hxdef.
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqDef x0 ck ce) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqdef_constraint_inv
                   ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
                as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqdef_noninterference_instant_pointwise; eauto.
              intros y Hfree.
              assert (Hlowy : low_var ty_env dlt_raw t y).
              {
                eapply simple_security_caexp; eauto.
              }
              assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
              { split; [reflexivity|exact Hfree]. }
              exact (Hdeps y Hdep_xy Hlowy).
            * destruct xs as [|xh xt].
              { simpl in Hxdef. contradiction. }
              destruct r as [[r ckr]|].
              2:{
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqapp_constraint_inv
                      ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                       & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                   as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
                 destruct (sem_eqapp_inv all_nodes bk H' (xh :: xt) ck f exps Hsem_eq')
                   as (ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock' & Hsem_node_c').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup;
                       [eapply Ordered_nodes_nodup_names; exact Hord
                       |exact Hfindcallee'
                       |exact Hfindcallee]).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps None).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                   (Hcallsec_node
                      (xh :: xt) ck f exps callee nsig_c
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps None)).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope [rst_type]).
                 {
                   simpl.
                   apply SecT.st_scoped_singleton.
                   repeat (apply in_or_app; right).
                   simpl. now right; left.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps None outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right.
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_clk0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' m).
                 {
                   eapply
                     (eqapp_inputs_low_eq_upto
                        ty_env ty_env_c callee callee_sig_cur inp_c
                        inptyp0 outtyp0 dlt_raw [rst_type] ckty0 t
                        bk H H' Hc Hc' exps ls ls' m); eauto.
                   intros z Hz j Hj.
                   assert (Hlowz : low_var ty_env dlt_raw t z).
                   {
                     eapply exp_type_low; eauto.
                   }
                   destruct
                     (free_exp_in_inputs_or_defined
                        P n (xh :: xt) ck callee.(n_name) exps None z
                        Hwcnode Heqin Hz)
                     as [Hin_z|Hdef_z].
                   - eapply Hlowin; eauto.
                   - destruct (Nat.eq_dec j m) as [Heqj|Hneqj].
                     + subst j.
                       assert (Hdep_xz :
                                 NLCaus.nl_depends_on_eq
                                   (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
                       {
                         split; [exact Hxdef|].
                         eapply nth_error_free_in_aexps; eauto.
                       }
                       exact (Hdeps z Hdep_xz Hlowz).
                     + eapply Hprev; eauto. lia.
                 }
                 pose proof
                   (Hcallout
                      (xh :: xt) ck callee.(n_name) exps callee callee_sig_cur
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      m ty_env_c callee_sig_cur t
                      bk_c bk_c' Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur
                      (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                         ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                         inp_c out_c locals_c raw_c st_n_c
                         Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                         Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                         Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty & Hnthyty & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty.
                   simpl in Hnthyty.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty
                        Hinst_out_eq Hnthyty)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 eapply
                   (eqapp_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' m i x yo); eauto.
              }
              {
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqreset_constraint_inv
                      ty_env clk_type rst_type xh xt ck f exps r ckr ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & rty0 & rstty0 & inptyp0 & outtyp0
                       & st_clk0 & st_rst0 & st_inp0
                       & Hfindsigc & Hck0 & Hr0 & Hrst0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct
                   (sem_eqreset_inv all_nodes bk H (xh :: xt) ck f exps r ckr Hsem_eq)
                   as (rys & rs & ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock
                       & Hsem_var_r & Hbools_r & Hsem_node_masked).
                 destruct
                   (sem_eqreset_inv all_nodes bk H' (xh :: xt) ck f exps r ckr Hsem_eq')
                   as (rys' & rs' & ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock'
                       & Hsem_var_r' & Hbools_r' & Hsem_node_masked').
                 set (kr := count rs m).
                 set (kr' := count rs' m).
                 specialize (Hsem_node_masked kr).
                 specialize (Hsem_node_masked' kr').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup; eauto).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps (Some (r, ckr))).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hrst0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env rst_type ckr)
                             SC.init_state = OK (rstty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hrst0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                   (Hresetsec_node
                      (xh :: xt) ck f exps r ckr callee nsig_c
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hr_scope : SecT.st_scoped caller_scope [rty0]).
                 {
                   apply SecT.st_scoped_singleton.
                   assert (Hinr_pair :
                             In (r, ckr)
                               (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   destruct (Hvars_scoped r) as (ty0 & Hfindr & Hinscope).
                   - eapply In_InMembers. exact Hinr_pair.
                   - rewrite Hr0 in Hfindr.
                     inversion Hfindr; subst ty0.
                     exact Hinscope.
                 }
                 assert
                   (Hfree_rclock_scope :
                      forall z,
                        Is_free_in_clock z ckr ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   assert (Hwr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ckr).
                   { eapply wc_env_var; eauto. }
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   - eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto.
                   - exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_rst :
                      SECCETYPING.assign_clk_type ty_env rst_type ckr = Some rstty0).
                 {
                   unfold SC.option_to_sec in Hrst0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env rst_type ckr) as [rstty'|]
                     eqn:Hassign; simpl in Hrst0_init; try discriminate.
                   inversion Hrst0_init; now subst rstty'.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope rstty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_type) (ck := ckr).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now right; left.
                   - exact Hfree_rclock_scope.
                   - exact Hassign_rst.
                 }
                 assert (Hrst_join_scope : SecT.st_scoped caller_scope ([rty0] ⊔ rstty0)).
                 {
                   eapply SecT.st_scoped_merge; eauto.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right.
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_rst0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hreset_ctrlm :
                           reset_control_low_eq_upto ty_env dlt_raw t r H H' m).
                 {
                   eapply reset_control_low_eq_upto_of_sem_var_eq.
                   intros Hlowr j Hj.
                   destruct
                     (reset_var_in_inputs_or_defined
                        P n (xh :: xt) ck callee.(n_name) exps r ckr
                        Hwcnode Heqin)
                     as [Hin_r|Hdef_r].
                   - eapply Hlowin; eauto.
                   - destruct (Nat.eq_dec j m) as [Heqj|Hneqj].
                     + subst j.
                       assert (Hdep_xr :
                                 NLCaus.nl_depends_on_eq
                                   (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x r).
                       {
                         split; [exact Hxdef|].
                         right. left. reflexivity.
                       }
                       exact (Hdeps r Hdep_xr Hlowr).
                     + eapply Hprev; eauto. lia.
                 }
                 assert (Hcount_eq :
                           forall j, j <= m -> count rs j = count rs' j).
                 {
                   eapply Hreset_ctrlm; eauto using Hsem_var_r, Hsem_var_r', Hbools_r, Hbools_r'.
                 }
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' m).
                 {
                   eapply
                     (eqapp_reset_inputs_low_eq_upto
                        ty_env ty_env_c callee callee_sig_cur inp_c
                        inptyp0 outtyp0 dlt_raw ([rty0] ⊔ rstty0) ckty0 t
                        bk H H' Hc Hc' exps rs rs' kr kr' ls ls' m); eauto.
                   - unfold kr. reflexivity.
                   - unfold kr'. reflexivity.
                   - exact Hcount_eq.
                   - intros z Hz j Hj.
                     assert (Hlowz : low_var ty_env dlt_raw t z).
                     {
                       eapply exp_type_low; eauto.
                     }
                     destruct
                       (free_exp_in_inputs_or_defined
                          P n (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) z
                          Hwcnode Heqin Hz)
                       as [Hin_z|Hdef_z].
                     + eapply Hlowin; eauto.
                     + destruct (Nat.eq_dec j m) as [Heqj|Hneqj].
                       * subst j.
                         assert (Hdep_xz :
                                   NLCaus.nl_depends_on_eq
                                     (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
                         {
                           split; [exact Hxdef|].
                           left.
                           eapply nth_error_free_in_aexps; eauto.
                         }
                         exact (Hdeps z Hdep_xz Hlowz).
                       * eapply Hprev; eauto. lia.
                 }
                 pose proof
                   (Hresetout
                      (xh :: xt) ck callee.(n_name) exps r ckr callee callee_sig_cur
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0
                      m Hreset_ctrlm)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      m ty_env_c callee_sig_cur t
                      (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur
                      (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                         ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                         inp_c out_c locals_c raw_c st_n_c
                         Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                         Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                         Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty & Hnthyty & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty.
                   simpl in Hnthyty.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty
                        Hinst_out_eq Hnthyty)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 assert (Hkr_eq : kr = count rs m).
                 { unfold kr. reflexivity. }
                 assert (Hkr'_eq : kr' = count rs' m).
                 { unfold kr'. reflexivity. }
                 eapply
                   (eqapp_reset_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' rs rs' kr kr' m i x yo); eauto.
              }
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqFby x0 ck c0 e) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqfby_constraint_inv
                   ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
                as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqfby_noninterference_delayed_pointwise; eauto.
              -- intros y Hclock.
                 assert (Hlowy : low_var ty_env dlt_raw t y).
                 {
                   eapply simple_security_aexp; eauto using freeAexp2.
                 }
                 assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqFby x0 ck c0 e) x0 y).
                 { split; [reflexivity|exact Hclock]. }
                 exact (Hdeps y Hdep_xy Hlowy).
              -- intros y Hfree j Hjlt.
                 assert (Hlowy : low_var ty_env dlt_raw t y).
                 {
                   eapply simple_security_aexp; eauto.
                 }
                 eapply free_aexp_low_eq_prefix_from_inputs_or_defined
                   with (P := P) (n := n) (x := x0) (ck := ck) (c0 := c0) (e := e)
                        (ty_env := ty_env) (dlt := dlt_raw) (t := t) (k := k); eauto.
          + assert (Hinputs_cur :
                       Forall
                         (fun x0 : ident =>
                            low_var ty_env dlt_raw t x0 ->
                            Env.find x0 (H m) = Env.find x0 (H' m))
                         (map fst n.(n_in))).
            {
              pose proof
                (history_low_eq_upto_inputs_pointwise n ty_env dlt_raw t H H' m Hlowin)
                as Hinputs.
              rewrite Forall_forall in *.
              intros x0 Hin Hobs.
              exact (Hinputs x0 Hin Hobs m (le_n m)).
            }
            exact Hinputs_cur.
          + eapply NLCaus.nl_global_causal_find; eauto.
        }
        eapply history_low_eq_upto_succ_intro; eauto.
        intros x Hinx Hlowx.
        rewrite Forall_forall in Hpts_cur.
        eapply Hpts_cur; eauto.
    Qed.

    (** Internal raw output theorem.

        Relation to the paper:
        this is not part of the public statement of noninterference.  It is
        the proof-internal theorem that should be derived from the paired
        [node_security] predicate and then used to recover the canonical
        output theorem. *)
    Theorem node_noninterference_outputs_raw:
      forall n dlt_sig dlt_raw,
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        node_outputs_raw_spec n dlt_sig dlt_raw.
    Proof.
      refine
        (fix IH n dlt_sig dlt_raw
             (Hsecure_cur : node_security all_nodes G envs aux_names n dlt_sig dlt_raw)
             {struct Hsecure_cur}
             : node_outputs_raw_spec n dlt_sig dlt_raw := _).
      destruct Hsecure_cur as
          [ty_env_sec sig_sec
           clk_id_sec rst_id_sec clk_type_sec rst_type_sec
           inp_sec out_sec locals_sec raw_sec st_n_sec
           Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
           Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
           Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
           Hcallsec_cur Hresetsec_cur].
      intros k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig Hsiggen
             Haux Hclk Hrst Hinp Hout Hlocals Hraw Hsigdef
             _ Hsatraw Hsem Hsem' Hlowin.
      assert (Hsecure_step :
                node_security all_nodes G envs aux_names n dlt_sig dlt_raw).
      {
        eapply SecureNode; eauto.
      }
      eapply history_low_eq_upto_weaken.
      - intros x Hinout.
        eapply Permutation_in.
        + exact (Permutation_sym n.(n_defd)).
        + rewrite map_app, in_app_iff.
          right.
          exact Hinout.
      - eapply node_noninterference_vars_defined_step with
            (sig := sig)
            (clk_id := clk_id)
            (rst_id := rst_id)
            (clk_type := clk_type)
            (rst_type := rst_type)
            (inp := inp)
            (out := out)
            (locals := locals)
            (raw := raw)
            (st_n := st_n)
            (bk := bk); eauto.
        + exact Hsecure_step.
        + intros xs ck f exps callee callee_sig
                 ckty inptyp outtyp st_clk st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hinp0 Hout0.
          eapply IH.
          eapply Hcallsec_cur; eauto.
        + intros xs ck f exps r ckr callee callee_sig
                 ckty rty rstty inptyp outtyp st_clk st_rst st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hrty Hrst0 Hinp0 Hout0
                 k_reset Hreset_ctrl.
          eapply IH.
          eapply Hresetsec_cur; eauto.
    Qed.

    (** Output-facing node noninterference theorem.

        Relation to the paper:
        this is the indexed-semantics analogue of the paper's NLustre
        noninterference theorem.  For now it is stated directly on the paired
        [node_security] predicate, so the replay witness [dlt_raw] remains
        explicit in the theorem statement while the proof architecture is
        still being settled. *)
    Theorem node_noninterference_outputs:
      forall n ty_env nsig dlt_sig dlt_raw t bk H H',
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SIG.find_signature n.(n_name) G = Some nsig ->
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq ty_env dlt_sig t (map fst n.(n_in)) H H' ->
        history_low_eq ty_env dlt_sig t (map fst n.(n_out)) H H'.
    Proof.
      intros n ty_env nsig dlt_sig dlt_raw t bk H H'
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig
             Hsecure Hsem Hsem' Hlowin.
      destruct Hsecure as
          [ty_env_sec sig_sec
           clk_id_sec rst_id_sec clk_type_sec rst_type_sec
           inp_sec out_sec locals_sec raw_sec st_n_sec
           Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
           Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
           Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
           Hcallsec_sec Hresetsec_sec].
      rewrite Hfindenv in Hfindenv_sec.
      inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
      rewrite Hfindsig in Hfindsig_sec.
      inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
      assert (Hsecure_cur :
                node_security all_nodes G envs aux_names n dlt_sig dlt_raw).
      {
        eapply SecureNode; eauto.
      }
      assert
        (Hscope_in :
           forall x,
             In x (map fst n.(n_in)) ->
             exists alpha,
               Env.find x ty_env = Some alpha
               /\ In alpha (signature_scope nsig)).
      {
        intros x Hinx.
        apply in_map_iff in Hinx as ((xin, ckin) & Heq & Hinpair).
        simpl in Heq. subst xin.
        apply In_InMembers in Hinpair.
        destruct
          (get_mappings_from_node_inmembers _ _ _ _ _ Hinpair Hinp_sec)
          as (alpha & Hfindalpha & Hinalpha).
        exists alpha.
        split; [exact Hfindalpha|].
        rewrite Hsigdef_sec.
        unfold signature_scope.
        apply in_or_app.
        left.
        exact Hinalpha.
      }
      assert
        (Hscope_out :
           forall x,
             In x (map fst n.(n_out)) ->
             exists alpha,
               Env.find x ty_env = Some alpha
               /\ In alpha (signature_scope nsig)).
      {
        intros x Hinx.
        apply in_map_iff in Hinx as ((xout, ckout) & Heq & Hinpair).
        simpl in Heq. subst xout.
        apply In_InMembers in Hinpair.
        destruct
          (get_mappings_from_node_inmembers _ _ _ _ _ Hinpair Hout_sec)
          as (alpha & Hfindalpha & Hinalpha).
        exists alpha.
        split; [exact Hfindalpha|].
        rewrite Hsigdef_sec.
        unfold signature_scope.
        apply in_or_app.
        right.
        apply in_or_app.
        left.
        exact Hinalpha.
      }
      assert (Hlowin_raw :
                history_low_eq ty_env dlt_raw t (map fst n.(n_in)) H H').
      {
        eapply history_low_eq_agree_on_scope
          with (scope := signature_scope nsig) (dlt1 := dlt_sig); eauto.
      }
      intros k x Hinx Hlowx.
      assert (Hlowx_raw : low_var ty_env dlt_raw t x).
      {
        destruct (Hscope_out x Hinx) as (alpha & Hfindalpha & Hinscope).
        eapply low_var_agree_on_scope; eauto.
      }
      pose proof
        (node_noninterference_outputs_raw n dlt_sig dlt_raw Hsecure_cur
           k ty_env nsig t bk bk H H'
           clk_id_sec rst_id_sec clk_type_sec rst_type_sec
           inp_sec out_sec locals_sec raw_sec st_n_sec
           Henvsgen Hord Hwcglob Hallsig Hcaus
           Hfindnode Hfindenv Hfindsig Hsiggen_sec
           Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
           Hraw_sec Hsigdef_sec Hsecure_cur Hsatraw_sec
           Hsem Hsem'
           (history_low_eq_upto_of_history_low_eq
              (map fst n.(n_in)) H H' k Hlowin_raw))
        as Hlowout_k.
      eapply Hlowout_k; eauto using le_n.
    Qed.



  End GENERATED_NODE_NONINTERFERENCE.

End SECNLUSNONINTERFERENCE.

Module SecNLusNonInterference
  (Import Ids    : IDS)
  (Import Lat    : Lattice)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import SecT   : SECTYPES Lat)
  (Import CESyn  : CESYNTAX Op)
  (Import SynNL  : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (NLCaus        : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING
      CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING)
  <: SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN
       SECCETYPING CETyp CEIsF CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps
       Indexed SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

  Include SECNLUSNONINTERFERENCE
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

End SecNLusNonInterference.
