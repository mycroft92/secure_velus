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

From Coq Require Import List.
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
      forall base_ty x ck ce xty ckty cety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt (ckty ⊔ cety) [xty] ->
        low_var x ->
        Is_free_in_caexp y ck ce ->
        low_var y.
    Proof.
      intros base_ty x ck ce xty ckty cety y
             Hfindx Hck Hce Hsat Hlowx Hfree.
      destruct (assign_caexp_type_free_bound base_ty ck ce ckty cety y Hfree Hck Hce)
        as (alpha & Hfindy & Hbound).
      apply (simple_security (ckty ⊔ cety) x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx).
    Qed.

    (** Low-dependency propagation for [EqFby] right-hand sides.

        Relation to the paper:
        this is the simple-security instantiation for NLustre [EqFby]:
        when the defined memory variable is low, every free variable of the
        guarded source expression feeding the delay is low as well. *)
    Lemma simple_security_aexp:
      forall base_ty x ck e xty ckty ety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt (ckty ⊔ ety) [xty] ->
        low_var x ->
        Is_free_in_aexp y ck e ->
        low_var y.
    Proof.
      intros base_ty x ck e xty ckty ety y
             Hfindx Hck He Hsat Hlowx Hfree.
      destruct (assign_aexp_type_free_bound base_ty ck e ckty ety y Hfree Hck He)
        as (alpha & Hfindy & Hbound).
      apply (simple_security (ckty ⊔ ety) x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx).
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

    (** Simple [EqDef] noninterference step.

        Relation to the paper:
        this is the indexed semantic proof step for a single non-call
        definition equation.  Once the raw typing constraint shows that every
        free dependency of the RHS is low, low-equivalence of those
        dependencies forces equality of the defined stream. *)
    Lemma eqdef_noninterference:
      forall X bk H H' x xs xs' ck ce base_ty xty ckty cety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_caexp y ck ce -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt (ckty ⊔ cety) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ck ce base_ty xty ckty cety
             Hlow HX Hfindx Hck Hce Hsat Hlowx Hvar Hrhs Hvar' Hrhs' k.
      assert (Hfree :
                forall y, Is_free_in_caexp y ck ce -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_caexp base_ty x ck ce xty ckty cety y
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
      forall X bk H H' x xs xs' ls ls' ck c0 e base_ty xty ckty ety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_aexp y ck e -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt (ckty ⊔ ety) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ls ls' ck c0 e base_ty xty ckty ety
             Hlow HX Hfindx Hck He Hsat Hlowx Hvar Hrhs Hfby
             Hvar' Hrhs' Hfby' k.
      assert (Hfree :
                forall y, Is_free_in_aexp y ck e -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_aexp base_ty x ck e xty ckty ety y
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

  End GENERATED_LOW_OBSERVATION.

  Section GENERATED_NODE_SECURITY.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Paper-style node security for generated NLustre nodes.

        Relation to the paper:
        this is the source-side formalisation of the paper's [Node Security]
        notion.  A node is secure with respect to a ground instantiation [dlt]
        when:

        - its generated signature constraints [ρ] are satisfied by [dlt]; and
        - each direct call equation recursively targets a secure callee under
          the call-site instantiation reconstructed by the existing typing
          functions and [SIG.inst_valuation].

        The definition is phrased over the generated local typing environment
        from [NameInterface] and the generated node signature from
        [SecNLusTyping]; it does not introduce a second typing judgment. *)

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
        for the callee itself.  That is why [node_security] recursively
        requires security of each direct callee under the instantiated
        valuation reconstructed at the call site. *)

    Inductive node_security : node -> ground_instantiation -> Prop :=
    | SecureNode :
        forall n ty_env sig dlt,
          find_node n.(n_name) all_nodes = Some n ->
          find_node_env n.(n_name) envs = Some ty_env ->
          SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
          signature_satisfied dlt sig ->
          (* normal call security *)
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
              node_security callee
                (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty
                   [sig.(s_reset)] outtyp)) ->
          (*reset call security*)
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
              node_security callee
                (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty
                   ([rty] ⊔ rstty) outtyp)) ->
          node_security n dlt.

  End GENERATED_NODE_SECURITY.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

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

    (** Internal node theorem on [vars_defined] under a raw valuation.

        Relation to the paper:
        this is the first indexed-history noninterference theorem for one
        generated NLustre node.  It is intentionally stated on
        [vars_defined n.(n_eqs)] rather than directly on outputs, because that
        is the exact variable set already tracked by the existing
        source-signature generation lemmas.

        Unlike the final paper-facing theorem, this proof-internal statement
        works over a ground instantiation [dlt] that already satisfies the raw
        generated constraints of the current node.  That stronger hypothesis is
        needed because [vars_defined n.(n_eqs)] contains eliminated locals, and
        the simplified stored signature does not constrain them directly.

        The later output-facing theorem should be obtained as a corollary using
        [n.(n_defd)] to transport the result to
        [map fst (n.(n_vars) ++ n.(n_out))], and then to outputs only. *)
    Theorem node_noninterference_vars_defined_raw:
      forall P n ty_env sig dlt t bk H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        NLCaus.nl_global_causal all_nodes ->
        Clo.wc_node P n ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
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
        node_security all_nodes G envs aux_names n dlt ->
        SecT.listSatisfiable dlt raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq ty_env dlt t (map fst n.(n_in)) H H' ->
        history_low_eq ty_env dlt t (vars_defined n.(n_eqs)) H H'.
    Proof.
      intros P n ty_env sig dlt t bk H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hcaus Hwc Hfindnode Hfindenv Hsig Haux Hclk Hrst
             Hinp Hout Hlocals Hraw Hsigdef Hsecure Hsatraw Hsem Hsem' Hlowin.
      (* Proof plan, kept next to the first theorem statement so later edits
         do not drift from the intended theorem shape.

         1. Recover the current node's generated typing facts, in particular
            [signature_good sig] from
            [SECNLUSTYPINGCORRECTNESS.generate_node_sig_good_from_local_env].
         2. Use [NLCaus.nl_global_causal all_nodes] to recover [NLCaus.nl_node_causal] for the current
            node and for every callee reached through [node_security].  The
            current-node instance provides an induction order on instantaneous
            dependencies; then use [generate_eqns_constraints_shape] together with
            [NoDup_var_defined_n_eqs] to select the unique defining raw
            constraint for each [x ∈ vars_defined n.(n_eqs)].
         3. For [EqDef] and [EqFby], use the raw constraint plus
            [SecT.listSatisfiable dlt raw] to show that all semantic dependencies of a
            low variable are low, and then apply the indexed environment
            switching lemmas from [CEProperties].
         4. For [EqApp] and resettable [EqApp], use the recursive callee clause
            in [node_security] together with
            [SIGPROOFS.generate_constraints_complete_good] and the call-site
            instantiated valuation.
         5. Conclude pointwise low-equivalence on
            [vars_defined n.(n_eqs)] and later transport it to the output-facing
            corollaries. *)
    Admitted.

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
