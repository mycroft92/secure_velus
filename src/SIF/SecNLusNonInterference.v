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
From Velus Require Import CoreExpr.CEIsFree.
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
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
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
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING
       CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING).

  (** The paper's [Γ] is not an arbitrary map in this development.  It is the
      node-local security environment produced by [NameInterface] for the
      current node and then consumed by [SecNLusTyping]. *)
  Section GENERATED_LOW_OBSERVATION.
    Variable all_nodes : global.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.
    Variable n : node.
    Variable ty_env : local_sec_env.
    Variable s : ident -> Lat.t.
    Variable t : Lat.t.

    Hypothesis Henvsgen :
      generate_node_scoped_env all_nodes = OK (envs, aux_names).
    Hypothesis Hfindenv :
      find_node_env n.(n_name) envs = Some ty_env.

    (** One raw variable is observable at level [t] when its generated security
        identifier is mapped by the ground instantiation below [t].

        Relation to the paper:
        this is the pointwise membership test behind the set [X⊑t], where the
        source-side [Γ] is represented here by the generated local typing
        environment [ty_env] for node [n]. *)
    Definition low_var (x : ident) : Prop :=
      exists α, Env.find x ty_env = Some α /\ s α ⊑ t.

    Definition low_var_dec (x : ident) : {low_var x} + {~ low_var x}.
    Proof.
      unfold low_var.
      destruct (Env.find x ty_env) as [α|] eqn:Hfind.
      - destruct (Lat.order_dec (s α) t) as [Hle|Hnle].
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

  End GENERATED_LOW_OBSERVATION.

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
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING
       CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING)
  <: SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN
       SECCETYPING CEIsF CEClo Str Ord Mem IsD IsF Clo CESem Indexed
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

  Include SECNLUSNONINTERFERENCE
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
    Str Ord Mem IsD IsF Clo CESem Indexed SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

End SecNLusNonInterference.
