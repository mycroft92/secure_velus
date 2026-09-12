(** Semantics of Lustre security types: ground instantiation, satisfaction,
    and the bridge to the lattice-mapping layer of [SecTypes.v].

    [SymLusTypes.v] is the syntactic half of the refinement-type extension:
    the term algebra, its equational theory, and the canonical form that
    decides it.  This file is the semantic half.  It answers two questions:

    - what a Lustre type *means* in a security lattice, given that a
      refinement type [a{|r|}] denotes [a] only when [r] is satisfied and is
      undefined otherwise; and

    - how the obligations a type carries become ordinary constraints of the
      kind [SecTypes.v] already reasons about, so that the constraint
      generator, [simplify], and [preserves_on] apply to them unchanged.

    As in [SymLusTypes.v], nothing here modifies [SymTypes.v] or [SecTypes.v].
    A property of [ST] or [constraint] at the NLustre or Stc level belongs in
    those files; one about the Lustre level, or about the Lustre-to-NLustre
    bridge on types, belongs here. *)

From Coq Require Import List.
From Coq Require Import PArith.

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecTypes.

Import ListNotations.

Module Type SECLUSTYPES (Import Lat : Lattice) (Import SecT : SECTYPES Lat).

  (** * Interpreting a Lustre type

      [ICTAC] interprets a refinement type as a *partial* function:
      [s(a{|r|}) = s(a)] when [s] satisfies [r], and undefined otherwise.
      Splitting that into a definedness predicate and a total interpretation
      of the carrier keeps the development free of partial functions: a
      Lustre type has a level, and separately it has obligations that a
      ground instantiation may or may not discharge. *)

  Definition lst_defined (dlt : ident -> Lat.t) (p : LST) : Prop :=
    listSatisfiable dlt (snd p).

  Definition lst_interp (dlt : ident -> Lat.t) (p : LST) : Lat.t :=
    hm_ext dlt (fst p).

  (** A term is interpreted through its canonical form, which is legitimate
      precisely because the canonical form decides the equational theory. *)

  Definition lty_defined (dlt : ident -> Lat.t) (t : lty) : Prop :=
    lst_defined dlt (norm t).

  Definition lty_interp (dlt : ident -> Lat.t) (t : lty) : Lat.t :=
    lst_interp dlt (norm t).

  (** * Soundness of the equational theory

      [ICTAC] Lemma 1.  Under the canonical-form representation this is a
      corollary of confluence rather than an induction over the equations:
      equal types have the same canonical form, so they have the same level
      and the same obligations under every ground instantiation. *)

  Theorem lty_eq_interp : forall dlt a b,
      lty_eq a b -> lty_interp dlt a = lty_interp dlt b.
  Proof.
    intros dlt a b Heq. unfold lty_interp, lst_interp.
    now rewrite (lty_eq_norm _ _ Heq).
  Qed.

  Theorem lty_eq_defined : forall dlt a b,
      lty_eq a b -> (lty_defined dlt a <-> lty_defined dlt b).
  Proof.
    intros dlt a b Heq. unfold lty_defined, lst_defined.
    now rewrite (lty_eq_norm _ _ Heq).
  Qed.

  Corollary lcons_eq_satisfied : forall dlt r r',
      lcons_eq r r' ->
      (listSatisfiable dlt (norm_cs r) <-> listSatisfiable dlt (norm_cs r')).
  Proof.
    intros dlt r r' Heq. now rewrite (lcons_eq_norm _ _ Heq).
  Qed.

  (** * Satisfaction of a canonical union

      [cmerge] is union, so satisfying a merged obligation set is satisfying
      both.  Everything below rests on this. *)

  Lemma listSatisfiable_cmerge : forall dlt r1 r2,
      listSatisfiable dlt (cmerge r1 r2)
      <-> listSatisfiable dlt r1 /\ listSatisfiable dlt r2.
  Proof.
    intros dlt r1 r2. unfold listSatisfiable. rewrite !Forall_forall.
    split.
    - intros H. split; intros c Hin; apply H, cmerge_In; tauto.
    - intros [H1 H2] c Hin. apply cmerge_In in Hin. destruct Hin; auto.
  Qed.

  (** * The derived constructors, semantically *)

  Lemma lst_defined_lbot : forall dlt, lst_defined dlt lbot.
  Proof. intros dlt. constructor. Qed.

  Lemma lst_defined_lvar : forall dlt d, lst_defined dlt (lvar d).
  Proof. intros dlt d. constructor. Qed.

  Lemma lst_interp_lvar : forall dlt d,
      lst_interp dlt (lvar d) = Lat.join (dlt d) Lat.bottom.
  Proof. reflexivity. Qed.

  (** A join is defined exactly when both sides are, and its level is the
      join of the two levels.  This is the semantic content of
      [ICTAC] Figure 5 line 3. *)

  Lemma lst_defined_ljoin : forall dlt p q,
      lst_defined dlt (ljoin p q) <-> lst_defined dlt p /\ lst_defined dlt q.
  Proof.
    intros dlt p q. unfold lst_defined, ljoin; simpl.
    apply listSatisfiable_cmerge.
  Qed.

  Lemma lst_interp_ljoin : forall dlt p q,
      lst_interp dlt (ljoin p q)
      = Lat.join (lst_interp dlt p) (lst_interp dlt q).
  Proof.
    intros dlt p q. unfold lst_interp, ljoin; simpl.
    apply hm_ext_merge_eq.
  Qed.

  (** Refining adds obligations and leaves the level alone. *)

  Lemma lst_defined_lrefine : forall dlt p r,
      lst_defined dlt (lrefine p r)
      <-> lst_defined dlt p /\ listSatisfiable dlt r.
  Proof.
    intros dlt p r. unfold lst_defined, lrefine; simpl.
    apply listSatisfiable_cmerge.
  Qed.

  Lemma lst_interp_lrefine : forall dlt p r,
      lst_interp dlt (lrefine p r) = lst_interp dlt p.
  Proof. reflexivity. Qed.

  (** * The hoisting rule, semantically

      This is the lemma the constraint generator is built on.  Constraining a
      Lustre type [p] to lie below a generated name [b] releases exactly two
      things: whatever [p] was already carrying, and the ordinary constraint
      relating [p]'s level to [b].  Both are plain [SymTypes.constraint]s, so
      every later phase reasons about them with the existing machinery. *)

  Theorem lconstrain_sound : forall dlt p b,
      listSatisfiable dlt (lconstrain p b)
      <-> lst_defined dlt p /\ Lat.order (lst_interp dlt p) (dlt b).
  Proof.
    intros dlt p b. unfold lconstrain.
    rewrite listSatisfiable_cmerge.
    unfold lst_defined, lst_interp.
    split.
    - intros [Hhead Htail]. split; auto.
      inversion Hhead as [|c cs Hc _]; subst.
      unfold constraintSatisfiable, satisfiable in Hc; simpl in Hc.
      eapply order_trans; [exact Hc|].
      simpl. apply join_least_upper_bound.
      + apply order_refl, eq_refl.
      + apply bottom_is_bottom.
    - intros [Hp Hle]. split; auto.
      constructor; auto.
      unfold constraintSatisfiable, satisfiable; simpl.
      eapply order_trans; [exact Hle|].
      apply join_bound1.
  Qed.

  (** * Degeneracy

      After unnesting no expression contains a node call, so no type carries
      an obligation and [LST] collapses to [ST].  The two legs of the
      Lustre-to-NLustre chain below unnesting therefore never meet a
      refinement type. *)

  Definition lst_plain (p : LST) : Prop := snd p = [].

  Lemma lst_plain_defined : forall dlt p, lst_plain p -> lst_defined dlt p.
  Proof.
    intros dlt p Hp. unfold lst_defined. rewrite Hp. constructor.
  Qed.

  Lemma lst_plain_ljoin : forall p q,
      lst_plain p -> lst_plain q -> lst_plain (ljoin p q).
  Proof.
    intros [a1 r1] [a2 r2] H1 H2. unfold lst_plain in *; simpl in *.
    subst. reflexivity.
  Qed.

  Lemma lst_plain_lbot : lst_plain lbot.
  Proof. reflexivity. Qed.

  Lemma lst_plain_lvar : forall d, lst_plain (lvar d).
  Proof. reflexivity. Qed.

  (** On a plain type, constraining reduces to the single ordinary constraint
      the NLustre generator would have emitted.  This is the equation that
      makes the transcription leg an equality rather than a refinement. *)

  Lemma lconstrain_plain : forall p b,
      lst_plain p -> lconstrain p b = [(fst p, [b])].
  Proof.
    intros [a r] b Hp. unfold lst_plain in Hp; simpl in Hp; subst.
    unfold lconstrain; simpl. reflexivity.
  Qed.

End SECLUSTYPES.

Module SecLusTypesFun (Lat : Lattice) (SecT : SECTYPES Lat)
  <: SECLUSTYPES Lat SecT.
  Include SECLUSTYPES Lat SecT.
End SecLusTypesFun.
