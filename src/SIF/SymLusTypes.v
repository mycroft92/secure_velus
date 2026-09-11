(** Symbolic security types for Lustre: refinement types and canonical forms.

    Lustre, unlike NLustre, lets a node call appear *inside* an expression.
    Such a call has no equation on which to hang the callee's instantiated
    constraints, so the constraints must travel inside the type itself.
    Following Prasad and Yerraguntla (ICTAC 2021, arXiv:2105.10687) -- cited
    below as [ICTAC] -- the type algebra of [SymTypes.v] is extended with a
    refinement type [a{|r|}], read "type [a], provided [r] holds".

    This file is the *syntactic* half of that extension: the term algebra of
    [ICTAC] Figure 5, its canonical forms, and the operations the constraint
    generator actually calls.  The semantic half -- ground instantiation,
    satisfaction, and the bridge to [SecTypes.preserves_on] -- lives in
    [SecLusTypes.v], and [LusTypes.v] assembles the two.

    Nothing here modifies [SymTypes.v].  [ST] and [constraint] are used
    exactly as that file defines them, and the canonical form of a Lustre
    type is a pair of the two.  A property of [ST] or [constraint] that is
    about the NLustre or Stc level belongs in [SymTypes.v]; one that is about
    the Lustre level, or about the Lustre-to-NLustre bridge on types, belongs
    here. *)

From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Lia.

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes.

Import ListNotations.

(** * A total order on constraints, and the canonical union it induces

    [ICTAC] Figure 5 reads the refinement component of a type as a *set* of
    constraints: the equations union it, and the equational theory is modulo
    associativity, commutativity and idempotence.  Representing that set as a
    list sorted under a total order makes all three definitional rather than
    something the proofs must carry around.

    [SymTypes.v] already has [constraint_merge], but its comparison sorts the
    left-hand side of a constraint on every call, so it is an order only on
    constraints that are already canonical.  Rather than perturb that
    definition -- which the NLustre, Stc and Obc developments depend on -- this
    section builds the plain lexicographic order, for which the merge laws
    hold unconditionally, exactly as [SymTypes.merge] does for [ST]. *)

Ltac poscase :=
  repeat match goal with
  | [ H : (?x ?= ?y)%positive = Eq |- _ ] => apply Pos.compare_eq in H; subst
  | [ H : (?x ?= ?y)%positive = Lt |- _ ] => rewrite Pos.compare_lt_iff in H
  | [ H : (?x ?= ?y)%positive = Gt |- _ ] => rewrite Pos.compare_gt_iff in H
  end.

Fixpoint ilex (l1 l2 : list ident) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: l1', y :: l2' =>
      match Pos.compare x y with
      | Eq => ilex l1' l2'
      | c => c
      end
  end.

Lemma ilex_refl : forall l, ilex l l = Eq.
Proof.
  induction l as [|x l IH]; simpl; auto.
  now rewrite Pos.compare_refl.
Qed.

Lemma ilex_eq : forall l1 l2, ilex l1 l2 = Eq -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; destruct l2 as [|y l2]; simpl; intros H;
    try discriminate; auto.
  destruct (x ?= y)%positive eqn:E; try discriminate.
  apply Pos.compare_eq in E; subst.
  f_equal; auto.
Qed.

Lemma ilex_antisym : forall l1 l2, ilex l2 l1 = CompOpp (ilex l1 l2).
Proof.
  induction l1 as [|x l1 IH]; destruct l2 as [|y l2]; simpl; auto.
  rewrite (Pos.compare_antisym y x).
  destruct (y ?= x)%positive eqn:E; simpl; auto.
Qed.

Lemma ilex_trans : forall l1 l2 l3,
    ilex l1 l2 = Lt -> ilex l2 l3 = Lt -> ilex l1 l3 = Lt.
Proof.
  induction l1 as [|x l1 IH]; destruct l2 as [|y l2]; destruct l3 as [|z l3];
    simpl; intros H1 H2; try discriminate; auto.
  destruct (x ?= y)%positive eqn:E1; destruct (y ?= z)%positive eqn:E2;
    try discriminate.
  - apply Pos.compare_eq in E1; apply Pos.compare_eq in E2; subst.
    rewrite Pos.compare_refl. eapply IH; eauto.
  - apply Pos.compare_eq in E1; subst. now rewrite E2.
  - apply Pos.compare_eq in E2; subst. now rewrite E1.
  - assert (Hxz : (x ?= z)%positive = Lt).
    { poscase. rewrite Pos.compare_lt_iff. lia. }
    now rewrite Hxz.
Qed.

Definition ccmp (c1 c2 : constraint) : comparison :=
  match ilex (fst c1) (fst c2) with
  | Eq => ilex (snd c1) (snd c2)
  | c => c
  end.

Lemma ccmp_refl : forall c, ccmp c c = Eq.
Proof. intros [a b]; unfold ccmp; simpl; now rewrite !ilex_refl. Qed.

Lemma ccmp_eq : forall c1 c2, ccmp c1 c2 = Eq -> c1 = c2.
Proof.
  intros [a1 b1] [a2 b2]; unfold ccmp; simpl; intros H.
  destruct (ilex a1 a2) eqn:E; try discriminate.
  apply ilex_eq in E; apply ilex_eq in H; subst; auto.
Qed.

Lemma ccmp_antisym : forall c1 c2, ccmp c2 c1 = CompOpp (ccmp c1 c2).
Proof.
  intros [a1 b1] [a2 b2]; unfold ccmp; simpl.
  rewrite (ilex_antisym a1 a2).
  destruct (ilex a1 a2) eqn:E; simpl; auto.
  apply ilex_antisym.
Qed.

Lemma ccmp_trans : forall c1 c2 c3,
    ccmp c1 c2 = Lt -> ccmp c2 c3 = Lt -> ccmp c1 c3 = Lt.
Proof.
  intros [a1 b1] [a2 b2] [a3 b3]; unfold ccmp; simpl; intros H1 H2.
  destruct (ilex a1 a2) eqn:E1; destruct (ilex a2 a3) eqn:E2; try discriminate.
  - apply ilex_eq in E1; apply ilex_eq in E2; subst.
    rewrite ilex_refl. eapply ilex_trans; eauto.
  - apply ilex_eq in E1; subst. now rewrite E2.
  - apply ilex_eq in E2; subst. now rewrite E1.
  - erewrite ilex_trans; eauto.
Qed.

Lemma ccmp_gt : forall c1 c2, ccmp c1 c2 = Gt -> ccmp c2 c1 = Lt.
Proof.
  intros c1 c2 H. rewrite ccmp_antisym, H. reflexivity.
Qed.

Lemma ccmp_lt_irrefl : forall c, ccmp c c = Lt -> False.
Proof. intros c H; rewrite ccmp_refl in H; discriminate. Qed.

(** * Canonical union of refinement constraint sets *)

Lemma ccmp_lt_gt : forall c1 c2, ccmp c1 c2 = Lt -> ccmp c2 c1 = Gt.
Proof. intros c1 c2 H. rewrite ccmp_antisym, H. reflexivity. Qed.

Ltac cabs :=
  match goal with
  | [ H1 : ccmp ?x ?y = Lt, H2 : ccmp ?y ?x = Lt |- _ ] =>
      elim (ccmp_lt_irrefl x (ccmp_trans _ _ _ H1 H2))
  | [ H1 : ccmp ?x ?y = Lt, H2 : ccmp ?y ?z = Lt, H3 : ccmp ?z ?x = Lt |- _ ] =>
      elim (ccmp_lt_irrefl x (ccmp_trans _ _ _ (ccmp_trans _ _ _ H1 H2) H3))
  end.

Fixpoint cmerge (r1 : list constraint) : list constraint -> list constraint :=
  fix cmerge' r2 :=
    match r1, r2 with
    | [], _ => r2
    | _, [] => r1
    | x :: xs, y :: ys =>
        match ccmp x y with
        | Lt => x :: cmerge xs r2
        | Eq => x :: cmerge xs ys
        | Gt => y :: cmerge' ys
        end
    end.

Lemma cmerge_nil : forall r, cmerge r [] = r.
Proof. destruct r; auto. Qed.

Lemma cmerge_nil2 : forall r, cmerge [] r = r.
Proof. destruct r; auto. Qed.

Lemma cmerge1 : forall x y xs ys,
    ccmp x y = Lt -> cmerge (x :: xs) (y :: ys) = x :: cmerge xs (y :: ys).
Proof. intros x y xs ys H. simpl. now rewrite H. Qed.

Lemma cmerge2 : forall x y xs ys,
    ccmp x y = Gt -> cmerge (x :: xs) (y :: ys) = y :: cmerge (x :: xs) ys.
Proof. intros x y xs ys H. simpl. now rewrite H. Qed.

Lemma cmerge3 : forall x xs ys, cmerge (x :: xs) (x :: ys) = x :: cmerge xs ys.
Proof. intros x xs ys. simpl. now rewrite ccmp_refl. Qed.

Lemma cmerge_comm : forall r1 r2, cmerge r1 r2 = cmerge r2 r1.
Proof.
  induction r1 as [|x xs IH]; intros r2.
  - now rewrite cmerge_nil, cmerge_nil2.
  - induction r2 as [|y ys IH2].
    + now rewrite cmerge_nil, cmerge_nil2.
    + destruct (ccmp x y) eqn:Exy.
      * apply ccmp_eq in Exy; subst.
        rewrite !cmerge3. f_equal. apply IH.
      * rewrite (cmerge1 _ _ _ _ Exy).
        rewrite (cmerge2 y x ys xs (ccmp_lt_gt _ _ Exy)).
        f_equal. apply IH.
      * rewrite (cmerge2 _ _ _ _ Exy).
        rewrite (cmerge1 y x ys xs (ccmp_gt _ _ Exy)).
        f_equal. apply IH2.
Qed.

Lemma cmerge_refl : forall r, cmerge r r = r.
Proof.
  induction r as [|x r IH]; auto.
  rewrite cmerge3. now f_equal.
Qed.

Lemma cmerge_assoc : forall r0 r1 r2,
    cmerge (cmerge r0 r1) r2 = cmerge r0 (cmerge r1 r2).
Proof.
  induction r0 as [|A R0 IH0].
  - intros. now rewrite !cmerge_nil2.
  - induction r1 as [|B R1 IH1].
    + intros. now rewrite cmerge_nil, cmerge_nil2.
    + induction r2 as [|C R2 IH2].
      * now rewrite !cmerge_nil.
      * destruct (ccmp A B) eqn:EAB.
        -- (* A = B *)
           apply ccmp_eq in EAB; subst B.
           rewrite cmerge3.
           destruct (ccmp A C) eqn:EAC.
           ++ apply ccmp_eq in EAC; subst C.
              rewrite !cmerge3. f_equal. apply IH0.
           ++ rewrite (cmerge1 _ _ _ _ EAC), (cmerge1 _ _ _ _ EAC), cmerge3.
              f_equal. apply IH0.
           ++ rewrite (cmerge2 _ _ _ _ EAC), (cmerge2 _ _ _ _ EAC).
              rewrite (cmerge2 _ _ _ _ EAC). f_equal.
              rewrite <- (cmerge3 A R0 R1). apply IH2.
        -- (* A < B *)
           rewrite (cmerge1 _ _ _ _ EAB).
           destruct (ccmp B C) eqn:EBC.
           ++ apply ccmp_eq in EBC; subst C.
              rewrite (cmerge1 _ _ _ _ EAB), cmerge3, (cmerge1 _ _ _ _ EAB).
              f_equal. rewrite IH0. now rewrite cmerge3.
           ++ assert (EAC : ccmp A C = Lt) by (eapply ccmp_trans; eauto).
              rewrite (cmerge1 _ _ _ _ EAC), (cmerge1 _ _ _ _ EBC),
                      (cmerge1 _ _ _ _ EAB).
              f_equal. rewrite IH0. now rewrite (cmerge1 _ _ _ _ EBC).
           ++ rewrite (cmerge2 _ _ _ _ EBC).
              destruct (ccmp A C) eqn:EAC.
              ** apply ccmp_eq in EAC; subst C.
                 rewrite cmerge3, cmerge3. f_equal. apply IH0.
              ** rewrite (cmerge1 _ _ _ _ EAC), (cmerge1 _ _ _ _ EAC).
                 f_equal. rewrite IH0. now rewrite (cmerge2 _ _ _ _ EBC).
              ** rewrite (cmerge2 _ _ _ _ EAC), (cmerge2 _ _ _ _ EAC).
                 f_equal. rewrite <- (cmerge1 _ _ _ _ EAB). apply IH2.
        -- (* A > B *)
           rewrite (cmerge2 _ _ _ _ EAB).
           destruct (ccmp B C) eqn:EBC.
           ++ apply ccmp_eq in EBC; subst C.
              rewrite cmerge3, cmerge3, (cmerge2 _ _ _ _ EAB).
              f_equal. apply IH1.
           ++ rewrite (cmerge1 _ _ _ _ EBC), (cmerge1 _ _ _ _ EBC),
                      (cmerge2 _ _ _ _ EAB).
              f_equal. apply IH1.
           ++ assert (EAC : ccmp A C = Gt).
              { apply ccmp_lt_gt. eapply ccmp_trans;
                  [apply ccmp_gt; exact EBC | apply ccmp_gt; exact EAB]. }
              rewrite (cmerge2 _ _ _ _ EBC), (cmerge2 _ _ _ _ EBC),
                      (cmerge2 _ _ _ _ EAC).
              f_equal. rewrite <- (cmerge2 _ _ _ _ EAB). apply IH2.
Qed.

(** * The term algebra

    [ICTAC] Figure 5:  [a, b ::= bot | d | a ⊔ b | a{|r|}]  with constraints
    [r ::= (t ⊑ a)*].  Types and constraints are mutually recursive: a
    refinement carries constraints, and those constraints relate types which
    may themselves be refined.

    The constraint list is spelled as its own member [lcons] of the mutual
    block rather than as [list (lty * lty)].  Both are accepted, but the
    mutual spelling gives a genuine mutual [Fixpoint] and a mutual induction
    scheme for free, which a nested [list] would not. *)

Inductive lty : Type :=
| LBot  : lty
| LVar  : ident -> lty
| LJoin : lty -> lty -> lty
| LRef  : lty -> lcons -> lty
with lcons : Type :=
| LCnil  : lcons
| LCcons : lty -> lty -> lcons -> lcons.

Scheme lty_mut   := Induction for lty   Sort Prop
  with lcons_mut := Induction for lcons Sort Prop.

Combined Scheme lty_lcons_mut from lty_mut, lcons_mut.

(** Union of refinement constraint sets.  [ICTAC] writes this as set union;
    at the term level it is append, and the canonical form below collapses
    order and duplication. *)

Fixpoint lcapp (r1 r2 : lcons) : lcons :=
  match r1 with
  | LCnil => r2
  | LCcons x y r1' => LCcons x y (lcapp r1' r2)
  end.

Lemma lcapp_nil : forall r, lcapp r LCnil = r.
Proof. induction r as [|x y r IH]; simpl; auto. now rewrite IH. Qed.

Lemma lcapp_assoc : forall r1 r2 r3,
    lcapp (lcapp r1 r2) r3 = lcapp r1 (lcapp r2 r3).
Proof. induction r1 as [|x y r1 IH]; simpl; auto. intros. now rewrite IH. Qed.

(** * Canonical forms

    The canonical form of a Lustre type is a pair [(a, r)] with [a : ST] the
    plain symbolic type and [r : list constraint] the refinement obligations
    it carries -- both from [SymTypes.v], untouched.

    In particular the hoisting rule of [ICTAC] Figure 5,

      {a{|r1|} ⊑ b{|r2|}} = {a ⊑ b} ∪ r1 ∪ r2,

    is what [norm_cs] does to each member of a refinement list: the relation
    between the two sides becomes one flat [constraint], and whatever the two
    sides were themselves carrying is unioned in alongside it.  That is the
    only way an obligation leaves a type and enters a constraint set, which
    is what keeps every later file on the existing [constraint] type. *)

Definition LST : Type := (ST * list constraint)%type.

Fixpoint norm (t : lty) : LST :=
  match t with
  | LBot => ([], [])
  | LVar d => ([d], [])
  | LJoin a b =>
      (merge (fst (norm a)) (fst (norm b)),
        cmerge (snd (norm a)) (snd (norm b)))
  | LRef a r =>
      (fst (norm a), cmerge (snd (norm a)) (norm_cs r))
  end
with norm_cs (r : lcons) : list constraint :=
  match r with
  | LCnil => []
  | LCcons x y r' =>
      cmerge
        (cmerge
           [(fst (norm x), fst (norm y))]
           (cmerge (snd (norm x)) (snd (norm y))))
        (norm_cs r')
  end.

Lemma norm_cs_lcapp : forall r1 r2,
    norm_cs (lcapp r1 r2) = cmerge (norm_cs r1) (norm_cs r2).
Proof.
  induction r1 as [|x y r1 IH]; intros r2; simpl.
  - now rewrite cmerge_nil2.
  - now rewrite IH, cmerge_assoc.
Qed.

(** Reading a canonical form back as a term.  [embed] is what makes
    completeness of [norm] provable: a term is equated to the embedding of
    its own canonical form, so two terms with the same canonical form are
    equated to each other. *)

Fixpoint embed_st (a : ST) : lty :=
  match a with
  | [] => LBot
  | d :: a' => LJoin (LVar d) (embed_st a')
  end.

Fixpoint embed_cs (r : list constraint) : lcons :=
  match r with
  | [] => LCnil
  | (x, y) :: r' => LCcons (embed_st x) (embed_st y) (embed_cs r')
  end.

Definition embed (p : LST) : lty := LRef (embed_st (fst p)) (embed_cs (snd p)).

(** * Derived constructors

    These are the operations [SecLTyping.v] actually calls.  They act on
    canonical forms directly, so the generator never builds an [lty] term:
    the term algebra exists to state and prove the equational theory, not to
    be computed with. *)

Definition lbot : LST := ([], []).

Definition lvar (d : ident) : LST := ([d], []).

Definition ljoin (p q : LST) : LST :=
  (merge (fst p) (fst q), cmerge (snd p) (snd q)).

Definition lrefine (p : LST) (r : list constraint) : LST :=
  (fst p, cmerge (snd p) r).

(** The hoisting rule as a function: constrain [p] to lie below the single
    generated name [b], releasing whatever [p] was carrying. *)
Definition lconstrain (p : LST) (b : ident) : list constraint :=
  cmerge [(fst p, [b])] (snd p).

Definition ljoin_all (ps : list LST) : LST := fold_right ljoin lbot ps.

(** [norm] agrees with the derived constructors, so a proof may move between
    the term view and the computed view at will. *)

Lemma norm_LBot : norm LBot = lbot.
Proof. reflexivity. Qed.

Lemma norm_LVar : forall d, norm (LVar d) = lvar d.
Proof. reflexivity. Qed.

Lemma norm_LJoin : forall a b, norm (LJoin a b) = ljoin (norm a) (norm b).
Proof. reflexivity. Qed.

Lemma norm_LRef : forall a r, norm (LRef a r) = lrefine (norm a) (norm_cs r).
Proof. reflexivity. Qed.

(** The derived constructors inherit the algebra of their components:
    [ljoin] is ACUI with unit [lbot], and [lrefine] accumulates. *)

Lemma ljoin_comm : forall p q, ljoin p q = ljoin q p.
Proof.
  intros [a1 r1] [a2 r2]; unfold ljoin; simpl.
  now rewrite MergeFacts.merge_comm, cmerge_comm.
Qed.

Lemma ljoin_assoc : forall p q s, ljoin (ljoin p q) s = ljoin p (ljoin q s).
Proof.
  intros [a1 r1] [a2 r2] [a3 r3]; unfold ljoin; simpl.
  now rewrite MergeFacts.merge_assoc, cmerge_assoc.
Qed.

Lemma ljoin_idem : forall p, ljoin p p = p.
Proof.
  intros [a r]; unfold ljoin; simpl.
  now rewrite MergeFacts.merge_refl, cmerge_refl.
Qed.

Lemma ljoin_lbot : forall p, ljoin p lbot = p.
Proof.
  intros [a r]; unfold ljoin, lbot; simpl.
  now rewrite MergeFacts.merge_nil, cmerge_nil.
Qed.

Lemma ljoin_lbot2 : forall p, ljoin lbot p = p.
Proof. intros p. rewrite ljoin_comm. apply ljoin_lbot. Qed.

Lemma lrefine_nil : forall p, lrefine p [] = p.
Proof. intros [a r]; unfold lrefine; simpl; now rewrite cmerge_nil. Qed.

Lemma lrefine_lrefine : forall p r1 r2,
    lrefine (lrefine p r1) r2 = lrefine p (cmerge r1 r2).
Proof. intros [a r] r1 r2; unfold lrefine; simpl; now rewrite cmerge_assoc. Qed.

(** [ICTAC] Figure 5, line 3: a join of two refined types is the join of the
    carriers refined by the union of what each was carrying. *)
Lemma ljoin_lrefine : forall p q r1 r2,
    ljoin (lrefine p r1) (lrefine q r2) = lrefine (ljoin p q) (cmerge r1 r2).
Proof.
  intros [a1 s1] [a2 s2] r1 r2; unfold ljoin, lrefine; simpl.
  f_equal.
  rewrite !cmerge_assoc. f_equal.
  rewrite <- !cmerge_assoc. f_equal.
  apply cmerge_comm.
Qed.
