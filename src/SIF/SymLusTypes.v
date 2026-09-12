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

(** * The equational theory of [ICTAC] Figure 5

    [ICTAC] Lemma 2 says the equations other than associativity and
    commutativity can be oriented left to right, that the resulting system is
    confluent modulo AC, and hence that equal types can be rewritten to a
    common form.  Rather than mechanise a rewriting system and a completion
    argument, this file states the theory as a congruence and proves that
    [norm] *decides* it: [lty_eq a b] exactly when [norm a = norm b].  That
    is the conclusion Lemma 2 is after, in the form later files can use, and
    it yields decidability of type equality as a corollary.

    Note which equations are primitive here.  Associativity, commutativity,
    idempotence and the unit for join are primitive, as are the four
    refinement equations of Figure 5 lines 2 and 3.  The refinement component
    is a *set*, so its permutation and duplication laws are primitive too --
    [LCE_swap] and [LCE_dedup] -- which is what lets a term be equated to its
    sorted, duplicate-free canonical form. *)

Inductive lty_eq : lty -> lty -> Prop :=
| LE_refl  : forall a, lty_eq a a
| LE_sym   : forall a b, lty_eq a b -> lty_eq b a
| LE_trans : forall a b c, lty_eq a b -> lty_eq b c -> lty_eq a c
| LE_cong_join : forall a a' b b',
    lty_eq a a' -> lty_eq b b' -> lty_eq (LJoin a b) (LJoin a' b')
| LE_cong_ref : forall a a' r r',
    lty_eq a a' -> lcons_eq r r' -> lty_eq (LRef a r) (LRef a' r')
| LE_jassoc : forall a b c, lty_eq (LJoin (LJoin a b) c) (LJoin a (LJoin b c))
| LE_jcomm  : forall a b, lty_eq (LJoin a b) (LJoin b a)
| LE_jidem  : forall a, lty_eq (LJoin a a) a
| LE_jbot   : forall a, lty_eq (LJoin a LBot) a
| LE_rnil   : forall a, lty_eq (LRef a LCnil) a
| LE_rjoin  : forall a1 r1 a2 r2,
    lty_eq (LJoin (LRef a1 r1) (LRef a2 r2)) (LRef (LJoin a1 a2) (lcapp r1 r2))
| LE_rref   : forall a r1 r2,
    lty_eq (LRef (LRef a r1) r2) (LRef a (lcapp r1 r2))

with lcons_eq : lcons -> lcons -> Prop :=
| LCE_refl  : forall r, lcons_eq r r
| LCE_sym   : forall r r', lcons_eq r r' -> lcons_eq r' r
| LCE_trans : forall r1 r2 r3, lcons_eq r1 r2 -> lcons_eq r2 r3 -> lcons_eq r1 r3
| LCE_cong  : forall x x' y y' r r',
    lty_eq x x' -> lty_eq y y' -> lcons_eq r r' ->
    lcons_eq (LCcons x y r) (LCcons x' y' r')
| LCE_swap  : forall x1 y1 x2 y2 r,
    lcons_eq (LCcons x1 y1 (LCcons x2 y2 r)) (LCcons x2 y2 (LCcons x1 y1 r))
| LCE_dedup : forall x y r, lcons_eq (LCcons x y (LCcons x y r)) (LCcons x y r)
| LCE_hoist : forall a r1 b r2 r,
    lcons_eq (LCcons (LRef a r1) (LRef b r2) r) (LCcons a b (lcapp r1 (lcapp r2 r))).

Scheme lty_eq_mut   := Minimality for lty_eq   Sort Prop
  with lcons_eq_mut := Minimality for lcons_eq Sort Prop.

Combined Scheme lty_lcons_eq_mut from lty_eq_mut, lcons_eq_mut.

Hint Constructors lty_eq lcons_eq.

(** * Soundness: the canonical form is an invariant of the theory *)

Lemma cmerge_shuffle : forall a b c, cmerge a (cmerge b c) = cmerge b (cmerge a c).
Proof.
  intros. rewrite <- !cmerge_assoc. now rewrite (cmerge_comm a b).
Qed.

Lemma cmerge_swap4 : forall a b c d,
    cmerge (cmerge a b) (cmerge c d) = cmerge (cmerge a c) (cmerge b d).
Proof.
  intros. rewrite !cmerge_assoc. f_equal. apply cmerge_shuffle.
Qed.

(** Raw equation lemmas.  [simpl] cannot be used on a [norm_cs] of a cons:
    the generated constraint is a literal singleton list, so [simpl] unfolds
    [cmerge] into its comparison and destroys the shape the algebraic lemmas
    match against.  These let a proof unfold exactly one layer instead. *)

Lemma norm_join : forall a b,
    norm (LJoin a b)
    = (merge (fst (norm a)) (fst (norm b)), cmerge (snd (norm a)) (snd (norm b))).
Proof. reflexivity. Qed.

Lemma norm_ref : forall a r,
    norm (LRef a r) = (fst (norm a), cmerge (snd (norm a)) (norm_cs r)).
Proof. reflexivity. Qed.

Lemma norm_cs_cons : forall x y r,
    norm_cs (LCcons x y r)
    = cmerge (cmerge [(fst (norm x), fst (norm y))]
                     (cmerge (snd (norm x)) (snd (norm y))))
             (norm_cs r).
Proof. reflexivity. Qed.

Lemma cmerge_dedup_l : forall a b, cmerge a (cmerge a b) = cmerge a b.
Proof. intros. now rewrite <- cmerge_assoc, cmerge_refl. Qed.

Theorem lty_lcons_eq_norm :
  (forall a b, lty_eq a b -> norm a = norm b)
  /\ (forall r r', lcons_eq r r' -> norm_cs r = norm_cs r').
Proof.
  apply lty_lcons_eq_mut.
  - (* LE_refl *) reflexivity.
  - (* LE_sym *) intros a b _ IH. now symmetry.
  - (* LE_trans *) intros a b c _ IH1 _ IH2. congruence.
  - (* LE_cong_join *) intros a a' b b' _ IH1 _ IH2. simpl. now rewrite IH1, IH2.
  - (* LE_cong_ref *) intros a a' r r' _ IH1 _ IH2. simpl. now rewrite IH1, IH2.
  - (* LE_jassoc *) intros a b c. simpl.
    now rewrite MergeFacts.merge_assoc, cmerge_assoc.
  - (* LE_jcomm *) intros a b. simpl.
    rewrite (MergeFacts.merge_comm (fst (norm a)) (fst (norm b))).
    now rewrite (cmerge_comm (snd (norm a)) (snd (norm b))).
  - (* LE_jidem *) intros a. simpl.
    rewrite MergeFacts.merge_refl, cmerge_refl. symmetry. apply surjective_pairing.
  - (* LE_jbot *) intros a. simpl.
    rewrite MergeFacts.merge_nil, cmerge_nil. symmetry. apply surjective_pairing.
  - (* LE_rnil *) intros a. simpl.
    rewrite cmerge_nil. symmetry. apply surjective_pairing.
  - (* LE_rjoin *) intros a1 r1 a2 r2. simpl.
    rewrite norm_cs_lcapp. f_equal. apply cmerge_swap4.
  - (* LE_rref *) intros a r1 r2. simpl.
    rewrite norm_cs_lcapp. f_equal. apply cmerge_assoc.
  - (* LCE_refl *) reflexivity.
  - (* LCE_sym *) intros r r' _ IH. now symmetry.
  - (* LCE_trans *) intros r1 r2 r3 _ IH1 _ IH2. congruence.
  - (* LCE_cong *) intros x x' y y' r r' _ IH1 _ IH2 _ IH3. simpl.
    now rewrite IH1, IH2, IH3.
  - (* LCE_swap *) intros x1 y1 x2 y2 r. simpl. apply cmerge_shuffle.
  - (* LCE_dedup *) intros x y r. simpl. apply cmerge_dedup_l.
  - (* LCE_hoist *) intros a r1 b r2 r.
    rewrite !norm_cs_cons, !norm_ref. cbn [fst snd].
    rewrite !norm_cs_lcapp, !cmerge_assoc.
    f_equal. f_equal. apply cmerge_shuffle.
Qed.

Corollary lty_eq_norm : forall a b, lty_eq a b -> norm a = norm b.
Proof. apply lty_lcons_eq_norm. Qed.

Corollary lcons_eq_norm : forall r r', lcons_eq r r' -> norm_cs r = norm_cs r'.
Proof. apply lty_lcons_eq_norm. Qed.

(** * Completeness: every term is equated to its own canonical form

    This is the direction that does the real work.  [merge] and [cmerge]
    sort and remove duplicates, so equating a term with the embedding of its
    canonical form means deriving a sorted, duplicate-free rearrangement from
    associativity, commutativity and idempotence alone.  [embed_st_merge] and
    [embed_cs_cmerge] are where that happens; everything after them is
    bookkeeping. *)

Lemma le_jbot2 : forall a, lty_eq (LJoin LBot a) a.
Proof. intros a. eapply LE_trans; [apply LE_jcomm | apply LE_jbot]. Qed.

Lemma le_jshuffle : forall a b c,
    lty_eq (LJoin a (LJoin b c)) (LJoin b (LJoin a c)).
Proof.
  intros a b c.
  eapply LE_trans; [apply LE_sym, LE_jassoc|].
  eapply LE_trans; [apply LE_cong_join; [apply LE_jcomm | apply LE_refl]|].
  apply LE_jassoc.
Qed.

Lemma le_jdup : forall a b c,
    lty_eq (LJoin (LJoin a b) (LJoin a c)) (LJoin a (LJoin b c)).
Proof.
  intros a b c.
  eapply LE_trans; [apply LE_jassoc|].
  eapply LE_trans;
    [apply LE_cong_join; [apply LE_refl | apply le_jshuffle]|].
  eapply LE_trans; [apply LE_sym, LE_jassoc|].
  apply LE_cong_join; [apply LE_jidem | apply LE_refl].
Qed.

(** [ICTAC] Figure 5 line 1, applied to a whole sorted union: the fold of
    [LJoin] over [merge s1 s2] is the join of the two folds. *)
Lemma embed_st_merge : forall s1 s2,
    lty_eq (embed_st (merge s1 s2)) (LJoin (embed_st s1) (embed_st s2)).
Proof.
  induction s1 as [|x xs IH1]; intros s2.
  - rewrite MergeFacts.merge_nil2. simpl. apply LE_sym, le_jbot2.
  - induction s2 as [|y ys IH2].
    + rewrite MergeFacts.merge_nil. simpl. apply LE_sym, LE_jbot.
    + destruct (Pos.compare x y) eqn:E.
      * apply Pos.compare_eq in E; subst y.
        rewrite MergeFacts.merge3. simpl.
        eapply LE_trans;
          [apply LE_cong_join; [apply LE_refl | apply IH1]|].
        apply LE_sym, le_jdup.
      * rewrite Pos.compare_lt_iff in E.
        rewrite MergeFacts.merge1 by exact E. simpl.
        eapply LE_trans;
          [apply LE_cong_join; [apply LE_refl | apply IH1]|].
        apply LE_sym, LE_jassoc.
      * rewrite Pos.compare_gt_iff in E.
        rewrite MergeFacts.merge2 by exact E. simpl.
        eapply LE_trans;
          [apply LE_cong_join; [apply LE_refl | apply IH2]|].
        apply le_jshuffle.
Qed.

Lemma lcapp_cong_r : forall q r r',
    lcons_eq r r' -> lcons_eq (lcapp q r) (lcapp q r').
Proof.
  induction q as [|u v q IH]; intros r r' H; simpl; auto.
Qed.

Lemma lcons_move : forall A x y B,
    lcons_eq (lcapp A (LCcons x y B)) (LCcons x y (lcapp A B)).
Proof.
  induction A as [|u v A IH]; intros x y B; simpl.
  - apply LCE_refl.
  - eapply LCE_trans.
    + apply LCE_cong; [apply LE_refl | apply LE_refl | apply IH].
    + apply LCE_swap.
Qed.

(** The [lcons] counterpart of [embed_st_merge]. *)
Lemma embed_cs_cmerge : forall r1 r2,
    lcons_eq (embed_cs (cmerge r1 r2)) (lcapp (embed_cs r1) (embed_cs r2)).
Proof.
  induction r1 as [|x xs IH1]; intros r2.
  - rewrite cmerge_nil2. apply LCE_refl.
  - induction r2 as [|y ys IH2].
    + rewrite cmerge_nil, lcapp_nil. apply LCE_refl.
    + destruct (ccmp x y) eqn:E.
      * apply ccmp_eq in E; subst y.
        rewrite cmerge3. destruct x as [x1 x2]; simpl.
        eapply LCE_trans.
        { apply LCE_cong; [apply LE_refl | apply LE_refl | apply IH1]. }
        apply LCE_sym.
        eapply LCE_trans.
        { apply LCE_cong;
            [apply LE_refl | apply LE_refl | apply lcons_move]. }
        apply LCE_dedup.
      * rewrite (cmerge1 _ _ _ _ E).
        destruct x as [x1 x2]; simpl.
        apply LCE_cong; [apply LE_refl | apply LE_refl | apply IH1].
      * rewrite (cmerge2 _ _ _ _ E).
        destruct x as [x1 x2]; destruct y as [y1 y2]; simpl.
        apply LCE_sym.
        eapply LCE_trans.
        { apply LCE_cong;
            [apply LE_refl | apply LE_refl | apply lcons_move]. }
        eapply LCE_trans; [apply LCE_swap|].
        apply LCE_cong; [apply LE_refl | apply LE_refl | ].
        apply LCE_sym. exact (IH2).
Qed.

Lemma embed_norm : forall t,
    embed (norm t) = LRef (embed_st (fst (norm t))) (embed_cs (snd (norm t))).
Proof. reflexivity. Qed.

Theorem lty_lcons_norm_embed :
  (forall t, lty_eq t (embed (norm t)))
  /\ (forall r, lcons_eq r (embed_cs (norm_cs r))).
Proof.
  apply lty_lcons_mut.
  - (* LBot *) apply LE_sym, LE_rnil.
  - (* LVar *) intros d. simpl.
    eapply LE_trans; [apply LE_sym, LE_jbot|].
    apply LE_sym, LE_rnil.
  - (* LJoin *) intros a IHa b IHb.
    eapply LE_trans; [apply LE_cong_join; [exact IHa | exact IHb]|].
    rewrite !embed_norm, norm_join. cbn [fst snd].
    eapply LE_trans; [apply LE_rjoin|].
    apply LE_cong_ref.
    + apply LE_sym, embed_st_merge.
    + apply LCE_sym, embed_cs_cmerge.
  - (* LRef *) intros a IHa r IHr.
    eapply LE_trans; [apply LE_cong_ref; [exact IHa | exact IHr]|].
    rewrite !embed_norm, norm_ref. cbn [fst snd].
    eapply LE_trans; [apply LE_rref|].
    apply LE_cong_ref; [apply LE_refl|].
    apply LCE_sym, embed_cs_cmerge.
  - (* LCnil *) apply LCE_refl.
  - (* LCcons *) intros x IHx y IHy r IHr.
    eapply LCE_trans;
      [apply LCE_cong; [exact IHx | exact IHy | exact IHr]|].
    rewrite !embed_norm.
    eapply LCE_trans; [apply LCE_hoist|].
    rewrite norm_cs_cons, !cmerge_assoc.
    apply LCE_sym.
    eapply LCE_trans; [apply embed_cs_cmerge|].
    simpl.
    apply LCE_cong; [apply LE_refl | apply LE_refl |].
    eapply LCE_trans; [apply embed_cs_cmerge|].
    apply lcapp_cong_r.
    apply embed_cs_cmerge.
Qed.

Corollary lty_norm_embed : forall t, lty_eq t (embed (norm t)).
Proof. apply lty_lcons_norm_embed. Qed.

Corollary lcons_norm_embed : forall r, lcons_eq r (embed_cs (norm_cs r)).
Proof. apply lty_lcons_norm_embed. Qed.

(** * Confluence

    [ICTAC] Lemma 2, in the form the rest of the development uses: [norm] is
    a canonical form for the equational theory.  Two types are equal in the
    theory exactly when they normalise to the same pair, so every term
    rewrites to a common form modulo AC, and type equality is decidable. *)

Theorem lty_eq_iff_norm : forall a b, lty_eq a b <-> norm a = norm b.
Proof.
  split.
  - apply lty_eq_norm.
  - intros H.
    eapply LE_trans; [apply lty_norm_embed|].
    rewrite H. apply LE_sym, lty_norm_embed.
Qed.

Theorem lcons_eq_iff_norm : forall r r', lcons_eq r r' <-> norm_cs r = norm_cs r'.
Proof.
  split.
  - apply lcons_eq_norm.
  - intros H.
    eapply LCE_trans; [apply lcons_norm_embed|].
    rewrite H. apply LCE_sym, lcons_norm_embed.
Qed.

Definition LST_eq_dec : forall (p q : LST), {p = q} + {p <> q}.
Proof.
  intros p q.
  repeat decide equality; apply Pos.eq_dec.
Defined.

Corollary lty_eq_dec : forall a b, {lty_eq a b} + {~ lty_eq a b}.
Proof.
  intros a b.
  destruct (LST_eq_dec (norm a) (norm b)) as [Heq|Hneq].
  - left. now apply lty_eq_iff_norm.
  - right. intros H. apply Hneq. now apply lty_eq_iff_norm.
Defined.

(** * Membership in a canonical union

    The semantic layer reads a refinement component as a conjunction of
    obligations, so it needs to know that [cmerge] is union on the nose: it
    keeps everything from both sides and invents nothing. *)

Lemma cmerge_In : forall r1 r2 c,
    In c (cmerge r1 r2) <-> In c r1 \/ In c r2.
Proof.
  induction r1 as [|x xs IH1]; intros r2 c.
  - rewrite cmerge_nil2. simpl. tauto.
  - induction r2 as [|y ys IH2].
    + rewrite cmerge_nil. simpl. tauto.
    + destruct (ccmp x y) eqn:E.
      * apply ccmp_eq in E; subst y.
        rewrite cmerge3. simpl. rewrite IH1. tauto.
      * rewrite (cmerge1 _ _ _ _ E). simpl. rewrite IH1. simpl. tauto.
      * rewrite (cmerge2 _ _ _ _ E). simpl. rewrite IH2. simpl. tauto.
Qed.
