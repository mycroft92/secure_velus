(** Utility lemmas on lists and positives used across the SIF proofs. *)

From Coq Require Import List.
From Coq Require Import Lists.ListSet.
From Coq Require Import Lia.

From Velus Require Import Common.
From Velus Require Import Environment.
From Coq Require Import Sorting.Permutation.

Import ListNotations.

Lemma lt_gt_false: forall a b, (a < b)%positive -> (b < a)%positive -> False.
Proof.
  assert (RelationClasses.Asymmetric Pos.lt).
   {apply RelationClasses.StrictOrder_Asymmetric. apply Pos.lt_strorder. }
  apply RelationClasses.asymmetry.
Qed.

Inductive sortedNoDup : (list ident) -> Prop :=
| sort_nil  : sortedNoDup []
| sort_1    : forall i1, sortedNoDup [i1]
| sort_cons : forall (i1 i2: ident) (l: list ident), (i1 < i2
  -> sortedNoDup (i2::l)
  -> sortedNoDup (i1::i2::l)) %positive.

Inductive sortedDecNoDup : (list ident) -> Prop :=
| sort_nild  : sortedDecNoDup []
| sort_1d    : forall i1, sortedDecNoDup [i1]
| sort_consd : forall (i1 i2: ident) (l: list ident), (i1 > i2
  -> sortedDecNoDup (i2::l)
  -> sortedDecNoDup (i1::i2::l)) %positive.
Hint Constructors sortedNoDup sortedDecNoDup.

Lemma sortedNoDup_in: forall i1 l i2, (i1 < i2 -> sortedNoDup (i2::l) -> ~In i1 (i2::l))%positive.
Proof.

  unfold not . induction l.
  - intros * H Hs contra. inversion contra. subst; apply Pos.lt_irrefl in H; auto. inversion H0.
  - intros * H Hs Hi. inversion Hs. subst. assert (i1<a)%positive as Hi1a. { lia. }
    inversion Hi.
    * subst. now apply Pos.lt_irrefl in H.
    * inversion H0; subst.
      + now apply  Pos.lt_irrefl in Hi1a.
      + eauto.
Qed.

Lemma sortedDecNoDup_in: forall i1 l i2, (i1 > i2 -> sortedDecNoDup (i2::l) -> ~In i1 (i2::l))%positive.
Proof.

  unfold not . induction l.
  - intros * H Hs contra. inversion contra. subst. rewrite Pos.gt_lt_iff in H. apply Pos.lt_irrefl in H; auto. inversion H0.
  - intros * H Hs Hi. inversion Hs. subst. assert (i1 > a)%positive as Hi1a. { lia. }
    inversion Hi.
    * subst. rewrite Pos.gt_lt_iff in H. now apply Pos.lt_irrefl in H.
    * inversion H0; subst.
      + rewrite Pos.gt_lt_iff in Hi1a. now apply  Pos.lt_irrefl in Hi1a.
      + eauto.
Qed.

Hint Constructors NoDup.
Hint Resolve sortedNoDup_in sortedDecNoDup_in.

Lemma sortedNoDup_NoDup: forall l, sortedNoDup l -> NoDup l.
Proof.
  induction l; intros; auto.
  inversion H; subst;
  apply NoDup_cons; auto.
Qed.

Lemma sortedDecNoDup_NoDup: forall l, sortedDecNoDup l -> NoDup l.
Proof.
  induction l; intros; auto.
  inversion H; subst.
  - auto.
  - apply NoDup_cons; auto.
Qed.

Lemma sortedNoDup_helper: forall l a b , sortedNoDup (a::b::l) -> sortedNoDup (a::l).
Proof.
  induction l as [|i l IHl]; auto.
  intros. inversion H; subst. inversion H4; subst.
  apply sort_cons; auto; try lia...
Qed.

Lemma sortedDecNoDup_helper: forall l a b , sortedDecNoDup (a::b::l) -> sortedDecNoDup (a::l).
Proof.
  induction l as [|i l IHl]; auto.
  intros. inversion H; subst. inversion H4; subst.
  apply sort_consd; auto; try lia...
Qed.

Lemma sortedNoDup_correct: (forall l i, sortedNoDup (i::l) -> forall a, In a l -> a > i) %positive.
Proof.
  induction l; intros.
  - inversion H0.
  - inversion H; subst.
    inversion H0.
    * subst. lia.
    * specialize (IHl i). eauto using sortedNoDup_helper.
Qed.

Lemma sortedDecNoDup_correct: (forall l i, sortedDecNoDup (i::l) -> forall a, In a l ->  a < i) %positive.
Proof.
  induction l; intros.
  - inversion H0.
  - inversion H; subst.
    inversion H0.
    * subst. lia.
    * specialize (IHl i). eauto using sortedDecNoDup_helper.
Qed.

Lemma sortedNoDup_easy: forall l a, sortedNoDup (a::l) -> sortedNoDup l.
Proof.
  induction l; intros; auto.
  inversion H; auto.
Qed.

Lemma sortedDecNoDup_easy: forall l a, sortedDecNoDup (a::l) -> sortedDecNoDup l.
Proof.
  induction l; intros; auto.
  inversion H; auto.
Qed.

Lemma sortedNoDup_hard: forall l a b, (sortedNoDup (a::l) -> b < a -> sortedNoDup (b:: a:: l))%positive.
Proof.
  induction l; intros; auto.

Qed.

Lemma sortedDecNoDup_hard: forall l a b, (sortedDecNoDup (a::l) -> b > a -> sortedDecNoDup (b:: a:: l))%positive.
Proof.
  induction l; intros; auto.

Qed.

Lemma sortedNoDup_hard2: forall l a b, (sortedNoDup (a::l) -> b <= a -> sortedNoDup (b:: l))%positive.
Proof.
  induction l; intros; auto.
  inversion H; subst. assert (b < a)%positive. { lia. }
  auto.

Qed.

Lemma sortedDecNoDup_hard2: forall l a b, (sortedDecNoDup (a::l) -> b >= a -> sortedDecNoDup (b:: l))%positive.
Proof.
  induction l; intros; auto.
  inversion H; subst. assert (b > a)%positive. { lia. }
  auto.

Qed.

Lemma list_len_1 : forall A (x:list A), length x = 1 <-> exists d, x = [d].
  Proof.
    split.
    - intros. unfold length in H. destruct x eqn:E in H.
      * discriminate H.
      * injection H. intros H_0. assert (l =[]).
        + apply length_zero_iff_nil in H_0. auto.
        + exists a. subst l. auto.
    - intros. destruct H. subst x. reflexivity.
Qed.

(** * Naming environments

    An environment maps program names to security-type names.  These
    facts are independent of the monad that builds the environment and
    of the gensym prefix it uses, so they are shared by the NLustre
    naming layer ([NameInterface]) and by the Stc and Obc security
    typings ([SecContext]). *)

Definition env_injective (env: Env.t ident) : Prop :=
  forall x y tx ty,
    Env.find x env = Some tx ->
    Env.find y env = Some ty ->
    tx = ty ->
    x = y.

Definition env_values (env: Env.t ident) : list (ident * ident) :=
  map (fun '(x, ty) => (ty, x)) (Env.elements env).

Lemma env_values_add:
  forall x ty env,
    ~ Env.In x env ->
    Permutation (env_values (Env.add x ty env))
                ((ty, x) :: env_values env).
Proof.
  intros x ty env Hnin.
  unfold env_values.
  replace ((ty, x) :: map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))
    with (map (fun '(x0, ty0) => (ty0, x0)) ((x, ty) :: Env.elements env))
    by reflexivity.
  now apply Permutation_map, Env.elements_add.
Qed.

Lemma env_values_nodup_injective:
  forall env,
    NoDupMembers (env_values env) ->
    env_injective env.
Proof.
  intros env Hnodup x y tx ty Hfindx Hfindy Heq.
  apply Env.elements_correct in Hfindx.
  apply Env.elements_correct in Hfindy.
  unfold env_values in Hnodup.
  assert (Hinx : In (tx, x) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
  { apply in_map_iff. exists (x, tx). split; [reflexivity|exact Hfindx]. }
  assert (Hiny : In (tx, y) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
  { subst ty.
    apply in_map_iff. exists (y, tx). split; [reflexivity|exact Hfindy]. }
  now eapply NoDupMembers_det; eauto.
Qed.

(** ** Reversal facts

    [translate_tcs] builds its Obc statement with a left fold, so the
    per-constraint blocks come out in reverse order compared with the
    STC generator.  These two lemmas move between the two orders: the
    pairing is reversed pointwise, and the flattened lists remain
    permutations of each other. *)

Lemma Forall2_rev:
  forall {A B} (P: A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    Forall2 P (rev xs) (rev ys).
Proof.
  intros A B P xs ys Hall.
  induction Hall as [|x y xs ys Hxy Hall IH]; simpl.
  - constructor.
  - apply Forall2_app; [exact IH|].
    constructor; [exact Hxy|constructor].
Qed.

Lemma concat_rev_Permutation:
  forall {A} (l: list (list A)),
    Permutation (concat (rev l)) (concat l).
Proof.
  intros A l.
  induction l as [|x l IH]; simpl.
  - constructor.
  - rewrite concat_app. simpl. rewrite app_nil_r.
    etransitivity; [apply Permutation_app_comm|].
    apply Permutation_app_head. exact IH.
Qed.

(** ** Combining two pairings over a common index list

    The translation bridge pairs each transition constraint both with
    its STC constraint block and with its Obc one; these lemmas glue the
    two pairings into a relation between the blocks themselves. *)

Lemma Forall2_combine:
  forall {A B C} (P: A -> B -> Prop) (Q: A -> C -> Prop) (R: B -> C -> Prop) xs ys zs,
    Forall2 P xs ys ->
    Forall2 Q xs zs ->
    (forall x y z, P x y -> Q x z -> R y z) ->
    Forall2 R ys zs.
Proof.
  intros A B C P Q R xs ys zs HP.
  revert zs.
  induction HP as [|x y xs ys Hxy HP IH]; intros zs HQ Himp.
  - inversion HQ; subst. constructor.
  - inversion HQ as [|x' z xs' zs' Hxz HQ']; subst.
    constructor.
    + eapply Himp; eauto.
    + eapply IH; eauto.
Qed.

Lemma Forall2_combine_with:
  forall {A B C} (P: A -> B -> Prop) (Q: A -> C -> Prop) (S: A -> Prop)
         (R: B -> C -> Prop) xs ys zs,
    Forall2 P xs ys ->
    Forall2 Q xs zs ->
    Forall S xs ->
    (forall x y z, S x -> P x y -> Q x z -> R y z) ->
    Forall2 R ys zs.
Proof.
  intros A B C P Q S R xs ys zs HP.
  revert zs.
  induction HP as [|x y xs ys Hxy HP IH]; intros zs HQ HS Himp.
  - inversion HQ; subst. constructor.
  - inversion HQ as [|x' z xs' zs' Hxz HQ']; subst.
    inversion HS as [|x'' xs'' Hx HS']; subst.
    constructor.
    + eapply Himp; eauto.
    + eapply IH; eauto.
Qed.

Lemma Forall_rev:
  forall {A} (P: A -> Prop) (l: list A),
    Forall P l ->
    Forall P (rev l).
Proof.
  intros A P l Hall.
  apply Forall_forall. intros x Hin.
  rewrite <- in_rev in Hin.
  eapply Forall_forall in Hall; eauto.
Qed.
