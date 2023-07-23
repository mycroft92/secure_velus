From Coq Require Import List.
From Coq Require Import Lists.ListSet.
From Coq Require Import Lia.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
(* From Coq Require Import Arith.
From Coq Require Import PArith. *)

Compute  (Pos.compare (xO (xI xH)) (xO (xI xH))).


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

(* We are changing the order to decreasing*)
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

Lemma sortedDecNoDup_in: forall i1 l i2, (i2 < i1 -> sortedDecNoDup (i2::l) -> ~In i1 (i2::l))%positive.
Proof.

  unfold not . induction l.
  - intros * H Hs contra. inversion contra. subst; apply Pos.lt_irrefl in H; auto. inversion H0.
  - intros * H Hs Hi. inversion Hs. subst. assert (a < i1)%positive as Hi1a. { lia. }
    inversion Hi.
    * subst. now apply Pos.lt_irrefl in H.
    * inversion H0; subst. 
      + now apply  Pos.lt_irrefl in Hi1a.
      + eauto.
Qed.


Hint Constructors NoDup.
Hint Resolve sortedNoDup_in.


Lemma sortedNoDup_NoDup: forall l, sortedNoDup l -> NoDup l.
Proof.
  induction l; intros; auto.
  inversion H; subst;
  apply NoDup_cons; auto.
Qed.

Lemma sortedNoDup_helper: forall l a b , sortedNoDup (a::b::l) -> sortedNoDup (a::l).
Proof.
  induction l as [|i l IHl]; auto.
  intros. inversion H; subst. inversion H4; subst.
  apply sort_cons; auto; try lia...
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

Lemma sortedNoDup_easy: forall l a, sortedNoDup (a::l) -> sortedNoDup l.
Proof.
  induction l; intros; auto.
  inversion H; auto.
Qed.

Lemma sortedNoDup_hard: forall l a b, (sortedNoDup (a::l) -> b < a -> sortedNoDup (b:: a:: l))%positive.
Proof.
  induction l; intros; auto.
 
Qed.

Lemma sortedNoDup_hard2: forall l a b, (sortedNoDup (a::l) -> b <= a -> sortedNoDup (b:: l))%positive.
Proof.
  induction l; intros; auto.
  inversion H; subst. assert (b < a)%positive. { lia. }
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