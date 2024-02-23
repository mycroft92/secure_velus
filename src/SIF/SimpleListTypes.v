From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Coq Require Import Lia.

Import ListNotations.
From Coq Require Import Recdef.



Definition ST := list ident.
Definition constraint := (ST*ident)%type.


Section ListIdentInd.
    Print nat_rect.
    Variable P : list ident -> Prop.
    Hypothesis PNill : P []. (* The property to prove is on lists*)
    Hypothesis PSingl : forall (a: ident), P [a].
    Hypothesis PCons  : 
      forall (a1 a2: ident) (l: list ident), 
        P l -> P (a1 :: a2 :: l).

    Fixpoint list_ind2 (l: list ident): P l :=
        match l with
        | []  => PNill
        | [a] => PSingl a
        | a1::a2::l' => PCons a1 a2 l' (list_ind2 l')
        end.

End ListIdentInd.

Check list_ind2.

(*first setup the ordering*)
Section MergeIdentList.

  Fixpoint split  (l:list ident) : ((list ident) * (list ident)) :=
    match l with
    | []  => ([],[])
    | [x] => ([x],[])
    | x1::x2::l' =>
      let (l1,l2) := split l' in
      (x1::l1,x2::l2)
    end.

  Lemma split_length: forall (l l1 l2: list ident),
    split l = (l1, l2) -> 
    length l1 <= length l /\ length l2 <= length l.
  Proof.
     induction l using list_ind2; intros;  split; try (inversion H; simpl; lia);
     inversion H; destruct (split l) as [l1' l2']; 
     inversion H1; simpl; destruct (IHl l1' l2') as [P1 P2]; auto; lia.
     Show Proof.
  Qed.

  (*This function is the auxiliary merge that merges two sorted lists*)
  (*Perhaps I can use an intermediate result of correctness on input *)
  Fixpoint mergeType (l1 l2: list ident) {struct l1} : list ident :=
    let fix merge_aux l2 :=
      (match l1, l2 with
      | [], _ => l2
      | _, [] => l1
      | a1::l1', a2::l2' => 
      (* Changed the order to greater than equals *)
        (match Pos.compare a1 a2 with
        | Lt => a2::(merge_aux l2')
        | Eq => a1::(mergeType l1' l2')
        | Gt => a1::(mergeType l1' l2)
        end)
      end) in merge_aux l2.
(* Need to do final mergesort*)
  Lemma merge_lt: forall (x1 x2: ident) r1 r2,
    Pos.compare x1 x2 = Lt -> 
      mergeType (x1::r1) (x2::r2) = x2:: mergeType (x1::r1) r2.
  Proof.
    intros. simpl.
    destruct (Pos.compare x1 x2); (try inversion H; auto).
    (* - inversion H; auto.
    - auto.
    - inversion H; auto. *)
  Qed.

  Lemma merge_eq: forall (x1 x2: ident) r1 r2,
    Pos.compare x1 x2 = Eq -> 
      mergeType (x1::r1) (x2::r2) = x1:: mergeType r1 r2.
  Proof.
    intros. simpl.
    destruct (Pos.compare x1 x2); (try inversion H; auto).
    (* - inversion H; auto.
    - auto.
    - inversion H; auto. *)
  Qed.

  Lemma merge_nil_l: forall l, mergeType [] l = l.
  Proof.
    intros. simpl. destruct l; auto.
  Qed.

  Lemma merge_nil_r: forall l, mergeType l [] = l.
  Proof.
    intros. simpl. destruct l; auto.
  Qed.

  Local Hint Resolve split_length merge_lt.

  Function mergesort (l: list ident) {measure length l}: list ident :=
    match l with
    | []  => []
    | [a] => [a]
    | _   => let (l1, l2) := split l in mergeType (mergesort l1) (mergesort l2)
    end.
  Proof.
    (*Recursive calls on l1 and l2 terminate *)
    - 
      intros; simpl in *; 
      destruct (split l1) as [l1' l2'] eqn:E; inv teq1; destruct (split_length _ _ _ E);
      simpl; lia.
    - 
      intros. simpl in *.  
      destruct (split l1) as [l1' l2'] eqn:E; inv teq1; destruct (split_length _ _ _ E);
      simpl; lia.
  Defined.
     
  Check mergesort_equation.
(* need to properly replace these with ident symbols and prove correctness*) 
  Lemma sorted_merge1: (forall x x1 l1 x2 l2, 
    x > x1 -> x > x2 -> sortedDecNoDup (mergeType (x1::l1) (x2::l2)) -> sortedDecNoDup (x::mergeType (x1::l1) (x2::l2)))%positive.
  Proof.
    intros. simpl in *. destruct (x1 ?= x2)%positive eqn:Heqn.
    - apply Pos.compare_eq_iff in Heqn; subst.  now apply sort_consd.
    - rewrite Pos.compare_lt_iff in Heqn. now apply sort_consd.
    - rewrite Pos.compare_gt_iff in Heqn. now apply sort_consd.
  Qed.  

  Lemma sorted_merge: forall l1, sortedDecNoDup l1 -> forall l2, sortedDecNoDup l2 -> sortedDecNoDup (mergeType l1 l2).
   Proof.
     induction l1; intros.
     - now rewrite merge_nil_l.
     - induction l2.
        + now rewrite merge_nil_r.
        Admitted.  

  Lemma mergesort_correct: forall l, sortedDecNoDup (mergesort l).
  Proof.
      apply mergesort_ind; intros; auto.
      now apply sorted_merge.
  Qed.

End MergeIdentList.

(*To yet prove the NoDuplication but first..*)
Section ConstraintOrdering.
(*do we assume the lists are sorted?*)
  Definition ident_list_compare (l1 l2: list ident): comparison :=
    let l1' := mergesort l1 in
    let l2' := mergesort l2 in
    (fix compare' (l1 l2: list ident): comparison :=
    match l1,l2 with
    | [], [] => Eq
    | [], _  => Lt
    | _, []  => Gt
    | a1::l1'', a2::l2'' => 
        match Pos.compare a1 a2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => compare' l1'' l2''
        end 
    end) l1' l2'.

  Definition ident_sorted_list_compare (l1 l2: list ident): comparison :=
    (fix compare' (l1 l2: list ident): comparison :=
    match l1,l2 with
    | [], [] => Eq
    | [], _  => Lt
    | _, []  => Gt
    | a1::l1'', a2::l2'' => 
        match Pos.compare a1 a2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => compare' l1'' l2''
        end 
    end) l1 l2.


End ConstraintOrdering.



Notation "x ⊔ y" := (merge_type x y) (at level 40, left associativity).
Definition st_remove := List.remove ident_eq_dec.
Definition st_mem    := my_set_mem.