(* Need to do sorting of ST and constraints *)
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Lists.ListSet.
From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import SIF.Helpers.


Import ListNotations.

(* Need to extend order from idents to list of idents*)
(* first step induction principle on list of idents*)

(* Local Ltac HelperCrush :=
   *)

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
        | Lt => a2::(mergeType l1' l2)
        | Eq => a1::(mergeType l1' l2')
        | Gt => a1::(merge_aux l2')
        end)
      end) in merge_aux l2.
(* Need to do final mergesort*)
  Lemma merge_lt: forall (x1 x2: ident) r1 r2,
    Pos.compare x1 x2 = Lt -> 
      mergeType (x1::r1) (x2::r2) = x2:: mergeType r1 (x2::r2).
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
(* Lemma sorted_merge1: forall x x1 l1 x2 l2, 
    x > x1 -> x > x2 -> sorted (mergeType (x1::l1) (x2::l2)) -> sorted (x::mergeType (x1::l1) (x2::l2)).*)

(* Lemma sorted_merge: forall l1, sorted l1 -> forall l2, sorted l2 -> sorted (mergeType l1 l2).*)

  Lemma mergesort_correct: forall l, sortedDecNoDup (mergesort l).
  Proof.
      Admitted.
End MergeIdentList.


Section ConstraintOrdering.
(*do we assume the lists are sorted?*)
  Fixpoint ident_list_compare (l1 l2: list ident): comparison :=
    let l1' := mergesort l1 in
    let l2' := mergesort l2 in
    match l1',l2' with
    | [], [] => EQ
    | [], _  => LT
    | _, []  => GT
    | a1::l1'', a2::l2'' => 
        match Pos.compare a1 a2 with
        | LT => LT
        | GT => GT
        | EQ => ident_list_compare l1'' l2''
        end 
    end.



    (* Do I need split?*)


