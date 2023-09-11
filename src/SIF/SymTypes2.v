From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Coq Require Import Lia.

Import ListNotations.
From Coq Require Import Recdef.


Inductive nonCanonST: Type :=
    | Bot  : nonCanonST
    | Var  : ident -> nonCanonST
    | Lub  : nonCanonST -> nonCanonST -> nonCanonST
    | Qual : nonCanonST -> uConstraint -> nonCanonST
with uConstraint: Type :=
    | CNil : uConstraint
    (* This version takes an ident. I need a way to escalate it to nonCanonST level *)
    | Cns  : (nonCanonST * ident) -> uConstraint -> uConstraint. 

Definition ST := list ident.
Definition constraint := (ST*ident)%type.


Fixpoint my_set_mem (a: ident) (st: ST) : bool :=
    match st with
    | [] => false
    | a_0 :: st' => if ident_eqb a_0 a then true else my_set_mem a st'
    end.

Lemma my_set_mem_correct: forall a st, my_set_mem a st = true <-> In a st.
Proof.
    intros. generalize dependent a. induction st; split; intros; auto.
    - inversion H.
    - simpl in H. destruct (ident_eqb a a0) eqn:E. 
        * apply (ident_eqb_eq) in E. subst. simpl. left. auto.
        * apply (ident_eqb_neq) in E. simpl. right. now apply IHst... 
    - simpl.  destruct (ident_eqb a a0) eqn:E. 
        * auto.
        * apply (ident_eqb_neq) in E. simpl in H. 
          destruct H as [H1|H2]. elim (E H1). (*a0 = a*)
          now apply IHst.
Qed.
  (*for now this is just a plain append*)
Fixpoint gatherCns (c1 c2:uConstraint): uConstraint:=
  match c1 with
  | CNil      => c2
  | Cns x c1' => Cns x (gatherCns c1' c2)
  end.

  (* Do a merge sort like operation not simple ++: Sanjiva*)
  (* Maybe assume sortedness and do the typing*)
Fixpoint canonicalizeType (nc: nonCanonST): (ST * (list constraint)) :=
    match nc with
    | Bot       => ([],  [])
    | Var x     => ([x], [])
    | Lub x1 x2 => let (s2, c2) := canonicalizeType x2 in
                   let (s1, c1)  := canonicalizeType x1 in
                    (mergesort s1 s2, c1 ++ c2)
    | Qual x c  => let c2 := canonicalizeConstraints c in
                   let (s1, c1)  := canonicalizeType x in  
                    (s1, c1++c2)
    end 
with canonicalizeConstraints (c: uConstraint):  (list constraint) :=
    match c with
    | CNil             => []
    | Cns (ncst,i) cxs => let  c2 := canonicalizeConstraints cxs in
                          let (s1, c1) := canonicalizeType ncst in
                          (s1,i):: (c1 ++ c2)
    end.

(*Setting this correctness is going to be hard*)
