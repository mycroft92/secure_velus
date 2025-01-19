From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Coq Require Import Lia.
Import ListNotations.
From Coq Require Import Recdef.
From Velus Require Import SIF.SymTypes.
(*These are types ued for Lustre typing, they are converted to simple types eventually.*)
(*canonical type specification and correctness to be proved*)
(* We will do this later*)


(* Canoncalize these and prove confluence*)
Inductive nonCanonST : Type :=
| Bot  : nonCanonST
| Var  : ident -> nonCanonST
| Lub  : nonCanonST -> nonCanonST  -> nonCanonST
| Qual  : nonCanonST -> uConstraint -> nonCanonST
with uConstraint: Type := 
| CNil : uConstraint
| Cns  : (nonCanonST * nonCanonST) -> uConstraint -> uConstraint.

Print constraint.
(* Needs to return a type and a constraint set *)
(* Constraint merge needs to be smarter*)
Fixpoint canonicalizeType (ty: nonCanonST) : (ST * (list constraint)) :=
    match ty with
    | Bot => ([],[])
    | Var i => ([i],[])
    | Lub x y => let (x',xc) := (canonicalizeType x) in
                 let (y',yc) := (canonicalizeType y) in
                 (x' ⊔ y', xc ++yc)
    | Qual x uc => ([],[])
    end
with canonicalizeConstraint (cons: uConstraint) : (list constraint) :=
  
  match cons with
  | CNil => []
  | Cns (lhs, rhs) cxs => let  cxs' := canonicalizeConstraint cxs in
                          let (s1, c1) := canonicalizeType lhs in
                          let (s2, c2)  := canonicalizeType rhs in
                          constraint_merge [(s1,s2)] (constraint_merge (constraint_merge c1 c2) cxs')

  end.
