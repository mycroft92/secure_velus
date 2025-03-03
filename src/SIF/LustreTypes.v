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


(**
* (rho, cons) ++ (rho, cons) results in confluence


*)


(* 
(* Canoncalize these and prove confluence*)
(* Don't work with syntax, instead work with ST*list constraint format*)
Inductive nonCanonST : Type :=
| Bot   : nonCanonST
| Var   : ident -> nonCanonST
| Lub   : nonCanonST -> nonCanonST  -> nonCanonST
| Qual  : nonCanonST -> uConstraint -> nonCanonST
with uConstraint: Type := 
| CNil  : uConstraint
| Cns   : (nonCanonST * nonCanonST) -> uConstraint -> uConstraint.

Inductive ncST : Type :=
| bot  : ncST
| lubs : list ident -> ncST
| qual : ncST -> ucons -> ncST
with ucons: Type :=
| cnil : ucons
| cns  : (ncST * ncST) -> ucons -> ucons.

Fixpoint canonicalizeT (ty: ncST) : (ST * (list constraint)):=
  match ty with
  | bot => ([], [])
  | lubs ls => (ls, [])
  | qual ty' cxs => 
    let (cty, cns') := canonicalizeT ty' in
    let cns'' := canonicalizeConstraints cxs in
    (cty, constraint_merge cns' cns'')
  end
with canonicalizeConstraints cn : list constraint :=
  match cn with
  | cnil => []
  | cns (lhs, rhs) cxs => 
    let  cxs' := canonicalizeConstraints cxs in
    let (s1, c1) := canonicalizeT lhs in
    let (s2, c2) := canonicalizeT rhs in
      constraint_merge [(s1,s2)] (constraint_merge (constraint_merge c1 c2) cxs') 
  end.


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
    | Qual x uc => let (x',xcs) := canonicalizeType x in
                   let cs := canonicalizeConstraint uc in
                   (x', constraint_merge cs xcs)
    end
with canonicalizeConstraint (cons: uConstraint) : (list constraint) :=
  
  match cons with
  | CNil => []
  | Cns (lhs, rhs) cxs => let  cxs' := canonicalizeConstraint cxs in
                          let (s1, c1) := canonicalizeType lhs in
                          let (s2, c2) := canonicalizeType rhs in
                          constraint_merge [(s1,s2)] (constraint_merge (constraint_merge c1 c2) cxs')

  end.


(* Write the relation for constraint-type rewrite*)

Inductive Rewrite_Rel (t: nonCanonST) (s: ST) : Prop :=.
(* State and prove confluence for that relation*)
Prove canonicalizeType satisfies the relation *)