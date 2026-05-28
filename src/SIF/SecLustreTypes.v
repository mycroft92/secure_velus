(** Symbolic types and constraint operations used by the Lustre-side security layer. *)

From Coq Require Import List.
From Coq Require Import Lists.ListSet.

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Coq Require Import Lia.
Import ListNotations.
From Coq Require Import Recdef.
From Velus Require Import SIF.SymTypes.

Inductive nonCanonST : Type :=
| Bot  : nonCanonST
| Var  : ident -> nonCanonST
| Lub  : nonCanonST -> nonCanonST  -> nonCanonST
| Qual  : nonCanonST -> uConstraint -> nonCanonST
with uConstraint: Type :=
| CNil : uConstraint
| Cns  : (nonCanonST * nonCanonST) -> uConstraint -> uConstraint.

Fixpoint gatherCns (c1 c2:uConstraint): uConstraint:=
  match c1 with
    | CNil => c2
    | Cns x c1' => Cns x (gatherCns c1' c2)
  end.

  Inductive EqNL : nonCanonST -> nonCanonST -> Prop :=
  | refl_case: forall α, EqNL  α α
  | lub_assoc: forall α β θ, EqNL (Lub (Lub α β) θ) (Lub α (Lub β θ))
  | lub_var_refl : forall α, EqNL (Lub (Var α) (Var α)) (Var α)
  | ref_base : forall α, EqNL (Qual α CNil) α
  | ref_lub  : forall α_1 α_2 ρ_1 ρ_2,
     EqNL (Lub (Qual α_1 ρ_1) (Qual α_2 ρ_2)) (Qual (Lub α_1 α_2) (gatherCns ρ_1 ρ_2))
  | ref_ref  : forall α ρ_1 ρ_2, EqNL (Qual (Qual α ρ_1) ρ_2) (Qual α (gatherCns ρ_1 ρ_2))

  | ref_lub_assocl: forall α_1 α_2 ρ,
              EqNL (Lub α_1 (Qual α_2 ρ) ) (Qual (Lub α_1 α_2) ρ)
  | ref_lub_assocr: forall α_1 α_2 ρ,
              EqNL (Lub (Qual α_1 ρ) α_2) (Qual (Lub α_1 α_2) ρ).

Hint Constructors EqNL.

Fixpoint canon (x:nonCanonST): (ST*(list constraint)) :=
  match x with
  | Bot   => ([],[])
  | Var i => ([i],[])
  | Lub α_1 α_2 =>
      let (st1,ρ_1):= canon α_1 in
      let (st2,ρ_2):= canon α_2 in
      (merge st1 st2, ρ_1 ++ ρ_2)
  | Qual i ρ =>
      let (st, ρ') := canon i in
      let ρ'' := unfurl ρ in
      (st, ρ''++ρ')
  end
with unfurl (ρ: uConstraint): list constraint :=
  match ρ with
  | CNil => []
  | Cns (α_1,α_2) ρ' =>
      let (α_1', ρ_1) := canon α_1 in
      let (α_2', ρ_2) := canon α_2 in
      let ρ'' := unfurl ρ' in
      (α_1',α_2') :: ρ_1 ++ ρ_2 ++ ρ''
  end.

Lemma cannon_sortedNoDup: forall x,
              match canon x with
              | (α,_) => sortedNoDup α
              end .
Proof.
  induction x as [|? | α_1 IH1 α_2 IH2| α ρ IH]; simpl; auto.
    - destruct (canon α_1). destruct (canon α_2). apply sortedNoDup_merge; auto.
    - destruct (canon α). auto.
Qed.
