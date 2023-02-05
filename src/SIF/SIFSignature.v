(*Describes security signature related properties.*)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 
From Coq   Require Import List Sorting.Permutation.
Import List.ListNotations.

(*
    Given a node with input variables: x,y and output: z in the node signature
    Say n_in: [α_1,α_2], n_out:= [β], 
    we always asssume x has type α_1, y has type α_2 and z has type β
    Constraints can be in any order!
*)

(* 1. How do I carry the constraints?
   2. How do I replace the vars in constraints with newly generated names? *)

(* Plan is to finish the typing here and then move to typing Lustre *)
Definition SecCtxt := Env.t ident. 
Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list (ident*ident); (*ordered list of input security types*)
    n_out  : list (ident*ident); (*ordered list of output security types*)
    n_reset: ident;
    n_clk  : ident; (*The base clock is always empty list*)
    constraints : list constraint; (*constraints*)
}.

Print ST.
Locate ident_eq_dec.

(* Function to substitute in the security type*)
Fixpoint subst_ident_in_type (ty: ST) (x: ident) (v: ident): ST :=
    match ty with
    | [] => []
    | x'::ty' => if ident_eq_dec x x' then v :: (subst_ident_in_type ty' x v)
                 else x' :: (subst_ident_in_type ty' x v)
    end.

Print constraint.

Definition subst_ident_in_constraint (c: constraint) (x: ident) (v: ident): constraint :=
    let (l,h) := c in
    (subst_ident_in_type l x v, subst_ident_in_type h x v).

