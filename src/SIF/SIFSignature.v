(*Describes security signature related properties.*)
(* Change this implementation to work with res and Sec Monad*)
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

Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list (ident*ident); (*ordered list of input security types*)
    n_out  : list (ident*ident); (*ordered list of output security types*)

    n_reset: ident;
    n_clk  : ident; (*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    constraints : list constraint; (*constraints*)
}.

(* Definition  *)
Local Open Scope option_monad_scope. (* for the monadic notations*)

(* Function to substitute in the security type*)
Fixpoint subst_ident_in_type (ty: ST) (x: ident) (v: ident): ST :=
    match ty with
    | []      => []
    | x'::ty' => if ident_eq_dec x x' then v :: (subst_ident_in_type ty' x v)
                 else x' :: (subst_ident_in_type ty' x v)
    end.


Definition subst_ident_in_constraint (c: constraint) (x: ident) (v: ident): constraint :=
    let (l,h) := c in
    (subst_ident_in_type l x v, h).


Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v:ident)
    : list constraint :=
    List.map (fun c => subst_ident_in_constraint c x v) cs.

(* Check fold_left. *)

(* foreach (x,v) in xv, substitute x with v in cs.*)
Fixpoint subst_idents_in_constraints (cs: list constraint) (xv: list (ident* ident)): list constraint :=
    match xv with
    | []           => cs
    | (x,v) :: xv' => subst_idents_in_constraints (subst_ident_in_constraints cs x v) xv'
    end.

(* Definition subst_signature (sig: signature) (n_in_map n_out_map: list (ident*ident)) (n_reset n_clk: ) *)

Local Fixpoint find_ident (out_map: list (ident*ident)) (x v: ident): option (ident*ident):=
    match out_map with
    | [] => None
    | (x', v'):: out' => if ident_eq_dec x x' then Some (v',v) else find_ident out' x v
    end.

(* this function generates the hash that subst_ident functions can use.
    We generate a new context everytime a node is analyzed hence we need to replace the idents in the constraints of the signature.
    (in_map: [(x,\alpha')]) (cons_map: [(x,\alpha)]) generates output [(\alpha,\alpha')] *)
Fixpoint generate_subst_map' (in_map cons_map acc: list (ident*ident)): option (list (ident*ident)) :=
    match in_map with
    | [] => Some acc
    | (x,v) :: in_map' => 
        do r <- find_ident cons_map x v;
        generate_subst_map' in_map' cons_map (acc ++ [r])
    end.

Definition generate_subst_map in_map cons_map := generate_subst_map' in_map cons_map [].


Definition subst_constraints 
    (node: signature) 
    (inputs_map outputs_map: list (ident*ident)) 
    (reset_type clk_type: ident): option (list constraint) :=
    do  inp_subst_map <- generate_subst_map inputs_map node.(n_in);
    do  out_subst_map <- generate_subst_map outputs_map node.(n_out);
        Some (subst_idents_in_constraints node.(constraints) (inp_subst_map ++ out_subst_map ++ [(node.(n_reset), reset_type); (node.(n_clk), clk_type)])).

(* What correctness criterion would be needed? *)