(*Describes security signature related properties.*)
(* Change this implementation to work with res and Sec Monad*)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 
From Velus Require Import SIF_fresh.SecContext.
From Coq   Require Import List Sorting.Permutation.
From Coq Require Import String. (*for errors*)
From compcert Require Import common.Errors.
Import List.ListNotations.

(*
    Given a node with input variables: x,y and output: z in the node signature
    Say n_in: [α_1,α_2], n_out:= [β], 
    we always asssume x has type α_1, y has type α_2 and z has type β
    Constraints can be in any order!
*)


Module Type SIGNATURE 
  (Import Ids : IDS)
  (Import SC  : SECMONAD Ids).
(* 1. How do I carry the constraints?
   2. How do I replace the vars in constraints with newly generated names? *)
Import SECMONADNotations.
Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list (ident*ident); (*ordered list of input security types*)
    n_out  : list (ident*ident); (*ordered list of output security types*)

    n_reset: ident*ident; (* We generate the name for the reset type and its corresponding value*)
    n_clk  : ident*ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    constraints : list constraint; (*constraints*)
}.
Definition secglobal := list signature.


Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(n_name) f).

(* Section Substitutions.
    (*This deals with substituting types into a signature's constraints during nodecalls *)

    Fixpoint subst_ident_in_type (ty: ST) (x: ident) (v: ident): ST :=
        match ty with
        | []      => []
        | x'::ty' => if ident_eq_dec x x' then v :: (subst_ident_in_type ty' x v)
                    else x' :: (subst_ident_in_type ty' x v)
        end.


    Definition subst_ident_in_constraint (c: constraint) (x: ident) (v: ident): constraint :=
        let (l,h) := c in
        match ident_eqb h x with
        | true  => (subst_ident_in_type l x v, v)
        | false => (subst_ident_in_type l x v, h)
        end.

    (* forall c ∈ cs, c[v/x]*)
    Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v:ident)
        : list constraint :=
        List.map (fun c => subst_ident_in_constraint c x v) cs.

    (* Check res. *)

    (* foreach (x,v) in xv, substitute x with v in cs.*)
    Fixpoint subst_idents_in_constraints (cs: list constraint) (xv: list (ident* ident)): list constraint :=
        match xv with
        | []           => cs
        | (x,v) :: xv' => subst_idents_in_constraints (subst_ident_in_constraints cs x v) xv'
        end.

    (* Finds x's mapping in the environment so that the sec type assumed for it in the signature can be replaced by the env value.*)
    Local Definition find (x v: ident) (env: Env.t ident): Sec (ident*ident) :=
        match (Env.find x env) with
        | Some v' => ret (v,v')
        | None    => error (MSG "Identifier not found in generated map" :: [CTX x])
        end.

    (* This would have been nicer with a monadic notation but 
    * I am not totally clear about notation overrides     *)
    (* Find that for a list of x's.*)
    Fixpoint find_all_idents (xvs: list (ident*ident)) (env: Env.t ident): Sec (list (ident*ident)) :=
        match xvs with
        | []  => ret []
        | (x,v)::xvs' => 
            do (v,v') <- find x v env;
            do xs <- find_all_idents xvs' env;
            ret ((v,v')::xs)
        end.

    (* Don't know how to block sec_reset and sec_clk as restricted identifiers*)
    Definition subst_constraints (node: signature) (env: Env.t ident) : Sec (list constraint):=
        do inp_subst_map <- find_all_idents node.(n_in) env;
        do out_subst_map <- find_all_idents node.(n_out) env;
        do reset_map     <- find (fst node.(n_reset)) (snd node.(n_reset)) env;
        do clk_map       <- find (fst node.(n_clk)) (snd node.(n_clk)) env;
        ret (subst_idents_in_constraints node.(constraints) (clk_map::reset_map::(inp_subst_map++out_subst_map))).

End Substitutions.  *)


Section Type_Substitutions.
    (* ty[v/x] substitution*)
  Local Definition subst_ident_in_type (ty: ST) (x: ident) (v: ST): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ (st_remove x v)
    end.
  
  Local Definition subst_ident_in_constraint (c: constraint) (x: ident) (v: ST): Sec constraint :=
    match c with
    | (ty, [x']) => 
      if ident_eqb x x' then
        error (MSG "Something wrong with fresh_gen, ident is regenerated in an inner node. " :: [CTX x])
      else ret (subst_ident_in_type ty x v, [x'])
    | _ => error (msg "malformed constraint")
    end.

   (* forall c ∈ cs, c[v/x]*)
   Local Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v:ST)
   : Sec (list constraint) :=
   mmap (fun c => subst_ident_in_constraint c x v) cs.

   (*input types are to substituted by this function *)
   Fixpoint subst_constraints_inp_map (cs: list constraint) (xs: list ident) (vs: list ST): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs => 
    (*Do we need additional help like x is not present in ANY vs?*)
      do cs' <- subst_ident_in_constraints cs x v;
      subst_constraints_inp_map cs' xs vs
    | _, _ => error (msg "Malformed replace map")
    end.

    Local Definition subst_ident (ty: ST) (x v: ident): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ [v]
    end.

    Local Definition subst_ident_constraint (c: constraint) (x v: ident): Sec constraint :=
    match c with
    | (ty, [x']) => 
       if ident_eqb x x' then
        ret (subst_ident ty x v, [v])
       else ret (subst_ident ty x v, [x'])
    | _  => error (msg "Malformed constraint")
    end.
   
End Type_Substitutions.

End SIGNATURE.
(* What correctness criterion would be needed? *)
(*Need to write a bunch of axioms that the number of list node == number of signature, for every node there is a signature etc..*)

Module Signature 
    (Ids : IDS)
    (SC : SECMONAD Ids) <: SIGNATURE Ids SC.
Include SIGNATURE Ids SC.
End Signature.

(*OLD stuf not needed*)
(* Definition subst_signature (sig: signature) (n_in_map n_out_map: list (ident*ident)) (n_reset n_clk: ) *)
(* 
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
        Some (subst_idents_in_constraints node.(constraints) (inp_subst_map ++ out_subst_map ++ [(node.(n_reset), reset_type); (node.(n_clk), clk_type)])). *)

