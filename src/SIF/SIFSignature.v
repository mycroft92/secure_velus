(*Describes security signature related properties.*)
(* Change this implementation to work with res and Sec Monad*)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 
From Velus Require Import SIF.SecTypes. 
From Velus Require Export SIF.SecLattice.
From Velus Require Import SIF.SecContext.
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
(* Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list (ident*ident); (*ordered list of input security types*)
    n_out  : list (ident*ident); (*ordered list of output security types*)

    n_reset: ident*ident; (* We generate the name for the reset type and its corresponding value*)
    n_clk  : ident*ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    constraints : list constraint; (*constraints*)
}. *)
(*simpler record*)
Record signature := mkSig {
    s_name : ident; (*node name*)
    s_in   : list ident; (*ordered list of input security types*)
    s_out  : list ident; (*ordered list of output security types*)

    s_reset: ident; (* We generate the name for the reset type and its corresponding value*)
    s_clk  : ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    s_constraints : list constraint; (*constraints*)
}.
Definition secglobal := list signature.


Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).


Section Type_Substitutions.
    (* ty[v/x] substitution*)
  Local Definition subst_ident_in_type (ty: ST) (x: ident) (v: ST): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ (st_remove x v)
    end.
  (* THIS is ST substitution, need to rethink. substituting preserves type maybe required here. *)
  
  Local Definition subst_inp_ident_in_constraint (c: constraint) (x: ident) (v: ST): Sec constraint :=
    match c with
    | (ty, [x']) => 
      if ident_eqb x x' then
        error (MSG "Something wrong with fresh_gen, ident is regenerated in an inner node. " :: [CTX x])
      else ret (subst_ident_in_type ty x v, [x'])
    | _ => error (msg "malformed constraint")
    end.
  (* THIS is ST substitution, need to rethink. substitution preserves satisfiability required here*)
   (* forall c ∈ cs, c[v/x]*)
   Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v: ST)
   : Sec (list constraint) :=
   mmap (fun c => subst_inp_ident_in_constraint c x v) cs.

   (*input types are to substituted by this function, in the FINAL call constraint set. *)
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
    if ident_eqb x v then error (msg "Illegal same ident substitution") else
    (match c with
    | (ty, [x']) => 
       if ident_eqb x x' then
        ret (subst_ident ty x v, [v])
       else ret (subst_ident ty x v, [x'])
    | _  => error (msg "Malformed constraint")
    end).

    Local Definition subst_ident_constraints (cs: list constraint) (x v: ident): Sec (list constraint) :=
    mmap (fun c => subst_ident_constraint c x v) cs.

    Fixpoint subst_constraints_out_map (cs: list constraint) (xs: list ident) (vs: list ident): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs => 
    (*Do we need additional help like x is not present in ANY vs?*)
      do cs' <- subst_ident_constraints cs x v;
      subst_constraints_out_map cs' xs vs
    | _, _ => error (msg "Malformed replace map")
    end.
  (* We need lemmas that the substitution is happening correctly *)
    Definition generate_constraints (node: signature) 
      (inp: list ST) 
      (clk: ST) 
      (res: ST) 
      (out: list ident): Sec (list constraint) :=
      do inp_subst_constraints <- subst_constraints_inp_map node.(s_constraints) node.(s_in) inp;
      do clk_subst_constraints <- subst_ident_in_constraints inp_subst_constraints node.(s_clk) clk;
      do res_subst_constraints <- subst_ident_in_constraints clk_subst_constraints node.(s_reset) res;
      subst_constraints_out_map res_subst_constraints node.(s_out) out.
    
  (* Substitution lemma *)
   
End Type_Substitutions.

End SIGNATURE.
(* What correctness criterion would be needed? *)
(**)
(*Need to write a bunch of axioms that the number of list node == number of signature, for every node there is a signature etc..*)

Module Signature 
    (Ids : IDS)
    (SC : SECMONAD Ids) <: SIGNATURE Ids SC.
Include SIGNATURE Ids SC.
End Signature.

Module Type SIGNATURE_PROOFS (Import Ids: IDS)
  (Import SC: SECMONAD Ids)
  (Import SIG: SIGNATURE Ids SC)
  (Import Lat: Lattice)
  (Import SecTypes: SECTYPES Lat).

Lemma st_remove_correct: forall dlt ty x, hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty.
Proof.
induction ty; intros.
- now unfold SymTypes.st_remove.
- unfold  SymTypes.st_remove. simpl.
  destruct (ident_eq_dec x a) eqn:Hxa.
  + subst x. assert (hm_ext dlt (remove ident_eq_dec a ty) ⊑ hm_ext dlt ty) as H1. { auto. }
  assert (hm_ext dlt ty ⊑ join (dlt a) (hm_ext dlt ty)) as H2. { apply join_bound2. }
  now eapply order_trans.
  + simpl. auto.
Qed. 



Lemma subst_ident_in_type_correct: 
    forall dlt x st ty, hm_ext dlt st ⊑ dlt x 
    -> hm_ext dlt (SIG.subst_ident_in_type ty x st) ⊑ hm_ext dlt ty.
Proof.
  induction ty; intros; unfold SIG.subst_ident_in_type; unfold SymTypes.my_set_mem; auto.
  destruct (ident_eqb a x) eqn:Hax.
  - unfold SymTypes.st_remove.  
    apply ident_eqb_eq in Hax; subst. simpl.
    destruct (ident_eq_dec x x) eqn:Hxx; auto.
    * fold SymTypes.st_remove. apply (hm_ext_distributive dlt (SymTypes.st_remove x st) (SymTypes.st_remove x ty) (join (dlt x) (hm_ext dlt ty))).
    + (* Mundane proofs, need to use lattice assumptions*)
Admitted.

End SIGNATURE_PROOFS.