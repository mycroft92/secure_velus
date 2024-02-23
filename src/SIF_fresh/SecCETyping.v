From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.

(* From Velus Require Import SIF.SecLattice. *)
From Coq Require Import PArith.
From Velus Require Import SIF.SIFSignature. (* Is this required? *)
From Velus Require Import SymTypes.




Module Type SECCETYPING 
    (Import Ids   : IDS)
    (Import Op    : OPERATORS)
    (Import CESyn : CESYNTAX Op).

    (* *)
    Section SecTypingCE.
      Variable ctxt: Env.t ST.
      Fixpoint assign_exp_type (e: exp) : option ST :=
        match e with
        | Econst const => Some []
        | Evar x _     => Env.find x ctxt
        | Ewhen exp x  =>
           (match assign_exp_type exp with
            | Some
              

       


End SECCETYPING.
