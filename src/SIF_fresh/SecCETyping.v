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
From Coq Require Import List.
Import ListNotations.


Module Type SECCETYPING 
    (Import Ids   : IDS)
    (Import Op    : OPERATORS)
    (Import CESyn : CESYNTAX Op).

  Open Scope option_monad_scope.  
  
    (* *)
  Section SecTypingCE.
    Variable ctxt: Env.t ident.
    Inductive wst_clock : clock -> ST -> Prop :=
      | wst_Base: forall ty,
        Env.find sec_clk ctxt = Some ty ->
        wst_clock Cbase [ty]
      | wst_On: forall ck x b ckty xty,
        wst_clock ck ckty ->
        Env.find x ctxt = Some xty ->
        wst_clock (Con ck x b) (ckty ⊔ [xty]).

    Inductive wst_exp : exp -> ST -> Prop :=
      | wst_Econst : forall c,
          wst_exp (Econst c) []
      | wst_Evar   : forall x t ty,
          Env.find x ctxt = Some ty ->
          wst_exp (Evar x t) [ty]
      | wst_Ewhen  : forall e x b xty ety,
          Env.find x ctxt = Some xty ->
          wst_exp e ety ->
          wst_exp (Ewhen e x b) (ety ⊔ [xty])
      | wst_Eunop  : forall o e ety t,
          wst_exp e ety ->
          wst_exp (Eunop o e t) ety
      | wst_Ebinop : forall b e1 e2 e1ty e2ty t,
          wst_exp e1 e1ty ->
          wst_exp e2 e2ty ->
          wst_exp (Ebinop b e1 e2 t) (e1ty ⊔ e2ty).

    Fixpoint assign_clk_type (c: clock): option ST :=
      match c with
      | Cbase       => 
        (match Env.find sec_clk ctxt with
          | Some cty => Some [cty]
          | None     => None
          end)

      | Con ck' x _ => 
          do ckty <- assign_clk_type ck';
          do xty  <- Env.find x ctxt;
          Some (ckty ⊔ [xty])
      end. 

    Fixpoint assign_exp_type (e: exp) : option ST :=
      match e with
      | Econst const   => Some []
      | Evar x _       => do xty <- Env.find x ctxt; Some [xty]
      | Ewhen exp x _  => 
          do ety <- assign_exp_type exp;
          do xty <- Env.find x ctxt;
          Some (ety ⊔ [xty])
      | Eunop _ e' _     => assign_exp_type e'
      | Ebinop _ e1 e2 _ => 
          do e1ty <- assign_exp_type e1;
          do e2ty <- assign_exp_type e2;
          Some (e1ty ⊔ e2ty)
      end.

    Fixpoint assign_cexp_type (ce: cexp) : option ST :=
      match ce with
      | Emerge x ce1 ce2 =>
          do xty  <- Env.find x ctxt;
          do c1ty <- assign_cexp_type ce1;
          do c2ty <- assign_cexp_type ce2;
          Some ([xty] ⊔ c1ty ⊔ c2ty)
      | Eite e cet cef  =>
          do ety  <- assign_exp_type e;
          do c1ty <- assign_cexp_type cet;
          do c2ty <- assign_cexp_type cef;
          Some (ety ⊔ c1ty ⊔ c2ty)
      |  Eexp e    => assign_exp_type e
      end.
    Hint Constructors wst_clock.

    Theorem assign_clk_correct: forall ck st, wst_clock ck st -> assign_clk_type ck = Some st.
    Proof.
      induction ck; intros.
      - simpl. inversion H. destruct (Env.find sec_clk ctxt) eqn:E. 
       * inversion H0; now subst.
       * congruence.
      - unfold assign_clk_type. fold assign_clk_type. 
        inversion H as [| ?????? H_find]. subst.
        assert (assign_clk_type ck = Some ckty) as H'. { now apply IHck. }
        rewrite H',H_find. reflexivity.
    Qed.
    
    (* Similar theorems needed for other syntactic levels*)
  End SecTypingCE. 


End SECCETYPING.
