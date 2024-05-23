
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import NLustre.
From Velus Require Import SIF.SimpleListTypes.
From Velus Require Import SIF_fresh.SecCETyping.
From Velus Require Import SIF_fresh.SecContext.
From Velus Require Import SIF.SIFSignature.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Open Scope list_scope.
Import List.ListNotations.
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import OpAux : OPERATORS_AUX   Op)
  (Import CStr  : COINDSTREAMS    Op OpAux)
  (Import IStr  : INDEXEDSTREAMS  Op OpAux)
  (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
  (Import CE    : COREEXPR    Ids Op OpAux      IStr)
  (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CE.Syn).
  (* Check wst_exp. *)

  (* expressions are already done in CETyping*)
  (* sec typing expressions : mapping -> expression -> sec type *)
  Check assign_cexp_type.
  Check assign_exp_type.
  Locate global.

  (* sec typing equations   : mapping -> equation -> constraints  *)
  Section SECEEQNTYPING.
    Variable G: secglobal.
    Print equation.
    Fixpoint assign_eqn_type (e: equation) (env: Env.t ident): Sec (list constraint) := 
      match e with
      | EqDef x ck cexp => .

  End SECEEQNTYPING.

  (* sec typing nodes *) 

  (**
   * 1. New name generation scheme
   *   a. Check elab->fresh monad usage
   * 2. Sets up mapping from idents -> idents
   * 3. Typing rules
   * 4. Do we assume that signatures are part of node records or are they seperate records?
   **) 
End SECNLUSTYPING.

Module SecNLusTyping  
(Ids   : IDS)
(Op    : OPERATORS)
(SC    : SECMONAD Ids)
(OpAux : OPERATORS_AUX   Op)
(CStr  : COINDSTREAMS    Op OpAux)
(IStr  : INDEXEDSTREAMS  Op OpAux)
(CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
(CE    : COREEXPR    Ids Op OpAux      IStr)
(NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
(SIG   : SIGNATURE   Ids SC)
(SECCETYPING: SECCETYPING Ids Op CE.Syn) <: SECNLUSTYPING Op SC OpAux CStr IStr CIStr CE NL SECCETYPING.

Include SECNLUSTYPING Op SC OpAux CStr IStr CIStr CE NL SECCETYPING.


End SecNLusTyping.
