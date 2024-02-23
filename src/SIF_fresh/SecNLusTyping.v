
From Velus Require Import Common.
From Velus Require Import SecLattice.

From Velus Require Import CoindToIndexed.
From Velus Require Import NLustre.

From Coq Require Import String. (*Required for Errors *)

Open Scope list_scope.
Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  

Module Type NLusTyping
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CStr  : COINDSTREAMS    Op OpAux)
       (Import IStr  : INDEXEDSTREAMS  Op OpAux)
       (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
       (Import CE    : COREEXPR    Ids Op OpAux      IStr)
       (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE).

   (* sec typing expressions : mapping -> expression -> sec type *)

   (* sec typing equations   : mapping -> equation -> constraints  *)

   (* sec typing nodes *) 

   (**
    * 1. New name generation scheme
    *   a. Check elab->fresh monad usage
    * 2. Sets up mapping from idents -> idents
    * 3. Typing rules
    * 4. Do we assume that signatures are part of node records or are they seperate records?
    **) 
End NLusTyping.
