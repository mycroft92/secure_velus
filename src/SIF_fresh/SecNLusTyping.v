
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import NLustre.
From Velus Require Import SIF.SimpleListTypes.
From Velus Require Import SIF_fresh.SecCETyping.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Open Scope list_scope.
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX   Op)
  (Import CStr  : COINDSTREAMS    Op OpAux)
  (Import IStr  : INDEXEDSTREAMS  Op OpAux)
  (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
  (Import CE    : COREEXPR    Ids Op OpAux      IStr)
  (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
  (Import SECCETYPING: SECCETYPING Ids Op CE.Syn).
  (* Check wst_exp. *)

  Section SecMonad.
    Context {A : Type}.
    (* The state is current fresh number to use to generate the name 
     * and the map of currently generated type for each program var *)
    Definition sec_state : Type := (ident * Env.t ident).
    Print res.
    Definition Sec A := sec_state -> res (A * sec_state).
    Definition init_state : sec_state := (xH, Env.empty _).

    Definition ret (x : A) : Sec A := fun st => OK (x, st).

    Definition bind {B : Type} (x : Sec A) (f : A -> Sec B) : Sec B :=
      fun st => match (x st) with
            | OK (a, st') => f a st'
            | Error err => Error err
            end.

    Definition bind2 {A1 A2 B : Type} (x : Sec (A1 * A2)) (f : A1 -> A2 -> Sec B) : Sec B :=
      fun st => match (x st) with
            | OK ((a1, a2), st') => f a1 a2 st'
            | Error err => Error err
            end.

    Definition error (msg : errmsg) : Sec A :=
      fun st => Error msg.

    Definition fresh_ident : Sec ident :=
      fun '(n, sub1) =>
        let id := Ids.gensym Ids.sec n in
        OK (id, (Pos.succ n, sub1)).

    (* Need a function to insert into the state and get the state itself*)



  End SecMonad.
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
End SECNLUSTYPING.
