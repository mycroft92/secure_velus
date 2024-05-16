From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.SimpleListTypes.


From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Open Scope list_scope.

Module SecMonad (Import Ids   : IDS).

Section MySecMonad.
Context {A : Type}.
(* The state is current fresh number to use to generate the name 
 * and the map of currently generated type for each program var *)
Definition sec_state : Type := (ident * Env.t ident).

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
(* Definition insert_map (x v: ident): Sec unit :=
  fun st => Env. *)


End MySecMonad.
End SecMonad.

Module ElabNotations.

Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" :=
  (bind2 A (fun X Y => B))
    (at level 200, X ident, Y ident, A at level 100, B at level 200).

End ElabNotations.