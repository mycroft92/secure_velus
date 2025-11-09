(* The point of this file is to create a consistent naming environment during NLustre typing phase.

These names woud be passed to STC as well. 
I ma unsure how we are going to do Lus-Nlus but we focus on NLus to STC for now.
Then onto non-interference*)
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.


From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Module Type  NameGen  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn).

  Section NameMonad.
  Context {A : Type}.

  (* The state is current fresh number to use to generate the name 
   * and the map of currently generated type for each program var *)
  (* Definition sec_state : Type := (ident * Env.t ident). *) (* Old formulation*)
  Definition name_state : Type := ident.
  Definition Name A := name_state -> (A * name_state).
  (* Definition init_state : sec_state := (xH, Env.empty _). *) (*old formulation*)
  Definition init_state : name_state := xH.
  (* Definition initialize : ident -> Env.t ident -> sec_state := fun xi ev => (xi, ev).  *) (*old formulaton*)
  Definition initialize : ident -> name_state := fun xi  => xi.
  
  Definition ret (x : A) : Name A := fun st =>  (x, st).
  
  Definition bind {B : Type} (x : Name A) (f : A -> Name B) : Name B :=
    fun st => match (x st) with
          | (a, st') => f a st'
          end.
  
  Definition bind2 {A1 A2 B : Type} (x : Name (A1 * A2)) (f : A1 -> A2 -> Name B) : Name B :=
    fun st => match (x st) with
          | ((a1, a2), st') => f a1 a2 st'
          end.
  
  (* Definition fresh_ident : Sec ident :=
    fun '(n, sub1) =>
      let id := Ids.gensym Ids.sec n in
      OK (id, (Pos.succ n, sub1)). *) (* old formulation*)
  Definition fresh_ident_gen : Name ident :=
    fun n =>
      let id := Ids.gensym Ids.sec n in
      (id, Pos.succ n).
  
  Definition gets : Name sec_state :=
    fun st =>  (st, st).

  (* (*Just ignore st'. We instead have st coming *)
  Definition puts : sec_state -> Sec unit :=
    fun st => fun st' => OK (tt, st).  *)
  
  Lemma name_bind_inv {B} : forall (x : Name A) (f : A -> Name B) res st,
      (bind x f) st = OK res ->
      exists y st'',
        x st = OK (y, st'') /\ f y st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind in Hbind.
    destruct (x st) as [[y st'']|]; eauto. inv Hbind.

  End NameMonad.

End NameGen.