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


Open Scope list_scope.

Module Type  NameGen  (Import Ids   : IDS)
  (Import Op    : OPERATORS)

  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn).

  Section NameMonad.
  Context {A : Type}.

  (* The state is current fresh number to use to generate the name 
   * and the map of currently generated type for each program var *)
  (* Definition sec_state : Type := (ident * Env.t ident). *) (* Old formulation*)
  Definition name_state : Type := ident.
  Definition Name A := name_state -> res (A * name_state).
  (* Definition init_state : sec_state := (xH, Env.empty _). *) (*old formulation*)
  Definition init_state : name_state := xH.
  (* Definition initialize : ident -> Env.t ident -> sec_state := fun xi ev => (xi, ev).  *) (*old formulaton*)
  Definition initialize : ident -> name_state := fun xi  => xi.
  
  Definition ret (x : A) : Name A := fun st =>  OK (x, st).
  
  Definition bind {B : Type} (x : Name A) (f : A -> Name B) : Name B :=
    fun st => match (x st) with
          | OK (a, st') => f a st'
          | Error err => Error err
          end.
  
  Definition bind2 {A1 A2 B : Type} (x : Name (A1 * A2)) (f : A1 -> A2 -> Name B) : Name B :=
    fun st => match (x st) with
          | OK ((a1, a2), st') => f a1 a2 st'
          | Error err => Error err
          end.
   Definition error (msg : errmsg) : Name A :=
    fun st => Error msg.
  
  (* Definition fresh_ident : Sec ident :=
    fun '(n, sub1) =>
      let id := Ids.gensym Ids.sec n in
      OK (id, (Pos.succ n, sub1)). *) (* old formulation*)
  Definition fresh_ident_gen : Name ident :=
    fun n =>
      let id := Ids.gensym Ids.sec n in
      OK (id, Pos.succ n).
  
  Definition gets : Name name_state :=
    fun st =>  OK (st, st).

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
  Qed.

  Lemma name_bind2_inv {A1 A2 B} : forall (x : Name (A1 * A2)) (f : A1 -> A2 -> Name B) res st,
      (bind2 x f) st = OK res ->
      exists y1 y2 st'',
        x st = OK ((y1, y2), st'') /\ f y1 y2 st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind2 in Hbind.
   destruct (x st) as [[[y1 y2] st'']|]; eauto. inv Hbind.
  Qed.

  End NameMonad.

  Module NAMEMONADNotations.
    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X ident, A at level 100, B at level 200).
        
    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200).
        
  End NAMEMONADNotations.
  Import NAMEMONADNotations.
  Import List.ListNotations.

(* To insert into the map*)
  Definition insert_env (k v: ident) (env: Env.t ident): Name (Env.t ident) :=
    let st:= Env.add k v env in
      ret st.

  Definition fresh_insert (k: ident) (env: Env.t ident): Name (Env.t ident*ident) :=
    if Env.mem k env then
     error (MSG "Key declared more than once ":: [CTX k])
    else
      do v <- fresh_ident_gen; 
      do e <- insert_env k v env;
      ret (e, v).

   

End NameGen.