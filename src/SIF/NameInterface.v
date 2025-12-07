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

Module Type  NAMEGEN  (Import Ids   : IDS)
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
  Definition insert_env  (env: Env.t ident) (k v: ident): Name (Env.t ident) :=
    let st:= Env.add k v env in
      ret st.

  Definition fresh_insert (env: Env.t ident) (k: ident) : Name (Env.t ident) :=
    if Env.mem k env then
     error (MSG "Key declared more than once ":: [CTX k])
    else
      do v <- fresh_ident_gen; 
      do e <- insert_env env k v;
      ret e.
  
  Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Name B).

  Fixpoint mmap (l: list A) {struct l} : Name (list B) :=
    match l with
    | nil => ret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; ret (hd' :: tl')
    end.
  End mmap.
    
  
  Fixpoint fresh_map_list (ks: list ident) (env: Env.t ident): Name (Env.t ident) :=
    match ks with
    | nil => ret env
    | k::ks' => (
      do e' <- fresh_insert env k;
      do e'' <- fresh_map_list ks' e';
      ret e'')
    end.

  Record node_aux_names := mkNames {
    nname : ident;
    nclk: ident;
    nrst: ident;
  }.
  
  Print node.
  (* Do something for clock and reset names, then their mappings*)
  Definition generate_new_names_for_node (n: node) (e: Env.t ident): Name (Env.t ident * node_aux_names):=
    do clk_name <- fresh_ident_gen;
    do rst_name <- fresh_ident_gen;
    do env' <- fresh_map_list ([clk_name; rst_name]  ++ (map fst  (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) e;
    ret (env', {| nname:= n.(n_name) ; nclk := clk_name ; nrst := rst_name|}).

  Fixpoint generate_node_env' (ns: list node) (e: Env.t ident) (acc: list node_aux_names): Name (Env.t ident * list node_aux_names) :=
    match ns with
    | [] => ret (e, acc)
    | n::ns' => 
      do (e',r) <- generate_new_names_for_node n e;
      do (e'', rs) <- generate_node_env' ns' e' (r::acc);
      ret (e'', rs)
    end.

  Definition generate_node_env (ns: list node) : res (Env.t ident * list node_aux_names) :=
    match generate_node_env' ns (Env.empty _) [] init_state with
    | OK ((e, names), _) => OK (e,names)
    | Error e => Error e
    end.

  Fixpoint find_node_names (n: ident) (nnames: list node_aux_names) : res node_aux_names :=
    match nnames with
    | [] => Error (MSG "Node not processed! ":: [CTX n])
    | name::nnames' => if (ident_eqb n name.(nname)) then OK name else find_node_names n nnames'
    end.
   

End NAMEGEN.


Module Type  NameGen  (Ids   : IDS)
  (Op    : OPERATORS)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn) <: NAMEGEN Ids Op CESyn SynNL.

Include NAMEGEN Ids Op CESyn SynNL.

End NameGen.