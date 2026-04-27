(** Shared security-name generation for the NLustre/STC translation proofs.

    The generators in this file build one common environment of security
    identifiers for node inputs, outputs, locals, and the extra clock/reset
    auxiliaries. Both NLustre and STC typing reuse that environment so the
    translation theorem can talk about a single naming discipline. *)
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.


From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Open Scope list_scope.

Record node_aux_names := mkNames {
    nname : ident;
    nclk: ident;
    nrst: ident;
}.
Import List.ListNotations.
Fixpoint find_node_names (n: ident) (nnames: list node_aux_names) : option node_aux_names :=
    match nnames with
    | [] => None
    | name::nnames' => if (ident_eqb n name.(nname)) then Some name else find_node_names n nnames'
    end.
   
Definition get_node_aux (n: ident) (nnames: list node_aux_names) : option (ident*ident) :=
    let nsearch := find_node_names n nnames in
    match nsearch with
    | Some nod => Some (nod.(nclk), nod.(nrst))
    | None => None
    end.
Section Env_helpers.

  Open Scope option_monad_scope.
  Fixpoint get_mappings (ns: list ident)  (env: Env.t ident) : option (list ident) :=
    match ns with
    | [] => Some []
    | x::xs => do t  <- Env.find x env;
              do ts <- get_mappings xs env;
              Some (t::ts)
    end.
  
  Fixpoint get_mappings_from_node {A: Type} (ns: list (ident * A) ) (env: Env.t ident) : option (list ident):=
    match ns with
    | [] => Some []
    | (x,_)::xs => do t  <- Env.find x env;
                   do ts <- get_mappings_from_node xs env;
                   Some (t::ts)
    end.

  (** The lemmas below are the reusable interface between the shared
      name-generation environment and the phase-specific typing proofs.

      They let later developments move back and forth between:
      - source identifiers in node/system interfaces;
      - their generated security identifiers in the shared environment;
      - list-level results returned by [get_mappings] / [get_mappings_from_node].

      Keeping these facts here avoids repeating the same environment-plumbing
      proofs inside both the NLustre/STC typing modules and the translation
      preservation file. *)

  Lemma get_mappings_app:
    forall xs ys env txs tys,
      get_mappings xs env = Some txs ->
      get_mappings ys env = Some tys ->
      get_mappings (xs ++ ys) env = Some (txs ++ tys).
  Proof.
    induction xs as [|x xs IH]; intros ys env txs tys Hxs Hys.
    - simpl in Hxs. inversion Hxs; subst. exact Hys.
    - simpl in Hxs.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [txs'|] eqn:Htail; try discriminate.
      inversion Hxs; subst txs.
      simpl. rewrite Hfind.
      rewrite (IH ys env txs' tys Htail Hys).
      reflexivity.
  Qed.

  Lemma get_mappings_from_node_eq:
    forall A (xs: list (ident * A)) env tys,
      get_mappings_from_node xs env = Some tys ->
      get_mappings (map fst xs) env = Some tys.
  Proof.
    induction xs as [|(x, a) xs IH]; intros env tys Hmap; simpl in *.
    - inversion Hmap; reflexivity.
    - destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings_from_node xs env) as [tys'|] eqn:Htail; try discriminate.
      inversion Hmap; subst tys.
      simpl. rewrite (IH env tys' Htail). reflexivity.
  Qed.

  Lemma get_mappings_from_node_app:
    forall A (xs ys: list (ident * A)) env txs tys,
      get_mappings_from_node xs env = Some txs ->
      get_mappings_from_node ys env = Some tys ->
      get_mappings_from_node (xs ++ ys) env = Some (txs ++ tys).
  Proof.
    induction xs as [|(x, a) xs IH]; intros ys env txs tys Hxs Hys; simpl in *.
    - inversion Hxs; subst. exact Hys.
    - destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings_from_node xs env) as [txs'|] eqn:Htail; try discriminate.
      inversion Hxs; subst txs.
      simpl. rewrite (IH ys env txs' tys Htail Hys). reflexivity.
  Qed.

  Lemma get_mappings_in:
    forall xs env tys x,
      In x xs ->
      get_mappings xs env = Some tys ->
      exists ty, Env.find x env = Some ty /\ In ty tys.
  Proof.
    induction xs as [|y ys IH]; intros env tys x Hin Hmap.
    - inversion Hin.
    - simpl in Hmap.
      destruct (Env.find y env) as [yty|] eqn:Hyfind; try discriminate.
      destruct (get_mappings ys env) as [tys'|] eqn:Hys; try discriminate.
      inversion Hmap; subst tys.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst x. exists yty. split; [exact Hyfind|left; reflexivity].
      + edestruct IH as (ty & Hfind & Hin'); eauto.
        exists ty. split; [exact Hfind|right; exact Hin'].
  Qed.

  Lemma get_mappings_from_node_inmembers:
    forall A (xs: list (ident * A)) env tys x,
      InMembers x xs ->
      get_mappings_from_node xs env = Some tys ->
      exists ty, Env.find x env = Some ty /\ In ty tys.
  Proof.
    intros A xs env tys x Hin Hmap.
    apply fst_InMembers in Hin.
    eapply get_mappings_in; eauto.
    eapply get_mappings_from_node_eq; eauto.
  Qed.

  Lemma get_mappings_from_node_In:
    forall A (xs: list (ident * A)) env tys ty,
      get_mappings_from_node xs env = Some tys ->
      In ty tys ->
      exists x a, In (x, a) xs /\ Env.find x env = Some ty.
  Proof.
    induction xs as [|(x, a) xs IH]; intros env tys ty Hmap Hin.
    - simpl in Hmap. inversion Hmap; subst. inversion Hin.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hfind.
      2: discriminate.
      destruct (get_mappings_from_node xs env) as [tys'|] eqn:Hmaps.
      2: discriminate.
      inversion Hmap; subst tys.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst ty. exists x, a. split; [left; reflexivity|exact Hfind].
      + specialize (IH env tys' ty Hmaps Hin) as (x' & a' & Hin' & Hfind').
        exists x', a'. split; [right; exact Hin'|exact Hfind'].
  Qed.
End Env_helpers.

Module Type  NAMEGEN  (Import Ids   : IDS)
  (Import Op    : OPERATORS)

  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn).

 

  Section NameMonad.
  Context {A : Type}.

  (* The state only tracks the next fresh index. The shared environment itself
     is threaded explicitly through the generators below. *)
  Definition name_state : Type := ident.
  Definition Name A := name_state -> res (A * name_state).
  Definition init_state : name_state := xH.
  Definition initialize : ident -> name_state := fun xi  => xi.
  
  Definition NMret (x : A) : Name A := fun st =>  OK (x, st).
  
  Definition NMbind {B : Type} (x : Name A) (f : A -> Name B) : Name B :=
    fun st => match (x st) with
          | OK (a, st') => f a st'
          | Error err => Error err
          end.
  
  Definition NMbind2 {A1 A2 B : Type} (x : Name (A1 * A2)) (f : A1 -> A2 -> Name B) : Name B :=
    fun st => match (x st) with
          | OK ((a1, a2), st') => f a1 a2 st'
          | Error err => Error err      
          end.
   Definition error (msg : errmsg) : Name A :=
    fun st => Error msg.
  
  Definition fresh_ident_gen : Name ident :=
    fun n =>
      let id := Ids.gensym Ids.sec n in
      OK (id, Pos.succ n).
  
  Definition gets : Name name_state :=
    fun st =>  OK (st, st).

  Lemma name_bind_inv {B} : forall (x : Name A) (f : A -> Name B) res st,
      (NMbind x f) st = OK res ->
      exists y st'',
        x st = OK (y, st'') /\ f y st'' = OK res.
  Proof.
    intros * Hbind.
    unfold NMbind in Hbind.
    destruct (x st) as [[y st'']|]; eauto. inv Hbind.
  Qed.

  Lemma name_bind2_inv {A1 A2 B} : forall (x : Name (A1 * A2)) (f : A1 -> A2 -> Name B) res st,
      (NMbind2 x f) st = OK res ->
      exists y1 y2 st'',
        x st = OK ((y1, y2), st'') /\ f y1 y2 st'' = OK res.
  Proof.
    intros * Hbind.
    unfold NMbind2 in Hbind.
   destruct (x st) as [[[y1 y2] st'']|]; eauto. inv Hbind.
  Qed.

  End NameMonad.

  Module NAMEMONADNotations.
    Notation "'do' X <- A ; B" :=
      (NMbind A (fun X => B))
        (at level 200, X ident, A at level 100, B at level 200).
        
    Notation "'do' ( X , Y ) <- A ; B" :=
      (NMbind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200).
        
  End NAMEMONADNotations.
  Import NAMEMONADNotations.

  (* Extend the shared security-name environment with one new program-variable
     to security-variable mapping. *)
  Definition insert_env  (env: Env.t ident) (k v: ident): Name (Env.t ident) :=
    let st:= Env.add k v env in
      NMret st.

  Definition fresh_insert (env: Env.t ident) (k: ident) : Name (Env.t ident) :=
    if Env.mem k env then
     error (MSG "Key declared more than once ":: [CTX k])
    else
      do v <- fresh_ident_gen; 
      do e <- insert_env env k v;
      NMret e.
  
  Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Name B).

  Fixpoint mmap (l: list A) {struct l} : Name (list B) :=
    match l with
    | nil => NMret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; NMret (hd' :: tl')
    end.
  End mmap.
    
  
  Fixpoint fresh_map_list (ks: list ident) (env: Env.t ident): Name (Env.t ident) :=
    match ks with
    | nil => NMret env
    | k::ks' => (
      do e' <- fresh_insert env k;
      do e'' <- fresh_map_list ks' e';
      NMret e'')
    end.

  (* Allocate clock/reset auxiliaries first, then fresh security variables for
     the node interface and locals in one shared environment. *)
  Definition generate_new_names_for_node (n: node) (e: Env.t ident): Name (Env.t ident * node_aux_names):=
    do clk_name <- fresh_ident_gen;
    do rst_name <- fresh_ident_gen;
    do env' <- fresh_map_list ([clk_name; rst_name]  ++ (map fst  (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) e;
    NMret (env', {| nname:= n.(n_name) ; nclk := clk_name ; nrst := rst_name|}).

  Fixpoint generate_node_env' (ns: list node) (e: Env.t ident) (acc: list node_aux_names): Name (Env.t ident * list node_aux_names) :=
    match ns with
    | [] => NMret (e, acc)
    | n::ns' => 
      do (e',r) <- generate_new_names_for_node n e;
      do (e'', rs) <- generate_node_env' ns' e' (r::acc);
      NMret (e'', rs)
    end.

  (* Generate the shared environment and per-node auxiliary-name table for an
     entire NLustre global. *)
  Definition generate_node_env (ns: list node) : res (Env.t ident * list node_aux_names) :=
    match generate_node_env' ns (Env.empty _) [] init_state with
    | OK ((e, names), _) => OK (e,names)
    | Error e => Error e
    end.

End NAMEGEN.


Module Type  NameGen  (Ids   : IDS)
  (Op    : OPERATORS)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn) <: NAMEGEN Ids Op CESyn SynNL.

Include NAMEGEN Ids Op CESyn SynNL.

End NameGen.
