(** Shared generation of security identifiers and node-scoped naming environments. *)

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.

From Coq Require Import String.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.
From compcert Require Import common.Errors.

Open Scope list_scope.

(** The auxiliary names minted once per node and consumed by *every*
    downstream language.  [nclk] and [nrst] are the node's clock and
    reset security types; [ninst] maps each of the node's subsystem
    instances to its own security type.

    [ninst] lives here rather than in the per-language generators for
    the same reason [nclk]/[nrst] do: STC and Obc must agree on these
    names.  STC only ever looks up the instances it resets, Obc looks up
    all of them, so if each minted its own the two would disagree. *)

Record node_aux_names := mkNames {
    nname : ident;
    nclk: ident;
    nrst: ident;
    ninst: Env.t ident;
}.

Definition local_sec_env : Type := Env.t ident.
Definition node_scoped_env : Type := Env.t local_sec_env.

Definition find_node_env (n: ident) (envs: node_scoped_env) : option local_sec_env :=
  Env.find n envs.

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

Definition get_node_inst (n: ident) (nnames: list node_aux_names) : option (Env.t ident) :=
    let nsearch := find_node_names n nnames in
    match nsearch with
    | Some nod => Some nod.(ninst)
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

  Lemma get_mappings_Some_iff:
    forall xs env,
      (exists tys, get_mappings xs env = Some tys) <->
      Forall (fun x => exists ty, Env.find x env = Some ty) xs.
  Proof.
    induction xs as [|x xs IH]; intros env; split.
    - intros _. constructor.
    - intros _. exists []. reflexivity.
    - intros (tys & Hmap). simpl in Hmap.
      destruct (Env.find x env) as [ty|] eqn:Hx; simpl in Hmap; try discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Hxs; simpl in Hmap; try discriminate.
      constructor.
      + eauto.
      + apply IH. eauto.
    - intros Hall. inversion Hall as [|x' xs' Hx Hxs]; subst.
      destruct Hx as (ty & Hx).
      destruct (proj2 (IH env) Hxs) as (tys & Htys).
      exists (ty :: tys). simpl. rewrite Hx, Htys. reflexivity.
  Qed.

  Lemma get_mappings_Permutation_Some:
    forall xs ys env txs,
      Permutation xs ys ->
      get_mappings xs env = Some txs ->
      exists tys, get_mappings ys env = Some tys.
  Proof.
    intros xs ys env txs Hperm Hxs.
    apply get_mappings_Some_iff.
    rewrite <- Hperm.
    apply get_mappings_Some_iff. eauto.
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

  Lemma get_mappings_In:
    forall xs env tys ty,
      get_mappings xs env = Some tys ->
      In ty tys ->
      exists x, In x xs /\ Env.find x env = Some ty.
  Proof.
    induction xs as [|x xs IH]; intros env tys ty Hmap Hin.
    - simpl in Hmap. inversion Hmap; subst. inversion Hin.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hfind.
      2: discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Hmaps.
      2: discriminate.
      inversion Hmap; subst tys.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst ty. exists x. split; [left; reflexivity|exact Hfind].
      + specialize (IH env tys' ty Hmaps Hin) as (x' & Hin' & Hfind').
        exists x'. split; [right; exact Hin'|exact Hfind'].
  Qed.

  (** Under an injective environment, mapping a duplicate-free list of
      names yields a duplicate-free list of types, and permuting the
      names permutes the types.  (`SecNLusTyping`/`SecSTCTyping` each
      carry a section-scoped copy of the first of these; they should be
      collapsed onto this one in a cleanup pass.) *)

  Lemma get_mappings_nodup_gen:
    forall xs env tys,
      NoDup xs ->
      env_injective env ->
      get_mappings xs env = Some tys ->
      NoDup tys.
  Proof.
    induction xs as [|x xs IH]; intros env tys Hnd Hinj Hmap.
    - simpl in Hmap. inversion Hmap. constructor.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hmap; try discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Hxs; simpl in Hmap; try discriminate.
      inversion Hmap; subst tys.
      inversion Hnd as [|? ? Hnin Hnd']; subst.
      constructor.
      + intro Hin.
        destruct (get_mappings_In _ _ _ _ Hxs Hin) as (y & Hiny & Hy).
        assert (x = y) by (eapply Hinj; eauto).
        subst y. contradiction.
      + eapply IH; eauto.
  Qed.

  Lemma get_mappings_perm:
    forall xs ys env txs tys,
      NoDup xs ->
      Permutation xs ys ->
      env_injective env ->
      get_mappings xs env = Some txs ->
      get_mappings ys env = Some tys ->
      Permutation txs tys.
  Proof.
    intros xs ys env txs tys Hnd Hperm Hinj Hxs Hys.
    assert (NoDup ys) as Hndy by (eapply Permutation_NoDup; eauto).
    apply NoDup_Permutation.
    - exact (get_mappings_nodup_gen xs env txs Hnd Hinj Hxs).
    - exact (get_mappings_nodup_gen ys env tys Hndy Hinj Hys).
    - intros ty; split; intro Hin.
      + destruct (get_mappings_In _ _ _ _ Hxs Hin) as (x & Hinx & Hx).
        assert (In x ys) by (rewrite <- Hperm; exact Hinx).
        destruct (get_mappings_in _ _ _ _ H Hys) as (ty' & Hy & Hinty).
        rewrite Hx in Hy. inversion Hy; subst. exact Hinty.
      + destruct (get_mappings_In _ _ _ _ Hys Hin) as (y & Hiny & Hy).
        assert (In y xs) by (rewrite Hperm; exact Hiny).
        destruct (get_mappings_in _ _ _ _ H Hxs) as (ty' & Hx & Hintx).
        rewrite Hy in Hx. inversion Hx; subst. exact Hintx.
  Qed.

  (** [get_mappings] succeeds exactly when every name is bound, so
      success transports along a permutation of the name list. *)

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

  (** Instance names carry the [sec_reset] prefix so that they never
      collide with the [sec] names of program variables: an instance is
      identified by one of the variables its call defines. *)

  Definition fresh_inst_ident_gen : Name ident :=
    fun n =>
      let id := Ids.gensym Ids.sec_reset n in
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

  Definition fresh_inst_insert (env: Env.t ident) (k: ident) : Name (Env.t ident) :=
    if Env.mem k env then
     error (MSG "Instance declared more than once ":: [CTX k])
    else
      do v <- fresh_inst_ident_gen;
      do e <- insert_env env k v;
      NMret e.

  Fixpoint fresh_inst_map_list (ks: list ident) (env: Env.t ident): Name (Env.t ident) :=
    match ks with
    | nil => NMret env
    | k::ks' => (
      do e' <- fresh_inst_insert env k;
      do e'' <- fresh_inst_map_list ks' e';
      NMret e'')
    end.

  Definition insert_node_env
    (envs: node_scoped_env) (name: ident) (local_env: local_sec_env)
    : Name node_scoped_env :=
    NMret (Env.add name local_env envs).

  Definition fresh_insert_node_env
    (envs: node_scoped_env) (name: ident) (local_env: local_sec_env)
    : Name node_scoped_env :=
    if Env.mem name envs then
      error (MSG "Node name declared more than once ":: [CTX name])
    else
      insert_node_env envs name local_env.

  Definition generate_local_env_for_node (n: node) : Name (local_sec_env * node_aux_names) :=
    do clk_name <- fresh_ident_gen;
    do rst_name <- fresh_ident_gen;
    do env' <- fresh_map_list
                 ([clk_name; rst_name]
                    ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
                 (Env.empty _);
    do inst_env <- fresh_inst_map_list
                     (map fst (gather_insts n.(n_eqs))) (Env.empty _);
    NMret (env', {| nname := n.(n_name); nclk := clk_name; nrst := rst_name;
                    ninst := inst_env |}).

  Fixpoint generate_node_scoped_env'
    (ns: list node) (envs: node_scoped_env) (acc: list node_aux_names)
    : Name (node_scoped_env * list node_aux_names) :=
    match ns with
    | [] => NMret (envs, acc)
    | n :: ns' =>
        do (local_env, r) <- generate_local_env_for_node n;
        do envs' <- fresh_insert_node_env envs n.(n_name) local_env;
        do (envs'', rs) <- generate_node_scoped_env' ns' envs' (r :: acc);
        NMret (envs'', rs)
    end.

  Definition generate_node_scoped_env (ns: list node)
    : res (node_scoped_env * list node_aux_names) :=
    match generate_node_scoped_env' ns (Env.empty _) [] init_state with
    | OK ((envs, names), _) => OK (envs, names)
    | Error e => Error e
    end.

  Lemma generate_node_scoped_env'_app_inv:
    forall ns1 ns2 envs acc st envs' aux st',
      generate_node_scoped_env' (ns1 ++ ns2) envs acc st = OK ((envs', aux), st') ->
      exists envs_mid aux_mid st_mid,
        generate_node_scoped_env' ns1 envs acc st = OK ((envs_mid, aux_mid), st_mid)
        /\ generate_node_scoped_env' ns2 envs_mid aux_mid st_mid = OK ((envs', aux), st').
  Proof.
    induction ns1 as [|n ns1 IH]; intros ns2 envs acc st envs' aux st' Hgen.
    - simpl in Hgen.
      exists envs, acc, st.
      split; [reflexivity|exact Hgen].
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hstep & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      edestruct IH as (envs_mid & aux_mid & st_mid & Hpref & Hsuf); eauto.
      exists envs_mid, aux_mid, st_mid.
      split.
      + simpl.
        unfold NMbind2.
        rewrite Hstep.
        simpl.
        unfold NMbind.
        rewrite Hins.
        simpl.
        rewrite Hpref.
        reflexivity.
      + exact Hsuf.
  Qed.

  Lemma generate_node_scoped_env'_app:
    forall ns1 ns2 envs acc st
           envs_mid aux_mid st_mid envs' aux st',
      generate_node_scoped_env' ns1 envs acc st = OK ((envs_mid, aux_mid), st_mid) ->
      generate_node_scoped_env' ns2 envs_mid aux_mid st_mid = OK ((envs', aux), st') ->
      generate_node_scoped_env' (ns1 ++ ns2) envs acc st = OK ((envs', aux), st').
  Proof.
    induction ns1 as [|n ns1 IH];
      intros ns2 envs acc st envs_mid aux_mid st_mid envs' aux st'
             Hpref Hsuf.
    - simpl in Hpref. inversion Hpref; subst. exact Hsuf.
    - simpl in Hpref.
      eapply name_bind2_inv in Hpref as (local_env & rec & st1 & Hstep & Hpref).
      eapply name_bind_inv in Hpref as (envs1 & stins & Hins & Hpref).
      eapply name_bind2_inv in Hpref as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs_mid aux_mid st_mid.
      simpl.
      unfold NMbind2.
      rewrite Hstep.
      simpl.
      unfold NMbind.
      rewrite Hins.
      simpl.
      rewrite (IH _ _ _ _ _ _ _ _ _ _ Hrec Hsuf).
      reflexivity.
  Qed.

  Lemma generate_node_scoped_env'_split_node:
    forall prefix n suffix envs acc st envs' aux st',
      generate_node_scoped_env' (prefix ++ n :: suffix) envs acc st = OK ((envs', aux), st') ->
      exists envs_pref aux_pref st_pref local_env rec st_local envs_cur st_cur,
        generate_node_scoped_env' prefix envs acc st = OK ((envs_pref, aux_pref), st_pref)
        /\ generate_local_env_for_node n st_pref = OK ((local_env, rec), st_local)
        /\ fresh_insert_node_env envs_pref n.(n_name) local_env st_local = OK (envs_cur, st_cur)
        /\ generate_node_scoped_env' suffix envs_cur (rec :: aux_pref) st_cur = OK ((envs', aux), st').
  Proof.
    intros prefix n suffix envs acc st envs' aux st' Hgen.
    eapply generate_node_scoped_env'_app_inv in Hgen
      as (envs_pref & aux_pref & st_pref & Hpref & Hrest).
    simpl in Hrest.
    eapply name_bind2_inv in Hrest as (local_env & rec & st_local & Hlocal & Hrest).
    eapply name_bind_inv in Hrest as (envs_cur & st_cur & Hins & Hrest).
    eapply name_bind2_inv in Hrest as (envs_end & aux_end & st_end & Htail & Hret).
    unfold NMret in Hret. inversion Hret; subst envs' aux st'.
    exists envs_pref, aux_pref, st_pref, local_env, rec, st_local, envs_cur, st_cur.
    repeat split; auto.
  Qed.

  Definition generate_new_names_for_node (n: node) (e: Env.t ident): Name (Env.t ident * node_aux_names):=
    do clk_name <- fresh_ident_gen;
    do rst_name <- fresh_ident_gen;
    do env' <- fresh_map_list ([clk_name; rst_name]  ++ (map fst  (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))) e;
    do inst_env <- fresh_inst_map_list
                     (map fst (gather_insts n.(n_eqs))) (Env.empty _);
    NMret (env', {| nname:= n.(n_name) ; nclk := clk_name ; nrst := rst_name;
                    ninst := inst_env |}).

  Fixpoint generate_node_env' (ns: list node) (e: Env.t ident) (acc: list node_aux_names): Name (Env.t ident * list node_aux_names) :=
    match ns with
    | [] => NMret (e, acc)
    | n::ns' =>
      do (e',r) <- generate_new_names_for_node n e;
      do (e'', rs) <- generate_node_env' ns' e' (r::acc);
      NMret (e'', rs)
    end.

  Lemma generate_node_env'_app_inv:
    forall ns1 ns2 env acc st env' aux st',
      generate_node_env' (ns1 ++ ns2) env acc st = OK ((env', aux), st') ->
      exists env_mid aux_mid st_mid,
        generate_node_env' ns1 env acc st = OK ((env_mid, aux_mid), st_mid)
        /\ generate_node_env' ns2 env_mid aux_mid st_mid = OK ((env', aux), st').
  Proof.
    induction ns1 as [|n ns1 IH]; intros ns2 env acc st env' aux st' Hgen.
    - simpl in Hgen.
      exists env, acc, st.
      split; [reflexivity|exact Hgen].
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (env1 & rec1 & st1 & Hstep & Hgen).
      eapply name_bind2_inv in Hgen as (env2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' aux st'.
      edestruct IH as (env_mid & aux_mid & st_mid & Hpref & Hsuf); eauto.
      exists env_mid, aux_mid, st_mid.
      split.
      + simpl.
        unfold NMbind2.
        rewrite Hstep.
        simpl.
        rewrite Hpref.
        reflexivity.
      + exact Hsuf.
  Qed.

  Lemma generate_node_env'_split_node:
    forall prefix n suffix env acc st env' aux st',
      generate_node_env' (prefix ++ n :: suffix) env acc st = OK ((env', aux), st') ->
      exists env_pref aux_pref st_pref env_cur rec st_cur,
        generate_node_env' prefix env acc st = OK ((env_pref, aux_pref), st_pref)
        /\ generate_new_names_for_node n env_pref st_pref = OK ((env_cur, rec), st_cur)
        /\ generate_node_env' suffix env_cur (rec :: aux_pref) st_cur = OK ((env', aux), st').
  Proof.
    intros prefix n suffix env acc st env' aux st' Hgen.
    eapply generate_node_env'_app_inv in Hgen
      as (env_pref & aux_pref & st_pref & Hpref & Hrest).
    simpl in Hrest.
    eapply name_bind2_inv in Hrest as (env_cur & rec & st_cur & Hstep & Hrest).
    eapply name_bind2_inv in Hrest as (env_end & aux_end & st_end & Htail & Hret).
    unfold NMret in Hret. inversion Hret; subst env' aux st'.
    exists env_pref, aux_pref, st_pref, env_cur, rec, st_cur.
    repeat split; auto.
  Qed.

  Lemma fresh_insert_preserves_find:
    forall env k st env' st' x ty,
      fresh_insert env k st = OK (env', st') ->
      Env.find x env = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    intros env k st env' st' x ty Hins Hfind.
    unfold fresh_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply name_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_ident_gen in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, NMret in Hins0. inversion Hins0; subst e st2.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    assert (Hxk : x <> k).
    { intro Heq. subst x.
      assert (Env.mem k env = true).
      { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
      congruence. }
    now rewrite Env.gso.
  Qed.

  Lemma fresh_map_list_preserves_find:
    forall ks env st env' st' x ty,
      fresh_map_list ks env st = OK (env', st') ->
      Env.find x env = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' x ty Hmap Hfind.
    - simpl in Hmap. inversion Hmap; subst. exact Hfind.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hrec).
      eapply name_bind_inv in Hrec as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      eapply IH; eauto.
      eapply fresh_insert_preserves_find; eauto.
  Qed.

  Lemma fresh_inst_insert_preserves_find:
    forall env k st env' st' x ty,
      fresh_inst_insert env k st = OK (env', st') ->
      Env.find x env = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    intros env k st env' st' x ty Hstep Hfind.
    unfold fresh_inst_insert in Hstep.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
    eapply name_bind_inv in Hstep as (e & ste & Hins & Hret).
    unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v stv.
    unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    destruct (ident_eq_dec x k) as [Heq|Hneq].
    - subst x.
      assert (Env.mem k env = true)
        by (apply Env.mem_1; unfold Env.In; eexists; exact Hfind).
      congruence.
    - now rewrite Env.gso by auto.
  Qed.

  Lemma fresh_inst_map_list_preserves_find:
    forall ks env st env' st' x ty,
      fresh_inst_map_list ks env st = OK (env', st') ->
      Env.find x env = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' x ty Hmap Hfind.
    - simpl in Hmap. inversion Hmap; subst. exact Hfind.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hrec).
      eapply name_bind_inv in Hrec as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      eapply IH; eauto.
      eapply fresh_inst_insert_preserves_find; eauto.
  Qed.

  Lemma fresh_insert_node_env_preserves_find:
    forall envs name local_env st envs' st' x env,
      fresh_insert_node_env envs name local_env st = OK (envs', st') ->
      find_node_env x envs = Some env ->
      find_node_env x envs' = Some env.
  Proof.
    intros envs name local_env st envs' st' x env Hins Hfind.
    unfold fresh_insert_node_env in Hins.
    destruct (Env.mem name envs) eqn:Hmem; try discriminate.
    unfold insert_node_env, NMret in Hins. inversion Hins; subst envs' st'.
    assert (Hxname : x <> name).
    { intro Heq. subst x.
      assert (Env.mem name envs = true).
      { apply Env.mem_1. unfold Env.In. eexists. exact Hfind. }
      congruence. }
    unfold find_node_env in *.
    now rewrite Env.gso.
  Qed.

  Lemma fresh_insert_node_env_finds_new:
    forall envs name local_env st envs' st',
      fresh_insert_node_env envs name local_env st = OK (envs', st') ->
      find_node_env name envs' = Some local_env.
  Proof.
    intros envs name local_env st envs' st' Hins.
    unfold fresh_insert_node_env in Hins.
    destruct (Env.mem name envs) eqn:Hmem; try discriminate.
    unfold insert_node_env, NMret in Hins. inversion Hins; subst envs' st'.
    unfold find_node_env. now rewrite Env.gss.
  Qed.

  Lemma generate_node_scoped_env'_preserves_find:
    forall ns envs acc st envs' aux st' x env,
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      find_node_env x envs = Some env ->
      find_node_env x envs' = Some env.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' x env Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Hfind.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      eapply IH; eauto.
      eapply fresh_insert_node_env_preserves_find; eauto.
  Qed.

  Lemma generate_node_scoped_env'_preserves_get_node_aux:
    forall ns envs acc st envs' aux st'
           name clk_id rst_id local_env,
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      get_node_aux name acc = Some (clk_id, rst_id) ->
      find_node_env name envs = Some local_env ->
      get_node_aux name aux = Some (clk_id, rst_id).
  Proof.
    induction ns as [|n ns IH];
      intros envs acc st envs' aux st' name clk_id rst_id local_env
             Hgen Haux Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Haux.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env' & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      assert (Hneq : name <> n.(n_name)).
      {
        intro Heq.
        subst name.
        unfold fresh_insert_node_env in Hins.
        assert (Env.mem (n_name n) envs = true).
        {
          apply Env.mem_1.
          unfold Env.In, find_node_env in Hfind.
          eexists; exact Hfind.
        }
        rewrite H in Hins.
        discriminate.
      }
      assert (Haux' : get_node_aux name (rec :: acc) = Some (clk_id, rst_id)).
      {
        unfold get_node_aux in *.
        simpl.
        destruct (ident_eqb name rec.(nname)) eqn:Hname.
        - apply ident_eqb_eq in Hname. subst name.
          unfold generate_local_env_for_node in Hlocal.
          eapply name_bind_inv in Hlocal as (clk_name & stc & Hclkgen & Hlocal).
          eapply name_bind_inv in Hlocal as (rst_name & str & Hrstgen & Hlocal).
          eapply name_bind_inv in Hlocal as (env0 & ste & Henvgen & Hlocal).
          eapply name_bind_inv in Hlocal as (inst_env0 & stei & Hinstgen & Hret0).
          unfold NMret in Hret0. inversion Hret0; subst rec st1 local_env'.
          contradiction.
        - exact Haux.
      }
      assert (Hfind' : find_node_env name envs1 = Some local_env).
      {
        eapply fresh_insert_node_env_preserves_find; eauto.
      }
      eapply IH; eauto.
  Qed.

  Lemma generate_node_scoped_env'_preserves_get_node_inst:
    forall ns envs acc st envs' aux st' name ie local_env,
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      get_node_inst name acc = Some ie ->
      find_node_env name envs = Some local_env ->
      get_node_inst name aux = Some ie.
  Proof.
    induction ns as [|n ns IH];
      intros envs acc st envs' aux st' name ie local_env Hgen Hinst Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Hinst.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env' & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      assert (Hneq : name <> n.(n_name)).
      {
        intro Heq. subst name.
        unfold fresh_insert_node_env in Hins.
        assert (Env.mem (n_name n) envs = true).
        { apply Env.mem_1. unfold Env.In, find_node_env in Hfind.
          eexists; exact Hfind. }
        rewrite H in Hins. discriminate.
      }
      assert (Hinst' : get_node_inst name (rec :: acc) = Some ie).
      {
        unfold get_node_inst in *. simpl.
        destruct (ident_eqb name rec.(nname)) eqn:Hname.
        - apply ident_eqb_eq in Hname. subst name.
          unfold generate_local_env_for_node in Hlocal.
          eapply name_bind_inv in Hlocal as (clk_name & stc & Hclkgen & Hlocal).
          eapply name_bind_inv in Hlocal as (rst_name & str & Hrstgen & Hlocal).
          eapply name_bind_inv in Hlocal as (env0 & ste & Henvgen & Hlocal).
          eapply name_bind_inv in Hlocal as (inst_env0 & stei & Hinstgen & Hret0).
          unfold NMret in Hret0. inversion Hret0; subst rec st1 local_env'.
          contradiction.
        - exact Hinst.
      }
      assert (Hfind' : find_node_env name envs1 = Some local_env).
      { eapply fresh_insert_node_env_preserves_find; eauto. }
      eapply IH; eauto.
  Qed.

  Lemma generate_node_scoped_env_find_current:
    forall prefix n suffix envs aux,
      generate_node_scoped_env (prefix ++ n :: suffix) = OK (envs, aux) ->
      exists local_env rec st_pref st_local,
        generate_local_env_for_node n st_pref = OK ((local_env, rec), st_local)
        /\ find_node_env n.(n_name) envs = Some local_env.
  Proof.
    intros prefix n suffix envs aux Hgen.
    unfold generate_node_scoped_env in Hgen.
    destruct (generate_node_scoped_env' (prefix ++ n :: suffix) (Env.empty _) [] init_state)
      as [[[envs' aux'] st']|] eqn:Hrun; try discriminate.
    inversion Hgen; subst envs aux.
    eapply generate_node_scoped_env'_split_node in Hrun
      as (envs_pref & aux_pref & st_pref & local_env & rec & st_local
          & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail).
    exists local_env, rec, st_pref, st_local.
    split; [exact Hlocal|].
    eapply generate_node_scoped_env'_preserves_find; eauto.
    eapply fresh_insert_node_env_finds_new; eauto.
  Qed.

  Lemma fresh_map_list_keys_fresh_from_initial:
    forall ks env st env' st' k,
      fresh_map_list ks env st = OK (env', st') ->
      In k ks ->
      ~ Env.In k env.
  Proof.
    induction ks as [|k0 ks IH]; intros env st env' st' k Hmap Hin.
    - inversion Hin.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst k.
        intro Hink.
        unfold fresh_insert in Hstep.
        apply Env.mem_1 in Hink.
        rewrite Hink in Hstep.
        discriminate.
      + intro Hink.
        eapply (IH env1 st1 env2 st2 k Hrec Hin).
        unfold Env.In.
        destruct Hink as (ty & Hfind).
        exists ty.
        eapply fresh_insert_preserves_find; eauto.
  Qed.

  (** The allocation list is interface-first -- clock, reset, inputs, outputs,
      and only then locals -- so that the security name given to an interface
      variable does not depend on how many locals the node happens to have.
      That is what lets two nodes with the same interface receive the same
      interface names even when one has extra locals, which is exactly the
      situation normalisation creates.

      Statements elsewhere quote a node's variables in the
      [n_in ++ n_vars ++ n_out] order, because that is the order [n_nodup] and
      [wc_node] use.  Membership, freshness and duplicate-freedom are all
      permutation-invariant, so the two spellings are interchangeable and this
      lemma is the bridge. *)

  Lemma node_keys_perm : forall (n : node),
      Permutation (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  (map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))).
  Proof.
    intro n. rewrite !map_app.
    apply Permutation_app_head, Permutation_app_comm.
  Qed.

  Lemma in_node_keys_perm : forall (n : node) k,
      In k (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      In k (map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))).
  Proof.
    intros n k. apply Permutation_in, node_keys_perm.
  Qed.

  Lemma generate_new_names_for_node_keys_fresh_from_initial:
    forall n env st env' aux st' k,
      generate_new_names_for_node n env st = OK ((env', aux), st') ->
      In k (aux.(nclk) :: aux.(nrst) :: map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      ~ Env.In k env.
  Proof.
    intros n env st env' aux st' k Hgen Hin.
    unfold generate_new_names_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env' aux st'.
    eapply fresh_map_list_keys_fresh_from_initial; eauto.
    simpl in Hin |- *.
    destruct Hin as [Hk|[Hk|Hk]]; auto.
    right; right. now apply in_node_keys_perm.
  Qed.

  Definition generate_node_env (ns: list node) : res (Env.t ident * list node_aux_names) :=
    match generate_node_env' ns (Env.empty _) [] init_state with
    | OK ((e, names), _) => OK (e,names)
    | Error e => Error e
    end.

  Definition env_sec_bounded (st: ident) (env: Env.t ident) : Prop :=
    forall x ty,
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive.

  Definition node_scoped_env_sec_bounded (st: ident) (envs: node_scoped_env) : Prop :=
    forall name local_env x ty,
      find_node_env name envs = Some local_env ->
      Env.find x local_env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive.

  Definition aux_sec_names (aux: list node_aux_names) : Prop :=
    forall rec,
      In rec aux ->
      exists i j,
        rec.(nclk) = Ids.gensym Ids.sec i
        /\ rec.(nrst) = Ids.gensym Ids.sec j.

  Lemma env_sec_bounded_step:
    forall st env,
      env_sec_bounded st env ->
      env_sec_bounded (Pos.succ st) env.
  Proof.
    intros st env Hbound x ty Hfind.
    specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
    exists n. split; auto.
    eapply Pos.lt_trans; eauto.
    apply Pos.lt_succ_diag_r.
  Qed.



  Lemma env_values_fresh_notin:
    forall env st,
      env_sec_bounded st env ->
      ~ InMembers (Ids.gensym Ids.sec st) (env_values env).
  Proof.
    intros env st Hbound Hin.
    apply InMembers_In in Hin as (x & Hin).
    unfold env_values in Hin.
    apply in_map_iff in Hin as ((x', ty') & Heq & Hele).
    simpl in Heq. inversion Heq; subst x' ty'. clear Heq.
    apply Env.elements_complete in Hele.
    specialize (Hbound _ _ Hele) as (n & Hgen & Hlt).
    apply gensym_injective in Hgen as [_ Hn]. subst n.
    now apply Pos.lt_irrefl in Hlt.
  Qed.

  Lemma fresh_insert_env_props:
    forall env k st env' st',
      env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      fresh_insert env k st = OK (env', st') ->
      env_sec_bounded st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    intros env k st env' st' Hbound Hnodup Hgen.
    unfold fresh_insert in Hgen.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
    eapply name_bind_inv in Hgen as (e & st2 & Hins & Hret).
    unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v st1.
    unfold insert_env, NMret in Hins. inversion Hins; subst e st2.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    split.
    - intros x ty Hfind.
      destruct (ident_eq_dec x k) as [Heq|Hneq].
      + subst x. rewrite Env.gss in Hfind. inversion Hfind; subst ty.
        exists st. split; [reflexivity|apply Pos.lt_succ_diag_r].
      + rewrite Env.gso in Hfind by auto.
        specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
        exists n. split; auto.
        eapply Pos.lt_trans; eauto.
        apply Pos.lt_succ_diag_r.
    - assert (Hnotin : ~ Env.In k env).
      { intro Hin. apply Env.mem_1 in Hin. rewrite Hmem in Hin. discriminate. }
      eapply (NoDupMembers_Permutation_Proper
                (env_values (Env.add k (Ids.gensym Ids.sec st) env))
                ((Ids.gensym Ids.sec st, k) :: env_values env)).
      + apply env_values_add; exact Hnotin.
      + constructor.
        * apply env_values_fresh_notin; exact Hbound.
        * exact Hnodup.
  Qed.

  Lemma fresh_map_list_env_props:
    forall ks env st env' st',
      env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      fresh_map_list ks env st = OK (env', st') ->
      env_sec_bounded st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hbound Hnodup Hgen.
    - simpl in Hgen. inversion Hgen; subst. auto.
    - simpl in Hgen.
      eapply name_bind_inv in Hgen as (env1 & st1 & Hstep & Hgen).
      eapply name_bind_inv in Hgen as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      destruct (fresh_insert_env_props _ _ _ _ _ Hbound Hnodup Hstep) as [Hbound1 Hnodup1].
      eapply IH; eauto.
  Qed.

  (** Properties of a freshly built instance environment: its values are
      [sec_reset] gensyms drawn from the state interval it consumed, it
      binds exactly the keys it was given, and distinct keys get distinct
      values. *)

  Definition env_reset_bounded_gen (st: ident) (env: Env.t ident) : Prop :=
    forall x ty,
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n /\ (n < st)%positive.

  Lemma env_values_fresh_notin_reset:
    forall env st,
      env_reset_bounded_gen st env ->
      ~ InMembers (Ids.gensym Ids.sec_reset st) (env_values env).
  Proof.
    intros env st Hbound Hin.
    apply InMembers_In in Hin as (x & Hin).
    unfold env_values in Hin.
    apply in_map_iff in Hin as ((x', ty') & Heq & Hele).
    simpl in Heq. inversion Heq; subst x' ty'. clear Heq.
    apply Env.elements_complete in Hele.
    specialize (Hbound _ _ Hele) as (n & Hgen & Hlt).
    apply gensym_injective in Hgen as [_ Hn]. subst n.
    now apply Pos.lt_irrefl in Hlt.
  Qed.

  Lemma fresh_inst_insert_env_props:
    forall env k st env' st',
      env_reset_bounded_gen st env ->
      NoDupMembers (env_values env) ->
      fresh_inst_insert env k st = OK (env', st') ->
      env_reset_bounded_gen st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    intros env k st env' st' Hbound Hnodup Hgen.
    unfold fresh_inst_insert in Hgen.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
    eapply name_bind_inv in Hgen as (e & st2 & Hins & Hret).
    unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v st1.
    unfold insert_env, NMret in Hins. inversion Hins; subst e st2.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    split.
    - intros x ty Hfind.
      destruct (ident_eq_dec x k) as [Heq|Hneq].
      + subst x. rewrite Env.gss in Hfind. inversion Hfind; subst ty.
        exists st. split; [reflexivity|apply Pos.lt_succ_diag_r].
      + rewrite Env.gso in Hfind by auto.
        specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
        exists n. split; auto.
        eapply Pos.lt_trans; eauto.
        apply Pos.lt_succ_diag_r.
    - assert (Hnotin : ~ Env.In k env).
      { intro Hin. apply Env.mem_1 in Hin. rewrite Hmem in Hin. discriminate. }
      eapply (NoDupMembers_Permutation_Proper
                (env_values (Env.add k (Ids.gensym Ids.sec_reset st) env))
                ((Ids.gensym Ids.sec_reset st, k) :: env_values env)).
      + apply env_values_add; exact Hnotin.
      + constructor.
        * apply env_values_fresh_notin_reset; exact Hbound.
        * exact Hnodup.
  Qed.

  Lemma fresh_inst_map_list_env_props:
    forall ks env st env' st',
      env_reset_bounded_gen st env ->
      NoDupMembers (env_values env) ->
      fresh_inst_map_list ks env st = OK (env', st') ->
      env_reset_bounded_gen st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hbound Hnodup Hgen.
    - simpl in Hgen. inversion Hgen; subst. auto.
    - simpl in Hgen.
      eapply name_bind_inv in Hgen as (env1 & st1 & Hstep & Hgen).
      eapply name_bind_inv in Hgen as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      destruct (fresh_inst_insert_env_props _ _ _ _ _ Hbound Hnodup Hstep)
        as [Hbound1 Hnodup1].
      eapply IH; eauto.
  Qed.

  (** An instance environment built from empty is injective and
      [sec_reset]-ranged. *)

  Lemma fresh_inst_map_list_from_empty_props:
    forall ks st ie st',
      fresh_inst_map_list ks (Env.empty _) st = OK (ie, st') ->
      env_injective ie
      /\ (forall x ty, Env.find x ie = Some ty ->
                       exists m, ty = Ids.gensym Ids.sec_reset m).
  Proof.
    intros ks st ie st' Hgen.
    destruct (fresh_inst_map_list_env_props ks (Env.empty _) st ie st')
      as [Hbound Hnodup].
    - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
    - constructor.
    - exact Hgen.
    - split.
      + eapply env_values_nodup_injective; eauto.
      + intros x ty Hfind.
        destruct (Hbound _ _ Hfind) as (m & Hm & _). eauto.
  Qed.

  Lemma fresh_inst_map_list_range:
    forall ks env st env' st',
      (forall x ty, Env.find x env = Some ty ->
                    exists n, ty = Ids.gensym Ids.sec_reset n) ->
      fresh_inst_map_list ks env st = OK (env', st') ->
      forall x ty, Env.find x env' = Some ty ->
                   exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Henv Hmap x ty Hfind.
    - simpl in Hmap. inversion Hmap; subst. eauto.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      eapply IH; [|exact Hrec|exact Hfind].
      intros y tz Hy.
      unfold fresh_inst_insert in Hstep.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
      eapply name_bind_inv in Hstep as (e & ste & Hins & Hret').
      unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v stv.
      unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
      unfold NMret in Hret'. inversion Hret'; subst env1 st1.
      destruct (ident_eq_dec y k) as [Heq|Hneq].
      + subst y. rewrite Env.gss in Hy. inversion Hy. eauto.
      + rewrite Env.gso in Hy by auto. eauto.
  Qed.

  Lemma fresh_inst_map_list_binds:
    forall ks env st env' st',
      fresh_inst_map_list ks env st = OK (env', st') ->
      forall x, In x ks -> exists ty, Env.find x env' = Some ty.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hmap x Hin.
    - inversion Hin.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      destruct Hin as [Heq|Hin].
      + subst x.
        unfold fresh_inst_insert in Hstep.
        destruct (Env.mem k env) eqn:Hmem; try discriminate.
        eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
        eapply name_bind_inv in Hstep as (e & ste & Hins & Hret').
        unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v stv.
        unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
        unfold NMret in Hret'. inversion Hret'; subst env1 st1.
        exists (Ids.gensym Ids.sec_reset st).
        eapply fresh_inst_map_list_preserves_find; [exact Hrec|].
        now rewrite Env.gss.
      + eapply IH; eauto.
  Qed.

  Lemma env_sec_bounded_le:
    forall st st' env,
      env_sec_bounded st env ->
      (st <= st')%positive ->
      env_sec_bounded st' env.
  Proof.
    intros st st' env Hbound Hle x ty Hfind.
    destruct (Hbound x ty Hfind) as (n & Hn & Hlt).
    exists n. split; [exact Hn|].
    eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma fresh_inst_map_list_state_monotone:
    forall ks env st env' st',
      fresh_inst_map_list ks env st = OK (env', st') ->
      (st <= st')%positive.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hmap.
    - simpl in Hmap. inversion Hmap; subst. reflexivity.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      unfold fresh_inst_insert in Hstep.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
      eapply name_bind_inv in Hstep as (e & ste & Hins & Hret').
      unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v stv.
      unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
      unfold NMret in Hret'. inversion Hret'; subst env1 st1.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply IH; eauto.
  Qed.

  Lemma fresh_map_list_state_monotone:
    forall ks env st env' st',
      fresh_map_list ks env st = OK (env', st') ->
      (st <= st')%positive.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hmap.
    - simpl in Hmap. inversion Hmap; subst. reflexivity.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      unfold fresh_insert in Hstep.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
      eapply name_bind_inv in Hstep as (e & ste & Hins & Hret').
      unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v stv.
      unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
      unfold NMret in Hret'. inversion Hret'; subst env1 st1.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply IH; eauto.
  Qed.

  Lemma fresh_map_list_find_old_or_ge_start:
    forall ks env st env' st' x ty,
      fresh_map_list ks env st = OK (env', st') ->
      Env.find x env' = Some ty ->
      (Env.find x env = Some ty)
      \/ exists n, ty = Ids.gensym Ids.sec n /\ (st <= n < st')%positive.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' x ty Hmap Hfind.
    - simpl in Hmap. inversion Hmap; subst. now left.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      unfold fresh_insert in Hstep.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
      eapply name_bind_inv in Hstep as (e & ste & Hins & Hret').
      unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v stv.
      unfold insert_env, NMret in Hins. inversion Hins; subst e ste.
      unfold NMret in Hret'. inversion Hret'; subst env1 st1.
      specialize (IH _ _ _ _ _ _ Hrec Hfind) as [Hold|Hnew].
      +
        destruct (ident_eq_dec x k) as [Heq|Hneq].
        * subst x. rewrite Env.gss in Hold. inversion Hold; subst ty.
          assert (Hmono : (Pos.succ st <= st2)%positive).
          { eapply fresh_map_list_state_monotone; eauto. }
          right. exists st. split; [reflexivity|].
          split; [reflexivity|].
          eapply Pos.lt_le_trans; [apply Pos.lt_succ_diag_r|exact Hmono].
        * rewrite Env.gso in Hold by exact Hneq.
          now left.
      + right.
        destruct Hnew as (n & Hty & [Hlo Hhi]).
        exists n. split; [exact Hty|].
        split; [eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo]|exact Hhi].
  Qed.

  Lemma fresh_map_list_find_ge_start_from_empty:
    forall ks st env' st' x ty,
      fresh_map_list ks (Env.empty _) st = OK (env', st') ->
      Env.find x env' = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n /\ (st <= n < st')%positive.
  Proof.
    intros ks st env' st' x ty Hmap Hfind.
    destruct (fresh_map_list_find_old_or_ge_start _ _ _ _ _ _ _ Hmap Hfind)
      as [Hold|Hnew].
    - rewrite Env.gempty in Hold. discriminate.
    - exact Hnew.
  Qed.

  Lemma generate_new_names_for_node_env_props:
    forall n env st env' aux st',
      env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      generate_new_names_for_node n env st = OK ((env', aux), st') ->
      env_sec_bounded st' env'
      /\ NoDupMembers (env_values env')
      /\ exists i j,
          aux.(nclk) = Ids.gensym Ids.sec i
          /\ aux.(nrst) = Ids.gensym Ids.sec j.
  Proof.
    intros n env st env' aux st' Hbound Hnodup Hgen.
    unfold generate_new_names_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env' aux st'.
    destruct (fresh_map_list_env_props _ _ _ _ _
                (env_sec_bounded_step _ _ (env_sec_bounded_step _ _ Hbound))
                Hnodup Hmap) as [Hbound' Hnodup'].
    split.
    { eapply env_sec_bounded_le; [exact Hbound'|].
      eapply fresh_inst_map_list_state_monotone; eauto. }
    split; [exact Hnodup'|].
    exists st, (Pos.succ st). auto.
  Qed.

  Lemma generate_local_env_for_node_injective:
    forall n st env aux st',
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      env_injective env.
  Proof.
    intros n st env aux st' Hgen.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    destruct (fresh_map_list_env_props
                ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
                   ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
                (Env.empty _) (Pos.succ (Pos.succ st)) env0 st3)
      as [_ Hnodup].
    - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
    - constructor.
    - exact Hmap.
    - eapply env_values_nodup_injective; eauto.
  Qed.

  Lemma generate_local_env_for_node_state_monotone:
    forall n st env aux st',
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      (st <= st')%positive.
  Proof.
    intros n st env aux st' Hgen.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
    eapply Pos.le_trans;
      [eapply fresh_map_list_state_monotone; eauto
      |eapply fresh_inst_map_list_state_monotone; eauto].
  Qed.

  Lemma generate_local_env_for_node_aux_sec_names:
    forall n st env aux st',
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      aux.(nclk) = Ids.gensym Ids.sec st
      /\ aux.(nrst) = Ids.gensym Ids.sec (Pos.succ st).
  Proof.
    intros n st env aux st' Hgen.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
      split; reflexivity.
  Qed.

  Lemma generate_local_env_for_node_name:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      rec.(nname) = n.(n_name).
  Proof.
    intros n st env rec st' Hgen.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env' & st3 & Henv & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold NMret in Hret. inversion Hret; subst rec st' env.
    reflexivity.
  Qed.

  Lemma generate_local_env_for_node_sec_range:
    forall n st env aux st' x ty,
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      Env.find x env = Some ty ->
      exists nsec, ty = Ids.gensym Ids.sec nsec.
  Proof.
    intros n st env aux st' x ty Hgen Hfind.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    pose proof
      (fresh_map_list_find_ge_start_from_empty
         ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
            ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
         (Pos.succ (Pos.succ st)) env0 st3 x ty Hmap Hfind)
      as (nsec & Hsec & _).
    now exists nsec.
  Qed.

  Lemma generate_local_env_for_node_lower_bound:
    forall n st env aux st' x ty,
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      Env.find x env = Some ty ->
      exists nsec, ty = Ids.gensym Ids.sec nsec /\ (Pos.succ (Pos.succ st) <= nsec)%positive.
  Proof.
    intros n st env aux st' x ty Hgen Hfind.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    pose proof
      (fresh_map_list_find_ge_start_from_empty
         ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
            ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
         (Pos.succ (Pos.succ st)) env0 st3 x ty Hmap Hfind)
      as (nsec & Hsec & [Hlo _]).
    exists nsec. split; auto.
  Qed.

  Lemma generate_local_env_for_node_bounded:
    forall n st env aux st',
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      env_sec_bounded st' env.
  Proof.
    intros n st env aux st' Hgen x ty Hfind.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    pose proof
      (fresh_map_list_find_ge_start_from_empty
         ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
            ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
         (Pos.succ (Pos.succ st)) env0 st3 x ty Hmap Hfind)
      as (nsec & Hsec & [_ Hhi]).
    exists nsec. split; [exact Hsec|].
    eapply Pos.lt_le_trans; [exact Hhi|].
    eapply fresh_inst_map_list_state_monotone; eauto.
  Qed.

  Lemma generate_local_env_for_node_fresh_from_bound:
    forall n st env aux st' x ty i,
      generate_local_env_for_node n st = OK ((env, aux), st') ->
      Env.find x env = Some ty ->
      (i < Pos.succ (Pos.succ st))%positive ->
      ty <> Ids.gensym Ids.sec i.
  Proof.
    intros n st env aux st' x ty i Hgen Hfind Hlt Heq.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    pose proof
      (fresh_map_list_find_ge_start_from_empty
         ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
            ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
         (Pos.succ (Pos.succ st)) env0 st3 x ty Hmap Hfind)
      as (nsec & Hsec & [Hlo _]).
    rewrite Heq in Hsec.
    apply gensym_injective in Hsec as [_ Hidx]. subst nsec.
    eapply Pos.lt_irrefl.
    eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma generate_node_scoped_env'_state_monotone:
    forall ns envs acc st envs' aux st',
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      (st <= st')%positive.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hgen.
    - simpl in Hgen. inversion Hgen; subst. reflexivity.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st_local & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      unfold fresh_insert_node_env in Hins.
      destruct (Env.mem n.(n_name) envs) eqn:Hmem; try discriminate.
      unfold insert_node_env, NMret in Hins. inversion Hins; subst envs1 stins.
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      eapply Pos.le_trans.
      + eapply generate_local_env_for_node_state_monotone; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma generate_node_scoped_env'_bounded:
    forall ns envs acc st envs' aux st',
      node_scoped_env_sec_bounded st envs ->
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      node_scoped_env_sec_bounded st' envs'.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hbound Hgen.
    - simpl in Hgen. inversion Hgen; subst.
      intros name local_env x ty Hfindenv Hfind.
      specialize (Hbound _ _ _ _ Hfindenv Hfind) as (k & Hk & Hlt).
      exists k. split; auto.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st_local & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & stins & Hins & Hgen).
      unfold fresh_insert_node_env in Hins.
      destruct (Env.mem n.(n_name) envs) eqn:Hmem; try discriminate.
      unfold insert_node_env, NMret in Hins. inversion Hins; subst envs1 stins.
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs' aux st'.
      assert (Hmono : (st <= st_local)%positive).
      { eapply generate_local_env_for_node_state_monotone; eauto. }
      assert (Hstepbound : node_scoped_env_sec_bounded st_local (Env.add n.(n_name) local_env envs)).
      {
        intros name local_env' x ty Hfindenv Hfind.
        unfold find_node_env in Hfindenv.
        rewrite Env.gsspec in Hfindenv.
        destruct (ident_eq_dec name n.(n_name)) as [Heq|Hneq].
        - subst name.
          destruct (Env.Props.P.F.eq_dec n.(n_name) n.(n_name)) as [_|Hneqself]; [|contradiction].
          simpl in Hfindenv. inversion Hfindenv; subst local_env'.
          eapply generate_local_env_for_node_bounded in Hlocal as Hlocalbound.
          specialize (Hlocalbound _ _ Hfind) as (k & Hk & Hlt).
          exists k. split; auto.
        - destruct (Env.Props.P.F.eq_dec name n.(n_name)) as [Heq'|_].
          { contradiction. }
          simpl in Hfindenv.
          specialize (Hbound _ _ _ _ Hfindenv Hfind) as (k & Hk & Hlt).
          exists k. split; auto.
          eapply Pos.lt_le_trans; eauto.
      }
      eapply IH; eauto.
  Qed.

  (** This packages the main properties of the global naming pass.  Later files use it to recover injective local environments, fresh auxiliary names, and the range bounds on generated security identifiers. *)
  Lemma generate_node_env_props':
    forall ns env acc st env' aux st',
      env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      aux_sec_names acc ->
      generate_node_env' ns env acc st = OK ((env', aux), st') ->
      env_sec_bounded st' env'
      /\ NoDupMembers (env_values env')
      /\ aux_sec_names aux.
  Proof.
    induction ns as [|n ns IH]; intros env acc st env' aux st'
                                        Hbound Hnodup Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. repeat split; auto.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (env1 & rec & st1 & Hstep & Hgen).
      eapply name_bind2_inv in Hgen as (env2 & rs & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' aux st'.
      destruct (generate_new_names_for_node_env_props _ _ _ _ _ _
                  Hbound Hnodup Hstep)
        as [Hbound1 [Hnodup1 Haux1]].
      assert (Hacc1 : aux_sec_names (rec :: acc)).
      { intros rec' Hin.
        destruct Hin as [Heq|Hin].
        - subst rec'. exact Haux1.
        - eapply Hacc; eauto. }
      eapply IH; eauto.
  Qed.

  Lemma generate_node_env_injective:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      env_injective env.
  Proof.
    intros all_nodes env aux_names Hgen.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
      as [_ [Hnodup _]];
      eauto.
    - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
    - constructor.
    - intros rec Hin. contradiction.
    - eapply env_values_nodup_injective; eauto.
  Qed.

  Lemma get_node_aux_In:
    forall name aux clk_id rst_id,
      get_node_aux name aux = Some (clk_id, rst_id) ->
      exists rec,
        In rec aux
        /\ rec.(nname) = name
        /\ rec.(nclk) = clk_id
        /\ rec.(nrst) = rst_id.
  Proof.
    induction aux as [|rec aux IH]; intros clk_id rst_id Haux.
    - unfold get_node_aux in Haux. simpl in Haux. discriminate.
    - unfold get_node_aux in Haux. simpl in Haux.
      destruct (ident_eqb name rec.(nname)) eqn:Hname.
      + inversion Haux; subst clk_id rst_id.
        apply ident_eqb_eq in Hname.
        exists rec. split; [now left|].
        repeat split; auto.
      + eapply IH in Haux as (rec' & Hin & Hn & Hc & Hr).
        exists rec'. split; [now right|].
        repeat split; auto.
  Qed.

  Lemma get_node_inst_In:
    forall name aux ie,
      get_node_inst name aux = Some ie ->
      exists rec, In rec aux /\ rec.(nname) = name /\ rec.(ninst) = ie.
  Proof.
    induction aux as [|rec aux IH]; intros ie Hinst.
    - unfold get_node_inst in Hinst. simpl in Hinst. discriminate.
    - unfold get_node_inst in Hinst. simpl in Hinst.
      destruct (ident_eqb name rec.(nname)) eqn:Hname.
      + inversion Hinst; subst ie.
        apply ident_eqb_eq in Hname.
        exists rec. repeat split; auto. now left.
      + eapply IH in Hinst as (rec' & Hin & Hn & Hi).
        exists rec'. repeat split; auto. now right.
  Qed.

  (** Every generated record carries an injective, [sec_reset]-ranged
      instance environment.  Stated over the whole record list, so it
      needs no correspondence between a record and the node it came
      from. *)

  Definition aux_inst_props (aux: list node_aux_names) : Prop :=
    Forall (fun rec =>
              env_injective rec.(ninst)
              /\ forall x ty, Env.find x rec.(ninst) = Some ty ->
                              exists m, ty = Ids.gensym Ids.sec_reset m)
           aux.

  Lemma generate_node_env'_inst_props:
    forall ns env acc st env' aux st',
      aux_inst_props acc ->
      generate_node_env' ns env acc st = OK ((env', aux), st') ->
      aux_inst_props aux.
  Proof.
    induction ns as [|n ns IH]; intros env acc st env' aux st' Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (env1 & rec & st1 & Hnew & Hrec).
      eapply name_bind2_inv in Hrec as (env2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env2 aux2 st2.
      eapply IH; [|exact Hrec].
      constructor; [|exact Hacc].
      unfold generate_new_names_for_node in Hnew.
      eapply name_bind_inv in Hnew as (clk_name & sa & Hclk & Hnew).
      eapply name_bind_inv in Hnew as (rst_name & sb & Hrst & Hnew).
      eapply name_bind_inv in Hnew as (env0 & sc & Hmap & Hnew).
      eapply name_bind_inv in Hnew as (ie & sd & Hinst & Hret2).
      unfold NMret in Hret2. inversion Hret2; subst env1 rec st1.
      simpl.
      eapply fresh_inst_map_list_from_empty_props; eauto.
  Qed.

  Lemma generate_node_env_inst_props:
    forall all_nodes env aux_names name ie,
      generate_node_env all_nodes = OK (env, aux_names) ->
      get_node_inst name aux_names = Some ie ->
      env_injective ie
      /\ (forall x ty, Env.find x ie = Some ty ->
                       exists m, ty = Ids.gensym Ids.sec_reset m).
  Proof.
    intros all_nodes env aux_names name ie Hgen Hinst.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    assert (Hprops : aux_inst_props aux0).
    { eapply generate_node_env'_inst_props; [|exact Hgen']. constructor. }
    destruct (get_node_inst_In _ _ _ Hinst) as (rec & Hin & _ & Hie).
    unfold aux_inst_props in Hprops.
    eapply Forall_forall in Hprops; [|exact Hin].
    now rewrite Hie in Hprops.
  Qed.

  Lemma generate_local_env_for_node_inst_props:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      env_injective rec.(ninst)
      /\ (forall x ty, Env.find x rec.(ninst) = Some ty ->
                       exists m, ty = Ids.gensym Ids.sec_reset m).
  Proof.
    intros n st env rec st' Hgen.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & sa & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & sb & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & sc & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (ie & sd & Hinst & Hret).
    unfold NMret in Hret. inversion Hret; subst env rec st'.
    simpl.
    eapply fresh_inst_map_list_from_empty_props; eauto.
  Qed.

  Lemma generate_node_scoped_env'_inst_props:
    forall ns envs acc st envs' aux st',
      aux_inst_props acc ->
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      aux_inst_props aux.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & st2 & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st3 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
      eapply IH; [|exact Hrec].
      constructor; [|exact Hacc].
      unfold generate_local_env_for_node in Hlocal.
      eapply name_bind_inv in Hlocal as (clk_name & sa & Hclk & Hlocal).
      eapply name_bind_inv in Hlocal as (rst_name & sb & Hrst & Hlocal).
      eapply name_bind_inv in Hlocal as (env0 & sc & Hmap & Hlocal).
      eapply name_bind_inv in Hlocal as (ie & sd & Hinst & Hret2).
      unfold NMret in Hret2. inversion Hret2; subst local_env rec st1.
      simpl.
      eapply fresh_inst_map_list_from_empty_props; eauto.
  Qed.

  Lemma generate_node_scoped_env_inst_props:
    forall all_nodes envs aux_names name ie,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      get_node_inst name aux_names = Some ie ->
      env_injective ie
      /\ (forall x ty, Env.find x ie = Some ty ->
                       exists m, ty = Ids.gensym Ids.sec_reset m).
  Proof.
    intros all_nodes envs aux_names name ie Hgen Hinst.
    unfold generate_node_scoped_env in Hgen.
    destruct (generate_node_scoped_env' all_nodes (Env.empty _) nil init_state)
      as [[[envs0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst envs aux_names.
    assert (Hprops : aux_inst_props aux0).
    { eapply generate_node_scoped_env'_inst_props; [|exact Hgen']. constructor. }
    destruct (get_node_inst_In _ _ _ Hinst) as (rec & Hin & _ & Hie).
    unfold aux_inst_props in Hprops.
    eapply Forall_forall in Hprops; [|exact Hin].
    now rewrite Hie in Hprops.
  Qed.

  (** The clock and reset names of a node are distinct: they are minted
      from consecutive states. *)

  Definition aux_clk_rst_distinct (aux: list node_aux_names) : Prop :=
    Forall (fun rec => ~ (rec.(nclk) = rec.(nrst))) aux.

  Lemma aux_clk_rst_distinct_get_node_aux:
    forall aux name clk_id rst_id,
      aux_clk_rst_distinct aux ->
      get_node_aux name aux = Some (clk_id, rst_id) ->
      ~ (clk_id = rst_id).
  Proof.
    intros aux name clk_id rst_id Hdist Haux.
    destruct (get_node_aux_In _ _ _ _ Haux) as (rec & Hin & _ & Hclk & Hrst).
    unfold aux_clk_rst_distinct in Hdist.
    rewrite Forall_forall in Hdist.
    specialize (Hdist rec Hin).
    now rewrite Hclk, Hrst in Hdist.
  Qed.

  Lemma generate_node_env'_clk_rst_distinct:
    forall ns env acc st env' aux st',
      aux_clk_rst_distinct acc ->
      generate_node_env' ns env acc st = OK ((env', aux), st') ->
      aux_clk_rst_distinct aux.
  Proof.
    induction ns as [|n ns IH]; intros env acc st env' aux st' Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (env1 & rec & st1 & Hnew & Hgen).
      eapply name_bind2_inv in Hgen as (env2 & aux2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env2 aux2 st2.
      eapply IH; [|exact Hrec].
      constructor; [|exact Hacc].
      unfold generate_new_names_for_node in Hnew.
      eapply name_bind_inv in Hnew as (clk_name & sa & Hclk & Hnew).
      eapply name_bind_inv in Hnew as (rst_name & sb & Hrst & Hnew).
      eapply name_bind_inv in Hnew as (env0 & sc & Hmap & Hnew).
      eapply name_bind_inv in Hnew as (ie & sd & Hinst & Hret2).
      unfold NMret in Hret2. inversion Hret2; subst env1 rec st1.
      unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name sa.
      unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name sb.
      simpl. intro Heq.
      apply gensym_injective in Heq as [_ Heq].
      pose proof (Pos.lt_succ_diag_r st) as Hlt.
      rewrite <- Heq in Hlt.
      exact (Pos.lt_irrefl _ Hlt).
  Qed.

  Lemma generate_node_env_clk_rst_distinct:
    forall all_nodes env aux_names name clk_id rst_id,
      generate_node_env all_nodes = OK (env, aux_names) ->
      get_node_aux name aux_names = Some (clk_id, rst_id) ->
      ~ (clk_id = rst_id).
  Proof.
    intros all_nodes env aux_names name clk_id rst_id Hgen Haux.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    assert (Hprops : aux_clk_rst_distinct aux0).
    { eapply generate_node_env'_clk_rst_distinct; [|exact Hgen']. constructor. }
    destruct (get_node_aux_In _ _ _ _ Haux) as (rec & Hin & _ & Hclk & Hrst).
    unfold aux_clk_rst_distinct in Hprops.
    rewrite Forall_forall in Hprops.
    specialize (Hprops rec Hin).
    rewrite Hclk, Hrst in Hprops. exact Hprops.
  Qed.

  (** The same fact for the per-node generator, read straight off the two
      consecutive [fresh_ident_gen] calls: the clock name is minted at
      [st] and the reset name at [Pos.succ st], so they cannot coincide.
      Nothing downstream has to assume it. *)

  Lemma generate_local_env_for_node_clk_rst_distinct:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      ~ (rec.(nclk) = rec.(nrst)).
  Proof.
    intros n st env rec st' Hgen.
    destruct (generate_local_env_for_node_aux_sec_names _ _ _ _ _ Hgen)
      as [Hclk Hrst].
    rewrite Hclk, Hrst. intro Heq.
    apply gensym_injective in Heq as [_ Heq].
    pose proof (Pos.lt_succ_diag_r st) as Hlt.
    rewrite <- Heq in Hlt.
    exact (Pos.lt_irrefl _ Hlt).
  Qed.

  Lemma generate_node_scoped_env'_clk_rst_distinct:
    forall ns envs acc st envs' aux st',
      aux_clk_rst_distinct acc ->
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      aux_clk_rst_distinct aux.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & st2 & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st3 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
      eapply IH; [|exact Hrec].
      constructor; [|exact Hacc].
      eapply generate_local_env_for_node_clk_rst_distinct; eauto.
  Qed.

  Lemma generate_node_scoped_env_clk_rst_distinct:
    forall all_nodes envs aux_names,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      aux_clk_rst_distinct aux_names.
  Proof.
    intros all_nodes envs aux_names Hgen.
    unfold generate_node_scoped_env in Hgen.
    destruct (generate_node_scoped_env' all_nodes (Env.empty _) nil init_state)
      as [[[envs0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst envs aux_names.
    eapply generate_node_scoped_env'_clk_rst_distinct; [constructor|exact Hgen'].
  Qed.

  Lemma generate_node_scoped_env'_aux_sec_names:
    forall ns envs acc st envs' aux st',
      aux_sec_names acc ->
      generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      aux_sec_names aux.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & st2 & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st3 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
      eapply IH; [|exact Hrec].
      intros rec' [Heq|Hin].
      + subst rec'.
        destruct (generate_local_env_for_node_aux_sec_names _ _ _ _ _ Hlocal)
          as [Hclk Hrst].
        eauto.
      + eapply Hacc; eauto.
  Qed.

  Lemma generate_node_scoped_env_aux_sec_names:
    forall all_nodes envs aux_names name clk_id rst_id,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      get_node_aux name aux_names = Some (clk_id, rst_id) ->
      exists i j,
        clk_id = Ids.gensym Ids.sec i
        /\ rst_id = Ids.gensym Ids.sec j.
  Proof.
    intros all_nodes envs aux_names name clk_id rst_id Hgen Haux.
    unfold generate_node_scoped_env in Hgen.
    destruct (generate_node_scoped_env' all_nodes (Env.empty _) nil init_state)
      as [[[envs0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst envs aux_names.
    assert (Hprops : aux_sec_names aux0).
    { eapply generate_node_scoped_env'_aux_sec_names; [|exact Hgen'].
      intros rec Hin; contradiction. }
    eapply get_node_aux_In in Haux as (rec & Hin & _ & Hclk & Hrst).
    specialize (Hprops rec Hin) as (i & j & Hi & Hj).
    rewrite Hclk, Hrst in *. eauto.
  Qed.

  Lemma generate_node_aux_sec_names:
    forall all_nodes env aux_names name clk_id rst_id,
      generate_node_env all_nodes = OK (env, aux_names) ->
      get_node_aux name aux_names = Some (clk_id, rst_id) ->
      exists i j,
        clk_id = Ids.gensym Ids.sec i
        /\ rst_id = Ids.gensym Ids.sec j.
  Proof.
    intros all_nodes env aux_names name clk_id rst_id Hgen Haux.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
      as [_ [_ Hauxsec]];
      eauto.
    - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
    - constructor.
    - intros rec Hin. contradiction.
    - eapply get_node_aux_In in Haux as (rec & Hin & _ & Hclk & Hrst).
      specialize (Hauxsec rec Hin) as (i & j & Hi & Hj).
      rewrite Hclk, Hrst in *. eauto.
  Qed.

  Lemma generate_node_env_sec_range:
    forall all_nodes env aux_names x ty,
      generate_node_env all_nodes = OK (env, aux_names) ->
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n.
  Proof.
    intros all_nodes env aux_names x ty Hgen Hfind.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
      as [Hbound _];
      eauto.
    - intros z tz Hz. rewrite Env.gempty in Hz. discriminate.
    - constructor.
    - intros rec Hin. contradiction.
    - specialize (Hbound _ _ Hfind) as [n [Hty _]].
      exists n. exact Hty.
  Qed.

  (** ** The naming facts every consumer needs

      Downstream proofs never use [generate_node_env] or
      [generate_local_env_for_node] directly; they use these four
      properties of the environment those calls produce.  Bundling them
      is what lets one theorem serve both the whole-program environment
      and a single node's local environment, so the [_from_local_env]
      and [_from_generated_env] pairs differ only in which constructor
      they invoke. *)

  (** The environment half is per node: it constrains one local
      environment.  The auxiliary half is per program: it constrains the
      single accumulated [aux_names] list every node shares.  Keeping
      them apart is what lets a caller quantify the first over the
      systems of a program while proving the second once. *)

  Definition env_naming_props (env: Env.t ident) : Prop :=
    env_injective env
    /\ (forall x ty, Env.find x env = Some ty ->
                     exists m, ty = Ids.gensym Ids.sec m).

  Definition aux_naming_props (aux_names: list node_aux_names) : Prop :=
    (forall name clk_id rst_id,
        get_node_aux name aux_names = Some (clk_id, rst_id) ->
        exists i j, clk_id = Ids.gensym Ids.sec i
                    /\ rst_id = Ids.gensym Ids.sec j)
    /\ (forall name ie,
           get_node_inst name aux_names = Some ie ->
           env_injective ie
           /\ (forall x ty, Env.find x ie = Some ty ->
                            exists m, ty = Ids.gensym Ids.sec_reset m))
    /\ aux_clk_rst_distinct aux_names.

  Definition naming_env_props
    (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
    env_naming_props env /\ aux_naming_props aux_names.

  Lemma env_naming_props_from_generated_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      env_naming_props env.
  Proof.
    intros all_nodes env aux_names Hgen.
    split; [eapply generate_node_env_injective; eauto|].
    intros; eapply generate_node_env_sec_range; eauto.
  Qed.

  Lemma env_naming_props_from_local_env:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      env_naming_props env.
  Proof.
    intros n st env rec st' Hlocal.
    split; [eapply generate_local_env_for_node_injective; eauto|].
    intros; eapply generate_local_env_for_node_sec_range; eauto.
  Qed.

  Lemma aux_naming_props_from_generated_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      aux_naming_props aux_names.
  Proof.
    intros all_nodes env aux_names Hgen.
    split; [intros; eapply generate_node_aux_sec_names; eauto|].
    split; [intros name ie Hinst; eapply generate_node_env_inst_props; eauto|].
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    eapply generate_node_env'_clk_rst_distinct; [constructor|exact Hgen'].
  Qed.

  Lemma aux_naming_props_from_scoped_env:
    forall all_nodes envs aux_names,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      aux_naming_props aux_names.
  Proof.
    intros all_nodes envs aux_names Hscoped.
    split; [intros; eapply generate_node_scoped_env_aux_sec_names; eauto|].
    split; [intros; eapply generate_node_scoped_env_inst_props; eauto|].
    eapply generate_node_scoped_env_clk_rst_distinct; eauto.
  Qed.

  Lemma naming_env_props_from_generated_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      naming_env_props env aux_names.
  Proof.
    intros all_nodes env aux_names Hgen.
    split; [eapply env_naming_props_from_generated_env
           |eapply aux_naming_props_from_generated_env]; eauto.
  Qed.

  (** The scoped counterpart.  The environment half comes from the one
      node's own [generate_local_env_for_node] run; the auxiliary half
      ranges over the whole accumulated list, so it comes from the
      scoped generator that produced it.  Both are read off the naming
      monad -- in particular the clock/reset distinctness, which is
      never assumed. *)

  Lemma naming_env_props_from_local_env:
    forall all_nodes envs aux_names n st env rec st',
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      naming_env_props env aux_names.
  Proof.
    intros all_nodes envs aux_names n st env rec st' Hscoped Hlocal.
    split; [eapply env_naming_props_from_local_env
           |eapply aux_naming_props_from_scoped_env]; eauto.
  Qed.

  (** ** The freshness window of one node's environment

      Every name [generate_local_env_for_node] mints lies strictly
      between the state before the call and the state after it.  This is
      the only thing the scoped signature induction needs from the
      naming run: it bounds the node's signature scope above, and bounds
      it below against everything generated earlier. *)

  Definition env_sec_window (env: Env.t ident) (st st': ident) : Prop :=
    (forall x ty,
        Env.find x env = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n
                  /\ (st <= n)%positive /\ (n < st')%positive)
    /\ (st <= st')%positive.

  Lemma env_sec_window_from_local_env:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      env_sec_window env st st'.
  Proof.
    intros n st env rec st' Hlocal.
    split; [|eapply generate_local_env_for_node_state_monotone; eauto].
    intros x ty Hfind.
    edestruct (generate_local_env_for_node_lower_bound
                 n st env rec st' x ty Hlocal Hfind) as (m & Hm & Hlo).
    exists m. split; [exact Hm|]. split.
    - eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    - destruct (generate_local_env_for_node_bounded
                  n st env rec st' Hlocal x ty Hfind) as (m' & Hm' & Hlt).
      rewrite Hm in Hm'. apply gensym_injective in Hm' as [_ Heq].
      subst m'. exact Hlt.
  Qed.

End NAMEGEN.

Module Type  NameGen  (Ids   : IDS)
  (Op    : OPERATORS)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn) <: NAMEGEN Ids Op CESyn SynNL.

Include NAMEGEN Ids Op CESyn SynNL.

End NameGen.
