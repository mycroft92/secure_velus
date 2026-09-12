(** Security-name allocation for Lustre nodes.

    [NameInterface.v] allocates the generated security names, and the rest of
    the development consumes what it produced: the naming pass runs once, over
    NLustre nodes, and the Stc and Obc generators read its result rather than
    minting their own.  That is the right discipline -- if each language minted
    its own names the phases would disagree -- but it is stated over
    [NLSYNTAX], so taken literally it would mean a Lustre program could only be
    typed once its NLustre translation existed.  The data flows the other way.

    This file gives Lustre its own allocator, defined by reusing
    [NameInterface.v]'s monad and combinators rather than duplicating them, and
    then proves the two agree: transcription preserves a node's name and its
    input, variable and output lists definitionally, and preserves the
    instances its equations call, so the environment allocated for a Lustre
    node is *equal* to the one allocated for its transcription.  Lustre is
    therefore typed on its own terms, and the agreement is a theorem.

    The equality is specific to transcription.  Unnesting and
    fby-initialisation add local variables, so across those passes the
    environments are related by inclusion and freshness, not by equality.

    Nothing in [NameInterface.v] is modified. *)

From Coq Require Import List.
From Coq Require Import PArith.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.NameInterface.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLNAMEGEN
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import LSyn    : LSYNTAX  Ids Op)
  (CESyn          : CESYNTAX     Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import NAMEGEN : NAMEGEN  Ids Op CESyn NLSyn)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn).

  Import NAMEMONADNotations.

  (** * Instances called by a Lustre node

      The Lustre spelling of [NLSyntax.gather_inst_eq].  A node call is named
      by the first variable it defines, on both sides, and [to_equation]
      carries the defined variables and the callee's name across unchanged. *)

  Definition gather_linst_eq (eq : equation) : list (ident * ident) :=
    match eq with
    | (x :: _, [Eapp f _ _ _]) => [(x, f)]
    | _ => []
    end.

  Definition gather_linsts := flat_map gather_linst_eq.

  (** * Allocation

      The same steps as [generate_local_env_for_node], over a Lustre node.  It
      is written out rather than shared because the two take different node
      records; every combinator it uses comes from [NAMEGEN]. *)

  Definition generate_local_env_for_lnode (n : node)
    : Name (local_sec_env * node_aux_names) :=
    do clk_name <- fresh_ident_gen;
    do rst_name <- fresh_ident_gen;
    do env' <- fresh_map_list
                 ([clk_name; rst_name]
                    ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
                 (Env.empty _);
    do inst_env <- fresh_inst_map_list
                     (map fst (gather_linsts n.(n_eqs))) (Env.empty _);
    NMret (env', {| nname := n.(n_name); nclk := clk_name; nrst := rst_name;
                    ninst := inst_env |}).

  Fixpoint generate_lnode_scoped_env'
    (ns : list node) (envs : node_scoped_env) (acc : list node_aux_names)
    : Name (node_scoped_env * list node_aux_names) :=
    match ns with
    | [] => NMret (envs, acc)
    | n :: ns' =>
        do (local_env, r) <- generate_local_env_for_lnode n;
        do envs' <- fresh_insert_node_env envs n.(n_name) local_env;
        do (envs'', rs) <- generate_lnode_scoped_env' ns' envs' (r :: acc);
        NMret (envs'', rs)
    end.

  Definition generate_lnode_scoped_env (ns : list node)
    : res (node_scoped_env * list node_aux_names) :=
    match generate_lnode_scoped_env' ns (Env.empty _) [] init_state with
    | OK ((envs, names), _) => OK (envs, names)
    | Error e => Error e
    end.

  (** The same run, keeping the final state.

      Every name this pass mints lies below that bound, so a generator started
      from it mints only names fresh from every program variable's security
      name.  That is what the Lustre constraint generator needs, because its
      call case is the first in the development that must mint at all: it
      draws from [Ids.sec], the very namespace this pass uses. *)

  Definition generate_lnode_scoped_env_st (ns : list node)
    : res (node_scoped_env * list node_aux_names * name_state) :=
    match generate_lnode_scoped_env' ns (Env.empty _) [] init_state with
    | OK ((envs, names), st) => OK (envs, names, st)
    | Error e => Error e
    end.

  Lemma generate_lnode_scoped_env_st_spec :
    forall ns envs names st,
      generate_lnode_scoped_env_st ns = OK (envs, names, st) ->
      generate_lnode_scoped_env ns = OK (envs, names).
  Proof.
    unfold generate_lnode_scoped_env_st, generate_lnode_scoped_env.
    intros ns envs names st H.
    destruct (generate_lnode_scoped_env' ns (Env.empty _) [] init_state)
      as [[[envs' names'] st']|e] eqn:E; try discriminate.
    now inversion H.
  Qed.

  (** * Agreement with the NLustre allocator *)

  Lemma to_equation_gather_inst :
    forall cenv envo eq eq',
      to_equation cenv envo eq = OK eq' ->
      NLSyn.gather_inst_eq eq' = gather_linst_eq eq.
  Proof.
    intros cenv envo [xs es] eq' Htr.
    destruct es as [|e [|e' es']]; simpl in Htr; try discriminate.
    destruct e;
      try (destruct xs as [|x [|]]; simpl in Htr; try discriminate;
           monadInv Htr; reflexivity).
    - (* Efby: an equation over fby names no instance on either side *)
      destruct l as [|e0 [|e0' l']]; destruct l0 as [|e1 [|e1' l0']];
        destruct xs as [|xa [|xb xsr]]; simpl in Htr;
          try discriminate;
          try (monadInv Htr; reflexivity);
          try (destruct (find_clock cenv xa); simpl in Htr; discriminate).
    - (* Eapp: the defined variables and the callee's name cross unchanged *)
      destruct o as [er|]; simpl in Htr.
      + destruct er; try discriminate.
        destruct a as [ty [ckx nm]]. monadInv Htr.
        destruct xs as [|xh xt]; reflexivity.
      + monadInv Htr. destruct xs as [|xh xt]; reflexivity.
  Qed.

  Lemma mmap_to_equation_gather :
    forall cenv envo eqs neqs,
      Errors.mmap (to_equation cenv envo) eqs = OK neqs ->
      NLSyn.gather_insts neqs = gather_linsts eqs.
  Proof.
    induction eqs as [|eq eqs IH]; intros neqs Hm; simpl in Hm.
    - inv Hm. reflexivity.
    - monadInv Hm. simpl.
      erewrite to_equation_gather_inst by eauto.
      erewrite IH by eauto. reflexivity.
  Qed.

  Lemma to_node_gather_insts :
    forall n n' Hp,
      to_node n Hp = OK n' ->
      NLSyn.gather_insts n'.(NLSyn.n_eqs) = gather_linsts n.(n_eqs).
  Proof.
    intros n n' Hp Htr. tonodeInv Htr. simpl.
    eapply mmap_to_equation_gather; eauto.
  Qed.

  (** One node: the environment allocated for a Lustre node is the very one
      allocated for its transcription.  Transcription keeps the name and the
      three variable lists definitionally, and by the lemma above it keeps the
      instances too, so there is nothing left for the two allocators to
      disagree about. *)

  Theorem to_node_local_env :
    forall n n' Hp,
      to_node n Hp = OK n' ->
      generate_local_env_for_lnode n = NAMEGEN.generate_local_env_for_node n'.
  Proof.
    intros n n' Hp Htr.
    unfold generate_local_env_for_lnode, NAMEGEN.generate_local_env_for_node.
    rewrite (to_node_in _ _ _ Htr), (to_node_vars _ _ _ Htr),
            (to_node_out _ _ _ Htr), (to_node_name _ _ _ Htr).
    rewrite <- (to_node_gather_insts _ _ _ Htr).
    reflexivity.
  Qed.

  (** Whole programs, stated pointwise in the fresh-name state so that the
      induction hypothesis can be used underneath the monad's binds. *)

  Theorem to_global_lscoped_env' :
    forall G P Hp envs acc st,
      to_global G Hp = OK P ->
      generate_lnode_scoped_env' G envs acc st
      = NAMEGEN.generate_node_scoped_env' P envs acc st.
  Proof.
    induction G as [|n G IH]; intros P Hp envs acc st Htr.
    - simpl in Htr. inv Htr. reflexivity.
    - simpl in Htr. monadInv Htr. simpl.
      rewrite (to_node_local_env _ _ _ EQ), (to_node_name _ _ _ EQ).
      unfold NMbind2, NMbind, NMret.
      destruct (NAMEGEN.generate_local_env_for_node x st)
        as [[[le r] st1]|e1]; auto.
      destruct (fresh_insert_node_env envs (NLSyn.n_name x) le st1)
        as [[envs' st2]|e2]; auto.
      erewrite IH by eauto. reflexivity.
  Qed.

  Corollary to_global_lscoped_env :
    forall G P Hp,
      to_global G Hp = OK P ->
      generate_lnode_scoped_env G = NAMEGEN.generate_node_scoped_env P.
  Proof.
    intros G P Hp Htr.
    unfold generate_lnode_scoped_env, NAMEGEN.generate_node_scoped_env.
    now rewrite (to_global_lscoped_env' _ _ _ (Env.empty _) [] init_state Htr).
  Qed.

End SECLNAMEGEN.
