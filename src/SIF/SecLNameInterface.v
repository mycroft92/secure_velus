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
    (** the Lustre-only names come last, on top of the settled shared
        allocation: the streams nested calls name ([anon_in_eqs]) *)
    do env'' <- fresh_map_list (map fst (anon_in_eqs n.(n_eqs))) env';
    NMret (env'', {| nname := n.(n_name); nclk := clk_name; nrst := rst_name;
                     ninst := inst_env |}).

  (** * The naming environment's domain

      Each node's security environment is built from [Env.empty] over the two
      auxiliary names and the node's declared variables, so a successful
      lookup identifies which of those the key is.

      This is what rules out a nested call sitting at another input's clock
      position: such a call's output name lives in [anon_in_eqs], which the
      node record's own [n_nodup] keeps disjoint from the declared variables,
      so [assign_clk_type] could not have succeeded on a clock naming it.
      The exclusion is therefore a fact about this pass and about the node
      record, not a condition on the programs a theorem covers. *)

  Lemma fresh_insert_domain :
    forall e k st e' st' w b,
      fresh_insert e k st = OK (e', st') ->
      Env.find w e' = Some b ->
      w = k \/ exists b0, Env.find w e = Some b0.
  Proof.
    intros e k st e' st' w b H Hf.
    unfold fresh_insert in H.
    destruct (Env.mem k e); [discriminate H|].
    apply name_bind_inv in H as (v & st1 & Hv & H).
    apply name_bind_inv in H as (e1 & st2 & He1 & Hret).
    unfold insert_env, NMret in He1, Hret.
    inversion He1; subst e1. inversion Hret; subst e' st'.
    destruct (ident_eq_dec w k) as [Heq|Hne]; [left; exact Heq|].
    right. exists b. rewrite <- Hf. symmetry.
    apply Env.gso. exact Hne.
  Qed.

  Lemma fresh_map_list_domain :
    forall ks e st e' st' w b,
      fresh_map_list ks e st = OK (e', st') ->
      Env.find w e' = Some b ->
      In w ks \/ exists b0, Env.find w e = Some b0.
  Proof.
    induction ks as [|k ks IH]; intros e st e' st' w b H Hf.
    - simpl in H. unfold NMret in H. inversion H; subst e' st'.
      right. exists b. exact Hf.
    - simpl in H.
      apply name_bind_inv in H as (e1 & st1 & He1 & H).
      apply name_bind_inv in H as (e2 & st2 & He2 & Hret).
      unfold NMret in Hret. inversion Hret; subst e2 st2.
      destruct (IH e1 st1 e' st' w b He2 Hf) as [Hin|(b0 & Hb0)];
        [left; right; exact Hin|].
      destruct (fresh_insert_domain e k st e1 st1 w b0 He1 Hb0)
        as [Heq|Hold]; [left; left; symmetry; exact Heq|].
      right. exact Hold.
  Qed.

  Lemma fresh_map_list_domain_empty :
    forall ks st e' st' w b,
      fresh_map_list ks (Env.empty ident) st = OK (e', st') ->
      Env.find w e' = Some b ->
      In w ks.
  Proof.
    intros ks st e' st' w b H Hf.
    destruct (fresh_map_list_domain ks (Env.empty ident) st e' st' w b H Hf)
      as [Hin|(b0 & Hb0)]; [exact Hin|].
    rewrite Env.gempty in Hb0. discriminate Hb0.
  Qed.

  (** And so, for one Lustre node's own environment: the two auxiliary
      names, the declared variables, or the Lustre-only anonymous streams. *)
  Lemma generate_local_env_for_lnode_domain :
    forall n st le aux st' w b,
      generate_local_env_for_lnode n st = OK ((le, aux), st') ->
      Env.find w le = Some b ->
      w = aux.(nclk) \/ w = aux.(nrst)
      \/ In w (List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
      \/ In w (List.map fst (anon_in_eqs n.(n_eqs))).
  Proof.
    intros n st le aux st' w b H Hf.
    unfold generate_local_env_for_lnode in H.
    apply name_bind_inv in H as (clk & st1 & Hclk & H).
    apply name_bind_inv in H as (rst & st2 & Hrst & H).
    apply name_bind_inv in H as (env1 & st3 & Henv & H).
    apply name_bind_inv in H as (ienv & st4 & Hienv & H).
    apply name_bind_inv in H as (env2 & st5 & Henv2 & Hret).
    unfold NMret in Hret. inversion Hret; subst le aux st'.
    simpl.
    destruct (fresh_map_list_domain _ _ _ _ _ w b Henv2 Hf)
      as [Hin|(b0 & Hb0)]; [now right; right; right|].
    apply (fresh_map_list_domain_empty _ st2 env1 st3 w b0 Henv) in Hb0.
    destruct Hb0 as [Hf'|[Hf'|Hf']]; [now left|now right; left|].
    right. right. left. exact Hf'.
  Qed.

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

  (** The Lustre allocator has the same range invariant as the NLustre
      allocator.  It is reproved here because its node records are different,
      although both allocators use the same [NAMEGEN] primitives. *)
  Lemma generate_local_env_for_lnode_bounded :
      forall n st env aux st',
        generate_local_env_for_lnode n st = OK ((env, aux), st') ->
        NAMEGEN.env_sec_bounded st' env.
  Proof.
    intros n st env aux st' Hgen x ty Hfind.
    unfold generate_local_env_for_lnode in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hgen).
    eapply name_bind_inv in Hgen as (env2 & st5 & Henv2 & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    destruct (fresh_map_list_find_old_or_ge_start _ _ _ _ _ _ _ Henv2 Hfind)
      as [Hfind0|(nn & Hnn & [_ Hhi])];
      [|exists nn; split; [exact Hnn|exact Hhi]].
    pose proof
      (fresh_map_list_find_ge_start_from_empty
         ([gensym Ids.sec st; gensym Ids.sec (Pos.succ st)]
            ++ map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
         (Pos.succ (Pos.succ st)) env0 st3 x ty Hmap Hfind0)
      as (nsec & Hsec & [_ Hhi]).
    exists nsec. split; [exact Hsec|].
    eapply Pos.lt_le_trans; [exact Hhi|].
    eapply Pos.le_trans;
      [eapply fresh_inst_map_list_state_monotone; eauto
      |eapply fresh_map_list_state_monotone; eauto].
  Qed.

  Lemma generate_local_env_for_lnode_state_monotone :
      forall n st env aux st',
        generate_local_env_for_lnode n st = OK ((env, aux), st') ->
        (st <= st')%positive.
  Proof.
    intros n st env aux st' Hgen.
    unfold generate_local_env_for_lnode in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hgen).
    eapply name_bind_inv in Hgen as (env2 & st5 & Henv2 & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env aux st'.
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
    eapply Pos.le_trans;
      [eapply fresh_map_list_state_monotone; eauto|].
    eapply Pos.le_trans;
      [eapply fresh_inst_map_list_state_monotone; eauto
      |eapply fresh_map_list_state_monotone; eauto].
  Qed.

  Lemma generate_lnode_scoped_env'_bounded :
      forall ns envs acc st envs' aux st',
        NAMEGEN.node_scoped_env_sec_bounded st envs ->
        generate_lnode_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
        NAMEGEN.node_scoped_env_sec_bounded st' envs'.
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
      { eapply generate_local_env_for_lnode_state_monotone; eauto. }
      assert (Hstepbound :
                NAMEGEN.node_scoped_env_sec_bounded
                  st_local (Env.add n.(n_name) local_env envs)).
      { intros name local_env' x ty Hfindenv Hfind.
        unfold find_node_env in Hfindenv. rewrite Env.gsspec in Hfindenv.
        destruct (ident_eq_dec name n.(n_name)) as [Heq|Hneq].
        - subst name.
          destruct (Env.Props.P.F.eq_dec n.(n_name) n.(n_name)) as [_|Hself];
            [|contradiction].
          simpl in Hfindenv. inversion Hfindenv; subst local_env'.
          eapply generate_local_env_for_lnode_bounded in Hlocal as Hlocalbound.
          specialize (Hlocalbound _ _ Hfind) as (k & Hk & Hlt).
          exists k. split; auto.
        - destruct (Env.Props.P.F.eq_dec name n.(n_name)) as [Heq'|Hneq'].
          + contradiction.
          + simpl in Hfindenv.
            specialize (Hbound _ _ _ _ Hfindenv Hfind) as (k & Hk & Hlt).
            exists k. split; auto.
            eapply Pos.lt_le_trans; eauto.
      }
      eapply IH; eauto.
  Qed.

  (** The final state returned by the naming pass is a genuine freshness
      boundary for ordinary security names.  Both the naming monad and the
      Lustre security monad use [Ids.sec]; hence a nested-call generator must
      start at this boundary rather than at [SC.init_state]. *)
  Lemma generate_lnode_scoped_env_st_fresh_sec :
      forall ns envs names st name local_env x ty i,
        generate_lnode_scoped_env_st ns = OK (envs, names, st) ->
        find_node_env name envs = Some local_env ->
        Env.find x local_env = Some ty ->
        (st <= i)%positive ->
        ty <> Ids.gensym Ids.sec i.
  Proof.
    intros ns envs names st name local_env x ty i Hgen Henv Hfind Hle Heq.
    unfold generate_lnode_scoped_env_st in Hgen.
    destruct (generate_lnode_scoped_env' ns (Env.empty _) [] init_state)
      as [[[envs' names'] st']|e] eqn:Hrun; try discriminate.
    inversion Hgen; subst envs names st. clear Hgen.
    assert (NAMEGEN.node_scoped_env_sec_bounded st' envs') as Hbound.
    { eapply generate_lnode_scoped_env'_bounded; [|exact Hrun].
      intros n le y u Hnone _.
      unfold find_node_env in Hnone. rewrite Env.gempty in Hnone.
      discriminate. }
    specialize (Hbound _ _ _ _ Henv Hfind) as (j & Hj & Hjlt).
    rewrite Heq in Hj.
    apply gensym_injective in Hj as [_ Hij]. subst j.
    eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto.
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

  (** A translated expression names no stream: [fresh_in] only collects the
      annotations of calls, and the translation rejects every call. *)
  Lemma to_lexp_fresh_nil :
    forall e r0, to_lexp e = OK r0 -> fresh_in e = [].
  Proof.
    induction e as [c|x a|op e a IHe|op e1 e2 a IHe1 IHe2|e0s es a IH0 IHs|e0s es a IH0 IHs|es x b a IHs|x ets efs a IHt IHf|e ets efs a IHe IHt IHf|f es ro a IHr IHs] using exp_ind2; intros r0 Htr; simpl in Htr.
    - reflexivity.
    - reflexivity.
    - destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl. now rewrite (IHe _ EQ).
    - destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl.
      now rewrite (IHe1 _ EQ), (IHe2 _ EQ1).
    - discriminate.
    - discriminate.
    - destruct es as [|e [|e' es']]; try discriminate.
      destruct a as [tys ck]. destruct tys as [|ty [|ty' tys']]; try discriminate.
      monadInv Htr. simpl. inversion IHs; subst.
      now rewrite (H1 _ EQ).
    - discriminate.
    - discriminate.
    - discriminate.
  Qed.

  Lemma to_cexp_fresh_nil :
    forall e ce, to_cexp e = OK ce -> fresh_in e = [].
  Proof.
    induction e as [c|x a|op e a IHe|op e1 e2 a IHe1 IHe2|e0s es a IH0 IHs|e0s es a IH0 IHs|es x b a IHs|x ets efs a IHt IHf|e ets efs a IHe IHt IHf|f es ro a IHr IHs] using exp_ind2; intros ce Htr; simpl in Htr.
    - reflexivity.
    - reflexivity.
    - monadInv Htr. destruct a as [ty ck]. monadInv EQ. simpl.
      repeat match goal with
             | H : to_lexp _ = OK _ |- _ =>
                 rewrite (to_lexp_fresh_nil _ _ H); clear H
             end; reflexivity.
    - monadInv Htr. destruct a as [ty ck]. monadInv EQ. simpl.
      repeat match goal with
             | H : to_lexp _ = OK _ |- _ =>
                 rewrite (to_lexp_fresh_nil _ _ H); clear H
             end; reflexivity.
    - discriminate.
    - discriminate.
    - monadInv Htr. exact (to_lexp_fresh_nil (Ewhen es x b a) _ EQ).
    - destruct ets as [|et [|et' ets']]; try discriminate.
      destruct efs as [|ef [|ef' efs']]; try discriminate.
      destruct a as [tys ck]. destruct tys as [|ty [|ty' tys']]; try discriminate.
      monadInv Htr. simpl.
      inversion IHt; subst. inversion IHf; subst.
      now rewrite (H1 _ EQ), (H3 _ EQ1).
    - destruct ets as [|et [|et' ets']]; try discriminate.
      destruct efs as [|ef [|ef' efs']]; try discriminate.
      destruct a as [tys ck]. destruct tys as [|ty [|ty' tys']]; try discriminate.
      monadInv Htr. simpl.
      inversion IHt; subst. inversion IHf; subst.
      match goal with H : to_lexp e = OK _ |- _ =>
        rewrite (to_lexp_fresh_nil _ _ H) end.
      match goal with H : to_cexp et = OK _ |- _ => rewrite (H1 _ H) end.
      match goal with H : to_cexp ef = OK _ |- _ => rewrite (H3 _ H) end.
      reflexivity.
    - discriminate.
  Qed.

  Lemma to_constant_fresh_nil :
    forall e k, to_constant e = OK k -> fresh_in e = [].
  Proof.
    induction e as [c|x a|op e a IHe|op e1 e2 a IHe1 IHe2|e0s es a IH0 IHs|e0s es a IH0 IHs|es x b a IHs|x ets efs a IHt IHf|e ets efs a IHe IHt IHf|f es ro a IHr IHs] using exp_ind2; intros k Htr; simpl in Htr;
      try discriminate.
    - reflexivity.
    - destruct es as [|e [|e' es']]; try discriminate.
      simpl. inversion IHs; subst. now rewrite (H1 _ Htr).
  Qed.

  Lemma mmap_to_lexp_fresh_nil :
    forall es les, Errors.mmap to_lexp es = OK les -> fresh_ins es = [].
  Proof.
    induction es as [|e es IH]; intros les Htr; [reflexivity|].
    simpl in Htr. monadInv Htr. unfold fresh_ins. simpl.
    rewrite (to_lexp_fresh_nil _ _ EQ).
    exact (IH _ EQ1).
  Qed.

  Opaque to_cexp to_lexp to_constant.

  Lemma to_equation_anon_nil :
    forall cenv envo eq eq',
      to_equation cenv envo eq = OK eq' -> anon_in_eq eq = [].
  Proof.
    intros cenv envo [xs es] eq' Htr.
    destruct es as [|e [|e' es']]; simpl in Htr; try discriminate.
    unfold anon_in_eq, anon_ins. simpl. rewrite app_nil_r.
    destruct e as [c|x a|op e a|op e1 e2 a|e0s es a|e0s es a|es x b a
                  |x ets efs a|e ets efs a|f es ro anns];
      try (destruct xs as [|x0 [|x1 xs']]; simpl in Htr; try discriminate;
           monadInv Htr;
           match goal with
           | H : to_cexp _ = OK _ |- _ => exact (to_cexp_fresh_nil _ _ H)
           end).
    - (* Efby *)
      destruct e0s as [|e0 [|e0' e0s']]; try (destruct xs as [|x0 [|x1 xs']];
        simpl in Htr; try discriminate; monadInv Htr;
        match goal with
        | H : to_cexp _ = OK _ |- _ => exact (to_cexp_fresh_nil _ _ H)
        end).
      destruct es as [|e1 [|e1' es']]; try (destruct xs as [|x0 [|x1 xs']];
        simpl in Htr; try discriminate; monadInv Htr;
        match goal with
        | H : to_cexp _ = OK _ |- _ => exact (to_cexp_fresh_nil _ _ H)
        end).
      destruct xs as [|x0 [|x1 xs']]; simpl in Htr; try discriminate.
      destruct (envo x0); simpl in Htr; try discriminate.
      monadInv Htr. simpl.
      rewrite (to_constant_fresh_nil _ _ EQ), (to_lexp_fresh_nil _ _ EQ0).
      reflexivity.
    - (* Eapp *)
      destruct ro as [er|]; simpl in Htr.
      + destruct er; try discriminate.
        destruct a as [ty [ckx nm]]. monadInv Htr. simpl.
        rewrite (mmap_to_lexp_fresh_nil _ _ EQ). reflexivity.
      + monadInv Htr. exact (mmap_to_lexp_fresh_nil _ _ EQ).
  Qed.

  Transparent to_cexp to_lexp to_constant.

  Lemma mmap_to_equation_anon_nil :
    forall cenv envo eqs neqs,
      Errors.mmap (to_equation cenv envo) eqs = OK neqs ->
      anon_in_eqs eqs = [].
  Proof.
    induction eqs as [|eq eqs IH]; intros neqs Htr; [reflexivity|].
    simpl in Htr. monadInv Htr. unfold anon_in_eqs. simpl.
    rewrite (to_equation_anon_nil _ _ _ _ EQ).
    exact (IH _ EQ1).
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

  Lemma to_node_anon_nil :
    forall n n' Hp,
      to_node n Hp = OK n' -> anon_in_eqs n.(n_eqs) = [].
  Proof.
    intros n n' Hp Htr. tonodeInv Htr.
    eapply mmap_to_equation_anon_nil; eauto.
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
    rewrite (to_node_anon_nil _ _ _ Htr). simpl map.
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

Module SecLNameGen
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import LSyn    : LSYNTAX  Ids Op)
  (CESyn          : CESYNTAX     Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import NAMEGEN : NAMEGEN  Ids Op CESyn NLSyn)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  <: SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR.

Include SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR.

End SecLNameGen.
