(** * The next statements, for proof

    NOT PART OF THE BUILD: not in [vfiles], so the compiled tree stays
    admit-free.  Both blocks below were checked by pasting them into throwaway
    copies of their target files and compiling, so they typecheck where they go.

    WHERE EACH BLOCK GOES
      Block A -> src/SIF/SecLusUnnestingNodes.v, inside Section NodeEquations,
                 before [End NodeEquations.]
      Block B -> src/SIF/SecLusNormFby.v, inside Section NormFbyNode,
                 before [End NormFbyNode.]

    WHERE THIS LEAVES THE LEG.  [normalize_signatures_weaken] (already proved)
    reduces preservation across normalisation to two per-node steps, one per
    pass.  Block A is Leg U's step, Block B is Leg I's, plus the one substantial
    thing Leg I still owes -- that a good level assignment exists for a node's
    run.  After those two, the only hypotheses left in the program-level
    statement are NOT phase-specific:

      (i)  the [A eq] ambients in Block A, which the pointwise (streams)
           contract exists to remove, and whose last piece is
           [carries_Eapp_streams];
      (ii) the program-level facts listed at the bottom of this file -- the
           naming pass's two lookups, and that a *generated Lustre* signature is
           good, scoped and has a duplicate-free scope.

    (ii) cannot be stated in either file: those facts are about
    [generate_all_lsignatures_scoped_env], which is built after
    SecLusUnnesting.v in the build order.  They need a new file, so they are
    given as prose at the bottom rather than as checked statements. *)

(* ================================================================== *)
(* BLOCK A -- SecLusUnnestingNodes.v, Section NodeEquations           *)
(* ================================================================== *)

    (** * Leg U's per-node step

        The counterpart of Leg I's, and the last thing between
        [unnest_global_signatures_weaken] and a program-level statement with no
        phase-specific hypotheses left.

        [unnest_node_entailment] supplies the entailment,
        [unnest_node_signatures_preserved_decoupled] the interface equality and
        the transport through [simplify], and [sig_call_weakens_from_good]
        converts the pair into what the lockstep consumes.

        Two families of hypothesis remain, and neither is phase-specific:

          the [A eq] ambients -- which is what the pointwise (streams) contract
          exists to remove, and which [carries_Eapp_streams] is the last piece
          of;

          and the program-level facts -- the naming pass's two lookups, and that
          a *generated Lustre* signature is good, scoped and has a
          duplicate-free scope.  Those are the Lustre analogue of what
          SecNLusTypingCorrectness.v proves for NLustre; they sit after
          SecLusUnnesting.v in the build order, so they enter here as
          hypotheses. *)
    Corollary unnest_node_step :
      forall (P Q : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs)
             (envs : node_scoped_env) (aux : list node_aux_names)
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        (** the naming pass, read at this node *)
        find_node_env n.(n_name) envs = Some env ->
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        cenv = lnode_clock_env (unnest_node P n Hwl Hpref) ->
        (** the pass's output is unnested, which makes the target run pure *)
        Forall (unnested_equation Q) (unnest_node P n Hwl Hpref).(n_eqs) ->
        (** the node is well formed and well clocked *)
        Forall (wl_equation P) n.(n_eqs) ->
        Forall (wc_equation P vars) n.(n_eqs) ->
        (** what the run minted is outside the visible scope *)
        (forall y,
            In y (moved_by env init_st
                    (snd (unnest_equations P n.(n_eqs) init_st))) ->
            ~ In y scope) ->
        (** the ambient premises: what the streams contract removes *)
        (forall eq eqs1 q q',
            In eq n.(n_eqs) -> unnest_equation P eq q = (eqs1, q') ->
            forall y ck ckty,
              In y (vars_defined eqs1) -> find_clock cenv y = OK ck ->
              assign_clk_type env base_ty ck = Some ckty ->
              incl (merge [rst_ty] ckty) (A eq)) ->
        (forall ce dlt,
            generate_leqns_constraints accT env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, stS1) ->
            listSatisfiable dlt ce ->
            forall eq b, In eq n.(n_eqs) -> In b (sec_of env (fst eq)) ->
              satisfiable dlt (A eq) [b]) ->
        (** the source run's own hygiene *)
        (forall ce ct1,
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, ct1) ->
            wf_constraints ce /\ constraints_scoped scope ce /\ sec_le ct1 stF) ->
        (forall ce ct1,
            generate_leqns_constraints accT env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, ct1) ->
            constraints_scoped scope ce /\ sec_le ct1 stF) ->
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (cns, ct1) ->
            forall y, In y (locals ++ minted stS0 ct1) -> ~ In y scope) ->
        (** and the program-level facts about the published pair *)
        signature_good sgS ->
        NoDup (signature_scope sgS) ->
        signature_good sgT ->
        signature_scoped sgT ->
        (forall z, In z (signature_scope sgS) -> In z scope) ->
        (forall inp ck rst os cns sa sb,
            generate_constraints sgS inp ck rst os sa = OK (cns, sb) ->
            call_subst_fresh sgS inp ck rst os /\ NoDup os) ->
        call_weakens accS accT ->
        generate_lnode_sig_scoped_env accS n envs aux stS0 = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT (unnest_node P n Hwl Hpref)
          envs aux stT0 = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
    Admitted.

(* ================================================================== *)
(* BLOCK B -- SecLusNormFby.v, Section NormFbyNode                    *)
(* ================================================================== *)

    (** ** The assignment a node's run needs, built

        The one substantial thing Leg I still owes.  [normfby_node_entailment]
        takes the level assignment as a parameter; this says a good one exists
        for the run [normfby_node] performs, which is what lets the parameter be
        eliminated.

        The construction is one entry per created variable -- a flag gets its
        clock's ambient, a delayed variable gets the ambient joined with its own
        delayed operand's type -- so the only real work is the three hygiene
        conditions:

          [levels_visible]   each level is built from [rst_ty], a clock type and
                             an operand type, all visible;
          [created_hidden]   a created variable's security name is not visible,
                             which is the premise below;
          [levels_functional] two entries for one name must agree.  A shared
                             flag contributes the same level twice, because a
                             flag's level is a function of its clock.  Two
                             delayed variables are distinct identifiers, by
                             [NoDup (st_ids stf)] with [fresh_ident_vars_perm];
                             and a flag is never a delayed variable, because the
                             state records one annotation per identifier and the
                             two differ in their [isinit] bit. *)
    Lemma node_pairs_exists :
      forall to_cut (eqs : list equation) eqs' stf,
        map_bind (fby_equation to_cut) eqs init_st = (eqs', stf) ->
        (** the naming pass covers the variables the run created, outside the
            visible scope *)
        (forall v a, In (v, a) (st_anns stf) ->
            exists b, Env.find v env = Some b /\ ~ In b scope) ->
        env_injective env ->
        (** and it created each identifier once *)
        NoDup (st_ids stf) ->
        (** the clock of every created variable is the one recorded with it *)
        (forall v a, In (v, a) (st_anns stf) ->
            exists ckty, assign_clk_type env base_ty (snd (fst a)) = Some ckty
                         /\ (forall z, In z ckty -> In z scope)) ->
        (** and what the node says about each delayed equation, minus the
            assignment itself *)
        (forall x e0 e ty ck name,
            In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) eqs
            \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) eqs ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ (forall q, assign_lexp_type G env base_ty rst_ty e0 q
                            = OK ([(s0, [])], q))
              /\ (forall q, assign_lexp_type G env base_ty rst_ty e q
                            = OK ([(s1, [])], q))
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        exists pairs,
          levels_functional pairs
          /\ created_hidden pairs
          /\ levels_visible pairs
          /\ Forall2 (fby_eqn_data pairs) eqs eqs'
          /\ (forall i cki ckti bi,
                 In (i, ((bool_type, cki), true)) (st_anns stf) ->
                 assign_clk_type env base_ty cki = Some ckti ->
                 Env.find i env = Some bi ->
                 In (bi, merge [rst_ty] ckti) pairs).
    Admitted.

    (** ** Leg I's per-node step, with the assignment eliminated

        [node_pairs_exists] feeds [normfby_node_entailment], which feeds
        [normfby_node_signatures_preserved_decoupled], which with
        [sig_call_weakens_from_good] gives what the lockstep consumes.  What is
        left as hypotheses are the program-level facts: the naming pass's two
        lookups, and that a *generated Lustre* signature is good, scoped and has
        a duplicate-free scope -- the Lustre analogue of what
        SecNLusTypingCorrectness.v proves for NLustre, and which lives after
        SecLusUnnesting.v in the build order. *)
    Corollary normfby_node_step :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs) (Q' : global)
             (envs : node_scoped_env) (aux : list node_aux_names)
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        (** the naming pass, read at this node *)
        find_node_env n.(n_name) envs = Some env ->
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        cenv = lnode_clock_env (normfby_node Q c n Hunt Hpref) ->
        (** the pass's output is unnested, which makes the target run pure *)
        Forall (unnested_equation Q')
          (normfby_node Q c n Hunt Hpref).(n_eqs) ->
        (** the hypotheses [node_pairs_exists] asks for, at this node *)
        env_injective env ->
        (forall eqs' stf,
            map_bind (fby_equation
                        (PS.union c (ps_from_list (List.map fst (n_out n)))))
              n.(n_eqs) init_st = (eqs', stf) ->
            (forall v a, In (v, a) (st_anns stf) ->
                exists b, Env.find v env = Some b /\ ~ In b scope)
            /\ NoDup (st_ids stf)
            /\ (forall v a, In (v, a) (st_anns stf) ->
                   exists ckty,
                     assign_clk_type env base_ty (snd (fst a)) = Some ckty
                     /\ (forall z, In z ckty -> In z scope))) ->
        (forall x e0 e ty ck name,
            In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) n.(n_eqs)
            \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) n.(n_eqs) ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ (forall q, assign_lexp_type G env base_ty rst_ty e0 q
                            = OK ([(s0, [])], q))
              /\ (forall q, assign_lexp_type G env base_ty rst_ty e q
                            = OK ([(s1, [])], q))
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)) ->
        (** the source run's own hygiene, as the node theorem asks *)
        (forall ce ct1,
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (ce, ct1) ->
            wf_constraints ce /\ constraints_scoped scope ce) ->
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints accS env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS0 = OK (cns, ct1) ->
            forall y, In y (locals ++ minted stS0 ct1) -> ~ In y scope) ->
        (** and the program-level facts about the published pair *)
        signature_good sgS ->
        NoDup (signature_scope sgS) ->
        signature_good sgT ->
        signature_scoped sgT ->
        (forall z, In z (signature_scope sgS) -> In z scope) ->
        (forall inp ck rst os cns sa sb,
            generate_constraints sgS inp ck rst os sa = OK (cns, sb) ->
            call_subst_fresh sgS inp ck rst os /\ NoDup os) ->
        call_weakens accS accT ->
        generate_lnode_sig_scoped_env accS n envs aux stS0 = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT (normfby_node Q c n Hunt Hpref)
          envs aux stT0 = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
    Admitted.

(* ================================================================== *)
(* AFTERWARDS -- a new file, after SecLusUnnesting.v / SecLusNormFby.v *)
(* ================================================================== *)

(** These are the Lustre analogue of what SecNLusTypingCorrectness.v proves for
    NLustre, and they are what Blocks A and B take as hypotheses.  Each is about
    a signature the Lustre generator PUBLISHES, so each is a statement about
    [generate_lnode_sig] / [generate_all_lsignatures_scoped_env]:

      generate_lnode_sig_good
        generate_lnode_sig G n env aux st = OK (sg, st') -> signature_good sg
      -- that is, wf_constraints on the published constraints and one constraint
         per output.  [simplify] is what arranges it: it keeps exactly the
         interface, and the raw constraints already target one name each.

      generate_lnode_sig_scoped
        ... -> signature_scoped sg
      -- every name the published constraints mention is in
         [signature_scope sg].  This is the fact [simplify] was given the locals
         and the minted names for; the elimination is what makes it true, and
         the plan's "one naming pass" decision is why the interface names are
         the ones left.

      generate_lnode_sig_scope_nodup
        ... -> NoDup (signature_scope sg)
      -- from [env] injective and [n_nodup]: the interface variables are
         distinct, so their security names are.

      generate_lnode_sig_instantiations
        ... -> forall inp ck rst os cns sa sb,
                 generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
                 call_subst_fresh sg inp ck rst os /\ NoDup os
      -- the separation between a callee's formals and a caller's actuals, and
         the distinctness of the actuals.  Stated, as everywhere else in this
         development, as a property of the instantiations the generator actually
         makes rather than of arbitrary actuals -- which is what makes it true.

      generate_lnode_scoped_env_at_node
        generate_lnode_scoped_env G = OK (envs, aux) ->
        In n G ->
        exists env, find_node_env n.(n_name) envs = Some env
                    /\ forall clk_id rst_id,
                         get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
                         Env.find clk_id env = Some <the node's base name>
                         /\ Env.find rst_id env = Some <the node's reset name>
      -- the naming pass read at one node.  SecLNameInterface.v has the pieces;
         Leg A's [generate_all_signatures_entails_scoped'] splits the same run at
         a node and is the template.

    One caution, learned twice on this leg: state each of these about the run
    the generator ACTUALLY performs, not about a description of it.  A premise
    quantified over all states, or keyed on a recorded annotation, speaks about
    identifiers the pass never created -- and is then unsatisfiable.  See
    work_docs/LegI_audit_2026_09_29.v. *)
