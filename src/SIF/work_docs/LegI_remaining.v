(** * Leg I: the remaining statements, for proof

    NOT PART OF THE BUILD.  This file is not in [vfiles]; the compiled tree
    stays admit-free.  Everything here is stated and nothing is proved.

    WHERE IT GOES.  Paste the whole block into [src/SIF/SecLusNormFby.v],
    inside [Section NormFbyNode], immediately before [End NormFbyNode.].  At
    that point [env], [base_ty], [rst_ty], [scope], [G] and [cenv] are section
    variables, which is why none of the statements below mention them as
    arguments.  Everything the block refers to -- [upds], [hm_ext],
    [preserves_on], [add_whens_const_type], [generate_leqns_cons_inv],
    [generate_ldef_constraint_eq], [fby_equation_spec], [fby_iteexp_created],
    [call_weakens], [sig_head_weakens], [state_pure_generate_leqns],
    [normfby_node_sig_interface], [generate_leqns_normfby_node_cenv] -- is
    already proved, either in that file or upstream of it.

    WHY THIS SHAPE, AND NOT THE OBVIOUS ONE.  The obvious composition -- prove
    [preserves_on] per equation and assemble the chunks with
    [preserves_on_concat_list] -- does not work, and the obstruction is a fact
    about the pass.  [init_var_for_clock] *reuses* an initialisation flag:

      | Some (x, _) => ((x, []), st)          (* reuse: creates nothing *)

    so two [arrow]s (or two non-constant [fby]s) on the same clock share one
    flag.  The first group creates it and emits its equation; the second merely
    mentions it.  Both groups' created-name sets then contain that flag, so
    [NoDup (concat extras)] -- which [preserves_on_concat_list] requires -- is
    false.  Nor may the flag be dropped from the second group's set (its
    constraint mentions the name, so the chunk would not be scoped) or put into
    [scope] (then the witness could not move it, and the flag's own equation
    would have nothing to make it hold).

    So the composition is done ONCE over the whole body, with a level *per
    created name* instead of one level per chunk.  A created name's level is
    the left-hand side of the target constraint that DEFINES it:

      - a flag on clock [ck] gets [merge [rst_ty] ckty], its clock's ambient;
      - a [px] gets [merge (merge [rst_ty] ckty) s1], where [s1] is the type of
        the delayed operand of the equation it was created for.

    Three things make this work, and they are exactly what the per-chunk route
    missed:

      1. it is UNIFORM ON THE SHARED NAME -- a flag's level depends only on its
         clock, so every equation mentioning it wants the same one, which is
         why sharing stops being a problem;
      2. [NoDup] IS RECOVERED -- the created names are collected once globally,
         not per chunk, so each appears exactly once;
      3. the assignment IS NOT CIRCULAR -- a created name's defining constraint
         mentions only visible names (clock samplers, and the delayed operand's
         type), never another created name, so the levels are values of the
         original valuation and nothing has to be solved.

    The three [_roles] lemmas below REPLACE [fby_cut_entails], [arrow_entails]
    and [fby_ite_entails].  Their membership arguments carry over verbatim from
    the proofs already in the file -- only the packaging changes, from a
    [preserves_on] to a [Forall2] of per-constraint facts.  Delete the three
    [_entails] lemmas and [preserves_on_fresh_names] once these are proved.

    Full discussion: work_docs/Lus2NLusSIF_plan.md, "CORRECTION 2026-09-27". *)

(* ------------------------------------------------------------------ *)
(* paste from here                                                    *)
(* ------------------------------------------------------------------ *)

    (** ** What one target constraint does *)

    Inductive target_role : Type :=
    (** it defines a name the pass created *)
    | Defines (d : ident)
    (** it bounds a visible name, and [M] is the source level bounding it *)
    | Bounds (d : ident) (M : ST).

    (** A created name's level has to be big enough for every constraint that
        defines it, and small enough for every constraint that uses it.  Hence
        containment in both clauses rather than equality: the flag's canonical
        level is its clock's ambient, which *contains* the left-hand side of
        its own equation (a constant under [when]s adds only samplers) and is
        *contained* in the ambient of every equation that mentions it. *)
    Definition role_shape (pairs : list (ident * ST))
      (c : constraint) (r : target_role) : Prop :=
      match r with
      | Defines d =>
          snd c = [d]
          /\ exists L, In (d, L) pairs /\ (forall z, In z (fst c) -> In z L)
      | Bounds d M =>
          snd c = [d]
          /\ In d scope
          /\ (forall z, In z M -> In z scope)
          /\ (forall z, In z (fst c) ->
                In z M
                \/ exists L, In (z, L) pairs /\ (forall w, In w L -> In w M))
      end.

    Definition role_bound (dlt : ident -> Lat.t)
      (c : constraint) (r : target_role) : Prop :=
      match r with
      | Defines _ => True
      | Bounds d M => hm_ext dlt M ⊑ hm_ext dlt [d]
      end.

    Definition created_hidden (pairs : list (ident * ST)) : Prop :=
      forall y L, In (y, L) pairs -> ~ In y scope.

    Definition levels_visible (pairs : list (ident * ST)) : Prop :=
      forall y L z, In (y, L) pairs -> In z L -> In z scope.

    (** ** The move, once, for a whole body *)

    Lemma upds_pairs_val :
      forall (pairs : list (ident * ST)) dlt y L,
        NoDup (List.map fst pairs) ->
        In (y, L) pairs ->
        upds (List.map fst pairs)
             (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt y
        = hm_ext dlt L.
    Admitted.

    Lemma upds_pairs_off :
      forall (pairs : list (ident * ST)) dlt z,
        ~ In z (List.map fst pairs) ->
        upds (List.map fst pairs)
             (List.map (fun p => hm_ext dlt (snd p)) pairs) dlt z
        = dlt z.
    Admitted.

    (** The witness is [upds (map fst pairs) (map (hm_ext dlt o snd) pairs) dlt].
        [levels_visible] is what makes that well defined: a level mentions no
        created name, so its value is the same before and after the update.

        This replaces [preserves_on_fresh_names], and is applied ONCE, at the
        node -- not per equation. *)
    Lemma preserves_on_created :
      forall (pairs : list (ident * ST)) (roles : list target_role) ce cet,
        NoDup (List.map fst pairs) ->
        created_hidden pairs ->
        levels_visible pairs ->
        Forall2 (role_shape pairs) cet roles ->
        (forall dlt, listSatisfiable dlt ce ->
           Forall2 (role_bound dlt) cet roles) ->
        preserves_on scope ce cet
        /\ constraints_scoped (scope ++ List.map fst pairs) cet.
    Admitted.

    (** ** The three shapes, repackaged

        Each keeps the premises of the corresponding [_entails] lemma and adds
        one membership fact per created name: its entry in the global
        assignment.  The proofs are the existing ones with the final
        [eapply preserves_on_fresh_names] replaced by an [exists roles]. *)

    Lemma fby_cut_roles :
      forall pairs x x' e0 e ann ck ckty s0 s1 b b' st ce cet u u',
        find_clock cenv x  = OK ck ->
        find_clock cenv x' = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find x' env = Some b' ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        (** the cut variable carries the source equation's own right-hand side,
            which is exactly what its new equation bounds *)
        In (b', merge (merge [rst_ty] ckty) (merge s0 s1)) pairs ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [ann]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])] st
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Admitted.

    Lemma arrow_roles :
      forall pairs x i e0 e ty ck name ckty s0 s1 b bi st ce cet u u' eqs,
        find_clock cenv x = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x env = Some b ->
        Env.find i env = Some bi ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        (** the flag's entry is its clock's ambient -- the same whichever
            equation created it, which is what makes sharing harmless *)
        In (bi, merge [rst_ty] ckty) pairs ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0] [e]
                    ([ty], (ck, name))]) :: eqs) st = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Admitted.

    Lemma fby_ite_roles :
      forall pairs x i px e0 e ty ck name ckty s0 s1 b bi bp st ce cet u u' eqs,
        find_clock cenv x  = OK ck ->
        find_clock cenv px = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        Env.find x  env = Some b ->
        Env.find i  env = Some bi ->
        Env.find px env = Some bp ->
        assign_lexp_type G env base_ty rst_ty e0 st = OK ([(s0, [])], st) ->
        assign_lexp_type G env base_ty rst_ty e  st = OK ([(s1, [])], st) ->
        (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                   In z scope) ->
        In b scope ->
        In (bi, merge [rst_ty] ckty) pairs ->
        (** [px] carries the ambient joined with the *delayed* operand's type:
            enough for its own equation, and inside the ambient of the [ite]
            that uses it -- the latter only because the source [fby] rule types
            both operands *)
        In (bp, merge (merge [rst_ty] ckty) s1) pairs ->
        (eqs = []
         \/ (find_clock cenv i = OK ck
             /\ eqs = [([i], [Efby [add_whens (Econst true_const) bool_type ck]
                                   [add_whens (Econst false_const) bool_type ck]
                                   [(bool_type, (ck, None))]])])) ->
        generate_leqn_constraint G env base_ty rst_ty cenv
          ([x], [Efby [e0] [e] [(ty, (ck, name))]]) st = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
           :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                        [(ty, (ck, name))]])
           :: eqs) st = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Admitted.

    (** ** One equation, whatever shape it has

        The dispatch, as [fby_equation_entails] already does it: split with
        [fby_equation_spec], read the created variables off the fresh state with
        [fby_iteexp_created] / [arrow_iteexp_created], and quote the case
        lemma.  On the two shapes the pass leaves alone the two runs are the
        same run, and every constraint takes a [Bounds] role with [M] its own
        left-hand side. *)
    Theorem fby_equation_roles :
      forall pairs to_cut xs es eqs' st st' ce cet s u u',
        fby_equation to_cut (xs, es) st = (eqs', st') ->
        (** what the node says about this equation, and the entry its [px]
            needs; vacuous on the shapes that create nothing *)
        (forall x e0 e ty ck name,
            xs = [x] ->
            (es = [Efby [e0] [e] [(ty, (ck, name))]]
             \/ es = [Earrow [e0] [e] [(ty, (ck, name))]]) ->
            exists ckty s0 s1 b,
              find_clock cenv x = OK ck
              /\ assign_clk_type env base_ty ck = Some ckty
              /\ Env.find x env = Some b
              /\ In b scope
              /\ assign_lexp_type G env base_ty rst_ty e0 s = OK ([(s0, [])], s)
              /\ assign_lexp_type G env base_ty rst_ty e  s = OK ([(s1, [])], s)
              /\ (forall z, In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                            In z scope)
              /\ (forall px bp,
                     In (px, ((ty, ck), false)) (st_anns st') ->
                     Env.find px env = Some bp ->
                     In (bp, merge (merge [rst_ty] ckty) s1) pairs)) ->
        (** and about every flag: its clock, its name, and its entry *)
        (forall y a, In (y, a) (st_anns st') ->
            find_clock cenv y = OK (snd (fst a))
            /\ exists c, Env.find y env = Some c /\ ~ In c scope) ->
        (forall i cki ckti bi,
            In (i, ((bool_type, cki), true)) (st_anns st') ->
            assign_clk_type env base_ty cki = Some ckti ->
            Env.find i env = Some bi ->
            In (bi, merge [rst_ty] ckti) pairs) ->
        (** the source's own constraints are visible, for the unchanged shapes *)
        constraints_scoped scope ce ->
        generate_leqn_constraint G env base_ty rst_ty cenv (xs, es) s
          = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv eqs' s
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Admitted.

    (** ** A node's equation list

        Induction on [eqs].  The two [Forall2]s compose with [Forall2_app], and
        the source's satisfaction splits with [Forall_app], so there is no
        disjointness bookkeeping at all -- that is the payoff of moving the
        composition out of the chunks.

        The operand types are given at *any* state because the operands are
        normalized, so [assign_lexp_normalized_pure] makes their runs
        restartable; that is what keeps the induction from having to track the
        states.  [map_bind_st_follows] weakens the [st_anns st'] premises from
        the whole run to each step. *)
    Theorem fby_equations_roles :
      forall pairs to_cut eqs eqs' st st' ce cet s u u',
        map_bind (fby_equation to_cut) eqs st = (eqs', st') ->
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
                            In z scope)
              /\ (forall px bp,
                     In (px, ((ty, ck), false)) (st_anns st') ->
                     Env.find px env = Some bp ->
                     In (bp, merge (merge [rst_ty] ckty) s1) pairs)) ->
        (forall y a, In (y, a) (st_anns st') ->
            find_clock cenv y = OK (snd (fst a))
            /\ exists c, Env.find y env = Some c /\ ~ In c scope) ->
        (forall i cki ckti bi,
            In (i, ((bool_type, cki), true)) (st_anns st') ->
            assign_clk_type env base_ty cki = Some ckti ->
            Env.find i env = Some bi ->
            In (bi, merge [rst_ty] ckti) pairs) ->
        constraints_scoped scope ce ->
        generate_leqns_constraints G env base_ty rst_ty cenv eqs s = OK (ce, u) ->
        generate_leqns_constraints G env base_ty rst_ty cenv (List.concat eqs') s
          = OK (cet, u') ->
        exists roles,
          Forall2 (role_shape pairs) cet roles
          /\ (forall dlt, listSatisfiable dlt ce ->
                Forall2 (role_bound dlt) cet roles).
    Admitted.

    (** ** The equation-level entailment, for a node

        [fby_equations_roles] followed by [preserves_on_created], with
        [normfby_node_fields] to identify the target equation list with
        [concat eqs'] and [generate_leqns_normfby_node_cenv] to read the source
        equations against the target's clock environment. *)
    Corollary normfby_node_entailment :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             pairs st0 ce cet ct1 ct1',
        cenv = lnode_clock_env (normfby_node Q c n Hunt Hpref) ->
        NoDup (List.map fst pairs) ->
        created_hidden pairs ->
        levels_visible pairs ->
        (** the per-equation and per-created-variable data, for this node's run;
            same two hypotheses as [fby_equations_roles], with [eqs := n_eqs n]
            and the run being the one [normfby_node] performs *)
        (forall eqs' stf,
            map_bind (fby_equation
                        (PS.union c (ps_from_list (List.map fst (n_out n)))))
              n.(n_eqs) init_st = (eqs', stf) ->
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
                  /\ (forall z,
                         In z (merge (merge [rst_ty] ckty) (merge s0 s1)) ->
                         In z scope)
                  /\ (forall px bp,
                         In (px, ((ty, ck), false)) (st_anns stf) ->
                         Env.find px env = Some bp ->
                         In (bp, merge (merge [rst_ty] ckty) s1) pairs))
            /\ (forall y a, In (y, a) (st_anns stf) ->
                   find_clock cenv y = OK (snd (fst a))
                   /\ exists d, Env.find y env = Some d /\ ~ In d scope)
            /\ (forall i cki ckti bi,
                   In (i, ((bool_type, cki), true)) (st_anns stf) ->
                   assign_clk_type env base_ty cki = Some ckti ->
                   Env.find i env = Some bi ->
                   In (bi, merge [rst_ty] ckti) pairs)) ->
        constraints_scoped scope ce ->
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env n) n.(n_eqs) st0 = OK (ce, ct1) ->
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env (normfby_node Q c n Hunt Hpref))
          (normfby_node Q c n Hunt Hpref).(n_eqs) st0 = OK (cet, ct1') ->
        preserves_on scope ce cet.
    Admitted.

    (** ** Signature preservation for one node, two accumulators, two states

        A near-copy of Leg U's [unnest_node_signatures_preserved_decoupled]:
        [normfby_node_sig_interface] for the five interface fields,
        [generate_leqns_constraints_weaken] for the intermediate run against the
        target accumulator, [state_pure_generate_leqns] to restart the target
        run at the source's state, and [preserves_on_simplify] through both
        eliminations. *)
    Theorem normfby_node_signatures_preserved_decoupled :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (Q' : global) (G1 G2 : secglobal) (aux : list node_aux_names)
             stS stT sg stS1 sg' stT1,
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        (** the pass's output is unnested, which is what makes it state-pure *)
        Forall (unnested_equation Q')
          (normfby_node Q c n Hunt Hpref).(n_eqs) ->
        call_weakens G1 G2 ->
        (forall ce cet ct1 ct1',
            generate_leqns_constraints G2 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (ce, ct1) ->
            generate_leqns_constraints G2 env base_ty rst_ty
              (lnode_clock_env (normfby_node Q c n Hunt Hpref))
              (normfby_node Q c n Hunt Hpref).(n_eqs) stS = OK (cet, ct1') ->
            preserves_on scope ce cet) ->
        (forall ce ct1,
            generate_leqns_constraints G1 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (ce, ct1) ->
            wf_constraints ce) ->
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints G1 env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) stS = OK (cns, ct1) ->
            forall x, In x (locals ++ minted stS ct1) -> ~ In x scope) ->
        generate_lnode_sig G1 n env aux stS = OK (sg, stS1) ->
        generate_lnode_sig G2 (normfby_node Q c n Hunt Hpref) env aux stT
          = OK (sg', stT1) ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg
        /\ preserves_on scope sg.(s_constraints) sg'.(s_constraints).
    Admitted.

    (** ** The per-node step the shared lockstep consumes

        [sig_call_weakens_from_good] turns the interface equality and the
        entailment into [sig_call_weakens].  The goodness and scopedness of the
        two *published* signatures are the Lustre analogue of what
        [SecNLusTypingCorrectness.v] proves for NLustre; they live after
        [SecLusUnnesting.v] in the build order, so they enter here as
        hypotheses, exactly as Leg A's [node_step_entails] leaves its own. *)
    Corollary normfby_node_step_weakens :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (envs : node_scoped_env) (aux : list node_aux_names)
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        find_node_env n.(n_name) envs = Some env ->
        call_weakens accS accT ->
        (** what this node's two runs give, from the theorem above *)
        (s_name sgT = s_name sgS
         /\ s_in sgT = s_in sgS
         /\ s_out sgT = s_out sgS
         /\ s_clk sgT = s_clk sgS
         /\ s_reset sgT = s_reset sgS
         /\ preserves_on scope sgS.(s_constraints) sgT.(s_constraints)) ->
        (** and what the program level knows about the published pair *)
        signature_good sgS ->
        NoDup (signature_scope sgS) ->
        signature_good sgT ->
        signature_scoped sgT ->
        (forall z, In z (signature_scope sgS) -> In z scope) ->
        (forall inp ck rst os cns sa sb,
            generate_constraints sgS inp ck rst os sa = OK (cns, sb) ->
            call_subst_fresh sgS inp ck rst os /\ NoDup os) ->
        generate_lnode_sig_scoped_env accS n envs aux stS0 = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT (normfby_node Q c n Hunt Hpref)
          envs aux stT0 = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
    Admitted.

    (** ** The whole program

        This one should follow directly, with nothing new:
        [generate_all_lsignatures_weakens] instantiated at
        [R := fun n m => exists Q c Hunt Hpref, m = normfby_node Q c n Hunt Hpref],
        with [normfby_global_normfbyed_nodes] and [normfbyed_nodes_rev] for the
        node lists and [normfby_node_step_weakens] for the step. *)
    Corollary normfby_global_signatures_weaken :
      forall (P : global) Hunt Hprefs (envs : node_scoped_env)
             (aux : list node_aux_names) stS stT GSout GTout,
        (forall accS accT nS nT sgS stS0 stS1 sgT stT0 stT1,
            (exists Q c (Hu : unnested_node Q nS)
                      (Hp : n_prefixes nS = norm1_prefs),
                nT = normfby_node Q c nS Hu Hp) ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envs aux stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nT envs aux stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        generate_all_lsignatures_scoped_env (rev P) envs aux stS = OK GSout ->
        generate_all_lsignatures_scoped_env
          (rev (normfby_global P Hunt Hprefs)) envs aux stT = OK GTout ->
        call_weakens GSout GTout.
    Admitted.

(* ------------------------------------------------------------------ *)
(* to here                                                            *)
(* ------------------------------------------------------------------ *)
