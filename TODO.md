# Active TODO

## Remaining theorem-stack cleanup

- Eliminate the remaining call-side assumptions from the final theorem stack:
  - `signatures_preserved_calls`
  - later: discharge `sec_not_in_gensym_prefs` from the concrete `Ident` naming
    setup so it stops living as a background correctness-module hypothesis

- Proof order:
  - checkpoint status:
    `successful_call_substitutions_fresh` is removed from the public theorem
    path after the node-scoped env pivot and the scoped-env rebuild of
    `generate_all_signatures_consistent_scoped'`
  - next: eliminate `signatures_preserved_calls`

- Preferred first approach for the call-side assumptions:
  - pivot `NameInterface.v` from one flat shared variable env to a node-scoped
    env-of-envs:
    - outer env keyed by unique node names
    - inner env keyed by raw variable/helper names local to that node
  - use that node-separated naming layer to make inter-node variable-name reuse
    legal by construction
  - then derive the caller/callee freshness facts from generated provenance in
    the node-scoped env, instead of leaving broad call-side assumptions in the
    final theorem stack
  - then derive the call-side freshness/preservation bridge from that stronger
    naming interface instead of leaving broad assumptions in the final theorem
    stack

- Migration order for the node-scoped naming pivot:
  - add the node-scoped env generation functions and lookup helpers in
    `NameInterface.v`
  - switch `SecNLusTyping.v` to fetch the current node’s local env before
    generating source constraints
  - switch `SecSTCTyping.v` similarly for translated STC systems
  - rebuild the correctness/provenance lemmas on top of the node-scoped env
  - migrate `SecNLusStcTranslation.v` from the old flat
    `generate_node_env`/`Env.t ident` theorem stack to the node-scoped env
    interfaces, then derive prefix-accumulator freshness there
  - current state:
    the node-scoped env migration is in place through the public lookup-based
    theorem, and the remaining work is now the semantic call-instantiation
    bridge behind `signatures_preserved_calls`

- Keep in mind:
  - inter-node reuse of the same raw input/local/output name must be allowed
  - only per-node no-dup conditions should remain required
  - `sec_not_in_gensym_prefs` is still to be discharged later from the
    concrete `Ident` setup

- Keep the active scoped preservation route stable:
  - `eqns_preserv_scoped`
  - `node_preserv_scoped`
  - `generated_node_preserv_scoped`
  - `generated_program_signatures_preserved_global`

- Keep deriving `env_injective` from `generate_node_env` via `NameInterface.v`.

## Structural cleanup after proofs stabilize

- Update the SIF markdown docs to reflect the post-refactor module ownership and theorem flow.
- Move the generic valuation-update agreement infrastructure out of
  `SecNLusStcTranslation.v` into `SecTypes.v`, in particular:
  - `upd_type`
  - `upd_ident`
  - `upd_types`
  - `upd_idents`
  - `upd_types_agree_on`
  - `upd_idents_agree_on`
- Move the remaining generic call-instantiation evaluation metatheory out of
  `SecNLusStcTranslation.v`, in particular the `hm_ext_*` substitution/update
  lemmas, into `SymTypes.v` / `SecTypes.v` where they match the underlying
  symbolic-type operations.
- Move the signature-instantiation completeness/correctness lemmas now being
  added in `SecNLusStcTranslation.v` into the signature layer
  (`SIFSignature.v`) once the final
  call-preservation proof is stable, in particular:
  - `call_actuals_scoped`
  - `call_subst_scoped`
  - `overlay_scope`
  - `overlay_scope_agree_on`
  - `overlay_scope_agree_outside`
  - `overlay_scope_agree_on_sig_scope`
  - `hm_ext_agree_on_scoped_type`
  - `subst_ident_constraint_complete_out`
  - `subst_ident_constraints_complete_out`
  - `subst_inp_ident_in_constraint_complete`
  - `subst_ident_in_constraints_complete`
  - `findST_none_notin_rhs`
  - `wf_constraints_of_singleton_perm`
  - `subst_rhs_ident_singletons_cons`
  - `subst_ident_constraints_shape_out_step`
  - `subst_constraints_out_map_shape_acc`
  - `subst_constraints_out_map_shape`
  - `signature_good_outputs_nodup`
  - `generate_constraints_complete_good`

- After each accepted proof step:
  - validate locally with direct `_CoqProject`-compatible `coqc`
  - validate globally with full repo `make`
  - then document, commit on `AI_version`, merge into `constraint_gen`, and push
