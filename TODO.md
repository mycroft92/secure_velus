# Active TODO

## Remaining theorem-stack cleanup

- Eliminate the remaining call-side assumptions from the final theorem stack:
  - `successful_call_substitutions_fresh`
  - `signatures_preserved_calls`
  - later: discharge `sec_not_in_gensym_prefs` from the concrete `Ident` naming
    setup so it stops living as a background correctness-module hypothesis

- Proof order:
  - eliminate `successful_call_substitutions_fresh`
  - then eliminate `signatures_preserved_calls`

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
  - immediate blocker in `SecNLusStcTranslation.v`:
    `generate_all_signatures_consistent_scoped'` still needs a
    prefix-generated accumulator provenance invariant, because the new
    generated-node bridge now consumes caller-scope freshness for the current
    node instead of the old global
    `successful_call_substitutions_fresh` premise
  - then resume elimination of
    `successful_call_substitutions_fresh`
    and
    `signatures_preserved_calls`

- Keep in mind:
  - inter-node reuse of the same raw input/local/output name must be allowed
  - only per-node no-dup conditions should remain required
  - `sec_not_in_gensym_prefs` is still to be discharged later from the
    concrete `Ident` setup

- Keep the active scoped preservation route stable:
  - `eqns_preserv_scoped`
  - `node_preserv_scoped`
  - `generated_node_preserv_scoped`
  - `generated_program_preserv_global`
  - `generated_program_signatures_preserved_global`

- Keep deriving `env_injective` from `generate_node_env` via `NameInterface.v`.

## Structural cleanup after proofs stabilize

- Update the SIF markdown docs to reflect the post-refactor module ownership and theorem flow.

- After each accepted proof step:
  - validate locally with direct `_CoqProject`-compatible `coqc`
  - validate globally with full repo `make`
  - then document, commit on `AI_version`, merge into `constraint_gen`, and push
