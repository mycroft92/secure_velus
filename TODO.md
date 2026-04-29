# Active TODO

## Remaining theorem-stack cleanup

- Eliminate the remaining call-side assumptions from the final theorem stack:
  - `successful_call_substitutions_fresh`
  - `signatures_preserved_calls`

- Proof order:
  - eliminate `successful_call_substitutions_fresh`
  - then eliminate `signatures_preserved_calls`

- Preferred first approach for the call-side assumptions:
  - strengthen `NameInterface.v` so the required caller/callee namespace
    separation holds by construction or by direct naming-layer theorems
  - then derive the call-side freshness/preservation bridge from that stronger
    naming interface instead of leaving broad assumptions in the final theorem
    stack

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
