Current proof state:

- the correctness split is in place:
  - `SecNLusTypingCorrectness.v`
  - `SecStcTypingCorrectness.v`
- `SecNLusStcTranslation.v` now keeps the cross-phase proof layer
- the full repo `make` succeeds in the current branch state

Remaining proof work:

- discharge
  `signatures_preserved_calls`
  from the final theorem stack
- `successful_call_substitutions_fresh` is already gone from the public theorem
  path; the remaining blocker is the semantic call bridge itself
- the current call-instantiation metatheory now includes:
  - output-substitution correctness/completeness
  - input-substitution completeness
  - reverse-order valuation reconstructions (`upd_types_rev`, `upd_idents_rev`)
- the next step is to relate those reverse-order reconstructions back to the
  forward `inst_valuation` under the generated freshness/distinctness facts,
  then use that to prove the theorem replacing `signatures_preserved_calls`
- the flat shared-variable env in `NameInterface.v` is now identified as too
  strong: two different nodes may legally reuse the same raw variable name, so
  the naming layer must move to a node-scoped env-of-envs before the final
  call-freshness proof can be completed cleanly
- resume by migrating `NameInterface.v`, `SecNLusTyping.v`, and
  `SecSTCTyping.v` to that node-scoped naming representation first
- keep deriving `env_injective` from `generate_node_env` through
  `NameInterface.v`

Public theorem structure:

- `generated_program_preserv_global` keeps the raw preservation statement
- `generated_program_signatures_preserved_global` gives the signature-level
  lookup corollary over the generated globals, without exposing internal locals
  or rerunning per-node signature generation

Validation discipline:

- use `_CoqProject`-compatible `coqc` for local debugging
- require full repo `make` before commit, merge, or push
