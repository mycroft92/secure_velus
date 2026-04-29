Current proof state:

- the correctness split is in place:
  - `SecNLusTypingCorrectness.v`
  - `SecStcTypingCorrectness.v`
- `SecNLusStcTranslation.v` now keeps the cross-phase proof layer
- the full repo `make` succeeds in the current branch state

Remaining proof work:

- discharge
  `successful_call_substitutions_fresh`
  and
  `signatures_preserved_calls`
  from the final theorem stack
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
