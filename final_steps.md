Current proof state:

- the correctness split is in place:
  - `SecNLusTypingCorrectness.v`
  - `SecStcTypingCorrectness.v`
- `SecNLusStcTranslation.v` now keeps the cross-phase proof layer
- the full repo `make` succeeds in the current branch state

Remaining proof work:

- discharge
  `generated_system_signatures_scoped`
  from the final theorem stack
- discharge
  `successful_call_substitutions_fresh`
  and
  `signatures_preserved_calls`
  from the final theorem stack
- keep deriving `env_injective` from `generate_node_env` through
  `NameInterface.v`

Public theorem structure:

- `generated_program_preserv_global` keeps the raw preservation statement
- `generated_program_signatures_preserved_global` gives the signature-level
  corollary without exposing internal locals

Validation discipline:

- use `_CoqProject`-compatible `coqc` for local debugging
- require full repo `make` before commit, merge, or push
