Current proof state:

- the correctness split is in place:
  - `SecNLusTypingCorrectness.v`
  - `SecStcTypingCorrectness.v`
- `SecNLusStcTranslation.v` now keeps the cross-phase proof layer
- the full repo `make` succeeds in the current branch state
- the SIF module/theorem-flow docs have been refreshed to match the current
  ownership split and the final lookup-based signature theorem

Remaining proof work:

- the public theorem stack no longer assumes:
  - `successful_call_substitutions_fresh`
  - `signatures_preserved_calls`
- the node-scoped naming pivot is complete enough for the final lookup theorem
  and the call-instantiation bridge is now internal
- remaining proof-side work is only:
  - discharge `sec_not_in_gensym_prefs` concretely
  - move generic helper lemmas out of `SecNLusStcTranslation.v`
  - refresh the module/theorem-flow documentation after those moves

Public theorem structure:

- `generated_program_preserv_global` keeps the raw preservation statement
- `generated_program_signatures_preserved_global` gives the signature-level
  lookup corollary over the generated globals, without exposing internal locals,
  rerunning per-node signature generation, or assuming any extra call-side
  bridge theorem

Validation discipline:

- use `_CoqProject`-compatible `coqc` for local debugging
- require full repo `make` before commit, merge, or push
