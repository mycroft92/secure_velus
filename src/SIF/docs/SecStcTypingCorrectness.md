# SecStcTypingCorrectness

## Role

`SecStcTypingCorrectness.v` owns target-local correctness lemmas used by the
translation proof but not requiring NLustre/STC comparison.

## Main Contents

- reset-environment range facts
- reset-environment lookup preservation facts
- reset-environment injectivity facts
- generated STC signature scopedness for generated globals
- target-side namespace facts showing visible STC signature identifiers stay in
  the shared `sec` namespace

## Relation To The Translation Proof

These lemmas provide the target-side structural invariants needed in
`SecNLusStcTranslation.v`:

- translated reset calls receive fresh STC-only reset-instance names
- reset-instance lookups preserve the intended namespace separation
- generated target signatures are scoped to their visible interface

## Relation To The Final Theorem

This file discharges the target-local premises used by the final call bridge
and the global consistency induction:

- `generate_sys_signature_scoped_env_scoped` supplies generated target
  signature scopedness
- `generated_sys_signature_scope_sec` connects generated target visible names
  back to the shared `sec` namespace
- the reset-environment lemmas justify the extra `TcReset` prefix constraint in
  the reset-call preservation argument

This keeps target-local environment reasoning out of the cross-phase
translation file.
