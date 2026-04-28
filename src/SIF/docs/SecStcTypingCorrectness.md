# SecStcTypingCorrectness

## Role

`SecStcTypingCorrectness.v` owns target-local correctness lemmas used by the
translation proof but not requiring NLustre/STC comparison.

## Main Contents

- reset-environment range facts
- reset-environment lookup preservation facts
- reset-environment injectivity facts
- generated STC signature scopedness for generated globals

## Relation To The Translation Proof

These lemmas provide the target-side structural invariants needed in
`SecNLusStcTranslation.v`:

- translated reset calls receive fresh STC-only reset-instance names
- reset-instance lookups preserve the intended namespace separation
- generated target signatures are scoped to their visible interface

This keeps target-local environment reasoning out of the cross-phase
translation file.
