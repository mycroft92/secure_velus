# SecNLusStcTranslation

## Role

`SecNLusStcTranslation.v` is the comparison layer between the NLustre and STC
security typings.  It states and proves the weakened preservation theorem used
by the thesis development.

## Main Semantic Notions

- `agree_on`: two valuations coincide on the variables we care about.
- `preserves_on`: source satisfiability transfers to target satisfiability while
  preserving `agree_on`.
- `signatures_preserved`: signature-level version of the same idea.

These definitions encode the deliberate weakening from the paper's strongest
interface-equality reading: STC may introduce private auxiliary variables as
long as shared variables agree.

## Scoped Concatenation

`preserves_on_concat_scoped` is the composition lemma used throughout the
equation-list proof.

It says that two preservation witnesses compose if the target-side private
variables are:

- scoped to `scope ++ extras_i`,
- outside the shared scope `scope`,
- disjoint across the two blocks.

For this development, the intended instantiation is:

- `scope`: the shared NLustre/STC node scope,
- `extras_i`: the STC reset-instance variables introduced by translating one
  equation.

## Equation-List Preservation

The equation-list proof works by:

1. prove one-step preservation for a single equation;
2. prove scopedness of the translated STC block for that equation;
3. accumulate reset-instance extras along the equation list;
4. compose head and tail with `preserves_on_concat_scoped`.

## Current Status

- This file contains the reset-extra bookkeeping layer:
  `eqn_reset_extras`, `eqns_reset_extras`,
  `trconstrs_reset_keys_translate_eqns`,
  `translated_reset_key_in_extras`,
  `translated_reset_key_fresh`.
- The generated-signature bridge lives here:
  `generated_signatures_preserved_from_simplify_bridge_scoped`.
- The global consistency and program theorems also live here:
  `generate_all_signatures_consistent`,
  `generated_program_preserv_global`,
  `generated_program_signatures_preserved_global`.

## Current Proof Boundary

This file now owns only cross-phase results.  Source-local and target-local
correctness facts live in:

- `SecNLusTypingCorrectness.v`
- `SecStcTypingCorrectness.v`

The remaining proof work is to eliminate the final theorem assumptions coming
from generated scopedness and call instantiation.

## Relation to the Paper

This file contains the mechanized preservation argument itself.  The current
weakened theorem keeps the spirit of the paper by preserving agreement on the
shared interface/local scope while allowing STC-only auxiliaries outside that
scope.
