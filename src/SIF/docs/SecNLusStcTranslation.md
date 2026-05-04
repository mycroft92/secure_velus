# SecNLusStcTranslation

## Role

`SecNLusStcTranslation.v` is the cross-phase syntactic comparison layer between
the NLustre and STC security typings. It states and proves the weakened
preservation theorem used by the thesis development.

## Main Lattice-Mapping Notions

- `agree_on`: two lattice mappings coincide on the variables we care about.
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
  `generated_signatures_preserved_from_simplify_bridge_local_env`.
- The global consistency and program theorems also live here:
  `generate_all_signatures_consistent_scoped'`,
  `generate_all_signatures_consistent`,
  `generated_program_signatures_preserved_global`.
  The last corollary is now lookup-based over the generated globals, so it no
  longer reruns per-node signature generation in its statement.

## Final Theorem Flow

The important theorem chain is now:

1. `eqn_preserv`
2. `eqns_preserv_scoped`
3. `node_preserv_scoped`
4. `generated_signatures_preserved_from_simplify_bridge_local_env`
5. `generate_all_signatures_consistent_scoped'`
6. `generate_all_signatures_consistent`
7. `generated_program_signatures_preserved_global`

The semantic consumer of this chain is now the weaker translated-behavior STC
noninterference corollary in `SecStcNonInterference.v`. That corollary uses:

- `SecNLusNonInterference.v` for the source indexed theorem;
- the existing NLustre indexed/memory semantic bridge;
- `NLustreToStc.Correctness.correctness_loop`; and
- `generated_program_signatures_preserved_global`.

`Signature_call_preserves` is proved internally in this file from:

- `signature_good` and call-instantiation lemmas from `SIFSignature.v`
- source-side generated-signature facts from `SecNLusTypingCorrectness.v`
- target-side reset/scopedness facts from `SecStcTypingCorrectness.v`

## Proof Boundary

This file now owns only syntactic/cross-phase results. Source-local and
target-local correctness facts live in:

- `SecNLusTypingCorrectness.v`
- `SecStcTypingCorrectness.v`

The public theorem stack is now free of the old call-side assumptions. This
file remains a preservation library for `SecStcNonInterference.v`, not a second
noninterference stack in its own right.

## Relation to the Paper

This file contains the mechanized preservation argument itself.  The current
weakened theorem keeps the spirit of the paper by preserving agreement on the
shared interface/local scope while allowing STC-only auxiliaries outside that
scope.
