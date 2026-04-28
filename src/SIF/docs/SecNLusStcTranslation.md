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

`preserves_on_concat_scoped` is the replacement for the older abstract
append-closure assumption.

It says that two preservation witnesses compose if the target-side private
variables are:

- scoped to `scope ++ extras_i`,
- outside the shared scope `scope`,
- disjoint across the two blocks.

For this development, the intended instantiation is:

- `scope`: the shared NLustre/STC node scope,
- `extras_i`: the STC reset-instance variables introduced by translating one
  equation.

## Intended Equation-List Proof

The planned replacement for the old list proof is:

1. prove one-step preservation for a single equation;
2. prove scopedness of the translated STC block for that equation;
3. accumulate reset-instance extras along the equation list;
4. compose head and tail with `preserves_on_concat_scoped`.

This is the route that replaced the old append-closure proof path completely.

## Current Status

- The caller-facing `call_constraints_shape` cleanup has already been pushed
  through the active proof stack far enough that
  `SecNLusStcTranslation.v` is locally `coqc`-clean again.
- The next proof artifacts to remove are therefore the remaining
  scopedness/call-side assumptions, not the call-shape premise.
- That STC-side refinement now exists in `SecSTCTyping.v` through
  `generate_trconstr*_scoped_on_keys`.
- This file now contains the matching reset-extra bookkeeping layer:
  `eqn_reset_extras`, `eqns_reset_extras`,
  `trconstrs_reset_keys_translate_eqns`,
  `translated_reset_key_in_extras`,
  `translated_reset_key_fresh`.

In practical terms, the next theorem work should happen in two layers:

1. rewrite `eqns_preserv` so it threads the concrete reset extras coming from
   `eqns_reset_extras`;
2. compose head and tail with `preserves_on_concat_scoped`, using the new
   key-to-extra bridge lemmas;
3. propagate that replacement through `node_preserv` and the global theorem
   stack until only the remaining scopedness/call-side assumptions are left.

## Relation to the Paper

This file contains the mechanized preservation argument itself.  The current
weakened theorem keeps the spirit of the paper by preserving agreement on the
shared interface/local scope while allowing STC-only auxiliaries outside that
scope.
