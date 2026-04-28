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

`preserves_on_concat_scoped` is the intended replacement for the older abstract
`preserves_on_app_closed` assumption.

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

This is the route for deleting `preserves_on_app_closed` completely.

## Current Status

- The caller-facing `call_constraints_shape` cleanup has already been pushed
  through the active proof stack far enough that
  `SecNLusStcTranslation.v` is locally `coqc`-clean again.
- The next proof artifact to remove is therefore
  `preserves_on_app_closed`, not the call-shape premise.
- The expected technical move is to refine the STC-side scopedness argument so
  it only talks about reset-instance variables actually used by the translated
  block, instead of every entry in the whole `reset_env`.

In practical terms, the next theorem work should happen in two layers:

1. strengthen the raw STC scopedness theorem in `SecSTCTyping.v`;
2. rewrite `eqns_preserv` and the downstream node/program theorems here to use
   that finer scopedness fact together with `preserves_on_concat_scoped`.

## Relation to the Paper

This file contains the mechanized preservation argument itself.  The current
weakened theorem keeps the spirit of the paper by preserving agreement on the
shared interface/local scope while allowing STC-only auxiliaries outside that
scope.
