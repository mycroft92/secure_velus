# SecNLusStcTranslation

## Role

`SecNLusStcTranslation.v` is the cross-phase preservation file.  It compares
generated NLustre signatures with generated STC signatures and proves that
every generated source signature has a matching generated target signature with
the same visible interface and call behavior.

## Core Interfaces

- `signatures_preserved`
  is the static stored-signature relation: same visible interface, and target
  constraints preserve source satisfiability on the source scope.
- `Signature_call_preserves`
  is the dynamic call-site strengthening saying that stored preservation
  survives actual call instantiation, for both ordinary and reset calls.
- `Signature_head_consistent`
  packages one aligned source/target signature pair with matching lookup name,
  matching visible fields, and call preservation.
- `Signature_consistent`
  lifts that pairwise packaging to whole generated source/target globals.

These definitions separate the public lookup-level result from the internal
work needed to handle call instantiation and STC-only reset auxiliaries.

## Reset Extras And Scoped Composition

The STC translation may introduce reset-instance variables for one translated
equation that do not exist on the source side.  This file isolates them with:

- `eqn_reset_extras`
  extracts the generated reset-instance identifiers needed by one translated
  source equation.
- `eqns_reset_extras`
  accumulates those private reset extras across a whole node equation list.
- `trconstrs_reset_keys_translate_eqn`
  relates reset keys read by the translated STC block back to the source
  equation that introduced them.
- `translated_reset_key_in_extras`
  proves every translated reset key really appears in the computed extras list.
- `translated_reset_key_fresh`
  proves those extras stay fresh from the shared visible source scope.

The point of this layer is to make translated target extras explicit so that
composition can be handled by `preserves_on_concat_scoped` from `SecTypes.v`.

## Equation And Node Preservation

The preservation chain is:

1. `eqn_preserv`
   proves one NLustre equation preserves to its translated STC block on the
   shared visible scope.
   It is the base simulation step before list-level composition.
2. `eqns_preserv_scoped`
   folds that argument over the equation list while accumulating the reset
   extras of each translated block.
   This is where `preserves_on_concat_scoped` is used to glue per-equation
   target blocks together.
3. `node_preserv_scoped`
   instantiates the list theorem with the concrete generated interface,
   locals, clock, reset, and reset extras of one node.
   It is still stated on raw generated constraints, not stored signatures.
4. `generated_node_preserv_scoped` and
   `generated_node_preserv_scoped_scoped_env`
   specialize the node theorem to signatures produced by the actual generators.
   The second version passes through the node-scoped environment interface used
   elsewhere in the development.

At this stage the theorem still talks about raw generated constraints, not yet
about stored simplified signatures.

## Signature Bridge

The raw-to-stored bridge is handled by:

- `generated_signatures_preserved_from_simplify_bridge_scoped`
  converts one raw scoped preservation theorem into stored-signature
  preservation once the needed source/target structural facts are available.
- `generated_signatures_preserved_from_simplify_bridge_local_env`
  specializes that bridge to the local-environment view produced by the actual
  NLustre and STC generators.
- `generated_signatures_preserved_from_simplify_bridge_scoped_env`
  repackages the same bridge through the node-scoped environment API used by
  the global theorem.

Both sides of this bridge use the same structural simplifier from
`SymTypes.v`, and the bridge is what reconnects the raw generated constraints
to those stored simplified signatures.

These theorems combine:

- source-side signature goodness and scope `NoDup` from
  `SecNLusTypingCorrectness.v`,
- target-side scopedness and namespace facts from
  `SecStcTypingCorrectness.v`,
- and the call replay lemmas from `SIFSignature.v`.

The result is a stored-signature preservation statement that is strong enough
to support call instantiation on both sides.

## Call Preservation Internals

The ordinary and reset call arguments are proved inside this file through:

- `signatures_preserved_simple_calls_from_good`
  proves ordinary-call preservation by replaying source call satisfiability
  back to the stored signature and then forward to the target call block.
- `signatures_preserved_reset_underlying_calls_from_good`
  proves the same replay argument for the underlying call part of a reset call,
  before adding the STC-only reset auxiliary.
- `signatures_preserved_reset_calls_from_good`
  completes the reset-call case by adding the fresh target-only reset
  constraint outside the shared visible scope.

These theorems start from stored-signature preservation plus generated-source
signature goodness, then reconstruct the caller-side valuation needed by
`generate_constraints_correct_inst` and `generate_constraints_complete_good`.
The reset-call theorem adds one STC-only reset constraint outside the shared
scope and uses the target reset-environment facts to keep that extra variable
fresh.

## Global Induction

`generate_all_signatures_consistent_scoped'` is the main accumulator theorem
for whole programs.  It performs a single induction over the node list and
builds three results at once for the generated target global:

- `Signature_consistent G1 G2`
- `secglobal_scoped G2`
- `secglobal_scope_sec G2`

It is the lockstep theorem that says the source and translated target globals
can be generated together while preserving lookup alignment and target-side
scope invariants at every prefix.

At each step, the proof:

1. recovers the current node's generated local environment;
2. applies the node-level raw preservation theorem;
3. crosses the simplify bridge to obtain a stored source/target signature pair;
4. packages that pair as a `generated_signature_step_consistent`;
5. extends the accumulator with `Signature_consistent_cons`;
6. re-establishes target global scopedness and namespace facts for the new
   accumulator.

`generate_all_signatures_consistent` is the empty-accumulator corollary.

## Public Theorem

`generated_program_signatures_preserved_global` is the exported lookup-based
result.  Once the node-scoped environments and both generated globals have been
built successfully, every source signature found in the NLustre global has a
matching STC signature in the translated global with
`Signature_head_consistent`.

In other words, later clients can treat source and translated target signature
lookups as paired summaries without reopening the raw translation proof.

That theorem is the exact interface consumed by `SecStcNonInterference.v`.
