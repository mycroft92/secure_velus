# SecNLusStcTranslation

## Role

`SecNLusStcTranslation.v` is the cross-phase preservation layer.  It compares
generated NLustre signatures with generated STC signatures and proves that
every generated source signature has a matching generated target signature
with the same visible interface and the same call behavior.

## Core Interfaces

- `signatures_preserved`
  stored-signature relation: same visible interface, and the target stored
  constraints preserve satisfiability of the source stored constraints on the
  source-visible scope
- `Signature_call_preserves`
  strengthening of stored preservation to actual call instantiation
- `Signature_head_consistent`
  packaged lookup result for one aligned source/target signature pair
- `Signature_consistent`
  global lookup consistency

These definitions separate the public lookup theorem from the internal work
needed to handle call replay and STC-only reset variables.

## Raw Preservation And The Simplify Bridge

The proof runs in two stages.

1. Prove preservation on raw generated constraints using `SecTypes.preserves_on`
   and equation-by-equation composition.
2. Cross from those raw constraints to stored signatures using the fact that
   both sides are simplified by the same `SymTypes.simplify`.

The bridge theorems are:

- `generated_signatures_preserved_from_simplify_bridge_scoped`
- `generated_signatures_preserved_from_simplify_bridge_local_env`
- `generated_signatures_preserved_from_simplify_bridge_scoped_env`

They combine:

- source-side `signature_good`, `NoDup`, and freshness from
  `SecNLusTypingCorrectness.v`
- target-side scope and namespace facts from
  `SecStcTypingCorrectness.v`
- the simplification-preservation results from `SecTypes.v`
- the call replay lemmas from `SIFSignature.v`

## Reset Extras And Scoped Composition

The STC translation may introduce reset-instance variables that do not exist
on the source side.  This file isolates them with:

- `eqn_reset_extras`
- `eqns_reset_extras`
- `trconstrs_reset_keys_translate_eqn`
- `translated_reset_key_in_extras`
- `translated_reset_key_fresh`

Those extras are the reason `preserves_on_concat_scoped` from `SecTypes.v`
matters: translated STC blocks can be concatenated while keeping private reset
state outside the shared source-visible scope.

## Preservation Chain

The preservation stack is:

1. `eqn_preserv`
   one NLustre equation preserves to its translated STC block
2. `eqns_preserv_scoped`
   list-level composition across the node body
3. `node_preserv_scoped`
   node-level raw preservation
4. `generated_node_preserv_scoped` and
   `generated_node_preserv_scoped_scoped_env`
   specialization to the actual generators

At this stage the theorem still talks about raw constraints.  The simplify
bridge is what turns it into a stored-signature theorem.

## Call Preservation Internals

Ordinary and reset calls are proved here through:

- `signatures_preserved_simple_calls_from_good`
- `signatures_preserved_reset_underlying_calls_from_good`
- `signatures_preserved_reset_calls_from_good`

The proof pattern is:

1. replay an instantiated source call block back to the stored source
   signature
2. apply stored-signature preservation
3. replay forward to the instantiated target call block

Reset calls add one STC-only reset auxiliary outside the source-visible scope,
and the target reset-environment lemmas keep that extra variable fresh.

## Global Induction

`generate_all_signatures_consistent_scoped'` is the main whole-program
accumulator theorem.  It builds, in lockstep:

- `Signature_consistent G1 G2`
- `secglobal_scoped G2`
- `secglobal_scope_sec G2`

for the generated target global.

`generate_all_signatures_consistent` is the empty-accumulator corollary.

## Public Theorem

`generated_program_signatures_preserved_global` is the exported result.  Once
the node-scoped environments and both generated globals have been built
successfully, every source signature lookup has a matching target signature
lookup with `Signature_head_consistent`.

That packaged theorem is the interface consumed by
`SecStcNonInterference.v`.
