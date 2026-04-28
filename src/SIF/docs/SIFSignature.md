# SIFSignature

## Role

`SIFSignature.v` defines the symbolic signature object shared by the NLustre and
STC security typing developments.  It is the boundary layer between:

- stored per-node/per-system security summaries, and
- call-time instantiation of those summaries inside a caller.

## Main Definitions

- `signature`: symbolic interface plus stored constraints.
- `secglobal`: list of such signatures.
- `generate_constraints`: instantiate a callee signature inside a caller.
- `signature_good`: stored-signature structural invariant.
- `secglobal_good`: global version of `signature_good`.

## Caller-Facing Reshaping

The important design choice in the current development is that
`generate_constraints` does not merely substitute caller information into the
stored constraints.  After substitution, it rebuilds the resulting constraint
list in the caller's output order.

This gives a stronger interface:

- stored signatures may keep constraints in any internal order;
- successful call instantiation still returns constraints indexed exactly by the
  caller outputs.

This is the intended replacement for the old external `call_constraints_shape`
assumption.

## Theorem Flow

- `signature_good` captures the stored invariant.
- `generate_constraints_shape` turns that stored invariant into the concrete
  call-time shape fact used by the typing modules.
- `generate_constraints_scoped` gives the corresponding call-time scopedness
  fact.

## Relation to the Paper

This module corresponds to the "instantiate a callee signature inside a caller"
part of the paper.  In the mechanized development, it isolates the
substitution/reordering metatheory so that the NLustre/STC typing files do not
need to assume separate call-shape lemmas externally.
