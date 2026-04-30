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
- `signature_scope`: the visible interface scope used by later preservation
  statements.
- `call_subst_fresh` / `call_subst_scoped`: the local side conditions used by
  the call-preservation bridge.

## Caller-Facing Reshaping

The important design choice in the current development is that
`generate_constraints` does not merely substitute caller information into the
stored constraints.  After substitution, it rebuilds the resulting constraint
list in the caller's output order.

This gives a stronger interface:

- stored signatures may keep constraints in any internal order;
- successful call instantiation still returns constraints indexed exactly by the
  caller outputs.

This is the signature-layer source of the call-time shape property used by the
typing developments.

## Theorem Flow

- `signature_good` captures the stored invariant.
- `generate_constraints_shape` turns that stored invariant into the concrete
  call-time shape fact used by the typing modules.
- `generate_constraints_scoped` gives the corresponding call-time scopedness
  fact.
- `inst_valuation` and its `inst_valuation_*` lemmas reconstruct the formal
  callee lattice mapping induced by one concrete caller instantiation.
- `generate_constraints_correct_inst` and `generate_constraints_complete_good`
  are the lattice-mapping bridge between stored signature constraints and the concrete
  call block returned by `generate_constraints`.

## Relation To The Final Theorem

This file provides the signature-local half of the final preservation result.
In the final theorem flow:

1. `SecNLusTypingCorrectness.v` proves generated NLustre signatures satisfy
   `signature_good` and `NoDup (signature_scope ...)`.
2. `SecStcTypingCorrectness.v` provides the target-side scopedness and naming
   facts needed to compare generated STC signatures.
3. `SecNLusStcTranslation.v` uses the call-instantiation metatheory from this
   file to prove `Signature_call_preserves` internally, so the public theorem
   no longer assumes a separate call-side bridge.

## Relation to the Paper

This module corresponds to the "instantiate a callee signature inside a caller"
part of the paper.  In the mechanized development, it isolates the
substitution/reordering metatheory so that the NLustre/STC typing files can use
call-time shape and scopedness results directly from the signature layer.
