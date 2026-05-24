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

## Theorem Statements

- `signature_good sig` means:
  `wf_constraints sig.(s_constraints)` and
  `Permutation (map snd sig.(s_constraints)) (map (fun ty => [ty]) sig.(s_out))`.
- `generate_constraints_shape`: if `NoDup out` and
  `generate_constraints sig inp clk rst out st = OK (cns, st')`, then
  `wf_constraints cns` and
  `map snd cns = map (fun ty => [ty]) out`.
- `generate_constraints_scoped`: if `signature_scoped sig`, all actual input,
  clock, and reset types are scoped to `scope`, all actual outputs lie in
  `scope`, and call generation succeeds, then `constraints_scoped scope cns`.
- `generate_constraints_correct_inst`: if `NoDup (signature_scope sig)`,
  `call_subst_fresh sig inp clk rst out`, and the stored signature constraints
  are satisfiable under `inst_valuation dlt sig inp clk rst out`, then the
  generated call constraints are satisfiable under that same instantiated
  valuation.
- `generate_constraints_complete_good`: if `signature_good sig` and call
  generation succeeds, then satisfiability of the generated call block
  reconstructs satisfiability of the stored signature constraints under the
  replay valuation built from the concrete inputs, clock, reset, and outputs.

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
