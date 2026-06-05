# Call Metatheory

## Role

This document explains the call-preservation layer spread across
`SIFSignature.v`, `SecNLusTypingCorrectness.v`,
`SecStcTypingCorrectness.v`, and `SecNLusStcTranslation.v`.

The goal is to show that once source and target signatures preserve each other
as stored summaries, they still preserve each other after concrete caller-side
instantiation.

## Stored Signatures First

At the stored-signature level, the translation proof works with:

- `signatures_preserved`
- `Signature_call_preserves`
- `Signature_head_consistent`

`signatures_preserved` is the static relation on stored signatures.  It says:

- the visible interface fields match
- the target stored constraints preserve satisfiability of the source stored
  constraints on the visible source scope

Those stored constraints are already the normalized summaries produced by
`SymTypes.simplify`.

## What A Call-Site Proof Must Do

For one call equation, the proof must:

1. start from satisfiability of the instantiated source call block
2. reconstruct the callee-side replay valuation induced by the caller actuals
3. transport satisfiability through stored-signature preservation
4. reconstruct satisfiability of the instantiated target call block

This is exactly what `Signature_call_preserves` packages.

## Freshness And Scopedness Side Conditions

The replay argument needs two local side conditions.

- `call_subst_scoped`
  the actual arguments used at the call site stay inside the caller-visible
  scope
- `call_subst_fresh`
  those actuals are fresh from the callee signature scope where replay needs
  stability outside the shared interface

Generated proofs discharge these side conditions using:

- source `signature_good` and scope `NoDup` from
  `SecNLusTypingCorrectness.v`
- target reset-environment range and injectivity from
  `SecStcTypingCorrectness.v`
- generated-name freshness and bounds from `NameInterface.v`

## Ordinary Calls

The main ordinary-call theorem is:

- `signatures_preserved_simple_calls_from_good`

Its proof has three stages.

1. Use `generate_constraints_complete_good` to replay the instantiated source
   call block back to the stored source signature under `lat_valuation`.
2. Apply the stored relation `signatures_preserved`.
3. Use `generate_constraints_correct_inst` to replay forward to the
   instantiated target call block.

The update and agreement lemmas from `SecTypes.v` are what keep this replay
stable on the visible scope.

## Reset Calls

The reset-call argument is split into:

- `signatures_preserved_reset_underlying_calls_from_good`
- `signatures_preserved_reset_calls_from_good`

It follows the same replay pattern as ordinary calls, but adds one STC-only
reset-instance variable and one extra target-side reset constraint.  The
target-local reset-environment lemmas show that this extra variable:

- lives in the dedicated reset namespace
- stays fresh from the shared visible scope
- only affects the target side outside the source-visible interface

## How This Feeds The Public Translation Theorem

The public theorem
`generated_program_signatures_preserved_global` only exposes
`Signature_head_consistent` for generated source and target signature pairs.

Inside that packaged result, call preservation has already been proved from:

- the stored-signature replay lemmas in `SIFSignature.v`
- the source and target correctness results
- the `SecTypes.v` agreement and preservation machinery

Later consumers do not need to reopen the call-instantiation proof.
