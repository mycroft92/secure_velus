# Call Metatheory

## Role

This document explains the current call-preservation layer proved across
`SIFSignature.v`, `SecNLusTypingCorrectness.v`,
`SecStcTypingCorrectness.v`, and `SecNLusStcTranslation.v`.

The main goal of this layer is to show that once source and target signatures
preserve each other as stored summaries, they also preserve each other when
instantiated inside a caller.

## Stored Signature Preservation

At the stored-signature level, the translation file works with:

- `signatures_preserved`
  is the stored-summary preservation relation used before any call actuals are
  substituted.
- `Signature_call_preserves`
  is the strengthened statement saying that this stored preservation survives
  concrete caller-side call instantiation.
- `Signature_head_consistent`
  is the packaged lookup-level result that later files consume, with call
  preservation already built in.

`signatures_preserved` is the static relation on stored signatures.  It says:

- the interface fields match, and
- the target stored constraints preserve satisfiability of the source stored
  constraints on the visible source scope.

That is enough for signature lookup and global consistency, but not yet enough
for call sites.  A call site needs the instantiated caller-facing constraint
blocks, not just the stored summaries.

## What Has To Be Proved At A Call Site

For one call equation, the proof must:

1. start from satisfiability of the instantiated source call block;
2. reconstruct the callee-side valuation induced by the caller actuals;
3. transport satisfiability through the stored-signature preservation theorem;
4. reconstruct satisfiability of the instantiated target call block.

This is exactly what `Signature_call_preserves` captures.

## Freshness And Scopedness Side Conditions

The replay argument needs two local side conditions.

- `call_subst_scoped`
  says that all actuals used at the call site live in the caller scope.
- `call_subst_fresh`
  says that those actuals are fresh with respect to the callee signature scope
  wherever freshness is needed for replay outside the shared scope.

These are not arbitrary assumptions.  They are discharged for generated
signatures and generated caller environments using:

- source signature goodness and scope `NoDup` from
  `SecNLusTypingCorrectness.v`,
- reset-environment range and injectivity facts from
  `SecStcTypingCorrectness.v`,
- generated-name freshness and bounds from `NameInterface.v`.

## Ordinary Calls

The ordinary-call theorem is:

- `signatures_preserved_simple_calls_from_good`
  proves that one instantiated source call can always be matched by an
  instantiated target call when the stored signatures already preserve and the
  generated source signature is structurally good.

Its proof has three stages.

1. Use `generate_constraints_complete_good` to replay the instantiated source
   call block back to the stored source signature under `lat_valuation`.
2. Apply the stored relation `signatures_preserved` on that replay valuation.
3. Use `generate_constraints_correct_inst` to turn the resulting target stored
   satisfiability into satisfiability of the instantiated target call block.

The main work is proving that the replay valuation agrees with the caller
valuation on the shared signature scope and remains unchanged outside that
scope where freshness is required.

## Reset Calls

The reset-call argument is split into:

- `signatures_preserved_reset_underlying_calls_from_good`
  handles the ordinary-call replay part of a reset call before the STC-only
  reset auxiliary is introduced.
- `signatures_preserved_reset_calls_from_good`
  finishes the reset-call proof by adding the fresh translated reset variable
  and showing it stays outside the source-visible interface.

It follows the same replay pattern as ordinary calls, but adds one STC-only
reset-instance variable and one extra reset constraint.  The target-local reset
environment lemmas show that:

- this extra variable is in the dedicated reset namespace,
- it is fresh from the visible shared scope,
- and it only affects the target side outside the source-visible interface.

That is why reset-call preservation still fits into the same visible-scope
preservation framework.

## How This Feeds The Public Translation Theorem

The call metatheory is internal plumbing for
`generated_program_signatures_preserved_global`.

The public lookup theorem only exposes `Signature_head_consistent` for
generated source and target signature pairs.  Inside that packaged result,
`Signature_call_preserves` has already been proved from:

- source generated-signature structure,
- target reset-environment correctness,
- generated naming freshness,
- and the replay lemmas in `SIFSignature.v`.

So later consumers, including `SecStcNonInterference.v`, do not need to reopen
the call-instantiation proof.
