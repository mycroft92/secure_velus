# SIFSignature

## Role

`SIFSignature.v` defines the stored signature format shared by the NLustre and
STC typing developments and proves the call-instantiation metatheory used by
the translation proof.

## Stored Interface

- `signature`
  is the stored summary exported for one node or system: visible inputs,
  outputs, clock/reset identifiers, and the replayable constraint list.
- `secglobal`
  is just the global list of those stored summaries.
- `find_signature`
  looks up one stored summary by node or system name.
- `signature_scope`
  is the visible interface set that later replay and preservation proofs agree
  to preserve: inputs, outputs, clock, and reset.

This file is where the development moves from raw generated constraints inside
one node or system to reusable summaries that later callers can instantiate.

## Call Instantiation

`generate_constraints` takes a stored callee signature and concrete caller-side
actuals:

- input symbolic types,
- clock type,
- reset type,
- output identifiers.

It performs input substitution, clock/reset substitution, output substitution,
and then reorders the resulting constraints so that the final list is indexed
by the caller output order.

That last reorder step is important.  Later typing proofs do not consume the
callee's internal constraint order; they consume a caller-facing block whose
right-hand sides match the caller outputs exactly.

## Structural Invariants

- `signature_good`
  says a stored signature has well-formed constraints and exactly one
  right-hand side per declared output.
- `secglobal_good`
  says every signature found in a global satisfies `signature_good`.
- `signature_scoped`
  says every stored constraint only mentions identifiers from the visible
  signature interface.
- `secglobal_scoped`
  lifts that scopedness guarantee to every signature found in a global.
- `signature_scope_sec`
  says every visible identifier in one signature comes from the ordinary `sec`
  namespace.
- `call_subst_fresh`
  packages the freshness side conditions needed so caller actuals do not clash
  with the callee's stored scope during replay.
- `call_subst_scoped`
  packages the dual scopedness side conditions saying the caller actuals really
  live inside the caller-visible scope.

The core shape theorem is `generate_constraints_shape`.  It turns
`signature_good` into the concrete fact that every generated call block is
well formed and indexed by the caller outputs.

## Replay Valuation

`lat_valuation` reconstructs the callee-side lattice valuation induced by one
concrete call.  It is the bridge between:

- satisfiability of the stored signature constraints, and
- satisfiability of the instantiated caller-facing call block.

The important replay lemmas are:

- `lat_valuation_agree_on_scope`
  says replaying a call does not change the valuation on the caller scope when
  the caller scope is fresh from the callee signature.
- `lat_valuation_outputs_eq`
  relates each callee output identifier to the concrete caller output variable
  it was instantiated with.
- `lat_valuation_inputs_eq`
  says each stored callee input is interpreted exactly as the caller actual
  type substituted for it.
- `lat_valuation_clk_eq`
  says the stored callee clock identifier evaluates to the caller clock type.
- `lat_valuation_reset_eq`
  says the stored callee reset identifier evaluates to the caller reset type.
- `lat_valuation_fields_agree_on_sig_scope`
  transports those replay equalities across two signatures with matching
  interface fields, which is what the translation proof needs at call sites.

These lemmas say that the replay valuation behaves exactly like the caller's
valuation on the callee's visible scope, while remaining stable outside that
scope when freshness side conditions hold.

## Main Theorems

- `generate_constraints_shape`
  proves that instantiating one stored signature produces a well-formed call
  block whose right-hand sides are exactly the caller outputs, in caller order.
- `generate_constraints_scoped`
  proves that if the caller actuals stay in scope, every instantiated call
  constraint also stays in that same caller scope.
- `generate_constraints_correct_inst`
  shows how a satisfying stored-signature valuation can be replayed forward to
  satisfy the generated caller-side call block.
- `generate_constraints_complete_good`
  proves the reverse direction: if the generated call block is satisfied and
  the stored signature is good, then the stored signature constraints are
  satisfied under the replay valuation.

## Downstream Use

- `SecNLusTyping.v` and `SecSTCTyping.v` use `generate_constraints` when
  typing source and translated call equations.
- `SecNLusTypingCorrectness.v` proves generated source signatures satisfy
  `signature_good` and have `NoDup (signature_scope sig)`.
- `SecNLusStcTranslation.v` uses the replay theorems here to prove
  `Signature_call_preserves` for both ordinary and reset calls.
