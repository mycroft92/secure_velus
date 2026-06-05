# SIFSignature

## Role

`SIFSignature.v` defines the stored signature format shared by the NLustre and
STC typing developments and proves the call-instantiation metatheory used by
translation and noninterference.

The important point is that this file works over stored signatures that have
already been simplified by `SymTypes.simplify`.

## Stored Interface

- `signature`
  stored summary for one node or translated system: visible inputs, outputs,
  clock, reset, and replayable constraints
- `secglobal`
  a global list of stored signatures
- `find_signature`
  lookup by node or system name
- `signature_scope`
  the visible interface that later proofs preserve: inputs, outputs, clock,
  and reset

This is the boundary between local raw generation and reusable cross-call
summaries.

## Call Instantiation

`generate_constraints` takes one stored callee signature together with:

- caller-side input symbolic types
- caller-side clock type
- caller-side reset type
- caller-side output identifiers

It instantiates the stored constraints by substituting those actuals and then
reorders the resulting block so that right-hand sides follow the caller output
order.

`generate_constraints` does not run simplification itself.  It assumes the
stored signature was already normalized when it was generated.

## Structural Invariants

- `signature_good`
  the stored signature has well-formed constraints and one singleton
  right-hand side per declared output
- `secglobal_good`
  every signature in a global is good
- `signature_scoped`
  stored constraints only mention identifiers from the visible interface
- `secglobal_scoped`
  global version of that scopedness fact
- `signature_scope_sec`
  visible identifiers live in the ordinary `sec` namespace
- `call_subst_fresh`
  caller actuals are fresh from the callee scope where replay needs that
- `call_subst_scoped`
  caller actuals really live in the caller-visible scope

## Replay Valuation

`lat_valuation` reconstructs the callee-side lattice valuation induced by one
concrete call.  It is the bridge between:

- satisfiability of the stored callee signature
- satisfiability of the instantiated caller-facing call block

The main replay lemmas are:

- `lat_valuation_agree_on_scope`
- `lat_valuation_outputs_eq`
- `lat_valuation_inputs_eq`
- `lat_valuation_clk_eq`
- `lat_valuation_reset_eq`
- `lat_valuation_fields_agree_on_sig_scope`

Together they say that replay behaves exactly like the caller valuation on the
callee's visible scope while remaining stable outside that scope when the
freshness side conditions hold.

## Main Theorems

- `generate_constraints_shape`
  instantiating one stored signature produces a well-formed call block whose
  right-hand sides are exactly the caller outputs
- `generate_constraints_scoped`
  scoped actuals produce a scoped caller-facing call block
- `generate_constraints_correct_inst`
  satisfiability of the stored signature replays forward to satisfiability of
  the instantiated call block
- `generate_constraints_complete_good`
  the reverse replay direction for good stored signatures

## Downstream Use

- `SecNLusTyping.v` and `SecSTCTyping.v`
  use `generate_constraints` in the call cases
- `SecNLusTypingCorrectness.v`
  proves generated source signatures satisfy `signature_good`
- `SecNLusStcTranslation.v`
  uses the replay theorems here to prove ordinary-call and reset-call
  preservation
