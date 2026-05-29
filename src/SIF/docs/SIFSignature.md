# SIFSignature

## Role

`SIFSignature.v` defines the stored signature format shared by the NLustre and
STC typing developments and proves the call-instantiation metatheory used by
the translation proof.

## Stored Interface

- `signature` stores a node or system name, its symbolic inputs and outputs,
  its reset and clock identifiers, and the constraint list exported for later
  callers.
- `secglobal` is a list of such signatures.
- `find_signature` performs lookup by node or system name.
- `signature_scope` is the visible interface scope:
  inputs, outputs, reset, and clock.

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

- `signature_good` records the stored well-formedness condition needed for
  replay proofs.
- `secglobal_good` lifts that invariant to a signature global.
- `signature_scoped`, `secglobal_scoped`, and `signature_scope_sec` track where
  visible identifiers are allowed to come from.
- `call_subst_fresh` and `call_subst_scoped` describe the side conditions that
  a concrete caller instantiation must satisfy.

The core shape theorem is `generate_constraints_shape`.  It turns
`signature_good` into the concrete fact that every generated call block is
well formed and indexed by the caller outputs.

## Replay Valuation

`inst_valuation` reconstructs the callee-side lattice valuation induced by one
concrete call.  It is the bridge between:

- satisfiability of the stored signature constraints, and
- satisfiability of the instantiated caller-facing call block.

The important replay lemmas are:

- `inst_valuation_agree_on_scope`
- `inst_valuation_outputs_eq`
- `inst_valuation_inputs_eq`
- `inst_valuation_clk_eq`
- `inst_valuation_reset_eq`
- `inst_valuation_fields_agree_on_sig_scope`

These lemmas say that the replay valuation behaves exactly like the caller's
valuation on the callee's visible scope, while remaining stable outside that
scope when freshness side conditions hold.

## Main Theorems

- `generate_constraints_shape`
  proves well-formedness and output alignment of an instantiated call block.
- `generate_constraints_scoped`
  proves that scoped actuals yield scoped instantiated constraints.
- `generate_constraints_correct_inst`
  transports satisfiability from the stored signature constraints to the
  generated call constraints under `inst_valuation`.
- `generate_constraints_complete_good`
  performs the converse transport for well-formed generated signatures.

## Downstream Use

- `SecNLusTyping.v` and `SecSTCTyping.v` use `generate_constraints` when
  typing source and translated call equations.
- `SecNLusTypingCorrectness.v` proves generated source signatures satisfy
  `signature_good` and have `NoDup (signature_scope sig)`.
- `SecNLusStcTranslation.v` uses the replay theorems here to prove
  `Signature_call_preserves` for both ordinary and reset calls.
