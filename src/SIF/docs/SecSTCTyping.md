# SecSTCTyping

## Role

`SecSTCTyping.v` is the STC-side constraint generator.  It assigns security
constraints to translated transition constraints, makes STC-only state
explicit, and packages the visible part into stored target signatures.

## STC-Specific State

### Reset Environment

The STC translation introduces reset-instance identifiers that do not exist on
the source side.  This file represents them explicitly through the generated
reset environment and threads that environment through transition-constraint
typing.

### Hidden Variables

`hidden_sys_vars` records which generated identifiers are removed before the
exported STC signature is stored:

- translated locals
- memory variables such as `s_lasts`
- STC-only reset-instance names

The stored signature therefore exposes only the translated interface that is
meant to be compared with the NLustre signature.

## Signature Generation

- transition-level generators produce raw target constraints
- list-level generators assemble one translated block
- `generate_sys_signature`
  stores `SymTypes.simplify raw (hidden_sys_vars ...)`
- `generate_sys_signature_scoped_env`
  node-scoped entry point
- `generate_all_sys_signatures_scoped_env`
  top-level target generator

As on the source side, stored target signatures are canonicalized by the same
shared `SymTypes.simplify`, including removal of trivial self-dependencies on
singleton right-hand sides.

## Main Theorem Families

- `trconstr_reset_keys`
  extracts the reset-instance keys read by one translated transition
  constraint
- `trconstrs_reset_keys`
  accumulates those keys across a whole translated block
- `generate_trconstr_constraint_scoped_on_keys`
  one translated block is scoped once the proof includes the visible scope
  plus the reset keys it may read
- `generate_trconstrs_constraints_scoped_on_keys`
  list-level version of the same argument
- `generate_sys_signature_scoped`
  the simplified stored target signature stays inside the visible translated
  interface
- `generate_all_sys_signatures_scoped`
  scopedness for the generated target global

The reset-key lemmas are the interface consumed by the translation proof when
it needs to isolate STC-only extras from the shared source-visible scope.

## Downstream Use

- `SecStcTypingCorrectness.v`
  proves the extra namespace and injectivity facts about generated reset names
  and target signatures
- `SecNLusStcTranslation.v`
  uses the reset-key scopedness theorems to compose translated equation blocks
  while keeping private reset extras separate from the NLustre scope
