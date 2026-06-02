# SecSTCTyping

## Role

`SecSTCTyping.v` is the STC-side symbolic typing generator.  It assigns
security constraints to translated transition constraints, isolates STC-only
state, and packages the visible part into stored target signatures.

## Generation Structure

### Reset Environment

The STC translation introduces reset-instance identifiers that do not exist on
the source side.  This file represents them explicitly through the generated
reset environment and threads that environment through transition-constraint
typing.

### Hidden Variables

`hidden_sys_vars` records which generated identifiers are removed before the
exported STC signature is stored:

- translated locals,
- memory variables such as `s_lasts`,
- STC-only reset-instance names.

The stored signature therefore exposes only the translated interface that is
meant to be compared with the NLustre signature.

### Signature Generation

- transition-level generators produce raw target constraints;
- list-level generators assemble one translated block;
- `generate_sys_signature` simplifies the raw result into a stored signature;
- `generate_sys_signature_scoped_env` and
  `generate_all_sys_signatures_scoped_env` are the node-scoped entry points
  used by the current translation theorem.

## Main Theorem Families

- `trconstr_reset_keys`
  extracts exactly which reset-instance keys one translated STC transition
  constraint reads.
- `trconstrs_reset_keys`
  accumulates those reset keys across a whole translated transition block.
- `generate_trconstr_constraint_scoped_on_keys`
  says one generated translated constraint block is scoped once the proof
  includes the visible scope plus the reset keys that block may read.
- `generate_trconstrs_constraints_scoped_on_keys`
  lifts that scopedness argument from one transition constraint to an entire
  translated transition list.
- `generate_sys_signature_scoped`
  proves the simplified stored STC signature only mentions identifiers from its
  visible translated interface.
- `generate_all_sys_signatures_scoped`
  lifts that signature-scopedness fact to the whole generated STC global.
- `generate_sys_signature_scoped_env`
  is the node-scoped entry point that first recovers the right local generated
  environment and then builds one scoped STC signature.
- `generate_all_sys_signatures_scoped_env`
  is the top-level node-scoped global generator consumed by the translation
  theorem.

The reset-key lemmas are the crucial interface for the translation proof.  They
show that one translated STC block is scoped once the proof knows the scope of
the visible variables and of exactly the reset-instance keys that block reads.

## Downstream Use

- `SecStcTypingCorrectness.v` proves the extra namespace and injectivity facts
  about generated reset names and generated target signatures.
- `SecNLusStcTranslation.v` uses the reset-key scopedness theorems to compose
  translated equation blocks while keeping their private reset extras separate
  from the shared NLustre scope.
