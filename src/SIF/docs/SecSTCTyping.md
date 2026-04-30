# SecSTCTyping

## Role

`SecSTCTyping.v` is the target-side security typing layer for STC.  It assigns
symbolic constraints to translated transition constraints and packages them into
system signatures.

## Main Sections

### Reset Auxiliaries

The STC translation introduces reset-instance variables that do not exist on
the NLustre side.  This file isolates them explicitly through the reset
environment machinery.

### Hidden Variables

`hidden_sys_vars` records which target-side variables are hidden when producing
an STC signature:

- ordinary locals,
- memory variables `s_lasts`,
- STC-only reset-instance variables.

This is the target-side analogue of eliminating local witnesses before
comparing signatures.

### Shape and Scopedness

The structural flow mirrors the source side:

- one-transition-constraint shape/scopedness lemmas,
- list-level theorems for translated systems,
- `generate_sys_signature_scoped`,
- `generate_all_sys_signatures_scoped`,
- `generate_sys_signature_scoped_env`,
- `generate_all_sys_signatures_scoped_env`.

## Relation To The Final Theorem

This file supplies the target-side generators used in the final theorem stack:

1. `generate_sys_signature_scoped` is the local STC scopedness theorem.
2. `generate_all_sys_signatures_scoped_env` builds the generated target global
   from the shared node-scoped naming data.
3. `SecStcTypingCorrectness.v` strengthens these results with reset-env and
   namespace facts that the translation proof uses when proving
   `Signature_head_consistent`.

## Relation to the Paper

This file is the STC half of the symbolic typing story.  Its role is to prove
that the target symbolic constraints are well structured and that the generated
STC signatures expose only the shared interface after hidden state is removed.

## Current Design Note

The STC side keeps more internal state than NLustre, so scopedness and hidden
variable elimination are explicit here rather than being left implicit in the
translation proof.

## Key Refinement

The translation proof uses the following more precise raw STC scopedness
interface:

- `trconstr_reset_keys`
- `trconstrs_reset_keys`
- `generate_trconstr_constraint_scoped_on_keys`
- `generate_trconstrs_constraints_scoped_on_keys`

These lemmas say that a translated STC block is scoped if the reset
environment is only known on the reset keys that block actually reads.  This
is the target-side scopedness interface used in the translation proof.
