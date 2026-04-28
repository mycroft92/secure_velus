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
- `generate_all_sys_signatures_scoped`.

## Relation to the Paper

This file is the STC half of the symbolic typing story.  Its role is to prove
that the target symbolic constraints are well structured and that the generated
STC signatures expose only the shared interface after hidden state is removed.

## Current Design Note

The STC side keeps more internal state than NLustre, so scopedness and hidden
variable elimination are explicit here rather than being left implicit in the
translation proof.

## Current Next Step

The next translation-level cleanup depends on a slightly more precise raw STC
scopedness lemma than the current generic one.

That refinement now exists:

- `trconstr_reset_keys`
- `trconstrs_reset_keys`
- `generate_trconstr_constraint_scoped_on_keys`
- `generate_trconstrs_constraints_scoped_on_keys`

These lemmas say that a translated STC block is scoped if the reset
environment is only known on the reset keys that block actually reads.

The older theorems
`generate_trconstr_constraint_scoped` and
`generate_trconstrs_constraints_scoped`
remain as wrapper corollaries when a caller already knows that every reset-env
lookup falls inside the chosen scope.

That refined interface is the entry point for the scoped composition step in
the translation proof.
