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

Today, `generate_trconstrs_constraints_scoped` is convenient for whole-system
scopedness, but it quantifies over every mapping in the full reset
environment.  For the `SecNLusStcTranslation.v` equation-list proof, the
needed statement is more local: only reset-instance variables actually used by
the translated block should have to lie in the chosen scope.

That refinement is the expected entry point for removing the remaining
`preserves_on_app_closed` assumption from the translation proof.
