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

## Theorem Statements

- `generate_trconstr_constraint_scoped_on_keys`: if the current translated
  constraint `tr` is well clocked, the visible source variables map into
  `scope`, the base/reset types are in `scope`, and every lookup on
  `trconstr_reset_keys tr` returns a type in `scope`, then a successful
  `generate_trconstr_constraint tr` produces `constraints_scoped scope cns`.
- `generate_trconstrs_constraints_scoped_on_keys`: the list-level version
  lifts the same statement from one translated STC constraint to an entire
  translated block using `trconstrs_reset_keys`.
- `generate_sys_signature_scoped`: if `secglobal_scoped G`, `env_injective env`,
  and `wc_system P s`, then any successful generated STC signature satisfies
  `signature_scoped`.
- `generate_all_sys_signatures_scoped`: if `wc_program systems` and the shared
  environment is injective, then successful generation of all STC signatures
  yields a `secglobal_scoped` result.
