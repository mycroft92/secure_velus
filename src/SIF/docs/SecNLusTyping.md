# SecNLusTyping

## Role

`SecNLusTyping.v` is the source-side security typing layer for NLustre.  It
turns equations and nodes into symbolic security constraints using the shared
naming environment.

## Main Sections

### Equation Constraint Generation

`generate_eqn_constraint` assigns symbolic constraints to one NLustre equation.
This is the entry point for source-side raw constraint generation.

### Shape and Well-Formedness

The central structural flow is:

- `generate_eqn_constraint_shape`
- `generate_eqns_constraints_shape`
- `generate_eqns_constraints_wf`
- `generate_node_eqns_constraints_wf`

This proves that raw generated NLustre constraints are well formed before
signature simplification.

### Scopedness

The scopedness flow is:

- local `assign_*_scoped` lemmas for expressions and clocks
- `generate_eqn_constraint_scoped`
- `generate_eqns_constraints_scoped`
- `generate_node_sig_scoped`
- `generate_all_signatures_scoped`

This is the source-side input used later by the translation proof when it needs
to show that generated NLustre signatures mention only interface variables.

## Relation to the Paper

This file is the NLustre half of the paper's symbolic typing story.  It proves
that the source symbolic constraints are structurally sound and appropriately
scoped before they are compared against STC.

## Current Design Note

The call case should no longer depend on an external
`call_constraints_shape` theorem premise.  Instead it should consume the
signature-layer facts provided by `SIFSignature.v`.
