# SecNLusTypingCorrectness

## Role

`SecNLusTypingCorrectness.v` owns source-local correctness lemmas used by the
translation proof but not requiring any STC-side reasoning.

## Main Contents

- generated-node naming inversion through the shared naming environment
- source-side namespace separation facts used by the translation proof
- `generated_node_simplify_ready_from_local_env`
- `generate_node_sig_good_from_local_env`
- `generate_node_sig_scope_nodup_from_local_env`
- generated NLustre signature scopedness for generated globals
- source-side caller-scope freshness derived from generated provenance
  (`node_scope_fresh_in_env`, `generated_callers_scope_fresh`)

## Relation To The Translation Proof

These lemmas supply the source-side structural input needed by
`SecNLusStcTranslation.v`:

- simplify readiness for generated source signatures
- scopedness of generated source signatures
- structural goodness and `NoDup (signature_scope ...)` for generated source
  signatures
- source-local naming facts used to show STC reset-instance names stay outside
  the visible NLustre scope

## Relation To The Final Theorem

This file discharges the source-side premises of the final call bridge:

- `generate_node_sig_good_from_local_env` provides `signature_good`
- `generate_node_sig_scope_nodup_from_local_env` provides the `NoDup` premise
  used by the lattice-mapping replay lemmas
- `node_scope_fresh_in_env_from_bounds` provides the caller/callee freshness
  fact needed in the generated consistency induction

Those are exactly the source-local ingredients consumed by
`SecNLusStcTranslation.v` when proving `Signature_head_consistent` for one
generated NLustre/STC signature pair.

The translation file therefore only needs to combine these source-side facts
with target-side correctness and the cross-phase preservation lemmas.
