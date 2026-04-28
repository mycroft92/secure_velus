# SecNLusTypingCorrectness

## Role

`SecNLusTypingCorrectness.v` owns source-local correctness lemmas used by the
translation proof but not requiring any STC-side reasoning.

## Main Contents

- generated-node naming inversion through the shared naming environment
- source-side namespace separation facts used by the translation proof
- `generated_node_simplify_ready` and its derivation from `generate_node_env`
- generated NLustre signature scopedness for generated globals

## Relation To The Translation Proof

These lemmas supply the source-side structural input needed by
`SecNLusStcTranslation.v`:

- simplify readiness for generated source signatures
- scopedness of generated source signatures
- source-local naming facts used to show STC reset-instance names stay outside
  the visible NLustre scope

The translation file therefore only needs to combine these source-side facts
with target-side correctness and the cross-phase preservation lemmas.
