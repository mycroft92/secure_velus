# SecStcTypingCorrectness

## Role

`SecStcTypingCorrectness.v` proves the target-local invariants that the
translation proof needs after raw STC signature generation has succeeded.

## Main Facts

- generated reset environments map reset-call keys into the dedicated
  `sec_reset` namespace;
- those reset environments are injective;
- generated STC signatures obtained from node-scoped environments are scoped;
- visible identifiers of generated STC signatures stay in the shared `sec`
  namespace.

The file does not compare source and target signatures directly.  It proves the
target side is structurally well behaved before the cross-phase argument starts.

## Main Theorems

- `generate_reset_env_range`
  proves every generated reset-environment entry lives in the dedicated
  `sec_reset` namespace.
- `generate_reset_env_injective`
  proves distinct reset-call keys receive distinct generated reset identifiers.
- `generate_sys_signature_scoped_env_scoped`
  packages target-signature scopedness through the same node-scoped environment
  interface used by the translation proof.
- `generated_sys_signature_scope_sec`
  proves the visible part of a generated STC signature stays in the ordinary
  shared `sec` namespace, not in the private reset namespace.

## Downstream Use

- `SecNLusStcTranslation.v` uses the reset-environment theorems when proving
  reset-call preservation and when isolating STC-only extras.
- The same file uses the scopedness and namespace theorems to build
  `Signature_head_consistent` for generated source/target signature pairs.
