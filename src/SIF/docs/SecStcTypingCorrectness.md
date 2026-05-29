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
  proves that every successful reset-environment lookup returns a generated
  `sec_reset` identifier.
- `generate_reset_env_injective`
  proves that two reset-call keys cannot map to the same generated reset name.
- `generate_sys_signature_scoped_env_scoped`
  packages scopedness for generated STC signatures through the node-scoped
  environment interface.
- `generated_sys_signature_scope_sec`
  proves that every visible identifier in a generated target signature lies in
  the shared `sec` namespace.

## Downstream Use

- `SecNLusStcTranslation.v` uses the reset-environment theorems when proving
  reset-call preservation and when isolating STC-only extras.
- The same file uses the scopedness and namespace theorems to build
  `Signature_head_consistent` for generated source/target signature pairs.
