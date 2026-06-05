# SecStcTypingCorrectness

## Role

`SecStcTypingCorrectness.v` proves the target-local invariants needed after
`SecSTCTyping.v` has generated a stored STC signature.

The file does not compare source and target signatures directly.  It proves
that the target side is structurally well behaved before the cross-phase
translation argument starts.

## Main Facts

- generated reset environments map reset-call keys into the dedicated
  `sec_reset` namespace
- generated reset environments are injective
- generated target signatures produced from node-scoped environments are
  scoped
- visible identifiers of generated target signatures stay in the shared
  ordinary `sec` namespace

## Main Theorems

- `generate_reset_env_range`
  every generated reset-environment entry lives in `sec_reset`
- `generate_reset_env_injective`
  distinct reset-call keys receive distinct generated reset identifiers
- `generate_sys_signature_scoped_env_scoped`
  target-signature scopedness through the node-scoped environment API
- `generated_sys_signature_scope_sec`
  the visible part of a generated STC signature stays in `sec`, not in the
  private reset namespace

## Downstream Use

- `SecNLusStcTranslation.v`
  uses the reset-environment theorems when proving reset-call preservation and
  when showing STC-only extras stay outside the source-visible scope
- the same translation file uses the scopedness and namespace theorems when it
  builds `Signature_head_consistent` for generated source/target pairs
