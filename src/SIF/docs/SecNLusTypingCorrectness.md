# SecNLusTypingCorrectness

## Role

`SecNLusTypingCorrectness.v` proves the source-local structural facts about
generated NLustre signatures that are not already covered by raw scopedness and
well-formedness.

## What This File Adds

Starting from a successful generated source signature, this file proves:

- the simplified signature is ready for replay arguments;
- the stored signature satisfies `signature_good`;
- the visible signature scope has no duplicates;
- the generated scope remains inside the intended namespace;
- caller-visible names are fresh with respect to earlier generated signatures.

These are the properties needed when the translation proof leaves the purely
local source generator and starts comparing source and target signatures or
replaying calls through them.

## Main Theorems

- `generated_node_simplify_ready_from_local_env`
  shows that the raw generated constraint list can be simplified into the
  stored source signature in the form expected by the signature layer.
- `generate_node_sig_good_from_local_env`
  proves `signature_good` for a generated NLustre signature.
- `generate_node_sig_scope_nodup_from_local_env`
  proves `NoDup (signature_scope sig)` for that same signature.
- `generate_node_sig_scoped_env_scoped`
  packages generated source signature scopedness through the node-scoped
  environment interface.
- `node_scope_fresh_in_env_from_bounds` and related lemmas derive freshness of
  the current caller scope from the name-generation bounds.

## Why The Freshness Lemmas Matter

The translation proof instantiates callee signatures inside caller scopes.
That only works cleanly when the caller's visible names are known to be fresh
with respect to the callee signature scope and previously generated globals.
This file derives that freshness from the ordering and bounds supplied by
`NameInterface.v`, rather than leaving it as an extra theorem assumption.

## Downstream Use

- `SecNLusStcTranslation.v` uses `signature_good` and scope `NoDup` to prove
  the ordinary-call and reset-call preservation lemmas.
- The same translation file uses the freshness theorems to keep STC-only reset
  instance names outside the shared visible scope.
- The NLustre noninterference files use these theorems when they replay
  satisfiability from stored signatures back to raw generated constraints.
