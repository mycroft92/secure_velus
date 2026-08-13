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

These proofs are about signatures produced by the shared symbolic simplifier in
`SymTypes.v`.  In particular, simplification eliminates locals before storage,
and the visible constraints are allowed to drop the trivial self-dependency of
one singleton-right-hand-side target on its own left-hand side.

## Main Theorems

- `generated_node_simplify_ready_from_local_env`
  proves the raw generated equation constraints are well formed and that the
  simplified-away locals do not leak back into the stored visible scope.
- `generate_node_sig_good_from_local_env`
  proves one generated NLustre signature satisfies the signature layer's main
  replay invariant `signature_good`.
- `generate_node_sig_scope_nodup_from_local_env`
  proves the visible interface of that generated signature has no duplicate
  identifiers.
- `generate_node_sig_scoped_env_scoped`
  re-expresses source-signature scopedness through the node-scoped environment
  API used by the rest of the development.
- `node_scope_fresh_in_env_from_bounds` and related lemmas
  derive that a current node's visible generated names are fresh from earlier
  signatures by using the monotone fresh-name bounds from `NameInterface.v`.

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
- `SecNLusTypingTotality.v` uses `generate_node_sig_good_from_local_env`,
  `generate_node_sig_scope_nodup_from_local_env` and
  `node_scope_fresh_in_env_from_bounds` in the other direction: not to describe
  a signature that was generated, but to show the *next* one can be.  The
  accumulator invariant of its program walk is exactly the conjunction of the
  first two, and the freshness lemma is what makes a caller's outputs fresh for
  the callee it calls.

## A note on direction

Everything here is conditioned on a successful generator run -- these are facts
*about* generated signatures, not evidence that any exist.  That second question
is answered separately, in `docs/signature-generation-totality.md`.
