# SecNLusTypingCorrectness

## Role

`SecNLusTypingCorrectness.v` proves the extra source-side structure needed
after `SecNLusTyping.v` has generated and simplified a node signature.

The file sits exactly at the boundary between:

- raw equation generation,
- stored simplified source signatures,
- and downstream replay and translation arguments

## What This File Adds

Starting from a successful generated source signature, this file proves:

- the raw equation constraints are well formed,
- eliminated locals do not remain in the visible stored scope,
- the stored signature satisfies `signature_good`,
- the visible signature scope has no duplicates,
- generated visible names stay in the intended namespace,
- and caller-visible names are fresh from earlier generated signatures

## Shared Symbolic Layer

This file now uses the symbolic lemmas directly from `SymTypes.v`.  It no
longer carries a local duplicate proof block for simplification facts such as:

- right-hand-side preservation,
- no-duplicate-target preservation,
- singleton-right-hand-side preservation,
- and the fact that simplification only mentions surviving visible identifiers

That keeps the symbolic metatheory in one place and leaves this file focused
on source-generation consequences.

## Main Theorems

- `generated_node_simplify_ready_from_local_env`
  packages the local preconditions needed to use the simplified signature:
  the raw constraints are well formed, and eliminated locals are absent from
  the visible signature scope
- `generate_node_sig_good_from_local_env`
  one generated NLustre signature satisfies `signature_good`
- `generate_node_sig_scope_nodup_from_local_env`
  the visible interface of that generated signature has no duplicates
- `generate_node_sig_scoped_env_scoped`
  source-signature scopedness through the node-scoped environment API
- `node_scope_fresh_in_env_from_bounds` and related lemmas
  generated names for the current node are fresh from earlier signatures

## Visible-Mention Lemmas

The later translation and noninterference proofs need to know that certain
generated helper names remain visible in the stored signature when they are
supposed to matter.

The local bridge here is:

- `subAll_mentions_other`
- `simplify_mentions_other`
- `generated_signature_constraints_mention_reset_scoped_env`
- `generated_signature_constraints_mention_clock_scoped_env`

Because `SymTypes.simplify` now removes trivial self-dependencies on
singleton-right-hand-side constraints, these lemmas reason about the case
where a variable is mentioned by some other constraint and is not itself one
of the eliminated raw singleton targets.

## Why The Freshness Facts Matter

Call preservation needs the caller's visible names to stay fresh from the
callee signature scope and from previously generated globals.  This file
derives those facts from the bounds and injectivity guarantees in
`NameInterface.v` instead of leaving them as extra assumptions.

## Downstream Use

- `SecNLusStcTranslation.v`
  uses `signature_good`, scope `NoDup`, and freshness to prove ordinary-call
  and reset-call preservation
- the source noninterference stack uses the same results when it replays from
  a stored simplified signature back to the raw generated node constraints
