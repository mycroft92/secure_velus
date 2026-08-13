# SIF Architecture

## Overview

This document gives the current module layout of `src/SIF/` and how the pieces
fit together.

## Foundations

- `Helpers.v`
  list and positivity lemmas used throughout the proofs.
- `SymTypes.v`
  symbolic security types and list-level utilities on them.
- `SecLattice.v`
  abstract lattice interface and derived lattice lemmas.
- `SecContext.v`
  state-and-error monad plus reusable lookup lemmas.
- `SecTypes.v`
  valuation agreement, constraint scopedness, and satisfiability-preservation
  combinators.

## Naming And Local Typing

- `NameInterface.v`
  generated security-name allocation and node-scoped environments.
- `SecNamingTotality.v`
  that allocation always succeeds and that its environment answers every
  lookup the generators make.
- `SecCETyping.v`
  symbolic typing for clocks and CoreExpr expressions.
- `SecNLusTyping.v`
  NLustre-side raw constraint and signature generation.
- `SecSTCTyping.v`
  STC-side raw constraint and signature generation, including reset-instance
  handling.

## Signature And Correctness Layers

- `SIFSignature.v`
  stored signature format and call-instantiation replay metatheory.
- `SecNLusTypingCorrectness.v`
  source-local structural facts for generated signatures.
- `SecStcTypingCorrectness.v`
  target-local structural facts for generated signatures and reset
  environments, plus stability of generation under reordering a body --
  which is what carries signatures across the scheduler.
- `SecObcTyping.v`
  Obc-side statement and class constraint generation.
- `SecObcTypingCorrectness.v`
  structural facts for generated Obc class signatures.
- `SecNLusTypingTotality.v`
  that the NLustre generator succeeds on any ordered, well-clocked program.
  Together with `SecNamingTotality.v` this discharges the root hypothesis
  every layer carries; see `docs/signature-generation-totality.md`.
- `NLustreCausality.v`
  node causality facts used by the noninterference proof.

## Translation Preservation

- `SecNLusStcTranslation.v`
  cross-phase preservation from generated NLustre signatures to generated STC
  signatures.

This file is where:

- raw equation preservation is proved,
- reset-instance extras are isolated,
- call preservation is reconstructed from the signature metatheory,
- and the whole-program generated signature globals are shown consistent.

- `SecStcObcTranslation.v`
  the same for STC signatures to Obc class signatures.  Longer than the leg
  above it because the target is imperative -- clocks become control flow, a
  control expression becomes a decision tree, and the reset method constrains
  names the source never mentions.  See `docs/SecStcObcTranslation.md` and
  `docs/Stc2Obc-additional-work.md`.
- `SecNLusStcObcEnv.v`
  environment threading for the whole chain.  The naming pass runs once, over
  NLustre nodes; this file is where the facts each layer states abstractly are
  discharged from that run, including across the scheduler.  It introduces no
  new typing rule or signature notion.

## Source Noninterference Stack

- `SecNLusNonInterferenceSupport.v`
  observation model, generic semantic transport, and `node_security`.
- `SecNLusNonInterferenceHelpers.v`
  generated-program replay and call transport lemmas.
- `SecNLusNonInterferenceClockedStep.v`
  time-step induction for low-equivalence of defined variables.
- `SecNLusNonInterference.v`
  packaging into the exported source output theorem.

This stack proves noninterference directly on the indexed NLustre semantics.

## Target Noninterference

- `SecStcNonInterference.v`
  translated-system noninterference theorem obtained by combining:
  source noninterference, NLustre/STC semantic preservation, and generated
  signature preservation.
- `SecObcNonInterference.v`
  the same one phase further down, for the class the compiler actually emits.
  Like the STC layer it is a *transport*: the imperative semantics is never
  attacked directly.  This file also assembles the totality chain, so its
  exported theorem needs no signature environment for STC, the scheduled STC
  program, or Obc.  See `docs/Obc-noninterference-proof.md`.

Both files state their theorems source-to-target: the hypotheses constrain runs
of the source node, the conclusion constrains the emitted code.  The Obc-level
input hypothesis and the inward-reading transport proofs make that easy to
misread, which is why each exported theorem carries a direction note.

## Constraint Export

- `SecNLusConstraintExport.v`
  executable dump of generated NLustre constraints and stored signatures.
- `SecStcConstraintExport.v`
  corresponding executable dump for generated STC constraints.
- `SecObcConstraintExport.v`
  the same for the Obc classes the compiler emits, taken after scheduling so
  each dump sits where its own theorem is stated.

These files are the user-facing tooling layer.  They reuse the same naming and
typing generators as the proof development.

Note that all three drivers generate over `rev nodes`.  `Ordered_nodes` places a
callee after its caller while the signature accumulator grows front-to-back, so
the reversal is what puts a callee's signature in the accumulator before its
caller needs it.
