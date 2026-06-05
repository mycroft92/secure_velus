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
  environments.
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

## Constraint Export

- `SecNLusConstraintExport.v`
  executable dump of generated NLustre constraints and stored signatures.
- `SecStcConstraintExport.v`
  corresponding executable dump for generated STC constraints.

These files are the user-facing tooling layer.  They reuse the same naming and
typing generators as the proof development.
