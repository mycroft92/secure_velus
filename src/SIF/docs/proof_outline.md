# SIF Architecture

## Overview

This document gives the current module layout of `src/SIF/` and the intended
split between the symbolic and lattice-valued layers.

## Foundations

- `Helpers.v`
  list and positivity lemmas used by the symbolic layer
- `SymTypes.v`
  the single symbolic source of truth for symbolic types, constraints,
  scopedness, substitution, and `simplify`
- `SecLattice.v`
  abstract lattice interface and derived lattice lemmas
- `SecContext.v`
  state-and-error monad plus lookup lemmas shared by the generators
- `SecTypes.v`
  valuation agreement, replay updates, and satisfiability-preservation results
  over the symbolic objects defined in `SymTypes.v`

The key split is:

- `SymTypes.v`
  purely symbolic reasoning with no `dlt`
- `SecTypes.v`
  proofs that interpret symbolic constraints under lattice valuations

## Naming And Raw Generation

- `NameInterface.v`
  generated security-name allocation and node-scoped environments
- `SecCETyping.v`
  symbolic typing for clocks and CoreExpr fragments
- `SecNLusTyping.v`
  NLustre-side raw constraint generation and source signature construction
- `SecSTCTyping.v`
  STC-side raw constraint generation and target signature construction

Both `SecNLusTyping.v` and `SecSTCTyping.v` finish by calling the same
`SymTypes.simplify`, so source and target stored signatures use the same
normal form.

## Stored Signatures And Local Correctness

- `SIFSignature.v`
  stored signature format and call-instantiation metatheory
- `SecNLusTypingCorrectness.v`
  source-side structure, freshness, and visibility facts for generated
  signatures
- `SecStcTypingCorrectness.v`
  target-side reset-environment and generated-signature structure facts
- `NLustreCausality.v`
  causality facts used by the source noninterference proof

## Translation Preservation

- `SecNLusStcTranslation.v`
  proves that generated NLustre signatures preserve to generated STC
  signatures

This is where:

- equation-level preservation is proved,
- STC-only reset extras are isolated,
- call preservation is reconstructed from stored-signature metatheory,
- and the whole-program source and target globals are shown lookup-consistent

## Source Noninterference

- `SecNLusNonInterferenceSupport.v`
  observation model and generic semantic transport
- `SecNLusNonInterferenceHelpers.v`
  replay lemmas and generated-program bookkeeping
- `SecNLusNonInterferenceClockedStep.v`
  time-step induction
- `SecNLusNonInterference.v`
  exported NLustre noninterference theorem

The source proof keeps both the stored simplified signature and the raw
generated constraints, because replay arguments use the stored summary while
the step proof still reasons equation by equation over the raw node body.

## Target Noninterference

- `SecStcNonInterference.v`
  translated-system noninterference theorem obtained by combining:
  source noninterference, NLustre/STC semantic preservation, and generated
  signature preservation

## Constraint Export

- `SecNLusConstraintExport.v`
  executable NLustre dump path
- `SecStcConstraintExport.v`
  executable STC dump path

These reuse the same generators and therefore dump the same normalized
constraint form produced by `SymTypes.simplify`.
