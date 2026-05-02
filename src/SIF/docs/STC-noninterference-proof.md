# STC Non-Interference Plan

## Goal

Record the target-side theorem strategy needed after the source theorem is
finished.

The current files are:

- `src/SIF/StcCausality.v`
- `src/SIF/SecStcNonInterference.v`
- `src/SIF/SecNLusStcTranslation.v`

The important design update is:

- we do not currently need a standalone intrinsic STC noninterference proof;
- the required target-side theorem is the weaker translated-behavior result.

## Main Design Choices

- The STC side still reuses the source-generated naming layer from
  `NameInterface`.
  The local security environment is looked up by translated system name.
- The actual theorem should eventually live in `SecNLusStcTranslation.v`, not
  as a separate self-contained STC proof development.
- The STC causality interface should reuse the existing target scheduling
  predicate `StcWellDefined.Is_well_sch` rather than introducing a second
  graph formalization immediately, but this is auxiliary unless a stronger
  native STC theorem later becomes necessary.

## Weaker STC Result

The intended theorem is:

- take two secure NLustre source runs;
- use source-side NLustre noninterference to get low-equivalent low outputs;
- transport each run to a translated STC loop;
- conclude that the translated STC behaviors are also low-equivalent on the
  observable outputs.

So the STC theorem is existential and preservation-based:

- it talks about STC behaviors produced by translation;
- it does not quantify over arbitrary STC semantic runs.

## Why This Is Enough

The repository already contains the key transport ingredients:

- `NLMemSemantics.sem_msem_node` / `msem_sem_node`
- `NLustreToStc.Correctness.correctness_loop`
- `SecNLusStcTranslation.generated_program_signatures_preserved_global`

That makes the weaker theorem substantially cheaper than a fully native STC
proof.

## What The Scaffolding Files Still Do

- `SecStcNonInterference.v`
  Keeps the low-observation vocabulary available on the STC side in case the
  final corollary wants an explicit target-side projection relation.
- `StcCausality.v`
  Keeps a target-local scheduling/causality interface available if a stronger
  theorem later becomes necessary.

## Files Added

- `src/SIF/StcCausality.v`
  Thin target-side causality/scheduling interface built on top of
  `Is_well_sch`, currently auxiliary.
- `src/SIF/SecStcNonInterference.v`
  STC-side observation scaffold, not the main theorem file.

## Immediate Next Steps

1. Finish the main NLustre noninterference theorem first.
2. After that, add the translated-behavior STC corollary in
   `SecNLusStcTranslation.v`.
3. Only revisit a native STC proof if the weaker result later turns out to be
   insufficient.
