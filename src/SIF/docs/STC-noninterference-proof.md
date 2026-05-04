# STC Non-Interference Plan

## Goal

Record the target-side theorem strategy after the source NLustre theorem is
finished.

The active files are now:

- `src/SIF/SecStcNonInterference.v`
- `src/SIF/SecNLusStcTranslation.v`
- `src/SIF/SecNLusNonInterference.v`

The important design decision is now fixed:

- we do not currently need a standalone intrinsic STC noninterference proof;
- the required STC-side result is the weaker translated-behavior theorem;
- the substantive semantic theorem should live in `SecStcNonInterference.v`;
- `SecNLusStcTranslation.v` stays the syntactic/preservation library
  underneath that bridge route.

## Bridge Route

The intended result is:

- take two secure NLustre source runs;
- use source-side NLustre noninterference to obtain low-equivalent observable
  outputs;
- transport both runs through the NLustre-to-STC semantic preservation chain;
- conclude that the resulting translated STC behaviors are also
  low-equivalent on the shared observable interface.

So the STC theorem is intentionally weaker than a native target theorem:

- it only speaks about STC behaviors that arise from translation;
- it does not quantify over arbitrary STC semantic runs.

## Why This Is The Right Route

The repository already contains the transport ingredients this corollary needs:

- `SecNLusNonInterference.v` for the source indexed theorem;
- `NLMemSemantics.sem_msem_node` / `msem_sem_node` to move between indexed and
  memory-style NLustre semantics;
- `NLustreToStc.Correctness.correctness_loop` for translation preservation of
  loops/behaviors;
- `SecNLusStcTranslation.generated_program_signatures_preserved_global` for
  source/target signature alignment on shared interface variables.

That is enough to justify a translated-behavior STC theorem without reopening a
separate intrinsic target proof architecture.

## Current File Roles

- `SecStcNonInterference.v`
  Home of the STC translated-behavior semantic theorem stack. It should stay
  bridge-oriented and should not grow into a second intrinsic target proof
  development.
- `SecNLusStcTranslation.v`
  Syntactic/preservation library consumed by `SecStcNonInterference.v`.

## Deferred Work

What is intentionally not on the critical path:

- a separate STC causality development;
- a full intrinsic STC noninterference theorem over arbitrary STC runs.

Those should only be revived if the preservation-based route turns out to be
too weak for the thesis statement.

## Current Status

The bridge route is now implemented in `SecStcNonInterference.v`.

The active semantic packaging is:

- `translated_system_behavior`
  states that an observed STC behavior is backed by an NLustre memory-semantics
  run plus the translated `initial_state`/`loop` witness.
- `system_security`
  is the target-facing analogue of `node_security`; it hides the source node
  witness but keeps the translated-system equality, source/target signature
  lookup facts, signature-head consistency, and the source `node_security`
  invariant.
- `translated_system_noninterference_outputs`
  is the weaker STC theorem actually justified by the development: it proves
  low-equivalent translated outputs for two translated STC behaviors under
  low-equivalent translated inputs and a shared base-clock hypothesis
  `eq_str (clock_of xss) (clock_of xss')`.

## Immediate Next Steps

1. Revalidate the full repository build once the STC bridge checkpoint is ready
   to commit.
2. Keep any later STC strengthening downstream of this bridge theorem, rather
   than rebuilding an intrinsic target proof stack first.
3. Continue the remaining thesis tasks, in particular the OCaml `-sif`
   constraint-dump path and any upstream packaging of the signature
   correspondence lemmas.
