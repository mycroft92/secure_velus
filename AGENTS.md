This repository contains thesis work built on top of the Velus compiler toolchain.

## Core Context

- The target reference is `STC_translation_preservation-2.pdf`. Read it before doing substantial work.
- `README.md` was written by the Velus team. Do not treat it as thesis-specific guidance.
- Velus compiles Lustre through several lowering phases, including `Lustre`, `NLustre`, `STC`, `Obc`, and finally `CLight`.

## Scope For This Thesis

- Focus on the `SIF` directory. That is where the thesis-specific implementation lives.
- Avoid reading from `Compcert` unless it is strictly necessary.
- Avoid reading `Obc`, `ObcToClight`, `StcToObc`, and `Transcription` for now. They are not relevant to the current thesis task.
- In general, each phase is mostly self-contained in its similarly named directory, except at phase boundaries.

## Modification Policy

- Avoid modifying Velus team code unless the paper truly requires it.
- Prefer implementing thesis-specific logic in the thesis-specific parts of the repository.
- When adding a new file or folder, update the relevant `vfiles`, then run `make clean`, then reconfigure with `./configure -clightgen x86_64-linux`.
- If you only modify existing files, that reconfiguration step is not required.

## Workflow Rules

- Before starting any changes, create/change and work on a branch named `AI_version` from the current state.
- Do not merge back without approval.
- Update `TODO.md` whenever you complete a task. Create it if it does not already exist.
- Document important design decisions clearly before proceeding with major changes.
- Each addition needs to be accompanied with a comment on where that piece fits if its a big developement
- Every theorem/lemma  needs a commentary on how it relates to paper

## Current Research Goal

Implement the paper as closely as possible, but correctness proofs take priority over matching an initial design exactly. Alternate design decisions are acceptable if they make the proof go through cleanly.

The immediate goal is to state and prove preservation of the security type system across translation from `NLustre` to `STC`.

Relevant files:

- `SecNLusTyping.v`: security type system for `NLustre`
- `SecSTCTyping.v`: analogous security typing work for `STC`
- `NameInterface.v`: an attempt to control name generation so the translation can be stated precisely
- `SecNLusStcTranslation.v`: current starting point for both the theorem statement and proof strategy

## Priority Task

Help state and prove the preservation theorem for the translation from `NLustre` to `STC`, using `SecNLusStcTranslation.v` as the starting point.
