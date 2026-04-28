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
- If you only modify existing files, that reconfiguration step is not required.
- Use direct local `coqc` runs with the exact load-path flags from `_CoqProject` to isolate proof errors while editing.
- For SIF files, the local debug command template is:
  `coqc -R /root/secure_velus/src Velus -R /root/secure_velus/CompCert/lib compcert.lib -R /root/secure_velus/CompCert/common compcert.common -R /root/secure_velus/CompCert/backend compcert.backend -R /root/secure_velus/CompCert/cfrontend compcert.cfrontend -R /root/secure_velus/CompCert/driver compcert.driver -R /root/secure_velus/CompCert/flocq compcert.flocq -R /root/secure_velus/CompCert/exportclight compcert.exportclight -R /root/secure_velus/CompCert/cparser compcert.cparser -R /root/secure_velus/CompCert/x86_64 compcert.x86_64 -R /root/secure_velus/CompCert/x86 compcert.x86 src/SIF/<File>.v`
- Do not rely on `make src/...` targets for local debugging here; they may fail silently.
- Always validate with full repo `make` before any merge or push.
- Do not run `./configure` unless generated dependency/config files actually need to be refreshed.
- Do not run `make clean` unless the build state is genuinely broken and incremental `make` is no longer trustworthy.

## Workflow Rules

- Before starting any changes, create/change and work on a branch named `AI_version` from the current state.
- Do not merge back without approval.
- Update `TODO.md` whenever you complete a task. Create it if it does not already exist.
- Document important design decisions clearly before proceeding with major changes.
- Each addition needs to be accompanied with a comment on where that piece fits if its a big developement
- Every theorem/lemma  needs a commentary on how it relates to paper

## Current Repair Workflow

- Repair the development one file at a time, in this order:
  `SecNLusTyping.v`, then `SecSTCTyping.v`, then `SecNLusStcTranslation.v`.
- During each file-level fix, use the `_CoqProject`-compatible direct `coqc` command above to get complete error context quickly.
- After each file-level fix, validate that state with full repo `make`.
- Once that state is validated, document the change, commit on `AI_version`, merge into `constraint_gen`, and push before moving to the next file.
- For module/interface breakages, prefer importing the upstream module types explicitly in functor signatures.
  Do not recreate those dependencies locally with new `Module ... := ...Fun ...` bindings when the proper module-type argument should be threaded through instead.
- Keep proof-architecture cleanup separate from syntax/interface repair:
  first restore compilation, then trim theorem assumptions.

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
