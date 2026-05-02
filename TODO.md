# TODO

- [x] Save a detailed indexed-semantics proof plan for NLustre noninterference in `src/SIF/docs/Non-interference-proof.md`.
- [x] Add the indexed low-observation and `(⊑ t)` projection definitions to `src/SIF/SecNLusNonInterference.v`.
- [x] Standardize NLustre noninterference vocabulary: paper `s` = Coq `dlt`, paper `ρ` = `sig.(s_constraints)`.
- [x] Refine the NLustre noninterference theorem shape and proof phases in `src/SIF/docs/Non-interference-proof.md`.
- [x] Document the main proof-engineering explanation points for indexed NLustre noninterference in `src/SIF/docs/Non-interference-proof.md`.
- [x] Prove the indexed simple-case helper layer in `src/SIF/SecNLusNonInterference.v`: simple-security specializations, history-switch lemmas, and `EqDef`/`EqFby` noninterference.
- [x] Record the current indexed NLustre noninterference proof status and next theorem-level steps in `src/SIF/docs/Non-interference-proof.md`.
- [x] Document why `n_ingt0` and equal security levels do not suffice for the node theorem without a causality/acyclicity assumption.
- [x] Extract the NLustre causality formalization into `src/SIF/NLustreCausality.v` and register it in `vfiles` and `_CoqProject`.
- [ ] Re-run direct `coqc` on `src/SIF/NLustreCausality.v` and the rewired `src/SIF/SecNLusNonInterference.v`, then fix any refactor fallout.
- [ ] Finish `node_noninterference_vars_defined_raw` using the imported NLustre causality induction.
- [ ] Add the `EqApp` and reset-call noninterference lemmas and connect them to `node_security`.
- [ ] Derive the output-facing corollaries from the internal `vars_defined` theorem.
