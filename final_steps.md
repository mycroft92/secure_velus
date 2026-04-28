Resume Plan

Current branch target after merge:
- `constraint_gen`

Current proof state:
- The simplify-completeness bridge is connected in `SecNLusStcTranslation.v`.
- Raw NLustre constraint generation now has a structural well-formedness theorem in `SecNLusTyping.v`:
  `generate_node_eqns_constraints_wf`.
- The call-shape premise is now shared at the signature layer as
  `call_constraints_shape` in `SIFSignature.v`, and the NLustre typing
  development consumes that generic form directly.
- The two structural obligations behind the old derived readiness predicate are
  discharged in `generated_node_simplify_ready_from_generated_env`:
  - `wf_constraints raw`
  - `forall x, In x locals -> ~ In x (sig_scope nsig)`
- The public/global theorems no longer assume
  `generated_node_simplify_ready_global`; they rebuild it internally from
  `generate_node_env` plus `call_constraints_shape`.
- The STC-side scopedness path now exists in `SecSTCTyping.v`:
  `generate_trconstrs_constraints_scoped`,
  `generate_sys_signature_scoped`,
  `generate_all_sys_signatures_scoped`.
- That STC scopedness interface is now refined further:
  `trconstr_reset_keys`,
  `trconstrs_reset_keys`,
  `generate_trconstr_constraint_scoped_on_keys`,
  `generate_trconstrs_constraints_scoped_on_keys`.
  The older whole-reset-env scopedness theorems remain as wrappers.
- The caller-facing reshaping cleanup for `call_constraints_shape` has been
  pushed through the active proof files far enough that
  `SecNLusStcTranslation.v` is locally `coqc`-clean again.
- `SecNLusStcTranslation.v` now also contains the reset-extra bookkeeping
  needed for scoped concatenation:
  `eqn_reset_extras`, `eqns_reset_extras`,
  translated reset-key tracking, and the bridge from those keys to concrete
  reset-instance extras/freshness in the generated reset environment.
- The most recent full repo `make` passed the Coq proof phase and entered the
  extraction/OCaml build before being interrupted manually; that is the last
  global checkpoint for the current branch state.
- Structural follow-up, but not the current priority:
  once the scoped-composition cleanup is stable and validated, extract
  the source-side and target-side local correctness developments into new
  functorized files `SecNLusTypingCorrectness.v` and
  `SecStcTypingCorrectness.v`. Those files should own the generated
  signature/raw-constraint scopedness and well-formedness theorems, leaving
  `SecNLusStcTranslation.v` focused on the cross-phase preservation argument.

What is still open:
- The next active blocker is no longer the call-shape premise. It is the
  remaining scopedness/call-side assumptions in `SecNLusStcTranslation.v`
  after the append-closure route was removed.
- `env_injective` still needs to be made explicit in the work plan.
  Status update: the proof now lives in `NameInterface.v` as a property of
  `generate_node_env`, and the STC global scopedness bridge already derives it
  from `generate_node_env` internally.
  Remaining cleanup is only to remove any obsolete translation-local copies of
  the same proof when convenient.
- The translation file still exposes the stronger pointwise predicate
  `generated_system_signatures_scoped`; this should be replaced by the
  generated-global STC theorem from `SecSTCTyping.v` once the accumulator-based
  step theorem is refactored.
- The current weakened preservation theorem shape in
  `SecNLusStcTranslation.v` still looks viable, but only if the remaining call
  bridge is closed through
    `successful_call_substitutions_fresh` and `signatures_preserved_calls`,
    rather than left as a final-layer premise.

Immediate next step:
1. Keep the scoped theorem chain stable:
   `eqns_preserv_scoped`, `node_preserv_scoped`,
   `generated_node_preserv_scoped`, and the updated global corollaries.
2. Then return to the remaining scopedness/call-side assumptions:
   `generated_node_signatures_scoped`,
   `generated_system_signatures_scoped`,
   `successful_call_substitutions_fresh`,
   `signatures_preserved_calls`.

Likely proof entry points:
- `eqns_preserv`
- `preserves_on_concat_scoped`
- `SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys`
- `translated_reset_key_in_extras`
- `signatures_preserved_calls`

Build discipline:
- When checking any new development, use full repo `make` only.
- Do not rely on target-level `make` or standalone `coqc` as proof validation.

Notes:
- `src/SIF_fresh/` is intentionally untouched.
- `SecSTCTyping.v` and `SecNLusStcTranslation.v` are locally `coqc`-clean in
  the current branch state.
- The local debugging workflow remains:
  direct `_CoqProject`-compatible `coqc` first, then full repo `make` before
  any commit/merge/push.

The resume plan for tomorrow is:

  1. Introduce the precise STC-side scopedness lemma needed for one translated
     equation/list block and prove it in `SecSTCTyping.v` if possible.
  2. Keep the scoped global preservation route intact and validate with full
     repo `make`.
  3. Then continue trimming the remaining scopedness/call-side assumptions.

Saved checkpoint decision:
- Do not perform the correctness-module split while the scoped theorem path is
  still moving.
- First stabilize the new theorem path.
- Then perform the module extraction as a cleanup refactor.

  The untracked src/SIF_fresh/ directory was left untouched.
