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
- The caller-facing reshaping cleanup for `call_constraints_shape` has been
  pushed through the active proof files far enough that
  `SecNLusStcTranslation.v` is locally `coqc`-clean again.
- The most recent full repo `make` passed the Coq proof phase and entered the
  extraction/OCaml build before being interrupted manually; that is the last
  global checkpoint for the current branch state.

What is still open:
- The next active blocker is no longer the call-shape premise. It is the
  proof-artifact assumption `preserves_on_app_closed` in
  `SecNLusStcTranslation.v`.
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
  `SecNLusStcTranslation.v` still looks viable, but only if two remaining proof
  artifacts are removed:
  - `preserves_on_app_closed` should be replaced by the scoped composition path
    already started via `preserves_on_concat_scoped`;
  - the call bridge should be closed through
    `successful_call_substitutions_fresh` and `signatures_preserved_calls`,
    rather than left as a final-layer premise.

Immediate next step:
1. Refine the STC-side raw scopedness theorem so it can talk about only the
   reset-instance variables actually used by the translated block, rather than
   every entry of the full `reset_env`.
2. Strengthen `eqns_preserv` to thread private reset extras and compose head
   and tail via `preserves_on_concat_scoped`.
3. Delete `preserves_on_app_closed` from `eqns_preserv`, `node_preserv`,
   `generated_node_preserv`, and the final global theorem stack.
4. Then return to the remaining scopedness/call-side assumptions:
   `generated_node_signatures_scoped`,
   `generated_system_signatures_scoped`,
   `successful_call_substitutions_fresh`,
   `signatures_preserved_calls`.

Likely proof entry points:
- `eqns_preserv`
- `preserves_on_concat_scoped`
- `SECSTCTYPING.generate_trconstrs_constraints_scoped`
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
  2. Rewrite `eqns_preserv` around `preserves_on_concat_scoped`.
  3. Remove `preserves_on_app_closed` from the global preservation theorem
     stack and validate with full repo `make`.
  4. Then continue trimming the remaining scopedness/call-side assumptions.

  The untracked src/SIF_fresh/ directory was left untouched.
