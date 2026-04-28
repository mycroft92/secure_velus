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

What is still open:
- The remaining premise for the simplify-side theorem stack is now only
  `forall G1, call_constraints_shape G1`.
- In practice, this means proving the signature-instantiation layer preserves:
  - singleton RHS shape
  - no duplicate RHS targets
  - output alignment with the caller-side `outtyp`
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
1. Prove a well-formedness theorem for `generate_constraints` in `SIFSignature.v`.
2. Use it to discharge `call_constraints_shape`.
3. Rework the equation-list composition proof in `SecNLusStcTranslation.v` so
   it no longer depends on `preserves_on_app_closed`.
4. Replace the remaining stronger pointwise STC-scopedness predicate in
   `SecNLusStcTranslation.v` with the new `SecSTCTyping.v` global theorem.
5. Revisit the call-instantiation bridge and remove any premise that can be
   discharged from scopedness plus freshness.

Likely proof entry points:
- `subst_constraints_out_map`
- `generate_constraints`
- `eqns_preserv`
- `preserves_on_concat_scoped`
- `signatures_preserved_calls`

Build discipline:
- When checking any new development, use full repo `make` only.
- Do not rely on target-level `make` or standalone `coqc` as proof validation.

Notes:
- `src/SIF_fresh/` is intentionally untouched.
- `SecSTCTyping.v` is now locally `coqc`-clean and has been validated by full
  repo `make` reaching the next failure in `SecNLusStcTranslation.v`.
- The current next proof failure is in
  `SecNLusStcTranslation.v:constraintSatisfiable_ext`; continue the same local
  `coqc` then full-`make` loop from there.

The resume plan for tomorrow is:

  1. Prove the generate_constraints well-formedness/call-shape theorem in SIFSignature.v.
  2. Use it to discharge call_constraints_shape.
  3. Replace the pointwise STC-scopedness premise in SecNLusStcTranslation.v with the STC typing theorem.
  4. Then revisit the final preservation theorem statements and remove any redundant premise.

  The untracked src/SIF_fresh/ directory was left untouched.
