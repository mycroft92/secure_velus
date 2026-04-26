Resume Plan

Current branch target after merge:
- `constraint_gen`

Current proof state:
- The simplify-completeness bridge is connected in `SecNLusStcTranslation.v`.
- Raw NLustre constraint generation now has a structural well-formedness theorem in `SecNLusTyping.v`:
  `generate_node_eqns_constraints_wf`.
- The two structural obligations behind the old derived readiness predicate are
  discharged in `generated_node_simplify_ready_from_generated_env`:
  - `wf_constraints raw`
  - `forall x, In x locals -> ~ In x (sig_scope nsig)`
- The public/global theorems no longer assume
  `generated_node_simplify_ready_global`; they rebuild it internally from
  `generate_node_env` plus `SECNLUSTYPING.call_constraints_shape`.

What is still open:
- The remaining premise for the simplify-side theorem stack is now only
  `forall G1, SECNLUSTYPING.call_constraints_shape G1 env`.
- In practice, this means proving the signature-instantiation layer preserves:
  - singleton RHS shape
  - no duplicate RHS targets
  - output alignment with the caller-side `outtyp`

Immediate next step:
1. Prove a well-formedness theorem for `generate_constraints` in `SIFSignature.v`.
2. Use it to discharge `SECNLUSTYPING.call_constraints_shape`.
3. Prove the generated NLustre/STC signature scoping theorem pair.
4. Reassess the final theorem statements and remove any now-redundant premise.

Likely proof entry points:
- `subst_ident_constraint_correct`
- `subst_constraints_out_map`
- `generate_constraints`
- `signatures_preserved_calls`

Suggested commands to resume:
- `make src/SIF/SIFSignature.vo`
- `make src/SIF/SecNLusTyping.vo`
- `make src/SIF/SecNLusStcTranslation.vo`

Notes:
- `src/SIF_fresh/` is intentionally untouched.

The resume plan for tomorrow is:

  1. Prove the generate_constraints well-formedness/call-shape theorem in SIFSignature.v.
  2. Use it to discharge SECNLUSTYPING.call_constraints_shape.
  3. Prove the generated signature scoping theorems from the signature-layer scope metatheory.
  4. Then revisit the final preservation theorem statements and remove any redundant premise.

  Verification passed with:
  make src/SIF/SecNLusTyping.vo src/SIF/SecNLusStcTranslation.vo

  The untracked src/SIF_fresh/ directory was left untouched.
