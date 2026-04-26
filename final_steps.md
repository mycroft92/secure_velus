Resume Plan

Current branch target after merge:
- `constraint_gen`

Current proof state:
- The simplify-completeness bridge is connected in `SecNLusStcTranslation.v`.
- Raw NLustre constraint generation now has a structural well-formedness theorem in `SecNLusTyping.v`:
  `generate_node_eqns_constraints_wf`.
- The two structural obligations behind
  `generated_node_simplify_ready_global` are discharged in
  `generated_node_simplify_ready_from_generated_env`:
  - `wf_constraints raw`
  - `forall x, In x locals -> ~ In x (sig_scope nsig)`

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
3. Replace uses of `generated_node_simplify_ready_global` with
   `generated_node_simplify_ready_global_from_call_shape`.
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
