# SIF Proof Outline

## Goal

The current thesis goal is the weakened NLustre-to-STC preservation theorem in
`SecNLusStcTranslation.v`, ending at:

- `generated_program_preserv_global`

The weakened statement does **not** require NLustre and STC valuations to be
identical everywhere.  It only requires them to agree on the shared
interface/local scope, while allowing STC-only auxiliary variables such as
reset-instance names.

## Why The Clocking Layer Matters

Clocking is not being used here for semantic preservation directly.  It is used
to justify **scope control**: every type variable mentioned by generated
constraints must come from the current node/system scope, except for explicit
STC-only reset-instance auxiliaries.

This is exactly the information needed to justify the scoped composition lemma
`preserves_on_concat_scoped` in place of the old append-closure path.

## Clocking Facts We Need

### 1. Local environment well-clocked

Needed fact:

- `wc_env vars`

Purpose:

- lets us turn membership facts `In (x, ck) vars` into clock well-formedness;
- is used both in NLustre-side scopedness and in STC-side scopedness.

Typical use sites:

- `SECNLUSTYPING.generate_eqn_constraint_scoped`
- `SECSTCTYPING.generate_trconstr_constraint_scoped_on_keys`

### 2. Local NLustre equations well-clocked

Needed fact:

- `Forall (wc_equation P vars) eqs`

Purpose:

- ensures free variables of equation clocks/expressions are in `vars`;
- in the `EqApp` case, gives the call-interface discipline:
  - actual inputs match callee inputs,
  - actual outputs match callee outputs,
  - reset variable belongs to the current local environment.

This is the source-side structural fact that makes scopedness proofs possible.

### 3. Translation preserves local clocking

Translation-layer wrappers:

- `translate_eqn_wc_local`
- `translate_eqns_wc_local`

Purpose:

- move from NLustre local clocking to STC local clocking without importing the
  full external proof stack into the preservation argument;
- provide the hypotheses required by
  `SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys`.

### 4. Node/global packaging

Standard source-side facts that may be needed when lifting from one equation
list to generated program theorems:

- `wc_node`
- `wc_global`
- `Ordered_nodes`

Purpose:

- recover well-clockedness of the currently translated node from the global
  program structure;
- justify lookup-based reasoning on callees in the ordered-node induction;
- support generated-global scopedness theorems when the proof leaves the
  equation-list level.

### 5. STC target-side key-scopedness

Provided by `SecSTCTyping.v`:

- `trconstr_reset_keys`
- `trconstrs_reset_keys`
- `generate_trconstr_constraint_scoped_on_keys`
- `generate_trconstrs_constraints_scoped_on_keys`

Purpose:

- the target scopedness theorem no longer needs the whole reset environment to
  be in scope;
- it only needs the specific reset keys actually consulted by the translated
  STC block.

This is the target-side theorem that makes scoped composition realistic.

## Translation-Specific Reset-Extra Layer

These lemmas live in `SecNLusStcTranslation.v` and connect the source equation
list to the target reset-instance auxiliaries:

- `reset_call_var`
- `reset_call_vars`
- `eqn_reset_extras`
- `eqns_reset_extras`
- `trconstrs_reset_keys_translate_eqns`
- `translated_reset_key_in_extras`
- `translated_reset_key_fresh`

Purpose:

- identify exactly which source equations create STC-only reset-instance
  variables;
- reconstruct the concrete extra-variable list used in the scoped composition
  proof;
- prove those extras are fresh from the shared NLustre/STC scope.

## Theorem Flow Toward The Final Preservation Theorem

### Source typing/scoping side

From `SecNLusTyping.v`:

- `generate_eqn_constraint_scoped`
- `generate_eqns_constraints_scoped`
- `generate_node_sig_scoped`
- `generate_all_signatures_scoped`
- `generate_node_eqns_constraints_wf`

Role:

- prove that NLustre-generated constraints and signatures only mention the
  visible source scope;
- provide the source-side input to `simplify_complete`;
- feed the source-side scopedness/global theorems used later in the translation
  layer.

### Target typing/scoping side

From `SecSTCTyping.v`:

- `generate_trconstr_constraint_scoped_on_keys`
- `generate_trconstrs_constraints_scoped_on_keys`
- `generate_sys_signature_scoped`
- `generate_all_sys_signatures_scoped`

Role:

- prove that translated STC constraints/signatures only mention the visible
  target scope plus the explicit reset-instance extras;
- support both raw target scopedness and the later signature-level scopedness
  theorems.

### Raw preservation side

From `SecNLusStcTranslation.v`:

- `eqn_preserv`
- `preserves_on_concat_scoped`
- the new local clocking/scopedness wrappers:
  - `translate_eqn_wc_local`
  - `translate_eqns_wc_local`
  - `translated_eqns_constraints_scoped_on_keys`
  - `translated_eqns_constraints_scoped`

Current scoped route:

- `eqns_preserv_scoped` composes:
  - single-equation preservation from `eqn_preserv`,
  - target scopedness from `translated_eqns_constraints_scoped`,
  - reset-extra freshness/nodup from the reset-extra layer,
  - `preserves_on_concat_scoped`.

This is the active replacement for the old append-closure path.

### Node/signature bridge side

Current bridge theorems:

- `generated_node_simplify_ready_from_generated_env`
- `generated_signatures_preserved_from_simplify_bridge`
- `generated_signature_step_consistent_concrete`
- `generate_all_signatures_consistent`

Role:

- move from raw node/system constraints to simplified stored signatures;
- rebuild `Signature_consistent` for generated globals;
- feed the final node/system/program preservation statements.

This bridge layer now sits on top of the scoped equation-list theorem rather
than the deleted append-closure route.

### Final public theorem stack

Current top-level endpoint:

- `generated_program_preserv_global`

Dependency chain:

1. raw preservation of one equation: `eqn_preserv`
2. raw preservation of an equation list: `eqns_preserv_scoped`
3. raw preservation of one node/system pair: `node_preserv_scoped`
4. generated-node raw theorem: `generated_node_preserv_scoped`
5. simplify/signature bridge:
   `generated_signatures_preserved_from_simplify_bridge_scoped`
6. global signature consistency:
   `generate_all_signatures_consistent`
7. final closed program theorem:
   `generated_program_preserv_global`

The current cleanup target is to remove the remaining scopedness/call-side
assumptions from this chain without introducing a new unrealistic theorem-level
assumption.

## Remaining Cleanup Targets

The final theorem stack should eventually stop mentioning:

- `call_constraints_shape`
- `generated_node_signatures_scoped`
- `generated_system_signatures_scoped`
- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

Current priority order:

1. replace pointwise scopedness assumptions by generated-global scopedness
2. close the call-side freshness/preservation bridge

## Relation To The Paper

The paper's proof can be read as:

1. local preservation for translated equations/calls,
2. lifting to nodes/systems,
3. lifting to generated globals,
4. concluding preservation at the program level.

This development follows that overall structure, but with a weaker semantic
relation (`agree_on` / `preserves_on`) to account for STC-only auxiliary
variables introduced during translation.
