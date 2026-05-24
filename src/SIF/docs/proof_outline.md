# SIF Proof Outline

## Goal

The active thesis theorem is the weakened NLustre-to-STC signature
preservation result in `SecNLusStcTranslation.v`, ending at:

- `generated_program_signatures_preserved_global`

The theorem preserves agreement on the shared interface and local scope while
allowing STC-only auxiliary variables such as reset-instance names.

## Module Ownership

### `SecNLusTyping.v`

Owns source-side symbolic typing and its direct structural theorems:

- raw NLustre constraint generation
- source signature generation
- scopedness and well-formedness results for generated NLustre constraints

### `SecSTCTyping.v`

Owns target-side symbolic typing:

- STC transition-constraint typing
- reset-environment generation
- STC signature generation
- scopedness results for translated STC constraints and generated STC signatures

### `NameInterface.v`

Owns the shared naming provenance:

- node-scoped environment generation
- split lemmas for prefix/current-node reasoning
- security-name range and injectivity facts
- generated-name freshness from bounds

### `SecContext.v`

Owns the generic monadic/environment interface:

- the state/error monad
- lookup consistency lemmas
- generic `mmap` / `option_to_sec` extensionality facts

### `SecTypes.v`

Owns the generic lattice-mapping layer:

- `agree_on`
- `preserves_on`
- scoped concatenation
- lattice-mapping update agreement lemmas

### `SIFSignature.v`

Owns signature-local call-instantiation metatheory:

- `signature_good`
- `generate_constraints`
- `call_subst_fresh` / `call_subst_scoped`
- `inst_valuation` and lattice-mapping replay lemmas
- correctness/completeness of instantiated call constraints

### `SecNLusTypingCorrectness.v`

Owns source-local correctness facts used by the translation proof:

- shared-name inversion facts for generated node environments
- generated-node simplify readiness
- generated NLustre signature scopedness for generated globals

### `SecStcTypingCorrectness.v`

Owns target-local correctness facts used by the translation proof:

- reset-environment range/injectivity facts
- reset-environment lookup preservation facts
- generated STC signature scopedness for generated globals

### `SecNLusStcTranslation.v`

Owns the cross-phase proof:

- weak preservation notions (`agree_on`, `preserves_on`, `signatures_preserved`)
- scoped composition (`preserves_on_concat_scoped`)
- equation/node/system preservation across translation
- the global generated-signature consistency theorem
- the final program theorem

## Why Clocking Matters

Clocking is used here as a structural discipline on generated constraints.
It ensures that every symbolic variable mentioned by generated constraints comes
from the current node/system scope, except for explicit STC reset-instance
auxiliaries.

The relevant facts are:

- `wc_env`
- `wc_equation`
- `wc_node`
- `wc_global`
- STC-side translated-constraint clocking used by
  `generate_trconstrs_constraints_scoped_on_keys`

## Theorem Flow

### Raw source side

From `SecNLusTyping.v`:

- `generate_eqn_constraint_scoped`
- `generate_eqns_constraints_scoped`
- `generate_node_eqns_constraints_wf`
- `generate_node_sig_scoped`
- `generate_all_signatures_scoped`

These show that generated NLustre constraints are well formed and only mention
the visible source scope.

### Raw target side

From `SecSTCTyping.v`:

- `generate_trconstr_constraint_scoped_on_keys`
- `generate_trconstrs_constraints_scoped_on_keys`
- `generate_sys_signature_scoped`
- `generate_all_sys_signatures_scoped`

These show that generated STC constraints are scoped to the visible target
scope together with the reset-instance names actually used by the translated
block.

### Translation-side composition

From `SecNLusStcTranslation.v`:

- `eqn_preserv`
- `translated_eqns_constraints_scoped`
- `preserves_on_concat_scoped`
- `eqns_preserv_scoped`
- `node_preserv_scoped`
- `generated_node_preserv_scoped`

This layer combines one-equation preservation with scoped target composition and
the reset-extra bookkeeping used for translated reset calls.

### Simplify/signature bridge

From `SecNLusTypingCorrectness.v` and `SecNLusStcTranslation.v`:

- `generated_node_simplify_ready_from_local_env`
- `generated_signatures_preserved_from_simplify_bridge_local_env`

This layer moves from raw generated constraints to stored simplified
signatures.

### Global consistency

From `SecNLusStcTranslation.v`:

- `Signature_consistent_cons`
- `generate_all_signatures_consistent_scoped'`
- `generate_all_signatures_consistent`

This is the accumulator induction that rebuilds source/target signature
consistency for generated globals.

### Final theorem stack

The active dependency chain is:

1. `eqn_preserv`
2. `eqns_preserv_scoped`
3. `node_preserv_scoped`
4. `generated_node_preserv_scoped`
5. `generated_signatures_preserved_from_simplify_bridge_local_env`
6. `generate_all_signatures_consistent`
7. `generated_program_signatures_preserved_global`

The public signature theorem at step 7 is lookup-based: it reads the generated
source/target signature globals through `find_signature` and returns
`Signature_head_consistent` directly, instead of rerunning per-node signature
generation.

## Statement Snapshot

- `eqn_preserv`: one translated STC block preserves satisfiability of the
  corresponding NLustre equation on the shared scope, while allowing STC-only
  reset-instance auxiliaries outside that scope.
- `node_preserv_scoped`: the node-level theorem lifts that preservation result
  to one aligned NLustre node and translated STC system using the concrete
  generated interface variables, locals, clock type, reset type, and reset
  extras.
- `generated_program_signatures_preserved_global`: if the shared node-scoped
  environments and both generated signature globals are built successfully and
  the source program is well clocked, then every source signature lookup has a
  matching target lookup with `Signature_head_consistent`.

## Call-Side Status

The final theorem stack no longer mentions either of the old call-side bridge
premises:

- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

Both are now discharged internally in `SecNLusStcTranslation.v` through:

- node-scoped naming provenance from `NameInterface.v`
- generated-signature structure from `SecNLusTypingCorrectness.v`
- target reset-env facts from `SecStcTypingCorrectness.v`
- call-instantiation metatheory from `SIFSignature.v`
