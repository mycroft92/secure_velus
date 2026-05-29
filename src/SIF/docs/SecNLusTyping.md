# SecNLusTyping

## Role

`SecNLusTyping.v` is the NLustre-side symbolic typing generator.  It reads a
generated node-local security environment and turns one NLustre node into:

- raw equation constraints,
- a simplified stored signature,
- and a global list of generated source signatures.

## Generation Structure

The file is organized around three levels.

### Equation Level

`generate_eqn_constraint` types one NLustre equation.  The cases mirror the
syntax:

- `EqDef`
- `EqFby`
- ordinary `EqApp`
- reset `EqApp`

For call equations, the generator looks up the callee signature in the current
global and instantiates it through `SIFSignature.generate_constraints`.

### Node Level

- `generate_eqns_constraints` folds equation generation over the node body.
- `generate_node_sig` packages the resulting raw constraints into a stored
  signature by simplifying away node locals.
- `generate_node_sig_scoped_env` is the node-scoped entry point used by the
  current development: it first recovers the node's local generated
  environment from `NameInterface.v` and then runs `generate_node_sig`.

### Global Level

- `generate_all_signatures'` accumulates source signatures.
- `generate_all_signatures_scoped_env` is the top-level current interface used
  by the translation and noninterference theorems.

## Main Theorem Families

- Shape and well-formedness:
  `generate_eqn_constraint_shape`,
  `generate_eqns_constraints_shape`,
  `generate_eqns_constraints_wf`,
  `generate_node_eqns_constraints_wf`.
- Scopedness:
  `generate_eqn_constraint_scoped`,
  `generate_eqns_constraints_scoped`,
  `generate_node_sig_scoped`,
  `generate_all_signatures_scoped`,
  `generate_node_sig_scoped_env`,
  `generate_all_signatures_scoped_env`.

The shape lemmas show that generated raw constraints have the expected single
target structure.  The scopedness lemmas show that every generated identifier
mentioned by the source constraints comes from the visible generated node
scope.

## Call Cases

The call cases do not implement their own substitution metatheory.  They rely
on `SIFSignature.v` for:

- call-block generation,
- well-formedness of instantiated call constraints,
- and scopedness of the caller-facing constraint block.

This keeps source typing focused on where the actual arguments come from and
what scope they live in, rather than on replaying signature substitutions.

## Downstream Use

- `SecNLusTypingCorrectness.v` strengthens these generation results with
  `signature_good`, `NoDup (signature_scope sig)`, and generated-name
  freshness.
- `SecNLusStcTranslation.v` uses the scoped generated source signatures when it
  compares NLustre and STC signatures.
- The NLustre noninterference proof uses the same generator to recover the raw
  source constraints tied to a secure node.
