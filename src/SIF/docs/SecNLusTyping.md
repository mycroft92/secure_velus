# SecNLusTyping

## Role

`SecNLusTyping.v` is the NLustre-side constraint generator.  Starting from a
generated node-local security environment, it produces:

- raw equation constraints,
- a simplified stored source signature,
- and a generated global of source signatures

## Generation Flow

The file is organized at three levels.

### Equation Level

`generate_eqn_constraint` types one NLustre equation.  The cases follow the
syntax:

- `EqDef`
- `EqFby`
- ordinary `EqApp`
- reset `EqApp`

Call equations do not replay signatures locally.  They reuse
`SIFSignature.generate_constraints`.

### Node Level

- `generate_eqns_constraints`
  folds equation generation over the node body
- `generate_node_sig`
  builds the stored signature for one node
- `generate_node_sig_scoped_env`
  recovers the right node-local environment and then calls
  `generate_node_sig`

The important node-level step is:

- `generate_node_sig`
  stores `SymTypes.simplify raw locals`

So node locals are eliminated before the signature is exported.

### Global Level

- `generate_all_signatures'`
  accumulates source signatures
- `generate_all_signatures_scoped_env`
  is the top-level node-scoped interface used downstream

## What `simplify` Means Here

The source generator and the target generator both use the same
`SymTypes.simplify`.  The stored source signature is therefore not just a
projection of the raw constraint list; it is the shared canonical form.

In particular, singleton-right-hand-side constraints are normalized so that a
target does not mention itself on the left.  That is why extracted dumps now
omit trivial self-dependencies.

## Main Theorem Families

- `generate_eqn_constraint_shape`
  one generated equation block has singleton right-hand sides for the defined
  variables
- `generate_eqns_constraints_shape`
  the full node body has the expected right-hand-side structure
- `generate_eqns_constraints_wf`
  whole-node raw constraints are well formed
- `generate_node_eqns_constraints_wf`
  node-level packaging of the same well-formedness fact
- `generate_eqn_constraint_scoped`
  one equation block only mentions identifiers from the generated node scope
- `generate_eqns_constraints_scoped`
  scopedness for the whole node body
- `generate_node_sig_scoped`
  the simplified stored source signature stays inside the visible interface
- `generate_all_signatures_scoped`
  scopedness for the generated source global
- `generate_node_sig_scoped_env`
  node-scoped entry point used by later files
- `generate_all_signatures_scoped_env`
  top-level source generator

## Downstream Use

- `SecNLusTypingCorrectness.v`
  strengthens the raw shape facts into `signature_good`, `NoDup`, freshness,
  and visibility results
- `SecNLusStcTranslation.v`
  compares these generated source signatures with generated STC signatures
- the source noninterference stack replays from the stored simplified
  signature back to the raw generated constraints
