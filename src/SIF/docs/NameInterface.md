# NameInterface

## Role

`NameInterface.v` generates the symbolic security identifiers used by the SIF
development.  It is the source of truth for how raw Lustre names become
generated security names, and it proves the lookup, range, injectivity, and
freshness facts used by every later typing and preservation proof.

## Main Data

- `node_aux_names`
  the generated clock and reset identifiers attached to one node
- `local_sec_env`
  the per-node map from raw Lustre variables to generated security names
- `node_scoped_env`
  the outer map from node names to their own local generated environments
- `find_node_env`
  lookup of one node-local generated environment
- `get_node_aux`
  lookup of one node's generated clock/reset pair

Two different nodes may reuse the same raw variable name.  The outer
environment is keyed by node name, so node-local naming remains local.

## Generation Pipeline

1. `generate_local_env_for_node`
   allocates fresh generated names for one node's inputs, outputs, locals,
   clock, and reset identifiers
2. `generate_node_scoped_env'`
   folds that step over the node list and stores the result under each node
   name
3. `generate_node_scoped_env`
   runs the fold from the empty environment
4. `generate_node_env`
   builds the flat global environment used by proofs that only need one raw
   variable map

## Lookup Interface

- `get_mappings`
  bulk lookup for a plain list of raw identifiers
- `get_mappings_from_node`
  bulk lookup for `(ident * A)` lists, which is the shape used by node
  inputs, outputs, and locals
- `get_mappings_in`
  every successful lookup result really came from the environment
- `get_mappings_from_node_In`
  every generated identifier in a successful result comes from some raw
  variable in the original node list
- `get_mappings_In` and related lemmas
  move between list-level lookup facts and pointwise `Env.find` facts

These lemmas are what let later proofs talk about generated signatures using
the list-based interfaces produced by the generators.

## Structural Invariants

The main theorem families say that:

- successful generation over `ns1 ++ ns2` can be split at the exact
  intermediate state after `ns1`
- once a node environment has been inserted, later generation does not change
  it
- generated node-local environments are injective
- generated ordinary visible names stay in the `sec` namespace
- later generated names are above the range used by earlier nodes, and are
  therefore fresh from them

Representative lemmas are:

- `generate_node_scoped_env'_split_node`
- `generate_node_env'_split_node`
- `fresh_insert_preserves_find`
- `generate_node_scoped_env'_preserves_find`
- `generate_local_env_for_node_injective`
- `generate_node_env_injective`
- `generate_local_env_for_node_sec_range`
- `generate_node_env_sec_range`
- `generate_local_env_for_node_bounded`
- `generate_local_env_for_node_fresh_from_bound`

## Downstream Use

- `SecNLusTyping.v` and `SecSTCTyping.v`
  read node-local environments from this file before generating signatures
- `SecNLusTypingCorrectness.v` and `SecStcTypingCorrectness.v`
  use the range, injectivity, and bound lemmas to prove signature structure
  and freshness
- `SecNLusStcTranslation.v`
  uses the split and freshness lemmas to separate caller scope from STC-only
  reset extras
