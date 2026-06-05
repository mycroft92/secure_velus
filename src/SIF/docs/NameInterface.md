# NameInterface

## Role

`NameInterface.v` generates the symbolic identifiers used by the SIF
development.  It is the single source of truth for how raw node-local Lustre
names become generated security names, and it provides the lookup and freshness
facts used by every later typing and preservation proof.

## Data Model

- `node_aux_names`
  stores the generated clock and reset identifiers that belong to one node.
- `local_sec_env`
  is the per-node map from raw Lustre variables to generated security names.
- `node_scoped_env`
  is the outer map from node names to their own local generated environments.
- `find_node_env`
  looks up the generated local environment for one node name.
- `get_node_aux`
  recovers the generated clock/reset pair recorded for one node.

The module keeps node-local names local.  Two different nodes may reuse the
same raw variable name because the outer environment is keyed by node name.

## Generation Pipeline

1. `generate_local_env_for_node`
   allocates fresh security names for one node's inputs, outputs, locals,
   clock, and reset identifiers.
2. `generate_node_scoped_env'`
   folds that local step over a node list while storing each node's environment
   under its node name.
3. `generate_node_scoped_env`
   runs the fold from the empty environment and exposes the finished node-keyed
   environment plus auxiliary names.
4. `generate_node_env`
   runs the flat global allocator used by proofs that only need one shared raw
   variable map instead of the node-keyed view.

## Core Lookup Interface

- `get_mappings`
  bulk-looks up a plain list of raw identifiers and returns their generated
  names in the same order.
- `get_mappings_from_node`
  does the same for `(ident * A)` lists, which is the shape used by node
  inputs, outputs, and locals.
- `get_mappings_in`
  says every source identifier present in a successful bulk lookup really comes
  from a matching `Env.find`.
- `get_mappings_from_node_In`
  runs that argument in the opposite direction: every generated identifier in a
  successful result came from some raw variable in the original node list.
- `get_mappings_In` and related lemmas
  are the bookkeeping bridge between list-level lookup results and pointwise
  environment facts used later in proofs.

These lookup lemmas are what let the typing and noninterference proofs move
between list-level interfaces and pointwise environment facts.

## Structural Invariants

The main theorem groups are:

- `generate_node_scoped_env'_app_inv`
  splits a successful run on `ns1 ++ ns2` into the exact intermediate state
  reached after `ns1` and the tail run on `ns2`.
- `generate_node_scoped_env'_split_node`
  isolates the local generation step for one chosen node inside a larger
  successful node-scoped pass.
- `generate_node_env'_app_inv`
  gives the same successful-split decomposition for the flat global generator.
- `generate_node_env'_split_node`
  isolates one node's flat-name generation step inside a larger successful
  global run.
- `fresh_insert_preserves_find`
  says inserting one fresh generated name does not change existing lookup
  results for other keys.
- `fresh_map_list_preserves_find`
  lifts that stability fact across a whole list of fresh insertions.
- `generate_node_scoped_env'_preserves_find`
  says once a node environment has been inserted, later node generation does
  not change that stored mapping.
- `generate_local_env_for_node_injective`
  proves one node-local environment never maps two raw names to the same
  generated security identifier.
- `generate_node_env_injective`
  lifts that injectivity fact to the flat environment generated for the whole
  program.
- `generate_local_env_for_node_sec_range`
  proves every identifier generated for one node lives in the ordinary `sec`
  namespace.
- `generate_node_env_sec_range`
  gives the same namespace-range guarantee for the whole flat program
  environment.
- `generate_local_env_for_node_bounded`
  says names generated for one node stay below the final fresh-state bound
  returned by that node's generation run.
- `generate_local_env_for_node_fresh_from_bound`
  turns the bound fact around: any later `sec` gensym is fresh from that node's
  already-generated names.
- `generate_node_scoped_env'_bounded`
  lifts the same bound discipline to the entire node-scoped environment after a
  successful global pass.

Together these results say:

- previously generated names stay stable when later nodes are processed;
- generated security identifiers stay inside the intended namespace;
- one generated identifier cannot correspond to two different raw names;
- later nodes receive identifiers above the range already used by earlier
  nodes.

## Downstream Use

- `SecNLusTyping.v` and `SecSTCTyping.v` read node-local environments from this
  file before generating signatures.
- `SecNLusTypingCorrectness.v` and `SecStcTypingCorrectness.v` use the range,
  injectivity, and bound lemmas to prove signature goodness and freshness.
- `SecNLusStcTranslation.v` uses the split and freshness lemmas to justify
  caller/callee separation and reset-name side conditions.
- The NLustre noninterference proof uses the same lookup and bound lemmas to
  recover the exact generated environment of a secure node and of its callees.
