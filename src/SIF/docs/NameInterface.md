# NameInterface

## Role

`NameInterface.v` generates the symbolic identifiers used by the SIF
development.  It is the single source of truth for how raw node-local Lustre
names become generated security names, and it provides the lookup and freshness
facts used by every later typing and preservation proof.

## Data Model

- `node_aux_names` stores the generated clock and reset identifiers for one
  node.
- `local_sec_env` maps one node's raw inputs, outputs, and locals to generated
  security identifiers.
- `node_scoped_env` maps node names to their `local_sec_env`.
- `find_node_env` and `get_node_aux` recover the generated data for one node.

The module keeps node-local names local.  Two different nodes may reuse the
same raw variable name because the outer environment is keyed by node name.

## Generation Pipeline

1. `generate_local_env_for_node` allocates one node's local environment and its
   clock/reset names.
2. `generate_node_scoped_env'` folds that step over a node list and builds the
   full `node_scoped_env`.
3. `generate_node_scoped_env` exposes the top-level node-scoped generator.
4. `generate_node_env` provides a flat environment interface for the parts of
   the development that only need a single shared map.

## Core Lookup Interface

- `get_mappings` looks up a list of raw identifiers in a local environment.
- `get_mappings_from_node` performs the same lookup on `(ident * A)` lists such
  as node inputs, outputs, and locals.
- `get_mappings_in`, `get_mappings_In`, and related lemmas convert successful
  bulk lookups back into individual `Env.find` facts.

These lookup lemmas are what let the typing and noninterference proofs move
between list-level interfaces and pointwise environment facts.

## Structural Invariants

The main theorem groups are:

- Split lemmas:
  `generate_node_scoped_env'_app_inv`,
  `generate_node_scoped_env'_split_node`,
  `generate_node_env'_app_inv`,
  `generate_node_env'_split_node`.
- Preservation lemmas:
  `fresh_insert_preserves_find`,
  `fresh_map_list_preserves_find`,
  `generate_node_scoped_env'_preserves_find`.
- Injectivity and range:
  `generate_local_env_for_node_injective`,
  `generate_node_env_injective`,
  `generate_local_env_for_node_sec_range`,
  `generate_node_env_sec_range`.
- Bounds and freshness:
  `generate_local_env_for_node_bounded`,
  `generate_local_env_for_node_fresh_from_bound`,
  `generate_node_scoped_env'_bounded`.

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
