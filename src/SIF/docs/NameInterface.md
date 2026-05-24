# NameInterface

## Role

`NameInterface.v` is the shared naming layer for the SIF development.  It is
the point where raw NLustre/STC identifiers are assigned generated security
identifiers before either typing phase starts.

The current design is node-scoped:

- outer environment keyed by unique node names
- inner environment keyed by raw names local to that node

This is the naming pivot that made inter-node reuse of the same raw
input/local/output name legal again.

## Main Definitions

- `local_sec_env`: one node's local raw-name to security-name mapping
- `node_scoped_env`: the program-wide map from node names to local envs
- `generate_local_env_for_node`: allocate one node's local security names
- `generate_node_scoped_env`: allocate the outer env-of-envs used by the
  scoped generation path
- `generate_node_env`: legacy flat shared env, still used where a single
  shared mapping is enough

## Key Theorem Families

- lookup/mapping interface:
  - `get_mappings`
  - `get_mappings_from_node`
  - `get_mappings_in`
  - `get_mappings_In`
- split/provenance:
  - `generate_node_scoped_env'_app_inv`
  - `generate_node_scoped_env'_split_node`
  - `generate_node_env'_app_inv`
  - `generate_node_env'_split_node`
- monotonicity/freshness:
  - `fresh_insert_preserves_find`
  - `fresh_map_list_preserves_find`
  - `generate_local_env_for_node_fresh_from_bound`
  - `generate_node_scoped_env'_bounded`
- namespace/range:
  - `generate_local_env_for_node_sec_range`
  - `generate_node_env_sec_range`
- injectivity:
  - `generate_local_env_for_node_injective`
  - `generate_node_env_injective`

## Theorem Statements

- `get_mappings_in`: if `In x xs` and `get_mappings xs env = Some tys`, then
  there exists some `ty` such that `Env.find x env = Some ty` and `In ty tys`.
- `generate_node_scoped_env'_split_node`: a successful run over
  `prefix ++ n :: suffix` decomposes into four concrete steps:
  generate the prefix environments, generate `n`'s local environment, insert
  that local environment at `n.(n_name)`, and then continue on the suffix.
- `generate_local_env_for_node_sec_range`: every value stored in a successful
  node-local environment is a generated security identifier
  `Ids.gensym Ids.sec nsec`.
- `generate_node_scoped_env'_bounded`: if the incoming node-scoped environment
  is bounded above by the current fresh counter, then the generated
  node-scoped environment is bounded above by the final counter as well.
- `generate_node_env_injective`: if
  `generate_node_env all_nodes = OK (env, aux_names)`, then `env` is
  injective, so equal generated security identifiers imply equal source keys.

## Relation To The Final Theorem

The final lookup-based signature preservation theorem depends on this file in
two ways:

1. `SecNLusTyping.v` and `SecSTCTyping.v` both generate signatures from the
   same node-scoped naming data, so the translation proof can compare them
   directly.
2. `SecNLusTypingCorrectness.v` and `SecStcTypingCorrectness.v` use the range,
   injectivity, and split lemmas here to prove caller/callee freshness and
   generated-signature namespace facts.

Without this file, the translation proof would have to assume those naming
separation facts externally.
