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

