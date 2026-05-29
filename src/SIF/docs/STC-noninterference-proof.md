# STC Translated Noninterference

## Scope

`SecStcNonInterference.v` proves the target-side noninterference theorem that
is actually exported by this development.  The theorem is about translated STC
systems, not arbitrary STC systems.

The main theorem is:

- `translated_system_noninterference_outputs`

## Core Definitions

- `tuple_stream_low_eq`
  is the target-facing low-equivalence relation on STC tuple streams.
- `translated_system_behavior`
  states that an observed STC behavior comes from an NLustre memory-semantics
  run together with the translated `initial_state` and `loop` witnesses.
- `system_security`
  packages the translated-system identity, source and target signature lookups,
  `Signature_head_consistent`, and the underlying source
  `node_security` witness.

The theorem is therefore phrased entirely in terms of translated STC systems,
while keeping the source proof obligations hidden inside `system_security`.

## Conversion Lemmas

Two small conversion lemmas connect the source and target observation formats:

- `history_low_eq_of_tuple_stream_low_eq`
- `tuple_stream_low_eq_of_history_low_eq`

They let the proof move back and forth between:

- the NLustre history view used by the source theorem, and
- the tuple-stream view used by the STC theorem statement.

## Proof Ingredients

The target theorem combines four already proved components.

### Source Noninterference

`SecNLusNonInterference.node_noninterference_outputs` gives low-equivalent
source outputs once the source node is secure and the source inputs are
low-equivalent.

### NLustre Indexed / Memory Bridge

The repository already contains the bridge between indexed NLustre semantics
and the memory semantics used by the STC translation correctness theorem.

### Translation Correctness

`NLustreToStc.Correctness.correctness_loop` transports an NLustre memory run to
the translated STC `initial_state` and `loop` behavior.

### Signature Preservation

`SecNLusStcTranslation.generated_program_signatures_preserved_global` ensures
that the generated source and target signatures agree on the visible interface
and on call behavior.  This is what lets the source `node_security` witness be
reused as the semantic security witness for the translated STC system.

## Proof Flow

The target theorem follows a direct bridge argument.

1. Use `system_security` to recover the source node, the generated source and
   target signatures, and the source `node_security` witness.
2. Convert target input low-equivalence into the NLustre history form consumed
   by the source theorem.
3. Apply `node_noninterference_outputs` to obtain low-equivalent source
   outputs.
4. Use the indexed/memory bridge plus translation correctness to show that the
   observed STC outputs are exactly the translated outputs of those source
   runs.
5. Convert the resulting source output relation back to
   `tuple_stream_low_eq`.

## Why The Theorem Mentions Base-Clock Equality

The STC theorem assumes
`eq_str (clock_of xss) (clock_of xss')`.
This is the target-side packaging of the clock alignment needed to compare the
two translated behaviors pointwise.  The source theorem already works with
clocked histories; this hypothesis is the STC-facing way of carrying the same
alignment requirement.

## Resulting Interface

The exported theorem says:

- if two observed STC behaviors come from translated executions of the same
  secure source node,
- and their translated inputs are low-equivalent,
- and their base clocks agree,

then their translated outputs are low-equivalent as well.

This is the exact target theorem justified by the current development.
