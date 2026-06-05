# STC Translated Noninterference

## Scope

`SecStcNonInterference.v` proves the target-side theorem exported by the SIF
development.  The statement is about translated STC systems, not arbitrary
STC systems.

The main theorem is:

- `translated_system_noninterference_outputs`

It says two translated STC executions of the same secure source node have
low-equivalent outputs whenever their translated inputs are low-equivalent and
their base clocks agree.

## Core Definitions

- `tuple_stream_low_eq`
  pointwise low-equivalence of STC input or output tuple streams
- `translated_system_behavior`
  an observed STC behavior really comes from a translated NLustre execution
- `system_security`
  packages the translated system, aligned source/target signature lookups,
  `Signature_head_consistent`, and the underlying secure source node witness

The target theorem is therefore phrased entirely in STC terms while hiding the
source-side proof obligations inside `system_security`.

## Proof Ingredients

The theorem combines four already proved components.

1. `SecNLusNonInterference.node_noninterference_outputs`
   source-side output noninterference
2. the repository's bridge between indexed NLustre semantics and the memory
   semantics used by STC translation correctness
3. `NLustreToStc.Correctness.correctness_loop`
   translation correctness from NLustre memory runs to STC behavior
4. `SecNLusStcTranslation.generated_program_signatures_preserved_global`
   lookup alignment and call preservation between generated source and target
   signatures

The last ingredient already packages call preservation between normalized
stored signatures, so the target theorem does not reopen the symbolic replay
proof.

## Proof Flow

The argument is a direct bridge.

1. recover the secure source node and aligned generated signatures from
   `system_security`
2. convert target input low-equivalence into the history relation consumed by
   the source theorem
3. apply the source theorem to obtain low-equivalent source outputs
4. use the indexed/memory bridge and translation correctness to identify the
   observed STC outputs with those translated source outputs
5. convert the result back to `tuple_stream_low_eq`

## Why Base-Clock Equality Appears

The theorem assumes `eq_str (clock_of xss) (clock_of xss')`.  This is the
target-side form of the same clock-alignment requirement already present in
the source theorem.

## Result

The exported theorem is the exact STC-facing noninterference guarantee proved
by the current development.
