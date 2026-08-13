# Obc Translated Noninterference

## Scope

`SecObcNonInterference.v` proves the Obc-side noninterference theorem exported by
this development.  Like the STC theorem it is about *translated* classes, not
arbitrary Obc classes, and like the STC theorem it is a **transport**: the
imperative semantics is never attacked directly.  A behaviour of a translated
class is exhibited together with the STC behaviour behind it -- which is what
`StcToObc.Correctness.correctness_loop_call` produces -- and the STC theorem is
run on that.

The Obc layer differs from the STC layer in two ways that shape the whole file:

- Obc speaks `option val` streams where STC speaks `value` streams, so the
  observation format has to be converted in both directions.
- The compiler does not hand Obc the translated program.  It hands it
  `schedule (translate all_nodes)`.  Every statement below that mentions a
  program mentions the scheduled one.

## Main Theorems

Listed source-inwards; each row weakens the hypotheses of the row above it.

- `translated_class_noninterference_outputs`
  two Obc executions of the same secure source node have low-equivalent output
  streams whenever their *dataflow* inputs are low-equivalent and their base
  clocks agree.  The input hypothesis stays at the dataflow level on purpose --
  see "Why the input hypothesis is asymmetric".
- `translated_class_noninterference_outputs_obc`
  the same with both sides phrased over Obc streams, for a caller who can also
  supply `same_low_presence`.
- `translated_class_noninterference_outputs_step`
  the same again, with both stream hypotheses and the conclusion indexed by the
  emitted class's `step` method rather than by the STC system's interface.
- `class_noninterference_outputs`
  the same, stated against the class-level witness `class_security` rather than
  the STC-level `system_security`.
- `translated_node_noninterference_outputs_step`
  **the exported theorem.**  Only `Gsrc` appears; `Gstc`, `Gstcs` and `Gobc` are
  produced internally, and the security input is `node_security` on the NLustre
  node.
- `translated_node_noninterference_outputs_from_msem`
  the same with the two `translated_class_behavior` hypotheses discharged too:
  the caller exhibits two NLustre `msem_node` runs and the input
  correspondences, and the class behaviours are built.

## Core Definitions

- `obc_stream_low_eq`
  the `option`-valued reading of `StcNI.tuple_stream_low_eq`: two runs agree on
  every low position at which **both** are present.  Absence is not itself
  constrained, exactly as in the STC statement, where an `absent` slot carries
  no `nth_error` witness either.
- `same_low_presence`
  the missing half: the two runs agree on *which* low inputs are present.
- `translated_class_behavior`
  an Obc behaviour together with the dataflow behaviour behind it and the two
  stream correspondences `correctness_loop_call` establishes -- inputs agree
  wherever the dataflow value is present (`eq_if_present`), outputs are the
  dataflow outputs read through `value_to_option`.  `xss`/`yss` stay explicit
  because the clock premise of the STC theorem is stated over them.
- `class_security`
  packages the STC witness `system_security`, the signature lookups in `Gstc`,
  `Gstcs` and `Gobc`, `signatures_preserved` across the scheduling step, and
  `Signature_head_consistent_obc` for the last leg.

## Conversion Lemmas

- `obc_stream_low_eq_of_tuple_stream_low_eq`
  the output side of the correspondence is exact -- `outs` is the pointwise
  image of `yss` -- so low-equivalence crosses it.  This is the direction the
  theorem needs.
- `tuple_stream_low_eq_of_obc_stream_low_eq`
  the input side, which needs `same_low_presence` as an extra premise.
- `translated_class_behavior_from_system`
  builds a class behaviour from an STC one, via `correctness_loop_call`.
- `translated_class_step_method`, `translated_class_step_interface`
  the STC system's interface *is* the emitted class's `step` method's:
  `translate_system` takes `m_in := idty s_in` and `m_out := idty s_out`, and
  `schedule_system` copies both.  This is what lets the conclusion be read off
  the class the compiler emits without assuming anything new.

## Proof Ingredients

### STC Noninterference

`StcNI.translated_system_noninterference_outputs` gives low-equivalent STC
outputs once the system is secure and the STC inputs are low-equivalent.

### Translation Correctness

`StcToObc.Correctness.correctness_loop_call` transports a scheduled STC run to
an Obc `loop_call`, and gives the two stream correspondences.

### Signature Preservation

Two legs, not one.  `SecNLusStcObcEnv.generated_signatures_preserved_by_scheduling`
carries the STC signatures across `schedule`, and
`SecStcObcTranslation.generated_program_signatures_preserved_obc_global` carries
them to Obc.  Both are assembled by
`SecNLusStcObcEnv.generated_program_signatures_preserved_obc_scheduled`.

### Signature Generation Totality

The reason the exported theorem needs no signature environment.  Where one
phase's generator succeeded, the next one's does too:

- `NLusStcBridge.generate_all_sys_signatures_scoped_env_ok`
  NLustre success implies STC success on `translate all_nodes`.
- `SecStcTypingCorrectness.generate_all_sys_signatures_reorder_ok_scoped`
  STC success survives a reordering of every system's body, so it survives
  `schedule`.  The scheduler only permutes bodies, so the two runs build their
  accumulators in lockstep; the induction re-establishes `sig_env_agrees` at
  each step.
- `StcObcBridge.generate_all_class_signatures_scoped_env_ok`
  STC success implies Obc success on the emitted classes.
- `generate_all_signatures_chain_ok` chains the three, and
  `generate_all_signatures_chain_ok_from_source` additionally derives the
  translated program's clocking from the source's, via the translation's own
  `NL2StcClocking.translate_wc`.

The chain is *relative* -- it starts from NLustre success.  That base case is
proved too, in `SecNamingTotality.v` and `SecNLusTypingTotality.v`:
`source_signature_generation_total` says an ordered, well-clocked source program
has a naming run and a successful NLustre generator run.  See
`docs/signature-generation-totality.md`.  The theorems below still *take* the
two `generate_... = OK` hypotheses rather than discharging them internally --
composing them needs the `all_nodes` / `rev all_nodes` mismatch settled first --
but they are now provable rather than merely assumed, so nothing here is
vacuous.

The Obc leg's one side condition with no STC counterpart -- that the naming pass
gave every instance of a system a state name, since the translated reset method
touches them all while STC only looks up the instances it resets -- is
*discharged*, not assumed.  `translate_node_insts_named`,
`schedule_system_insts_named` and `scheduled_translate_insts_named` carry it
from `NLusStcBridge.generate_node_scoped_env_insts_named`, which reads it off the
naming pass: `generate_local_env_for_node` builds the instance environment from
exactly `map fst (gather_insts n_eqs)`, and `gather_eqs` collects the same ones.

## Proof Flow

1. From `node_security` and the NLustre generator's success, run the totality
   chain to obtain `Gstc`, `Gstcs`, `Gobc` and, via
   `class_security_from_node_security`, the `class_security` witness.
2. Read the two class behaviours' dataflow halves out of
   `translated_class_behavior`.
3. Convert Obc input low-equivalence to `tuple_stream_low_eq` using
   `same_low_presence` and `eq_if_present`.
4. Apply the STC theorem.
5. Convert the resulting `tuple_stream_low_eq` on outputs back to
   `obc_stream_low_eq` through `value_to_option`.
6. Re-index the conclusion by the `step` method's `m_out`.

## Why The Input Hypothesis Is Asymmetric

`translated_class_noninterference_outputs` states the input hypothesis at the
dataflow level even though its conclusion is at the Obc level.  This is not an
oversight.  `eq_if_present` says nothing at all about an Obc slot whose dataflow
value is absent, so Obc-level agreement on the inputs is strictly *weaker* than
`tuple_stream_low_eq` and cannot replace it without also assuming the two runs
agree on which inputs are present.  That assumption is `same_low_presence`, and
the `_obc` variant is exactly the version that takes it.

The output side has no such gap: `outs` is the pointwise image of `yss`, so the
conversion is an equivalence.

## Why The Theorem Mentions Base-Clock Equality

Unchanged from the STC layer.  `eq_str (clock_of xss) (clock_of xss')` is the
clock alignment needed to compare the two behaviours pointwise; it is carried
through untouched.

## Resulting Interface

The exported theorem says:

- if two Obc behaviours come from executions of the class the compiler emits for
  the same secure source node,
- and the source program is well-clocked, ordered and causal,
- and the scheduled STC program is well-scheduled (which the compiler *checks* --
  `NLCorrectness.is_well_sch_program` -- rather than proves, so it is genuinely
  a hypothesis),
- and their low inputs agree, in presence and in value,
- and their base clocks agree,

then the outputs of the emitted `step` method are low-equivalent.

No signature environment for STC, for the scheduled STC program, or for Obc has
to be supplied by the caller: the generators are proved total along the chain.
The two source-side hypotheses that remain -- the naming run and the NLustre
generator run -- are provable for any ordered, well-clocked program
(`source_signature_generation_total`), so the statement is not vacuous; they are
discharged by the caller rather than inside the theorem.
