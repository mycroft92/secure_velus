# Secure Velus: SIF Development on Top of the Velus EMSOFT'21 Artifact

This repository is a development on top of Velus's `emsoft21-artifact`
repository. The upstream Velus compiler, proofs, build system, and supporting
infrastructure remain in place here; our original work is concentrated in the
`src/SIF/` directory.

The upstream Velus documentation is still useful:

- `doc/index.html` links the EMSOFT 2021 article to the corresponding Coq
  definitions and proofs.
- `examples/readme.md` describes the example Lustre programs shipped with the
  artifact.

## Where Our Work Lives

The source related to our work is located in `src/SIF/`.

Work-map notes:

- [`src/SIF/docs/proof_outline.md`](src/SIF/docs/proof_outline.md)
- [`src/SIF/docs/call_metatheory.md`](src/SIF/docs/call_metatheory.md)

For the current simplification split:

- `SymTypes.v` is the single symbolic source of truth for `simplify` and its
  structural facts.
- `SecTypes.v` contains the lattice-valued correctness/completeness layer for
  that simplifier.

The main proof entry points and core interfaces are:

- [`src/SIF/SecNLusStcTranslation.v`](src/SIF/SecNLusStcTranslation.v)
  Translation-preservation results from generated NLustre security signatures
  to translated STC signatures. Main public bridge theorem:
  [`generated_program_signatures_preserved_global`](src/SIF/SecNLusStcTranslation.v#L2797).
- [`src/SIF/SecNLusNonInterference.v`](src/SIF/SecNLusNonInterference.v)
  The NLustre indexed-semantics noninterference development. Main theorem:
  [`node_noninterference_outputs`](src/SIF/SecNLusNonInterference.v#L174).
- [`src/SIF/SecStcNonInterference.v`](src/SIF/SecStcNonInterference.v)
  The STC-facing translated-behavior noninterference result. Main theorem:
  [`translated_system_noninterference_outputs`](src/SIF/SecStcNonInterference.v#L241).
- [`src/SIF/NameInterface.v`](src/SIF/NameInterface.v)
  Shared naming discipline for generated security identifiers. Main entry
  points: [`generate_node_scoped_env`](src/SIF/NameInterface.v#L296),
  [`generate_node_env`](src/SIF/NameInterface.v#L669), and
  [`generate_node_env_props'`](src/SIF/NameInterface.v#L1148).
- [`src/SIF/SIFSignature.v`](src/SIF/SIFSignature.v)
  Security signatures and call instantiation. Main entry points:
  [`generate_constraints`](src/SIF/SIFSignature.v#L90),
  [`signature_scope`](src/SIF/SIFSignature.v#L141),
  [`generate_constraints_correct_inst`](src/SIF/SIFSignature.v#L2454), and
  [`generate_constraints_complete_good`](src/SIF/SIFSignature.v#L2791).

### Major Results Table

| File | Docs | Major results | Role |
| --- | --- | --- | --- |
| [`src/SIF/SecNLusStcTranslation.v`](src/SIF/SecNLusStcTranslation.v) | [`SecNLusStcTranslation.md`](src/SIF/docs/SecNLusStcTranslation.md), [`call_metatheory.md`](src/SIF/docs/call_metatheory.md) | [`eqn_preserv`](src/SIF/SecNLusStcTranslation.v#L752), [`generate_all_signatures_consistent_scoped'`](src/SIF/SecNLusStcTranslation.v#L2515), [`generated_program_signatures_preserved_global`](src/SIF/SecNLusStcTranslation.v#L2797) | Equation-level preservation, global source/target signature consistency, and the public lookup bridge used by the STC theorem. |
| [`src/SIF/SecNLusNonInterference.v`](src/SIF/SecNLusNonInterference.v) | [`Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md) | [`node_noninterference_outputs_raw`](src/SIF/SecNLusNonInterference.v#L83), [`node_noninterference_outputs`](src/SIF/SecNLusNonInterference.v#L174) | Raw-output form of the source theorem and the final NLustre noninterference statement on observable outputs. |
| [`src/SIF/SecStcNonInterference.v`](src/SIF/SecStcNonInterference.v) | [`STC-noninterference-proof.md`](src/SIF/docs/STC-noninterference-proof.md) | [`translated_system_noninterference_outputs`](src/SIF/SecStcNonInterference.v#L241) | Final STC-facing noninterference theorem for translated behaviors. |

### Comprehensive `src/SIF/` File Guide

#### Foundations and utilities

| File | Docs | Highlight definitions / theorems | Role |
| --- | --- | --- | --- |
| [`src/SIF/Helpers.v`](src/SIF/Helpers.v) | - | [`sortedNoDup_NoDup`](src/SIF/Helpers.v#L62), [`sortedNoDup_correct`](src/SIF/Helpers.v#L91) | Basic sortedness and no-duplication lemmas on positive identifiers used by the symbolic-type layers. |
| [`src/SIF/SecLattice.v`](src/SIF/SecLattice.v) | - | [`join_assoc_eq`](src/SIF/SecLattice.v#L136) | Abstract lattice equations and order lemmas used throughout the security metatheory. |
| [`src/SIF/SecContext.v`](src/SIF/SecContext.v) | [`SecContext.md`](src/SIF/docs/SecContext.md) | [`Sec`](src/SIF/SecContext.v#L20), [`find_env`](src/SIF/SecContext.v#L83), [`fresh_insert`](src/SIF/SecContext.v#L128) | Security monad, state threading, environment lookup, and fresh-name insertion for the generators. |
| [`src/SIF/SecCETyping.v`](src/SIF/SecCETyping.v) | - | [`assign_clk_correct`](src/SIF/SecCETyping.v#L45), [`assign_clk_correct2`](src/SIF/SecCETyping.v#L68) | Symbolic typing interface for clocks and CoreExpr fragments. |
| [`src/SIF/NameInterface.v`](src/SIF/NameInterface.v) | [`NameInterface.md`](src/SIF/docs/NameInterface.md) | [`generate_node_scoped_env`](src/SIF/NameInterface.v#L296), [`generate_node_scoped_env'_split_node`](src/SIF/NameInterface.v#L361), [`generate_node_env`](src/SIF/NameInterface.v#L669), [`generate_node_env_props'`](src/SIF/NameInterface.v#L1148), [`generate_node_env_injective`](src/SIF/NameInterface.v#L1176) | Shared naming discipline, node-indexed local environments, auxiliary clock/reset names, and the freshness/range/injectivity facts used by the source and target generators. |
| [`src/SIF/SIFSignature.v`](src/SIF/SIFSignature.v) | [`SIFSignature.md`](src/SIF/docs/SIFSignature.md), [`call_metatheory.md`](src/SIF/docs/call_metatheory.md) | [`generate_constraints`](src/SIF/SIFSignature.v#L90), [`signature_scope`](src/SIF/SIFSignature.v#L141), [`signature_fields_agree`](src/SIF/SIFSignature.v#L189), [`generate_constraints_shape`](src/SIF/SIFSignature.v#L613), [`generate_constraints_scoped`](src/SIF/SIFSignature.v#L857), [`generate_constraints_correct_inst`](src/SIF/SIFSignature.v#L2454), [`generate_constraints_complete_good`](src/SIF/SIFSignature.v#L2791) | Call-time instantiation of stored signatures and the core shape/scopedness/correctness/completeness facts reused by typing, translation, and noninterference. |
| [`src/SIF/SymTypes.v`](src/SIF/SymTypes.v) | - | [`ST`](src/SIF/SymTypes.v#L11), [`constraint`](src/SIF/SymTypes.v#L12), [`wf_constraints`](src/SIF/SymTypes.v#L411), [`simplify_scoped`](src/SIF/SymTypes.v#L764) | Canonical symbolic types, scopedness/well-formedness facts, and the shared structural simplifier used by both source and target signatures. |
| [`src/SIF/SecTypes.v`](src/SIF/SecTypes.v) | [`SecTypes.md`](src/SIF/docs/SecTypes.md) | [`agree_on`](src/SIF/SecTypes.v#L847), [`preserves_on`](src/SIF/SecTypes.v#L869), [`simplify_complete`](src/SIF/SecTypes.v#L812) | Lattice-valued agreement, preservation, and completeness results for the symbolic constraints and simplifier exported through `SymTypes.v`. |

#### Typing, signature generation, and export

| File | Docs | Highlight definitions / theorems | Role |
| --- | --- | --- | --- |
| [`src/SIF/SecNLusTyping.v`](src/SIF/SecNLusTyping.v) | [`SecNLusTyping.md`](src/SIF/docs/SecNLusTyping.md) | [`generate_eqn_constraint`](src/SIF/SecNLusTyping.v#L55), [`generate_eqns_constraints_scoped`](src/SIF/SecNLusTyping.v#L575), [`generate_node_sig_scoped`](src/SIF/SecNLusTyping.v#L932), [`generate_all_signatures_scoped`](src/SIF/SecNLusTyping.v#L1113) | Symbolic security typing for NLustre equations and generation of scoped source signatures. |
| [`src/SIF/SecNLusTypingCorrectness.v`](src/SIF/SecNLusTypingCorrectness.v) | [`SecNLusTypingCorrectness.md`](src/SIF/docs/SecNLusTypingCorrectness.md) | [`generated_callers_scope_fresh`](src/SIF/SecNLusTypingCorrectness.v#L116), [`generate_node_sig_scoped_env_scoped`](src/SIF/SecNLusTypingCorrectness.v#L1301), [`generate_all_source_signatures_good_scoped_env'`](src/SIF/SecNLusTypingCorrectness.v#L1471), [`generated_signature_constraints_mention_reset_scoped_env`](src/SIF/SecNLusTypingCorrectness.v#L2579), [`generated_signature_constraints_mention_clock_scoped_env`](src/SIF/SecNLusTypingCorrectness.v#L3092) | Correctness properties of generated source signatures, especially structural goodness and visible reset/clock mentions used later by call and noninterference proofs. |
| [`src/SIF/SecSTCTyping.v`](src/SIF/SecSTCTyping.v) | [`SecSTCTyping.md`](src/SIF/docs/SecSTCTyping.md) | [`hidden_sys_vars`](src/SIF/SecSTCTyping.v#L53), [`generate_reset_env`](src/SIF/SecSTCTyping.v#L108), [`generate_trconstrs_constraints_scoped`](src/SIF/SecSTCTyping.v#L1001), [`generate_sys_signature_scoped`](src/SIF/SecSTCTyping.v#L1380), [`generate_all_sys_signatures_scoped`](src/SIF/SecSTCTyping.v#L1581) | Target-side symbolic typing for translated STC systems, including reset-instance handling and scoped target signature generation. |
| [`src/SIF/SecStcTypingCorrectness.v`](src/SIF/SecStcTypingCorrectness.v) | [`SecStcTypingCorrectness.md`](src/SIF/docs/SecStcTypingCorrectness.md) | [`generate_sys_signature_scoped_env_scoped`](src/SIF/SecStcTypingCorrectness.v#L206), [`generated_sys_signature_scope_sec`](src/SIF/SecStcTypingCorrectness.v#L464), [`generate_reset_env_injective`](src/SIF/SecStcTypingCorrectness.v#L561) | Correctness and namespace properties for generated STC signatures and reset-instance environments. |
| [`src/SIF/SecNLusConstraintExport.v`](src/SIF/SecNLusConstraintExport.v) | - | [`sif_constraint_dump`](src/SIF/SecNLusConstraintExport.v#L50), [`build_node_constraint_dump`](src/SIF/SecNLusConstraintExport.v#L58), [`generate_nlustre_constraint_dump`](src/SIF/SecNLusConstraintExport.v#L126) | Executable extraction path for dumping generated NLustre SIF constraints. |
| [`src/SIF/SecStcConstraintExport.v`](src/SIF/SecStcConstraintExport.v) | - | [`stc_constraint_dump`](src/SIF/SecStcConstraintExport.v#L54), [`build_system_constraint_dump`](src/SIF/SecStcConstraintExport.v#L87), [`generate_stc_constraint_dump`](src/SIF/SecStcConstraintExport.v#L175) | Executable extraction path for dumping generated STC SIF constraints. |

#### Translation and noninterference

| File | Docs | Highlight definitions / theorems | Role |
| --- | --- | --- | --- |
| [`src/SIF/NLustreCausality.v`](src/SIF/NLustreCausality.v) | - | [`nl_global_causal`](src/SIF/NLustreCausality.v#L51), [`nl_node_causal_ind`](src/SIF/NLustreCausality.v#L135) | Causality notions and induction principles for NLustre nodes. |
| [`src/SIF/SecNLusStcTranslation.v`](src/SIF/SecNLusStcTranslation.v) | [`SecNLusStcTranslation.md`](src/SIF/docs/SecNLusStcTranslation.md), [`call_metatheory.md`](src/SIF/docs/call_metatheory.md) | [`Signature_consistent`](src/SIF/SecNLusStcTranslation.v#L113), [`eqn_preserv`](src/SIF/SecNLusStcTranslation.v#L752), [`generate_all_signatures_consistent_scoped'`](src/SIF/SecNLusStcTranslation.v#L2515), [`generated_program_signatures_preserved_global`](src/SIF/SecNLusStcTranslation.v#L2797) | Main source-to-target signature-preservation layer, from one equation up to global source/target signature lookup compatibility. |
| [`src/SIF/SecNLusNonInterferenceSupport.v`](src/SIF/SecNLusNonInterferenceSupport.v) | [`Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md) | [`ground_instantiation`](src/SIF/SecNLusNonInterferenceSupport.v#L69), [`low_var`](src/SIF/SecNLusNonInterferenceSupport.v#L93), [`history_low_eq`](src/SIF/SecNLusNonInterferenceSupport.v#L202), [`history_low_eq_projected_history_eq`](src/SIF/SecNLusNonInterferenceSupport.v#L278) | Definitions of low observation and the semantic transport lemmas on histories used by the source theorem. |
| [`src/SIF/SecNLusNonInterferenceHelpers.v`](src/SIF/SecNLusNonInterferenceHelpers.v) | [`Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md) | [`reset_control_low_eq_upto`](src/SIF/SecNLusNonInterferenceHelpers.v#L81), [`signature_satisfied_replays_raw`](src/SIF/SecNLusNonInterferenceHelpers.v#L174), [`node_noninterference_vars_defined_step_base_mainline`](src/SIF/SecNLusNonInterferenceHelpers.v#L3046) | Intermediate replay and transport lemmas that connect signature satisfiability to equation-by-equation noninterference reasoning. |
| [`src/SIF/SecNLusNonInterferenceClockedStep.v`](src/SIF/SecNLusNonInterferenceClockedStep.v#L83) | [`Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md) | [`node_noninterference_vars_defined_step_mainline`](src/SIF/SecNLusNonInterferenceClockedStep.v#L83) | Main clocked step theorem used in the source noninterference induction. |
| [`src/SIF/SecNLusNonInterference.v`](src/SIF/SecNLusNonInterference.v) | [`Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md) | [`node_noninterference_outputs_raw`](src/SIF/SecNLusNonInterference.v#L83), [`node_noninterference_outputs`](src/SIF/SecNLusNonInterference.v#L174) | Final NLustre indexed noninterference result on observable outputs. |
| [`src/SIF/SecStcNonInterference.v`](src/SIF/SecStcNonInterference.v) | [`STC-noninterference-proof.md`](src/SIF/docs/STC-noninterference-proof.md) | [`translated_system_behavior`](src/SIF/SecStcNonInterference.v#L97), [`system_security`](src/SIF/SecStcNonInterference.v#L105), [`translated_system_noninterference_outputs`](src/SIF/SecStcNonInterference.v#L241) | Target-side translated-behavior formulation and the final STC-facing noninterference theorem. |

Related executable constraint-export code is also in `src/SIF/`, especially:

- [`src/SIF/SecNLusConstraintExport.v`](src/SIF/SecNLusConstraintExport.v#L126)
  `generate_nlustre_constraint_dump`
- [`src/SIF/SecStcConstraintExport.v`](src/SIF/SecStcConstraintExport.v#L175)
  `generate_stc_constraint_dump`
- [`src/SIF/siflib.ml`](src/SIF/siflib.ml)

## Building

Velus has been implemented in Coq 8.9.1. The original artifact also depends on
Menhir and the bundled CompCert tree.

To check the proofs and build the compiler:

```sh
./configure [options] target
make
```

The configuration script follows the same general structure as CompCert's,
with an additional `-compcertdir` option to specify the CompCert directory.

The original upstream README used the following local `opam` workflow:

```sh
cd $VELUS_DIR
mkdir opam
opam init --root=opam --compiler=4.07.1
eval `opam config env --root=$VELUS_DIR/opam`
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -j4 coq.8.9.1 menhir.20200624 coq-menhirlib.20200624
```

## Using the Compiler

To see the compiler options:

```sh
./velus -h
```

A standard compilation run looks like:

```sh
./velus examples/count.lus
```

which produces `examples/count.s`.

The `pre` operator is not treated directly. An uninitialized delay `pre e`
must be replaced by an initialized one such as `0 fby e`.

## Generating SIF Constraints

The constraint-dump path for the SIF development is exposed through the `-dsif`
option in [`src/velusmain.ml`](src/velusmain.ml#L167). The driver enters the
dump path at [`dump_sif_if`](src/velusmain.ml#L86), then calls
[`SecNLusConstraintExport.generate_nlustre_constraint_dump`](src/SIF/SecNLusConstraintExport.v#L126)
and
[`SecStcConstraintExport.generate_stc_constraint_dump`](src/SIF/SecStcConstraintExport.v#L175).

Run:

```sh
./velus -dsif <file>.lus
```

For example:

```sh
./velus -dsif examples/count.lus
```

This generates:

- `<file>.n.sif`
  The generated NLustre security-signature/constraint dump.
- `<file>.s.sif`
  The generated STC security-signature/constraint dump.

These dumps are produced by the SIF export path in:

- [`SecNLusConstraintExport.generate_nlustre_constraint_dump`](src/SIF/SecNLusConstraintExport.v#L126)
- [`SecStcConstraintExport.generate_stc_constraint_dump`](src/SIF/SecStcConstraintExport.v#L175)

Useful companion options from the Velus driver are:

- `-dnlustre` to dump normalized NLustre
- `-dstc` to dump the STC intermediate form
- `-dsch` to dump scheduled STC
- `-dobc` to dump OBC
- `-dclight` to dump generated Clight

## Copyright and License

The Velus compiler and the original artifact files remain the work of the
Velus team, and their copyright and license notices should remain intact.

In this repository, we only claim original contributions under `src/SIF/`
unless a file explicitly states otherwise.

The top-level [`LICENSE`](LICENSE) file should therefore be read as preserving
the upstream Velus licensing, not as replacing the Velus team's ownership of
their code.
