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

The main proof entry points are:

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

### Major Results Table

| File | Major results | Role |
| --- | --- | --- |
| [`src/SIF/SecNLusStcTranslation.v`](src/SIF/SecNLusStcTranslation.v) | [`eqn_preserv`](src/SIF/SecNLusStcTranslation.v#L752), [`generate_all_signatures_consistent_scoped'`](src/SIF/SecNLusStcTranslation.v#L2515), [`generated_program_signatures_preserved_global`](src/SIF/SecNLusStcTranslation.v#L2797) | Equation-level preservation, global source/target signature consistency, and the public lookup bridge used by the STC theorem. |
| [`src/SIF/SecNLusNonInterference.v`](src/SIF/SecNLusNonInterference.v) | [`node_noninterference_outputs_raw`](src/SIF/SecNLusNonInterference.v#L83), [`node_noninterference_outputs`](src/SIF/SecNLusNonInterference.v#L174) | Raw-output form of the source theorem and the final NLustre noninterference statement on observable outputs. |
| [`src/SIF/SecStcNonInterference.v`](src/SIF/SecStcNonInterference.v) | [`translated_system_noninterference_outputs`](src/SIF/SecStcNonInterference.v#L241) | Final STC-facing noninterference theorem for translated behaviors. |

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
