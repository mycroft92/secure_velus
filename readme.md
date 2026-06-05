# Secure Velus

This repository extends the Velus EMSOFT'21 artifact with a security
information-flow (SIF) development under `src/SIF/`.  The upstream Velus
compiler, proofs, and build system are still present; the SIF-specific work is
concentrated in that directory.

## Start Here

- [`src/SIF/docs/proof_outline.md`](src/SIF/docs/proof_outline.md)
  current module map for the SIF development
- [`src/SIF/docs/SymTypes.md`](src/SIF/docs/SymTypes.md)
  symbolic constraint representation and simplification
- [`src/SIF/docs/SecTypes.md`](src/SIF/docs/SecTypes.md)
  lattice-valued preservation and replay layer
- [`src/SIF/docs/call_metatheory.md`](src/SIF/docs/call_metatheory.md)
  call-instantiation preservation across source and target
- [`src/SIF/docs/Non-interference-proof.md`](src/SIF/docs/Non-interference-proof.md)
  source NLustre noninterference stack
- [`src/SIF/docs/STC-noninterference-proof.md`](src/SIF/docs/STC-noninterference-proof.md)
  target STC noninterference theorem

The upstream Velus documentation is still useful:

- `doc/index.html`
  links the EMSOFT 2021 paper to the corresponding Coq definitions
- `examples/readme.md`
  describes the Lustre examples shipped with Velus

## SIF Layout

The SIF development is organized in layers.

### Foundations

- `Helpers.v`
  list and positivity lemmas used by the symbolic layer
- `SecLattice.v`
  abstract lattice laws and order lemmas
- `SymTypes.v`
  the single symbolic-constraint layer: symbolic types, scopedness,
  substitution, and `simplify`
- `SecTypes.v`
  the lattice-valued layer: valuation agreement, replay updates, and
  satisfiability preservation over `SymTypes`
- `SecContext.v`
  state-and-error monad plus lookup lemmas used by the generators
- `NameInterface.v`
  generated security names, node-local environments, and freshness facts

### Signature Generation

- `SIFSignature.v`
  stored signature format and call instantiation
- `SecNLusTyping.v`
  NLustre-side constraint generation
- `SecSTCTyping.v`
  STC-side constraint generation
- `SecNLusTypingCorrectness.v`
  source-side structure, freshness, and visibility facts
- `SecStcTypingCorrectness.v`
  target-side reset-environment and signature structure facts

### Cross-Phase Results

- `SecNLusStcTranslation.v`
  source-to-target signature preservation
- `SecNLusNonInterference*.v`
  source noninterference stack
- `SecStcNonInterference.v`
  target noninterference theorem

### Constraint Export

- `SecNLusConstraintExport.v`
  dumps generated NLustre signatures and constraints
- `SecStcConstraintExport.v`
  dumps generated STC signatures and constraints

## Current Symbolic Split

The symbolic split is intentional.

- `SymTypes.v` owns the symbolic representation:
  `ST`, `constraint`, `wf_constraints`, `constraint_scope`,
  `constraint_scoped`, `constraints_scoped`, `st_scoped`, substitution, and
  `simplify`
- `SecTypes.v` owns everything that depends on lattice valuations:
  `agree_on`, `preserves_on`, `overlay_scope`, replay updates, and the
  preservation/completeness proofs for simplification

`SecTypes.v` still re-exports the symbolic interface for convenience, but
`SymTypes.v` is the source of truth for the symbolic metatheory.

Both source and target signature generators use the same
`SymTypes.simplify`.  The simplifier now normalizes singleton-right-hand-side
constraints by removing the target from its own left-hand side.  For example,

```text
[sec$3, sec$4, sec$5, sec$6, sec$9] <= [sec$9]
```

is stored and dumped as

```text
[sec$3, sec$4, sec$5, sec$6] <= [sec$9]
```

This keeps exported signatures canonical and removes trivial self-dependencies.

## Build Notes

Velus itself is still built in the usual way:

```sh
./configure [options] target
make
```

For SIF development, the practical workflow is:

- local iteration:
  run `coqc` directly on the file you are editing, using the flags from
  `_CoqProject`
- dependency rebuild:
  clear stale `*.vo` files under `src/SIF/` and then run `make`

The full `make` rebuild is much slower, so it is mainly useful when a local
`coqc` run fails because of stale dependency artifacts or inconsistent
assumptions.

The current `_CoqProject` already declares the logical roots for `Velus` and
the bundled `compcert.*` libraries.

## Generating SIF Constraint Dumps

The SIF export path is exposed through the Velus driver:

```sh
./velus -dsif <file>.lus
```

For example:

```sh
./velus -dsif examples/count.lus
```

This produces:

- `<file>.n.sif`
  generated NLustre signature and constraint dump
- `<file>.s.sif`
  generated STC signature and constraint dump

Useful companion flags from the Velus driver are:

- `-dnlustre`
- `-dstc`
- `-dsch`
- `-dobc`
- `-dclight`

## License

The upstream Velus code remains under the original Velus licensing terms.
This repository only claims original SIF contributions under `src/SIF/`
unless a file states otherwise.
