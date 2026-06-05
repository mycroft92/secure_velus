# SymTypes

## Role

`SymTypes.v` is the single symbolic-constraint layer shared by the whole SIF
development.  It does not talk about lattice valuations or `dlt`.  Its job is
to define the canonical symbolic representation and the structural facts that
both source and target proofs reuse.

## Core Objects

- `ST`
  symbolic security types, represented as lists of identifiers
- `constraint`
  symbolic constraints of the form `(lhs, rhs)`
- `merge`, `intersect`, `mergesort`
  canonical list-level operations used to keep symbolic types normalized
- `st_remove`, `st_mem`, `findST`
  basic symbolic utilities used by elimination
- `subST`
  substitutes one singleton target inside a symbolic type
- `wf_constraints`
  well-formedness of a constraint list: singleton right-hand sides and no
  duplicate targets
- `constraint_scope`, `constraint_scoped`, `constraints_scoped`, `st_scoped`
  structural scopedness predicates

This file is the symbolic source of truth.  Later files may re-export these
definitions, but they do not redefine them.

## Simplification

`simplify cns ds` eliminates local identifiers `ds` from a raw constraint list
by repeatedly:

1. finding a defining singleton target `[d]`,
2. substituting its left-hand side into the other constraints with `subAll`,
3. removing the defining constraint itself,
4. recurring on the remaining locals

The important normalization step is:

- `normalize_constraint lhs rhs := (st_remove rhs lhs, [rhs])`

So after substitution, a surviving singleton-right-hand-side constraint is
stored without its own target on the left.  This means the simplifier now
turns

```text
[sec$3, sec$4, sec$5, sec$6, sec$9] <= [sec$9]
```

into

```text
[sec$3, sec$4, sec$5, sec$6] <= [sec$9]
```

instead of keeping the trivial self-dependency.

## Main Structural Lemmas

- `st_scoped_weaken` and `constraints_scoped_weaken`
  scopedness monotonicity
- `findST_of_rhs_in`
  if `findST cns d = Some st`, then `[d]` is really a right-hand side in `cns`
- `subAll_scoped_elim`
  substitution preserves scopedness while dropping one eliminated local
- `subAll_preserves_other_rhs`
  substitution does not change unrelated right-hand sides
- `subAll_rhs_in`, `subAll_nodup`, `subAll_singleton_rhs`, `subAll_wf`
  well-formedness preservation for one elimination step
- `simplify_scoped`
  the simplified constraint list stays inside the visible scope
- `simplify_rhs_in`, `simplify_preserves_other_rhs`
  surviving right-hand sides still come from the original raw constraints
- `simplify_nodup`, `simplify_singleton_rhs`, `simplify_wf`
  global structural preservation for the full simplifier

These lemmas are intentionally symbolic.  They say what `simplify` does to the
shape of constraints before any lattice semantics is applied.

## Downstream Use

- `SecTypes.v`
  proves satisfiability preservation and completeness for the symbolic
  operations defined here
- `SecNLusTyping.v` and `SecSTCTyping.v`
  use `simplify` to build stored source and target signatures
- `SecNLusTypingCorrectness.v`
  uses the structural lemmas directly, instead of carrying a local duplicate
  proof block
- the export path dumps constraints in exactly this normalized form
