# SecTypes

## Role

`SecTypes.v` is the generic lattice-mapping layer for symbolic security types.
It does not depend on NLustre or STC syntax.  Its job is to define what it
means for two valuations to agree on a scope and what it means for one
constraint list to preserve satisfiability to another.

## Core Definitions

- `wf_constraints`
  says a constraint list is well-formed: each right-hand side is a singleton,
  and no target variable is defined twice.
- `constraint_scoped`, `constraints_scoped`, `st_scoped`
  state that every identifier mentioned by one constraint, a list of
  constraints, or one symbolic type stays inside a declared scope.
- `agree_on`
  says two valuations may differ globally but give the same answers on the
  variables in the current proof scope.
- `preserves_on`
  is the main refinement relation: any satisfying source valuation can be
  turned into a target valuation that still agrees on the visible scope.
- `overlay_scope`
  builds a valuation that uses one valuation on a chosen scope and falls back
  to another valuation everywhere else.
- `upd_type`, `upd_ident`, `upd_types`, `upd_idents`
  perform forward substitutions on one valuation by replacing variables with
  symbolic types or with other identifiers.
- `upd_types_rev`, `upd_idents_rev`
  perform the same substitutions in reverse-fold order, which matches the way
  call replay rebuilds a callee valuation.

`agree_on` is the basic interface notion: two valuations may differ globally
but must coincide on the variables currently visible to a proof.  All later
preservation theorems are stated in those terms.

## Main Lemma Groups

- `agree_on_refl`
  is the trivial self-agreement fact for one valuation.
- `agree_on_trans`
  chains two agreement facts through an intermediate valuation.
- `hm_ext_agree_on_st`
  says `hm_ext` computes the same lattice join when two valuations agree on
  every identifier inside the queried symbolic type.
- `hm_ext_agree_on_scoped_type`
  is the scoped version used when the type is known to stay inside a larger
  visible scope.
- `overlay_scope_agree_on`
  shows that overlaying another valuation does not change behavior on the
  protected scope itself.
- `constraintSatisfiable_ext`
  transports satisfiability of one scoped constraint across agreeing
  valuations.
- `listSatisfiable_ext`
  lifts that same transport argument to an entire scoped constraint list.
- `preserves_on_nil`
  says the empty constraint list preserves to itself without changing the
  valuation.
- `preserves_on_weaken`
  lets a preservation theorem be reused on a smaller visible scope.
- `preserves_on_concat_scoped`
  composes two preservation results while keeping each block's private extras
  outside the shared scope.
- `upd_types_agree_on`
  says substituting fresh type actuals leaves the valuation unchanged on any
  unrelated scope.
- `upd_types_rev_agree_on`
  gives the same scope-preservation fact for the reverse-fold substitution used
  by replay.
- `upd_idents_agree_on`
  says fresh identifier substitutions do not change values on a disjoint scope.
- `upd_idents_rev_agree_on`
  is the reverse-fold version for identifier substitutions.
- `upd_types_rev_outside`
  says reverse type substitution is literally the identity outside the updated
  identifiers.
- `upd_idents_rev_outside`
  gives the same outside-scope identity fact for identifier substitutions.

## Why `preserves_on_concat_scoped` Matters

`preserves_on_concat_scoped` is the key composition lemma used by the
translation proof.  It allows two translated target blocks to be concatenated
while preserving the same shared source scope, provided each block's private
extras are:

- scoped to `scope ++ extras`,
- outside the shared `scope`,
- and disjoint from the extras of the other block.

This is exactly the shape needed when the STC translation introduces reset
instance variables that are local to one translated equation.

## Downstream Use

- `SIFSignature.v` uses the update lemmas to replay call instantiations.
- `SecNLusStcTranslation.v` defines signature preservation in terms of
  `preserves_on` and composes translated equation blocks with
  `preserves_on_concat_scoped`.
- The noninterference files use `agree_on` and satisfiability transport when
  moving between simplified signatures and raw generated constraints.
