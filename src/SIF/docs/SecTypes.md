# SecTypes

## Role

`SecTypes.v` is the generic lattice-mapping layer for symbolic security types.
It does not depend on NLustre or STC syntax.  Its job is to define what it
means for two valuations to agree on a scope and what it means for one
constraint list to preserve satisfiability to another.

## Core Definitions

- `wf_constraints`
- `constraint_scoped`, `constraints_scoped`, `st_scoped`
- `agree_on`
- `preserves_on`
- `overlay_scope`
- `upd_type`, `upd_ident`, `upd_types`, `upd_idents`
- `upd_types_rev`, `upd_idents_rev`

`agree_on` is the basic interface notion: two valuations may differ globally
but must coincide on the variables currently visible to a proof.  All later
preservation theorems are stated in those terms.

## Main Lemma Groups

- Agreement transport:
  `agree_on_refl`,
  `agree_on_trans`,
  `hm_ext_agree_on_st`,
  `hm_ext_agree_on_scoped_type`,
  `overlay_scope_agree_on`.
- Preservation combinators:
  `constraintSatisfiable_ext`,
  `listSatisfiable_ext`,
  `preserves_on_nil`,
  `preserves_on_weaken`,
  `preserves_on_concat_scoped`.
- Update lemmas:
  `upd_types_agree_on`,
  `upd_types_rev_agree_on`,
  `upd_idents_agree_on`,
  `upd_idents_rev_agree_on`,
  `upd_types_rev_outside`,
  `upd_idents_rev_outside`.

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
