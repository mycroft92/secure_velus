# SecTypes

## Role

`SecTypes.v` is the lattice-valued layer that sits on top of `SymTypes.v`.
It interprets symbolic constraints under a valuation `dlt : ident -> Lat.t`
and proves the agreement and preservation theorems used by replay,
translation, and noninterference.

## Split With `SymTypes.v`

The symbolic and semantic responsibilities are now separate.

- `SymTypes.v`
  owns `ST`, `constraint`, `wf_constraints`, scopedness predicates,
  substitution, and `simplify`
- `SecTypes.v`
  owns valuation agreement, replay updates, satisfiability transport, and
  preservation/completeness results about those symbolic operations

For convenience, `SecTypes.v` re-exports the symbolic interface, but the
definitions themselves live in `SymTypes.v`.

## Main Semantic Interfaces

- `agree_on`
  two valuations may differ globally but coincide on the visible scope
- `preserves_on`
  any source valuation satisfying one constraint list can be turned into a
  target valuation satisfying another list while preserving the visible scope
- `overlay_scope`
  builds a valuation that uses one valuation on a chosen scope and falls back
  to another outside it

These are the core notions used later by call replay and by the
source-to-target translation theorem.

## Replay Update Combinators

- `upd_type`, `upd_ident`
  one-step valuation updates
- `upd_types`, `upd_idents`
  forward folds of those updates
- `upd_types_rev`, `upd_idents_rev`
  reverse folds matching the order used by call replay

The corresponding lemmas show that these updates preserve agreement on scopes
that are disjoint from the updated identifiers.

## Main Lemma Families

- `agree_on_refl`, `agree_on_trans`
  basic agreement algebra
- `hm_ext_agree_on_st`, `hm_ext_agree_on_scoped_type`
  evaluation of a symbolic type only depends on the identifiers it mentions
- `constraintSatisfiable_ext`, `listSatisfiable_ext`
  satisfiability transports across agreeing valuations
- `preserves_on_nil`, `preserves_on_weaken`
  basic preservation constructors
- `preserves_on_concat_scoped`
  composition theorem used when translated STC blocks add private extras
- `upd_types_agree_on`, `upd_types_rev_agree_on`
  scope preservation for symbolic-type replay updates
- `upd_idents_agree_on`, `upd_idents_rev_agree_on`
  scope preservation for identifier replay updates
- `upd_types_rev_outside`, `upd_idents_rev_outside`
  updates are literally the identity off the replay scope

## Simplification Semantics

`SymTypes.simplify` is structural; `SecTypes.v` proves that it is semantically
sound.

The key lemmas are:

- `subAll_is_correct`
  one substitution step preserves satisfiability
- `subAll_complete` and `subAll_complete_none`
  the converse direction for one step
- `simplify_simplifyRel`
  packages the simplifier as the reflexive relation used by later proofs
- `simplify_is_correct`
  a simplified signature is semantically at least as strong as the raw one
- `simplify_complete`
  the simplified signature is also complete for the visible scope

Because `SymTypes.subAll` now removes a target from its own singleton left-hand
side, the semantic proofs include the bridge lemmas
`satisfiable_remove_self_lhs` and `satisfiable_restore_self_lhs`.

## Why `preserves_on_concat_scoped` Matters

`preserves_on_concat_scoped` is the composition theorem used in
`SecNLusStcTranslation.v`.  It lets two translated STC blocks be concatenated
while preserving the same shared source-visible scope, provided each block's
private extras stay outside that shared scope and outside each other.

This is exactly the pattern needed for STC reset-instance variables.

## Downstream Use

- `SIFSignature.v`
  uses the replay updates when reconstructing callee valuations
- `SecNLusStcTranslation.v`
  defines source-to-target preservation in terms of `preserves_on`
- the noninterference stack uses `agree_on` and satisfiability transport when
  moving between stored simplified signatures and raw generated constraints
