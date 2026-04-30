# SecTypes

## Role

`SecTypes.v` is the generic lattice-mapping layer for symbolic security types
and constraint satisfaction once a mapping `dlt : ident -> Lat.t` is fixed.

It is intentionally phase-agnostic.  Both the signature layer and the
translation-preservation proof build on top of it.

## Main Definitions

- `wf_constraints`
- `constraint_scoped`, `constraints_scoped`, `st_scoped`
- `agree_on`
- `preserves_on`
- `overlay_scope`
- `upd_type`, `upd_ident`, `upd_types`, `upd_idents`
- reverse-order update variants used by call-instantiation replay:
  `upd_types_rev`, `upd_idents_rev`

## Key Theorem Families

- agreement and scopedness:
  - `agree_on_trans`
  - `agree_on_refl`
  - `hm_ext_agree_on_st`
  - `hm_ext_agree_on_scoped_type`
  - `overlay_scope_agree_on`
- preservation combinators:
  - `constraintSatisfiable_ext`
  - `listSatisfiable_ext`
  - `preserves_on_concat_scoped`
  - `preserves_on_nil`
  - `preserves_on_weaken`
- update-side agreement lemmas:
  - `upd_types_agree_on`
  - `upd_types_rev_agree_on`
  - `upd_idents_agree_on`
  - `upd_idents_rev_agree_on`
  - `upd_type_agree_on`
  - `upd_ident_agree_on`
  - `upd_types_rev_outside`
  - `upd_idents_rev_outside`

## Relation To The Final Theorem

`SecNLusStcTranslation.v` defines the cross-phase notion
`signatures_preserved` by instantiating `preserves_on` on source and target
signature constraints.

The final theorem path then uses:

1. `preserves_on_concat_scoped` to compose translated equation blocks,
2. the update/agreement lemmas to replay call instantiations,
3. `listSatisfiable_ext` to transport satisfaction across lattice mappings that
   agree on the relevant scope.

So this file is the generic lattice-mapping substrate beneath the final
signature-preservation theorem.
