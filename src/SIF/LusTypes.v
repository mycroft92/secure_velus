(** The Lustre security type framework, assembled.

    [SymLusTypes.v] is the syntactic half: the refinement term algebra of
    ICTAC 2021 Figure 5, its equational theory, and the canonical form that
    decides it.  [SecLusTypes.v] is the semantic half: interpretation in a
    security lattice, satisfaction, and the bridge to [SecTypes.v].

    This file puts the two behind one name, the way [Lustre.v] assembles
    [LSyntax], [LTyping] and [LClocking].  Clients of the Lustre security
    type system should import this rather than either half.

    Keeping the two halves out of [SymTypes.v] and [SecTypes.v] is deliberate:
    those modules are large and every NLustre, Stc and Obc proof rests on
    them.  A property of [ST] or [constraint] at the NLustre or Stc level
    belongs there; a property about the Lustre level, or about the
    Lustre-to-NLustre bridge on types, belongs in one of the two halves
    assembled here. *)

From Velus Require Import Common.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.

From Velus Require Export SIF.SymLusTypes.
From Velus Require Import SIF.SecLusTypes.

Module Type LUSTYPES (Lat : Lattice) (SecT : SECTYPES Lat).
  Declare Module Export SecLus : SECLUSTYPES Lat SecT.
End LUSTYPES.

Module LusTypesFun (Lat : Lattice) (SecT : SECTYPES Lat)
  <: LUSTYPES Lat SecT.
  Module Export SecLus := SecLusTypesFun Lat SecT.
End LusTypesFun.
