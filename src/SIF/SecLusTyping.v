(* This is going to be the lustre typing details*)
From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Environment.
(* Imports from VELUS*)


From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SIFSignature.
(* Fixpoint and wt_exp definitions*)
Module Type SEC_LUSTRE_TYPING
    (Import Ids   : IDS)
    (Import Op    : OPERATORS)
    (Import OpAux : OPERATORS_AUX   Op)
    (Import CStr  : COINDSTREAMS    Op OpAux)
    (Import IStr  : INDEXEDSTREAMS Op OpAux)
    (Import L     : LUSTRE  Ids Op OpAux CStr IStr)
    (Import Lat   : Lattice).
    Check env.
    (* Predicate takes Ordered list of nodes with signatures and assigns types/constraints to expressions/statemets*)
    Section Lustre_Sec_Typing.
    Variable G: global.

    End Lustre_Sec_Typing.

End SEC_LUSTRE_TYPING.