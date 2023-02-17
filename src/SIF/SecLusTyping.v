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
    
    Section Lustre_Sec_Typing.
    Inductive 

End SEC_LUSTRE_TYPING.