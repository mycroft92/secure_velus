From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import NLustre.
From Velus Require Import CoindToIndexed.
From Velus Require Import Environment.
(* Imports from VELUS*)


From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
(* Fixpoint and wt_exp definitions*)
Module Type SEC_NLUSTRE_TYPING 
    (Import Ids   : IDS)
    (Import Op    : OPERATORS)
    (Import OpAux : OPERATORS_AUX   Op)
    (Import CStr  : COINDSTREAMS    Op OpAux)
    (Import IStr  : INDEXEDSTREAMS  Op OpAux)
    (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
    (Import CE    : COREEXPR    Ids Op OpAux      IStr)
    (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
    (Import Lat   : Lattice).
    Check env.
    
    Variable G: global.
    (*G has all the nodes, the analysis is recursive on G*)
    (* Context maps idents to idents*)
    Local Definition Ctxt := Env.t ident. 
    (* Inductive wst_exp: ctxt *)


End SEC_NLUSTRE_TYPING.
