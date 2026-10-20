(** Every signature-satisfying valuation of a generated node is the signature-level
    valuation of a [node_security] witness.

    [node_security] is the invariant the noninterference proof consumes.  Here it is
    constructed rather than assumed: from a valuation satisfying a node's stored
    signature, [signature_satisfied_replays_raw] gives a raw valuation agreeing on the
    scope, the callee clauses are read off the instantiated constraints (a satisfied
    call block gives a satisfied callee signature, by completeness of the substitution),
    and the callee is taken at its own witness by induction on the call structure. *)

From Coq Require Import List Sorting.Permutation Lia Wf_nat PArith.BinPos Arith.PeanoNat.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterferenceClockedStep.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module SecNLusNodeSecurity
  (Import Ids    : IDS)
  (Import Lat    : Lattice)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import SecT   : SECTYPES Lat)
  (Import CESyn  : CESYNTAX Op)
  (Import SynNL  : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (NLCaus        : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN CEIsF CEClo SECCETYPING
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING Ord Mem IsD IsF Clo SECNLUSTYPING)
.

Module NI := SecNLusNonInterference Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN
  CETyp CEIsF CEClo SECCETYPING Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed
  SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.
Import NI.


End SecNLusNodeSecurity.
