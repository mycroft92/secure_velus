From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.

(** * STC causality

    This file packages the target-side acyclicity/scheduling condition that a
    stronger intrinsic STC noninterference theorem would use.

    Unlike NLustre, STC already carries an explicit sequential discipline over
    transition constraints through [Is_well_sch].  The target semantics is
    stateful and distinguishes current-step environment bindings from memory
    updates, so reusing that existing scheduling predicate is the cleanest
    initial causality interface.

    In particular, this avoids introducing a second graph formalization before
    we know the exact final theorem shape for [TcNext], reset handlers, and the
    STC-only reset-instance auxiliaries.

    Current status note:
    the main thesis path currently targets only the weaker translated-behavior
    STC result, so this file is auxiliary rather than critical-path. *)

Module Type STCCAUSALITY
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import CESyn  : CESYNTAX Op)
       (Import Syn    : STCSYNTAX Ids Op CESyn)
       (Import Syst   : STCISSYSTEM Ids Op CESyn Syn)
       (Import Ord    : STCORDERED Ids Op CESyn Syn Syst)
       (Import Var    : STCISVARIABLE Ids Op CESyn Syn)
       (Import Last   : STCISLAST Ids Op CESyn Syn)
       (Import Def    : STCISDEFINED Ids Op CESyn Syn Var Last)
       (Import CEIsF  : CEISFREE Ids Op CESyn)
       (Import IsF    : STCISFREE Ids Op CESyn Syn CEIsF)
       (Import WellDef: STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Last Def CEIsF IsF).

  (** System-local causality / scheduling view.

      Relation to the paper:
      this is the STC-side source-structure hypothesis corresponding to the
      acyclicity assumption used on the NLustre side.  For STC, the repository
      already expresses it as a well-scheduled transition-constraint list. *)
  Definition stc_system_causal (s : system) : Prop :=
    WellDef.Is_well_sch
      (map fst s.(s_in))
      (ps_from_list (map fst s.(s_lasts)))
      s.(s_tcs).

  Definition stc_global_causal (P : program) : Prop :=
    Forall stc_system_causal P.

  (** Global well-scheduling immediately yields the causality view used by the
      later noninterference file.

      Relation to the paper:
      this is the target-side bridge from the existing STC well-definedness
      infrastructure to the dedicated causality vocabulary used by the
      security proof. *)
  Lemma well_scheduled_stc_global_causal:
    forall P,
      WellDef.Well_scheduled P ->
      stc_global_causal P.
  Proof.
    unfold WellDef.Well_scheduled, stc_global_causal, stc_system_causal.
    auto.
  Qed.

  (** Recovering system-local causality from a global assumption.

      Relation to the paper:
      recursive call proofs on the STC side will need to project the global
      scheduling assumption back to the current system and its callees. *)
  Lemma stc_global_causal_find:
    forall P s P',
      stc_global_causal P ->
      find_system s.(s_name) P = Some (s, P') ->
      stc_system_causal s.
  Proof.
    intros P s P' Hcausal Hfind.
    eapply Forall_forall; eauto.
    eapply find_system_In; eauto.
  Qed.

  (** One-step inversion of the scheduling predicate.

      Relation to the paper:
      later local STC proofs will inspect the current head transition
      constraint and reason about the already-scheduled tail. *)
  Lemma stc_system_causal_inv:
    forall inputs mems tc tcs,
      WellDef.Is_well_sch inputs mems (tc :: tcs) ->
      WellDef.Is_well_sch inputs mems tcs.
  Proof.
    intros * Hsch.
    inversion Hsch; auto.
  Qed.
End STCCAUSALITY.

Module StcCausality
       (Ids    : IDS)
       (Op     : OPERATORS)
       (CESyn  : CESYNTAX Op)
       (Syn    : STCSYNTAX Ids Op CESyn)
       (Syst   : STCISSYSTEM Ids Op CESyn Syn)
       (Ord    : STCORDERED Ids Op CESyn Syn Syst)
       (Var    : STCISVARIABLE Ids Op CESyn Syn)
       (Last   : STCISLAST Ids Op CESyn Syn)
       (Def    : STCISDEFINED Ids Op CESyn Syn Var Last)
       (CEIsF  : CEISFREE Ids Op CESyn)
       (IsF    : STCISFREE Ids Op CESyn Syn CEIsF)
       (WellDef: STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Last Def CEIsF IsF)
       <: STCCAUSALITY Ids Op CESyn Syn Syst Ord Var Last Def CEIsF IsF WellDef.
  Include STCCAUSALITY Ids Op CESyn Syn Syst Ord Var Last Def CEIsF IsF WellDef.
End StcCausality.
