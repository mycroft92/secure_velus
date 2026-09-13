(** Noninterference for STC behaviors that come from translated secure NLustre nodes. *)

From Coq Require Import List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindToIndexed.
From Velus Require Import CoreExpr.
From Velus Require Import NLustre.
From Velus Require Import Stc.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import NLustreToStc.Correctness.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import SIF.SecNLusStcTranslation.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECSTCNONINTERFERENCE
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import CStr  : COINDSTREAMS Op OpAux)
  (Import Str   : INDEXEDSTREAMS Op OpAux)
  (Import CIStr : COINDTOINDEXED Op OpAux CStr Str)
  (Import SC    : SECMONAD Ids)
  (Import SecT  : SECTYPES Lat)
  (Import CE    : COREEXPR Ids Op OpAux Str)
  (Import NL    : NLUSTRE Ids Op OpAux CStr Str CIStr CE)
  (Import Stc   : STC Ids Op OpAux Str CE)
  (Import Translation : TRANSLATION Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (Correctness  : CORRECTNESS Ids Op OpAux CStr Str CIStr CE NL Stc Translation)
  (Import SIG          : SIGNATURE Ids SC)
  (Import SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN      : NAMEGEN Ids Op CE.Syn NL.Syn)
  (Import SECCETYPING  : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (NLCaus              : NLUSTRECAUSALITY Ids Op CE.Syn NL.Syn CE.IsF NL.IsF)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CE.Syn NL.Syn SIG NAMEGEN CE.IsF CE.Clo
       SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
       NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo
       SECNLUSTYPING)
  (NLusSupport :
     SECNLUSNONINTERFERENCESUPPORT Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG
       NAMEGEN CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD
       NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (NLusNI :
     SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG NAMEGEN
       CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD NL.IsF
       NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (NLusStcBridge :
     SECNLUSSTCTRANSLATION Ids Lat Op SC SecT CE.Syn NL.Syn Stc.Syn NL.Mem
       Translation SIG SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord
       NL.IsD NL.IsF NL.Clo SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Stc.Last
       Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING
       SECSTCTYPINGCORRECTNESS).

  Definition ground_instantiation : Type := NLusSupport.ground_instantiation.

  Definition tuple_stream_low_eq
    (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
    (xs : list ident) (xss xss' : stream (list value)) : Prop :=
    forall k i x v v',
      nth_error xs i = Some x ->
      NLusSupport.low_var ty_env dlt t x ->
      nth_error (xss k) i = Some v ->
      nth_error (xss' k) i = Some v' ->
      v = v'.

  Definition translated_system_behavior
    (all_nodes : NL.Syn.global) (sys : Stc.Syn.system)
    (xss yss : stream (list value)) : Prop :=
    exists M,
      NL.MemSem.msem_node all_nodes (Stc.Syn.s_name sys) xss M yss /\
      Stc.Sem.initial_state (Translation.translate all_nodes) (Stc.Syn.s_name sys) (M 0) /\
      Stc.Sem.loop (Translation.translate all_nodes) (Stc.Syn.s_name sys) xss yss (M 0) 0.

  Definition system_security
    (all_nodes : NL.Syn.global) (Gsrc Gstc : secglobal)
    (envs : node_scoped_env) (aux_names : list node_aux_names)
    (sys : Stc.Syn.system)
    (dlt_sig dlt_raw : ground_instantiation) : Prop :=
    exists n nsig ssig,
      sys = Translation.translate_node n /\
      find_node n.(n_name) all_nodes = Some n /\
      SIG.find_signature n.(n_name) Gsrc = Some nsig /\
      SIG.find_signature (Stc.Syn.s_name sys) Gstc = Some ssig /\
      NLusStcBridge.Signature_head_consistent nsig ssig /\
      NLusNI.node_security all_nodes Gsrc envs aux_names n dlt_sig dlt_raw.

  (** This moves low-equivalence from tuple streams back to history form so the source theorem can be applied. *)
  Lemma history_low_eq_of_tuple_stream_low_eq:
    forall ty_env dlt t xs H H' xss xss',
      CE.Sem.sem_vars H xs xss ->
      CE.Sem.sem_vars H' xs xss' ->
      tuple_stream_low_eq ty_env dlt t xs xss xss' ->
      NLusSupport.history_low_eq ty_env dlt t xs H H'.
  Proof.
    intros ty_env dlt t xs H H' xss xss' Hvars Hvars' Hlow k x Hin Hlowx.
    destruct (SecT.In_nth_error_ex _ _ _ Hin) as [i Hnthx].
    specialize (Hvars k).
    specialize (Hvars' k).
    destruct (nth_error (xss k) i) as [v|] eqn:Hnthv.
    - destruct (nth_error (xss' k) i) as [v'|] eqn:Hnthv'.
      + eapply NLusSupport.sem_vars_instant_nth_error in Hvars; eauto.
        eapply NLusSupport.sem_vars_instant_nth_error in Hvars'; eauto.
        unfold sem_var_instant in Hvars, Hvars'.
        rewrite Hvars, Hvars'.
        f_equal.
        eapply Hlow; eauto.
      + assert (Hi : i < length xs).
        {
          apply nth_error_Some.
          rewrite Hnthx.
          discriminate.
        }
        assert (Hi' : i < length (xss' k)).
        {
          rewrite <- (Forall2_length _ _ _ Hvars').
          exact Hi.
        }
        pose proof (nth_error_nth' (xss' k) i absent Hi') as Hsome.
        rewrite Hnthv' in Hsome.
        discriminate.
    - assert (Hi : i < length xs).
      {
        apply nth_error_Some.
        rewrite Hnthx.
        discriminate.
      }
      assert (Hi' : i < length (xss k)).
      {
        rewrite <- (Forall2_length _ _ _ Hvars).
        exact Hi.
      }
      pose proof (nth_error_nth' (xss k) i absent Hi') as Hsome.
      rewrite Hnthv in Hsome.
      discriminate.
  Qed.

  (** This converts the source-side history result back to tuple-stream equality on translated inputs or outputs. *)
  Lemma tuple_stream_low_eq_of_history_low_eq:
    forall ty_env dlt t xs H H' xss xss',
      CE.Sem.sem_vars H xs xss ->
      CE.Sem.sem_vars H' xs xss' ->
      NLusSupport.history_low_eq ty_env dlt t xs H H' ->
      tuple_stream_low_eq ty_env dlt t xs xss xss'.
  Proof.
    intros ty_env dlt t xs H H' xss xss' Hvars Hvars' Hlow k i x v v'
           Hnthx Hlowx Hnthv Hnthv'.
    specialize (Hvars k).
    specialize (Hvars' k).
    eapply NLusSupport.sem_vars_instant_nth_error in Hvars; eauto.
    eapply NLusSupport.sem_vars_instant_nth_error in Hvars'; eauto.
    unfold sem_var_instant in Hvars, Hvars'.
    specialize (Hlow k).
    specialize (Hlow x (nth_error_In _ _ Hnthx) Hlowx).
    rewrite Hvars in Hlow.
    rewrite Hvars' in Hlow.
    now inversion Hlow.
  Qed.

  Lemma translated_system_behavior_from_msem:
    forall (all_nodes : NL.Syn.global) (sys : Stc.Syn.system) xss M yss,
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      NL.MemSem.msem_node all_nodes (Stc.Syn.s_name sys) xss M yss ->
      translated_system_behavior all_nodes sys xss yss.
  Proof.
    intros all_nodes sys xss M yss Hord Hwc Hmsem.
    unfold translated_system_behavior.
    pose proof
      (Correctness.correctness_loop all_nodes (Stc.Syn.s_name sys) xss M yss Hord Hwc Hmsem)
      as (Hinit & Hloop).
    exists M.
    repeat split; assumption.
  Qed.

  Lemma system_security_from_node_security:
    forall all_nodes Gsrc Gstc envs aux_names n dlt_sig dlt_raw,
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Clo.wc_global all_nodes ->
      NL.Ord.Ordered_nodes all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK Gsrc ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env (Translation.translate all_nodes) envs aux_names = OK Gstc ->
      find_node n.(n_name) all_nodes = Some n ->
      NLusNI.node_security all_nodes Gsrc envs aux_names n dlt_sig dlt_raw ->
      system_security all_nodes Gsrc Gstc envs aux_names (Translation.translate_node n) dlt_sig dlt_raw.
  Proof.
    intros all_nodes Gsrc Gstc envs aux_names n dlt_sig dlt_raw
           Henvsgen Hwc Hord Hallsrc Hallstc Hfindnode Hsec.
    destruct Hsec as
      [ty_env nsig
       clk_id rst_id clk_type rst_type inp out locals raw st_n
       Hfindnode_sec Hfindenv_sec Hfindsig Hsiggen
       Haux Hclk Hrst Hinp Hout Hlocals Hraw
       Hsigdef Hsatsig Hagree Hsatraw Hcallsec Hresetsec].
    destruct
      (NLusStcBridge.generated_program_signatures_preserved_global
         all_nodes Gsrc Gstc envs aux_names
         Henvsgen Hwc Hord Hallsrc Hallstc
         n.(n_name) nsig Hfindsig)
      as (ssig & Hfindstc & Hhead).
    unfold system_security.
    exists n, nsig, ssig.
    split; [reflexivity|].
    split; [exact Hfindnode|].
    split; [exact Hfindsig|].
    split; [simpl; exact Hfindstc|].
    split; [exact Hhead|].
    econstructor; eauto.
  Qed.

  (** This is the final STC-facing theorem.  It takes a translated system together with the source security witness behind it, runs the NLustre noninterference theorem on the matching source node, and transports the conclusion back to the translated STC input and output streams.  The statement is exactly about translated behaviors, which is the target property proved by this development. *)
  (** Direction: source to target, like the Obc layer above it.  The
      hypotheses constrain runs of the Stc system the compiler emits for
      a secure NLustre node, and the conclusion is low-equivalence of
      that system's outputs.  This is the theorem the Obc layer runs on
      the dataflow behaviour it reads out of a
      [translated_class_behavior]. *)
  Theorem translated_system_noninterference_outputs:
    forall all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss',
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK Gsrc ->
      NLCaus.nl_global_causal all_nodes ->
      find_node_env (Stc.Syn.s_name sys) envs = Some ty_env ->
      system_security all_nodes Gsrc Gstc envs aux_names sys dlt_sig dlt_raw ->
      translated_system_behavior all_nodes sys xss yss ->
      translated_system_behavior all_nodes sys xss' yss' ->
      eq_str (clock_of xss) (clock_of xss') ->
      tuple_stream_low_eq ty_env dlt_sig t (List.map fst (Stc.Syn.s_in sys)) xss xss' ->
      tuple_stream_low_eq ty_env dlt_sig t (List.map fst (Stc.Syn.s_out sys)) yss yss'.
  Proof.
    intros all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss'
           Henvsgen Hord Hwc Hallsrc Hcaus Hfindenv
           Hsyssec Hbeh Hbeh' Hclock_eq Hlowin.
    destruct Hsyssec as
      (n & nsig & ssig
       & Hsys & Hfindnode & Hfindsig & Hfindsig_stc & Hhead & Hnodesec).
    subst sys.
    simpl in Hfindenv, Hlowin |- *.
    destruct Hbeh as (M & Hmsem & Hinit & Hloop).
    destruct Hbeh' as (M' & Hmsem' & Hinit' & Hloop').
    pose proof Hmsem as Hsemnode.
    pose proof Hmsem' as Hsemnode'.
    eapply NL.MemSem.msem_sem_node in Hsemnode.
    eapply NL.MemSem.msem_sem_node in Hsemnode'.
    destruct (NLusSupport.sem_node_inv all_nodes n.(n_name) xss yss Hsemnode)
      as (bk & Hsrc & nd & Hbk & Hfindnd & Hsem_in & Hsem_out & Hclocked & Heqs).
    destruct (NLusSupport.sem_node_inv all_nodes n.(n_name) xss' yss' Hsemnode')
      as (bk' & Hsrc' & nd' & Hbk' & Hfindnd' & Hsem_in' & Hsem_out' & Hclocked' & Heqs').
    assert (Hnd_eq : nd = n) by congruence.
    assert (Hnd_eq' : nd' = n) by congruence.
    subst nd nd'.
    subst bk bk'.
    assert (Heqs'_clock :
              Forall (NL.Sem.sem_equation all_nodes (clock_of xss) Hsrc') n.(n_eqs)).
    {
      rewrite Forall_forall in *.
      intros eq Heqin.
      specialize (Heqs' eq Heqin).
      eapply NL.Sem.sem_equation_eq_str; eauto.
      intros k. symmetry. apply Hclock_eq.
    }
    assert (Hlow_hist :
              NLusSupport.history_low_eq ty_env dlt_sig t (List.map fst n.(n_in)) Hsrc Hsrc').
    {
      eapply history_low_eq_of_tuple_stream_low_eq; eauto.
    }
    pose proof
      (NLusNI.node_noninterference_outputs
         all_nodes Gsrc envs aux_names
         n ty_env nsig dlt_sig dlt_raw t (clock_of xss) Hsrc Hsrc'
         Henvsgen Hord Hwc Hallsrc Hcaus
         Hfindnode Hfindenv Hfindsig Hnodesec
         Heqs Heqs'_clock Hlow_hist)
      as Hlow_out.
    eapply tuple_stream_low_eq_of_history_low_eq; eauto.
  Qed.
End SECSTCNONINTERFERENCE.

Module SecStcNonInterference
  (Ids   : IDS)
  (Lat   : Lattice)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Op)
  (CStr  : COINDSTREAMS Op OpAux)
  (Str   : INDEXEDSTREAMS Op OpAux)
  (CIStr : COINDTOINDEXED Op OpAux CStr Str)
  (SC    : SECMONAD Ids)
  (SecT  : SECTYPES Lat)
  (CE    : COREEXPR Ids Op OpAux Str)
  (NL    : NLUSTRE Ids Op OpAux CStr Str CIStr CE)
  (Stc   : STC Ids Op OpAux Str CE)
  (Translation : TRANSLATION Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (Correctness : CORRECTNESS Ids Op OpAux CStr Str CIStr CE NL Stc Translation)
  (SIG          : SIGNATURE Ids SC)
  (SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (NAMEGEN      : NAMEGEN Ids Op CE.Syn NL.Syn)
  (SECCETYPING  : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (NLCaus       : NLUSTRECAUSALITY Ids Op CE.Syn NL.Syn CE.IsF NL.IsF)
  (SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CE.Syn NL.Syn SIG NAMEGEN CE.IsF CE.Clo
       SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo)
  (SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
       NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo
       SECNLUSTYPING)
  (NLusSupport :
     SECNLUSNONINTERFERENCESUPPORT Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG
       NAMEGEN CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD
       NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (NLusNI :
     SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG NAMEGEN
       CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD NL.IsF
       NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (NLusStcBridge :
     SECNLUSSTCTRANSLATION Ids Lat Op SC SecT CE.Syn NL.Syn Stc.Syn NL.Mem
       Translation SIG SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord
       NL.IsD NL.IsF NL.Clo SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Stc.Last
       Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING
       SECSTCTYPINGCORRECTNESS)
  <: SECSTCNONINTERFERENCE
       Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc Translation
       Correctness SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI SECSTCTYPING
       SECSTCTYPINGCORRECTNESS NLusStcBridge.
  Include SECSTCNONINTERFERENCE
            Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc Translation
            Correctness SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
            SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI
            SECSTCTYPING SECSTCTYPINGCORRECTNESS NLusStcBridge.
End SecStcNonInterference.
