(** End to end: a source security policy gives noninterference of the Obc step method.

    [policy_node_security] constructs the NLustre witness from a valuation satisfying
    the source signature (no security-data hypothesis); [class_security_from_node_security]
    carries it through Stc, scheduling and Obc; [class_noninterference_outputs] concludes. *)

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
From Velus Require Import Stc.StcSchedule.
From Velus Require Import Obc.
From Velus Require NLustreToStc.Translation.
From Velus Require NLustreToStc.Correctness.
From Velus Require StcToObc.Translation.
From Velus Require StcToObc.Correctness.
From Velus Require Import StcToObc.StcMemoryCorres.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecTypes.
From Velus Require NLustreToStc.NL2StcClocking.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import SIF.SecNLusNodeSecurity.
From Velus Require Import SIF.SecObcNonInterference.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import SIF.SecNLusStcTranslation.
From Velus Require Import SIF.SecObcTyping.
From Velus Require Import SIF.SecObcTypingCorrectness.
From Velus Require Import SIF.SecStcObcTranslation.
From Velus Require Import SIF.SecNLusStcObcEnv.
From Velus Require Import SIF.SecStcNonInterference.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.


Module SecEndToEnd
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
  (Import TransNL : NLustreToStc.Translation.TRANSLATION
                      Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (NLStcCorr : NLustreToStc.Correctness.CORRECTNESS
                 Ids Op OpAux CStr Str CIStr CE NL Stc TransNL)
  (** The translation's own clocking theorem, so that the Stc program's
      well-clockedness is derived from the source's rather than assumed. *)
  (NL2StcClo : NLustreToStc.NL2StcClocking.NL2STCCLOCKING
                 Ids Op OpAux CStr Str CIStr CE NL Stc TransNL)
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
  (Import NLusNI :
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
       TransNL SIG SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord
       NL.IsD NL.IsF NL.Clo SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Stc.Last
       Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING
       SECSTCTYPINGCORRECTNESS)
  (StcNI :
     SECSTCNONINTERFERENCE Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       TransNL NLStcCorr SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI SECSTCTYPING
       SECSTCTYPINGCORRECTNESS NLusStcBridge)
  (** The Obc side proper: syntax, semantics and the translation's own
      correctness theorem, exactly as [NLCorrectness] wires them. *)
  (Import Obc   : OBC Ids Op OpAux)
  (Import TransObc : StcToObc.Translation.TRANSLATION
                       Ids Op OpAux CE.Syn Stc.Syn Obc.Syn)
  (Import Corres : STCMEMORYCORRES Ids Op CE.Syn Stc.Syn Stc.Last)
  (StcObcCorr : StcToObc.Correctness.CORRECTNESS
                  Ids Op OpAux Str CE Stc Obc TransObc Corres)
  (** Velus's own scheduler: the Obc code the compiler emits comes from
      the *scheduled* Stc program, which is the only one [Well_defined]
      can hold of. *)
  (ExtSch : EXT_STCSCHEDULER Ids Op CE.Syn Stc.Syn)
  (Sched : STCSCHEDULE Ids Op OpAux Str CE Stc.Syn Stc.Syst Stc.Ord Stc.Sem
             Stc.Typ Stc.Var Stc.Last Stc.Def Stc.Clo Stc.Free Stc.Wdef ExtSch)
  (** The Stc-to-Obc signature bridge, so that a class's security witness
      can name the Obc signature the way [system_security] names the Stc
      one.  Taken as a parameter, not re-derived. *)
  (SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC Obc.Syn SIG)
  (SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC Obc.Syn Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (StcObcBridge :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CE.Syn Stc.Syn Obc.Syn Lat SecT SIG
       SIGPROOFS CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def Stc.Syst
       Stc.Ord Stc.Free Stc.Clo SECSTCTYPING NL.Syn NAMEGEN Stc.Wdef
       SECSTCTYPINGCORRECTNESS TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS)
  (** The chain layer, which is where the environment facts and the
      scheduling step are discharged. *)
  (ChainEnv :
     SECNLUSSTCOBCENV Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       ExtSch Sched Obc.Syn TransNL TransObc SIG SIGPROOFS NAMEGEN
       SECCETYPING SECSTCTYPING SECSTCTYPINGCORRECTNESS SECOBCTYPING
       SECOBCTYPINGCORRECTNESS StcObcBridge)
  (Import ObcNI :
     SECOBCNONINTERFERENCE
       Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc TransNL
       NLStcCorr NL2StcClo SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI
       SECSTCTYPING SECSTCTYPINGCORRECTNESS NLusStcBridge StcNI Obc
       TransObc Corres StcObcCorr ExtSch Sched SECOBCTYPING
       SECOBCTYPINGCORRECTNESS StcObcBridge ChainEnv).

  Module NS := SecNLusNodeSecurity Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG NAMEGEN
    CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD NL.IsF NLCaus NL.Clo
    CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusNI.

  Theorem policy_class_noninterference:
    forall all_nodes Gsrc Gstc Gstcs Gobc envs aux_names pre n post sgS sgN d1,
      NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      Stc.Clo.wc_program (TransNL.translate all_nodes) ->
      Stc.Wdef.Well_scheduled (Sched.schedule (TransNL.translate (rev all_nodes))) ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux_names
        = OK Gsrc ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (TransNL.translate (rev all_nodes)) envs aux_names = OK Gstc ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (Sched.schedule (TransNL.translate (rev all_nodes))) envs aux_names = OK Gstcs ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env
        (TransObc.translate (Sched.schedule (TransNL.translate (rev all_nodes))))
        envs aux_names = OK Gobc ->
      NLCaus.nl_global_causal all_nodes ->
      rev all_nodes = pre ++ n :: post ->
      SIG.find_signature n.(NL.Syn.n_name) Gsrc = Some sgN ->
      SIGPROOFS.signatures_preserved sgS sgN ->
      NLusSupport.signature_satisfied d1 sgS ->
      exists w,
        SecT.agree_on (SIG.signature_scope sgS) d1 w /\
        forall stepm ty_env t xss xss' yss yss' ins ins' outs outs',
          Obc.Syn.find_method step
            (TransObc.translate_system
               (Sched.schedule_system (TransNL.translate_node n))).(Obc.Syn.c_methods)
            = Some stepm ->
          find_node_env n.(NL.Syn.n_name) envs = Some ty_env ->
          translated_class_behavior all_nodes (TransNL.translate_node n)
            xss yss ins outs ->
          translated_class_behavior all_nodes (TransNL.translate_node n)
            xss' yss' ins' outs' ->
          eq_str (clock_of xss) (clock_of xss') ->
          same_low_presence ty_env w t
            (List.map fst stepm.(Obc.Syn.m_in)) xss xss' ->
          obc_stream_low_eq ty_env w t
            (List.map fst stepm.(Obc.Syn.m_in)) ins ins' ->
          obc_stream_low_eq ty_env w t
            (List.map fst stepm.(Obc.Syn.m_out)) outs outs'.
  Proof.
    intros all_nodes Gsrc Gstc Gstcs Gobc envs aux_names pre n post sgS sgN d1
      Henv Hord Hwc Hwcstc Hsch Hgsrc Hgstc Hgstcs Hgobc Hcaus Hsplit Hfind Hpres Hsat.
    destruct (NS.policy_node_security all_nodes envs aux_names Gsrc Henv Hord Hwc
                Hgsrc pre n post Hsplit sgS sgN d1 Hfind Hpres Hsat)
      as (w & Hagree & Hsec).
    exists w. split; [exact Hagree|].
    intros stepm ty_env t xss xss' yss yss' ins ins' outs outs' Hstepm Hfenv
      Hb Hb' Hclk Habs Hlow.
    assert (Hnin : In n all_nodes).
    { apply (proj2 (in_rev _ _)). rewrite Hsplit. apply in_or_app. right. left. reflexivity. }
    assert (Hfn : NL.Syn.find_node n.(NL.Syn.n_name) all_nodes = Some n)
      by (apply NS.find_node_of_In'; [exact (Ordered_nodes_nodup_names all_nodes Hord)|exact Hnin]).
    pose proof (class_security_from_node_security all_nodes Gsrc Gstc Gstcs Gobc envs
                  aux_names n w w Henv Hord Hwc Hwcstc Hsch Hgsrc Hgstc Hgstcs Hgobc
                  Hfn Hsec) as Hcls.
    eapply class_noninterference_outputs;
      [reflexivity|exact Hstepm|exact Henv|exact Hord|exact Hwc|exact Hgsrc|exact Hcaus
      |exact Hfenv|exact Hcls|exact Hb|exact Hb'|exact Hclk|exact Habs|exact Hlow].
  Qed.

End SecEndToEnd.
