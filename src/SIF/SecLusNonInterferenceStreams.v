(** Noninterference for Lustre over Lustre's own semantics.

    [SecLusNonInterference.v] states the leg over the *transcribed* node's runs:
    its semantic hypotheses are [Indexed.sem_equation] on [nd'].  That is the
    granularity the NLustre theorem is phrased at, so nothing was lost in the
    pull-back, but it is not yet a statement about Lustre behaviour.

    Closing that does not need the NLustre theorem transported into coinductive
    semantics.  It needs the semantics brought the other way, and both bridges
    already exist:

      [LS.sem_node G f ins outs]
        -- [Transcription.Correctness.sem_l_nl] -->
      [NLSC.sem_node P f ins outs]
        -- [NLCoindToIndexed.implies] -->
      [Indexed.sem_node P f (tr_Streams ins) (tr_Streams outs)]

    and inverting [Indexed.sem_node] hands back exactly what the NLustre
    theorem wants: the history, and [Forall (sem_equation bk H) nd'.(n_eqs)].
    The same inversion gives [sem_vars H (map fst nd'.(n_out)) yss], which is
    what turns the conclusion from a statement about the history into one about
    the output streams. *)

From Coq Require Import List.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
From Velus Require Import CoindToIndexed.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics.
From Velus Require Import Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLCoindSemantics.
From Velus Require Import NLustre.NLCoindToIndexed.
From Velus Require Import Transcription.Tr.
From Velus Require Import Transcription.TrClocking.
From Velus Require Import Transcription.Correctness.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecLusNLusTranslation.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import SIF.SecLusNonInterference.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLUSNONINTERFERENCESTREAMS
  (Import Ids     : IDS)
  (Import Lat     : Lattice)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import SecT    : SECTYPES Lat)
  (Import LSyn    : LSYNTAX Ids Op)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CETyp          : CETYPING Ids Op CESyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Str            : INDEXEDSTREAMS Op OpAux)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (NLMem          : MEMORIES Ids Op CESyn NLSyn)
  (NLIsD          : ISDEFINED Ids Op CESyn NLSyn NLMem)
  (NLIsF          : ISFREE Ids Op CESyn NLSyn CEIsF)
  (NLCaus         : NLUSTRECAUSALITY Ids Op CESyn NLSyn CEIsF NLIsF)
  (NLClo          : NLCLOCKING Ids Op CESyn NLSyn NLOrd NLMem NLIsD CEIsF NLIsF CEClo)
  (CESem          : CESEMANTICS Ids Op OpAux CESyn Str)
  (CEProps        : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Indexed        : NLINDEXEDSEMANTICS Ids Op OpAux CESyn NLSyn Str NLOrd CESem)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import SECNL   : SECNLUSTYPING Ids Op SC CESyn NLSyn SIG NAMEGEN CEIsF CEClo
                      SECCET NLOrd NLMem NLIsD NLIsF NLClo)
  (SECNLC         : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn NLSyn Lat SecT SIG
                      SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd NLMem NLIsD
                      NLIsF NLClo SECNL)
  (SECLNG         : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (LClo           : LCLOCKING Ids Op LSyn)
  (Import LOrd    : LORDERED Ids Op LSyn)
  (TRC            : TRCLOCKING Ids Op OpAux LSyn LClo CESyn NLSyn NLOrd NLMem
                      NLIsD CEIsF NLIsF CEClo NLClo TR)
  (Import NLNI    : SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT
                      CESyn NLSyn SIG NAMEGEN CETyp CEIsF CEClo SECCET Str
                      NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps
                      Indexed SIGPROOFS SECNL SECNLC)
  (Import SECLNL  : SECLUSNLUSTRANSLATION Ids Op OpAux SC LSyn CESyn NLSyn Lat
                      SecT STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd
                      NLMem NLIsD NLIsF NLClo TR SECL SECNL SECNLC SECLNG LClo
                      LOrd TRC)
  (LTyp           : LTYPING Ids Op LSyn)
  (LCau           : LCAUSALITY Ids Op LSyn)
  (Import CStr    : COINDSTREAMS Op OpAux)
  (LSem           : LSEMANTICS Ids Op OpAux LSyn LOrd CStr)
  (LCS            : LCLOCKSEMANTICS Ids Op OpAux LSyn LClo LCau LOrd CStr Str
                      LSem)
  (LN             : NORMALIZATION Ids Op OpAux LSyn LCau)
  (NLSC           : NLCOINDSEMANTICS Ids Op OpAux CESyn NLSyn CStr NLOrd)
  (TRCorr         : CORRECTNESS Ids Op OpAux LSyn CESyn NLSyn TR LTyp LClo LCau
                      NLOrd LOrd CStr Str LSem LCS LN NLSC)
  (CIStr          : COINDTOINDEXED Op OpAux CStr Str)
  (NLC2I          : NLCOINDTOINDEXED Ids Op OpAux CESyn NLSyn Str CStr CIStr
                      NLOrd CESem Indexed NLSC)
  (Import SECLNI  : SECLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CETyp CEIsF CEClo SECCET Str NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps Indexed TR SECL SECNL SECNLC SECLNG LClo LOrd TRC NLNI SECLNL).

  (** * From a Lustre run to the transcribed node's history

      The two bridges, composed, and then [Indexed.sem_node] inverted.  What
      comes back is the shape the NLustre noninterference theorem is stated
      over -- and, in [sem_vars] on the outputs, the link from that history to
      the streams the Lustre run produced. *)

  Lemma lustre_run_to_nlustre_history :
    forall G P Hp f ins outs,
      LN.NormFby.normalized_global G ->
      LOrd.Ordered_nodes G ->
      Forall LCau.node_causal G ->
      LTyp.wt_global G ->
      LClo.wc_global G ->
      to_global G Hp = OK P ->
      LSem.sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      exists n H,
        NLSyn.find_node f P = Some n
        /\ CESem.sem_vars H (List.map fst n.(NLSyn.n_in)) (CIStr.tr_Streams ins)
        /\ CESem.sem_vars H (List.map fst n.(NLSyn.n_out)) (CIStr.tr_Streams outs)
        /\ Forall (Indexed.sem_equation P
                     (CESem.clock_of (CIStr.tr_Streams ins)) H)
                  n.(NLSyn.n_eqs).
  Proof.
    intros G P Hp f ins outs Hnorm Hord Hcaus Hwt Hwc Htr Hsem Hclkin.
    assert (Hnl : NLSC.sem_node P f ins outs)
      by (eapply TRCorr.sem_l_nl; eauto).
    apply NLC2I.implies in Hnl.
    inversion Hnl as [bk H f' xss yss n Hbk Hfind Hin Hout Hclocked Heqs].
    subst bk xss yss f'.
    exists n, H. repeat split; assumption.
  Qed.

End SECLUSNONINTERFERENCESTREAMS.

Module SecLusNonInterferenceStreams
  (Import Ids     : IDS)
  (Import Lat     : Lattice)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import SecT    : SECTYPES Lat)
  (Import LSyn    : LSYNTAX Ids Op)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CETyp          : CETYPING Ids Op CESyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Str            : INDEXEDSTREAMS Op OpAux)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (NLMem          : MEMORIES Ids Op CESyn NLSyn)
  (NLIsD          : ISDEFINED Ids Op CESyn NLSyn NLMem)
  (NLIsF          : ISFREE Ids Op CESyn NLSyn CEIsF)
  (NLCaus         : NLUSTRECAUSALITY Ids Op CESyn NLSyn CEIsF NLIsF)
  (NLClo          : NLCLOCKING Ids Op CESyn NLSyn NLOrd NLMem NLIsD CEIsF NLIsF CEClo)
  (CESem          : CESEMANTICS Ids Op OpAux CESyn Str)
  (CEProps        : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Indexed        : NLINDEXEDSEMANTICS Ids Op OpAux CESyn NLSyn Str NLOrd CESem)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import SECNL   : SECNLUSTYPING Ids Op SC CESyn NLSyn SIG NAMEGEN CEIsF CEClo
                      SECCET NLOrd NLMem NLIsD NLIsF NLClo)
  (SECNLC         : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn NLSyn Lat SecT SIG
                      SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd NLMem NLIsD
                      NLIsF NLClo SECNL)
  (SECLNG         : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (LClo           : LCLOCKING Ids Op LSyn)
  (Import LOrd    : LORDERED Ids Op LSyn)
  (TRC            : TRCLOCKING Ids Op OpAux LSyn LClo CESyn NLSyn NLOrd NLMem
                      NLIsD CEIsF NLIsF CEClo NLClo TR)
  (Import NLNI    : SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT
                      CESyn NLSyn SIG NAMEGEN CETyp CEIsF CEClo SECCET Str
                      NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps
                      Indexed SIGPROOFS SECNL SECNLC)
  (Import SECLNL  : SECLUSNLUSTRANSLATION Ids Op OpAux SC LSyn CESyn NLSyn Lat
                      SecT STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd
                      NLMem NLIsD NLIsF NLClo TR SECL SECNL SECNLC SECLNG LClo
                      LOrd TRC)
  (LTyp           : LTYPING Ids Op LSyn)
  (LCau           : LCAUSALITY Ids Op LSyn)
  (Import CStr    : COINDSTREAMS Op OpAux)
  (LSem           : LSEMANTICS Ids Op OpAux LSyn LOrd CStr)
  (LCS            : LCLOCKSEMANTICS Ids Op OpAux LSyn LClo LCau LOrd CStr Str
                      LSem)
  (LN             : NORMALIZATION Ids Op OpAux LSyn LCau)
  (NLSC           : NLCOINDSEMANTICS Ids Op OpAux CESyn NLSyn CStr NLOrd)
  (TRCorr         : CORRECTNESS Ids Op OpAux LSyn CESyn NLSyn TR LTyp LClo LCau
                      NLOrd LOrd CStr Str LSem LCS LN NLSC)
  (CIStr          : COINDTOINDEXED Op OpAux CStr Str)
  (NLC2I          : NLCOINDTOINDEXED Ids Op OpAux CESyn NLSyn Str CStr CIStr
                      NLOrd CESem Indexed NLSC)
  (Import SECLNI  : SECLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CETyp CEIsF CEClo SECCET Str NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps Indexed TR SECL SECNL SECNLC SECLNG LClo LOrd TRC NLNI SECLNL)
  <: SECLUSNONINTERFERENCESTREAMS Ids Lat Op OpAux SC SecT LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CETyp CEIsF CEClo SECCET Str NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps Indexed TR SECL SECNL SECNLC SECLNG LClo LOrd TRC NLNI SECLNL LTyp LCau CStr LSem LCS LN NLSC TRCorr CIStr NLC2I SECLNI.

Include SECLUSNONINTERFERENCESTREAMS Ids Lat Op OpAux SC SecT LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CETyp CEIsF CEClo SECCET Str NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps Indexed TR SECL SECNL SECNLC SECLNG LClo LOrd TRC NLNI SECLNL LTyp LCau CStr LSem LCS LN NLSC TRCorr CIStr NLC2I SECLNI.

End SecLusNonInterferenceStreams.
