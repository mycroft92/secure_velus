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
From Coq Require Import Lia.

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

  (** * From the history to the streams

      [node_noninterference_outputs] concludes about the node's *history*.  The
      Lustre run produces *streams*.  [SNode] supplies the link -- [sem_vars H
      (map fst n_out) yss] -- so a history agreement transfers positionally to
      a stream agreement.

      The notion mirrors [SecObcNonInterference.obc_stream_low_eq]: indexed by
      position rather than by name, because a stream carries values in the
      order of the interface, not a map.  Presence is included, since an
      NLustre stream element is a [value] and not an [option val]; the Obc leg
      splits presence out into [same_low_presence] because its element type
      cannot carry it. *)

  Definition stream_low_eq
    (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
    (xs : list ident) (xss xss' : Str.stream (list value)) : Prop :=
    forall k i x v v',
      nth_error xs i = Some x ->
      low_var ty_env dlt t x ->
      nth_error (xss k) i = Some v ->
      nth_error (xss' k) i = Some v' ->
      v = v'.

  Lemma Forall2_nth_error :
    forall {A B} (R : A -> B -> Prop) l1 l2 i a b,
      Forall2 R l1 l2 ->
      nth_error l1 i = Some a ->
      nth_error l2 i = Some b ->
      R a b.
  Proof.
    intros A B R l1 l2 i a b HF. revert i.
    induction HF as [|x y l1 l2 Hxy HF IH]; intros i Ha Hb.
    - destruct i; simpl in Ha; discriminate.
    - destruct i; simpl in Ha, Hb.
      + inversion Ha; inversion Hb; subst. exact Hxy.
      + eapply IH; eauto.
  Qed.

  Lemma history_low_eq_streams :
    forall ty_env dlt t xs H H' xss xss',
      history_low_eq ty_env dlt t xs H H' ->
      CESem.sem_vars H xs xss ->
      CESem.sem_vars H' xs xss' ->
      stream_low_eq ty_env dlt t xs xss xss'.
  Proof.
    intros ty_env dlt t xs H H' xss xss' Hlow Hsem Hsem'
           k i x v v' Hnth Hlowx Hv Hv'.
    specialize (Hsem k). specialize (Hsem' k).
    unfold CESem.sem_vars_instant in Hsem, Hsem'.
    assert (Hfx : Str.sem_var_instant (H k) x v)
      by (eapply (Forall2_nth_error (Str.sem_var_instant (H k)) xs (xss k));
          eauto).
    assert (Hfx' : Str.sem_var_instant (H' k) x v')
      by (eapply (Forall2_nth_error (Str.sem_var_instant (H' k)) xs (xss' k));
          eauto).
    unfold Str.sem_var_instant in Hfx, Hfx'.
    assert (Hin : In x xs) by (eapply nth_error_In; eauto).
    specialize (Hlow k x Hin Hlowx).
    rewrite Hfx, Hfx' in Hlow. now inversion Hlow.
  Qed.

  (** * Lustre in, Lustre out

      The two halves joined.  Each Lustre run descends to a history of the
      transcribed node; the NLustre theorem relates the two histories on the
      low outputs; [history_low_eq_streams] carries that back to the streams
      the Lustre runs produced.

      The one side condition the composition exposes is that both runs share
      the base clock.  [SNode] fixes [bk] as [clock_of] of the inputs, and the
      NLustre theorem needs one [bk] for both runs, so the two input stream
      families must have the same clock.  That is not an artefact: presence is
      observable, and the Obc leg carries the same condition as
      [eq_str (clock_of xss) (clock_of xss')]. *)

  Theorem lnode_noninterference_streams :
    forall G P Hp envs aux_names GL GN st
           nd nd' Hpn ty_env nsig dlt_sig dlt_raw t ins outs ins' outs',
      (* the source program, well formed enough to transcribe and to run *)
      to_global G Hp = OK P ->
      LN.NormFby.normalized_global G ->
      LOrd.Ordered_nodes G ->
      Forall LCau.node_causal G ->
      LTyp.wt_global G ->
      LClo.wc_global G ->
      (* the two signature globals, from the drivers *)
      SECLNG.generate_lnode_scoped_env G = OK (envs, aux_names) ->
      generate_all_lsignatures_scoped_env G envs aux_names st = OK GL ->
      SECNL.generate_all_signatures_scoped_env P envs aux_names = OK GN ->
      transcribed_program_context G P GL GN envs aux_names ->
      (* the node, and its security *)
      to_node nd Hpn = OK nd' ->
      lnode_security G GL envs aux_names nd dlt_sig dlt_raw ->
      NLOrd.Ordered_nodes P ->
      NLClo.wc_global P ->
      NLCaus.nl_global_causal P ->
      NLSyn.find_node nd'.(NLSyn.n_name) P = Some nd' ->
      find_node_env nd'.(NLSyn.n_name) envs = Some ty_env ->
      find_signature nd'.(NLSyn.n_name) GN = Some nsig ->
      (* two runs of the source node *)
      LSem.sem_node G nd.(n_name) ins outs ->
      LSem.sem_node G nd.(n_name) ins' outs' ->
      LCS.sem_clock_inputs G nd.(n_name) ins ->
      LCS.sem_clock_inputs G nd.(n_name) ins' ->
      CESem.clock_of (CIStr.tr_Streams ins)
        = CESem.clock_of (CIStr.tr_Streams ins') ->
      (* agreeing on the low inputs *)
      stream_low_eq ty_env dlt_sig t (List.map fst nd.(n_in))
        (CIStr.tr_Streams ins) (CIStr.tr_Streams ins') ->
      (* ... agree on the low outputs *)
      stream_low_eq ty_env dlt_sig t (List.map fst nd.(n_out))
        (CIStr.tr_Streams outs) (CIStr.tr_Streams outs').
  Proof.
    intros G P Hp envs aux_names GL GN st
           nd nd' Hpn ty_env nsig dlt_sig dlt_raw t ins outs ins' outs'
           Htg Hnorm Hordl Hcausl Hwt Hwcl
           Hnames Hlsigs Hnsigs Hctxs Htn Hsec
           Hord Hwc Hcaus HfndP Hfenv Hfsig
           Hrun Hrun' Hclkin Hclkin' Hclkeq Hlowin.
    pose proof (to_node_name _ _ _ Htn) as Hname.
    (* each run descends to a history of the transcribed node *)
    destruct (lustre_run_to_nlustre_history G P Hp _ _ _
                Hnorm Hordl Hcausl Hwt Hwcl Htg Hrun Hclkin)
      as (n & H & Hfn & Hin & Hout & Heqs).
    destruct (lustre_run_to_nlustre_history G P Hp _ _ _
                Hnorm Hordl Hcausl Hwt Hwcl Htg Hrun' Hclkin')
      as (n2 & H' & Hfn2 & Hin' & Hout' & Heqs').
    (* both runs find the same node, and it is the transcription of nd *)
    rewrite Hname, HfndP in Hfn. inversion Hfn; subst n.
    rewrite Hname, HfndP in Hfn2. inversion Hfn2; subst n2.
    rewrite <- Hclkeq in Heqs'.
    (* the inputs agree as histories *)
    assert (Hlowh : history_low_eq ty_env dlt_sig t (List.map fst nd.(n_in)) H H').
    { intros k x Hinx Hlowx.
      apply In_nth_error in Hinx as (i & Hnth).
      specialize (Hin k). specialize (Hin' k).
      unfold CESem.sem_vars_instant in Hin, Hin'.
      rewrite <- (to_node_in _ _ _ Htn) in Hin, Hin'.
      destruct (nth_error (CIStr.tr_Streams ins k) i) as [v|] eqn:Ev.
      2:{ exfalso.
          apply nth_error_None in Ev. apply Forall2_length in Hin.
          assert (i < length (List.map fst nd.(n_in)))
            by (apply nth_error_Some; rewrite Hnth; discriminate).
          lia. }
      destruct (nth_error (CIStr.tr_Streams ins' k) i) as [v'|] eqn:Ev'.
      2:{ exfalso.
          apply nth_error_None in Ev'. apply Forall2_length in Hin'.
          assert (i < length (List.map fst nd.(n_in)))
            by (apply nth_error_Some; rewrite Hnth; discriminate).
          lia. }
      assert (Hfx : Str.sem_var_instant (H k) x v)
        by (eapply (Forall2_nth_error (Str.sem_var_instant (H k))); eauto).
      assert (Hfx' : Str.sem_var_instant (H' k) x v')
        by (eapply (Forall2_nth_error (Str.sem_var_instant (H' k))); eauto).
      unfold Str.sem_var_instant in Hfx, Hfx'.
      rewrite Hfx, Hfx'. f_equal.
      eapply Hlowin; eauto. }
    (* the NLustre theorem *)
    assert (Hlowout :
              history_low_eq ty_env dlt_sig t (List.map fst nd.(n_out)) H H').
    { eapply (lnode_noninterference_outputs_generated G P Hp envs aux_names
                GL GN st nd nd' Hpn ty_env nsig dlt_sig dlt_raw t); eauto. }
    (* and back to the streams *)
    rewrite (to_node_out _ _ _ Htn) in Hlowout |- *.
    eapply history_low_eq_streams; eauto.
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
