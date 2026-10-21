(** Noninterference for a source Lustre node, over Lustre's own (coinductive) semantics.

    The theorem [LusNI.lustre_noninterference] ties the two halves of the Lustre leg:

    - the signature half ([Check.source_signatures_entail_nlustre]): the signatures generated
      for the source program entail those of the transcribed NLustre program, so a policy
      (a valuation satisfying the stored constraints of the source signature) is realised by
      a valuation satisfying the NLustre signature;
    - the NLustre noninterference theorem, whose [node_security] hypothesis is constructed
      from that valuation ([SecNLusNodeSecurity.policy_node_security]) rather than assumed.

    Two runs of the source node (Lustre semantics, [L.Sem.sem_node]) with low-equal inputs
    have low-equal outputs.  The runs descend to NLustre by the correctness of the two
    normalisation passes and of the transcription ([source_run_nl]); the NLustre theorem is
    applied to the histories of the two runs, and the result is read back as a statement
    about the Lustre streams ([stream_low_eq]).  No hypothesis about the security data of
    the normalised program is taken. *)

From Velus Require Import Common.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecLusNLusTranslation.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SecLusUnnesting.
From Velus Require Import SIF.SecNamingTotality.
From Velus Require Import SIF.SecLNamingTotality.
From Velus Require Import SIF.SecLusNormalization.
From Velus Require Import SIF.SecLusConstraintExport.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterferenceClockedStep.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import SIF.SecNLusNodeSecurity.
From Coq Require Import String List.
From compcert Require Import common.Errors.
Import ListNotations.
Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module Import OpAux := Interface.OpAux.

Module LusNI (Lat : Lattice).
  Module C := Check Lat.
  Module NLCaus := NLustreCausality Ids Op CE.Syn NL.Syn CE.IsF NL.IsF.
  Module CausBridge := NLustreCausalityBridge Ids Op OpAux L.Syn CE.Syn NL.Syn CE.IsF NL.IsF L.Clo L.Cau TR.Tr NLCaus.
  Module NI := SecNLusNonInterference Ids Lat Op OpAux SC C.SecT CE.Syn NL.Syn SIG
    ConcreteNameGen CE.Typ CE.IsF CE.Clo ConcreteSecCETyping IStr NL.Ord NL.Mem NL.IsD
    NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem C.SIGPROOFS C.SECNLUSTYPING C.SECNLC.
  Module NS := SecNLusNodeSecurity Ids Lat Op OpAux SC C.SecT CE.Syn NL.Syn SIG
    ConcreteNameGen CE.Typ CE.IsF CE.Clo ConcreteSecCETyping IStr NL.Ord NL.Mem NL.IsD
    NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem C.SIGPROOFS C.SECNLUSTYPING C.SECNLC NI.

  Section SOURCE_RUN.
  Import L.Norm.Norm.
  Lemma source_run_nl :
    forall G Hwl Hpr Hunt Hpref1 P Hp f ins outs,
      L.Typ.wt_global G -> L.Clo.wc_global G ->
      Forall L.Cau.node_causal (Unnesting.unnest_global G Hwl Hpr) ->
      TR.Tr.to_global (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) Hp = OK P ->
      L.Sem.sem_node G f ins outs ->
      L.ClSem.sem_clock_inputs G f ins ->
      NL.CoindSem.sem_node P f ins outs.
  Proof.
    intros G Hwl Hpr Hunt Hpref1 P Hp f ins outs Hwt Hwc Hcaus Htr Hsem Hclk.
    set (G1 := Unnesting.unnest_global G Hwl Hpr) in *.
    assert (Hwt1 : L.Typ.wt_global G1) by exact (L.Norm.Correct.Typing.unnest_global_wt G Hwl Hpr Hwt).
    assert (Hwc1 : L.Clo.wc_global G1) by exact (L.Norm.Correct.Clocking.unnest_global_wc G Hwl Hpr Hwc).
    assert (Hsem1 : L.Sem.sem_node G1 f ins outs) by exact (L.Norm.Correct.unnest_global_sem G Hwl Hpr f ins outs Hwt Hwc Hsem).
    assert (Hclk1 : L.ClSem.sem_clock_inputs G1 f ins) by exact (L.Norm.Correct.unnest_global_sem_clock_inputs G Hwl Hpr f ins Hclk).
    assert (Hsem2 := L.Norm.Correct.normfby_global_sem G1 Hunt Hpref1 f ins outs Hwt1 Hwc1
                       (L.Norm.Correct.wt_global_Ordered_nodes G1 Hwt1) Hcaus Hsem1 Hclk1).
    assert (Hclk2 := L.Norm.Correct.normfby_global_sem_clock_inputs G1 Hunt Hpref1 f ins Hclk1).
    eapply TR.Correctness.sem_l_nl; [| | | | | exact Htr | exact Hsem2 | exact Hclk2].
    - exact (NormFby.normfby_global_normalized_global G1 Hunt Hpref1).
    - exact (L.Norm.Correct.wt_global_Ordered_nodes _ (L.Norm.Correct.Typing.normfby_global_wt G1 Hunt Hpref1 Hwt1)).
    - exact (L.Norm.Correct.Causality.normfby_global_causal G1 Hunt Hpref1 Hwc1 Hcaus).
    - exact (L.Norm.Correct.Typing.normfby_global_wt G1 Hunt Hpref1 Hwt1).
    - exact (L.Norm.Correct.Clocking.normfby_global_wc G1 Hunt Hpref1 Hwc1).
  Qed.
  End SOURCE_RUN.

  Section FIND_NL.
  Import L.Norm.Norm.
  Lemma find_node_nl :
    forall G Hwl Hpr Hunt Hpref1 P Hp f n,
      L.Syn.find_node f G = Some n ->
      TR.Tr.to_global (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) Hp = OK P ->
      exists n', NL.Syn.find_node f P = Some n'
                 /\ NL.Syn.n_in n' = L.Syn.n_in n /\ NL.Syn.n_out n' = L.Syn.n_out n.
  Proof.
    intros G Hwl Hpr Hunt Hpref1 P Hp f n Hfind Htr.
    assert (Heq : L.Syn.global_iface_eq G (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1)).
    { etransitivity; [apply Unnesting.unnest_global_eq|apply NormFby.normfby_global_eq]. }
    eapply L.Syn.global_iface_eq_find in Hfind as (n' & Hfind' & (_ & _ & Hin & Hout)); [|exact Heq].
    eapply TR.Tr.find_node_global in Hfind' as (n'' & ? & Hfind'' & Htonode); eauto.
    exists n''. repeat split; auto.
    - eapply TR.Tr.to_node_in in Htonode; eauto. congruence.
    - eapply TR.Tr.to_node_out in Htonode; eauto. congruence.
  Qed.
  End FIND_NL.

  Lemma nl_run_history :
    forall P f ins outs,
      NL.CoindSem.sem_node P f ins outs ->
      exists n H,
        NL.Syn.find_node f P = Some n
        /\ CE.Sem.sem_vars H (List.map fst n.(NL.Syn.n_in)) (CIStr.tr_Streams ins)
        /\ CE.Sem.sem_vars H (List.map fst n.(NL.Syn.n_out)) (CIStr.tr_Streams outs)
        /\ Forall (NL.Sem.sem_equation P (CE.Sem.clock_of (CIStr.tr_Streams ins)) H)
                  n.(NL.Syn.n_eqs).
  Proof.
    intros P f ins outs Hnl.
    apply NL.CoindToIdx.implies in Hnl.
    inversion Hnl as [bk H f' xss yss n Hbk Hfind Hin Hout Hclocked Heqs].
    subst bk xss yss f'.
    exists n, H. repeat split; assumption.
  Qed.

  Definition stream_low_eq
    (ty_env : local_sec_env) (dlt : NI.ground_instantiation) (t : Lat.t)
    (xs : list ident) (xss xss' : IStr.stream (list OpAux.value)) : Prop :=
    forall k i x v v',
      nth_error xs i = Some x ->
      NI.low_var ty_env dlt t x ->
      nth_error (xss k) i = Some v ->
      nth_error (xss' k) i = Some v' ->
      v = v'.

  Lemma Forall2_nth_error' :
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
      NI.history_low_eq ty_env dlt t xs H H' ->
      CE.Sem.sem_vars H xs xss ->
      CE.Sem.sem_vars H' xs xss' ->
      stream_low_eq ty_env dlt t xs xss xss'.
  Proof.
    intros ty_env dlt t xs H H' xss xss' Hlow Hsem Hsem'
           k i x v v' Hnth Hlowx Hv Hv'.
    specialize (Hsem k). specialize (Hsem' k).
    unfold CE.Sem.sem_vars_instant in Hsem, Hsem'.
    assert (Hfx : IStr.sem_var_instant (H k) x v)
      by (eapply (Forall2_nth_error' (IStr.sem_var_instant (H k)) xs (xss k)); eauto).
    assert (Hfx' : IStr.sem_var_instant (H' k) x v')
      by (eapply (Forall2_nth_error' (IStr.sem_var_instant (H' k)) xs (xss' k)); eauto).
    unfold IStr.sem_var_instant in Hfx, Hfx'.
    assert (Hin : In x xs) by (eapply nth_error_In; eauto).
    specialize (Hlow k x Hin Hlowx).
    rewrite Hfx, Hfx' in Hlow. now inversion Hlow.
  Qed.

  Lemma nl_stream_ni :
    forall P envs aux G n ty_env nsig w t ins outs ins' outs',
      ConcreteNameGen.generate_node_scoped_env (rev P) = OK (envs, aux) ->
      NL.Ord.Ordered_nodes P ->
      NL.Clo.wc_global P ->
      C.SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK G ->
      NLCaus.nl_global_causal P ->
      NL.Syn.find_node n.(NL.Syn.n_name) P = Some n ->
      find_node_env n.(NL.Syn.n_name) envs = Some ty_env ->
      SIG.find_signature n.(NL.Syn.n_name) G = Some nsig ->
      NI.node_security P G envs aux n w w ->
      NL.CoindSem.sem_node P n.(NL.Syn.n_name) ins outs ->
      NL.CoindSem.sem_node P n.(NL.Syn.n_name) ins' outs' ->
      CE.Sem.clock_of (CIStr.tr_Streams ins) = CE.Sem.clock_of (CIStr.tr_Streams ins') ->
      stream_low_eq ty_env w t (List.map fst n.(NL.Syn.n_in))
        (CIStr.tr_Streams ins) (CIStr.tr_Streams ins') ->
      stream_low_eq ty_env w t (List.map fst n.(NL.Syn.n_out))
        (CIStr.tr_Streams outs) (CIStr.tr_Streams outs').
  Proof.
    intros P envs aux G n ty_env nsig w t ins outs ins' outs'
      Henv Hord Hwc Hgen Hcaus Hfn Hfenv Hfsig Hsec Hrun Hrun' Hclkeq Hlowin.
    destruct (nl_run_history _ _ _ _ Hrun) as (n1 & H & Hf1 & Hin & Hout & Heqs).
    destruct (nl_run_history _ _ _ _ Hrun') as (n2 & H' & Hf2 & Hin' & Hout' & Heqs').
    rewrite Hfn in Hf1. inversion Hf1; subst n1.
    rewrite Hfn in Hf2. inversion Hf2; subst n2.
    rewrite <- Hclkeq in Heqs'.
    assert (Hlowh : NI.history_low_eq ty_env w t (List.map fst n.(NL.Syn.n_in)) H H').
    { intros k x Hinx Hlowx.
      apply In_nth_error in Hinx as (i & Hnth).
      specialize (Hin k). specialize (Hin' k).
      unfold CE.Sem.sem_vars_instant in Hin, Hin'.
      destruct (nth_error (CIStr.tr_Streams ins k) i) as [v|] eqn:Ev.
      2:{ exfalso.
          apply nth_error_None in Ev. apply Forall2_length in Hin.
          assert (Hlt : i < length (List.map fst n.(NL.Syn.n_in)))
            by (apply nth_error_Some; rewrite Hnth; discriminate).
          rewrite Hin in Hlt. exact (PeanoNat.Nat.lt_irrefl _ (PeanoNat.Nat.le_lt_trans _ _ _ Ev Hlt)). }
      destruct (nth_error (CIStr.tr_Streams ins' k) i) as [v'|] eqn:Ev'.
      2:{ exfalso.
          apply nth_error_None in Ev'. apply Forall2_length in Hin'.
          assert (Hlt : i < length (List.map fst n.(NL.Syn.n_in)))
            by (apply nth_error_Some; rewrite Hnth; discriminate).
          rewrite Hin' in Hlt. exact (PeanoNat.Nat.lt_irrefl _ (PeanoNat.Nat.le_lt_trans _ _ _ Ev' Hlt)). }
      assert (Hfx : IStr.sem_var_instant (H k) x v)
        by (eapply (Forall2_nth_error' (IStr.sem_var_instant (H k))); eauto).
      assert (Hfx' : IStr.sem_var_instant (H' k) x v')
        by (eapply (Forall2_nth_error' (IStr.sem_var_instant (H' k))); eauto).
      unfold IStr.sem_var_instant in Hfx, Hfx'.
      rewrite Hfx, Hfx'. f_equal.
      eapply Hlowin; eauto. }
    assert (Hlowout : NI.history_low_eq ty_env w t (List.map fst n.(NL.Syn.n_out)) H H').
    { eapply (NI.node_noninterference_outputs P G envs aux n ty_env nsig w w t
                (CE.Sem.clock_of (CIStr.tr_Streams ins)) H H'); eauto. }
    eapply history_low_eq_streams; eauto.
  Qed.

  Section MAIN.
  Import L.Norm.Norm.
  Theorem lustre_noninterference :
    forall (G : L.Syn.global) (Hwl : L.Syn.wl_global G)
           (Hpr : Forall (fun n => L.Syn.n_prefixes n = Unnesting.elab_prefs) G)
           (Hunt : Unnesting.unnested_global (Unnesting.unnest_global G Hwl Hpr))
           (Hpref1 : Forall (fun n => L.Syn.n_prefixes n = NormFby.norm1_prefs)
                       (Unnesting.unnest_global G Hwl Hpr)),
      L.Clo.wc_global G -> L.Typ.wt_global G ->
      Forall L.Cau.node_causal (Unnesting.unnest_global G Hwl Hpr) ->
      forall envs aux stN st GS GT GM P Hp GN,
        ConcreteSecLNameGen.generate_lnode_scoped_env_st
          (rev (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1))
          = OK (envs, aux, stN) ->
        C.LegN.sec_le stN st ->
        L.Ord.Ordered_nodes
          (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env (rev G) envs aux
          st = OK GS ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env
          (rev (Unnesting.unnest_global G Hwl Hpr)) envs aux st = OK GT ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env
          (rev (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1))
          envs aux st = OK GM ->
        TR.Tr.to_global
          (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) Hp
          = OK P ->
        ConcreteNameGen.generate_node_scoped_env (rev P) = OK (envs, aux) ->
        NL.Ord.Ordered_nodes P ->
        NL.Clo.wc_global P ->
        C.SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK GN ->
        forall f nS sgS d1,
          L.Syn.find_node f G = Some nS ->
          SIG.find_signature f GS = Some sgS ->
          NI.signature_satisfied d1 sgS ->
          exists w,
            C.SecT.agree_on (SIG.signature_scope sgS) d1 w /\
            forall ty_env t ins outs ins' outs',
              find_node_env f envs = Some ty_env ->
              L.Sem.sem_node G f ins outs ->
              L.Sem.sem_node G f ins' outs' ->
              L.ClSem.sem_clock_inputs G f ins ->
              L.ClSem.sem_clock_inputs G f ins' ->
              CE.Sem.clock_of (CIStr.tr_Streams ins) = CE.Sem.clock_of (CIStr.tr_Streams ins') ->
              stream_low_eq ty_env w t (List.map fst nS.(L.Syn.n_in))
                (CIStr.tr_Streams ins) (CIStr.tr_Streams ins') ->
              stream_low_eq ty_env w t (List.map fst nS.(L.Syn.n_out))
                (CIStr.tr_Streams outs) (CIStr.tr_Streams outs').
  Proof.
    intros G Hwl Hpr Hunt Hpref1 Hwc Hwt Hcaus1 envs aux stN st GS GT GM P Hp GN
      Hnaming Hle Hord2 HgS HgT HgM Htr Hnames HordP HwcP HgN f nS sgS d1 Hfn HfS Hsat.
    set (G1 := Unnesting.unnest_global G Hwl Hpr) in *.
    assert (Hwt1 : L.Typ.wt_global G1) by exact (L.Norm.Correct.Typing.unnest_global_wt G Hwl Hpr Hwt).
    assert (Hwc1 : L.Clo.wc_global G1) by exact (L.Norm.Correct.Clocking.unnest_global_wc G Hwl Hpr Hwc).
    assert (Hwc2 : L.Clo.wc_global (NormFby.normfby_global G1 Hunt Hpref1))
      by exact (L.Norm.Correct.Clocking.normfby_global_wc G1 Hunt Hpref1 Hwc1).
    assert (Hcaus2 : Forall L.Cau.node_causal (NormFby.normfby_global G1 Hunt Hpref1))
      by exact (L.Norm.Correct.Causality.normfby_global_causal G1 Hunt Hpref1 Hwc1 Hcaus1).
    assert (HcausP : NLCaus.nl_global_causal P)
      by exact (CausBridge.to_global_causal _ P Hp Hwc2 Htr Hcaus2).
    (* the signature half *)
    pose proof (C.source_signatures_entail_nlustre G Hwl Hpr Hunt Hpref1 Hwc Hwt envs aux
                  stN st GS GT GM P Hp GN Hnaming Hle Hord2 HgS HgT HgM Htr Hnames HordP HwcP HgN)
      as Hent.
    destruct (C.source_policy_realised GS GN Hent f sgS HfS) as (sgN & HfN & Hpres).
    (* the node of the transcribed program *)
    destruct (find_node_nl G Hwl Hpr Hunt Hpref1 P Hp f nS Hfn Htr)
      as (n' & Hfn' & Hin & Hout).
    destruct (NL.Syn.find_node_In _ _ _ Hfn') as (Hname & HinP).
    assert (HinR : In n' (rev P)) by (apply (proj1 (in_rev _ _)); exact HinP).
    destruct (in_split _ _ HinR) as (pre & post & Hsplit).
    assert (HfN' : SIG.find_signature n'.(NL.Syn.n_name) GN = Some sgN) by (rewrite Hname; exact HfN).
    destruct (NS.policy_node_security P envs aux GN Hnames HordP HwcP HgN pre n' post Hsplit
                sgS sgN d1 HfN' Hpres Hsat) as (w & Hagree & Hsec).
    exists w. split; [exact Hagree|].
    intros ty_env t ins outs ins' outs' Hfenv Hrun Hrun' Hck Hck' Hclkeq Hlowin.
    assert (Hr : forall ins outs, L.Sem.sem_node G f ins outs ->
                   L.ClSem.sem_clock_inputs G f ins ->
                   NL.CoindSem.sem_node P n'.(NL.Syn.n_name) ins outs).
    { intros ins0 outs0 Hs Hc. rewrite Hname.
      exact (source_run_nl G Hwl Hpr Hunt Hpref1 P Hp f ins0 outs0 Hwt Hwc Hcaus1 Htr Hs Hc). }
    rewrite <- Hin in Hlowin. rewrite <- Hout.
    eapply (nl_stream_ni P envs aux GN n' ty_env sgN w t ins outs ins' outs');
      [exact Hnames|exact HordP|exact HwcP|exact HgN|exact HcausP|rewrite Hname; exact Hfn'
      |rewrite Hname; exact Hfenv|exact HfN'|exact Hsec
      |exact (Hr _ _ Hrun Hck)|exact (Hr _ _ Hrun' Hck')|exact Hclkeq|exact Hlowin].
  Qed.
  End MAIN.

End LusNI.
