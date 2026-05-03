(* Indexed-semantics observation layer for NLustre noninterference.

   This file starts the thesis-specific noninterference development on the
   source language side.  The first step is to formalise the paper's
   [(⊑ t)-projected Stream] notion directly over the indexed semantics used by
   Vélus:

   - raw program variables are observed through a generated local security env;
   - a ground instantiation assigns lattice classes to generated security ids;
   - projection keeps exactly those raw variables whose security class is at
     most the observation level [t].

   The later semantic theorems should be stated against the relational form
   [history_low_eq], while the concrete projector [project_history_le_t] keeps a
   paper-facing version of the same notion. *)

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
From Velus Require Import SIF.SecNLusNonInterferenceHelpers.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSNONINTERFERENCE
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
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
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
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING).

  (** Vocabulary alignment with the papers.

      The noninterference papers use:
      - [s] for a ground instantiation of symbolic security variables;
      - [ρ] for the generated constraints attached to a node signature.

      In the Coq development we standardise this as follows:
      - [dlt] is the ground instantiation used throughout [SecTypes] and
        [SIFSignature];
      - [sig.(s_constraints)] is exactly the paper's [ρ];
      - "ρ is satisfied by s" is formalised as [signature_satisfied dlt sig].

      Keeping this translation explicit avoids introducing parallel notation in
      the noninterference proof. *)


  Include SECNLUSNONINTERFERENCEHELPERS
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Successor-step transport of plain-call inputs from caller equality.

        Relation to the paper:
        in the successor [EqApp] case, the recursive callee theorem consumes
        low-equivalence on the callee inputs over the whole prefix.  This
        lemma packages exactly that caller-to-callee transport for ordinary
        calls, isolating the indexed actual-argument reasoning from the main
        causal induction. *)
    Theorem node_noninterference_outputs_raw:
      forall n dlt_sig dlt_raw,
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        node_outputs_raw_spec all_nodes G envs aux_names n dlt_sig dlt_raw.
    Proof.
      refine
        (fix IH n dlt_sig dlt_raw
             (Hsecure_cur : node_security all_nodes G envs aux_names n dlt_sig dlt_raw)
             {struct Hsecure_cur}
             : node_outputs_raw_spec all_nodes G envs aux_names n dlt_sig dlt_raw := _).
      destruct Hsecure_cur as
          [ty_env_sec sig_sec
           clk_id_sec rst_id_sec clk_type_sec rst_type_sec
           inp_sec out_sec locals_sec raw_sec st_n_sec
           Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
           Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
           Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
           Hcallsec_cur Hresetsec_cur].
      intros k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig Hsiggen
             Haux Hclk Hrst Hinp Hout Hlocals Hraw Hsigdef
             _ Hsatraw Hsem Hsem' Hlowin.
      assert (Hsecure_step :
                node_security all_nodes G envs aux_names n dlt_sig dlt_raw).
      {
        eapply SecureNode
          with (ty_env := ty_env_sec) (sig := sig_sec)
               (clk_id := clk_id_sec) (rst_id := rst_id_sec)
               (clk_type := clk_type_sec) (rst_type := rst_type_sec)
               (inp := inp_sec) (out := out_sec) (locals := locals_sec)
               (raw := raw_sec) (st_n := st_n_sec).
        - exact Hfindnode_sec.
        - exact Hfindenv_sec.
        - exact Hfindsig_sec.
        - exact Hsiggen_sec.
        - exact Haux_sec.
        - exact Hclk_sec.
        - exact Hrst_sec.
        - exact Hinp_sec.
        - exact Hout_sec.
        - exact Hlocals_sec.
        - exact Hraw_sec.
        - exact Hsigdef_sec.
        - exact Hsatsig_sec.
        - exact Hagree_sec.
        - exact Hsatraw_sec.
        - exact Hcallsec_cur.
        - exact Hresetsec_cur.
      }
      eapply history_low_eq_upto_weaken.
      - intros x Hinout.
        eapply Permutation_in.
        + exact (Permutation_sym n.(n_defd)).
        + rewrite map_app, in_app_iff.
          right.
          exact Hinout.
      - eapply node_noninterference_vars_defined_step with
            (sig := sig)
            (clk_id := clk_id)
            (rst_id := rst_id)
            (clk_type := clk_type)
            (rst_type := rst_type)
            (inp := inp)
            (out := out)
            (locals := locals)
            (raw := raw)
            (st_n := st_n)
            (bk := bk); eauto.
        + exact Hsecure_step.
        + intros xs ck f exps callee callee_sig
                 ckty inptyp outtyp st_clk st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hinp0 Hout0.
          eapply IH.
          eapply Hcallsec_cur; eauto.
        + intros xs ck f exps r ckr callee callee_sig
                 ckty rty rstty inptyp outtyp st_clk st_rst st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hrty Hrst0 Hinp0 Hout0
                 k_reset Hreset_ctrl.
          eapply IH.
          eapply Hresetsec_cur; eauto.
    Qed.

    (** Output-facing node noninterference theorem.

        Relation to the paper:
        this is the indexed-semantics analogue of the paper's NLustre
        noninterference theorem.  For now it is stated directly on the paired
        [node_security] predicate, so the replay witness [dlt_raw] remains
        explicit in the theorem statement while the proof architecture is
        still being settled. *)
    Theorem node_noninterference_outputs:
      forall n ty_env nsig dlt_sig dlt_raw t bk H H',
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SIG.find_signature n.(n_name) G = Some nsig ->
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq ty_env dlt_sig t (map fst n.(n_in)) H H' ->
        history_low_eq ty_env dlt_sig t (map fst n.(n_out)) H H'.
    Admitted.

  End GENERATED_NODE_NONINTERFERENCE.
End SECNLUSNONINTERFERENCE.

Module SecNLusNonInterference
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
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
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
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING)
  <: SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN
       SECCETYPING CETyp CEIsF CEClo Str Ord Mem IsD IsF NLCaus Clo CESem
       CEProps Indexed SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

Include SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CESyn SynNL SIG
  NAMEGEN SECCETYPING CETyp CEIsF CEClo Str Ord Mem IsD IsF NLCaus Clo CESem
  CEProps Indexed SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

End SecNLusNonInterference.
