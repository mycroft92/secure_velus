(** Final NLustre indexed noninterference result on observable node outputs. *)

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

  Include SECNLUSNONINTERFERENCECLOCKEDSTEP
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** This converts the packaged node-security assumptions into the raw output specification used by the final output theorem. *)
    Theorem node_noninterference_outputs_raw:
      forall n dlt_sig dlt_raw,
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        node_outputs_raw_spec_clocked all_nodes G envs aux_names n dlt_sig dlt_raw.
    Proof.
      intros n dlt_sig dlt_raw Hsecure.
      induction Hsecure.
      intros k ty_env' sig' t bk bk' Hhist Hhist'
             clk_id' rst_id' clk_type' rst_type'
             inp' out' locals' raw' st_n'
             Henvsgen' Hord' Hwcglob' Hallsig' Hcaus'
             Hfindnode' Hfindenv' Hfindsig' Hsiggen'
             Haux' Hclk' Hrst' Hinp' Hout' Hlocals' Hraw'
             Hsigdef' Hsecure' Hsatraw' Hsem_eq Hsem_eq' Hclock_eq Hlowin.
      assert (Htyenv_eq : ty_env' = ty_env) by congruence.
      assert (Hsig_eq : sig' = sig) by congruence.
      subst ty_env' sig'.
      eapply history_low_eq_upto_weaken.
      - intros x Hinx.
        match goal with
        | Hcur : find_node ?nd.(n_name) all_nodes = Some ?nd |- _ =>
            assert (Hin_vo : In x (map fst (nd.(n_vars) ++ nd.(n_out)))) by
              (rewrite map_app; apply in_or_app; now right);
            eapply Permutation_in; [apply Permutation_sym, nd.(n_defd)|exact Hin_vo]
        end.
      - eapply node_noninterference_vars_defined_step_mainline; eauto.
        + intros xs ck f exps callee callee_sig
                 ckty inptyp outtyp st_clk st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hinp0 Hout0.
          rewrite Hsig_eq in Hck0 |- *.
          match goal with
          | Hrec :
              forall (xs : list ident) (ck : clock) (f : ident)
                     (exps : list exp) (callee : node)
                     (callee_sig : signature) (ckty : SymTypes.ST)
                     (inptyp : list SymTypes.ST) (outtyp : list ident)
                     (st_clk st_inp : sec_state),
                In (EqApp xs ck f exps None) (n_eqs nd) ->
                find_node f all_nodes = Some callee ->
                find_signature f G = Some callee_sig ->
                option_to_sec (assign_clk_type ty_env (s_clk sig) ck)
                  SC.init_state = OK (ckty, st_clk) ->
                SC.mmap
                  (fun e : exp => option_to_sec (assign_exp_type ty_env e))
                  exps st_clk = OK (inptyp, st_inp) ->
                get_mappings xs ty_env = Some outtyp ->
                node_outputs_raw_spec_clocked all_nodes G envs aux_names
                  callee
                  (inst_valuation dlt_sig callee_sig inptyp ckty
                     [s_reset sig] outtyp)
                  (inst_valuation dlt_raw callee_sig inptyp ckty
                     [s_reset sig] outtyp) |- _ =>
              eapply Hrec; eauto
          end.
        + intros xs ck f exps r ckr callee callee_sig
                 ckty rty rstty inptyp outtyp st_clk st_rst st_inp
                 Heqin Hfindcallee Hfindsigc Hck0 Hr0 Hrst0 Hinp0 Hout0
                 k_reset Hreset_ctrl.
          rewrite Hsig_eq in Hck0, Hrst0.
          match goal with
          | Hrec :
              forall (xs : list ident) (ck : clock) (f : ident)
                     (exps : list exp) (r : ident) (ckr : clock)
                     (callee : node) (callee_sig : signature)
                     (ckty : SymTypes.ST) (rty : ident)
                     (rstty : SymTypes.ST) (inptyp : list SymTypes.ST)
                     (outtyp : list ident)
                     (st_clk st_rst st_inp : sec_state),
                In (EqApp xs ck f exps (Some (r, ckr))) (n_eqs nd) ->
                find_node f all_nodes = Some callee ->
                find_signature f G = Some callee_sig ->
                option_to_sec (assign_clk_type ty_env (s_clk sig) ck)
                  SC.init_state = OK (ckty, st_clk) ->
                Env.find r ty_env = Some rty ->
                option_to_sec (assign_clk_type ty_env (s_reset sig) ckr)
                  st_clk = OK (rstty, st_rst) ->
                SC.mmap
                  (fun e : exp => option_to_sec (assign_exp_type ty_env e))
                  exps st_rst = OK (inptyp, st_inp) ->
                get_mappings xs ty_env = Some outtyp ->
                node_outputs_raw_spec_clocked all_nodes G envs aux_names
                  callee
                  (inst_valuation dlt_sig callee_sig inptyp ckty
                     ([rty] ⊔ rstty) outtyp)
                  (inst_valuation dlt_raw callee_sig inptyp ckty
                     ([rty] ⊔ rstty) outtyp) |- _ =>
              eapply Hrec; eauto
          end.
    Qed.

    (** This is the main NLustre noninterference theorem.  For a generated node signature, a source security witness, and two executions with low-equivalent inputs, it proves that the observable outputs agree at every allowed security level.  The translated STC theorem later reuses this result through the source-to-target bridge instead of reproving noninterference directly on STC. *)
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
    Proof.
      intros n ty_env nsig dlt_sig dlt_raw t bk H H'
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig Hsecure Hsem Hsem' Hlowin.
      inversion Hsecure as
        [ty_env_sec sig
         clk_id rst_id clk_type rst_type inp out locals raw st_n
         Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen
         Haux Hclk Hrst Hinp Hout Hlocals Hraw
         Hsigdef Hsatsig Hagree Hsatraw Hcallsec Hresetsec].
      assert (Htyenv_eq : ty_env_sec = ty_env) by congruence.
      assert (Hsig_eq : sig = nsig) by congruence.
      assert (Hsigdef_nsig :
                nsig =
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}).
      {
        rewrite <- Hsig_eq.
        exact Hsigdef.
      }
      subst ty_env_sec sig.
      assert (Hscope_in :
                forall x, In x (map fst n.(n_in)) ->
                  exists alpha,
                    Env.find x ty_env = Some alpha /\ In alpha (signature_scope nsig)).
      {
        intros x Hin.
        pose proof (get_mappings_from_node_eq _ _ _ _ Hinp) as Hinp_eq.
        destruct (get_mappings_in _ _ _ _ Hin Hinp_eq)
          as (alpha & Hfind & Hinalpha).
        exists alpha.
        split; [exact Hfind|].
        unfold signature_scope.
        rewrite <- Hsig_eq.
        simpl.
        repeat rewrite in_app_iff.
        left.
        exact Hinalpha.
      }
      assert (Hscope_out :
                forall x, In x (map fst n.(n_out)) ->
                  exists alpha,
                    Env.find x ty_env = Some alpha /\ In alpha (signature_scope nsig)).
      {
        intros x Hin.
        pose proof (get_mappings_from_node_eq _ _ _ _ Hout) as Hout_eq.
        destruct (get_mappings_in _ _ _ _ Hin Hout_eq)
          as (alpha & Hfind & Hinalpha).
        exists alpha.
        split; [exact Hfind|].
        unfold signature_scope.
        rewrite <- Hsig_eq.
        simpl.
        repeat rewrite in_app_iff.
        right.
        left.
        exact Hinalpha.
      }
      assert (Hagree_nsig : agree_on (signature_scope nsig) dlt_sig dlt_raw).
      {
        rewrite <- Hsig_eq.
        exact Hagree.
      }
      assert (Hsiggen_nsig :
                SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK nsig).
      {
        rewrite Hsigdef_nsig.
        exact Hsiggen.
      }
      assert (Hlowin_raw :
                history_low_eq ty_env dlt_raw t (map fst n.(n_in)) H H').
      {
        eapply (history_low_eq_agree_on_scope
                  ty_env t (map fst n.(n_in)) (signature_scope nsig)
                  dlt_sig dlt_raw H H').
        - exact Hscope_in.
        - exact Hagree_nsig.
        - exact Hlowin.
      }
      assert (Hlowout_raw :
                history_low_eq ty_env dlt_raw t (map fst n.(n_out)) H H').
      {
        apply history_low_eq_from_Forall_pointwise.
        apply Forall_forall.
        intros x Hinx Hlowx k.
        specialize
          (node_noninterference_outputs_raw n dlt_sig dlt_raw Hsecure
             k ty_env nsig t bk bk H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig Hsiggen_nsig
             Haux Hclk Hrst Hinp Hout Hlocals Hraw
             Hsigdef_nsig Hsecure Hsatraw Hsem Hsem'
             (clock_eq_upto_refl bk k)
             (history_low_eq_upto_of_history_low_eq
                ty_env dlt_raw t (map fst n.(n_in)) H H' k Hlowin_raw))
          as Hk.
        specialize (Hk k (Nat.le_refl k)).
        eapply Hk; eauto.
      }
      eapply (history_low_eq_agree_on_scope
                ty_env t (map fst n.(n_out)) (signature_scope nsig)
                dlt_raw dlt_sig H H').
      - exact Hscope_out.
      - eapply agree_on_sym; exact Hagree_nsig.
      - exact Hlowout_raw.
    Qed.

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
