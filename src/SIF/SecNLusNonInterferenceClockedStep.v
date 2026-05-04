(* Clock-aware step theorems for NLustre indexed noninterference.

   The papers' node-level noninterference argument is organized around one
   equation-step theorem.  This file contains the finalized clock-aware version
   used by the reset-sensitive development: the current node may run under two
   base clocks that agree on the observed prefix, while recursive calls still
   reuse the one-node helper infrastructure from
   [SecNLusNonInterferenceHelpers]. *)

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

Module Type SECNLUSNONINTERFERENCECLOCKEDSTEP
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

  Include SECNLUSNONINTERFERENCEHELPERS
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS
    SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

  Section GENERATED_NODE_NONINTERFERENCE_CLOCKED_STEP.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Instantaneous [EqDef] noninterference with distinct ambient clocks.

        Relation to the paper:
        the paper's indexed proof only needs the current instant of a simple
        definition equation.  Once the two runs are allowed to have different
        ambient base clocks, the local semantic bridge needs exactly one extra
        premise: equality of those base clocks at the current instant. *)
    Lemma eqdef_noninterference_instant_pointwise_clocked:
      forall bk bk' H H' x xs xs' ck ce k,
        (forall y, Is_free_in_caexp y ck ce ->
             Env.find y (H k) = Env.find y (H' k)) ->
        bk k = bk' k ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk' H' ck ce xs' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk bk' H H' x xs xs' ck ce k
             Hdep Hbk_eq Hvar Hrhs Hvar' Hrhs'.
      specialize (Hvar k).
      specialize (Hrhs k).
      specialize (Hvar' k).
      specialize (Hrhs' k).
      rewrite <- Hbk_eq in Hrhs'.
      assert (Hrhs_sw : sem_caexp_instant (bk k) (H' k) ck ce (xs k)).
      {
        apply
          (proj1
             (sem_caexp_instant_switch_env
                (bk k) (H k) (H' k) ck ce (xs k)
                (fun y Hy =>
                   match Hy with
                   | or_introl Hyck => Hdep y (FreeCAexp2 _ _ _ Hyck)
                   | or_intror Hyce => Hdep y (FreeCAexp1 _ _ _ Hyce)
                   end))).
        exact Hrhs.
      }
      assert (Hxs : xs k = xs' k).
      { eapply sem_caexp_instant_det; eauto. }
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** Prefix preservation for guarded source expressions under two ambient clocks.

        Relation to the paper:
        delayed equations only read the payload of their source expression on
        the earlier prefix.  In the two-clock setting, that prefix transport
        additionally needs equality of the ambient clocks on the same prefix. *)
    Lemma sem_aexp_prefix_eq_clocked:
      forall bk bk' H H' ck e ls ls' k,
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        (forall j, j < k -> bk j = bk' j) ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk' H' ck e ls' ->
        forall j, j < k -> ls j = ls' j.
    Proof.
      intros bk bk' H H' ck e ls ls' k Hdep Hbk Hsem Hsem' j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
      rewrite <- (Hbk j Hj) in Hsem'.
      assert (Hsw : sem_aexp_instant (bk j) (H' j) ck e (ls j)).
      {
        apply
          (proj1
             (sem_aexp_instant_switch_env
                (bk j) (H j) (H' j) ck e (ls j)
                (fun y Hy =>
                   match Hy with
                   | or_introl Hyck => Hdep y (freeAexp2 _ _ _ Hyck) j Hj
                   | or_intror Hye => Hdep y (freeAexp1 _ _ _ Hye) j Hj
                   end))).
        exact Hsem.
      }
      eapply sem_aexp_instant_det; eauto.
    Qed.

    (** Current-presence preservation for guarded source expressions under two ambient clocks.

        Relation to the paper:
        the delayed case only needs the current presence/absence bit of the
        feeding expression.  With distinct ambient clocks, current presence is
        still determined once the source clock dependencies agree and the two
        ambient clocks are equal at that instant. *)
    Lemma sem_aexp_same_presence_from_clock_clocked:
      forall bk bk' H H' ck e ls ls' k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        bk k = bk' k ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk' H' ck e ls' ->
        (ls k = absent <-> ls' k = absent).
    Proof.
      intros bk bk' H H' ck e ls ls' k Hdep Hbk_eq Hsem Hsem'.
      specialize (Hsem k).
      specialize (Hsem' k).
      rewrite <- Hbk_eq in Hsem'.
      assert (Hclk_sw :
                forall b,
                  sem_clock_instant (bk k) (H k) ck b
                  <-> sem_clock_instant (bk k) (H' k) ck b).
      {
        intro b.
        apply sem_clock_instant_switch_env.
        exact Hdep.
      }
      destruct (ls k) eqn:Hlk, (ls' k) eqn:Hlk'; split; intro Hab; try reflexivity;
        try congruence.
      - pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem) as Hf.
        pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem') as Ht.
        pose proof (proj1 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
      - pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem) as Ht.
        pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem') as Hf.
        pose proof (proj2 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
    Qed.

    (** Delayed [EqFby] noninterference under two ambient clocks.

        Relation to the paper:
        this is the delayed equation step needed by the two-clock current-node
        theorem.  The current instant consumes equality of the source clock and
        of the ambient clocks, while the delayed payload still only depends on
        the earlier prefix. *)
    Lemma eqfby_noninterference_delayed_pointwise_clocked:
      forall bk bk' H H' x xs xs' ls ls' ck c0 e k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        (forall j, j < k -> bk j = bk' j) ->
        bk k = bk' k ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk' H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk bk' H H' x xs xs' ls ls' ck c0 e k
             Hclock Hpast Hbk_prefix Hbk_cur
             Hvar Hrhs Hfby Hvar' Hrhs' Hfby'.
      assert (Hls_prefix : forall j, j < k -> ls j = ls' j).
      { eapply sem_aexp_prefix_eq_clocked; eauto. }
      assert (Hls_abs : ls k = absent <-> ls' k = absent).
      { eapply sem_aexp_same_presence_from_clock_clocked; eauto. }
      assert (Hxs_k : xs k = xs' k).
      {
        rewrite Hfby, Hfby'.
        eapply fby_eq_delay_prefix; eauto.
      }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs_k in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    (** One non-reset call input is low-equal under two ambient clocks.

        Relation to the paper:
        recursive calls evaluate their actual expressions in the caller.  The
        two-clock current-node theorem therefore needs the expression-transport
        step to account for potentially different ambient clocks on the two
        caller runs, but only at the observed instant. *)
    Lemma eqapp_input_var_low_eq_pointwise_clocked:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk bk' H H' Hc Hc' exps ls ls'
             k ii y ity e ety,
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        bk k = bk' k ->
        sem_exps bk H exps ls ->
        sem_exps bk' H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk bk' H H' Hc Hc' exps ls ls'
             k ii y ity e ety
             Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq Hbk_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk' k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      rewrite <- Hbk_eq in Hsemv'.
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hnthv in Hnthvin.
      inversion Hnthvin; subst vin; clear Hnthvin.
      rewrite Hnthv' in Hnthvin'.
      inversion Hnthvin'; subst vin'; clear Hnthvin'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** One reset-call input is low-equal under two ambient clocks.

        Relation to the paper:
        this is the reset-aware companion of the previous lemma.  The caller
        still evaluates the actual expressions under its own ambient clock, so
        the only extra ingredient beyond the older proof is equality of the
        two ambient clocks at the observed instant. *)
    Lemma eqapp_reset_input_var_low_eq_pointwise_clocked:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk bk' H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        bk k = bk' k ->
        sem_exps bk H exps ls ->
        sem_exps bk' H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk bk' H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety
             Hkr Hkr' Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq Hbk_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk' k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      rewrite <- Hbk_eq in Hsemv'.
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (mask kr rs ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (mask kr' rs' ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hkr in Hnthvin.
      rewrite Hkr' in Hnthvin'.
      pose proof
        (nth_error_mask_count_self rs ls k ii vin Hnthvin)
        as Hnthvin0.
      pose proof
        (nth_error_mask_count_self rs' ls' k ii vin' Hnthvin')
        as Hnthvin0'.
      rewrite Hnthv in Hnthvin0.
      inversion Hnthvin0; subst vin; clear Hnthvin0.
      rewrite Hnthv' in Hnthvin0'.
      inversion Hnthvin0'; subst vin'; clear Hnthvin0'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** Successor-step transport of non-reset call inputs under two ambient clocks.

        Relation to the paper:
        this is the successor indexed-input transport used at recursive plain
        calls, but strengthened to compare caller runs that may have different
        ambient clocks agreeing only on the observed prefix. *)
    Lemma succ_eqapp_nonreset_inputs_low_eq_upto_clocked:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk bk'
             xh xt ck callee exps x k
             inp_c inptyp outtyp ckty rstty callee_sig ls ls',
        Clo.wc_node P n ->
        In (EqApp (xh :: xt) ck callee.(n_name) exps None) n.(n_eqs) ->
        In x (xh :: xt) ->
        (forall y,
            NLCaus.nl_depends_on_eq
              (EqApp (xh :: xt) ck callee.(n_name) exps None) x y ->
            low_var ty_env dlt_raw obs y ->
            Env.find y (H (S k)) = Env.find y (H' (S k))) ->
        history_low_eq_upto ty_env dlt_raw obs (map fst (n_in n)) H H' (S k) ->
        history_low_eq_upto ty_env dlt_raw obs (vars_defined (n_eqs n)) H H' k ->
        clock_eq_upto bk bk' (S k) ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt_raw ty)
          callee_sig.(s_in) inptyp ->
        sem_exps bk H exps ls ->
        sem_exps bk' H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk bk'
             xh xt ck callee exps x k
             inp_c inptyp outtyp ckty rstty callee_sig ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev Hclock_eq
             Hsig_in Hinp_c Hforinp Hinst_in_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthety & Heqexp).
      assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ obs).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt_raw ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthety.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthety in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      assert (Hfree_eq :
                forall z,
                  Is_free_in_exp z e ->
                  Env.find z (H j) = Env.find z (H' j)).
      {
        intros z Hz.
        assert (Hlowz : low_var ty_env dlt_raw obs z).
        {
          refine
            (exp_type_low
               ty_env dlt_raw obs e ety z _ _ _).
          - exact Heqexp.
          - exact Hety_low.
          - exact Hz.
        }
        assert (Hzs : Exists (Is_free_in_exp z) exps).
        {
          eapply Exists_exists.
          exists e.
          split; [eapply nth_error_In; exact Hnthe|exact Hz].
        }
        destruct
          (free_exp_in_inputs_or_defined
             P n (xh :: xt) ck callee.(n_name) exps None z
             Hwcnode Heqin Hzs)
          as [Hin_z|Hdef_z].
        - eapply Hlowin; eauto.
        - destruct (Nat.eq_dec j (S k)) as [Heqj|Hneqj].
          + subst j.
            assert (Hdep_xz :
                      NLCaus.nl_depends_on_eq
                        (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
            {
              split; [exact Hxdef|].
              eapply nth_error_free_in_aexps; eauto.
            }
            exact (Hdeps z Hdep_xz Hlowz).
          + eapply Hprev; eauto. lia.
      }
      eapply
        (eqapp_input_var_low_eq_pointwise_clocked
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt_raw rstty ckty obs
           bk bk' H H' Hc Hc' exps ls ls'
           j ii y ity e ety).
      - exact Hnthy.
      - exact Hfindy.
      - exact Hnthsig.
      - exact Hnthety.
      - exact Hnthe.
      - exact Heqexp.
      - exact Hinst_in_eq.
      - exact Hlowy.
      - exact Hfree_eq.
      - exact (Hclock_eq j Hj).
      - exact Hsem_exps.
      - exact Hsem_exps'.
      - exact Hsem_vars_in_c.
      - exact Hsem_vars_in_c'.
    Qed.

    (** Successor-step transport of reset-call inputs under two ambient clocks.

        Relation to the paper:
        this is the reset-aware companion of the previous lemma.  The only
        semantic strengthening is the explicit caller-clock prefix premise used
        when the active reset segment is observed on both runs. *)
    Lemma succ_eqapp_reset_inputs_low_eq_upto_clocked:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk bk'
             xh xt ck callee exps r ckr x k
             inp_c inptyp outtyp ckty rstty callee_sig
             rs rs' kr kr' ls ls',
        Clo.wc_node P n ->
        In (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) n.(n_eqs) ->
        In x (xh :: xt) ->
        (forall y,
            NLCaus.nl_depends_on_eq
              (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x y ->
            low_var ty_env dlt_raw obs y ->
            Env.find y (H (S k)) = Env.find y (H' (S k))) ->
        history_low_eq_upto ty_env dlt_raw obs (map fst (n_in n)) H H' (S k) ->
        history_low_eq_upto ty_env dlt_raw obs (vars_defined (n_eqs n)) H H' k ->
        clock_eq_upto bk bk' (S k) ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt_raw ty)
          callee_sig.(s_in) inptyp ->
        kr = count rs (S k) ->
        kr' = count rs' (S k) ->
        (forall j, j <= S k -> count rs j = count rs' j) ->
        sem_exps bk H exps ls ->
        sem_exps bk' H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk bk'
             xh xt ck callee exps r ckr x k
             inp_c inptyp outtyp ckty rstty callee_sig
             rs rs' kr kr' ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev Hclock_eq
             Hsig_in Hinp_c Hforinp Hinst_in_eq
             Hkr Hkr' Hcount_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthety & Heqexp).
      assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ obs).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt_raw ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthety.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthety in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      assert (Hfree_eq :
                forall z,
                  Is_free_in_exp z e ->
                  Env.find z (H j) = Env.find z (H' j)).
      {
        intros z Hz.
        assert (Hlowz : low_var ty_env dlt_raw obs z).
        {
          refine
            (exp_type_low
               ty_env dlt_raw obs e ety z _ _ _).
          - exact Heqexp.
          - exact Hety_low.
          - exact Hz.
        }
        assert (Hzs : Exists (Is_free_in_exp z) exps).
        {
          eapply Exists_exists.
          exists e.
          split; [eapply nth_error_In; exact Hnthe|exact Hz].
        }
        destruct
          (free_exp_in_inputs_or_defined
             P n (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) z
             Hwcnode Heqin Hzs)
          as [Hin_z|Hdef_z].
        - eapply Hlowin; eauto.
        - destruct (Nat.eq_dec j (S k)) as [Heqj|Hneqj].
          + subst j.
            assert (Hdep_xz :
                      NLCaus.nl_depends_on_eq
                        (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
            {
              split; [exact Hxdef|].
              left.
              eapply nth_error_free_in_aexps; eauto.
            }
            exact (Hdeps z Hdep_xz Hlowz).
          + eapply Hprev; eauto. lia.
      }
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq (S k) (le_n (S k))) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        eapply
          (eqapp_reset_input_var_low_eq_pointwise_clocked
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt_raw rstty ckty obs
             bk bk' H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety).
        + symmetry; exact Hactive.
        + symmetry; exact Hactive'.
        + exact Hnthy.
        + exact Hfindy.
        + exact Hnthsig.
        + exact Hnthety.
        + exact Hnthe.
        + exact Heqexp.
        + exact Hinst_in_eq.
        + exact Hlowy.
        + exact Hfree_eq.
        + exact (Hclock_eq j Hj).
        + exact Hsem_exps.
        + exact Hsem_exps'.
        + exact Hsem_vars_in_c.
        + exact Hsem_vars_in_c'.
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq (S k) (le_n (S k))) as Hcntk.
          apply Hopaque.
          rewrite Hcntj.
          rewrite Heq.
          rewrite Hkr'.
          rewrite <- Hcntk.
          symmetry.
          exact Hkr.
        }
        specialize (Hsem_vars_in_c j).
        specialize (Hsem_vars_in_c' j).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc j))
             (map fst callee.(n_in)) (mask kr rs ls j) ii y
             Hsem_vars_in_c Hnthy)
          as (vin & Hnthvin & Hsem_y).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc' j))
             (map fst callee.(n_in)) (mask kr' rs' ls' j) ii y
             Hsem_vars_in_c' Hnthy)
          as (vin' & Hnthvin' & Hsem_y').
        rewrite (mask_opaque ls kr rs j Hopaque) in Hnthvin.
        rewrite (mask_opaque ls' kr' rs' j Hopaque') in Hnthvin'.
        pose proof (nth_error_all_absent_absent _ (ls 0) _ _ Hnthvin) as Hvin.
        pose proof (nth_error_all_absent_absent _ (ls' 0) _ _ Hnthvin') as Hvin'.
        unfold sem_var_instant in Hsem_y, Hsem_y'.
        subst vin vin'.
        rewrite Hsem_y, Hsem_y'.
        reflexivity.
    Qed.

    (** Mainline base case of the clocked current-node step theorem.

        Relation to the paper:
        the public noninterference theorem compares two indexed runs.  The
        final internal step theorem must therefore allow different ambient
        clocks already at the current node, with an explicit prefix-alignment
        premise [clock_eq_upto bk bk' 0].  This theorem is the designated
        base-case entry point for that two-clock route. *)
    Theorem node_noninterference_vars_defined_step_base_mainline :
      forall n dlt_sig dlt_raw
             ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SIG.find_signature n.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := n.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        (forall xs ck f exps callee callee_sig
                ckty inptyp outtyp st_clk st_inp,
            In (EqApp xs ck f exps None) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_clk = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            node_outputs_raw_spec_clocked all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)) ->
        (forall xs ck f exps r ckr callee callee_sig
                ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
            In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            Env.find r ty_env = Some rty ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_reset) ckr)
              st_clk = OK (rstty, st_rst) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_rst = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            forall k_reset,
              reset_control_low_eq_upto ty_env dlt_raw t r H H' k_reset ->
            node_outputs_raw_spec_clocked all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)) ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') n.(n_eqs) ->
        clock_eq_upto bk bk' 0 ->
        history_low_eq_upto ty_env dlt_raw t (map fst n.(n_in)) H H' 0 ->
        history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' 0.
    Proof.
      intros n dlt_sig dlt_raw
             ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hord Hwcglob Hallsig Hcaus Hfindnode Hfindenv
             Hfindsig Hsiggen Haux Hclk Hrst Hinp Hout Hlocals Hraw
             Hsigdef Hsecure Hcallout Hresetout Hsatraw Hsem Hsem' Hclock_eq Hlowin.
      assert
        (Hpts :
           Forall
             (fun x =>
                low_var ty_env dlt_raw t x ->
                forall j, j <= 0 -> Env.find x (H j) = Env.find x (H' j))
             (vars_defined n.(n_eqs))).
      {
        pose proof (Ordered_nodes_nodup_names _ Hord) as Hndnames.
        destruct Hsecure as
            [ty_env_sec sig_sec
             clk_id_sec rst_id_sec clk_type_sec rst_type_sec
             inp_sec out_sec locals_sec raw_sec st_n_sec
             Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
             Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
             Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
             Hcallsec_cur Hresetsec_cur].
        rewrite Hfindenv in Hfindenv_sec.
        inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
        rewrite Hfindsig in Hfindsig_sec.
        inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
        rewrite <- H1 in Hcallsec_cur, Hresetsec_cur, Hsatsig_sec, Hagree_sec.
        rewrite Hsigdef in Hcallsec_cur, Hresetsec_cur, Hcallout, Hresetout.
        pose proof Hcallsec_cur as Hcallsec_node.
        pose proof Hresetsec_cur as Hresetsec_node.
        eapply nl_node_causal_ind_defined.
        + intros eq x Heqin Hxdef Hdeps Hlowx j Hj.
          assert (Hj0 : j = 0) by lia.
          subst j.
          destruct eq as [x0 ck ce|xs ck f exps r|x0 ck c0 e];
            simpl in Hxdef.
          * assert (Hx : x = x0).
            { simpl in Hxdef. intuition. }
            subst x.
            assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqDef x0 ck ce)).
            { eapply Forall_forall; eauto. }
            assert (Hsem_eq' : Indexed.sem_equation all_nodes bk' H' (EqDef x0 ck ce)).
            { eapply Forall_forall; eauto. }
            inversion Hsem_eq; subst; clear Hsem_eq.
            inversion Hsem_eq'; subst; clear Hsem_eq'.
            destruct
              (generate_eqns_constraints_member G
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqDef x0 ck ce) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqdef_constraint_inv G
                 ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
              as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
            assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
            {
              rewrite Hcns in Hmid.
              inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
              inversion Hnil; subst; clear Hnil.
              exact Hsat_ceq.
            }
            refine
              (eqdef_noninterference_instant_pointwise_clocked
                 bk bk' H H' x0 xs xs0 ck ce 0 _ _ _ _ _ _).
            - intros y Hfree.
              assert (Hlowy : low_var ty_env dlt_raw t y).
              {
                eapply simple_security_caexp; eauto.
              }
              assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
              { split; [reflexivity|exact Hfree]. }
              specialize (Hdeps y Hdep_xy Hlowy 0 (le_n 0)).
              exact Hdeps.
            - exact (Hclock_eq 0 (le_n 0)).
            - eassumption.
            - eassumption.
            - eassumption.
            - eassumption.
          * destruct xs as [|xh xt].
            { simpl in Hxdef. contradiction. }
            destruct r as [[r ckr]|].
            2:{
               assert (Hsem_eq :
                         Indexed.sem_equation all_nodes bk H
                           (EqApp (xh :: xt) ck f exps None)).
               { eapply Forall_forall; eauto. }
               assert (Hsem_eq' :
                         Indexed.sem_equation all_nodes bk' H'
                           (EqApp (xh :: xt) ck f exps None)).
               { eapply Forall_forall; eauto. }
               destruct
                 (generate_eqns_constraints_member G
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqapp_constraint_inv G
                    ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                 as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                     & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
               destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
               destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                 as (xty0 & Hnthout & Hfindx0).
               destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                 as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
               destruct (sem_eqapp_inv all_nodes bk' H' (xh :: xt) ck f exps Hsem_eq')
                 as (ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock' & Hsem_node_c').
               destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c)
                 as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                     & Hsem_vars_in_c & Hsem_vars_callee_out
                     & Hsem_clocked_c & Hsem_eqs_c).
               destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c')
                 as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                     & Hsem_vars_in_c' & Hsem_vars_callee_out'
                     & Hsem_clocked_c' & Hsem_eqs_c').
               assert (Hcallee_eq : callee' = callee)
                 by (eapply find_node_unique_nodup;
                     [eapply Ordered_nodes_nodup_names; exact Hord
                     |exact Hfindcallee'
                     |exact Hfindcallee]).
               subst callee'.
               assert (Hneqf : f <> n.(n_name)).
               {
                 intro Heqf.
                 eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                 eapply Exists_exists.
                 exists (EqApp (xh :: xt) ck f exps None).
                 split; [exact Heqin|].
                 subst f.
                 constructor.
               }
               assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
               {
                 intro Heq.
                 apply Hneqf.
                 rewrite Heq.
                 symmetry.
                 exact (proj1 (find_node_In _ _ _ Hfindcallee)).
               }
               assert (Hck0_init :
                         SC.option_to_sec
                           (SECCETYPING.assign_clk_type ty_env clk_type ck)
                           SC.init_state = OK (ckty0, SC.init_state)).
               {
                 eapply option_to_sec_assign_clk_state_irrel.
                 exact Hck0.
               }
               assert (Hinp0_init :
                         SC.mmap
                           (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                           exps SC.init_state = OK (inptyp0, SC.init_state)).
               {
                 eapply mmap_assign_exp_type_state_irrel.
                 exact Hinp0.
               }
               pose proof
                (Hcallsec_node
                    (xh :: xt) ck f exps callee nsig_c
                    ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                    Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                 as Hcallee_secure.
               destruct Hcallee_secure as
                   [ty_env_c sig_c
                    clk_id_c rst_id_c clk_type_c rst_type_c
                    inp_c out_c locals_c raw_c st_n_c
                    Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                    Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                    Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                    Hcallsec_c Hresetsec_c].
               pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
               rewrite Hcallee_name in Hfindsig_c.
               rewrite Hfindsigc in Hfindsig_c.
               assert (Hsig_eq : nsig_c = sig_c).
               { inversion Hfindsig_c; reflexivity. }
               subst nsig_c.
               pose
                 (callee_sig_cur :=
                    {| s_name := callee.(n_name);
                       s_in := inp_c;
                       s_out := out_c;
                       s_reset := rst_type_c;
                       s_clk := clk_type_c;
                       s_constraints := SymTypes.simplify raw_c locals_c |}).
               rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                 Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
               set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
               set (dlt_sig_c :=
                      SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                        [rst_type] outtyp0).
               set (dlt_raw_c :=
                      SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                        [rst_type] outtyp0).
               destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
                 as [P Hwcnode].
               destruct Hwcnode as [_ [_ [Hwcenv Hwc_eqs]]].
               assert (Hwcapp :
                         Clo.wc_equation P
                           (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                           (EqApp (xh :: xt) ck f exps None)).
               {
                 rewrite Forall_forall in Hwc_eqs.
                 exact (Hwc_eqs _ Heqin).
               }
               inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                     Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
               assert
                 (Hvars_scoped :
                    SECNLUSTYPING.vars_env_scoped ty_env
                      (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                      caller_scope).
               {
                 eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                   eauto.
               }
               assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
               {
                 eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                   with (scope := caller_scope)
                        (es := exps)
                        (st := SC.init_state)
                        (st' := SC.init_state); eauto.
                 eapply SECNLUSTYPING.wc_call_args_scoped
                   with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        (scope := caller_scope)
                        (sub := sub)
                        (ck := ck)
                        (ins := n0.(n_in)); eauto.
               }
               assert
                 (Hfree_clock_scope :
                    forall z,
                      Is_free_in_clock z ck ->
                      exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
               {
                 intros z Hz.
                 destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                 { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                 exists ty0; split; [exact Hfindz|exact Hinscope].
               }
               assert
                 (Hassign_ck :
                    SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
               {
                 unfold SC.option_to_sec in Hck0_init.
                 destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                   eqn:Hassign; simpl in Hck0_init; try discriminate.
                 inversion Hck0_init; now subst ckty'.
               }
               assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
               {
                 eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                 - simpl. repeat (apply in_or_app; right).
                   simpl. now left.
                 - exact Hfree_clock_scope.
                 - exact Hassign_ck.
               }
               assert (Hrst_scope : SecT.st_scoped caller_scope [rst_type]).
               {
                 simpl.
                 apply SecT.st_scoped_singleton.
                 repeat (apply in_or_app; right).
                 simpl. now right; left.
               }
               assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
               {
                 rewrite Forall_forall.
                 intros ty Hty.
                 pose proof
                   (eqapp_outtyp_in_out_or_locals
                      n ty_env out locals (xh :: xt) ck callee.(n_name) exps None outtyp0 ty
                      Heqin Hout0 Hout Hlocals Hty)
                   as Hin_out_or_locals.
                 replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                 - apply in_or_app. right.
                   eapply In_app_weaken_right.
                   exact Hin_out_or_locals.
                 - unfold caller_scope.
                   repeat rewrite <- app_assoc.
                   reflexivity.
               }
               assert (Hscopefresh :
                         SIG.scope_fresh caller_scope callee_sig_cur).
               {
                 eapply generated_caller_scope_fresh_scoped_env
                   with (caller := n)
                        (callee := callee)
                        (caller_env := ty_env)
                        (callee_env := ty_env_c)
                        (clk_id := clk_id)
                        (rst_id := rst_id)
                        (clk_type := clk_type)
                        (rst_type := rst_type)
                        (inp := inp)
                        (out := out)
                        (locals := locals); eauto.
               }
               assert (Hndscope_c :
                         NoDup (SIG.signature_scope callee_sig_cur)).
               {
                 eapply generated_sig_scope_nodup_scoped_env
                   with (n := callee)
                        (ty_env := ty_env_c)
                        (clk_id := clk_id_c)
                        (rst_id := rst_id_c)
                        (clk_type := clk_type_c)
                        (rst_type := rst_type_c)
                        (inp := inp_c)
                        (out := out_c); eauto.
               }
               assert (Hfresh_call :
                         SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0).
               {
                 eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
               }
               pose proof
                 (generate_constraints_lengths
                    callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                    ceq st_inp0 stceq Hcallc)
                 as [Hlen_in_c Hlen_out_c].
               destruct
                 (mmap_assign_exp_type_inv ty_env exps inptyp0 st_clk0 st_inp0 Hinp0)
                 as [_ Hforinp0].
               pose proof
                 (SIGPROOFS.inst_valuation_inputs_eq
                    dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                    Hfresh_call Hndscope_c Hlen_in_c)
                 as Hinst_in_eq.
               pose proof
                 (SIGPROOFS.inst_valuation_outputs_eq
                    dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                    Hfresh_call Hndscope_c Hlen_out_c)
                 as Hinst_out_eq.
               assert (Hlowin_c :
                         history_low_eq_upto ty_env_c dlt_raw_c t
                           (map fst callee.(n_in)) Hc Hc' 0).
               {
                 intros j Hj_le y Hiny Hlowy.
                 assert (Hj0 : j = 0) by lia.
                 subst j.
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hinp_c)
                   as Hinp_c_eq.
                 destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
                   as (ity & Hnthity & Hfindy).
                 assert (Hii_exps : ii < List.length exps).
                 {
                   pose proof (Forall2_length _ _ _ Hforinp0) as Hlen_exps.
                   unfold callee_sig_cur in Hlen_in_c.
                   simpl in Hlen_in_c.
                   rewrite Hlen_exps.
                   rewrite <- Hlen_in_c.
                   apply nth_error_Some.
                   rewrite Hnthity.
                   discriminate.
                 }
                 destruct (nth_error exps ii) as [e|] eqn:Hnthe.
                 2:{
                   apply nth_error_None in Hnthe.
                   lia.
                 }
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
                      exps inptyp0 ii e
                      Hforinp0 Hnthe)
                   as (ety & Hnthety & Heqexp).
                 assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ t).
                 {
                   destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindy in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 ty =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x0 = SecT.hm_ext dlt_raw ty)
                        (s_in callee_sig_cur) inptyp0 ii ity
                        Hinst_in_eq Hnthity)
                     as (ety' & Hnthety' & Hinsteq).
                   unfold callee_sig_cur in Hnthity.
                   simpl in Hnthity.
                   change (nth_error inptyp0 ii = Some ety) in Hnthety.
                   change (nth_error inptyp0 ii = Some ety') in Hnthety'.
                   rewrite Hnthety in Hnthety'.
                   inversion Hnthety'; subst ety'; clear Hnthety'.
                   rewrite <- Hinsteq.
                   exact Halpha_low.
                 }
                 assert (Hfree_eq :
                           forall z,
                             Is_free_in_exp z e ->
                             Env.find z (H 0) = Env.find z (H' 0)).
                 {
                   intros z Hz.
                   assert (Hlowz : low_var ty_env dlt_raw t z).
                   {
                     eapply exp_type_low; eauto.
                   }
                   assert (Hdep_xz :
                             NLCaus.nl_depends_on_eq
                               (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
                   {
                     split; [exact Hxdef|].
                     eapply nth_error_free_in_aexps; eauto.
                   }
                   exact (Hdeps z Hdep_xz Hlowz 0 (le_n 0)).
                 }
                 eapply
                   (eqapp_input_var_low_eq_pointwise_clocked
                      ty_env ty_env_c callee callee_sig_cur
                      inptyp0 outtyp0 dlt_raw [rst_type] ckty0 t
                      bk bk' H H' Hc Hc' exps ls ls' 0 ii y ity e ety); eauto.
               }
               assert (HgoodG : SIG.secglobal_good G).
               {
                 eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env.
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
               }
               assert (Hsiggood_c : SIG.signature_good callee_sig_cur).
               {
                 eapply HgoodG.
                 exact Hfindsigc.
               }
               assert
                 (Hresetlhs_c :
                    forall y lhs,
                      findST callee_sig_cur.(s_constraints) y = Some lhs ->
                      In callee_sig_cur.(s_reset) lhs).
               {
                 intros y lhs Hfindlhs.
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_reset_scoped_env
                      all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
                 - exact Hfindsigc.
                 - exact Hfindlhs.
               }
               assert
                 (Hclocklhs_c :
                    forall y lhs,
                      findST callee_sig_cur.(s_constraints) y = Some lhs ->
                      In callee_sig_cur.(s_clk) lhs).
               {
                 intros y lhs Hfindlhs.
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_clock_scoped_env
                      all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
                 - exact Hfindsigc.
                 - exact Hfindlhs.
               }
               assert (Hlowxty0 : dlt_raw xty0 ⊑ t).
               {
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha.
                 exact Halpha_low.
               }
               assert (Hi_out : i < length (s_out callee_sig_cur)).
               {
                 rewrite Hlen_out_c.
                 apply nth_error_Some.
                 rewrite Hnthout.
                 discriminate.
               }
               destruct (nth_error (s_out callee_sig_cur) i) as [yty|] eqn:Hnthyty.
               2:{
                 apply nth_error_None in Hnthyty.
                 lia.
               }
               assert (Hsatceq : SecT.listSatisfiable dlt_raw ceq).
               {
                 pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                   as Hmid.
                 specialize (Hmid Hsatraw).
                 exact Hmid.
               }
               assert (Hlow_ck : SecT.hm_ext dlt_raw ckty0 ⊑ t).
               {
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_clock_low
                      callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 ceq st_inp0 stceq
                      dlt_raw t i yty xty0).
                 - exact Hsiggood_c.
                 - exact Hclocklhs_c.
                 - exact Hfresh_call.
                 - exact Hndscope_c.
                 - exact Hlen_in_c.
                 - exact Hlen_out_c.
                 - exact Hcallc.
                 - exact Hsatceq.
                 - exact Hnthyty.
                 - exact Hnthout.
                 - exact Hlowxty0.
               }
               assert (Hclock_eq0 : clock_eq_upto (clock_of ls) (clock_of ls') 0).
               {
                 intros j Hj0.
                 assert (Hjz : j = 0) by lia.
                 subst j.
                 eapply sem_clock_eq_upto_from_env_eq
                   with (bk := bk) (bk' := bk') (H := H) (H' := H') (ck := ck) (k := 0).
                 - exact Hsem_clock.
                 - exact Hsem_clock'.
                 - exact Hclock_eq.
                 - intros z Hz j1 Hj1.
                   destruct (Hfree_clock_scope z Hz) as (ty0 & Hfindz & _).
                   assert (Hlowz : low_var ty_env dlt_raw t z).
                   {
                     exists ty0.
                     split; [exact Hfindz|].
                     eapply order_trans.
                     1:{ eapply SecT.hm_ext_list_in1.
                         eapply assign_clk_type_free_var_in; eauto. }
                     exact Hlow_ck.
                   }
                   assert (Hdep_xz :
                             NLCaus.nl_depends_on_eq
                               (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
                   {
                     split; [exact Hxdef|].
                     apply freeAexps2.
                     exact Hz.
                   }
                   exact (Hdeps z Hdep_xz Hlowz j1 Hj1).
                 - exact Hj0.
               }
               pose proof
                 (Hcallout
                    (xh :: xt) ck callee.(n_name) exps callee callee_sig_cur
                    ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                    Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                 as Hcallee_out_raw.
               assert
                 (Hsigdef_cur :
                    callee_sig_cur =
                    {| s_name := callee.(n_name);
                       s_in := inp_c;
                       s_out := out_c;
                       s_reset := rst_type_c;
                       s_clk := clk_type_c;
                       s_constraints := SymTypes.simplify raw_c locals_c |}).
               {
                 unfold callee_sig_cur.
                 reflexivity.
               }
               specialize
                 (Hcallee_out_raw
                    0 ty_env_c callee_sig_cur t (clock_of ls) (clock_of ls') Hc Hc'
                    clk_id_c rst_id_c clk_type_c rst_type_c
                    inp_c out_c locals_c raw_c st_n_c
                    Henvsgen Hord Hwcglob Hallsig Hcaus
                    Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                    Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                    Hraw_c Hsigdef_cur
                    (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                       ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                       inp_c out_c locals_c raw_c st_n_c
                       Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                       Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                       Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                    Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hclock_eq0 Hlowin_c).
               pose proof
                 (get_mappings_from_node_eq _ _ _ _ Hout_c)
                 as Hout_c_eq.
               assert (Hiout : i < List.length (map fst callee.(n_out))).
               {
                 pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                 unfold callee_sig_cur in Hlen_out_c.
                 simpl in Hlen_out_c.
                 assert (Hiout0 : i < List.length outtyp0).
                 {
                   apply nth_error_Some.
                   rewrite Hnthout.
                   discriminate.
                 }
                 lia.
               }
               destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
               2:{
                 apply nth_error_None in Hnthyo.
                 lia.
               }
               destruct
                 (get_mappings_nth_error_inv
                    (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                 as (yty_out & Hnthyty_out & Hfindyo).
               assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
               {
                 exists yty_out.
                 split; [exact Hfindyo|].
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha; clear Hfindalpha.
                 unfold callee_sig_cur in Hnthyty_out.
                 simpl in Hnthyty_out.
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun x v =>
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           [rst_type] outtyp0 v =
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           [rst_type] outtyp0 x)
                      (s_out callee_sig_cur) outtyp0 i yty_out
                      Hinst_out_eq Hnthyty_out)
                   as (xty' & Hnthxty' & Hinsteq).
                 rewrite Hnthout in Hnthxty'.
                 inversion Hnthxty'; subst xty'; clear Hnthxty'.
                 unfold dlt_raw_c.
                 rewrite <- Hinsteq.
                 destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                 rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                            dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 xty0).
                 - exact Halpha_low.
                 - unfold SIG.outputs_fresh in Houtfresh.
                   rewrite Forall_forall in Houtfresh.
                   apply Houtfresh.
                   eapply SecT.nth_error_In_local.
                   exact Hnthout.
               }
               eapply
                 (eqapp_output_transport_pointwise
                    ty_env_c dlt_raw_c t
                    H H' Hc Hc' callee
                    (xh :: xt) ys ys' 0 i x yo); eauto.
            }
               assert (Hsem_eq :
                         Indexed.sem_equation all_nodes bk H
                           (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
               { eapply Forall_forall; eauto. }
               assert (Hsem_eq' :
                         Indexed.sem_equation all_nodes bk' H'
                           (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
               { eapply Forall_forall; eauto. }
               destruct
                 (generate_eqns_constraints_member G
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqreset_constraint_inv G
                    ty_env clk_type rst_type xh xt ck f exps r ckr ceq steq stceq Hgeq)
                 as (nsig_c & ckty0 & rty0 & rstty0 & inptyp0 & outtyp0
                     & st_clk0 & st_rst0 & st_inp0
                     & Hfindsigc & Hck0 & Hr0 & Hrst0 & Hinp0 & Hout0 & Hcallc).
               destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
               destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                 as (xty0 & Hnthout & Hfindx0).
               destruct
                 (sem_eqreset_inv all_nodes bk H (xh :: xt) ck f exps r ckr Hsem_eq)
                 as (rys & rs & ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock
                     & Hsem_var_r & Hbools_r & Hsem_node_masked).
               destruct
                 (sem_eqreset_inv all_nodes bk' H' (xh :: xt) ck f exps r ckr Hsem_eq')
                 as (rys' & rs' & ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock'
                     & Hsem_var_r' & Hbools_r' & Hsem_node_masked').
               set (kr := count rs 0).
               set (kr' := count rs' 0).
               specialize (Hsem_node_masked kr).
               specialize (Hsem_node_masked' kr').
               destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked)
                 as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                     & Hsem_vars_in_c & Hsem_vars_callee_out
                     & Hsem_clocked_c & Hsem_eqs_c).
               destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked')
                 as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                     & Hsem_vars_in_c' & Hsem_vars_callee_out'
                     & Hsem_clocked_c' & Hsem_eqs_c').
               assert (Hcallee_eq : callee' = callee)
                 by (eapply find_node_unique_nodup;
                     [eapply Ordered_nodes_nodup_names; exact Hord
                     |exact Hfindcallee'
                     |exact Hfindcallee]).
               subst callee'.
               assert (Hneqf : f <> n.(n_name)).
               {
                 intro Heqf.
                 eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                 eapply Exists_exists.
                 exists (EqApp (xh :: xt) ck f exps (Some (r, ckr))).
                 split; [exact Heqin|].
                 subst f.
                 constructor.
               }
               assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
               {
                 intro Heq.
                 apply Hneqf.
                 rewrite Heq.
                 symmetry.
                 exact (proj1 (find_node_In _ _ _ Hfindcallee)).
               }
               assert (Hck0_init :
                         SC.option_to_sec
                           (SECCETYPING.assign_clk_type ty_env clk_type ck)
                           SC.init_state = OK (ckty0, SC.init_state)).
               {
                 eapply option_to_sec_assign_clk_state_irrel.
                 exact Hck0.
               }
               assert (Hrst0_init :
                         SC.option_to_sec
                           (SECCETYPING.assign_clk_type ty_env rst_type ckr)
                           SC.init_state = OK (rstty0, SC.init_state)).
               {
                 eapply option_to_sec_assign_clk_state_irrel.
                 exact Hrst0.
               }
               assert (Hinp0_init :
                         SC.mmap
                           (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                           exps SC.init_state = OK (inptyp0, SC.init_state)).
               {
                 eapply mmap_assign_exp_type_state_irrel.
                 exact Hinp0.
               }
               pose proof
                (Hresetsec_node
                    (xh :: xt) ck f exps r ckr callee nsig_c
                    ckty0 rty0 rstty0 inptyp0 outtyp0
                    SC.init_state SC.init_state SC.init_state
                    Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0)
                 as Hcallee_secure.
               destruct Hcallee_secure as
                   [ty_env_c sig_c
                    clk_id_c rst_id_c clk_type_c rst_type_c
                    inp_c out_c locals_c raw_c st_n_c
                    Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                    Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                    Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                    Hcallsec_c Hresetsec_c].
               pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
               rewrite Hcallee_name in Hfindsig_c.
               rewrite Hfindsigc in Hfindsig_c.
               assert (Hsig_eq : nsig_c = sig_c).
               { inversion Hfindsig_c; reflexivity. }
               subst nsig_c.
               pose
                 (callee_sig_cur :=
                    {| s_name := callee.(n_name);
                       s_in := inp_c;
                       s_out := out_c;
                       s_reset := rst_type_c;
                       s_clk := clk_type_c;
                       s_constraints := SymTypes.simplify raw_c locals_c |}).
               rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                 Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
               set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
               set (dlt_sig_c :=
                      SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                        ([rty0] ⊔ rstty0) outtyp0).
               set (dlt_raw_c :=
                      SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                        ([rty0] ⊔ rstty0) outtyp0).
               destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
                 as [P Hwcnode].
               destruct Hwcnode as [_ [_ [Hwcenv Hwc_eqs]]].
               assert (Hwcapp :
                         Clo.wc_equation P
                           (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                           (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
               {
                 rewrite Forall_forall in Hwc_eqs.
                 exact (Hwc_eqs _ Heqin).
               }
               inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                     Hfindwc Hins Hwcouts Hreset|]; subst.
               assert
                 (Hvars_scoped :
                    SECNLUSTYPING.vars_env_scoped ty_env
                      (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                      caller_scope).
               {
                 eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                   eauto.
               }
               assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
               {
                 eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                   with (scope := caller_scope)
                        (es := exps)
                        (st := SC.init_state)
                        (st' := SC.init_state); eauto.
                 eapply SECNLUSTYPING.wc_call_args_scoped
                   with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        (scope := caller_scope)
                        (sub := sub)
                        (ck := ck)
                        (ins := n0.(n_in)); eauto.
               }
               assert
                 (Hfree_clock_scope :
                    forall z,
                      Is_free_in_clock z ck ->
                      exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
               {
                 intros z Hz.
                 destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                 { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                 exists ty0; split; [exact Hfindz|exact Hinscope].
               }
               assert
                 (Hassign_ck :
                    SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
               {
                 unfold SC.option_to_sec in Hck0_init.
                 destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                   eqn:Hassign; simpl in Hck0_init; try discriminate.
                 inversion Hck0_init; now subst ckty'.
               }
               assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
               {
                 eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                 - simpl. repeat (apply in_or_app; right).
                   simpl. now left.
                 - exact Hfree_clock_scope.
                 - exact Hassign_ck.
               }
               assert (Hr_scope : SecT.st_scoped caller_scope [rty0]).
               {
                 apply SecT.st_scoped_singleton.
                 assert (Hinr_pair :
                           In (r, ckr)
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                 { eapply wc_reset_in_call_vars; eauto. }
                 destruct (Hvars_scoped r) as (ty0 & Hfindr & Hinscope).
                 - eapply In_InMembers. exact Hinr_pair.
                 - rewrite Hr0 in Hfindr.
                   inversion Hfindr; subst ty0.
                   exact Hinscope.
               }
               assert
                 (Hfree_rclock_scope :
                    forall z,
                      Is_free_in_clock z ckr ->
                      exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
               {
                 intros z Hz.
                 assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                 { eapply wc_reset_in_call_vars; eauto. }
                 assert (Hwr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ckr).
                 { eapply wc_env_var; eauto. }
                 destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                 - eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto.
                 - exists ty0; split; [exact Hfindz|exact Hinscope].
               }
               assert
                 (Hassign_rst :
                    SECCETYPING.assign_clk_type ty_env rst_type ckr = Some rstty0).
               {
                 unfold SC.option_to_sec in Hrst0_init.
                 destruct (SECCETYPING.assign_clk_type ty_env rst_type ckr) as [rstty'|]
                   eqn:Hassign; simpl in Hrst0_init; try discriminate.
                 inversion Hrst0_init; now subst rstty'.
               }
               assert (Hrst_scope : SecT.st_scoped caller_scope rstty0).
               {
                 eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_type) (ck := ckr).
                 - simpl. repeat (apply in_or_app; right).
                   simpl. now right; left.
                 - exact Hfree_rclock_scope.
                 - exact Hassign_rst.
               }
               assert (Hrst_join_scope : SecT.st_scoped caller_scope ([rty0] ⊔ rstty0)).
               {
                 eapply SecT.st_scoped_merge; eauto.
               }
               assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
               {
                 rewrite Forall_forall.
                 intros ty Hty.
                 pose proof
                   (eqapp_outtyp_in_out_or_locals
                      n ty_env out locals (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) outtyp0 ty
                      Heqin Hout0 Hout Hlocals Hty)
                   as Hin_out_or_locals.
                 replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                 - apply in_or_app. right.
                   eapply In_app_weaken_right.
                   exact Hin_out_or_locals.
                 - unfold caller_scope.
                   repeat rewrite <- app_assoc.
                   reflexivity.
               }
               assert (Hscopefresh :
                         SIG.scope_fresh caller_scope callee_sig_cur).
               {
                 eapply generated_caller_scope_fresh_scoped_env
                   with (caller := n)
                        (callee := callee)
                        (caller_env := ty_env)
                        (callee_env := ty_env_c)
                        (clk_id := clk_id)
                        (rst_id := rst_id)
                        (clk_type := clk_type)
                        (rst_type := rst_type)
                        (inp := inp)
                        (out := out)
                        (locals := locals); eauto.
               }
               assert (Hndscope_c :
                         NoDup (SIG.signature_scope callee_sig_cur)).
               {
                 eapply generated_sig_scope_nodup_scoped_env
                   with (n := callee)
                        (ty_env := ty_env_c)
                        (clk_id := clk_id_c)
                        (rst_id := rst_id_c)
                        (clk_type := clk_type_c)
                        (rst_type := rst_type_c)
                        (inp := inp_c)
                        (out := out_c); eauto.
               }
               assert (Hfresh_call :
                         SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0
                           ([rty0] ⊔ rstty0) outtyp0).
               {
                 eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
               }
               pose proof
                 (generate_constraints_lengths
                    callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                    ceq st_inp0 stceq Hcallc)
                 as [Hlen_in_c Hlen_out_c].
               destruct
                 (mmap_assign_exp_type_inv ty_env exps inptyp0 st_rst0 st_inp0 Hinp0)
                 as [_ Hforinp0].
               pose proof
                 (SIGPROOFS.inst_valuation_inputs_eq
                    dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                    Hfresh_call Hndscope_c Hlen_in_c)
                 as Hinst_in_eq.
               pose proof
                 (SIGPROOFS.inst_valuation_outputs_eq
                    dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                    Hfresh_call Hndscope_c Hlen_out_c)
                 as Hinst_out_eq.
               assert (Hlowin_c :
                         history_low_eq_upto ty_env_c dlt_raw_c t
                           (map fst callee.(n_in)) Hc Hc' 0).
               {
                 intros j Hj_le y Hiny Hlowy.
                 assert (Hj0 : j = 0) by lia.
                 subst j.
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hinp_c)
                   as Hinp_c_eq.
                 destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
                   as (ity & Hnthity & Hfindy).
                 assert (Hii_exps : ii < List.length exps).
                 {
                   pose proof (Forall2_length _ _ _ Hforinp0) as Hlen_exps.
                   unfold callee_sig_cur in Hlen_in_c.
                   simpl in Hlen_in_c.
                   rewrite Hlen_exps.
                   rewrite <- Hlen_in_c.
                   apply nth_error_Some.
                   rewrite Hnthity.
                   discriminate.
                 }
                 destruct (nth_error exps ii) as [e|] eqn:Hnthe.
                 2:{
                   apply nth_error_None in Hnthe.
                   lia.
                 }
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
                      exps inptyp0 ii e
                      Hforinp0 Hnthe)
                   as (ety & Hnthety & Heqexp).
                 assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ t).
                 {
                   destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindy in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 ty =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 x0 = SecT.hm_ext dlt_raw ty)
                        (s_in callee_sig_cur) inptyp0 ii ity
                        Hinst_in_eq Hnthity)
                     as (ety' & Hnthety' & Hinsteq).
                   unfold callee_sig_cur in Hnthity.
                   simpl in Hnthity.
                   change (nth_error inptyp0 ii = Some ety) in Hnthety.
                   change (nth_error inptyp0 ii = Some ety') in Hnthety'.
                   rewrite Hnthety in Hnthety'.
                   inversion Hnthety'; subst ety'; clear Hnthety'.
                   rewrite <- Hinsteq.
                   exact Halpha_low.
                 }
                 assert (Hfree_eq :
                           forall z,
                             Is_free_in_exp z e ->
                             Env.find z (H 0) = Env.find z (H' 0)).
                 {
                   intros z Hz.
                   assert (Hlowz : low_var ty_env dlt_raw t z).
                   {
                     eapply exp_type_low; eauto.
                   }
                   assert (Hdep_xz :
                             NLCaus.nl_depends_on_eq
                               (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
                   {
                     split; [exact Hxdef|].
                     left.
                     eapply nth_error_free_in_aexps; eauto.
                   }
                   exact (Hdeps z Hdep_xz Hlowz 0 (le_n 0)).
                 }
                 eapply
                   (eqapp_reset_input_var_low_eq_pointwise_clocked
                      ty_env ty_env_c callee callee_sig_cur
                      inptyp0 outtyp0 dlt_raw ([rty0] ⊔ rstty0) ckty0 t
                      bk bk' H H' Hc Hc' exps rs rs' kr kr' ls ls' 0 ii y ity e ety); eauto.
               }
               assert (Hreset_ctrl0 :
                         reset_control_low_eq_upto ty_env dlt_raw t r H H' 0).
               {
                 eapply reset_control_low_eq_upto_of_sem_var_eq.
                 intros Hlowr j0 Hj0.
                 assert (Hdep_xr :
                           NLCaus.nl_depends_on_eq
                             (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x r).
                 {
                   split; [exact Hxdef|].
                   right. left. reflexivity.
                   }
                 exact (Hdeps r Hdep_xr Hlowr j0 Hj0).
               }
               assert (HgoodG : SIG.secglobal_good G).
               {
                 eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env.
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
               }
               assert (Hsiggood_c : SIG.signature_good callee_sig_cur).
               {
                 eapply HgoodG.
                 exact Hfindsigc.
               }
               assert
                 (Hresetlhs_c :
                    forall y lhs,
                      findST callee_sig_cur.(s_constraints) y = Some lhs ->
                      In callee_sig_cur.(s_reset) lhs).
               {
                 intros y lhs Hfindlhs.
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_reset_scoped_env
                      all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
                 - exact Hfindsigc.
                 - exact Hfindlhs.
               }
               assert
                 (Hclocklhs_c :
                    forall y lhs,
                      findST callee_sig_cur.(s_constraints) y = Some lhs ->
                      In callee_sig_cur.(s_clk) lhs).
               {
                 intros y lhs Hfindlhs.
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_clock_scoped_env
                      all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                 - exact Henvsgen.
                 - exact Hwcglob.
                 - exact Hallsig.
                 - exact Hfindsigc.
                 - exact Hfindlhs.
               }
               assert (Hlowxty0 : dlt_raw xty0 ⊑ t).
               {
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha.
                 exact Halpha_low.
               }
               assert (Hi_out : i < length (s_out callee_sig_cur)).
               {
                 rewrite Hlen_out_c.
                 apply nth_error_Some.
                 rewrite Hnthout.
                 discriminate.
               }
               destruct (nth_error (s_out callee_sig_cur) i) as [yty|] eqn:Hnthyty.
               2:{
                 apply nth_error_None in Hnthyty.
                 lia.
               }
               assert (Hsatceq : SecT.listSatisfiable dlt_raw ceq).
               {
                 pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                   as Hmid.
                 specialize (Hmid Hsatraw).
                 exact Hmid.
               }
               assert (Hlow_rst_join : SecT.hm_ext dlt_raw ([rty0] ⊔ rstty0) ⊑ t).
               {
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_reset_low
                      callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 ceq st_inp0 stceq
                      dlt_raw t i yty xty0).
                 - exact Hsiggood_c.
                 - exact Hresetlhs_c.
                 - exact Hfresh_call.
                 - exact Hndscope_c.
                 - exact Hlen_in_c.
                 - exact Hlen_out_c.
                 - exact Hcallc.
                 - exact Hsatceq.
                 - exact Hnthyty.
                 - exact Hnthout.
                 - exact Hlowxty0.
               }
               assert (Hlowr0 : low_var ty_env dlt_raw t r).
               {
                 exists rty0.
                 split; [exact Hr0|].
                 apply order_trans with (y := SecT.hm_ext dlt_raw [rty0]).
                 - apply singleton_type_bound.
                 - apply order_trans with (y := SecT.hm_ext dlt_raw ([rty0] ⊔ rstty0)).
                   + apply SecT.hm_ext_concat_l.
                   + exact Hlow_rst_join.
               }
               assert (Hlow_ck0 : SecT.hm_ext dlt_raw ckty0 ⊑ t).
               {
                 eapply
                   (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_clock_low
                      callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 ceq st_inp0 stceq
                      dlt_raw t i yty xty0).
                 - exact Hsiggood_c.
                 - exact Hclocklhs_c.
                 - exact Hfresh_call.
                 - exact Hndscope_c.
                 - exact Hlen_in_c.
                 - exact Hlen_out_c.
                 - exact Hcallc.
                 - exact Hsatceq.
                 - exact Hnthyty.
                 - exact Hnthout.
                 - exact Hlowxty0.
               }
               assert (Hclock_eq_raw0 : clock_eq_upto (clock_of ls) (clock_of ls') 0).
               {
                 intros j Hj0.
                 assert (Hjz : j = 0) by lia.
                 subst j.
                 eapply sem_clock_eq_upto_from_env_eq
                   with (bk := bk) (bk' := bk') (H := H) (H' := H') (ck := ck) (k := 0).
                 - exact Hsem_clock.
                 - exact Hsem_clock'.
                 - exact Hclock_eq.
                 - intros z Hz j1 Hj1.
                   destruct (Hfree_clock_scope z Hz) as (ty0 & Hfindz & _).
                   assert (Hlowz : low_var ty_env dlt_raw t z).
                   {
                     exists ty0.
                     split; [exact Hfindz|].
                     eapply order_trans.
                     1:{
                       eapply SecT.hm_ext_list_in1.
                       eapply (assign_clk_type_free_var_in ty_env clk_type ck ckty0 z ty0).
                       - exact Hassign_ck.
                       - exact Hz.
                       - exact Hfindz.
                     }
                     exact Hlow_ck0.
                   }
                   assert (Hdep_xz :
                             NLCaus.nl_depends_on_eq
                               (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
                   {
                     split; [exact Hxdef|].
                     left.
                     apply freeAexps2.
                     exact Hz.
                   }
                   exact (Hdeps z Hdep_xz Hlowz j1 Hj1).
                 - exact Hj0.
               }
               assert (Hcount_eq0 : forall j, j <= 0 -> count rs j = count rs' j).
               {
                 intros j Hj0.
                 exact
                   (Hreset_ctrl0 rys rys' rs rs' Hsem_var_r Hsem_var_r' Hbools_r Hbools_r'
                      Hlowr0 j Hj0).
               }
               assert (Hkr_eq : kr = count rs 0).
               { unfold kr. reflexivity. }
               assert (Hkr'_eq : kr' = count rs' 0).
               { unfold kr'. reflexivity. }
               assert
                 (Hclock_eq0 :
                    clock_eq_upto (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) 0).
               {
                 intros j_mask Hj_mask.
                 eapply clock_of_mask_eq_upto; eauto.
               }
               pose proof
                 (Hresetout
                    (xh :: xt) ck callee.(n_name) exps r ckr callee callee_sig_cur
                    ckty0 rty0 rstty0 inptyp0 outtyp0
                    SC.init_state SC.init_state SC.init_state
                    Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0
                    0
                    Hreset_ctrl0)
                 as Hcallee_out_raw.
               assert
                 (Hsigdef_cur :
                    callee_sig_cur =
                    {| s_name := callee.(n_name);
                       s_in := inp_c;
                       s_out := out_c;
                       s_reset := rst_type_c;
                       s_clk := clk_type_c;
                       s_constraints := SymTypes.simplify raw_c locals_c |}).
               {
                 unfold callee_sig_cur.
                 reflexivity.
               }
               specialize
                 (Hcallee_out_raw
                    0 ty_env_c callee_sig_cur t
                    (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) Hc Hc'
                    clk_id_c rst_id_c clk_type_c rst_type_c
                    inp_c out_c locals_c raw_c st_n_c
                    Henvsgen Hord Hwcglob Hallsig Hcaus
                    Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                    Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                    Hraw_c Hsigdef_cur
                    (SecureNode all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c
                       ty_env_c callee_sig_cur clk_id_c rst_id_c clk_type_c rst_type_c
                       inp_c out_c locals_c raw_c st_n_c
                       Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                       Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c Hraw_c
                       Hsigdef_cur Hsatsig_c Hagree_c Hsatraw_c Hcallsec_c Hresetsec_c)
                    Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hclock_eq0 Hlowin_c).
               pose proof
                 (get_mappings_from_node_eq _ _ _ _ Hout_c)
                 as Hout_c_eq.
               assert (Hiout : i < List.length (map fst callee.(n_out))).
               {
                 pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                 unfold callee_sig_cur in Hlen_out_c.
                 simpl in Hlen_out_c.
                 assert (Hiout0 : i < List.length outtyp0).
                 {
                   apply nth_error_Some.
                   rewrite Hnthout.
                   discriminate.
                 }
                 lia.
               }
               destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
               2:{
                 apply nth_error_None in Hnthyo.
                 lia.
               }
               destruct
                 (get_mappings_nth_error_inv
                    (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                 as (yty_out0 & Hnthyty0 & Hfindyo).
               assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
               {
                 exists yty_out0.
                 split; [exact Hfindyo|].
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha; clear Hfindalpha.
                 unfold callee_sig_cur in Hnthyty0.
                 simpl in Hnthyty0.
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun x0 v =>
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           ([rty0] ⊔ rstty0) outtyp0 v =
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           ([rty0] ⊔ rstty0) outtyp0 x0)
                      (s_out callee_sig_cur) outtyp0 i yty_out0
                      Hinst_out_eq Hnthyty0)
                   as (xty' & Hnthxty' & Hinsteq).
                 rewrite Hnthout in Hnthxty'.
                 inversion Hnthxty'; subst xty'; clear Hnthxty'.
                 unfold dlt_raw_c.
                 rewrite <- Hinsteq.
                 destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                 rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                            dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 xty0).
                 - exact Halpha_low.
                 - unfold SIG.outputs_fresh in Houtfresh.
                   rewrite Forall_forall in Houtfresh.
                   apply Houtfresh.
                   eapply SecT.nth_error_In_local.
                   exact Hnthout.
               }
               eapply
                 (eqapp_reset_output_transport_pointwise
                    ty_env_c dlt_raw_c t
                    H H' Hc Hc' callee
                    (xh :: xt) ys ys' rs rs' kr kr' 0 i x yo); eauto.
          * assert (Hx : x = x0).
            { simpl in Hxdef. intuition. }
            subst x.
            assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqFby x0 ck c0 e)).
            { eapply Forall_forall; eauto. }
            assert (Hsem_eq' : Indexed.sem_equation all_nodes bk' H' (EqFby x0 ck c0 e)).
            { eapply Forall_forall; eauto. }
            inversion Hsem_eq as
                [| | | ? ? ? ? ? ? ? ? Hfby_aexp0 Hfby_var0 Hfby_eq0];
              subst; clear Hsem_eq.
            inversion Hsem_eq' as
                [| | | ? ? ? ? ? ? ? ? Hfby_aexp0' Hfby_var0' Hfby_eq0'];
              subst; clear Hsem_eq'.
            destruct
              (generate_eqns_constraints_member G
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqFby x0 ck c0 e) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqfby_constraint_inv G
                 ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
              as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
            assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
            {
              rewrite Hcns in Hmid.
              inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
              inversion Hnil; subst; clear Hnil.
              exact Hsat_ceq.
            }
            eapply
              (eqfby_noninterference_delayed_pointwise_clocked
                 bk bk' H H' x0 _ _ _ _ ck c0 e 0).
            -- intros y Hclock.
               assert (Hlowy : low_var ty_env dlt_raw t y).
               {
                 eapply simple_security_aexp; eauto using freeAexp2.
               }
               assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqFby x0 ck c0 e) x0 y).
               { split; [reflexivity|exact Hclock]. }
               specialize (Hdeps y Hdep_xy Hlowy 0 (le_n 0)).
               exact Hdeps.
            -- intros y Hfree j Hjlt.
               exfalso. lia.
            -- intros j Hjlt.
               exfalso. lia.
            -- exact (Hclock_eq 0 (le_n 0)).
            -- exact Hfby_var0.
            -- exact Hfby_aexp0.
            -- reflexivity.
            -- exact Hfby_var0'.
            -- exact Hfby_aexp0'.
            -- reflexivity.
        + eapply history_low_eq_upto_inputs_pointwise; eauto.
        + eapply NLCaus.nl_global_causal_find; eauto.
      }
      eapply history_low_eq_upto_from_Forall_pointwise; eauto.
    Qed.
    (** Mainline two-clock step theorem.

        Relation to the paper:
        this is the proof-internal node-step theorem consumed by the raw
        output theorem.  It differs from the older helper theorem only in the
        current-node ambient clocks: the second run uses [bk'] and the proof
        carries an explicit prefix premise [clock_eq_upto bk bk' k].  The
        recursive call premises remain the clocked raw-output specs already
        used in the helper layer. *)
    Theorem node_noninterference_vars_defined_step_mainline :
      forall n dlt_sig dlt_raw k
             ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SIG.find_signature n.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := n.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names n dlt_sig dlt_raw ->
        (forall xs ck f exps callee callee_sig
                ckty inptyp outtyp st_clk st_inp,
            In (EqApp xs ck f exps None) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_clk = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            node_outputs_raw_spec_clocked all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)) ->
        (forall xs ck f exps r ckr callee callee_sig
                ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
            In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
            find_node f all_nodes = Some callee ->
            SIG.find_signature f G = Some callee_sig ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
              SC.init_state = OK (ckty, st_clk) ->
            Env.find r ty_env = Some rty ->
            SC.option_to_sec
              (SECCETYPING.assign_clk_type ty_env sig.(s_reset) ckr)
              st_clk = OK (rstty, st_rst) ->
            SC.mmap
              (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
              exps st_rst = OK (inptyp, st_inp) ->
            get_mappings xs ty_env = Some outtyp ->
            forall k_reset,
              reset_control_low_eq_upto ty_env dlt_raw t r H H' k_reset ->
            node_outputs_raw_spec_clocked all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)) ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') n.(n_eqs) ->
        clock_eq_upto bk bk' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst n.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' k.
    Proof.
      intros n dlt_sig dlt_raw k.
      induction k as [|k IHk];
        intros ty_env sig t bk bk' H H'
               clk_id rst_id clk_type rst_type inp out locals raw st_n
               Henvsgen Hord Hwcglob Hallsig Hcaus Hfindnode Hfindenv
               Hfindsig Hsiggen Haux Hclk Hrst Hinp Hout Hlocals Hraw
               Hsigdef Hsecure Hcallout Hresetout Hsatraw Hsem Hsem' Hclock_eq Hlowin.
      - eapply node_noninterference_vars_defined_step_base_mainline; eauto.
      - set (m := S k).
        destruct (wc_global_find_node all_nodes n Hwcglob Hfindnode)
          as [P Hwcnode].
        pose proof Hwcnode as Hwcnode_full.
        destruct Hwcnode_full as [_ [_ [Hwcenv Hwc_eqs]]].
        assert (Hprev :
                  history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' k).
        {
          eapply IHk with
              (ty_env := ty_env) (sig := sig) (t := t) (bk := bk) (H := H) (H' := H')
              (clk_id := clk_id) (rst_id := rst_id)
              (clk_type := clk_type) (rst_type := rst_type)
              (inp := inp) (out := out) (locals := locals)
              (raw := raw) (st_n := st_n).
          - exact Henvsgen.
          - exact Hord.
          - exact Hwcglob.
          - exact Hallsig.
          - exact Hcaus.
          - exact Hfindnode.
          - exact Hfindenv.
          - exact Hfindsig.
          - exact Hsiggen.
          - exact Haux.
          - exact Hclk.
          - exact Hrst.
          - exact Hinp.
          - exact Hout.
          - exact Hlocals.
          - exact Hraw.
          - exact Hsigdef.
          - exact Hsecure.
          - intros xs ck f exps callee callee_sig
                   ckty inptyp outtyp st_clk st_inp
                   Heqin Hfindcallee Hfindsigc Hck0 Hinp0 Hout0.
            eapply Hcallout; eauto.
          - intros xs ck f exps r ckr callee callee_sig
                   ckty rty rstty inptyp outtyp st_clk st_rst st_inp
                   Heqin Hfindcallee Hfindsigc Hck0 Hr0 Hrst0 Hinp0 Hout0
                   k_reset Hreset_ctrl.
            eapply Hresetout; eauto.
          - exact Hsatraw.
          - exact Hsem.
          - exact Hsem'.
          - unfold m.
            intros j Hj.
            exact (Hclock_eq j (Nat.le_trans _ _ _ Hj (Nat.le_succ_diag_r k))).
          - unfold m.
            eapply history_low_eq_upto_monotone.
            + apply Nat.le_succ_diag_r.
            + exact Hlowin.
        }
        pose proof (Ordered_nodes_nodup_names _ Hord) as Hndnames.
        destruct Hsecure as
            [ty_env_sec sig_sec
             clk_id_sec rst_id_sec clk_type_sec rst_type_sec
             inp_sec out_sec locals_sec raw_sec st_n_sec
             Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
             Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
             Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
             Hcallsec_cur Hresetsec_cur].
        rewrite Hfindenv in Hfindenv_sec.
        inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
        rewrite Hfindsig in Hfindsig_sec.
        inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
        rewrite <- H1 in Hcallsec_cur, Hresetsec_cur, Hsatsig_sec, Hagree_sec.
        rewrite Hsigdef in Hcallsec_cur, Hresetsec_cur, Hcallout, Hresetout.
        pose proof Hcallsec_cur as Hcallsec_node.
        pose proof Hresetsec_cur as Hresetsec_node.
        assert
          (Hpts_cur :
             Forall
               (fun x =>
                  low_var ty_env dlt_raw t x ->
                  Env.find x (H m) = Env.find x (H' m))
               (vars_defined n.(n_eqs))).
        {
          eapply nl_node_causal_ind_defined.
          + intros eq x Heqin Hxdef Hdeps Hlowx.
            destruct eq as [x0 ck ce|xs ck f exps r|x0 ck c0 e];
              simpl in Hxdef.
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk' H' (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member G
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqDef x0 ck ce) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqdef_constraint_inv G
                   ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
                as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              refine
                (eqdef_noninterference_instant_pointwise_clocked
                   bk bk' H H' x0 xs xs0 ck ce m _ _ _ _ _ _).
              - intros y Hfree.
                assert (Hlowy : low_var ty_env dlt_raw t y).
                {
                  eapply simple_security_caexp; eauto.
                }
                assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
                { split; [reflexivity|exact Hfree]. }
                exact (Hdeps y Hdep_xy Hlowy).
              - exact (Hclock_eq m (le_n m)).
              - eassumption.
              - eassumption.
              - eassumption.
              - eassumption.
            * destruct xs as [|xh xt].
              { simpl in Hxdef. contradiction. }
              destruct r as [[r ckr]|].
              2:{
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk' H'
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member G
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqapp_constraint_inv G
                      ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                       & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                   as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
                 destruct (sem_eqapp_inv all_nodes bk' H' (xh :: xt) ck f exps Hsem_eq')
                   as (ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock' & Hsem_node_c').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_c')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup;
                       [eapply Ordered_nodes_nodup_names; exact Hord
                       |exact Hfindcallee'
                       |exact Hfindcallee]).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps None).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                   (Hcallsec_node
                      (xh :: xt) ck f exps callee nsig_c
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps None)).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope [rst_type]).
                 {
                   simpl.
                   apply SecT.st_scoped_singleton.
                   repeat (apply in_or_app; right).
                   simpl. now right; left.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps None outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right.
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_clk0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' m).
                 {
                   unfold dlt_raw_c.
                   eapply
                     (succ_eqapp_nonreset_inputs_low_eq_upto_clocked
                        P n ty_env ty_env_c dlt_raw t
                        H H' Hc Hc' bk bk'
                        xh xt ck callee exps x k
                        inp_c inptyp0 outtyp0 ckty0 [rst_type] callee_sig_cur ls ls').
                   - exact Hwcnode.
                   - exact Heqin.
                   - exact Hxdef.
                   - exact Hdeps.
                   - exact Hlowin.
                   - exact Hprev.
                   - exact Hclock_eq.
                   - reflexivity.
                   - exact Hinp_c.
                   - exact Hforinp0.
                   - exact Hinst_in_eq.
                   - exact Hsem_exps.
                   - exact Hsem_exps'.
                   - exact Hsem_vars_in_c.
                   - exact Hsem_vars_in_c'.
                 }
                 assert (Hcallee_secure :
                           node_security all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c).
                 {
                   eapply SecureNode; eauto.
                 }
                 assert (HgoodG : SIG.secglobal_good G).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env.
                   - exact Henvsgen.
                   - exact Hwcglob.
                   - exact Hallsig.
                 }
                 assert (Hsiggood_c : SIG.signature_good callee_sig_cur).
                 {
                   eapply HgoodG.
                   exact Hfindsigc.
                 }
                 assert
                   (Hclocklhs_c :
                      forall y lhs,
                        findST callee_sig_cur.(s_constraints) y = Some lhs ->
                        In callee_sig_cur.(s_clk) lhs).
                 {
                   intros y lhs Hfindlhs.
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_clock_scoped_env
                        all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                   - exact Henvsgen.
                   - exact Hwcglob.
                   - exact Hallsig.
                   - exact Hfindsigc.
                   - exact Hfindlhs.
                 }
                 assert (Hlowxty0 : dlt_raw xty0 ⊑ t).
                 {
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha.
                   exact Halpha_low.
                 }
                 assert (Hi_out : i < length (s_out callee_sig_cur)).
                 {
                   rewrite Hlen_out_c.
                   apply nth_error_Some.
                   rewrite Hnthout.
                   discriminate.
                 }
                 destruct (nth_error (s_out callee_sig_cur) i) as [yty|] eqn:Hnthyty.
                 2:{
                   apply nth_error_None in Hnthyty.
                   lia.
                 }
                 assert (Hsatceq : SecT.listSatisfiable dlt_raw ceq).
                 {
                   pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                     as Hmid.
                   specialize (Hmid Hsatraw).
                   exact Hmid.
                 }
                 assert (Hlow_ck : SecT.hm_ext dlt_raw ckty0 ⊑ t).
                 {
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_clock_low
                        callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 ceq st_inp0 stceq
                        dlt_raw t i yty xty0).
                   - exact Hsiggood_c.
                   - exact Hclocklhs_c.
                   - exact Hfresh_call.
                   - exact Hndscope_c.
                   - exact Hlen_in_c.
                   - exact Hlen_out_c.
                   - exact Hcallc.
                   - exact Hsatceq.
                   - exact Hnthyty.
                   - exact Hnthout.
                   - exact Hlowxty0.
                 }
                 assert (Hclock_eqm : clock_eq_upto (clock_of ls) (clock_of ls') m).
                 {
                   intros j Hj.
                   eapply sem_clock_eq_upto_from_env_eq
                     with (bk := bk) (bk' := bk') (H := H) (H' := H') (ck := ck) (k := m).
                   - exact Hsem_clock.
                   - exact Hsem_clock'.
                   - exact Hclock_eq.
                   - intros z Hz j0 Hj0.
                     destruct (Hfree_clock_scope z Hz) as (ty0 & Hfindz & _).
                     assert (Hlowz : low_var ty_env dlt_raw t z).
                     {
                       exists ty0.
                       split; [exact Hfindz|].
                       eapply order_trans.
                       1:{
                         eapply SecT.hm_ext_list_in1.
                         eapply (assign_clk_type_free_var_in ty_env clk_type ck ckty0 z ty0).
                         - exact Hassign_ck.
                         - exact Hz.
                         - exact Hfindz.
                       }
                       exact Hlow_ck.
                     }
                     assert (Hdep_xz :
                               NLCaus.nl_depends_on_eq
                                 (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
                     {
                       split; [exact Hxdef|].
                       apply freeAexps2.
                       exact Hz.
                     }
                     destruct (Nat.eq_dec j0 m) as [Heqj0|Hneqj0].
                     + subst j0.
                       exact (Hdeps z Hdep_xz Hlowz).
                     + assert (Hjlt : j0 < S k).
                       {
                         unfold m in Hj0, Hneqj0.
                         destruct (Nat.compare_spec j0 (S k)) as [Heq|Hlt|Hgt].
                         - exfalso. apply Hneqj0. exact Heq.
                         - exact Hlt.
                         - exfalso.
                           eapply Nat.lt_irrefl.
                           eapply Nat.lt_le_trans; eauto.
                       }
                       eapply
                         (free_clock_low_eq_prefix_from_inputs_or_defined
                            P n ty_env dlt_raw t H H' (xh :: xt) ck callee.(n_name) exps None z k);
                         eauto.
                   - exact Hj.
                 }
                 pose proof
                   (Hcallout
                      (xh :: xt) ck callee.(n_name) exps callee callee_sig_cur
                      ckty0 inptyp0 outtyp0 SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hinp0_init Hout0)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      m ty_env_c callee_sig_cur t
                      (clock_of ls) (clock_of ls') Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur Hcallee_secure
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hclock_eqm Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty_out & Hnthyty_out & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty_out.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty_out.
                   simpl in Hnthyty_out.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty_out
                        Hinst_out_eq Hnthyty_out)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 eapply
                   (eqapp_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' m i x yo); eauto.
              }
              {
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk' H'
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member G
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqreset_constraint_inv G
                      ty_env clk_type rst_type xh xt ck f exps r ckr ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & rty0 & rstty0 & inptyp0 & outtyp0
                       & st_clk0 & st_rst0 & st_inp0
                       & Hfindsigc & Hck0 & Hr0 & Hrst0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct
                   (sem_eqreset_inv all_nodes bk H (xh :: xt) ck f exps r ckr Hsem_eq)
                   as (rys & rs & ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock
                       & Hsem_var_r & Hbools_r & Hsem_node_masked).
                 destruct
                   (sem_eqreset_inv all_nodes bk' H' (xh :: xt) ck f exps r ckr Hsem_eq')
                   as (rys' & rs' & ls' & ys' & Hsem_exps' & Hsem_vars_out' & Hsem_clock'
                       & Hsem_var_r' & Hbools_r' & Hsem_node_masked').
                 set (kr := count rs m).
                 set (kr' := count rs' m).
                 specialize (Hsem_node_masked kr).
                 specialize (Hsem_node_masked' kr').
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked)
                   as (bk_c & Hc & callee & Hbk_c & Hfindcallee
                       & Hsem_vars_in_c & Hsem_vars_callee_out
                       & Hsem_clocked_c & Hsem_eqs_c).
                 destruct (sem_node_inv all_nodes _ _ _ Hsem_node_masked')
                   as (bk_c' & Hc' & callee' & Hbk_c' & Hfindcallee'
                       & Hsem_vars_in_c' & Hsem_vars_callee_out'
                       & Hsem_clocked_c' & Hsem_eqs_c').
                 assert (Hcallee_eq : callee' = callee)
                   by (eapply find_node_unique_nodup; eauto).
                 subst callee'.
                 assert (Hneqf : f <> n.(n_name)).
                 {
                   intro Heqf.
                   eapply (find_node_not_Is_node_in _ _ _ Hord Hfindnode).
                   eapply Exists_exists.
                   exists (EqApp (xh :: xt) ck f exps (Some (r, ckr))).
                   split; [exact Heqin|].
                   subst f.
                   constructor.
                 }
                 assert (Hneqcaller_callee : n.(n_name) <> callee.(n_name)).
                 {
                   intro Heq.
                   apply Hneqf.
                   rewrite Heq.
                   symmetry.
                   exact (proj1 (find_node_In _ _ _ Hfindcallee)).
                 }
                 assert (Hck0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env clk_type ck)
                             SC.init_state = OK (ckty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hck0.
                 }
                 assert (Hrst0_init :
                           SC.option_to_sec
                             (SECCETYPING.assign_clk_type ty_env rst_type ckr)
                             SC.init_state = OK (rstty0, SC.init_state)).
                 {
                   eapply option_to_sec_assign_clk_state_irrel.
                   exact Hrst0.
                 }
                 assert (Hinp0_init :
                           SC.mmap
                             (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                             exps SC.init_state = OK (inptyp0, SC.init_state)).
                 {
                   eapply mmap_assign_exp_type_state_irrel.
                   exact Hinp0.
                 }
                 pose proof
                   (Hresetsec_node
                      (xh :: xt) ck f exps r ckr callee nsig_c
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0)
                   as Hcallee_secure.
                 destruct Hcallee_secure as
                     [ty_env_c sig_c
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Hfindcallee_sec Hfindenv_c Hfindsig_c Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_c Hsatsig_c Hagree_c Hsatraw_c
                      Hcallsec_c Hresetsec_c].
                 pose proof (proj1 (find_node_In _ _ _ Hfindcallee)) as Hcallee_name.
                 rewrite Hcallee_name in Hfindsig_c.
                 rewrite Hfindsigc in Hfindsig_c.
                 assert (Hsig_eq : nsig_c = sig_c).
                 { inversion Hfindsig_c; reflexivity. }
                 subst nsig_c.
                 pose
                   (callee_sig_cur :=
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 rewrite Hsigdef_c in Hfindsig_c, Hfindsigc, Hsiggen_c,
                   Hsatsig_c, Hagree_c, Hcallsec_c, Hresetsec_c.
                 set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
                 set (dlt_sig_c :=
                        SIGPROOFS.inst_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 assert (Hwcapp :
                           Clo.wc_equation P
                             (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 {
                   rewrite Forall_forall in Hwc_eqs.
                   exact (Hwc_eqs _ Heqin).
                 }
                 inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                                       Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
                 assert
                   (Hvars_scoped :
                      SECNLUSTYPING.vars_env_scoped ty_env
                        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        caller_scope).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
                     eauto.
                 }
                 assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp0).
                 {
                   eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
                     with (scope := caller_scope)
                          (es := exps)
                          (st := SC.init_state)
                          (st' := SC.init_state); eauto.
                   eapply SECNLUSTYPING.wc_call_args_scoped
                     with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                          (scope := caller_scope)
                          (sub := sub)
                          (ck := ck)
                          (ins := n0.(n_in)); eauto.
                 }
                 assert
                   (Hfree_clock_scope :
                      forall z,
                        Is_free_in_clock z ck ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
                   exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_ck :
                      SECCETYPING.assign_clk_type ty_env clk_type ck = Some ckty0).
                 {
                   unfold SC.option_to_sec in Hck0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
                     eqn:Hassign; simpl in Hck0_init; try discriminate.
                   inversion Hck0_init; now subst ckty'.
                 }
                 assert (Hck_scope : SecT.st_scoped caller_scope ckty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := clk_type) (ck := ck).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now left.
                   - exact Hfree_clock_scope.
                   - exact Hassign_ck.
                 }
                 assert (Hr_scope : SecT.st_scoped caller_scope [rty0]).
                 {
                   apply SecT.st_scoped_singleton.
                   assert (Hinr_pair :
                             In (r, ckr)
                               (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   destruct (Hvars_scoped r) as (ty0 & Hfindr & Hinscope).
                   - eapply In_InMembers. exact Hinr_pair.
                   - rewrite Hr0 in Hfindr.
                     inversion Hfindr; subst ty0.
                     exact Hinscope.
                 }
                 assert
                   (Hfree_rclock_scope :
                      forall z,
                        Is_free_in_clock z ckr ->
                        exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
                 {
                   intros z Hz.
                   assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply wc_reset_in_call_vars; eauto. }
                   assert (Hwr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ckr).
                   { eapply wc_env_var; eauto. }
                   destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
                   - eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto.
                   - exists ty0; split; [exact Hfindz|exact Hinscope].
                 }
                 assert
                   (Hassign_rst :
                      SECCETYPING.assign_clk_type ty_env rst_type ckr = Some rstty0).
                 {
                   unfold SC.option_to_sec in Hrst0_init.
                   destruct (SECCETYPING.assign_clk_type ty_env rst_type ckr) as [rstty'|]
                     eqn:Hassign; simpl in Hrst0_init; try discriminate.
                   inversion Hrst0_init; now subst rstty'.
                 }
                 assert (Hrst_scope : SecT.st_scoped caller_scope rstty0).
                 {
                   eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_type) (ck := ckr).
                   - simpl. repeat (apply in_or_app; right).
                     simpl. now right; left.
                   - exact Hfree_rclock_scope.
                   - exact Hassign_rst.
                 }
                 assert (Hrst_join_scope : SecT.st_scoped caller_scope ([rty0] ⊔ rstty0)).
                 {
                   eapply SecT.st_scoped_merge; eauto.
                 }
                 assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp0).
                 {
                   rewrite Forall_forall.
                   intros ty Hty.
                   pose proof
                     (eqapp_outtyp_in_out_or_locals
                        n ty_env out locals (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) outtyp0 ty
                        Heqin Hout0 Hout Hlocals Hty)
                     as Hin_out_or_locals.
                   replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
                   - apply in_or_app. right.
                     eapply In_app_weaken_right.
                     exact Hin_out_or_locals.
                   - unfold caller_scope.
                     repeat rewrite <- app_assoc.
                     reflexivity.
                 }
                 assert (Hscopefresh :
                           SIG.scope_fresh caller_scope callee_sig_cur).
                 {
                   eapply generated_caller_scope_fresh_scoped_env
                     with (caller := n)
                          (callee := callee)
                          (caller_env := ty_env)
                          (callee_env := ty_env_c)
                          (clk_id := clk_id)
                          (rst_id := rst_id)
                          (clk_type := clk_type)
                          (rst_type := rst_type)
                          (inp := inp)
                          (out := out)
                          (locals := locals); eauto.
                 }
                 assert (Hndscope_c :
                           NoDup (SIG.signature_scope callee_sig_cur)).
                 {
                   eapply generated_sig_scope_nodup_scoped_env
                     with (n := callee)
                          (ty_env := ty_env_c)
                          (clk_id := clk_id_c)
                          (rst_id := rst_id_c)
                          (clk_type := clk_type_c)
                          (rst_type := rst_type_c)
                          (inp := inp_c)
                          (out := out_c); eauto.
                 }
                 assert (Hfresh_call :
                           SIG.call_subst_fresh callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0).
                 {
                   eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
                 }
                 pose proof
                   (generate_constraints_lengths
                      callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      ceq st_inp0 stceq Hcallc)
                   as [Hlen_in_c Hlen_out_c].
                 destruct
                   (mmap_assign_exp_type_inv ty_env exps inptyp0 st_rst0 st_inp0 Hinp0)
                   as [_ Hforinp0].
                 pose proof
                   (SIGPROOFS.inst_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.inst_valuation_outputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_out_c)
                   as Hinst_out_eq.
                 assert (Hsatceq : SecT.listSatisfiable dlt_raw ceq).
                 {
                   pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                     as Hmid.
                   specialize (Hmid Hsatraw).
                   exact Hmid.
                 }
                 assert (HgoodG : SIG.secglobal_good G).
                 {
                   eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env.
                   - exact Henvsgen.
                   - exact Hwcglob.
                   - exact Hallsig.
                 }
                 assert (Hsiggood_c : SIG.signature_good callee_sig_cur).
                 {
                   eapply HgoodG.
                   exact Hfindsigc.
                 }
                 assert
                   (Hresetlhs_c :
                      forall y lhs,
                        findST callee_sig_cur.(s_constraints) y = Some lhs ->
                        In callee_sig_cur.(s_reset) lhs).
                 {
                   intros y lhs Hfindlhs.
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_reset_scoped_env
                        all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                   - exact Henvsgen.
                   - exact Hwcglob.
                   - exact Hallsig.
                   - exact Hfindsigc.
                   - exact Hfindlhs.
                 }
                 assert (Hlowxty0 : dlt_raw xty0 ⊑ t).
                 {
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha.
                   exact Halpha_low.
                 }
                 assert (Hi_out : i < length (s_out callee_sig_cur)).
                 {
                   rewrite Hlen_out_c.
                   apply nth_error_Some.
                   rewrite Hnthout.
                   discriminate.
                 }
                 destruct (nth_error (s_out callee_sig_cur) i) as [yty|] eqn:Hnthyty.
                 2:{
                   apply nth_error_None in Hnthyty.
                   lia.
                 }
                 assert (Hlow_rst_join : SecT.hm_ext dlt_raw ([rty0] ⊔ rstty0) ⊑ t).
                 {
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_reset_low
                        callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 ceq st_inp0 stceq
                        dlt_raw t i yty xty0); eauto.
                 }
                 assert
                   (Hclocklhs_c :
                      forall y lhs,
                        findST callee_sig_cur.(s_constraints) y = Some lhs ->
                        In callee_sig_cur.(s_clk) lhs).
                 {
                   intros y lhs Hfindlhs.
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.generated_signature_constraints_mention_clock_scoped_env
                        all_nodes envs aux_names G callee.(n_name) callee_sig_cur y lhs).
                   - exact Henvsgen.
                   - exact Hwcglob.
                   - exact Hallsig.
                   - exact Hfindsigc.
                   - exact Hfindlhs.
                 }
                 assert (Hlowr : low_var ty_env dlt_raw t r).
                 {
                   exists rty0.
                   split; [exact Hr0|].
                   apply order_trans with (y := SecT.hm_ext dlt_raw [rty0]).
                   - apply singleton_type_bound.
                   - apply order_trans with (y := SecT.hm_ext dlt_raw ([rty0] ⊔ rstty0)).
                     + apply SecT.hm_ext_concat_l.
                     + exact Hlow_rst_join.
                 }
                 assert (Hlow_ck : SecT.hm_ext dlt_raw ckty0 ⊑ t).
                 {
                   eapply
                     (SECNLUSTYPINGCORRECTNESS.call_output_low_implies_clock_low
                        callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 ceq st_inp0 stceq
                        dlt_raw t i yty xty0).
                   - exact Hsiggood_c.
                   - exact Hclocklhs_c.
                   - exact Hfresh_call.
                   - exact Hndscope_c.
                   - exact Hlen_in_c.
                   - exact Hlen_out_c.
                   - exact Hcallc.
                   - exact Hsatceq.
                   - exact Hnthyty.
                   - exact Hnthout.
                   - exact Hlowxty0.
                 }
                 assert (Hreset_ctrlm :
                           reset_control_low_eq_upto ty_env dlt_raw t r H H' m).
                 {
                   eapply reset_control_low_eq_upto_of_sem_var_eq.
                   intros Hlowr1 j Hj.
                   destruct
                     (reset_var_in_inputs_or_defined
                        P n (xh :: xt) ck callee.(n_name) exps r ckr
                        Hwcnode Heqin)
                     as [Hin_r|Hdef_r].
                   - eapply Hlowin; eauto.
                   - destruct (Nat.eq_dec j m) as [Heqj|Hneqj].
                     + subst j.
                       assert (Hdep_xr :
                                 NLCaus.nl_depends_on_eq
                                   (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x r).
                       {
                         split; [exact Hxdef|].
                         right. left. reflexivity.
                       }
                       exact (Hdeps r Hdep_xr Hlowr1).
                     + eapply Hprev; eauto. lia.
                 }
                 assert (Hcount_eq :
                           forall j, j <= m -> count rs j = count rs' j).
                 {
                   intros j Hj.
                   exact (Hreset_ctrlm rys rys' rs rs' Hsem_var_r Hsem_var_r'
                            Hbools_r Hbools_r' Hlowr j Hj).
                 }
                 assert (Hclock_eq_rawm : clock_eq_upto (clock_of ls) (clock_of ls') m).
                 {
                   intros j Hj.
                   eapply sem_clock_eq_upto_from_env_eq
                     with (bk := bk) (bk' := bk') (H := H) (H' := H') (ck := ck) (k := m).
                   - exact Hsem_clock.
                   - exact Hsem_clock'.
                   - exact Hclock_eq.
                   - intros z Hz j0 Hj0.
                     destruct (Hfree_clock_scope z Hz) as (ty0 & Hfindz & _).
                     assert (Hlowz : low_var ty_env dlt_raw t z).
                     {
                       exists ty0.
                       split; [exact Hfindz|].
                       eapply order_trans.
                       1:{
                         eapply SecT.hm_ext_list_in1.
                         eapply (assign_clk_type_free_var_in ty_env clk_type ck ckty0 z ty0).
                         - exact Hassign_ck.
                         - exact Hz.
                         - exact Hfindz.
                       }
                       exact Hlow_ck.
                     }
                     assert (Hdep_xz :
                               NLCaus.nl_depends_on_eq
                                 (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
                     {
                       split; [exact Hxdef|].
                       left.
                       apply freeAexps2.
                       exact Hz.
                     }
                     destruct (Nat.eq_dec j0 m) as [Heqj0|Hneqj0].
                     + subst j0.
                       exact (Hdeps z Hdep_xz Hlowz).
                     + assert (Hjlt : j0 < S k).
                       {
                         unfold m in Hj0, Hneqj0.
                         destruct (Nat.compare_spec j0 (S k)) as [Heq|Hlt|Hgt].
                         - exfalso. apply Hneqj0. exact Heq.
                         - exact Hlt.
                         - exfalso.
                           eapply Nat.lt_irrefl.
                           eapply Nat.lt_le_trans; eauto.
                       }
                       eapply
                         (free_clock_low_eq_prefix_from_inputs_or_defined
                            P n ty_env dlt_raw t H H' (xh :: xt) ck callee.(n_name) exps
                            (Some (r, ckr)) z k);
                         eauto.
                   - exact Hj.
                 }
                 assert (Hkr_eq : kr = count rs m).
                 { unfold kr. reflexivity. }
                 assert (Hkr'_eq : kr' = count rs' m).
                 { unfold kr'. reflexivity. }
                 assert
                   (Hclock_eqm :
                      clock_eq_upto (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) m).
                 {
                   intros j Hj.
                   eapply clock_of_mask_eq_upto; eauto.
                 }
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' m).
                 {
                   unfold dlt_raw_c.
                   eapply
                     (succ_eqapp_reset_inputs_low_eq_upto_clocked
                        P n ty_env ty_env_c dlt_raw t
                        H H' Hc Hc' bk bk'
                        xh xt ck callee exps r ckr x k
                        inp_c inptyp0 outtyp0 ckty0 ([rty0] ⊔ rstty0) callee_sig_cur
                        rs rs' kr kr' ls ls').
                   - exact Hwcnode.
                   - exact Heqin.
                   - exact Hxdef.
                   - exact Hdeps.
                   - exact Hlowin.
                   - exact Hprev.
                   - exact Hclock_eq.
                   - reflexivity.
                   - exact Hinp_c.
                   - exact Hforinp0.
                   - exact Hinst_in_eq.
                   - exact Hkr_eq.
                   - exact Hkr'_eq.
                   - exact Hcount_eq.
                   - exact Hsem_exps.
                   - exact Hsem_exps'.
                   - exact Hsem_vars_in_c.
                   - exact Hsem_vars_in_c'.
                 }
                 assert (Hcallee_secure :
                           node_security all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c).
                 {
                   eapply SecureNode; eauto.
                 }
                 pose proof
                   (Hresetout
                      (xh :: xt) ck callee.(n_name) exps r ckr callee callee_sig_cur
                      ckty0 rty0 rstty0 inptyp0 outtyp0
                      SC.init_state SC.init_state SC.init_state
                      Heqin Hfindcallee Hfindsigc Hck0_init Hr0 Hrst0_init Hinp0_init Hout0
                      m Hreset_ctrlm)
                   as Hcallee_out_raw.
                 assert
                   (Hsigdef_cur :
                      callee_sig_cur =
                      {| s_name := callee.(n_name);
                         s_in := inp_c;
                         s_out := out_c;
                         s_reset := rst_type_c;
                         s_clk := clk_type_c;
                         s_constraints := SymTypes.simplify raw_c locals_c |}).
                 {
                   unfold callee_sig_cur.
                   reflexivity.
                 }
                 specialize
                   (Hcallee_out_raw
                      m ty_env_c callee_sig_cur t
                      (clock_of (mask kr rs ls)) (clock_of (mask kr' rs' ls')) Hc Hc'
                      clk_id_c rst_id_c clk_type_c rst_type_c
                      inp_c out_c locals_c raw_c st_n_c
                      Henvsgen Hord Hwcglob Hallsig Hcaus
                      Hfindcallee Hfindenv_c Hfindsigc Hsiggen_c
                      Haux_c Hclk_c Hrst_c Hinp_c Hout_c Hlocals_c
                      Hraw_c Hsigdef_cur Hcallee_secure
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hclock_eqm Hlowin_c).
                 pose proof
                   (get_mappings_from_node_eq _ _ _ _ Hout_c)
                   as Hout_c_eq.
                 assert (Hiout : i < List.length (map fst callee.(n_out))).
                 {
                   pose proof (get_mappings_length _ _ _ Hout_c_eq) as Hlen_mapout.
                   unfold callee_sig_cur in Hlen_out_c.
                   simpl in Hlen_out_c.
                   assert (Hiout0 : i < List.length outtyp0).
                   {
                     apply nth_error_Some.
                     rewrite Hnthout.
                     discriminate.
                   }
                   lia.
                 }
                 destruct (nth_error (map fst callee.(n_out)) i) as [yo|] eqn:Hnthyo.
                 2:{
                   apply nth_error_None in Hnthyo.
                   lia.
                 }
                 destruct
                   (get_mappings_nth_error_inv
                      (map fst callee.(n_out)) ty_env_c out_c i yo Hout_c_eq Hnthyo)
                   as (yty_out2 & Hnthyty2 & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty_out2.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty2.
                   simpl in Hnthyty2.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty_out2
                        Hinst_out_eq Hnthyty2)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.inst_valuation_outside_sig_scope
                              dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0 xty0).
                   - exact Halpha_low.
                   - unfold SIG.outputs_fresh in Houtfresh.
                     rewrite Forall_forall in Houtfresh.
                     apply Houtfresh.
                     eapply SecT.nth_error_In_local.
                     exact Hnthout.
                 }
                 eapply
                   (eqapp_reset_output_transport_pointwise
                      ty_env_c dlt_raw_c t
                      H H' Hc Hc' callee
                      (xh :: xt) ys ys' rs rs' kr kr' m i x yo); eauto.
              }
            * assert (Hx : x = x0).
              { simpl in Hxdef. intuition. }
              subst x.
              assert (Hsem_eq : Indexed.sem_equation all_nodes bk H (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk' H' (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq as
                  [| | | ? ? ? ? ? ? ? ? Hfby_aexpS Hfby_varS Hfby_eqS];
                subst; clear Hsem_eq.
              inversion Hsem_eq' as
                  [| | | ? ? ? ? ? ? ? ? Hfby_aexpS' Hfby_varS' Hfby_eqS'];
                subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member G
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqFby x0 ck c0 e) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqfby_constraint_inv G
                   ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
                as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply
                (eqfby_noninterference_delayed_pointwise_clocked
                   bk bk' H H' x0 _ _ _ _ ck c0 e m).
              -- intros y Hclock.
                 assert (Hlowy : low_var ty_env dlt_raw t y).
                 {
                   refine
                     (simple_security_aexp
                        ty_env dlt_raw t
                        clk_type rst_type
                        x0 ck e
                        xty0 ckty0 ety0 y
                        _ _ _ _ _ _).
                   - exact Hfindx0.
                   - exact Hck0.
                   - exact He0.
                   - exact Hsat1.
                   - exact Hlowx.
                   - exact (freeAexp2 _ _ _ Hclock).
                 }
                 assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqFby x0 ck c0 e) x0 y).
                 { split; [reflexivity|exact Hclock]. }
                 exact (Hdeps y Hdep_xy Hlowy).
              -- intros y Hfree j Hjlt.
                 assert (Hlowy : low_var ty_env dlt_raw t y).
                 {
                   refine
                     (simple_security_aexp
                        ty_env dlt_raw t
                        clk_type rst_type
                        x0 ck e
                        xty0 ckty0 ety0 y
                        _ _ _ _ _ _).
                   - exact Hfindx0.
                   - exact Hck0.
                   - exact He0.
                   - exact Hsat1.
                   - exact Hlowx.
                   - exact Hfree.
                 }
                 eapply free_aexp_low_eq_prefix_from_inputs_or_defined
                   with (P := P) (n := n) (x := x0) (ck := ck) (c0 := c0) (e := e)
                        (ty_env := ty_env) (dlt := dlt_raw) (t := t) (k := k); eauto.
              -- intros j Hjlt.
                 exact (Hclock_eq j (Nat.lt_le_incl _ _ Hjlt)).
              -- exact (Hclock_eq m (le_n m)).
              -- exact Hfby_varS.
              -- exact Hfby_aexpS.
              -- reflexivity.
              -- exact Hfby_varS'.
              -- exact Hfby_aexpS'.
              -- reflexivity.
          + assert (Hinputs_cur :
                       Forall
                         (fun x0 : ident =>
                            low_var ty_env dlt_raw t x0 ->
                            Env.find x0 (H m) = Env.find x0 (H' m))
                         (map fst n.(n_in))).
            {
              pose proof
                (history_low_eq_upto_inputs_pointwise n ty_env dlt_raw t H H' m Hlowin)
                as Hinputs.
              rewrite Forall_forall in *.
              intros x0 Hin Hobs.
              exact (Hinputs x0 Hin Hobs m (le_n m)).
            }
            exact Hinputs_cur.
          + eapply NLCaus.nl_global_causal_find; eauto.
        }
        eapply history_low_eq_upto_succ_intro; eauto.
        intros x Hinx Hlowx.
        rewrite Forall_forall in Hpts_cur.
        eapply Hpts_cur; eauto.
    Qed.

  End GENERATED_NODE_NONINTERFERENCE_CLOCKED_STEP.

End SECNLUSNONINTERFERENCECLOCKEDSTEP.

Module SecNLusNonInterferenceClockedStep
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
  <: SECNLUSNONINTERFERENCECLOCKEDSTEP Ids Lat Op OpAux SC SecT CESyn SynNL
       SIG NAMEGEN SECCETYPING CETyp CEIsF CEClo Str Ord Mem IsD IsF NLCaus
       Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS.

Include SECNLUSNONINTERFERENCECLOCKEDSTEP
  Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
  CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS
  SECNLUSTYPING SECNLUSTYPINGCORRECTNESS.

End SecNLusNonInterferenceClockedStep.
