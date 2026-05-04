(* Mainline copy layer for the NLustre noninterference step theorem.

   This file exists to decouple ongoing proof-architecture work on the
   top-level step theorem from the already-stabilized helper file.

   Relation to the paper:
   the paper's node-level noninterference argument is built around one
   equation-step theorem.  The original helper file now contains a stable
   one-clock version of that theorem.  This file is the designated place to
   evolve the next version of that step theorem, in particular the
   two-clock/current-node generalization needed by the raw output theorem,
   without forcing every edit through the older helper stack. *)

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
    Admitted.

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
    Admitted.

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
