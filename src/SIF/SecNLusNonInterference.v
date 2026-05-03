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
    Lemma succ_eqapp_nonreset_inputs_low_eq_upto:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
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
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps x k
             inp_c inptyp outtyp ckty rstty callee_sig ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev
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
        (eqapp_input_var_low_eq_pointwise
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt_raw rstty ckty obs
           bk H H' Hc Hc' exps ls ls'
           j ii y ity e ety); eauto.
    Qed.

    (** Successor-step transport of reset-call inputs from caller equality.

        Relation to the paper:
        this is the reset-aware analogue of
        [succ_eqapp_nonreset_inputs_low_eq_upto].  The recursive callee run
        is taken on one masked reset segment, so the proof must additionally
        split on whether a past instant still belongs to that active segment
        or lies in an opaque, fully absent prefix. *)
    Lemma succ_eqapp_reset_inputs_low_eq_upto:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
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
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps r ckr x k
             inp_c inptyp outtyp ckty rstty callee_sig
             rs rs' kr kr' ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev
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
          (eqapp_reset_input_var_low_eq_pointwise
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt_raw rstty ckty obs
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety); eauto.
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

    (** Base-step case of [node_noninterference_vars_defined_step].

        Relation to the paper:
        this packages the [k = 0] branch of the indexed noninterference
        induction as a standalone proof artifact.  The semantic argument is
        unchanged; the extraction is only to keep the main theorem shell small
        enough for Coq to replay predictably. *)
    Lemma node_noninterference_vars_defined_step_base:
      forall n dlt_sig dlt_raw
             ty_env sig t bk H H'
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
            node_outputs_raw_spec all_nodes G envs aux_names callee
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
            node_outputs_raw_spec all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)) ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst n.(n_in)) H H' 0 ->
        history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' 0.
    Proof.
      intros n dlt_sig dlt_raw
             ty_env sig t bk H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Henvsgen Hord Hwcglob Hallsig Hcaus Hfindnode Hfindenv
             Hfindsig Hsiggen Haux Hclk Hrst Hinp Hout Hlocals Hraw
             Hsigdef Hsecure Hcallout Hresetout Hsatraw Hsem Hsem' Hlowin.
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
            assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqDef x0 ck ce)).
            { eapply Forall_forall; eauto. }
            inversion Hsem_eq; subst; clear Hsem_eq.
            inversion Hsem_eq'; subst; clear Hsem_eq'.
            destruct
              (generate_eqns_constraints_member
                 G
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqDef x0 ck ce) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqdef_constraint_inv
                 G
                 ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
              as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
            assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
            {
              rewrite Hcns in Hmid.
              inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
              inversion Hnil; subst; clear Hnil.
              exact Hsat_ceq.
            }
            eapply eqdef_noninterference_instant_pointwise; eauto.
            intros y Hfree.
            assert (Hlowy : low_var ty_env dlt_raw t y).
            {
              eapply simple_security_caexp; eauto.
            }
            assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
            { split; [reflexivity|exact Hfree]. }
            specialize (Hdeps y Hdep_xy Hlowy 0 (le_n 0)).
            exact Hdeps.
          * destruct xs as [|xh xt].
            { simpl in Hxdef. contradiction. }
            destruct r as [[r ckr]|].
            2:{
               assert (Hsem_eq :
                         Indexed.sem_equation all_nodes bk H
                           (EqApp (xh :: xt) ck f exps None)).
               { eapply Forall_forall; eauto. }
               assert (Hsem_eq' :
                         Indexed.sem_equation all_nodes bk H'
                           (EqApp (xh :: xt) ck f exps None)).
               { eapply Forall_forall; eauto. }
               destruct
                 (generate_eqns_constraints_member
                    G
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqapp_constraint_inv
                    G
                    ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                 as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                     & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
               destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
               destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                 as (xty0 & Hnthout & Hfindx0).
               destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                 as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
               destruct (sem_eqapp_inv all_nodes bk H' (xh :: xt) ck f exps Hsem_eq')
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
                   (eqapp_input_var_low_eq_pointwise
                      ty_env ty_env_c callee callee_sig_cur
                      inptyp0 outtyp0 dlt_raw [rst_type] ckty0 t
                      bk H H' Hc Hc' exps ls ls' 0 ii y ity e ety); eauto.
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
                    Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
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
                 as (yty & Hnthyty & Hfindyo).
               assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
               {
                 exists yty.
                 split; [exact Hfindyo|].
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha; clear Hfindalpha.
                 unfold callee_sig_cur in Hnthyty.
                 simpl in Hnthyty.
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun x v =>
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           [rst_type] outtyp0 v =
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           [rst_type] outtyp0 x)
                      (s_out callee_sig_cur) outtyp0 i yty
                      Hinst_out_eq Hnthyty)
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
                         Indexed.sem_equation all_nodes bk H'
                           (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
               { eapply Forall_forall; eauto. }
               destruct
                 (generate_eqns_constraints_member
                    G
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqreset_constraint_inv
                    G
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
                 (sem_eqreset_inv all_nodes bk H' (xh :: xt) ck f exps r ckr Hsem_eq')
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
                   (eqapp_reset_input_var_low_eq_pointwise
                      ty_env ty_env_c callee callee_sig_cur
                      inptyp0 outtyp0 dlt_raw ([rty0] ⊔ rstty0) ckty0 t
                      bk H H' Hc Hc' exps rs rs' kr kr' ls ls' 0 ii y ity e ety); eauto.
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
                    Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
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
                 as (yty & Hnthyty & Hfindyo).
               assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
               {
                 exists yty.
                 split; [exact Hfindyo|].
                 destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                 rewrite Hfindx0 in Hfindalpha.
                 inversion Hfindalpha; subst alpha; clear Hfindalpha.
                 unfold callee_sig_cur in Hnthyty.
                 simpl in Hnthyty.
                 destruct
                   (SecT.Forall2_nth_error_inv
                      _ _
                      (fun x0 v =>
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           ([rty0] ⊔ rstty0) outtyp0 v =
                         SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                           ([rty0] ⊔ rstty0) outtyp0 x0)
                      (s_out callee_sig_cur) outtyp0 i yty
                      Hinst_out_eq Hnthyty)
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
               assert (Hkr_eq : kr = count rs 0).
               { unfold kr. reflexivity. }
               assert (Hkr'_eq : kr' = count rs' 0).
               { unfold kr'. reflexivity. }
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
            assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqFby x0 ck c0 e)).
            { eapply Forall_forall; eauto. }
            inversion Hsem_eq; subst; clear Hsem_eq.
            inversion Hsem_eq'; subst; clear Hsem_eq'.
            destruct
              (generate_eqns_constraints_member
                 G
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqFby x0 ck c0 e) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqfby_constraint_inv
                 G
                 ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
              as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
            assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
            {
              rewrite Hcns in Hmid.
              inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
              inversion Hnil; subst; clear Hnil.
              exact Hsat_ceq.
            }
            eapply eqfby_noninterference_delayed_pointwise; eauto.
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
        + eapply history_low_eq_upto_inputs_pointwise; eauto.
        + eapply NLCaus.nl_global_causal_find; eauto.
      }
      eapply history_low_eq_upto_from_Forall_pointwise; eauto.
    Qed.

    Theorem node_noninterference_vars_defined_step:
      forall n dlt_sig dlt_raw k
             ty_env sig t bk H H'
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
            node_outputs_raw_spec all_nodes G envs aux_names callee
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
            node_outputs_raw_spec all_nodes G envs aux_names callee
              (SIGPROOFS.inst_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)) ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) n.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk H') n.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst n.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (vars_defined n.(n_eqs)) H H' k.
    Proof.
      intros n dlt_sig dlt_raw k.
      induction k as [|k IHk];
        intros ty_env sig t bk H H'
               clk_id rst_id clk_type rst_type inp out locals raw st_n
               Henvsgen Hord Hwcglob Hallsig Hcaus Hfindnode Hfindenv
               Hfindsig Hsiggen Haux Hclk Hrst Hinp Hout Hlocals Hraw
               Hsigdef Hsecure Hcallout Hresetout Hsatraw Hsem Hsem' Hlowin.
      - eapply node_noninterference_vars_defined_step_base; eauto.
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
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqDef x0 ck ce)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   G
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqDef x0 ck ce) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqdef_constraint_inv
                   G
                   ty_env clk_type rst_type x0 ck ce ceq steq stceq Hgeq)
                as (ckty0 & cety0 & xty0 & Hcns & Hck0 & Hce0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ cety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqdef_noninterference_instant_pointwise; eauto.
              intros y Hfree.
              assert (Hlowy : low_var ty_env dlt_raw t y).
              {
                eapply simple_security_caexp; eauto.
              }
              assert (Hdep_xy : NLCaus.nl_depends_on_eq (EqDef x0 ck ce) x0 y).
              { split; [reflexivity|exact Hfree]. }
              exact (Hdeps y Hdep_xy Hlowy).
            * destruct xs as [|xh xt].
              { simpl in Hxdef. contradiction. }
              destruct r as [[r ckr]|].
              2:{
                 assert (Hsem_eq :
                           Indexed.sem_equation all_nodes bk H
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 assert (Hsem_eq' :
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps None)).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      G
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqapp_constraint_inv
                      G
                      ty_env clk_type rst_type xh xt ck f exps ceq steq stceq Hgeq)
                   as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0
                       & Hfindsigc & Hck0 & Hinp0 & Hout0 & Hcallc).
                 destruct (SecT.In_nth_error_ex _ _ _ Hxdef) as [i Hnthx].
                 destruct (get_mappings_nth_error_inv (xh :: xt) ty_env outtyp0 i x Hout0 Hnthx)
                   as (xty0 & Hnthout & Hfindx0).
                 destruct (sem_eqapp_inv all_nodes bk H (xh :: xt) ck f exps Hsem_eq)
                   as (ls & ys & Hsem_exps & Hsem_vars_out & Hsem_clock & Hsem_node_c).
                 destruct (sem_eqapp_inv all_nodes bk H' (xh :: xt) ck f exps Hsem_eq')
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
                     (succ_eqapp_nonreset_inputs_low_eq_upto
                        P n ty_env ty_env_c dlt_raw t
                        H H' Hc Hc' bk
                        xh xt ck callee exps x k
                        inp_c inptyp0 outtyp0 ckty0 [rst_type] callee_sig_cur ls ls');
                     eauto.
                 }
                 assert (Hcallee_secure :
                           node_security all_nodes G envs aux_names callee dlt_sig_c dlt_raw_c).
                 {
                   eapply SecureNode; eauto.
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
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
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
                   as (yty_out & Hnthyty & Hfindyo).
                 assert (Hlowyo : low_var ty_env_c dlt_raw_c t yo).
                 {
                   exists yty_out.
                   split; [exact Hfindyo|].
                   destruct Hlowx as (alpha & Hfindalpha & Halpha_low).
                   rewrite Hfindx0 in Hfindalpha.
                   inversion Hfindalpha; subst alpha; clear Hfindalpha.
                   unfold callee_sig_cur in Hnthyty.
                   simpl in Hnthyty.
                   destruct
                     (SecT.Forall2_nth_error_inv
                        _ _
                        (fun x0 v =>
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 v =
                           SIGPROOFS.inst_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty_out
                        Hinst_out_eq Hnthyty)
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
                           Indexed.sem_equation all_nodes bk H'
                             (EqApp (xh :: xt) ck f exps (Some (r, ckr)))).
                 { eapply Forall_forall; eauto. }
                 destruct
                   (generate_eqns_constraints_member
                      G
                      ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                      (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                   as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
                 destruct
                   (generate_eqreset_constraint_inv
                      G
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
                   (sem_eqreset_inv all_nodes bk H' (xh :: xt) ck f exps r ckr Hsem_eq')
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
                 assert (Hlowin_c :
                           history_low_eq_upto ty_env_c dlt_raw_c t
                             (map fst callee.(n_in)) Hc Hc' m).
                 {
                   unfold dlt_raw_c.
                   eapply
                     (succ_eqapp_reset_inputs_low_eq_upto
                        P n ty_env ty_env_c dlt_raw t
                        H H' Hc Hc' bk
                        xh xt ck callee exps r ckr x k
                        inp_c inptyp0 outtyp0 ckty0 ([rty0] ⊔ rstty0) callee_sig_cur
                        rs rs' kr kr' ls ls');
                     eauto.
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
                      Hsatraw_c Hsem_eqs_c Hsem_eqs_c' Hlowin_c).
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
                 assert (Hkr_eq : kr = count rs m).
                 { unfold kr. reflexivity. }
                 assert (Hkr'_eq : kr' = count rs' m).
                 { unfold kr'. reflexivity. }
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
              assert (Hsem_eq' : Indexed.sem_equation all_nodes bk H' (EqFby x0 ck c0 e)).
              { eapply Forall_forall; eauto. }
              inversion Hsem_eq; subst; clear Hsem_eq.
              inversion Hsem_eq'; subst; clear Hsem_eq'.
              destruct
                (generate_eqns_constraints_member
                   G
                   ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                   (EqFby x0 ck c0 e) Heqin Hraw)
                as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
              pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
                as Hmid.
              rewrite Hsplit in Hsatraw.
              specialize (Hmid Hsatraw).
              destruct
                (generate_eqfby_constraint_inv
                   G
                   ty_env clk_type rst_type x0 ck c0 e ceq steq stceq Hgeq)
                as (ckty0 & ety0 & xty0 & Hcns & Hck0 & He0 & Hfindx0).
              assert (Hsat1 : SecT.satisfiable dlt_raw ((([rst_type] ⊔ ckty0) ⊔ ety0)) [xty0]).
              {
                rewrite Hcns in Hmid.
                inversion Hmid as [|? ? Hsat_ceq Hnil]; subst; clear Hmid.
                inversion Hnil; subst; clear Hnil.
                exact Hsat_ceq.
              }
              eapply eqfby_noninterference_delayed_pointwise; eauto.
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

    (** Internal raw output theorem.

        Relation to the paper:
        this is not part of the public statement of noninterference.  It is
        the proof-internal theorem that should be derived from the paired
        [node_security] predicate and then used to recover the canonical
        output theorem. *)
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
        eapply SecureNode; eauto.
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
    Proof.
      intros n ty_env nsig dlt_sig dlt_raw t bk H H'
             Henvsgen Hord Hwcglob Hallsig Hcaus
             Hfindnode Hfindenv Hfindsig
             Hsecure Hsem Hsem' Hlowin.
      destruct Hsecure as
          [ty_env_sec sig_sec
           clk_id_sec rst_id_sec clk_type_sec rst_type_sec
           inp_sec out_sec locals_sec raw_sec st_n_sec
           Hfindnode_sec Hfindenv_sec Hfindsig_sec Hsiggen_sec
           Haux_sec Hclk_sec Hrst_sec Hinp_sec Hout_sec Hlocals_sec
           Hraw_sec Hsigdef_sec Hsatsig_sec Hagree_sec Hsatraw_sec
           Hcallsec_sec Hresetsec_sec].
      rewrite Hfindenv in Hfindenv_sec.
      inversion Hfindenv_sec; subst ty_env_sec; clear Hfindenv_sec.
      rewrite Hfindsig in Hfindsig_sec.
      inversion Hfindsig_sec; subst sig_sec; clear Hfindsig_sec.
      assert (Hsecure_cur :
                node_security all_nodes G envs aux_names n dlt_sig dlt_raw).
      {
        eapply SecureNode; eauto.
      }
      assert
        (Hscope_in :
           forall x,
             In x (map fst n.(n_in)) ->
             exists alpha,
               Env.find x ty_env = Some alpha
               /\ In alpha (signature_scope nsig)).
      {
        intros x Hinx.
        apply in_map_iff in Hinx as ((xin, ckin) & Heq & Hinpair).
        simpl in Heq. subst xin.
        apply In_InMembers in Hinpair.
        destruct
          (get_mappings_from_node_inmembers _ _ _ _ _ Hinpair Hinp_sec)
          as (alpha & Hfindalpha & Hinalpha).
        exists alpha.
        split; [exact Hfindalpha|].
        rewrite Hsigdef_sec.
        unfold signature_scope.
        apply in_or_app.
        left.
        exact Hinalpha.
      }
      assert
