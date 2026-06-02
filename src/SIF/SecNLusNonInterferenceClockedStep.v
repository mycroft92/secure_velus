(** Clocked step lemma used in the NLustre noninterference proof. *)

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

    (** This is the main successor-step theorem for a secure node.  It combines the local transport lemmas with clock alignment to extend low-equivalence from the observed prefix to the next instant for all currently defined low variables.  The final node-output theorem applies this step result throughout the indexed execution. *)
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
              (SIGPROOFS.lat_valuation dlt_sig callee_sig inptyp ckty
                 [sig.(s_reset)] outtyp)
              (SIGPROOFS.lat_valuation dlt_raw callee_sig inptyp ckty
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
              (SIGPROOFS.lat_valuation dlt_sig callee_sig inptyp ckty
                 ([rty] ⊔ rstty) outtyp)
              (SIGPROOFS.lat_valuation dlt_raw callee_sig inptyp ckty
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
                        SIGPROOFS.lat_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          [rst_type] outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
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
                   (SIGPROOFS.lat_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 [rst_type] outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.lat_valuation_outputs_eq
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
                           SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 v =
                           SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             [rst_type] outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty_out
                        Hinst_out_eq Hnthyty_out)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.lat_valuation_outside_sig_scope
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
                        SIGPROOFS.lat_valuation dlt_sig callee_sig_cur inptyp0 ckty0
                          ([rty0] ⊔ rstty0) outtyp0).
                 set (dlt_raw_c :=
                        SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
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
                   (SIGPROOFS.lat_valuation_inputs_eq
                      dlt_raw callee_sig_cur inptyp0 ckty0 ([rty0] ⊔ rstty0) outtyp0
                      Hfresh_call Hndscope_c Hlen_in_c)
                   as Hinst_in_eq.
                 pose proof
                   (SIGPROOFS.lat_valuation_outputs_eq
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
                           SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 v =
                           SIGPROOFS.lat_valuation dlt_raw callee_sig_cur inptyp0 ckty0
                             ([rty0] ⊔ rstty0) outtyp0 x0)
                        (s_out callee_sig_cur) outtyp0 i yty_out2
                        Hinst_out_eq Hnthyty2)
                     as (xty' & Hnthxty' & Hinsteq).
                   rewrite Hnthout in Hnthxty'.
                   inversion Hnthxty'; subst xty'; clear Hnthxty'.
                   unfold dlt_raw_c.
                   rewrite <- Hinsteq.
                   destruct Hfresh_call as [_ [_ [_ Houtfresh]]].
                   rewrite (SIGPROOFS.lat_valuation_outside_sig_scope
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
