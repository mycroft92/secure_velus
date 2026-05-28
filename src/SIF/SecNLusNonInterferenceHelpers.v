(** Helper lemmas for replaying signatures and transporting low-equivalence through NLustre equations and calls. *)

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
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSNONINTERFERENCEHELPERS
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

  Include SECNLUSNONINTERFERENCESUPPORT
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    Definition reset_control_low_eq_upto
      (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
      (r : ident) (H H' : history) (k : nat) : Prop :=
      forall ys ys' rs rs',
        sem_var H r ys ->
        sem_var H' r ys' ->
        bools_of ys rs ->
        bools_of ys' rs' ->
        low_var ty_env dlt t r ->
        forall j, j <= k -> count rs j = count rs' j.

    Lemma reset_control_low_eq_upto_of_sem_var_eq :
      forall ty_env dlt t r H H' k,
        (low_var ty_env dlt t r ->
         forall j, j <= k -> Env.find r (H j) = Env.find r (H' j)) ->
        reset_control_low_eq_upto ty_env dlt t r H H' k.
    Proof.
      intros ty_env dlt t r H H' k Heq ys ys' rs rs'
             Hsemr Hsemr' Hbool Hbool' Hlowr j Hj.
      assert (Hys_eq : forall j0, j0 <= k -> ys j0 = ys' j0).
      {
        eapply sem_var_low_eq_upto; eauto.
      }
      assert (Hrs_eq : forall j0, j0 <= k -> rs j0 = rs' j0).
      {
        eapply bools_of_eq_upto; eauto.
      }
      exact (count_eq_upto rs rs' k Hrs_eq j Hj).
    Qed.

    Definition clock_eq_upto
      (bk bk' : cstream) (k : nat) : Prop :=
      forall j, j <= k -> bk j = bk' j.

    Lemma clock_eq_upto_refl :
      forall bk k,
        clock_eq_upto bk bk k.
    Proof.
      intros bk k j Hj.
      reflexivity.
    Qed.

    Lemma agree_on_sym:
      forall scope dlt1 dlt2,
        SecT.agree_on scope dlt1 dlt2 ->
        SecT.agree_on scope dlt2 dlt1.
    Proof.
      intros scope dlt1 dlt2 Hagree x Hin.
      symmetry. exact (Hagree x Hin).
    Qed.

    Lemma low_var_agree_on_scope:
      forall ty_env t scope dlt1 dlt2 x alpha,
        Env.find x ty_env = Some alpha ->
        In alpha scope ->
        SecT.agree_on scope dlt1 dlt2 ->
        low_var ty_env dlt1 t x ->
        low_var ty_env dlt2 t x.
    Proof.
      intros ty_env t scope dlt1 dlt2 x alpha Hfind Hinscope Hagree Hlow.
      destruct Hlow as (alpha' & Hfind' & Hle).
      rewrite Hfind in Hfind'.
      inversion Hfind'. subst alpha'. clear Hfind'.
      exists alpha.
      split; [exact Hfind|].
      rewrite <- (Hagree alpha Hinscope).
      exact Hle.
    Qed.

    Lemma history_low_eq_agree_on_scope:
      forall ty_env t X scope dlt1 dlt2 H H',
        (forall x, In x X -> exists alpha, Env.find x ty_env = Some alpha /\ In alpha scope) ->
        SecT.agree_on scope dlt1 dlt2 ->
        history_low_eq ty_env dlt1 t X H H' ->
        history_low_eq ty_env dlt2 t X H H'.
    Proof.
      intros ty_env t X scope dlt1 dlt2 H H' Hscope Hagree Hlow k x Hin Hobs.
      apply Hlow; [exact Hin|].
      destruct (Hscope x Hin) as (alpha & Hfind & Hinscope).
      eapply low_var_agree_on_scope; eauto.
      eapply agree_on_sym; eauto.
    Qed.

    Lemma history_low_eq_weaken:
      forall ty_env dlt t X Y H H',
        (forall x, In x Y -> In x X) ->
        history_low_eq ty_env dlt t X H H' ->
        history_low_eq ty_env dlt t Y H H'.
    Proof.
      intros ty_env dlt t X Y H H' Hsub Hlow k x Hin Hobs.
      eapply Hlow; eauto.
    Qed.

    Lemma signature_satisfied_replays_raw:
      forall P n ty_env sig dlt,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Clo.wc_node P n ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        signature_satisfied dlt sig ->
        exists dlt_raw clk_id rst_id clk_type rst_type inp out locals raw st_n,
          get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id ty_env = Some clk_type
          /\ Env.find rst_id ty_env = Some rst_type
          /\ get_mappings_from_node n.(n_in) ty_env = Some inp
          /\ get_mappings_from_node n.(n_out) ty_env = Some out
          /\ get_mappings_from_node n.(n_vars) ty_env = Some locals
          /\ generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n)
          /\ sig = {| s_name := n.(n_name);
                      s_in := inp;
                      s_out := out;
                      s_reset := rst_type;
                      s_clk := clk_type;
                      s_constraints := SymTypes.simplify raw locals |}
          /\ SecT.agree_on (signature_scope sig) dlt dlt_raw
          /\ SecT.listSatisfiable dlt_raw raw.
    Proof.
      intros P n ty_env sig dlt
             Henvsgen Hwc Hfindnode Hfindenv Hsigsc Hsatsig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigsc.
      rewrite Hfindenv in Hsigsc.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv
           G n ty_env aux_names sig Hsigsc)
        as Hinv.
      destruct Hinv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef).
      pose proof (find_node_In _ _ _ Hfindnode) as [_ Hin].
      apply in_split in Hin as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'. clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node as
          (envs_pref & aux_pref & st_pref & local_env & rec & st_local
           & envs_cur & st_cur & Hpref & Hlocalgen & Hins & Htail);
        eauto.
      assert (Hcurfind : find_node_env n.(n_name) envs_cur = Some local_env).
      { eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto. }
      assert (Hlocalfind : find_node_env n.(n_name) envs = Some local_env).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto. }
      rewrite Hfindenv in Hlocalfind.
      inversion Hlocalfind.
      assert (Hauxhead :
                get_node_aux n.(n_name) (rec :: aux_pref) =
                Some (rec.(nclk), rec.(nrst))).
      {
        pose proof Hlocalgen as Hlocalshape.
        unfold NAMEGEN.generate_local_env_for_node in Hlocalshape.
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (clk_name & stc & Hclkgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (rst_name & str & Hrstgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (env0 & ste & Henvgen & Hret0).
        unfold NAMEGEN.NMret in Hret0.
        inversion Hret0; subst rec st_local.
        unfold get_node_aux. simpl.
        rewrite ident_eqb_refl. reflexivity.
      }
      assert (Hauxrec :
                get_node_aux n.(n_name) aux_names =
                Some (rec.(nclk), rec.(nrst))).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto. }
      rewrite Haux in Hauxrec.
      inversion Hauxrec; subst clk_id rst_id.
      assert (Hsigshape :
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}
                =
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}).
      { reflexivity. }
      subst ty_env sig.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_from_local_env
           G n
           {| s_name := n.(n_name);
              s_in := inp;
              s_out := out;
              s_reset := rst_type;
              s_clk := clk_type;
              s_constraints := SymTypes.simplify raw locals |}
           local_env rec aux_names st_pref st_local
           clk_type rst_type inp out locals raw st_n
           Hlocalgen Hsigsc Hclk Hrst Hinp Hout Hlocals Hraw Hsigshape)
        as Hready.
      destruct Hready as [Hwfraw Hlocalsdisj].
      edestruct (SecT.simplify_complete
                   raw locals
                   (signature_scope
                      {| s_name := n.(n_name);
                         s_in := inp;
                         s_out := out;
                         s_reset := rst_type;
                         s_clk := clk_type;
                         s_constraints := SymTypes.simplify raw locals |})
                   dlt)
        as (dlt_raw & Hagree & Hsatraw); eauto.
        exists dlt_raw, rec.(nclk), rec.(nrst), clk_type, rst_type, inp, out, locals, raw, st_n.
        repeat split; auto.
    Qed.

    Lemma nl_node_causal_ind_defined:
      forall (n : node) (P_var : ident -> Prop),
        (forall eq x,
            In eq n.(n_eqs) ->
            In x (var_defined eq) ->
            (forall y, NLCaus.nl_depends_on_eq eq x y -> P_var y) ->
            P_var x) ->
        Forall P_var (map fst n.(n_in)) ->
        NLCaus.nl_node_causal n ->
        Forall P_var (vars_defined n.(n_eqs)).
    Proof.
      intros n P_var Heqcase Hinputs Hcaus.
      pose proof
        (NLCaus.nl_node_causal_ind
           n P_var Heqcase Hinputs Hcaus)
        as Hall.
      rewrite map_app in Hall.
      apply Forall_app in Hall as [_ Hdefd].
      rewrite n.(n_defd).
      exact Hdefd.
    Qed.

    Lemma history_low_eq_inputs_pointwise:
      forall (n : node) ty_env dlt t H H',
        history_low_eq ty_env dlt t (map fst n.(n_in)) H H' ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall k, Env.find x (H k) = Env.find x (H' k))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' Hlow.
      apply Forall_forall.
      intros x Hin Hobs k.
      eapply Hlow; eauto.
    Qed.

    Lemma history_low_eq_upto_inputs_pointwise:
      forall (n : node) ty_env dlt t H H' k,
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' k ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall j, j <= k -> Env.find x (H j) = Env.find x (H' j))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' k Hlow.
      apply Forall_forall.
      intros x Hin Hobs j Hj.
      eapply Hlow; eauto.
    Qed.

    Lemma generate_eqns_constraints_member:
      forall ty_env clk_type rst_type eqs raw st st' eq,
        In eq eqs ->
        generate_eqns_constraints G ty_env clk_type rst_type eqs st = OK (raw, st') ->
        exists ceq pre post steq stceq,
          raw = pre ++ ceq ++ post
          /\ generate_eqn_constraint G ty_env clk_type rst_type eq steq = OK (ceq, stceq).
    Proof.
      intros ty_env clk_type rst_type eqs.
      induction eqs as [|eq0 eqs IH]; intros raw st st' eq Hin Hgen.
      - inversion Hin.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c0 & st1 & Hc0 & Hgen).
        eapply sec_bind_inv in Hgen as (cs0 & st2 & Hcs0 & Hret).
        unfold ret in Hret. inversion Hret; subst raw st'. clear Hret.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst eq.
          exists c0, [], cs0, st, st1.
          split; [reflexivity|exact Hc0].
        + destruct (IH cs0 st1 st2 eq Hin Hcs0)
            as (ceq & pre & post & steq & stceq & Hraw & Hgeq).
          exists ceq, (c0 ++ pre), post, steq, stceq.
          split.
          * rewrite Hraw. now rewrite app_assoc.
          * exact Hgeq.
    Qed.

    Lemma listSatisfiable_app_middle:
      forall dlt pre mid post,
        SecT.listSatisfiable dlt (pre ++ mid ++ post) ->
        SecT.listSatisfiable dlt mid.
    Proof.
      intros dlt pre mid post Hsat.
      unfold SecT.listSatisfiable in *.
      repeat rewrite Forall_app in Hsat.
      destruct Hsat as [_ [Hmid _]].
      exact Hmid.
    Qed.

    Lemma mmap_assign_exp_type_inv:
      forall ty_env es tys st st',
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        st' = st
        /\ Forall2
             (fun e ty => SECCETYPING.assign_exp_type ty_env e = Some ty)
             es tys.
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' Hmap.
      - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst.
        split; [reflexivity|constructor].
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ Htl) as [Hst Htys].
        subst st2.
        unfold ret in Hret. inversion Hret; subst tys st'.
        split; [reflexivity|].
        constructor; auto.
    Qed.

    Lemma option_to_sec_assign_clk_state_irrel:
      forall ty_env base ck st st' ckty st0,
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st = OK (ckty, st') ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st0 = OK (ckty, st0).
    Proof.
      intros ty_env base ck st st' ckty st0 Hck.
      unfold SC.option_to_sec in *.
      destruct (SECCETYPING.assign_clk_type ty_env base ck) as [ckty'|] eqn:Hassign;
        try discriminate.
      inversion Hck; subst.
      reflexivity.
    Qed.

    Lemma mmap_assign_exp_type_state_irrel:
      forall ty_env es tys st st' st0,
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st0 = OK (tys, st0).
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' st0 Hmap.
      - simpl in Hmap. unfold SC.ret in Hmap. inversion Hmap; subst.
        reflexivity.
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ st0 Htl).
        unfold SC.ret in Hret. inversion Hret; subst tys st'.
        cbn [SC.mmap].
        cbn [SC.option_to_sec].
        rewrite Heq.
        unfold SC.bind, SC.ret.
        simpl.
        destruct
          (SC.mmap
             (fun e0 : exp => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e0))
             es st0)
          as [[tys0 st0']|err] eqn:Hm.
        + inversion IH; subst. reflexivity.
        + discriminate.
    Qed.

    Lemma eqapp_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
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
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
             k ii y ity e ety
             Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
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
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
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

    Lemma eqapp_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    Lemma eqapp_reset_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
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
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety
             Hkr Hkr' Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
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
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
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

    Lemma eqapp_reset_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) (mask kr rs ys) ->
        sem_vars Hc' (map fst callee.(n_out)) (mask kr' rs' ys') ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo
             Hkr Hkr' Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (mask kr rs ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (mask kr' rs' ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      rewrite Hkr in Hnthvo.
      rewrite Hkr' in Hnthvo'.
      pose proof
        (nth_error_mask_count_self rs ys k i vo Hnthvo)
        as Hnthvo0.
      pose proof
        (nth_error_mask_count_self rs' ys' k i vo' Hnthvo')
        as Hnthvo0'.
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo0 in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo0' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    Lemma get_mappings_nth_error_inv:
      forall xs ty_env tys i x,
        get_mappings xs ty_env = Some tys ->
        nth_error xs i = Some x ->
        exists ty,
          nth_error tys i = Some ty
          /\ Env.find x ty_env = Some ty.
    Proof.
      induction xs as [|y ys IH]; intros ty_env tys i x Hmap Hnth.
      - destruct i; inversion Hnth.
      - simpl in Hmap.
        destruct (Env.find y ty_env) as [yty|] eqn:Hyfind; try discriminate.
        destruct (get_mappings ys ty_env) as [tys'|] eqn:Hys; try discriminate.
        inversion Hmap; subst tys.
        destruct i as [|i].
        + simpl in Hnth. inversion Hnth; subst x.
          exists yty. split; [reflexivity|exact Hyfind].
        + simpl in Hnth.
          specialize (IH ty_env tys' i x Hys Hnth) as (ty & Hnthty & Hfindty).
          exists ty.
          split.
          * exact Hnthty.
          * exact Hfindty.
    Qed.

    Lemma get_mappings_length:
      forall xs ty_env tys,
        get_mappings xs ty_env = Some tys ->
        List.length xs = List.length tys.
    Proof.
      induction xs as [|x xs IH]; intros ty_env tys Hmap.
      - simpl in Hmap. inversion Hmap. reflexivity.
      - simpl in Hmap.
        destruct (Env.find x ty_env) as [xty|] eqn:Hfind; try discriminate.
        destruct (get_mappings xs ty_env) as [tys'|] eqn:Htl; try discriminate.
        inversion Hmap; subst tys.
        simpl. f_equal.
        eapply IH; eauto.
    Qed.

    Lemma eqapp_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k,
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k
             Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs
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
        as (ety & Hnthinpty & Heqexp).
      eapply
        (eqapp_input_var_low_eq_pointwise
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt rstty ckty t
           bk H H' Hc Hc' exps ls ls'
           j ii y ity e ety); eauto.
      intros z Hz.
      eapply Hfree_eqs.
      - eapply Exists_exists.
        exists e.
        split.
        + eapply nth_error_In.
          exact Hnthe.
        + exact Hz.
      - exact Hj.
    Qed.

    Lemma eqapp_reset_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k,
        kr = count rs k ->
        kr' = count rs' k ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        (forall j, j <= k -> count rs j = count rs' j) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k
             Hkr Hkr' Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs Hcount_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof (get_mappings_from_node_eq _ _ _ _ Hinp_c) as Hinp_c_eq.
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
        as (ety & Hnthinpty & Heqexp).
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        eapply
          (eqapp_reset_input_var_low_eq_pointwise
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety); eauto.
        intros z Hz.
        eapply Hfree_eqs.
        + eapply Exists_exists.
          exists e.
          split.
          * eapply nth_error_In.
            exact Hnthe.
          * exact Hz.
        + exact Hj.
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
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

    Lemma eqapp_outputs_low_eq_upto:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        forall j, j <= k -> Env.find x (H j) = Env.find x (H' j).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'
             j Hj.
      eapply
        (eqapp_output_transport_pointwise
           ty_env_c dlt_raw_c t
           H H' Hc Hc' callee
           xs ys ys' j i x yo); eauto.
      eapply history_low_eq_upto_monotone; eauto.
    Qed.

    Lemma defined_var_type_in_out_or_locals:
      forall n ty_env out locals x ty,
        Env.find x ty_env = Some ty ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In x (vars_defined n.(n_eqs)) ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals x ty Hfind Hout Hlocals Hdef.
      assert (Hin_vo : In x (map fst (n.(n_vars) ++ n.(n_out)))).
      {
        eapply Permutation_in; [apply n.(n_defd)|exact Hdef].
      }
      rewrite map_app, in_app_iff in Hin_vo.
      destruct Hin_vo as [Hin_local|Hin_out].
      - apply in_map_iff in Hin_local as ((xlocal, alocal) & Heq & Hin_local).
        simpl in Heq. subst xlocal.
        apply In_InMembers in Hin_local.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_local Hlocals)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. right. exact Hin'.
      - apply in_map_iff in Hin_out as ((xout, aout) & Heq & Hin_out).
        simpl in Heq. subst xout.
        apply In_InMembers in Hin_out.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_out Hout)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. left. exact Hin'.
    Qed.

    Lemma find_nodes_linear_order:
      forall n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node n1.(n_name) all_nodes = Some n1 ->
        find_node n2.(n_name) all_nodes = Some n2 ->
        n1.(n_name) <> n2.(n_name) ->
        (exists prefix mid suffix,
            all_nodes = prefix ++ n1 :: mid ++ n2 :: suffix)
        \/ (exists prefix mid suffix,
            all_nodes = prefix ++ n2 :: mid ++ n1 :: suffix).
    Proof.
      intros n1 n2 Hndnames Hfind1 Hfind2 Hneq.
      pose proof (find_node_In _ _ _ Hfind1) as [_ Hin1].
      pose proof (find_node_In _ _ _ Hfind2) as [_ Hin2].
      apply in_split in Hin1 as (prefix1 & suffix1 & Hall1).
      subst all_nodes.
      simpl in Hin2.
      rewrite in_app_iff in Hin2.
      simpl in Hin2.
      destruct Hin2 as [Hin2|[Heq12|Hin2]].
      - apply in_split in Hin2 as (prefix2 & suffix2 & Hprefix2).
        right.
        exists prefix2, suffix2, suffix1.
        rewrite Hprefix2. repeat rewrite <- app_assoc. reflexivity.
      - subst n2.
        exfalso. apply Hneq. reflexivity.
      - apply in_split in Hin2 as (mid & suffix2 & Hsuffix2).
        left.
        exists prefix1, mid, suffix2.
        rewrite Hsuffix2. repeat rewrite <- app_assoc. reflexivity.
    Qed.

    Lemma find_node_unique_nodup:
      forall f n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node f all_nodes = Some n1 ->
        find_node f all_nodes = Some n2 ->
        n1 = n2.
    Proof.
      intros f n1 n2 _ Hfind1 Hfind2.
      revert f n1 n2 Hfind1 Hfind2.
      induction all_nodes as [|nd nds IH]; intros f n1 n2 Hfind1 Hfind2.
      - discriminate.
      - simpl in Hfind1, Hfind2.
        destruct (ident_eqb nd.(n_name) f) eqn:Hname.
        + inversion Hfind1; inversion Hfind2; subst; reflexivity.
        + eapply IH; eauto.
    Qed.

    Lemma Ordered_nodes_nodup_names:
      forall nodes,
        Ordered_nodes nodes ->
        NoDup (map n_name nodes).
    Proof.
      intros nodes Hord.
      induction Hord as [|nd nds Hord IH Hcalls Hfresh].
      - constructor.
      - simpl. constructor.
        + intro Hin.
          apply in_map_iff in Hin as (nd' & Heq & Hin').
          rewrite Forall_forall in Hfresh.
          specialize (Hfresh _ Hin').
          simpl in Heq.
          apply Hfresh.
          symmetry.
          exact Heq.
        + exact IH.
    Qed.

    Lemma generated_sig_scope_nodup_scoped_env:
      forall n ty_env clk_id rst_id clk_type rst_type inp out,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        NoDup
          (SIG.signature_scope
             {| s_name := n.(n_name);
                s_in := inp;
                s_out := out;
                s_reset := rst_type;
                s_clk := clk_type;
                s_constraints := nil |}).
    Proof.
      intros n ty_env clk_id rst_id clk_type rst_type inp out
             Henvsgen Hfindnode Hfindenv Haux Hclk Hrst Hinp Hout.
      pose proof (find_node_In _ _ _ Hfindnode) as (_ & Hinnode).
      apply in_split in Hinnode as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref & aux_pref & st_pref
            & local_env & rec & st_local
            & envs_cur & st_cur
            & Hpref & Hlocal & Hins & Htail);
        eauto.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof
          (NAMEGEN.generate_node_scoped_env'_preserves_find
             _ _ _ _ _ _ _ _ _ Htail Hfind_cur)
          as Hfind_final.
        exact Hfind_final.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrec_name.
        assert (Haux_cur : get_node_aux n.(n_name) (rec :: aux_pref) = Some (rec.(nclk), rec.(nrst))).
        {
          unfold get_node_aux.
          simpl.
          rewrite <- Hrec_name.
          rewrite ident_eqb_refl.
          reflexivity.
        }
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
      }
      rewrite Hfindenv in Hfindlocal.
      inversion Hfindlocal; subst local_env.
      rewrite Haux in Hauxlocal.
      inversion Hauxlocal; subst clk_id rst_id.
      eapply SECNLUSTYPINGCORRECTNESS.generate_node_sig_scope_nodup_from_local_env;
        eauto.
    Qed.

    Lemma fresh_insert_node_env_state:
      forall envs0 name local_env st envs' st',
        NAMEGEN.fresh_insert_node_env envs0 name local_env st = OK (envs', st') ->
        st' = st.
    Proof.
      intros envs0 name local_env st envs' st' Hins.
      unfold NAMEGEN.fresh_insert_node_env in Hins.
      destruct (Env.mem name envs0) eqn:Hmem; try discriminate.
      unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
      inversion Hins; reflexivity.
    Qed.

    Lemma scope_fresh_from_upper_lower_bounds:
      forall scope sig st,
        (forall ty,
            In ty scope ->
            exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive) ->
        (forall ty,
            In ty (signature_scope sig) ->
            exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive) ->
        SIG.scope_fresh scope sig.
    Proof.
      intros scope sig st Hupper Hlower ty Hinscope Hinsig.
      destruct (Hupper ty Hinscope) as (n1 & Hty1 & Hlt1).
      destruct (Hlower ty Hinsig) as (n2 & Hty2 & Hle2).
      rewrite Hty1 in Hty2.
      apply gensym_injective in Hty2 as [_ Heq]. subst n2.
      eapply Pos.lt_irrefl.
      eapply Pos.lt_le_trans; eauto.
    Qed.

    Lemma eqapp_outtyp_in_out_or_locals:
      forall n ty_env out locals xs ck f exps r outtyp ty,
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        get_mappings xs ty_env = Some outtyp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In ty outtyp ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals xs ck f exps r outtyp ty
             Heqin Hmap Hout Hlocals Hin.
      destruct (get_mappings_In _ _ _ _ Hmap Hin) as (x & Hinx & Hfindx).
      assert (Hxdef : In x (vars_defined n.(n_eqs))).
      {
        unfold vars_defined.
        apply in_flat_map.
        exists (EqApp xs ck f exps r).
        split; [exact Heqin|exact Hinx].
      }
      eapply defined_var_type_in_out_or_locals; eauto.
    Qed.

    Lemma generated_caller_scope_fresh_scoped_env:
      forall caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        NoDup (map n_name all_nodes) ->
        find_node caller.(n_name) all_nodes = Some caller ->
        find_node callee.(n_name) all_nodes = Some callee ->
        caller.(n_name) <> callee.(n_name) ->
        find_node_env caller.(n_name) envs = Some caller_env ->
        find_node_env callee.(n_name) envs = Some callee_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G callee envs aux_names = OK callee_sig ->
        get_node_aux caller.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id caller_env = Some clk_type ->
        Env.find rst_id caller_env = Some rst_type ->
        get_mappings_from_node caller.(n_in) caller_env = Some inp ->
        get_mappings_from_node caller.(n_out) caller_env = Some out ->
        get_mappings_from_node caller.(n_vars) caller_env = Some locals ->
        SIG.scope_fresh
          (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
          callee_sig.
    Proof.
      intros caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals
             Henvsgen Hndnames Hfindcaller Hfindcallee Hneq
             Hfindenvcaller Hfindenvcallee Hsiggencallee
             Hauxcaller Hclkcaller Hrstcaller
             Hinpcaller Houtcaller Hlocalscaller.
      pose proof
        (find_nodes_linear_order
           caller callee Hndnames Hfindcaller Hfindcallee Hneq)
        as Hord.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           all_nodes (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st_final]|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsiggencallee.
      rewrite Hfindenvcallee in Hsiggencallee.
      destruct Hord as
          [(prefix & mid & suffix & Hall)
          |(prefix & mid & suffix & Hall)];
        subst all_nodes.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_call) as Hcall_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_call Hfind_call_cur)
            as Hfind_call_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_call Hfind_call_pref)
            as Hfind_call_after_cal.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_call_after_cal)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_cal_cur)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_upper :
                  forall ty,
                    In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (m < st_pref_call)%positive).
        {
          intros ty Hin.
          destruct
            (node_scope_upper_bounded_from_local_env
               caller st_pref_cal local_env_cal rec_cal st_local_cal
               clk_id rst_id clk_type rst_type inp out locals ty
               Hlocal_cal Hclkcaller Hrstcaller Hinpcaller Houtcaller Hlocalscaller Hin)
            as (m & Hm & Hlt).
          exists m. split; auto.
          eapply Pos.lt_le_trans; eauto.
          rewrite <- Hcur_cal. exact Hcall_mid_le.
        }
        assert (Hcallee_lower :
                  forall ty,
                    In ty (signature_scope callee_sig) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (st_pref_call <= m)%positive).
        {
          intros ty Hin.
          destruct
            (SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_lower_bound_from_local_env
               G callee local_env_call aux_names callee_sig
               st_pref_call rec_call st_local_call ty
               Hlocal_call Hsiggencallee Hin)
            as (m & Hm & Hlo).
          exists m. split; auto.
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
        }
        eapply scope_fresh_from_upper_lower_bounds; eauto.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_cal) as Hcal_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_call_cur)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_cal Hfind_cal_cur)
            as Hfind_cal_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_cal Hfind_cal_pref)
            as Hfind_cal_after_call.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_cal_after_call)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_lower :
                  SIG.scope_lower_bounded
                    (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                    st_pref_cal).
        {
          eapply SECNLUSTYPINGCORRECTNESS.node_scope_lower_bounded_from_local_env; eauto.
        }
        assert (Hcallee_upper0 :
                  SIG.signature_scope_bounded_above callee_sig st_local_call).
        {
          intros ty Hin.
          eapply SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_upper_bound_from_local_env
            with (rec := rec_call) (st := st_pref_call) (st' := st_local_call)
                 (aux_names := aux_names); eauto.
        }
        assert (Hcallee_upper :
                  SIG.signature_scope_bounded_above callee_sig st_pref_cal).
        {
          eapply SIG.signature_scope_bounded_above_monotone; eauto.
          rewrite <- Hcur_call. exact Hcal_mid_le.
        }
        eapply SIG.scope_fresh_from_bounds; eauto.
    Qed.

    Lemma generate_eqdef_constraint_inv:
      forall ty_env base_ty rst_ty x ck ce cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqDef x ck ce) st =
        OK (cns, st') ->
        exists ckty cety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ cety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_cexp_type ty_env ce = Some cety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck ce cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (cety & st2 & Hce & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in Hce.
      destruct (SECCETYPING.assign_cexp_type ty_env ce) as [cety'|] eqn:Hce';
        try discriminate.
      inversion Hce; subst cety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', cety', xty'.
      repeat split; reflexivity.
    Qed.

    Lemma generate_eqfby_constraint_inv:
      forall ty_env base_ty rst_ty x ck c0 e cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqFby x ck c0 e) st =
        OK (cns, st') ->
        exists ckty ety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ ety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_exp_type ty_env e = Some ety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck c0 e cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (ety & st2 & He & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in He.
      destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:He';
        try discriminate.
      inversion He; subst ety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', ety', xty'.
      repeat split; reflexivity.
    Qed.

    Lemma generate_eqapp_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps None) st = OK (cns, st') ->
        exists callee_sig ckty inptyp outtyp st_clk st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_clk = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty [rst_ty] outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      exists callee_sig, ckty, inptyp, (xty' :: tys'), st_clk, st_inp.
      repeat split; auto.
    Qed.

    Lemma generate_eqreset_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps r ckr cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps (Some (r, ckr))) st = OK (cns, st') ->
        exists callee_sig ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ Env.find r ty_env = Some rty
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env rst_ty ckr) st_clk =
               OK (rstty, st_rst)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_rst = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty ([rty] ⊔ rstty) outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps r ckr cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (rty & st_rty & Hrty & Hgen).
      eapply sec_bind_inv in Hgen as (rstty & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      unfold SC.find_env in Hrty.
      destruct (Env.find r ty_env) as [rty'|] eqn:Hrfind; try discriminate.
      unfold SC.ret in Hrty. inversion Hrty; subst rty st_rty.
      exists callee_sig, ckty, rty', rstty, inptyp, (xty' :: tys'), st_clk, st_rst, st_inp.
      repeat split; auto.
    Qed.

    Lemma generate_constraints_lengths:
      forall sig inp clk rst out cns st st',
        SIG.generate_constraints sig inp clk rst out st = OK (cns, st') ->
        List.length sig.(s_in) = List.length inp
        /\ List.length sig.(s_out) = List.length out.
    Proof.
      intros sig inp clk rst out cns st st' Hgen.
      unfold SIG.generate_constraints in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
      eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
      eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hgen).
      split.
      - eapply SIGPROOFS.subst_constraints_inp_map_length; eauto.
      - eapply SIGPROOFS.subst_constraints_out_map_length; eauto.
    Qed.

    Lemma In_app_weaken_right:
      forall (A : Type) (x : A) a b ,
        In x a ->
        In x (a ++ b).
    Proof.
      intros A x a b Hin.
      apply in_or_app.
      left.
      exact Hin.
    Qed.

    Lemma inst_valuation_outputs_eq_outputs_fresh:
      forall dlt sig inp clk rst out,
        SIG.outputs_fresh (signature_scope sig) out ->
        NoDup (signature_scope sig) ->
        List.length sig.(s_out) = List.length out ->
        Forall2
          (fun x v =>
             SIGPROOFS.inst_valuation dlt sig inp clk rst out v =
             SIGPROOFS.inst_valuation dlt sig inp clk rst out x)
          sig.(s_out) out.
    Proof.
      intros dlt sig inp clk rst out Houtfresh Hndscope Hlen.
      destruct sig as [sname sin sout sreset sclk sconstraints].
      simpl in *.
      set (sigfull :=
             {| s_name := sname;
                s_in := sin;
                s_out := sout;
                s_reset := sreset;
                s_clk := sclk;
                s_constraints := sconstraints |}).
      set (ival := SIGPROOFS.inst_valuation dlt sigfull inp clk rst out).
      destruct (SIGPROOFS.sig_scope_nodup_decomp sigfull Hndscope)
        as [_ [Hnout [Hfreshin [Houtnotin _]]]].
      assert (Htail :
                Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v)
                        sout out).
      {
        eapply SIGPROOFS.upd_idents_rev_eq_on_pairs.
        - intros x Hin. unfold signature_scope. apply in_or_app. right.
          apply in_or_app. left. exact Hin.
        - exact Houtfresh.
        - exact Hnout.
        - exact Hlen.
      }
      assert (Houtsafe :
                forall x,
                  In x sout ->
                  ~ In x sin /\ ~ In x [sclk; sreset]).
      {
        intros x Hinout.
        split.
        - intro Hinin.
          rewrite Forall_forall in Hfreshin.
          specialize (Hfreshin _ Hinin).
          apply Hfreshin.
          apply in_app_iff. left. exact Hinout.
        - rewrite Forall_forall in Houtnotin.
          exact (Houtnotin _ Hinout).
      }
      assert (Hformal :
                forall x,
                  In x sout ->
                  ival x = upd_idents_rev dlt sout out x).
      {
        intros x Hinout.
        unfold ival, SIGPROOFS.inst_valuation.
        rewrite upd_types_rev_outside.
        2:{
          destruct (Houtsafe x Hinout) as [Hxin _].
          exact Hxin.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now left; symmetry.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now right; left; symmetry.
        }
        reflexivity.
      }
      assert (Hactual :
                forall v,
                  In v out ->
                  ival v = dlt v).
      {
        intros v Hinout.
        unfold ival.
        eapply SIGPROOFS.inst_valuation_outside_sig_scope.
        unfold SIG.outputs_fresh in Houtfresh.
        rewrite Forall_forall in Houtfresh.
        exact (Houtfresh _ Hinout).
      }
      assert (HformalF : Forall (fun x => ival x = upd_idents_rev dlt sout out x) sout).
      {
        rewrite Forall_forall.
        intros x Hin.
        exact (Hformal x Hin).
      }
      assert (HactualF : Forall (fun v => ival v = dlt v) out).
      {
        rewrite Forall_forall.
        intros v Hin.
        exact (Hactual v Hin).
      }
      assert
        (Hconv :
           forall xs ys,
             Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v) xs ys ->
             Forall (fun x => ival x = upd_idents_rev dlt sout out x) xs ->
             Forall (fun v => ival v = dlt v) ys ->
             Forall2 (fun x v => ival v = ival x) xs ys).
      {
        intros xs ys Hrel.
        induction Hrel; intros Hf1 Hf2.
        - constructor.
        - inversion Hf1 as [|x' xs' Hx Hxs]; subst.
          inversion Hf2 as [|y' ys' Hy Hys]; subst.
          constructor.
          + transitivity (dlt y).
            * exact Hy.
            * rewrite Hx. symmetry. exact H.
          + eapply IHHrel; eauto.
      }
      eapply Hconv; eauto.
    Qed.

    Definition node_outputs_raw_spec
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
      forall k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node nd.(n_name) all_nodes = Some nd ->
        find_node_env nd.(n_name) envs = Some ty_env ->
        SIG.find_signature nd.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
        get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node nd.(n_in) ty_env = Some inp ->
        get_mappings_from_node nd.(n_out) ty_env = Some out ->
        get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := nd.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names nd dlt_sig dlt_raw ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') nd.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_out)) H H' k.

    Definition node_outputs_raw_spec_clocked
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
      forall k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node nd.(n_name) all_nodes = Some nd ->
        find_node_env nd.(n_name) envs = Some ty_env ->
        SIG.find_signature nd.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
        get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node nd.(n_in) ty_env = Some inp ->
        get_mappings_from_node nd.(n_out) ty_env = Some out ->
        get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := nd.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names nd dlt_sig dlt_raw ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') nd.(n_eqs) ->
        clock_eq_upto bk bk' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_out)) H H' k.

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

    (** This is the base transport theorem for the current node.  Assuming the two runs already agree on the low information needed up to the current instant, it proves low-equivalence for the variables defined by the current equation list.  The clocked step theorem builds on this result. *)
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
            node_outputs_raw_spec_clocked callee
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
            node_outputs_raw_spec_clocked callee
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
              (generate_eqns_constraints_member
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqDef x0 ck ce) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqdef_constraint_inv
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
                 (generate_eqns_constraints_member
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps None) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqapp_constraint_inv
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
                 (generate_eqns_constraints_member
                    ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                    (EqApp (xh :: xt) ck f exps (Some (r, ckr))) Heqin Hraw)
                 as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
               destruct
                 (generate_eqreset_constraint_inv
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
              (generate_eqns_constraints_member
                 ty_env clk_type rst_type n.(n_eqs) raw init_state st_n
                 (EqFby x0 ck c0 e) Heqin Hraw)
              as (ceq & pre & post & steq & stceq & Hsplit & Hgeq).
            pose proof (listSatisfiable_app_middle dlt_raw pre ceq post)
              as Hmid.
            rewrite Hsplit in Hsatraw.
            specialize (Hmid Hsatraw).
            destruct
              (generate_eqfby_constraint_inv
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

  End GENERATED_NODE_NONINTERFERENCE.

End SECNLUSNONINTERFERENCEHELPERS.
