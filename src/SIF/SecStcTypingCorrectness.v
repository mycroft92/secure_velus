(** Correctness facts for generated STC signatures and reset-instance environments. *)

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import Clocks.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Sorting.Permutation.
From compcert Require Import common.Errors.

Module Type SECSTCTYPINGCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Import WD    : STCWELLDEFINED Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo).



  Ltac mySecInv :=
    simpl in *;
    match goal with
    | H: OK _ = OK _ |- _ =>
      inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
      discriminate
    | H: ret _ _ = _ |- _ =>
      unfold ret in H
    | H: bind ?x ?f ?st = OK ?res |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK ?res |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.


  Lemma generate_reset_env_range':
    forall trs env acc st reset_env rids st' x ty,
      (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
      generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
      Env.find x reset_env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ty Henv Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. eauto.
    - simpl in Hgen.
      destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
      1,2,4: eapply IH; eauto.
      repeat mySecInv.
      eapply IH; [|eauto|eauto].
      intros y ty' Hy.
      eapply fresh_reset_insert_sec_range; eauto.
  Qed.

  Lemma generate_reset_env_range:
    forall trs reset_env rids st' x ty,
      generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
      Env.find x reset_env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    intros trs reset_env rids st' x ty Hgen Hfind.
    unfold generate_reset_env in Hgen.
    eapply generate_reset_env_range'; eauto.
    intros y ty' Hy.
    rewrite Env.gempty in Hy. discriminate.
  Qed.


  Lemma generate_reset_env'_preserves_find:
    forall trs env acc st reset_env rids st' x ty,
      generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
      Env.find x env = Some ty ->
      Env.find x reset_env = Some ty.
  Proof.
    induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ty Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Hfind.
    - simpl in Hgen.
      destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
      1,2,4: eapply IH; eauto.
      eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
      eapply IH; eauto.
    eapply fresh_reset_insert_preserves_find; eauto.
  Qed.

  (** This turns the scoped-env STC generator into a scoped target signature.  The translation file uses it when it reconstructs one translated system from the shared node-scoped environment. *)
  Theorem generate_sys_signature_scoped_env_scoped:
    forall G P s envs env aux_names sig,
      secglobal_scoped G ->
      Clo.wc_system P s ->
      find_node_env s.(SynStc.s_name) envs = Some env ->
      env_injective env ->
      SECSTCTYPING.generate_sys_signature_scoped_env G s envs aux_names = OK sig ->
      signature_scoped sig.
  Proof.
      intros G P s envs env aux_names sig
             Hscoped Hwc Hfindenv Hinj Hsig.
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hsig.
      rewrite Hfindenv in Hsig.
      eapply SECSTCTYPING.generate_sys_signature_scoped; eauto.
  Qed.

  Lemma call_output_low_implies_reset_low:
    forall sig inptyp ckty rstty outtyp cns st st'
           dlt t i y v,
      signature_good sig ->
      (forall y lhs,
          findST sig.(s_constraints) y = Some lhs ->
          In sig.(s_reset) lhs) ->
      call_subst_fresh sig inptyp ckty rstty outtyp ->
      NoDup (signature_scope sig) ->
      List.length sig.(s_in) = List.length inptyp ->
      List.length sig.(s_out) = List.length outtyp ->
      generate_constraints sig inptyp ckty rstty outtyp st = OK (cns, st') ->
      listSatisfiable dlt cns ->
      nth_error sig.(s_out) i = Some y ->
      nth_error outtyp i = Some v ->
      dlt v ⊑ t ->
      hm_ext dlt rstty ⊑ t.
  Proof.
    intros sig inptyp ckty rstty outtyp cns st st'
           dlt t i y v
           Hgood Hresetlhs Hfresh Hndscope HlenIn HlenOut Hgen Hsat
           Hnthy Hnthv Hlowv.
    assert (Hinfresh : Forall2 (fun x ty => ~ In x ty) sig.(s_in) inptyp).
    { eapply call_subst_fresh_inputs_notin_pairs; eauto. }
    assert (Hclkfresh_notin : ~ In sig.(s_clk) ckty).
    {
      destruct Hfresh as [_ [Hclkfresh [_ _]]].
      unfold type_fresh in Hclkfresh.
      rewrite Forall_forall in Hclkfresh.
      intro Hin.
      eapply Hclkfresh.
      - exact Hin.
      - unfold signature_scope.
        repeat rewrite in_app_iff.
        simpl. auto.
    }
    assert (Hrstfresh_notin : ~ In sig.(s_reset) rstty).
    {
      destruct Hfresh as [_ [_ [Hrstfresh _]]].
      unfold type_fresh in Hrstfresh.
      rewrite Forall_forall in Hrstfresh.
      intro Hin.
      eapply Hrstfresh.
      - exact Hin.
      - unfold signature_scope.
        repeat rewrite in_app_iff.
        simpl. auto.
    }
    pose proof
      (generate_constraints_complete_good
         sig inptyp ckty rstty outtyp cns st st'
         Hgood Hgen dlt Hsat Hinfresh Hclkfresh_notin Hrstfresh_notin)
      as Hsat_sig.
    pose proof
      (lat_valuation_outputs_eq
         dlt sig inptyp ckty rstty outtyp
         Hfresh Hndscope HlenOut)
      as Hout_eq.
    destruct
      (Forall2_nth_error_inv
         _ _
         (fun x v0 =>
            lat_valuation dlt sig inptyp ckty rstty outtyp v0 =
            lat_valuation dlt sig inptyp ckty rstty outtyp x)
         sig.(s_out) outtyp i y
         Hout_eq Hnthy)
      as (v' & Hnthv' & Hinst_out).
    rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. clear Hnthv'.
    destruct Hgood as [Hwf Hperm].
    assert (Hinrhs : In [y] (map snd sig.(s_constraints))).
    {
      eapply Permutation_in; [exact (Permutation_sym Hperm)|].
      apply in_map_iff.
      exists y.
      split; [reflexivity|].
      eapply nth_error_In_local; eauto.
    }
    destruct (findST_of_rhs_in sig.(s_constraints) y Hinrhs)
      as (lhs & Hfindlhs).
    assert (Hresetin : In sig.(s_reset) lhs).
    { eapply Hresetlhs; eauto. }
    assert (Hlowv_inst :
              lat_valuation dlt sig inptyp ckty rstty outtyp v ⊑ t).
    {
      destruct Hfresh as [_ [_ [_ Houtfresh]]].
      rewrite (lat_valuation_outside_sig_scope
                 dlt sig inptyp ckty rstty outtyp v).
      - exact Hlowv.
      - unfold outputs_fresh in Houtfresh.
        rewrite Forall_forall in Houtfresh.
        eapply Houtfresh.
        eapply nth_error_In_local; eauto.
    }
    assert (Hlowy :
              lat_valuation dlt sig inptyp ckty rstty outtyp y ⊑ t).
    {
      rewrite <- Hinst_out.
      exact Hlowv_inst.
    }
    unfold listSatisfiable in Hsat_sig.
    rewrite Forall_forall in Hsat_sig.
    specialize (Hsat_sig _ (find_correct _ _ _ Hfindlhs)).
    unfold constraintSatisfiable, satisfiable in Hsat_sig.
    simpl in Hsat_sig.
    rewrite <- (lat_valuation_reset_eq
                  dlt sig inptyp ckty rstty outtyp
                  Hfresh Hndscope).
    apply order_trans with
        (y := hm_ext (lat_valuation dlt sig inptyp ckty rstty outtyp) lhs).
    - apply hm_ext_list_in1.
      exact Hresetin.
    - apply order_trans with
        (y := join (lat_valuation dlt sig inptyp ckty rstty outtyp y) bottom).
      + exact Hsat_sig.
      + apply join_least_upper_bound.
        * exact Hlowy.
        * apply bottom_is_bottom.
  Qed.

  Lemma generate_sys_signature_inv:
    forall G s env aux_names sig,
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      exists clk_id rst_id clk_type rst_type inp out slocals slasts
             reset_env rids st_reset sconst st_s,
        get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id)
        /\ Env.find clk_id env = Some clk_type
        /\ Env.find rst_id env = Some rst_type
        /\ get_mappings_from_node s.(SynStc.s_in) env = Some inp
        /\ get_mappings_from_node s.(SynStc.s_out) env = Some out
        /\ get_mappings_from_node s.(SynStc.s_vars) env = Some slocals
        /\ get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts
        /\ get_node_inst s.(SynStc.s_name) aux_names = Some reset_env
        /\ get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids
        /\ generate_trconstrs_constraints G env reset_env clk_type rst_type s.(SynStc.s_tcs) st_reset = OK (sconst, st_s)
        /\ sig = {| s_name := s.(SynStc.s_name);
                    s_in := inp;
                    s_out := out;
                    s_reset := rst_type;
                    s_clk := clk_type;
                    s_constraints := SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids) |}.
  Proof.
    intros G s env aux_names sig Hsig.
    unfold SECSTCTYPING.generate_sys_signature in Hsig.
    lazymatch type of Hsig with
    | context [match ?m with | OK _ => _ | Error _ => _ end = _] =>
        remember m as gen_res eqn:Hgen
    end.
    destruct gen_res as [[packed st_res]|]; try discriminate.
    destruct packed as [packed env0].
    destruct packed as [packed packed_constraints].
    destruct packed as [packed packed_clk_type].
    destruct packed as [packed packed_rst_type].
    destruct packed as [packed_inp packed_out].
    simpl in Hsig.
    inversion Hsig; clear Hsig; subst.
    symmetry in Hgen.
    eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
    eapply sec_bind_inv in Hgen as (clk_type & st_clk & Hclk & Hgen).
    eapply sec_bind_inv in Hgen as (rst_type & st_rst & Hrst & Hgen).
    eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
    eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
    eapply sec_bind_inv in Hgen as (slocals & st_locals & Hslocals & Hgen).
    eapply sec_bind_inv in Hgen as (slasts & st_lasts & Hslasts & Hgen).
    eapply sec_bind_inv in Hgen as (reset_env & st_renv & Hresetenv & Hgen).
    eapply sec_bind_inv in Hgen as (rids & st_rids & Hrids & Hgen).
    eapply sec_bind_inv in Hgen as (sconst & st_s & Hsconst & Hret).
    unfold option_to_sec in Haux.
    destruct (get_node_aux (s.(SynStc.s_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
    inversion Haux; subst clk_id0 rst_id0 st_aux.
    unfold option_to_sec in Hclk.
    destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
    inversion Hclk; subst clk_type0 st_clk.
    unfold option_to_sec in Hrst.
    destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
    inversion Hrst; subst rst_type0 st_rst.
    unfold option_to_sec in Hinp.
    destruct (get_mappings_from_node (s.(SynStc.s_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
    inversion Hinp; subst inp0 st_inp.
    unfold option_to_sec in Hout.
    destruct (get_mappings_from_node (s.(SynStc.s_out)) env) as [out0|] eqn:Hout0; try discriminate.
    inversion Hout; subst out0 st_out.
    unfold option_to_sec in Hslocals.
    destruct (get_mappings_from_node (s.(SynStc.s_vars)) env) as [slocals0|] eqn:Hslocals0; try discriminate.
    inversion Hslocals; subst slocals0 st_locals.
    unfold option_to_sec in Hslasts.
    destruct (get_mappings_from_node (s.(SynStc.s_lasts)) env) as [slasts0|] eqn:Hslasts0; try discriminate.
    inversion Hslasts; subst slasts0 st_lasts.
    unfold ret in Hret. inversion Hret; subst.
    unfold option_to_sec in Hresetenv.
    destruct (get_node_inst (s.(SynStc.s_name)) aux_names) as [reset_env0|] eqn:Hrenv0;
      try discriminate.
    unfold ret in Hresetenv. inversion Hresetenv; subst reset_env0.
    unfold option_to_sec in Hrids.
    destruct (get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env)
      as [rids0|] eqn:Hrids0; try discriminate.
    unfold ret in Hrids. inversion Hrids; subst rids0.
    exists clk_id, rst_id, packed_clk_type, packed_rst_type, packed_inp, packed_out,
           slocals, slasts, reset_env, rids, st_rids, sconst, st_res.
    repeat split; eauto.
  Qed.

  Lemma generated_sys_signature_scope_key:
    forall G s env aux_names sig ty,
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      In ty (signature_scope sig) ->
      exists clk_id rst_id x,
        get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id)
        /\ (In x (map fst s.(SynStc.s_in))
            \/ In x (map fst s.(SynStc.s_out))
            \/ x = clk_id
            \/ x = rst_id)
        /\ Env.find x env = Some ty.
  Proof.
    intros G s env aux_names sig ty Hsig Hin.
    edestruct generate_sys_signature_inv as
        (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
         & reset_env & rids & st_reset & sconst & st_s
         & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
         & Hresetenv & Hrids & Hsconst & Hsigdef); eauto.
    subst sig.
    unfold signature_scope in Hin.
    repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|Hin]].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
        as (x & a & Hinx & Hfindx).
      exists clk_id, rst_id, x.
      split; [exact Haux|].
      split.
      + left. now apply in_map with (f := fst) in Hinx.
      + exact Hfindx.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
        as (x & a & Hinx & Hfindx).
      exists clk_id, rst_id, x.
      split; [exact Haux|].
      split.
      + right; left. now apply in_map with (f := fst) in Hinx.
      + exact Hfindx.
    - destruct Hin as [Hinclk|[Hinrst|[]]].
      + subst ty.
        exists clk_id, rst_id, clk_id.
        split; [exact Haux|].
        split.
        * right; right; left; reflexivity.
        * exact Hclk.
      + subst ty.
        exists clk_id, rst_id, rst_id.
        split; [exact Haux|].
        split.
        * right; right; right; reflexivity.
        * exact Hrst.
  Qed.

  (** The raw targets of a system are pairwise distinct: variables and
      lasts get distinct [sec] names because the source names are
      distinct and the environment is injective, the reset instances get
      distinct [sec_reset] names, and the two prefixes never collide. *)

  Lemma targets_nodup:
    forall env reset_env tcs tys vs ls rs,
      env_injective env ->
      (forall x ty, Env.find x env = Some ty -> exists n, ty = Ids.gensym Ids.sec n) ->
      (forall x ty, Env.find x reset_env = Some ty ->
                    exists n, ty = Ids.gensym Ids.sec_reset n) ->
      SECSTCTYPING.trconstrs_targets env reset_env tcs = Some tys ->
      get_mappings (variables tcs) env = Some vs ->
      get_mappings (lasts_of tcs) env = Some ls ->
      get_mappings (map fst (resets_of tcs)) reset_env = Some rs ->
      NoDup (variables tcs ++ lasts_of tcs) ->
      NoDup rs ->
      NoDup tys.
  Proof.
    intros env reset_env tcs tys vs ls rs
           Hinj Hsec Hrst Htys Hvs Hls Hrs Hndnames Hndrs.
    assert (Hperm : Permutation tys (vs ++ ls ++ rs)).
    { eapply SECSTCTYPING.trconstrs_targets_perm; eauto. }
    assert (Hvl : get_mappings (variables tcs ++ lasts_of tcs) env = Some (vs ++ ls)).
    { eapply get_mappings_app; eauto. }
    assert (Hndvl : NoDup (vs ++ ls)).
    { eapply (SECSTCTYPING.get_mappings_nodup env (variables tcs ++ lasts_of tcs) (vs ++ ls));
        [exact Hndnames|exact Hinj|exact Hvl]. }
    assert (Hdisj : Forall (fun z => ~ In z rs) (vs ++ ls)).
    { rewrite Forall_forall.
      intros z Hz Hzr.
      destruct (get_mappings_In _ _ _ _ Hvl Hz) as (x & _ & Hfx).
      destruct (get_mappings_In _ _ _ _ Hrs Hzr) as (o & _ & Hfo).
      destruct (Hsec _ _ Hfx) as (n1 & Hn1).
      destruct (Hrst _ _ Hfo) as (n2 & Hn2).
      rewrite Hn1 in Hn2.
      apply gensym_injective in Hn2.
      destruct Hn2 as [Hpref Hidx].
      exact (Ids.sec_neq_sec_reset Hpref). }
    eapply Permutation_NoDup; [symmetry; exact Hperm|].
    rewrite app_assoc.
    apply NoDup_app'; [exact Hndvl|exact Hndrs|exact Hdisj].
  Qed.

  Lemma generated_sys_signature_scope_sec:
    forall all_nodes G s env aux_names sig,
      generate_node_env all_nodes = OK (env, aux_names) ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      signature_scope_sec sig.
  Proof.
    intros all_nodes G s env aux_names sig Henvgen Hsig ty Hin.
    destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
      as (clk_id & rst_id & x & _ & _ & Hfind).
    eapply NAMEGEN.generate_node_env_sec_range in Hfind; eauto.
  Qed.




  Lemma generate_reset_env_props':
    forall trs env acc st reset_env rids st',
      env_reset_bounded st env ->
      NoDupMembers (env_values env) ->
      generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
      env_reset_bounded st' reset_env
      /\ NoDupMembers (env_values reset_env).
  Proof.
    induction trs as [|tr trs IH]; intros env acc st reset_env rids st'
                                          Hbound Hnodup Hgen.
    - simpl in Hgen. inversion Hgen; subst. auto.
    - simpl in Hgen.
      destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
      1,2,4: eapply IH; eauto.
      eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
      destruct (fresh_reset_insert_env_props _ _ _ _ _ _
                  Hbound Hnodup Hstep) as [Hbound1 Hnodup1].
      eapply IH; eauto.
  Qed.

  Lemma generate_reset_env_injective:
    forall trs reset_env rids st',
      generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
      forall x y tx ty,
        Env.find x reset_env = Some tx ->
        Env.find y reset_env = Some ty ->
        tx = ty ->
        x = y.
  Proof.
    intros trs reset_env rids st' Hgen.
    unfold generate_reset_env in Hgen.
    destruct (generate_reset_env' trs (Env.empty _) nil init_state)
      as [[[reset_env0 rids0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst reset_env rids st'.
    intros x y tx ty Hfindx Hfindy Heq.
    destruct (generate_reset_env_props' trs (Env.empty _) nil init_state reset_env0 rids0 st0)
      as [_ Hnodup];
      eauto.
    - intros z tz Hz. rewrite Env.gempty in Hz. discriminate.
    - constructor.
    - eapply env_values_nodup_injective; eauto.
  Qed.

  Lemma generate_reset_env'_has_reset_stmt:
    forall trs env acc st reset_env rids st' x ck f,
      generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
      In (TcReset x ck f) trs ->
      exists ty, Env.find x reset_env = Some ty.
  Proof.
    induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ck f Hgen Hin.
    - inversion Hin.
    - simpl in Hgen.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst tr.
        eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
        exists i.
        eapply generate_reset_env'_preserves_find; eauto.
        unfold assign_reset_type in Hstep.
        unfold fresh_reset_insert in Hstep.
        destruct (Env.mem x env) eqn:Hmem; try discriminate.
        eapply sec_bind_inv in Hstep as (v & stv & Hfreshid & Hstep).
        eapply sec_bind_inv in Hstep as (env0 & ste & Hins & Hdone).
        unfold fresh_reset_ident in Hfreshid. inversion Hfreshid; subst v stv.
        unfold insert_env, ret in Hins. inversion Hins; subst env0 ste.
        unfold ret in Hdone. inversion Hdone; subst env1 i st1.
        rewrite Env.gss. reflexivity.
      + destruct tr as [x0 ck0 ce|x0 ck0 e|x0 rck0 f0|x0 xs ck0 b f0 exps].
        1,2,4: eauto.
        eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
        eauto.
  Qed.

  Lemma generate_reset_env_has_reset_stmt:
    forall trs reset_env rids st' x ck f,
      generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
      In (TcReset x ck f) trs ->
      exists ty, Env.find x reset_env = Some ty.
  Proof.
    intros trs reset_env rids st' x ck f Hgen Hin.
    unfold generate_reset_env in Hgen.
    eapply generate_reset_env'_has_reset_stmt; eauto.
  Qed.

  Lemma trconstrs_reset_keys_app:
    forall trs1 trs2,
      SECSTCTYPING.trconstrs_reset_keys (trs1 ++ trs2)
      = SECSTCTYPING.trconstrs_reset_keys trs1
          ++ SECSTCTYPING.trconstrs_reset_keys trs2.
  Proof.
    induction trs1 as [|tr trs1 IH]; intros trs2; simpl.
    - reflexivity.
    - rewrite IH, app_assoc. reflexivity.
  Qed.

  (** Source names carried by a system are atoms or gensyms drawn from
      the translation prefixes, never [sec] gensyms; the security
      identifiers therefore never clash with program variables. *)

  Lemma atom_or_gensym_not_sec:
    forall x i,
      AtomOrGensym (PSP.of_list gensym_prefs) x ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros x i Hgood Heq.
    destruct Hgood as [Hat|Hex].
    - rewrite Heq in Hat.
      eapply gensym_not_atom; eauto.
    - unfold PS.Exists in Hex.
      destruct Hex as (pre & Hinpre & m & Hm).
      rewrite Heq in Hm.
      symmetry in Hm.
      apply gensym_injective in Hm as [Hpre _]. subst pre.
      apply PSP.of_list_1 in Hinpre.
      apply SetoidList.InA_alt in Hinpre as (pre' & Heq' & Hinpre).
      subst pre'.
      exact (Ids.sec_not_in_gensym_prefs Hinpre).
  Qed.

  Lemma sys_name_not_sec_gensym:
    forall s x i,
      In x (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
              ++ map fst s.(SynStc.s_lasts)) ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros s x i Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct s.(SynStc.s_good) as [Hgood _].
      rewrite Forall_forall in Hgood.
      eapply atom_or_gensym_not_sec; eauto.
    - destruct s.(SynStc.s_good) as [_ [Hgood _]].
      rewrite Forall_forall in Hgood.
      eapply atom_or_gensym_not_sec; eauto.
  Qed.

  (** [s_nodup] separates the hidden names (locals and lasts) from the
      visible ones (inputs and outputs). *)

  Lemma sys_hidden_visible_disjoint:
    forall s x,
      In x (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_lasts)) ->
      In x (map fst s.(SynStc.s_in) ++ map fst s.(SynStc.s_out)) ->
      False.
  Proof.
    intros s x Hh Hv.
    pose proof s.(SynStc.s_nodup) as Hnd.
    apply in_app_iff in Hh as [Hb|Hd]; apply in_app_iff in Hv as [Ha|Hc].
    - eapply (NoDup_app_In x _ _ Hnd Ha).
      apply in_or_app; left; exact Hb.
    - apply NoDup_app_r in Hnd.
      eapply (NoDup_app_In x _ _ Hnd Hb).
      apply in_or_app; left; exact Hc.
    - eapply (NoDup_app_In x _ _ Hnd Ha).
      apply in_or_app; right; apply in_or_app; right; exact Hd.
    - apply NoDup_app_r in Hnd. apply NoDup_app_r in Hnd.
      eapply (NoDup_app_In x _ _ Hnd Hc).
      exact Hd.
  Qed.

  (** The names eliminated by [simplify] are disjoint from the public
      scope of the generated signature.  Locals and lasts are hidden
      because their source names differ from the inputs, outputs and
      auxiliary identifiers; reset instances are hidden because they
      carry the [sec_reset] prefix. *)

  Lemma generated_sys_hidden_disjoint:
    forall s env aux_names
           clk_id rst_id clk_type rst_type inp out slocals slasts
           reset_env rids ty,
      env_injective env ->
      (forall x ty', Env.find x env = Some ty' ->
                     exists m, ty' = Ids.gensym Ids.sec m) ->
      (exists i j, clk_id = Ids.gensym Ids.sec i
                   /\ rst_id = Ids.gensym Ids.sec j) ->
      get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
      get_mappings_from_node s.(SynStc.s_out) env = Some out ->
      get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
      get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
      get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
      (forall x ty', Env.find x reset_env = Some ty' ->
                     exists n, ty' = Ids.gensym Ids.sec_reset n) ->
      In ty (SECSTCTYPING.hidden_sys_vars slocals slasts rids) ->
      ~ In ty (inp ++ out ++ [clk_type; rst_type]).
  Proof.
    intros s env aux_names
           clk_id rst_id clk_type rst_type inp out slocals slasts
           reset_env rids ty
           Hinj Hsecrange Hauxsec
           Haux Hclk Hrst Hinp Hout Hslocals Hslasts Hrids Hrstrange Hin Hvis.
    (* Every visible type is a [sec] gensym coming from a source name or
       from one of the two auxiliary identifiers. *)
    assert (Hviskey : exists x,
               (In x (map fst s.(SynStc.s_in) ++ map fst s.(SynStc.s_out))
                \/ x = clk_id \/ x = rst_id)
               /\ Env.find x env = Some ty).
    {
      repeat rewrite in_app_iff in Hvis.
      destruct Hvis as [Hv|[Hv|Hv]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hv)
          as (x & a & Hinx & Hfindx).
        exists x. split; [left; apply in_or_app; left|exact Hfindx].
        now apply in_map with (f := fst) in Hinx.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hv)
          as (x & a & Hinx & Hfindx).
        exists x. split; [left; apply in_or_app; right|exact Hfindx].
        now apply in_map with (f := fst) in Hinx.
      - destruct Hv as [Hv|[Hv|[]]].
        + subst ty. exists clk_id. split; [right; left; reflexivity|exact Hclk].
        + subst ty. exists rst_id. split; [right; right; reflexivity|exact Hrst].
    }
    destruct Hviskey as (x' & Hx'where & Hx'find).
    unfold SECSTCTYPING.hidden_sys_vars in Hin.
    apply nodup_In in Hin.
    repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|Hin]].
    - (* a local *)
      destruct (get_mappings_from_node_In _ _ _ _ _ Hslocals Hin)
        as (x & a & Hinx & Hfindx).
      assert (x = x') by (eapply Hinj; eauto). subst x'.
      destruct Hx'where as [Hx'|Hx'].
      + eapply sys_hidden_visible_disjoint; [|exact Hx'].
        apply in_or_app; left. now apply in_map with (f := fst) in Hinx.
      + destruct Hauxsec
          as (i & j & Hi & Hj).
        assert (Hxs : In x (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_vars)
                                       ++ s.(SynStc.s_out))
                              ++ map fst s.(SynStc.s_lasts))).
        { apply in_or_app; left.
          rewrite map_app. apply in_or_app; right.
          rewrite map_app. apply in_or_app; left.
          now apply in_map with (f := fst) in Hinx. }
        destruct Hx' as [Hx'|Hx'].
        * rewrite Hx', Hi in Hxs.
          exact (sys_name_not_sec_gensym s _ i Hxs Logic.eq_refl).
        * rewrite Hx', Hj in Hxs.
          exact (sys_name_not_sec_gensym s _ j Hxs Logic.eq_refl).
    - (* a last *)
      destruct (get_mappings_from_node_In _ _ _ _ _ Hslasts Hin)
        as (x & a & Hinx & Hfindx).
      assert (x = x') by (eapply Hinj; eauto). subst x'.
      destruct Hx'where as [Hx'|Hx'].
      + eapply sys_hidden_visible_disjoint; [|exact Hx'].
        apply in_or_app; right. now apply in_map with (f := fst) in Hinx.
      + destruct Hauxsec
          as (i & j & Hi & Hj).
        assert (Hxs : In x (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_vars)
                                       ++ s.(SynStc.s_out))
                              ++ map fst s.(SynStc.s_lasts))).
        { apply in_or_app; right.
          now apply in_map with (f := fst) in Hinx. }
        destruct Hx' as [Hx'|Hx'].
        * rewrite Hx', Hi in Hxs.
          exact (sys_name_not_sec_gensym s _ i Hxs Logic.eq_refl).
        * rewrite Hx', Hj in Hxs.
          exact (sys_name_not_sec_gensym s _ j Hxs Logic.eq_refl).
    - (* a reset instance: prefixes differ *)
      destruct (get_mappings_In _ _ _ _ Hrids Hin) as (o & _ & Hfindo).
      destruct (Hrstrange _ _ Hfindo) as (n2 & Hn2).
      destruct (Hsecrange _ _ Hx'find) as (n1 & Hn1).
      rewrite Hn1 in Hn2.
      apply gensym_injective in Hn2 as [Hpref _].
      exact (Ids.sec_neq_sec_reset Hpref).
  Qed.

  (** A well-scheduled body resets each instance at most once: the
      scheduling condition forces every later sub of an instance to
      carry a strictly smaller index than the current one, and a
      [TcReset] already sits at index 0. *)

  Lemma Is_well_sch_resets_nodup:
    forall tcs inputs mems,
      Is_well_sch inputs mems tcs ->
      NoDup (map fst (resets_of tcs)).
  Proof.
    induction tcs as [|tc tcs IH]; intros inputs mems Hsch; simpl.
    - constructor.
    - assert (Hsch' : Is_well_sch inputs mems tcs) by (inversion Hsch; auto).
      destruct tc as [x ck ce|x ck e|i ck f|i xs ck b g es]; simpl;
        try (now eapply IH; eauto).
      constructor.
      + intro Hin.
        eapply (WD.Reset_not_Reset_in tcs inputs mems i ck f Hsch).
        now apply SECSTCTYPING.resets_of_Reset_in.
      + eapply IH; eauto.
  Qed.

  (** The public scope of a generated STC signature is duplicate-free:
      inputs and outputs are images of distinct source names under an
      injective environment, and the two auxiliary names are distinct
      from each other and, being [sec] gensyms, from every source name. *)

  Theorem generate_sys_signature_scope_nodup:
    forall G s env aux_names sig,
      NAMEGEN.naming_env_props env aux_names ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      NoDup (signature_scope sig).
  Proof.
    intros G s env aux_names sig
           ((Hinjp & Hsecp) & (Hauxsecp & Hinstp & Hdistp)) Hsig.
    edestruct generate_sys_signature_inv as
        (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
         & reset_env & rids & st_reset & sconst & st_s
         & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
         & Hrenv & Hrids & Hsconst & Hsigdef); [exact Hsig|].
    subst sig. unfold signature_scope; simpl.
    assert (Hinj : env_injective env) by exact Hinjp.
    (* the whole scope is the image of one key list *)
    assert (Hmapio : get_mappings (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_out)))
                       env = Some (inp ++ out)).
    { rewrite map_app. eapply get_mappings_app;
        eapply get_mappings_from_node_eq; eauto. }
    assert (Hmapall :
              get_mappings (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_out))
                              ++ [clk_id; rst_id]) env
              = Some ((inp ++ out) ++ [clk_type; rst_type])).
    { eapply get_mappings_app; [exact Hmapio|].
      simpl. now rewrite Hclk, Hrst. }
    (* the key list is duplicate-free *)
    assert (Hndio : NoDup (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_out)))).
    { pose proof s.(SynStc.s_nodup) as Hnd.
      rewrite map_app. apply NoDup_app'.
      - now apply NoDup_app_l in Hnd.
      - apply NoDup_app_r in Hnd. apply NoDup_app_r in Hnd.
        now apply NoDup_app_l in Hnd.
      - rewrite Forall_forall. intros x Hinx Hxout.
        eapply (NoDup_app_In x _ _ Hnd Hinx).
        apply in_or_app; right. apply in_or_app; now left. }
    assert (Hauxnotin : forall x, List.In x [clk_id; rst_id] ->
                                  ~ List.In x (map fst (s.(SynStc.s_in)
                                                          ++ s.(SynStc.s_out)))).
    { intros x Hx Hin.
      destruct (Hauxsecp _ _ _ Haux) as (i & j & Hi & Hj).
      rewrite map_app in Hin.
      eapply (sys_name_not_sec_gensym s x
                (if ident_eq_dec x clk_id then i else j)).
      - apply in_or_app; left.
        rewrite map_app. apply in_app_iff in Hin as [H|H].
        + apply in_or_app; now left.
        + apply in_or_app; right. rewrite map_app. apply in_or_app; now right.
      - destruct Hx as [Heq|[Heq|[]]]; subst x.
        + destruct (ident_eq_dec clk_id clk_id); [exact Hi|contradiction].
        + destruct (ident_eq_dec rst_id clk_id) as [He|_]; [rewrite He|]; auto. }
    assert (Hndkeys : NoDup (map fst (s.(SynStc.s_in) ++ s.(SynStc.s_out))
                               ++ [clk_id; rst_id])).
    { apply NoDup_app'; [exact Hndio| |].
      - constructor.
        + intro Hin. simpl in Hin. destruct Hin as [Heq|[]].
          eapply (NAMEGEN.aux_clk_rst_distinct_get_node_aux
                    _ _ _ _ Hdistp Haux).
          symmetry. exact Heq.
        + constructor; [intro Hin; inversion Hin|constructor].
      - rewrite Forall_forall. intros x Hinx Hxaux.
        eapply Hauxnotin; eauto. }
    assert (Hnd : NoDup ((inp ++ out) ++ [clk_type; rst_type]))
      by (eapply get_mappings_nodup_gen; eauto).
    now rewrite <- app_assoc in Hnd.
  Qed.

  (** Every generated STC signature is good: its constraints are well
      formed and their targets are exactly the signature outputs.  This
      is the STC counterpart of [generate_node_sig_good_from_local_env]
      on the NLustre side; the extra work is that the raw targets now
      also cover lasts and reset instances, both of which [simplify]
      eliminates. *)

  Theorem generate_sys_signature_good:
    forall G P s env aux_names sig,
      NAMEGEN.naming_env_props env aux_names ->
      secglobal_scoped G ->
      Clo.wc_system P s ->
      (** Well-scheduling, which gives that the system resets each
          instance at most once.  Two [TcReset]s for one instance would
          emit two constraints on the same target, so some such
          condition is genuinely needed; [Well_scheduled] is already a
          standing assumption of the Stc-to-Obc pipeline. *)
      Is_well_sch (map fst s.(SynStc.s_in))
                  (ps_from_list (map fst s.(SynStc.s_lasts)))
                  s.(SynStc.s_tcs) ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      signature_good sig.
  Proof.
    intros G P s env aux_names sig
           ((Hinjp & Hsecp) & (Hauxsecp & Hinstp & Hdistp)) Hglobsc Hwc Hsch Hsig.
    assert (Hndkeys : NoDup (map fst (resets_of s.(SynStc.s_tcs))))
      by (eapply Is_well_sch_resets_nodup; eauto).
    assert (Hinj : env_injective env) by exact Hinjp.
    pose proof (SECSTCTYPING.generate_sys_signature_scoped
                  G P s env aux_names sig Hglobsc Hinj Hwc Hsig) as Hsigscoped.
    edestruct generate_sys_signature_inv as
        (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
         & reset_env & rids & st_reset & sconst & st_s
         & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
         & Hresetenv & Hrids & Hsconst & Hsigdef); eauto.
    remember (SECSTCTYPING.hidden_sys_vars slocals slasts rids) as hid eqn:Hhid.
    subst sig.
    set (nsig := {| s_name := s.(SynStc.s_name);
                    s_in := inp;
                    s_out := out;
                    s_reset := rst_type;
                    s_clk := clk_type;
                    s_constraints := SymTypes.simplify sconst hid |}) in *.

    (* The eliminated names never show up in the public scope. *)
    assert (Hdisj : forall ty, In ty hid -> ~ In ty (signature_scope nsig)).
    { intros ty Hinty. subst nsig. unfold signature_scope; cbn.
      subst hid.
      assert (Hinj0 : env_injective env) by exact Hinjp.
      assert (Hsec0 : forall x tz, Env.find x env = Some tz ->
                                   exists m, tz = Ids.gensym Ids.sec m)
        by exact Hsecp.
      assert (Haux0 : exists i j, clk_id = Ids.gensym Ids.sec i
                                  /\ rst_id = Ids.gensym Ids.sec j)
        by (eapply Hauxsecp; eauto).
      assert (Hrst0 : forall x tz, Env.find x reset_env = Some tz ->
                                   exists m, tz = Ids.gensym Ids.sec_reset m)
        by exact (proj2 (Hinstp _ _ Hresetenv)).
      eapply generated_sys_hidden_disjoint; eassumption. }

    (* Name-level distinctness, transported to the transition constraints. *)
    assert (Hndvl : NoDup (variables s.(SynStc.s_tcs) ++ lasts_of s.(SynStc.s_tcs))).
    { eapply Permutation_NoDup with
        (l := (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_out))
                ++ map fst s.(SynStc.s_lasts)).
      - apply Permutation_app.
        + exact (SynStc.s_vars_out_in_tcs s).
        + exact (SynStc.s_lasts_in_tcs s).
      - rewrite <- app_assoc.
        pose proof s.(SynStc.s_nodup) as Hnd.
        now apply NoDup_app_r in Hnd. }
    assert (Hnddef : NoDup (Def.defined s.(SynStc.s_tcs))).
    { eapply Permutation_NoDup; [symmetry; exact (Def.s_defined s)|exact Hndvl]. }

    (* Type-level images of the three families of targets. *)
    assert (Hvo : get_mappings (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_out))
                    env = Some (slocals ++ out)).
    { apply get_mappings_app; eapply get_mappings_from_node_eq; eauto. }
    destruct (get_mappings_Permutation_Some _ _ _ _ (SynStc.s_vars_out_in_tcs s) Hvo)
      as (vs & Hvs).
    assert (Hpermvs : Permutation (slocals ++ out) vs).
    { eapply get_mappings_perm;
        [|exact (SynStc.s_vars_out_in_tcs s)|exact Hinj|exact Hvo|exact Hvs].
      pose proof s.(SynStc.s_nodup) as Hnd.
      apply NoDup_app_r in Hnd.
      rewrite app_assoc in Hnd.
      apply NoDup_app'_iff in Hnd as [Hnd' _]. exact Hnd'. }
    assert (Hls0 : get_mappings (map fst s.(SynStc.s_lasts)) env = Some slasts)
      by (eapply get_mappings_from_node_eq; eauto).
    destruct (get_mappings_Permutation_Some _ _ _ _ (SynStc.s_lasts_in_tcs s) Hls0)
      as (ls & Hls).
    assert (Hpermls : Permutation slasts ls).
    { eapply get_mappings_perm;
        [|exact (SynStc.s_lasts_in_tcs s)|exact Hinj|exact Hls0|exact Hls].
      pose proof s.(SynStc.s_nodup) as Hnd.
      apply NoDup_app_r, NoDup_app_r, NoDup_app_r in Hnd. exact Hnd. }
    pose proof Hrids as Hrs.
    assert (Hndrids : NoDup rids).
    { eapply get_mappings_nodup_gen; [exact Hndkeys| |exact Hrs].
      exact (proj1 (Hinstp _ _ Hresetenv)). }

    (* Shape and well-formedness of the raw constraints. *)
    destruct (SECSTCTYPING.generate_trconstrs_constraints_targets
                G env reset_env clk_type rst_type s.(SynStc.s_tcs) sconst st_reset st_s
                Hinj Hnddef Hsconst) as (tys & Htys & Hsnd).
    assert (Hsecrange : forall x ty, Env.find x env = Some ty ->
                                     exists n, ty = Ids.gensym Ids.sec n).
    { intros x ty Hf. eapply Hsecp; eauto. }
    assert (Hrstrange : forall x ty, Env.find x reset_env = Some ty ->
                                     exists n, ty = Ids.gensym Ids.sec_reset n).
    { exact (proj2 (Hinstp _ _ Hresetenv)). }
    assert (Hndtys : NoDup tys)
      by exact (targets_nodup env reset_env s.(SynStc.s_tcs) tys vs ls rids
                  Hinj Hsecrange Hrstrange Htys Hvs Hls Hrs Hndvl Hndrids).
    assert (Hwfraw : wf_constraints sconst)
      by exact (SECSTCTYPING.generate_trconstrs_constraints_wf
                  G env reset_env clk_type rst_type s.(SynStc.s_tcs) sconst
                  st_reset st_s tys Hinj Hnddef Hsconst Htys Hndtys).
    assert (Hpermtys : Permutation tys (slocals ++ out ++ slasts ++ rids)).
    { etransitivity.
      - exact (SECSTCTYPING.trconstrs_targets_perm
                 env reset_env s.(SynStc.s_tcs) tys vs ls rids Htys Hvs Hls Hrs).
      - transitivity ((slocals ++ out) ++ slasts ++ rids).
        + apply Permutation_app; [symmetry; exact Hpermvs|].
          apply Permutation_app; [symmetry; exact Hpermls|reflexivity].
        + rewrite <- app_assoc. reflexivity. }
    assert (Hpermraw : Permutation (map snd sconst)
                         (map (fun ty => [ty]) (slocals ++ out ++ slasts ++ rids))).
    { rewrite Hsnd. apply Permutation_map. exact Hpermtys. }
    assert (Hndall : NoDup (slocals ++ out ++ slasts ++ rids)).
    { eapply NoDup_map_inv with (f := fun ty => [ty]).
      eapply Permutation_NoDup; [exact Hpermraw|exact (proj1 Hwfraw)]. }
    assert (Hwf_simpl : wf_constraints (SymTypes.simplify sconst hid)).
    { split.
      - eapply SymTypes.simplify_nodup. exact (proj1 Hwfraw).
      - eapply SymTypes.simplify_singleton_rhs. exact (proj2 Hwfraw). }

    unfold signature_good. subst nsig. cbn.
    split; [exact Hwf_simpl|].
    apply NoDup_Permutation.
    - exact (proj1 Hwf_simpl).
    - apply SIG.nodup_singleton_map.
      apply NoDup_app_r in Hndall.
      apply NoDup_app'_iff in Hndall as [Hndout _]. exact Hndout.
    - intros rhs; split; intro Hinr.
      + pose proof (SymTypes.simplify_rhs_in _ _ _ Hinr) as Hinraw.
        eapply Permutation_in in Hinraw; [|exact Hpermraw].
        apply in_map_iff in Hinraw as (ty & Hrhs & Hinall).
        subst rhs.
        assert (Hcase : In ty out \/ In ty hid).
        { subst hid. unfold SECSTCTYPING.hidden_sys_vars.
          apply in_app_iff in Hinall as [H1|Hinall].
          - right. apply nodup_In. apply in_or_app; left; exact H1.
          - apply in_app_iff in Hinall as [H2|Hinall].
            + left; exact H2.
            + right. apply nodup_In. apply in_or_app; right; exact Hinall. }
        destruct Hcase as [Hcase|Hcase].
        * apply in_map_iff. exists ty. split; [reflexivity|exact Hcase].
        * exfalso.
          destruct (SymTypes.findST_of_rhs_in _ _ Hinr) as (stc & Hfindrhs).
          apply SymTypes.find_correct in Hfindrhs.
          unfold signature_scoped in Hsigscoped. cbn in Hsigscoped.
          eapply Forall_forall in Hsigscoped; [|exact Hfindrhs].
          eapply Hdisj; [exact Hcase|].
          unfold signature_scope; cbn.
          eapply constraint_scoped_rhs; [exact Hsigscoped|now left].
      + apply in_map_iff in Hinr as (ty & Hrhs & Hinout).
        subst rhs.
        assert (Hinsigscope : In ty (signature_scope
                    {| s_name := s.(SynStc.s_name);
                       s_in := inp;
                       s_out := out;
                       s_reset := rst_type;
                       s_clk := clk_type;
                       s_constraints := SymTypes.simplify sconst hid |})).
        { unfold signature_scope; cbn.
          apply in_or_app; right. apply in_or_app; left. exact Hinout. }
        eapply SymTypes.simplify_preserves_other_rhs.
        * intros d Hd Htyeq. subst d.
          exact (Hdisj ty Hd Hinsigscope).
        * eapply Permutation_in; [symmetry; exact Hpermraw|].
          apply in_map_iff. exists ty. split; [reflexivity|].
          apply in_or_app; right. apply in_or_app; left. exact Hinout.
  Qed.

  (** ** Side conditions for the downstream bridge

      The Stc counterparts of [node_scope_fresh_in_env] and
      [generated_node_simplify_ready].  A system's raw constraints range
      over more than a node's do -- the lasts and the reset instances are
      hidden alongside the locals -- so both conditions are phrased
      against that wider list, which is exactly the raw scope the
      Stc-to-Obc bridge works in. *)

  Definition sys_scope_fresh_in_env
    (s: SynStc.system) (env: Env.t ident)
    (aux_names: list node_aux_names) (G: secglobal) : Prop :=
    forall clk_id rst_id clk_type rst_type inp out slocals slasts reset_env rids,
      get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
      get_mappings_from_node s.(SynStc.s_out) env = Some out ->
      get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
      get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
      get_node_inst s.(SynStc.s_name) aux_names = Some reset_env ->
      get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
      SIG.secglobal_scope_fresh
        (inp ++ out ++ slocals ++ slasts ++ rids ++ [clk_type; rst_type]) G.

  Definition generated_sys_simplify_ready
    (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
    forall G s sig clk_id rst_id clk_type rst_type inp out slocals slasts
           reset_env rids raw st_reset st_s,
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
      get_mappings_from_node s.(SynStc.s_out) env = Some out ->
      get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
      get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
      get_node_inst s.(SynStc.s_name) aux_names = Some reset_env ->
      get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
      SECSTCTYPING.generate_trconstrs_constraints G env reset_env clk_type rst_type
        s.(SynStc.s_tcs) st_reset = OK (raw, st_s) ->
      (** Well-schedulability, as for [generate_sys_signature_good]: two
          [TcReset]s for one instance would put the same target on two
          constraints, which is exactly what [wf_constraints] forbids.
          It is already a standing assumption of the Stc-to-Obc
          pipeline.  NLustre needs no counterpart. *)
      Is_well_sch (map fst s.(SynStc.s_in))
                  (ps_from_list (map fst s.(SynStc.s_lasts))) s.(SynStc.s_tcs) ->
      sig = {| s_name := s.(SynStc.s_name);
               s_in := inp;
               s_out := out;
               s_reset := rst_type;
               s_clk := clk_type;
               s_constraints :=
                 SymTypes.simplify raw
                   (SECSTCTYPING.hidden_sys_vars slocals slasts rids) |} ->
      wf_constraints raw
      /\ (forall x, In x (SECSTCTYPING.hidden_sys_vars slocals slasts rids) ->
                    ~ In x (signature_scope sig)).

  (** ** Discharging the two side conditions

      The Stc counterparts of NLustre's
      [generated_node_simplify_ready_from_generated_env] and
      [node_scope_fresh_in_env_from_bounds]. *)

  Lemma generate_sys_signature_raw_wf:
    forall G s env aux_names clk_type rst_type
           out slocals slasts reset_env rids sconst st_reset st_s,
      env_injective env ->
      (forall x ty, Env.find x env = Some ty ->
                    exists m, ty = Ids.gensym Ids.sec m) ->
      env_injective reset_env ->
      (forall x ty, Env.find x reset_env = Some ty ->
                    exists m, ty = Ids.gensym Ids.sec_reset m) ->
      Is_well_sch (map fst s.(SynStc.s_in))
                  (ps_from_list (map fst s.(SynStc.s_lasts))) s.(SynStc.s_tcs) ->
      get_mappings_from_node s.(SynStc.s_out) env = Some out ->
      get_mappings_from_node s.(SynStc.s_vars) env = Some slocals ->
      get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts ->
      get_node_inst s.(SynStc.s_name) aux_names = Some reset_env ->
      get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
      SECSTCTYPING.generate_trconstrs_constraints G env reset_env clk_type rst_type
        s.(SynStc.s_tcs) st_reset = OK (sconst, st_s) ->
      wf_constraints sconst.
  Proof.
    intros G s env aux_names clk_type rst_type
           out slocals slasts reset_env rids sconst st_reset st_s
           Hinj Hsecrange Hinstinj Hrstrange
           Hsch Hout Hslocals Hslasts Hresetenv Hrids Hsconst.
    assert (Hndvl : NoDup (variables s.(SynStc.s_tcs) ++ lasts_of s.(SynStc.s_tcs))).
    { eapply Permutation_NoDup with
        (l := (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_out))
                ++ map fst s.(SynStc.s_lasts)).
      - apply Permutation_app.
        + exact (SynStc.s_vars_out_in_tcs s).
        + exact (SynStc.s_lasts_in_tcs s).
      - rewrite <- app_assoc.
        pose proof s.(SynStc.s_nodup) as Hnd.
        now apply NoDup_app_r in Hnd. }
    assert (Hnddef : NoDup (Def.defined s.(SynStc.s_tcs)))
      by (eapply Permutation_NoDup; [symmetry; exact (Def.s_defined s)|exact Hndvl]).
    destruct (SECSTCTYPING.generate_trconstrs_constraints_targets
                G env reset_env clk_type rst_type s.(SynStc.s_tcs) sconst
                st_reset st_s Hinj Hnddef Hsconst) as (tys & Htys & Hsnd).
    assert (Hvo : get_mappings (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_out))
                    env = Some (slocals ++ out))
      by (apply get_mappings_app; eapply get_mappings_from_node_eq; eauto).
    destruct (get_mappings_Permutation_Some _ _ _ _ (SynStc.s_vars_out_in_tcs s) Hvo)
      as (vs & Hvs).
    assert (Hls0 : get_mappings (map fst s.(SynStc.s_lasts)) env = Some slasts)
      by (eapply get_mappings_from_node_eq; eauto).
    destruct (get_mappings_Permutation_Some _ _ _ _ (SynStc.s_lasts_in_tcs s) Hls0)
      as (ls & Hls).
    assert (Hndrids : NoDup rids).
    { eapply get_mappings_nodup_gen;
        [eapply Is_well_sch_resets_nodup; exact Hsch|exact Hinstinj|exact Hrids]. }
    exact (SECSTCTYPING.generate_trconstrs_constraints_wf
             G env reset_env clk_type rst_type s.(SynStc.s_tcs) sconst
             st_reset st_s tys Hinj Hnddef Hsconst Htys
             (targets_nodup env reset_env s.(SynStc.s_tcs) tys vs ls rids
                Hinj Hsecrange Hrstrange Htys Hvs Hls Hrids Hndvl Hndrids)).
  Qed.

  (** Everything the two halves need about the naming pass is exactly
      [naming_env_props], so this one proof serves both the flat
      whole-program environment and a single node's local environment;
      the two corollaries below differ only in which constructor of that
      bundle they invoke. *)

  Theorem generated_sys_simplify_ready_from_naming_props:
    forall env aux_names,
      NAMEGEN.naming_env_props env aux_names ->
      generated_sys_simplify_ready env aux_names.
  Proof.
    intros env aux_names ((Hinj0 & Hsec0) & (Hauxsec & Hinstprops & _))
           G s sig clk_id rst_id clk_type rst_type inp out slocals slasts
           reset_env rids raw st_reset st_s
           Hsig Haux Hclk Hrst Hinp Hout Hslocals Hslasts Hresetenv Hrids
           Hraw Hsch Hsigdef.
    destruct (Hinstprops _ _ Hresetenv) as (Hinstinj0 & Hrst0).
    assert (Haux0 : exists i j, clk_id = Ids.gensym Ids.sec i
                                /\ rst_id = Ids.gensym Ids.sec j)
      by (eapply Hauxsec; eauto).
    split.
    - eapply generate_sys_signature_raw_wf;
        [exact Hinj0|exact Hsec0|exact Hinstinj0|exact Hrst0
        |exact Hsch|exact Hout|exact Hslocals|exact Hslasts
        |exact Hresetenv|exact Hrids|exact Hraw].
    - intros ty Hinhid. subst sig. unfold signature_scope; cbn.
      eapply generated_sys_hidden_disjoint;
        [exact Hinj0|exact Hsec0|exact Haux0|exact Haux|exact Hclk|exact Hrst
        |exact Hinp|exact Hout|exact Hslocals|exact Hslasts|exact Hrids
        |exact Hrst0|exact Hinhid].
  Qed.

  Corollary generated_sys_simplify_ready_from_generated_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      generated_sys_simplify_ready env aux_names.
  Proof.
    intros all_nodes env aux_names Henv.
    eapply generated_sys_simplify_ready_from_naming_props.
    eapply NAMEGEN.naming_env_props_from_generated_env; eauto.
  Qed.

  (** Every name the generator hands out is a [sec] gensym minted at or
      after [st].  This is the Stc reading of what
      [generate_local_env_for_node] gives NLustre. *)

  Definition env_sec_lower_bounded (e: Env.t ident) (st: ident) : Prop :=
    forall x ty,
      Env.find x e = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive.

  Lemma sys_scope_fresh_in_env_from_bounds:
    forall s env aux_names G st,
      (forall ie x ty,
          get_node_inst s.(SynStc.s_name) aux_names = Some ie ->
          Env.find x ie = Some ty ->
          exists n, ty = Ids.gensym Ids.sec_reset n) ->
      env_sec_lower_bounded env st ->
      SIG.secglobal_scope_bounded_above G st ->
      (** the reset instances are outside the bound argument entirely:
          they are [sec_reset] names, and a signature scope holds only
          [sec] ones *)
      SIG.secglobal_scope_sec G ->
      sys_scope_fresh_in_env s env aux_names G.
  Proof.
    intros s env aux_names G st Hrstrange Hlo Hhi Hgsec
           clk_id rst_id clk_type rst_type inp out slocals slasts reset_env rids
           Haux Hclk Hrst Hinp Hout Hslocals Hslasts Hresetenv Hrids
           f sig Hfind ty Hinscope Hinsig.
    assert (Hsplit : In ty rids
                     \/ In ty (inp ++ out ++ slocals ++ slasts
                                 ++ [clk_type; rst_type]))
      by (repeat rewrite in_app_iff in *; tauto).
    destruct Hsplit as [Hinr|Hin'].
    - (* a reset instance: wrong gensym prefix for any signature scope *)
      destruct (get_mappings_In _ _ _ _ Hrids Hinr) as (o & _ & Hfindo).
      eapply SIG.sec_reset_not_in_signature_scope;
        [eapply Hgsec; exact Hfind
        |exact (Hrstrange _ _ _ Hresetenv Hfindo)
        |exact Hinsig].
    - (* everything else: minted at or after [st], so above the accumulator *)
      assert (Hsub : SIG.scope_lower_bounded
                       (inp ++ out ++ slocals ++ slasts
                          ++ [clk_type; rst_type]) st).
      { intros ty' Hin''.
        assert (Hfindty : exists x, Env.find x env = Some ty').
        { repeat (apply in_app_iff in Hin'' as [Hin''|Hin'']);
            [ apply get_mappings_from_node_eq in Hinp
            | apply get_mappings_from_node_eq in Hout
            | apply get_mappings_from_node_eq in Hslocals
            | apply get_mappings_from_node_eq in Hslasts
            | ].
          1-4: match goal with
               | H: get_mappings _ _ = Some _ |- _ =>
                   destruct (get_mappings_In _ _ _ _ H Hin'') as (x & _ & Hf);
                   now exists x
               end.
          destruct Hin'' as [Heq|[Heq|[]]]; subst ty'; eauto. }
        destruct Hfindty as (x & Hfindty). exact (Hlo _ _ Hfindty). }
      exact (SIG.scope_fresh_from_bounds _ _ _ Hsub (Hhi f sig Hfind) ty Hin' Hinsig).
  Qed.

  (** ** Per-node bounds

      In the scoped setting a system's environment is the one
      [generate_local_env_for_node] minted for it, so its names sit
      strictly between the state before and after that node.  These are
      the Stc readings of NLustre's
      [node_scope_lower_bounded_from_local_env] and
      [generated_node_sig_scope_upper_bound_from_local_env]. *)

  (** ** Relating two signature accumulators

      The scheduler is [map schedule_system], so it never reorders the
      program: the two generator runs build their accumulators in
      lockstep and every callee lookup on one side has a matching lookup
      on the other.  This records that, with the shape facts the
      call-preservation theorems need. *)

  Definition sig_env_preserved (G G': secglobal) : Prop :=
    forall f n,
      find_signature f G = Some n ->
      exists n', find_signature f G' = Some n'
                 /\ signatures_preserved n n'
                 /\ signature_good n
                 /\ NoDup (signature_scope n)
                 /\ signature_scoped n'.

  (** The call actuals a [TcCall] hands to the callee are computed from
      the environment alone, so both runs produce the same ones.  Stated
      against the generator's own equations, which is the only place the
      actuals exist. *)

  Definition call_actuals_in_scope
    (env: Env.t ident) (base_ty: ident) (scope: list ident)
    (e: SynStc.trconstr) : Prop :=
    forall i xs ck rst f es inptyp ckty outtyp sa sb sc sd se sf,
      e = SynStc.TcCall i xs ck rst f es ->
      option_to_sec (assign_clk_type env base_ty ck) sa = OK (ckty, sb) ->
      mmap (fun x => option_to_sec (assign_exp_type env x)) es sc
        = OK (inptyp, sd) ->
      mmap (fun x => find_env x env) xs se = OK (outtyp, sf) ->
      SIG.call_actuals_scoped scope inptyp ckty outtyp.

  (** Which is just the clocking judgement read through the environment
      -- the same reading the scoping theorem makes. *)

  Lemma call_actuals_in_scope_from_wc:
    forall P vars env base_ty scope e,
      wc_env vars ->
      Clo.wc_trconstr P vars e ->
      SECSTCTYPING.vars_env_scoped env vars scope ->
      In base_ty scope ->
      call_actuals_in_scope env base_ty scope e.
  Proof.
    intros P vars env base_ty scope e Henv Hwc Hvars Hbase
           i xs ck rst f es inptyp ckty outtyp sa sb sc sd se sf
           Heq Hck Hinp Hout.
    subst e.
    eapply SECSTCTYPING.wc_trconstr_call_actuals_scoped; eauto.
  Qed.

  Lemma generate_trconstr_constraint_preserved:
    forall G G' env reset_env base_ty rst_ty scope e
           nconst sconst st1 st1' st2 st2',
      sig_env_preserved G G' ->
      SIG.secglobal_scope_fresh scope G ->
      In rst_ty scope ->
      call_actuals_in_scope env base_ty scope e ->
      (forall i xs ck f es rinst,
          e = SynStc.TcCall i xs ck true f es ->
          Env.find i reset_env = Some rinst ->
          In rinst scope) ->
      SECSTCTYPING.generate_trconstr_constraint G env reset_env base_ty rst_ty e
        st1 = OK (nconst, st1') ->
      SECSTCTYPING.generate_trconstr_constraint G' env reset_env base_ty rst_ty e
        st2 = OK (sconst, st2') ->
      preserves_on scope nconst sconst.
  Proof.
    intros G G' env reset_env base_ty rst_ty scope e
           nconst sconst st1 st1' st2 st2'
           Hpres Hfresh Hrst Hact Hrinst Hgen1 Hgen2.
    destruct e as [x ck ce|x ck ex|x ck f|i xs ck rst f es].
    - assert (Heq : nconst = sconst)
        by (eapply state_pure_det;
            [apply SECSTCTYPING.state_pure_generate_trconstr_constraint
             with (G := G) (env := env) (reset_env := reset_env)
                  (base_ty := base_ty) (rst_ty := rst_ty)
             |exact Hgen1|exact Hgen2]).
      subst sconst. apply preserves_on_refl.
    - assert (Heq : nconst = sconst)
        by (eapply state_pure_det;
            [apply SECSTCTYPING.state_pure_generate_trconstr_constraint
             with (G := G) (env := env) (reset_env := reset_env)
                  (base_ty := base_ty) (rst_ty := rst_ty)
             |exact Hgen1|exact Hgen2]).
      subst sconst. apply preserves_on_refl.
    - assert (Heq : nconst = sconst)
        by (eapply state_pure_det;
            [apply SECSTCTYPING.state_pure_generate_trconstr_constraint
             with (G := G) (env := env) (reset_env := reset_env)
                  (base_ty := base_ty) (rst_ty := rst_ty)
             |exact Hgen1|exact Hgen2]).
      subst sconst. apply preserves_on_refl.
    - simpl in Hgen1, Hgen2.
      destruct xs as [|y ys].
      { destruct rst; unfold ret in Hgen1, Hgen2;
          inversion Hgen1; inversion Hgen2; subst; apply preserves_on_refl. }
      destruct (find_signature f G) as [n|] eqn:Hfind;
        [|destruct rst; discriminate].
      destruct (Hpres _ _ Hfind)
        as (n' & Hfind' & Hpresnn' & Hgood & Hnd & Hscoped').
      rewrite Hfind' in Hgen2.
      assert (Hsf : SIG.scope_fresh scope n) by (eapply Hfresh; eauto).
      destruct rst.
      + eapply sec_bind_inv in Hgen1 as (ckty & sa1 & Hck1 & Hgen1).
        eapply sec_bind_inv in Hgen1 as (inptyp & sb1 & Hin1 & Hgen1).
        eapply sec_bind_inv in Hgen1 as (outtyp & sc1 & Hout1 & Hgen1).
        eapply sec_bind_inv in Hgen1 as (rinst & sd1 & Hri1 & Hgen1).
        eapply sec_bind_inv in Hgen2 as (ckty2 & sa2 & Hck2 & Hgen2).
        eapply sec_bind_inv in Hgen2 as (inptyp2 & sb2 & Hin2 & Hgen2).
        eapply sec_bind_inv in Hgen2 as (outtyp2 & sc2 & Hout2 & Hgen2).
        eapply sec_bind_inv in Hgen2 as (rinst2 & sd2 & Hri2 & Hgen2).
        assert (ckty2 = ckty)
          by (eapply state_pure_det;
              [apply state_pure_option_to_sec|exact Hck2|exact Hck1]).
        assert (inptyp2 = inptyp)
          by (eapply state_pure_det;
              [apply (state_pure_mmap
                        (fun x => option_to_sec (assign_exp_type env x)));
               intro; apply state_pure_option_to_sec
              |exact Hin2|exact Hin1]).
        assert (outtyp2 = outtyp)
          by (eapply state_pure_det;
              [apply (state_pure_mmap (fun x => find_env x env));
               intro; apply state_pure_find_env
              |exact Hout2|exact Hout1]).
        assert (rinst2 = rinst)
          by (eapply state_pure_det;
              [apply state_pure_find_env|exact Hri2|exact Hri1]).
        subst ckty2 inptyp2 outtyp2 rinst2.
        destruct (Hact i (y :: ys) ck true f es inptyp ckty outtyp
                    _ _ _ _ _ _ Logic.eq_refl Hck1 Hin1 Hout1)
          as (Hinpsc & Hcksc & Houtsc).
        assert (Hrisc : In rinst scope).
        { eapply Hrinst; [reflexivity|].
          unfold find_env in Hri1.
          destruct (Env.find i reset_env); [now inversion Hri1|discriminate]. }
        eapply signatures_preserved_equal_calls_from_good
          with (nsig := n) (ssig := n') (srcrst := [rinst]);
          [exact Hgood|exact Hnd|exact Hscoped'|exact Hpresnn'|exact Hsf| | 
          |exact Hgen1|exact Hgen2].
        * split; [split; [exact Hinpsc|split; [exact Hcksc|exact Houtsc]]|].
          apply st_scoped_singleton. exact Hrisc.
        * eapply SIG.call_subst_fresh_from_scope_fresh;
            [exact Hsf|exact Hinpsc|exact Hcksc
            |apply st_scoped_singleton; exact Hrisc|exact Houtsc].
      + eapply sec_bind_inv in Hgen1 as (ckty & sa1 & Hck1 & Hgen1).
        eapply sec_bind_inv in Hgen1 as (inptyp & sb1 & Hin1 & Hgen1).
        eapply sec_bind_inv in Hgen1 as (outtyp & sc1 & Hout1 & Hgen1).
        eapply sec_bind_inv in Hgen2 as (ckty2 & sa2 & Hck2 & Hgen2).
        eapply sec_bind_inv in Hgen2 as (inptyp2 & sb2 & Hin2 & Hgen2).
        eapply sec_bind_inv in Hgen2 as (outtyp2 & sc2 & Hout2 & Hgen2).
        assert (ckty2 = ckty)
          by (eapply state_pure_det;
              [apply state_pure_option_to_sec|exact Hck2|exact Hck1]).
        assert (inptyp2 = inptyp)
          by (eapply state_pure_det;
              [apply (state_pure_mmap
                        (fun x => option_to_sec (assign_exp_type env x)));
               intro; apply state_pure_option_to_sec
              |exact Hin2|exact Hin1]).
        assert (outtyp2 = outtyp)
          by (eapply state_pure_det;
              [apply (state_pure_mmap (fun x => find_env x env));
               intro; apply state_pure_find_env
              |exact Hout2|exact Hout1]).
        subst ckty2 inptyp2 outtyp2.
        destruct (Hact i (y :: ys) ck false f es inptyp ckty outtyp
                    _ _ _ _ _ _ Logic.eq_refl Hck1 Hin1 Hout1)
          as (Hinpsc & Hcksc & Houtsc).
        eapply signatures_preserved_equal_calls_from_good
          with (nsig := n) (ssig := n') (srcrst := [rst_ty]);
          [exact Hgood|exact Hnd|exact Hscoped'|exact Hpresnn'|exact Hsf| | 
          |exact Hgen1|exact Hgen2].
        * split; [split; [exact Hinpsc|split; [exact Hcksc|exact Houtsc]]|].
          apply st_scoped_singleton. exact Hrst.
        * eapply SIG.call_subst_fresh_from_scope_fresh;
            [exact Hsf|exact Hinpsc|exact Hcksc
            |apply st_scoped_singleton; exact Hrst|exact Houtsc].
  Qed.

  (** A whole body, generated twice from two accumulators.  The chunks
      line up one for one -- both runs walk the same [tcs] -- so no
      permutation is involved here; that is factored out and applied to
      the assembled result.  There are no target-side-only names at
      Stc-to-Stc, so every [extras] entry is empty and the freshness and
      duplication premises of the combinator are vacuous. *)

  Lemma generate_trconstrs_constraints_preserved:
    forall G G' env reset_env base_ty rst_ty scope tcs
           nconst sconst st1 st1' st2 st2',
      sig_env_preserved G G' ->
      SIG.secglobal_scope_fresh scope G ->
      In rst_ty scope ->
      Forall (call_actuals_in_scope env base_ty scope) tcs ->
      (forall i xs ck f es rinst,
          In (SynStc.TcCall i xs ck true f es) tcs ->
          Env.find i reset_env = Some rinst ->
          In rinst scope) ->
      constraints_scoped scope sconst ->
      SECSTCTYPING.generate_trconstrs_constraints G env reset_env base_ty rst_ty
        tcs st1 = OK (nconst, st1') ->
      SECSTCTYPING.generate_trconstrs_constraints G' env reset_env base_ty rst_ty
        tcs st2 = OK (sconst, st2') ->
      preserves_on scope nconst sconst.
  Proof.
    intros G G' env reset_env base_ty rst_ty scope tcs.
    induction tcs as [|tc tcs IH];
      intros nconst sconst st1 st1' st2 st2'
             Hpres Hfresh Hrst Hact Hrinst Hsc Hgen1 Hgen2.
    - simpl in Hgen1, Hgen2. unfold ret in Hgen1, Hgen2.
      inversion Hgen1; inversion Hgen2; subst. apply preserves_on_nil.
    - simpl in Hgen1, Hgen2.
      eapply sec_bind_inv in Hgen1 as (c1 & sa1 & Hhd1 & Hgen1).
      eapply sec_bind_inv in Hgen1 as (cs1 & sb1 & Htl1 & Hret1).
      unfold ret in Hret1. inversion Hret1; subst nconst st1'.
      eapply sec_bind_inv in Hgen2 as (c2 & sa2 & Hhd2 & Hgen2).
      eapply sec_bind_inv in Hgen2 as (cs2 & sb2 & Htl2 & Hret2).
      unfold ret in Hret2. inversion Hret2; subst sconst st2'.
      inversion Hact as [|tc' tcs' Hacthd Hacttl]; subst.
      apply Forall_app in Hsc as (Hsc1 & Hsc2).
      eapply preserves_on_concat_scoped with (extras1 := []) (extras2 := []).
      + simpl. constructor.
      + simpl. intros x [].
      + rewrite app_nil_r. exact Hsc1.
      + rewrite app_nil_r. exact Hsc2.
      + eapply generate_trconstr_constraint_preserved;
          [exact Hpres|exact Hfresh|exact Hrst|exact Hacthd| |exact Hhd1|exact Hhd2].
        intros i xs ck f es rinst Heq Hfind.
        subst tc. apply (Hrinst i xs ck f es rinst); [now left|exact Hfind].
      + eapply IH;
          [exact Hpres|exact Hfresh|exact Hrst|exact Hacttl| |exact Hsc2
          |exact Htl1|exact Htl2].
        intros i xs ck f es rinst Hin Hfind.
        apply (Hrinst i xs ck f es rinst); [now right|exact Hfind].
  Qed.

  (** ** Reordering a system's body preserves its signature

      The scheduler permutes [s_tcs] and changes nothing else.  Since
      constraint generation mints no identifiers, the raw constraints
      permute with identical names, so the two signatures preserve each
      other.  Only the hidden-name lists genuinely differ -- the reset
      instances are collected in body order -- and
      [preserves_on_simplify_bridge] allows those to be unrelated. *)

  Theorem generate_sys_signature_reorder_preserved:
    forall G G' P s s' env aux_names sig sig',
      s'.(SynStc.s_name) = s.(SynStc.s_name) ->
      s'.(SynStc.s_in) = s.(SynStc.s_in) ->
      s'.(SynStc.s_out) = s.(SynStc.s_out) ->
      s'.(SynStc.s_vars) = s.(SynStc.s_vars) ->
      s'.(SynStc.s_lasts) = s.(SynStc.s_lasts) ->
      Permutation s.(SynStc.s_tcs) s'.(SynStc.s_tcs) ->
      generated_sys_simplify_ready env aux_names ->
      Is_well_sch (map fst s.(SynStc.s_in))
                  (ps_from_list (map fst s.(SynStc.s_lasts))) s.(SynStc.s_tcs) ->
      Clo.wc_system P s ->
      secglobal_scoped G' ->
      sig_env_preserved G G' ->
      sys_scope_fresh_in_env s env aux_names G ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      SECSTCTYPING.generate_sys_signature G' s' env aux_names = OK sig' ->
      signatures_preserved sig sig'.
  Proof.
    intros G G' P s s' env aux_names sig sig'
           Hname Hin Hout Hvars Hlasts Hperm Hready Hsch Hwc Hscoped' Hpres
           Hfresh Hsig Hsig'.
    edestruct generate_sys_signature_inv as
        (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
         & reset_env & rids & st_reset & sconst & st_s
         & Haux & Hclk & Hrst & Hinp & Hout' & Hslocals & Hslasts
         & Hrenv & Hrids & Hsconst & Hsigdef); [exact Hsig|].
    edestruct generate_sys_signature_inv as
        (clk_id2 & rst_id2 & clk_type2 & rst_type2 & inp2 & out2 & slocals2
         & slasts2 & reset_env2 & rids2 & st_reset2 & sconst2 & st_s2
         & Haux2 & Hclk2 & Hrst2 & Hinp2 & Hout2 & Hslocals2 & Hslasts2
         & Hrenv2 & Hrids2 & Hsconst2 & Hsigdef2); [exact Hsig'|].
    (* everything but the body is copied, so the two inversions agree *)
    rewrite Hname in Haux2, Hrenv2.
    rewrite Haux in Haux2. inversion Haux2; subst clk_id2 rst_id2.
    rewrite Hclk in Hclk2. inversion Hclk2; subst clk_type2.
    rewrite Hrst in Hrst2. inversion Hrst2; subst rst_type2.
    rewrite Hrenv in Hrenv2. inversion Hrenv2; subst reset_env2.
    rewrite Hin in Hinp2. rewrite Hinp in Hinp2. inversion Hinp2; subst inp2.
    rewrite Hout in Hout2. rewrite Hout' in Hout2. inversion Hout2; subst out2.
    edestruct Hready as (Hwf & Hdisj);
      [exact Hsig|exact Haux|exact Hclk|exact Hrst|exact Hinp|exact Hout'
      |exact Hslocals|exact Hslasts|exact Hrenv|exact Hrids|exact Hsconst
      |exact Hsch|exact Hsigdef|].
    destruct Hwc as (_ & _ & Henvvars & Hwtcs).
    (* the scope the raw constraints live in, in the flat form the
       freshness premise is stated over *)
    set (rawscope := inp ++ out ++ slocals ++ slasts ++ rids
                       ++ [clk_type; rst_type]).
    destruct (SECSTCTYPING.sys_raw_scope_facts s env clk_type rst_type inp out
                slocals slasts reset_env rids Hinp Hout' Hslocals Hslasts Hrids)
      as (Hvarssc & Hbasesc & Hrstsc & Hkeyssc).
    assert (Hincl : forall x,
               In x (SECSTCTYPING.sys_raw_scope inp out clk_type rst_type
                       slocals slasts rids) ->
               In x rawscope).
    { intros x Hx.
      unfold SECSTCTYPING.sys_raw_scope, SECSTCTYPING.hidden_sys_vars in Hx.
      rewrite in_app_iff, nodup_In in Hx.
      unfold rawscope. repeat rewrite in_app_iff in *. tauto. }
    assert (Hfr : SIG.secglobal_scope_fresh rawscope G).
    { unfold rawscope.
      eapply Hfresh;
        [exact Haux|exact Hclk|exact Hrst|exact Hinp|exact Hout'
        |exact Hslocals|exact Hslasts|exact Hrenv|exact Hrids]. }
    assert (Hact : Forall (call_actuals_in_scope env clk_type rawscope)
                     s.(SynStc.s_tcs)).
    { rewrite Forall_forall. intros tc Htc.
      eapply call_actuals_in_scope_from_wc
        with (P := P)
             (vars := idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars)
                              ++ s.(SynStc.s_out)) ++ idck s.(SynStc.s_lasts)).
      - exact Henvvars.
      - rewrite Forall_forall in Hwtcs. exact (Hwtcs tc Htc).
      - intros x Hmem. destruct (Hvarssc x Hmem) as (ty & Hf & Hins).
        exists ty. split; [exact Hf|apply Hincl; exact Hins].
      - apply Hincl; exact Hbasesc. }
    assert (Hrinsts : forall i xs ck f es rinst,
               In (SynStc.TcCall i xs ck true f es) s.(SynStc.s_tcs) ->
               Env.find i reset_env = Some rinst ->
               In rinst rawscope).
    { intros i xs ck f es rinst Hincall Hfind.
      apply Hincl. apply (Hkeyssc i rinst st_reset st_reset).
      - eapply SECSTCTYPING.In_trconstrs_reset_keys_call; exact Hincall.
      - unfold find_env. rewrite Hfind. reflexivity. }
    (* the target run, moved back onto the original body order *)
    destruct (SECSTCTYPING.generate_trconstrs_constraints_Permutation_ok
                G' env reset_env clk_type rst_type
                s'.(SynStc.s_tcs) s.(SynStc.s_tcs) st_reset2 sconst2 st_s2
                st_reset2 (Permutation_sym Hperm) Hsconst2)
      as (mid & Hmid & Hpermmid).
    assert (Hscmid : constraints_scoped rawscope mid).
    { eapply constraints_scoped_weaken; [exact Hincl|].
      eapply SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys
        with (P := P)
             (vars := idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars)
                              ++ s.(SynStc.s_out)) ++ idck s.(SynStc.s_lasts));
        [exact Hscoped'|exact Henvvars|exact Hwtcs|exact Hvarssc
        |exact Hbasesc|exact Hrstsc|exact Hkeyssc|exact Hmid]. }
    assert (Hpreson : preserves_on rawscope sconst sconst2).
    { eapply preserves_on_Permutation with (c1 := sconst) (c2 := mid);
        [apply Permutation_refl|apply Permutation_sym; exact Hpermmid|].
      eapply generate_trconstrs_constraints_preserved;
        [exact Hpres|exact Hfr|apply Hincl; exact Hrstsc|exact Hact
        |exact Hrinsts|exact Hscmid|exact Hsconst|exact Hmid]. }
    subst sig sig'. split.
    - repeat split; reflexivity.
    - cbn [s_constraints].
      eapply preserves_on_simplify_bridge with (rawscope := rawscope).
      + exact Hwf.
      + exact Hdisj.
      + intros x Hx. unfold signature_scope in Hx. cbn in Hx.
        unfold rawscope. repeat rewrite in_app_iff in *. tauto.
      + exact Hpreson.
  Qed.

  (** ** Systems with a windowed environment

      What the scoped signature induction actually consumes, per system:
      the environment its signature is generated from, and the state
      window that environment's names live in.  Consecutive systems get
      abutting windows, which is exactly the statement that a system's
      names postdate every signature generated before it.

      Phrasing the induction against this rather than against the
      NLustre naming run is what keeps the Stc-to-Obc theorems free of
      NLustre nodes: the one lemma below is where that coupling lives. *)

  Inductive scoped_envs_windowed (envs: node_scoped_env)
    : ident -> list SynStc.system -> Prop :=
  | SEW_nil: forall st,
      scoped_envs_windowed envs st []
  | SEW_cons: forall st st' s systems env,
      find_node_env s.(SynStc.s_name) envs = Some env ->
      NAMEGEN.env_naming_props env ->
      NAMEGEN.env_sec_window env st st' ->
      scoped_envs_windowed envs st' systems ->
      scoped_envs_windowed envs st (s :: systems).

  Lemma env_sec_lower_bounded_from_local_env:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      env_sec_lower_bounded env st.
  Proof.
    intros n st env rec st' Hlocal x ty Hfind.
    edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                 n st env rec st' x ty Hlocal Hfind) as (m & Hm & Hlo).
    exists m. split; [exact Hm|].
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
    eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
  Qed.

  Lemma generated_sys_signature_scope_upper_bound_from_local_env:
    forall G s n env aux_names sig st rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      SIG.signature_scope_bounded_above sig st'.
  Proof.
    intros G s n env aux_names sig st rec st' Hlocal Hsig ty Hin.
    destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    exact (NAMEGEN.generate_local_env_for_node_bounded
             n st env rec st' Hlocal x ty Hfind).
  Qed.

  Lemma generated_sys_signature_scope_sec_from_local_env:
    forall G s n env aux_names sig st rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      signature_scope_sec sig.
  Proof.
    intros G s n env aux_names sig st rec st' Hlocal Hsig ty Hin.
    destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
  Qed.

  (** The same two bounds, read off the environment's own properties
      rather than off the run that produced it.  Every element of a
      generated signature's scope is some [Env.find x env], so both
      bounds factor through the environment. *)

  Lemma generated_sys_signature_scope_sec_from_env_props:
    forall G s env aux_names sig,
      NAMEGEN.env_naming_props env ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      signature_scope_sec sig.
  Proof.
    intros G s env aux_names sig (_ & Hsec) Hsig ty Hin.
    destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    eapply Hsec; eauto.
  Qed.

  Lemma generated_sys_signature_scope_bounded_from_window:
    forall G s env aux_names sig st st',
      NAMEGEN.env_sec_window env st st' ->
      SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
      SIG.signature_scope_bounded_above sig st'.
  Proof.
    intros G s env aux_names sig st st' (Hwin & _) Hsig ty Hin.
    destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    destruct (Hwin _ _ Hfind) as (m & Hm & _ & Hlt).
    exists m. split; assumption.
  Qed.

  Lemma env_sec_lower_bounded_from_window:
    forall env st st',
      NAMEGEN.env_sec_window env st st' ->
      env_sec_lower_bounded env st.
  Proof.
    intros env st st' (Hwin & _) x ty Hfind.
    destruct (Hwin _ _ Hfind) as (m & Hm & Hlo & _).
    exists m. split; assumption.
  Qed.

  (** The local-environment form, mirroring NLustre's
      [generated_node_simplify_ready_from_local_env].  Same conjunction,
      same two halves; only the source of the environment facts differs. *)

  Corollary generated_sys_simplify_ready_from_local_env:
    forall all_nodes envs aux_names n st env rec st',
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      generated_sys_simplify_ready env aux_names.
  Proof.
    intros all_nodes envs aux_names n st env rec st' Hscoped Hlocal.
    eapply generated_sys_simplify_ready_from_naming_props.
    eapply NAMEGEN.naming_env_props_from_local_env; eauto.
  Qed.

End SECSTCTYPINGCORRECTNESS.

Module SecStcTypingCorrectness
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Import WD    : STCWELLDEFINED Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo)
  <: SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo WD SECSTCTYPING.

Include SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo WD SECSTCTYPING.

End SecStcTypingCorrectness.
