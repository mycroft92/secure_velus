(** Correctness facts for generated STC signatures and reset-instance environments. *)

From Velus Require Import Common.
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
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecSTCTyping.
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
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo).

  Definition env_values (env: Env.t ident) : list (ident * ident) :=
    map (fun '(x, ty) => (ty, x)) (Env.elements env).

  Lemma env_values_add:
    forall x ty env,
      ~ Env.In x env ->
      Permutation (env_values (Env.add x ty env))
                  ((ty, x) :: env_values env).
  Proof.
    intros x ty env Hnin.
    unfold env_values.
    replace ((ty, x) :: map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))
      with (map (fun '(x0, ty0) => (ty0, x0)) ((x, ty) :: Env.elements env))
      by reflexivity.
    now apply Permutation_map, Env.elements_add.
  Qed.

  Lemma env_values_nodup_injective:
    forall env,
      NoDupMembers (env_values env) ->
      SECSTCTYPING.env_injective env.
  Proof.
    intros env Hnodup x y tx ty Hfindx Hfindy Heq.
    apply Env.elements_correct in Hfindx.
    apply Env.elements_correct in Hfindy.
    unfold env_values in Hnodup.
    assert (Hinx : In (tx, x) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
    { apply in_map_iff. exists (x, tx). split; [reflexivity|exact Hfindx]. }
    assert (Hiny : In (tx, y) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
    { subst ty.
      apply in_map_iff. exists (y, tx). split; [reflexivity|exact Hfindy]. }
    now eapply NoDupMembers_det; eauto.
  Qed.

  Definition reset_env_sec_bounded (st: ident) (env: Env.t ident) : Prop :=
    forall x ty,
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n /\ (n < st)%positive.

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

  Lemma fresh_reset_insert_sec_range:
    forall env k st env' rst_inst st' x ty,
      (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
      fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
      Env.find x env' = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    intros env k st env' rst_inst st' x ty Henv Hins Hfind.
    unfold fresh_reset_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_reset_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0.
    inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret. subst env' rst_inst st'.
    destruct (Pos.eq_dec x k) as [Heq|Hneq].
    - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
      eexists; reflexivity.
    - rewrite Env.gso in Hfind; eauto.
  Qed.

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

  Lemma fresh_reset_insert_preserves_find:
    forall env k st env' rst_inst st' x ty,
      fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
      Env.find x env = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    intros env k st env' rst_inst st' x ty Hins Hfind.
    unfold fresh_reset_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_reset_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
    assert (Hxk : x <> k).
    { intro Heq. subst x.
      assert (Env.mem k env = true).
      { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
      congruence. }
    now rewrite Env.gso.
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
      SECSTCTYPING.env_injective env ->
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
      (inst_valuation_outputs_eq
         dlt sig inptyp ckty rstty outtyp
         Hfresh Hndscope HlenOut)
      as Hout_eq.
    destruct
      (Forall2_nth_error_inv
         _ _
         (fun x v0 =>
            inst_valuation dlt sig inptyp ckty rstty outtyp v0 =
            inst_valuation dlt sig inptyp ckty rstty outtyp x)
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
              inst_valuation dlt sig inptyp ckty rstty outtyp v ⊑ t).
    {
      destruct Hfresh as [_ [_ [_ Houtfresh]]].
      rewrite (inst_valuation_outside_sig_scope
                 dlt sig inptyp ckty rstty outtyp v).
      - exact Hlowv.
      - unfold outputs_fresh in Houtfresh.
        rewrite Forall_forall in Houtfresh.
        eapply Houtfresh.
        eapply nth_error_In_local; eauto.
    }
    assert (Hlowy :
              inst_valuation dlt sig inptyp ckty rstty outtyp y ⊑ t).
    {
      rewrite <- Hinst_out.
      exact Hlowv_inst.
    }
    unfold listSatisfiable in Hsat_sig.
    rewrite Forall_forall in Hsat_sig.
    specialize (Hsat_sig _ (find_correct _ _ _ Hfindlhs)).
    unfold constraintSatisfiable, satisfiable in Hsat_sig.
    simpl in Hsat_sig.
    rewrite <- (inst_valuation_reset_eq
                  dlt sig inptyp ckty rstty outtyp
                  Hfresh Hndscope).
    apply order_trans with
        (y := hm_ext (inst_valuation dlt sig inptyp ckty rstty outtyp) lhs).
    - apply hm_ext_list_in1.
      exact Hresetin.
    - apply order_trans with
        (y := join (inst_valuation dlt sig inptyp ckty rstty outtyp y) bottom).
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
        /\ generate_reset_env s.(SynStc.s_tcs) init_state = OK ((reset_env, rids), st_reset)
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
    eapply sec_bind2_inv in Hgen as (reset_env & rids & st_reset & Hresetenv & Hgen).
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
    exists clk_id, rst_id, packed_clk_type, packed_rst_type, packed_inp, packed_out,
           slocals, slasts, reset_env, rids, st_reset, sconst, st_res.
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
         & Hresetenv & Hsconst & Hsigdef); eauto.
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

  Lemma reset_env_sec_bounded_step:
    forall st env,
      reset_env_sec_bounded st env ->
      reset_env_sec_bounded (Pos.succ st) env.
  Proof.
    intros st env Hbound x ty Hfind.
    specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
    exists n. split; auto.
    eapply Pos.lt_trans; eauto.
    apply Pos.lt_succ_diag_r.
  Qed.

  Lemma reset_env_values_fresh_notin:
    forall env st,
      reset_env_sec_bounded st env ->
      ~ InMembers (Ids.gensym Ids.sec_reset st) (env_values env).
  Proof.
    intros env st Hbound Hin.
    apply InMembers_In in Hin as (x & Hin).
    unfold env_values in Hin.
    apply in_map_iff in Hin as ((x', ty') & Heq & Hele).
    simpl in Heq. inversion Heq; subst x' ty'. clear Heq.
    apply Env.elements_complete in Hele.
    specialize (Hbound _ _ Hele) as (n & Hgen & Hlt).
    apply gensym_injective in Hgen as [_ Hn]. subst n.
    now apply Pos.lt_irrefl in Hlt.
  Qed.

  Lemma fresh_reset_insert_env_props:
    forall env k st env' rst_inst st',
      reset_env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
      reset_env_sec_bounded st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    intros env k st env' rst_inst st' Hbound Hnodup Hgen.
    unfold fresh_reset_insert in Hgen.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
    eapply sec_bind_inv in Hgen as (e & st2 & Hins & Hret).
    unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins. inversion Hins; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
    split.
    - intros x ty Hfind.
      destruct (ident_eq_dec x k) as [Heq|Hneq].
      + subst x. rewrite Env.gss in Hfind. inversion Hfind; subst ty.
        exists st. split; [reflexivity|apply Pos.lt_succ_diag_r].
      + rewrite Env.gso in Hfind by auto.
        specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
        exists n. split; auto.
        eapply Pos.lt_trans; eauto.
        apply Pos.lt_succ_diag_r.
    - assert (Hnotin : ~ Env.In k env).
      { intro Hin. apply Env.mem_1 in Hin. rewrite Hmem in Hin. discriminate. }
      eapply (NoDupMembers_Permutation_Proper
                (env_values (Env.add k (Ids.gensym Ids.sec_reset st) env))
                ((Ids.gensym Ids.sec_reset st, k) :: env_values env)).
      + apply env_values_add; exact Hnotin.
      + constructor.
        * apply reset_env_values_fresh_notin; exact Hbound.
        * exact Hnodup.
  Qed.

  Lemma generate_reset_env_props':
    forall trs env acc st reset_env rids st',
      reset_env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
      reset_env_sec_bounded st' reset_env
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
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo)
  <: SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING.

Include SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING.

End SecStcTypingCorrectness.
