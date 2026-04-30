From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecSTCTyping.
From Coq Require Import Sorting.Permutation.
From compcert Require Import common.Errors.

Module Type SECSTCTYPINGCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE Ids SC)
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

  (** Target-local reset-environment correctness.

      These lemmas are purely STC-side: they describe how the translated reset
      environment is built, why its generated type variables stay in the
      `sec_reset` namespace, and why that environment preserves injectivity and
      lookup facts.  They are used later by the translation proof, but do not
      themselves relate NLustre and STC. *)

  (** We reuse the same environment-viewing convention as the shared naming
      layer: an environment is observed through the list of pairs
      [(generated_security_name, source_key)] produced by [Env.elements].  The
      reset-environment proofs only need the generic list properties of this
      view, so they live here instead of the translation file. *)
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

  (** Node-scoped target signature generation.

      This is the STC-side counterpart of
      [SECNLUSTYPINGCORRECTNESS.generate_node_sig_scoped_env_scoped].  The
      node-scoped naming layer only changes how the current system's local env
      is recovered from the outer table; once that local env is projected, the
      existing target typing proof applies unchanged. *)
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

  (** Target-only structural fact for reset-key extraction.

      The helper [trconstrs_reset_keys] is later combined with NLustre reset
      bookkeeping, but this append decomposition is purely STC-side and belongs
      with the other reset-environment support lemmas. *)
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
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE Ids SC)
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
  <: SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING.

Include SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING.

End SecStcTypingCorrectness.
