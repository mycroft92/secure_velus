(** Low-equivalence definitions and semantic transport lemmas for NLustre noninterference. *)

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
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSNONINTERFERENCESUPPORT
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
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn CEIsF CEClo)
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
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN CEIsF CEClo SECCETYPING
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING Ord Mem IsD IsF Clo SECNLUSTYPING).

  Definition ground_instantiation : Type := ident -> Lat.t.

  Definition signature_constraints (sig : signature) : list constraint :=
    sig.(s_constraints).

  Definition signature_satisfied
    (dlt : ground_instantiation) (sig : signature) : Prop :=
    SecT.listSatisfiable dlt (signature_constraints sig).

  Section GENERATED_LOW_OBSERVATION.
    Variable all_nodes : global.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.
    Variable n : node.
    Variable ty_env : local_sec_env.
    Variable dlt : ground_instantiation.
    Variable t : Lat.t.

    Hypothesis Henvsgen :
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names).
    Hypothesis Hfindenv :
      find_node_env n.(n_name) envs = Some ty_env.

    (** A variable is low when its generated security type is below the observation level.  The rest of the file uses this as the basic observation predicate. *)
    Definition low_var (x : ident) : Prop :=
      exists α, Env.find x ty_env = Some α /\ dlt α ⊑ t.

    Definition low_var_dec (x : ident) : {low_var x} + {~ low_var x}.
    Proof.
      unfold low_var.
      destruct (Env.find x ty_env) as [α|] eqn:Hfind.
      - destruct (Lat.order_dec (dlt α) t) as [Hle|Hnle].
        + left. now exists α.
        + right. intros (α' & Hfind' & Hle').
          inv Hfind'. contradiction.
      - right. intros (α & Hfind' & _).
        discriminate Hfind'.
    Defined.

    Definition low_var_b (x : ident) : bool :=
      if low_var_dec x then true else false.

    Lemma low_var_b_spec:
      forall x,
        low_var_b x = true <-> low_var x.
    Proof.
      intros x.
      unfold low_var_b.
      destruct (low_var_dec x); split; intro H; auto; discriminate.
    Qed.

    Definition vars_le_t (X : list ident) : list ident :=
      filter low_var_b X.

    Lemma vars_le_t_spec:
      forall X x,
        In x (vars_le_t X) <-> In x X /\ low_var x.
    Proof.
      intros X x.
      unfold vars_le_t.
      rewrite filter_In.
      rewrite low_var_b_spec.
      tauto.
    Qed.

    Definition project_env_on (xs : list ident) (R : env) : env :=
      fold_right
        (fun x acc =>
           match Env.find x R with
           | Some v => Env.add x v acc
           | None => acc
           end)
        (Env.empty _)
        xs.

    Lemma project_env_on_find:
      forall xs R x,
        Env.find x (project_env_on xs R) =
        if in_dec ident_eq_dec x xs then Env.find x R else None.
    Proof.
      induction xs as [|y xs IH]; intros R x; simpl.
      - destruct (in_dec ident_eq_dec x []); [contradiction|apply Env.gempty].
      - destruct (Env.find y R) as [v|] eqn:Hy.
        + destruct (ident_eq_dec x y) as [Heq|Hneq].
          * subst x.
            rewrite Env.gss.
            rewrite Hy.
            destruct (ident_eq_dec y y) as [_|Hneq']; [reflexivity|contradiction].
          * rewrite Env.gso by exact Hneq.
            rewrite IH.
            destruct (in_dec ident_eq_dec x (y :: xs)) as [Hin|Hin].
            -- simpl in Hin. destruct Hin as [Heq|Hin'].
               ++ subst. contradiction.
               ++ destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hin''].
                  ** destruct (ident_eq_dec y x) as [Heq'|Hneq'].
                     --- exfalso. apply Hneq. symmetry. exact Heq'.
                     --- reflexivity.
                  ** contradiction.
            -- destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hinxs'].
               ++ exfalso. apply Hin. right. exact Hinxs.
               ++ destruct (ident_eq_dec y x) as [Heq'|Hneq'].
                  ** exfalso. apply Hneq. symmetry. exact Heq'.
                  ** reflexivity.
        + rewrite IH.
          destruct (in_dec ident_eq_dec x (y :: xs)) as [Hin|Hin].
          * simpl in Hin. destruct Hin as [Heq|Hin'].
            -- subst x.
               rewrite Hy.
               destruct (in_dec ident_eq_dec y xs) as [Hinxs|Hinxs'].
               ++ destruct (ident_eq_dec y y) as [Heq|Hneq']; [reflexivity|contradiction].
               ++ destruct (ident_eq_dec y y) as [Heq|Hneq']; [reflexivity|contradiction].
            -- destruct (in_dec ident_eq_dec x xs) as [Hinxs|Hin''].
               ++ destruct (ident_eq_dec y x) as [Heq|Hneq]; [reflexivity|reflexivity].
               ++ contradiction.
          * destruct (in_dec ident_eq_dec x xs) as [Hin'|Hin''].
            -- exfalso. apply Hin. right. exact Hin'.
            -- destruct (ident_eq_dec y x) as [Heq|Hneq].
               ++ subst x. exfalso. apply Hin. now left.
               ++ reflexivity.
    Qed.

    Definition project_env_le_t (X : list ident) (R : env) : env :=
      project_env_on (vars_le_t X) R.

    Definition project_history_le_t (X : list ident) (H : history) : history :=
      fun k => project_env_le_t X (H k).

    Definition env_low_eq (X : list ident) (R R' : env) : Prop :=
      forall x,
        In x X ->
        low_var x ->
        Env.find x R = Env.find x R'.

    Definition history_low_eq (X : list ident) (H H' : history) : Prop :=
      forall k,
        env_low_eq X (H k) (H' k).

    Definition history_low_eq_upto (X : list ident) (H H' : history) (k : nat) : Prop :=
      forall j,
        j <= k ->
        env_low_eq X (H j) (H' j).

    Definition projected_env_eq (X : list ident) (R R' : env) : Prop :=
      forall x,
        Env.find x (project_env_le_t X R) =
        Env.find x (project_env_le_t X R').

    Definition projected_history_eq (X : list ident) (H H' : history) : Prop :=
      forall k x,
        Env.find x (project_history_le_t X H k) =
        Env.find x (project_history_le_t X H' k).

    Lemma project_env_le_t_find_low:
      forall X R x,
        In x X ->
        low_var x ->
        Env.find x (project_env_le_t X R) = Env.find x R.
    Proof.
      intros X R x Hin Hlow.
      unfold project_env_le_t.
      rewrite project_env_on_find.
      destruct (in_dec ident_eq_dec x (vars_le_t X)) as [Hin'|Hin']; [reflexivity|].
      exfalso.
      apply Hin'.
      apply vars_le_t_spec.
      now split.
    Qed.

    Lemma project_env_le_t_find_excluded:
      forall X R x,
        ~ In x X \/ ~ low_var x ->
        Env.find x (project_env_le_t X R) = None.
    Proof.
      intros X R x Hexcl.
      unfold project_env_le_t.
      rewrite project_env_on_find.
      destruct (in_dec ident_eq_dec x (vars_le_t X)) as [Hin|Hin]; [|reflexivity].
      exfalso.
      apply vars_le_t_spec in Hin.
      tauto.
    Qed.

    Lemma env_low_eq_projected_env_eq:
      forall X R R',
        env_low_eq X R R' ->
        projected_env_eq X R R'.
    Proof.
      intros X R R' Hlow x.
      destruct (in_dec ident_eq_dec x X) as [Hin|Hnin].
      - destruct (low_var_dec x) as [Hobs|Hnobs].
        + rewrite !project_env_le_t_find_low by assumption.
          now apply Hlow.
        + rewrite !project_env_le_t_find_excluded by now right.
          reflexivity.
      - rewrite !project_env_le_t_find_excluded by now left.
        reflexivity.
    Qed.

    Lemma projected_env_eq_env_low_eq:
      forall X R R',
        projected_env_eq X R R' ->
        env_low_eq X R R'.
    Proof.
      intros X R R' Hproj x Hin Hlow.
      specialize (Hproj x).
      rewrite !project_env_le_t_find_low in Hproj; auto.
    Qed.

    (** This rewrites low-equivalence of histories as equality after projection to the low variables.  Later semantic lemmas switch between these two views as needed. *)
    Lemma history_low_eq_projected_history_eq:
      forall X H H',
        history_low_eq X H H' ->
        projected_history_eq X H H'.
    Proof.
      intros X H H' Hlow k x.
      apply env_low_eq_projected_env_eq.
      apply Hlow.
    Qed.

    Lemma projected_history_eq_history_low_eq:
      forall X H H',
        projected_history_eq X H H' ->
        history_low_eq X H H'.
    Proof.
      intros X H H' Hproj k.
      apply projected_env_eq_env_low_eq.
      intros x.
      apply Hproj.
    Qed.

    Lemma history_low_eq_upto_of_history_low_eq:
      forall X H H' k,
        history_low_eq X H H' ->
        history_low_eq_upto X H H' k.
    Proof.
      intros X H H' k Hlow j _.
      apply Hlow.
    Qed.

    Lemma history_low_eq_upto_weaken:
      forall X Y H H' k,
        (forall x, In x Y -> In x X) ->
        history_low_eq_upto X H H' k ->
        history_low_eq_upto Y H H' k.
    Proof.
      intros X Y H H' k Hsub Hlow j Hj x Hin Hobs.
      eapply Hlow; eauto.
    Qed.

    Lemma history_low_eq_upto_monotone:
      forall X H H' k1 k2,
        k1 <= k2 ->
        history_low_eq_upto X H H' k2 ->
        history_low_eq_upto X H H' k1.
    Proof.
      intros X H H' k1 k2 Hle Hlow j Hj.
      eapply Hlow; lia.
    Qed.

    Lemma history_low_eq_upto_from_Forall_pointwise:
      forall X H H' k,
        Forall
          (fun x =>
             low_var x ->
             forall j, j <= k -> Env.find x (H j) = Env.find x (H' j))
          X ->
        history_low_eq_upto X H H' k.
    Proof.
      intros X H H' k Hpts j Hj x Hin Hlow.
      eapply Forall_forall in Hpts; [|exact Hin].
      eapply Hpts; eauto.
    Qed.

    Lemma history_low_eq_upto_succ_intro:
      forall X H H' k,
        history_low_eq_upto X H H' k ->
        (forall x, In x X -> low_var x ->
           Env.find x (H (S k)) = Env.find x (H' (S k))) ->
        history_low_eq_upto X H H' (S k).
    Proof.
      intros X H H' k Hprev Hcur j Hj x Hin Hlow.
      destruct (Nat.eq_dec j (S k)) as [Heq|Hneq].
      - subst j. eapply Hcur; eauto.
      - eapply Hprev; eauto. lia.
    Qed.

    Lemma singleton_type_bound:
      forall alpha,
        dlt alpha ⊑ SecT.hm_ext dlt [alpha].
    Proof.
      intro alpha.
      simpl.
      apply join_bound1.
    Qed.

    Lemma left_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st1 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      eapply order_trans.
      - apply SecT.hm_ext_concat_l.
      - apply SecT.hm_ext_concat_l.
    Qed.

    Lemma middle_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st2 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      eapply order_trans.
      - apply SecT.hm_ext_concat_r.
      - apply SecT.hm_ext_concat_l.
    Qed.

    Lemma right_triple_type_bound:
      forall st1 st2 st3,
        SecT.hm_ext dlt st3 ⊑ SecT.hm_ext dlt ((st1 ⊔ st2) ⊔ st3).
    Proof.
      intros st1 st2 st3.
      apply SecT.hm_ext_concat_r.
    Qed.

    Lemma assign_clk_type_free_bound:
      forall base ck st x,
        Is_free_in_clock x ck ->
        SECCETYPING.assign_clk_type ty_env base ck = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros base ck.
      induction ck as [|ck IH y b]; intros st x Hfree Hassign.
      - inversion Hfree.
      - eapply SECCETYPING.assign_clk_inv in Hassign as
            (st' & yty & Hst & Hck & Hfindy).
        apply CEIsF.Is_free_in_clock_disj in Hfree as [Heq|Hfree].
        + subst x.
          exists yty.
          split; [exact Hfindy|].
          subst st.
          eapply order_trans.
          * apply singleton_type_bound.
          * apply SecT.hm_ext_concat_r.
        + edestruct IH as (alpha & Hfind & Hbound); eauto.
          exists alpha.
          split; [exact Hfind|].
          subst st.
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
    Qed.

    Lemma assign_exp_type_free_bound:
      forall e st x,
        Is_free_in_exp x e ->
        SECCETYPING.assign_exp_type ty_env e = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros e.
      induction e as [c|y ty|e IHe y b|op e IHe ty|op e1 IHe1 e2 IHe2 ty];
        intros st x Hfree Hassign; simpl in Hassign.
      - inversion Hfree.
      - inversion Hfree; subst.
        destruct (Env.find y ty_env) as [yty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst st.
        exists yty.
        split; [reflexivity|].
        apply singleton_type_bound.
      - apply CEIsF.Is_free_in_when_disj in Hfree as [Heq|Hfree].
        + destruct (SECCETYPING.assign_exp_type ty_env e) as [ety|] eqn:He; try discriminate.
          destruct (Env.find y ty_env) as [yty|] eqn:Hfindy; try discriminate.
          inversion Hassign; subst st.
          subst x.
          exists yty.
          split; [exact Hfindy|].
          eapply order_trans.
          * apply singleton_type_bound.
          * apply SecT.hm_ext_concat_r.
        + destruct (SECCETYPING.assign_exp_type ty_env e) as [ety|] eqn:He; try discriminate.
          destruct (Env.find y ty_env) as [yty|] eqn:Hfindy; try discriminate.
          assert (Hsame : Some ety = Some ety) by reflexivity.
          destruct (IHe ety _ Hfree Hsame) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
      - inversion Hfree; subst.
        eauto.
      - destruct (SECCETYPING.assign_exp_type ty_env e1) as [e1ty|] eqn:He1; try discriminate.
        destruct (SECCETYPING.assign_exp_type ty_env e2) as [e2ty|] eqn:He2; try discriminate.
        inversion Hfree as [| | | |x' op' e1' e2' ty' Hdisj]; subst; clear Hfree.
        destruct Hdisj as [Hfree1|Hfree2].
        + assert (Hsame1 : Some e1ty = Some e1ty) by reflexivity.
          destruct (IHe1 e1ty _ Hfree1 Hsame1) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_l.
        + assert (Hsame2 : Some e2ty = Some e2ty) by reflexivity.
          destruct (IHe2 e2ty _ Hfree2 Hsame2) as (alpha & Hfind & Hbound).
          inversion Hassign; subst st.
          exists alpha.
          split; [exact Hfind|].
          eapply order_trans; [exact Hbound|].
          apply SecT.hm_ext_concat_r.
    Qed.

    Lemma assign_cexp_type_free_bound:
      forall ce st x,
        Is_free_in_cexp x ce ->
        SECCETYPING.assign_cexp_type ty_env ce = Some st ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt st.
    Proof.
      intros ce st x Hfree.
      revert st.
      induction Hfree as
          [i ce_t ce_f
          |i ce_t ce_f y Hfree_t IHt
          |i ce_t ce_f y Hfree_f IHf
          |y b ce_t ce_f Hfree_b
          |y b ce_t ce_f Hfree_t IHt
          |y b ce_t ce_f Hfree_f IHf
          |e y Hfree_e];
        intros st Hassign; simpl in Hassign.
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        exists ity.
        split; [reflexivity|].
        eapply order_trans.
        + apply singleton_type_bound.
        + apply left_triple_type_bound.
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_t : Some tty = Some tty) by reflexivity.
        destruct (IHt tty Hsame_t) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (middle_triple_type_bound [ity] tty fty).
      - destruct (Env.find i ty_env) as [ity|] eqn:Hfindi; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_f : Some fty = Some fty) by reflexivity.
        destruct (IHf fty Hsame_f) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (right_triple_type_bound [ity] tty fty).
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        destruct (assign_exp_type_free_bound b bty y Hfree_b Hb) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply left_triple_type_bound.
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_t : Some tty = Some tty) by reflexivity.
        destruct (IHt tty Hsame_t) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (middle_triple_type_bound bty tty fty).
      - destruct (SECCETYPING.assign_exp_type ty_env b) as [bty|] eqn:Hb; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_t) as [tty|] eqn:Ht; try discriminate.
        destruct (SECCETYPING.assign_cexp_type ty_env ce_f) as [fty|] eqn:Hf; try discriminate.
        inversion Hassign; subst st.
        assert (Hsame_f : Some fty = Some fty) by reflexivity.
        destruct (IHf fty Hsame_f) as (alpha & Hfind & Hbound).
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        eapply (right_triple_type_bound bty tty fty).
      - eapply assign_exp_type_free_bound; eauto.
    Qed.

    Lemma assign_aexp_type_free_bound:
      forall base ck e ckty ety x,
        Is_free_in_aexp x ck e ->
        SECCETYPING.assign_clk_type ty_env base ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt (ckty ⊔ ety).
    Proof.
      intros base ck e ckty ety x Hfree Hck He.
      inversion Hfree; subst.
      - match goal with
        | Hexp : Is_free_in_exp x e |- _ =>
            destruct (assign_exp_type_free_bound e ety x Hexp He)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_r.
      - match goal with
        | Hckfree : Is_free_in_clock x ck |- _ =>
            destruct (assign_clk_type_free_bound base ck ckty x Hckfree Hck)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_l.
    Qed.

    Lemma assign_caexp_type_free_bound:
      forall base ck ce ckty cety x,
        Is_free_in_caexp x ck ce ->
        SECCETYPING.assign_clk_type ty_env base ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        exists alpha,
          Env.find x ty_env = Some alpha
          /\ dlt alpha ⊑ SecT.hm_ext dlt (ckty ⊔ cety).
    Proof.
      intros base ck ce ckty cety x Hfree Hck Hce.
      inversion Hfree; subst.
      - match goal with
        | Hcefree : Is_free_in_cexp x ce |- _ =>
            destruct (assign_cexp_type_free_bound ce cety x Hcefree Hce)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_r.
      - match goal with
        | Hckfree : Is_free_in_clock x ck |- _ =>
            destruct (assign_clk_type_free_bound base ck ckty x Hckfree Hck)
              as (alpha & Hfind & Hbound)
        end.
        exists alpha.
        split; [exact Hfind|].
        eapply order_trans; [exact Hbound|].
        apply SecT.hm_ext_concat_l.
    Qed.

    Lemma simple_security:
      forall lhs x y xty alpha,
        Env.find x ty_env = Some xty ->
        Env.find y ty_env = Some alpha ->
        dlt alpha ⊑ SecT.hm_ext dlt lhs ->
        SecT.satisfiable dlt lhs [xty] ->
        low_var x ->
        low_var y.
    Proof.
      intros lhs x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx.
      destruct Hlowx as (alpha_x & Hfindx' & Hlowx).
      rewrite Hfindx in Hfindx'.
      inversion Hfindx'; subst alpha_x.
      exists alpha.
      split; [exact Hfindy|].
      eapply order_trans; [exact Hbound|].
      eapply order_trans; [exact Hsat|].
      simpl.
      apply join_least_upper_bound.
      - exact Hlowx.
      - apply bottom_is_bottom.
    Qed.

    Lemma simple_security_caexp:
      forall base_ty rst_ty x ck ce xty ckty cety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        Is_free_in_caexp y ck ce ->
        low_var y.
    Proof.
      intros base_ty rst_ty x ck ce xty ckty cety y
             Hfindx Hck Hce Hsat Hlowx Hfree.
      destruct (assign_caexp_type_free_bound base_ty ck ce ckty cety y Hfree Hck Hce)
        as (alpha & Hfindy & Hbound).
      assert (Hbound' : dlt alpha ⊑ SecT.hm_ext dlt ((([rst_ty] ⊔ ckty) ⊔ cety))).
      { eapply order_trans; [exact Hbound|].
        rewrite SymTypes.MergeFacts.merge_assoc.
        apply SecT.hm_ext_concat_r. }
      apply (simple_security ((([rst_ty] ⊔ ckty) ⊔ cety)) x y xty alpha
               Hfindx Hfindy Hbound' Hsat Hlowx).
    Qed.

    Lemma simple_security_aexp:
      forall base_ty rst_ty x ck e xty ckty ety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        Is_free_in_aexp y ck e ->
        low_var y.
    Proof.
      intros base_ty rst_ty x ck e xty ckty ety y
             Hfindx Hck He Hsat Hlowx Hfree.
      destruct (assign_aexp_type_free_bound base_ty ck e ckty ety y Hfree Hck He)
        as (alpha & Hfindy & Hbound).
      assert (Hbound' : dlt alpha ⊑ SecT.hm_ext dlt ((([rst_ty] ⊔ ckty) ⊔ ety))).
      { eapply order_trans; [exact Hbound|].
        rewrite SymTypes.MergeFacts.merge_assoc.
        apply SecT.hm_ext_concat_r. }
      apply (simple_security ((([rst_ty] ⊔ ckty) ⊔ ety)) x y xty alpha
               Hfindx Hfindy Hbound' Hsat Hlowx).
    Qed.

    Lemma simple_security_exp:
      forall x e xty ety y,
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ety [xty] ->
        low_var x ->
        Is_free_in_exp y e ->
        low_var y.
    Proof.
      intros x e xty ety y
             Hfindx He Hsat Hlowx Hfree.
      destruct (assign_exp_type_free_bound e ety y Hfree He)
        as (alpha & Hfindy & Hbound).
      apply (simple_security ety x y xty alpha Hfindx Hfindy Hbound Hsat Hlowx).
    Qed.

    Lemma sem_caexp_switch_history_low:
      forall X bk H H' ck ce xs,
        history_low_eq X H H' ->
        (forall y, Is_free_in_caexp y ck ce -> In y X /\ low_var y) ->
        sem_caexp bk H ck ce xs ->
        sem_caexp bk H' ck ce xs.
    Proof.
      intros X bk H H' ck ce xs Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_caexp_instant_switch_env
              (bk k) (H k) (H' k) ck ce (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck =>
                     let Hdep := Hfree y (FreeCAexp2 _ _ _ Hyck) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 | or_intror Hyce =>
                     let Hdep := Hfree y (FreeCAexp1 _ _ _ Hyce) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 end))).
      exact Hsem.
    Qed.

    Lemma sem_aexp_switch_history_low:
      forall X bk H H' ck e xs,
        history_low_eq X H H' ->
        (forall y, Is_free_in_aexp y ck e -> In y X /\ low_var y) ->
        sem_aexp bk H ck e xs ->
        sem_aexp bk H' ck e xs.
    Proof.
      intros X bk H H' ck e xs Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_aexp_instant_switch_env
              (bk k) (H k) (H' k) ck e (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck =>
                     let Hdep := Hfree y (freeAexp2 _ _ _ Hyck) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 | or_intror Hyexp =>
                     let Hdep := Hfree y (freeAexp1 _ _ _ Hyexp) in
                     let Hin := proj1 Hdep in
                     let Hobs := proj2 Hdep in
                     Hlow k y Hin Hobs
                 end))).
      exact Hsem.
    Qed.

    Lemma sem_exps_switch_history_low:
      forall X bk H H' es ls,
        history_low_eq X H H' ->
        (forall y, Exists (Is_free_in_exp y) es -> In y X /\ low_var y) ->
        sem_exps bk H es ls ->
        sem_exps bk H' es ls.
    Proof.
      intros X bk H H' es ls Hlow Hfree Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_exps_instant_switch_env
              (bk k) (H k) (H' k) es (ls k)
              (fun y Hy =>
                 let Hdep := Hfree y Hy in
                 let Hin := proj1 Hdep in
                 let Hobs := proj2 Hdep in
                 Hlow k y Hin Hobs))).
      exact Hsem.
    Qed.

    Lemma sem_vars_instant_nth_error:
      forall R xs vs i x v,
        sem_vars_instant R xs vs ->
        nth_error xs i = Some x ->
        nth_error vs i = Some v ->
        sem_var_instant R x v.
    Proof.
      intros R xs vs i x v Hvars Hnthx Hnthv.
      destruct
        (SecT.Forall2_nth_error_inv
           _ _ (sem_var_instant R) xs vs i x Hvars Hnthx)
        as (v' & Hnthv' & Hvar).
        rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. exact Hvar.
    Qed.

    Lemma sem_exps_instant_nth_error:
      forall b R es vs i e v,
        sem_exps_instant b R es vs ->
        nth_error es i = Some e ->
        nth_error vs i = Some v ->
        sem_exp_instant b R e v.
    Proof.
      intros b R es vs i e v Hexp Hnthe Hnthv.
      destruct
        (SecT.Forall2_nth_error_inv
           _ _ (sem_exp_instant b R) es vs i e Hexp Hnthe)
        as (v' & Hnthv' & Hv).
      rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. exact Hv.
    Qed.

    Lemma nth_error_free_in_aexps:
      forall es i e y ck,
        nth_error es i = Some e ->
        Is_free_in_exp y e ->
        Is_free_in_aexps y ck es.
    Proof.
      intros es i e y ck Hnth Hfree.
      apply freeAexps1.
      revert i e Hnth Hfree.
      induction es as [|e0 es IH]; intros i e Hnth Hfree.
      - destruct i; inversion Hnth.
      - destruct i as [|i].
        + simpl in Hnth. inversion Hnth; subst e.
          constructor. exact Hfree.
        + simpl in Hnth.
          constructor 2.
          eapply IH; eauto.
    Qed.

    Lemma history_low_eq_upto_of_sem_vars_eq:
      forall xs H H' vs vs' k,
        sem_vars H xs vs ->
        sem_vars H' xs vs' ->
        (forall j, j <= k -> vs j = vs' j) ->
        history_low_eq_upto xs H H' k.
    Proof.
      intros xs H H' vs vs' k Hvars Hvars' Heq j Hj x Hin _.
      destruct (SecT.In_nth_error_ex _ _ _ Hin) as [i Hnthx].
      specialize (Hvars j).
      specialize (Hvars' j).
      pose proof (Heq j Hj) as Hvals.
      destruct (nth_error (vs j) i) as [v|] eqn:Hnthv.
      - eapply sem_vars_instant_nth_error in Hvars; eauto.
        pose proof Hnthv as Hnthv'.
        rewrite Hvals in Hnthv'.
        eapply sem_vars_instant_nth_error in Hvars'; eauto.
        unfold sem_var_instant in Hvars, Hvars'.
        rewrite Hvars, Hvars'.
        reflexivity.
      - assert (Hi : i < List.length xs).
        {
          apply nth_error_Some.
          rewrite Hnthx.
          discriminate.
        }
        pose proof (Forall2_length _ _ _ Hvars) as Hlen.
        assert (Hi_vs : i < List.length (vs j)).
        { rewrite <- Hlen. exact Hi. }
        pose proof (nth_error_nth' (vs j) i absent Hi_vs) as Hsome.
        rewrite Hnthv in Hsome.
        discriminate.
    Qed.

    Lemma sem_exps_prefix_eq:
      forall bk H H' es ls ls' k,
        (forall y, Exists (Is_free_in_exp y) es ->
             forall j, j <= k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_exps bk H es ls ->
        sem_exps bk H' es ls' ->
        forall j, j <= k -> ls j = ls' j.
    Proof.
      intros bk H H' es ls ls' k Hdep Hsem Hsem' j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
      assert (Hsw : sem_exps_instant (bk j) (H' j) es (ls j)).
      {
        apply
          (proj1
             (sem_exps_instant_switch_env
                (bk j) (H j) (H' j) es (ls j)
                (fun y Hy => Hdep y Hy j Hj))).
        exact Hsem.
      }
      eapply sem_exps_instant_det; eauto.
    Qed.

    Lemma sem_eqapp_inv:
      forall bk H xs ck f exps,
        Indexed.sem_equation all_nodes bk H (EqApp xs ck f exps None) ->
        exists ls ys,
          sem_exps bk H exps ls /\
          sem_vars H xs ys /\
          sem_clock bk H ck (clock_of ls) /\
          Indexed.sem_node all_nodes f ls ys.
    Proof.
      intros bk H xs ck f exps Hsem.
      inversion Hsem; subst; clear Hsem.
      exists ls, xs0.
      repeat split; assumption.
    Qed.

    Lemma sem_eqreset_inv:
      forall bk H xs ck f exps r ckr,
        Indexed.sem_equation all_nodes bk H (EqApp xs ck f exps (Some (r, ckr))) ->
        exists ys rs ls outs,
          sem_exps bk H exps ls /\
          sem_vars H xs outs /\
          sem_clock bk H ck (clock_of ls) /\
          sem_var H r ys /\
          bools_of ys rs /\
          (forall k, Indexed.sem_node all_nodes f (mask k rs ls) (mask k rs outs)).
    Proof.
      intros bk H xs ck f exps r ckr Hsem.
      inversion Hsem; subst; clear Hsem.
      exists ys, rs, ls, xs0.
      repeat split; assumption.
    Qed.

    Lemma sem_node_inv:
      forall f xss yss,
        Indexed.sem_node all_nodes f xss yss ->
        exists bk H nd,
          bk = clock_of xss /\
          find_node f all_nodes = Some nd /\
          sem_vars H (map fst nd.(n_in)) xss /\
          sem_vars H (map fst nd.(n_out)) yss /\
          sem_clocked_vars bk H (idck nd.(n_in)) /\
          Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs).
    Proof.
      intros f xss yss Hsem.
      destruct Hsem
        as [bk0 H0 f0 xss0 yss0 n0 Hbk Hfind Hin Hout Hclock Heqs].
      exists bk0, H0, n0.
      repeat split; assumption.
    Qed.

    Lemma wc_reset_in_call_vars:
      forall P vars xs ck f exps rx rck,
        Clo.wc_equation P vars (EqApp xs ck f exps (Some (rx, rck))) ->
        In (rx, rck) vars.
    Proof.
      intros P vars xs ck f exps rx rck Hwc.
      inversion Hwc as [|xs' ck' f' exps' r' nd sub Hfind Hins Houts Hr|]; subst.
      eapply Hr. reflexivity.
    Qed.

    Lemma nth_error_mask_count_self:
      forall rs xss k i v,
        nth_error (mask (count rs k) rs xss k) i = Some v ->
        nth_error (xss k) i = Some v.
    Proof.
      intros rs xss k i v Hnth.
      unfold mask in Hnth.
      rewrite Nat.eqb_refl in Hnth.
      exact Hnth.
    Qed.

    Lemma nth_error_all_absent_absent:
      forall (A : Type) (xs : list A) i v,
        nth_error (all_absent xs) i = Some v ->
        v = absent.
    Proof.
      intros A xs.
      induction xs as [|x xs IH]; intros i v Hnth.
      - destruct i; inversion Hnth.
      - destruct i as [|i].
        + simpl in Hnth. inversion Hnth. reflexivity.
        + simpl in Hnth. eapply IH; eauto.
    Qed.

    Lemma exp_type_low:
      forall e ety y,
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.hm_ext dlt ety ⊑ t ->
        Is_free_in_exp y e ->
        low_var y.
    Proof.
      intros e ety y He Hlow Hfree.
      destruct (assign_exp_type_free_bound e ety y Hfree He)
        as (alpha & Hfind & Hbound).
      exists alpha.
      split; [exact Hfind|].
      eapply order_trans; eauto.
    Qed.

    Lemma hold_eq_prefix:
      forall v0 xs xs' k,
        (forall j, j < k -> xs j = xs' j) ->
        Indexed.hold v0 xs k = Indexed.hold v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix.
      induction k as [|m IH]; [reflexivity|].
      simpl.
      assert (Hm : m < S m) by lia.
      pose proof (Hprefix m Hm) as Hm_eq.
      rewrite Hm_eq.
      destruct (xs' m) eqn:Hn; auto.
    Qed.

    Lemma fby_eq_prefix:
      forall v0 xs xs' k,
        (forall j, j <= k -> xs j = xs' j) ->
        Indexed.fby v0 xs k = Indexed.fby v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix.
      unfold Indexed.fby.
      pose proof (Hprefix k (le_n k)) as Hk_eq.
      rewrite Hk_eq.
      destruct (xs' k) eqn:Hn; auto.
      f_equal.
      apply hold_eq_prefix.
      intros j Hj.
      apply Hprefix.
      lia.
    Qed.

    Lemma fby_eq_delay_prefix:
      forall v0 xs xs' k,
        (forall j, j < k -> xs j = xs' j) ->
        (xs k = absent <-> xs' k = absent) ->
        Indexed.fby v0 xs k = Indexed.fby v0 xs' k.
    Proof.
      intros v0 xs xs' k Hprefix Habs.
      unfold Indexed.fby.
      destruct (xs k) eqn:Hk.
      - destruct (xs' k) eqn:Hk'; simpl.
        + reflexivity.
        + exfalso.
          assert (Hab0 : absent = absent) by reflexivity.
          pose proof (proj1 Habs Hab0) as Hab.
          congruence.
      - destruct (xs' k) eqn:Hk'; simpl.
        + exfalso.
          assert (Hab0 : absent = absent) by reflexivity.
          pose proof (proj2 Habs Hab0) as Hab.
          congruence.
        + f_equal.
          eapply hold_eq_prefix; eauto.
    Qed.

    Lemma sem_aexp_prefix_eq:
      forall bk H H' ck e ls ls' k,
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk H' ck e ls' ->
        forall j, j < k -> ls j = ls' j.
    Proof.
      intros bk H H' ck e ls ls' k Hdep Hsem Hsem' j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
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
        - exact Hsem.
      }
      eapply sem_aexp_instant_det; eauto.
    Qed.

    Lemma sem_aexp_instant_absent_clock_false:
      forall b R ck e,
        sem_aexp_instant b R ck e absent ->
        sem_clock_instant b R ck false.
    Proof.
      intros b R ck e Hsem.
      inversion Hsem; subst; auto; discriminate.
    Qed.

    Lemma sem_aexp_instant_present_clock_true:
      forall b R ck e v,
        sem_aexp_instant b R ck e (present v) ->
        sem_clock_instant b R ck true.
    Proof.
      intros b R ck e v Hsem.
      inversion Hsem; subst; auto; discriminate.
    Qed.

    Lemma sem_aexp_same_presence_from_clock:
      forall bk H H' ck e ls ls' k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        sem_aexp bk H ck e ls ->
        sem_aexp bk H' ck e ls' ->
        (ls k = absent <-> ls' k = absent).
    Proof.
      intros bk H H' ck e ls ls' k Hdep Hsem Hsem'.
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
      - specialize (Hsem k). rewrite Hlk in Hsem.
        specialize (Hsem' k). rewrite Hlk' in Hsem'.
        pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem) as Hf.
        pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem') as Ht.
        pose proof (proj1 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
      - specialize (Hsem k). rewrite Hlk in Hsem.
        specialize (Hsem' k). rewrite Hlk' in Hsem'.
        pose proof (sem_aexp_instant_present_clock_true _ _ _ _ _ Hsem) as Ht.
        pose proof (sem_aexp_instant_absent_clock_false _ _ _ _ Hsem') as Hf.
        pose proof (proj2 (Hclk_sw false) Hf) as Hf'.
        assert (Heq : false = true).
        { eapply sem_clock_instant_det; eauto. }
        discriminate.
    Qed.

    Lemma history_low_eq_from_Forall_pointwise:
      forall X H H',
        Forall (fun x => low_var x -> forall k, Env.find x (H k) = Env.find x (H' k)) X ->
        history_low_eq X H H'.
    Proof.
      intros X H H' Hpts k x Hin Hlow.
      eapply Forall_forall in Hpts; [|exact Hin].
      eapply Hpts; eauto.
    Qed.

    Lemma eqdef_noninterference:
      forall X bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_caexp y ck ce -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety
             Hlow HX Hfindx Hck Hce Hsat Hlowx Hvar Hrhs Hvar' Hrhs' k.
      assert (Hfree :
                forall y, Is_free_in_caexp y ck ce -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_caexp base_ty rst_ty x ck ce xty ckty cety y
                   Hfindx Hck Hce Hsat Hlowx Hy). }
      assert (Hrhs_switched : sem_caexp bk H' ck ce xs).
      { eapply sem_caexp_switch_history_low; eauto. }
      assert (Hxs : xs = xs').
      { eapply sem_caexp_det; eauto. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    Lemma eqfby_noninterference:
      forall X bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety,
        history_low_eq X H H' ->
        (forall y, Is_free_in_aexp y ck e -> In y X) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros X bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety
             Hlow HX Hfindx Hck He Hsat Hlowx Hvar Hrhs Hfby
             Hvar' Hrhs' Hfby' k.
      assert (Hfree :
                forall y, Is_free_in_aexp y ck e -> In y X /\ low_var y).
      { intros y Hy. split.
        - apply HX; exact Hy.
        - apply (simple_security_aexp base_ty rst_ty x ck e xty ckty ety y
                   Hfindx Hck He Hsat Hlowx Hy). }
      assert (Hrhs_switched : sem_aexp bk H' ck e ls).
      { eapply sem_aexp_switch_history_low; eauto. }
      assert (Hls : ls = ls').
      { eapply sem_aexp_det; eauto. }
      assert (Hxs : xs = xs').
      { rewrite Hfby.
        rewrite <- Hls in Hfby'.
        rewrite Hfby'.
        reflexivity. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    Lemma sem_caexp_switch_pointwise:
      forall bk H H' ck ce xs,
        (forall y, Is_free_in_caexp y ck ce ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        sem_caexp bk H ck ce xs ->
        sem_caexp bk H' ck ce xs.
    Proof.
      intros bk H H' ck ce xs Hdep Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_caexp_instant_switch_env
              (bk k) (H k) (H' k) ck ce (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck => Hdep y (FreeCAexp2 _ _ _ Hyck) k
                 | or_intror Hyce => Hdep y (FreeCAexp1 _ _ _ Hyce) k
                 end))).
      exact Hsem.
    Qed.

    Lemma sem_aexp_switch_pointwise:
      forall bk H H' ck e xs,
        (forall y, Is_free_in_aexp y ck e ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        sem_aexp bk H ck e xs ->
        sem_aexp bk H' ck e xs.
    Proof.
      intros bk H H' ck e xs Hdep Hsem k.
      specialize (Hsem k).
      apply
        (proj1
           (sem_aexp_instant_switch_env
              (bk k) (H k) (H' k) ck e (xs k)
              (fun y Hy =>
                 match Hy with
                 | or_introl Hyck => Hdep y (freeAexp2 _ _ _ Hyck) k
                 | or_intror Hye => Hdep y (freeAexp1 _ _ _ Hye) k
                 end))).
      exact Hsem.
    Qed.

    Lemma eqdef_noninterference_pointwise:
      forall bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety,
        (forall y, Is_free_in_caexp y ck ce ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_cexp_type ty_env ce = Some cety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ cety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ck ce base_ty rst_ty xty ckty cety
             Hdep Hfindx Hck Hce Hsat Hlowx Hvar Hrhs Hvar' Hrhs' k.
      assert (Hrhs_switched : sem_caexp bk H' ck ce xs).
      { eapply sem_caexp_switch_pointwise; eauto. }
      assert (Hxs : xs = xs').
      { eapply sem_caexp_det; eauto. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    Lemma eqdef_noninterference_instant_pointwise:
      forall bk H H' x xs xs' ck ce k,
        (forall y, Is_free_in_caexp y ck ce ->
             Env.find y (H k) = Env.find y (H' k)) ->
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_var H' x xs' ->
        sem_caexp bk H' ck ce xs' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ck ce k
             Hdep Hvar Hrhs Hvar' Hrhs'.
      specialize (Hvar k).
      specialize (Hrhs k).
      specialize (Hvar' k).
      specialize (Hrhs' k).
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

    Lemma eqfby_noninterference_pointwise:
      forall bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety,
        (forall y, Is_free_in_aexp y ck e ->
             forall k, Env.find y (H k) = Env.find y (H' k)) ->
        Env.find x ty_env = Some xty ->
        SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        SecT.satisfiable dlt ((([rst_ty] ⊔ ckty) ⊔ ety)) [xty] ->
        low_var x ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        forall k, Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ls ls' ck c0 e base_ty rst_ty xty ckty ety
             Hdep Hfindx Hck He Hsat Hlowx Hvar Hrhs Hfby
             Hvar' Hrhs' Hfby' k.
      assert (Hrhs_switched : sem_aexp bk H' ck e ls).
      { eapply sem_aexp_switch_pointwise; eauto. }
      assert (Hls : ls = ls').
      { eapply sem_aexp_det; eauto. }
      assert (Hxs : xs = xs').
      { rewrite Hfby.
        rewrite <- Hls in Hfby'.
        rewrite Hfby'.
        reflexivity. }
      specialize (Hvar k).
      specialize (Hvar' k).
      rewrite <- Hxs in Hvar'.
      rewrite Hvar, Hvar'.
      reflexivity.
    Qed.

    Lemma eqfby_noninterference_delayed_pointwise:
      forall bk H H' x xs xs' ls ls' ck c0 e k,
        (forall y, Is_free_in_clock y ck ->
             Env.find y (H k) = Env.find y (H' k)) ->
        (forall y, Is_free_in_aexp y ck e ->
             forall j, j < k -> Env.find y (H j) = Env.find y (H' j)) ->
        sem_var H x xs ->
        sem_aexp bk H ck e ls ->
        xs = Indexed.fby (sem_const c0) ls ->
        sem_var H' x xs' ->
        sem_aexp bk H' ck e ls' ->
        xs' = Indexed.fby (sem_const c0) ls' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros bk H H' x xs xs' ls ls' ck c0 e k
             Hclock Hpast
             Hvar Hrhs Hfby Hvar' Hrhs' Hfby'.
      assert (Hls_prefix : forall j, j < k -> ls j = ls' j).
      { eapply sem_aexp_prefix_eq; eauto. }
      assert (Hls_abs : ls k = absent <-> ls' k = absent).
      { eapply sem_aexp_same_presence_from_clock; eauto. }
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

  End GENERATED_LOW_OBSERVATION.

  (** Observation depends on a valuation only through the security names of
      the observed variables, so two valuations that agree on a set holding
      those names observe alike. *)
  Lemma low_var_agree :
    forall ty_env d d' t S x,
      SecT.agree_on S d d' ->
      (exists a, Env.find x ty_env = Some a /\ In a S) ->
      low_var ty_env d t x -> low_var ty_env d' t x.
  Proof.
    intros ty_env d d' t S x Hag (a & Hfa & Hin) (b & Hfb & Hle).
    rewrite Hfa in Hfb. inversion Hfb; subst b.
    exists a. split; [exact Hfa|]. rewrite <- (Hag a Hin). exact Hle.
  Qed.

  Lemma get_mappings_scope_incl :
    forall A (xs : list (ident * A)) env tys x S,
      get_mappings_from_node xs env = Some tys ->
      In x (map fst xs) ->
      incl tys S ->
      exists a, Env.find x env = Some a /\ In a S.
  Proof.
    intros A xs env tys x S Hmap Hx Hincl.
    apply fst_InMembers in Hx.
    destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hx Hmap)
      as (a & Hfind & Hin).
    exists a. split; [exact Hfind|apply Hincl; exact Hin].
  Qed.

  Lemma history_low_eq_upto_agree :
    forall ty_env d d' t S X H H' k,
      SecT.agree_on S d d' ->
      (forall x, In x X -> exists a, Env.find x ty_env = Some a /\ In a S) ->
      history_low_eq_upto ty_env d t X H H' k ->
      history_low_eq_upto ty_env d' t X H H' k.
  Proof.
    intros ty_env d d' t S X H H' k Hag HX Hl j Hj x Hx Hlow.
    apply (Hl j Hj x Hx).
    destruct (HX x Hx) as (a & Hfa & Hin).
    destruct Hlow as (b & Hfb & Hle). rewrite Hfa in Hfb. inversion Hfb; subst b.
    exists a. split; [exact Hfa|]. rewrite (Hag a Hin). exact Hle.
  Qed.

  Section GENERATED_NODE_SECURITY.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** This recovers the local clocking fact for a node found in a well-clocked global.  Many generated-signature and semantic lemmas use it to move from a global assumption to a node-local one. *)
    Lemma wc_global_find_node:
      forall n,
        Clo.wc_global all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
        exists P, Clo.wc_node P n.
    Proof.
      intros n Hwc Hfind.
      pose proof (find_node_In _ _ _ Hfind) as (_ & Hin).
      apply in_split in Hin as (prefix & suffix & Hall).
      subst all_nodes.
      exists suffix.
      clear Hfind.
      revert suffix Hwc.
      induction prefix as [|m prefix IH]; intros suffix Hwc.
      - simpl in Hwc.
        inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        exact Hwc_head.
      - simpl in Hwc.
        inversion Hwc as [|m' ms Hwc_tail Hwc_head]; subst m' ms.
        eapply IH; eauto.
    Qed.

    Lemma Is_free_in_wc_clock:
      forall vars x ck,
        wc_clock vars ck ->
        Is_free_in_clock x ck ->
        InMembers x vars.
    Proof.
      intros vars x ck Hwc.
      induction Hwc; intros Hfree.
      - inversion Hfree.
      - inversion Hfree; subst; eauto.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
    Qed.

    Lemma Is_free_in_wc_exp:
      forall vars x e ck,
        wc_exp vars e ck ->
        Is_free_in_exp x e ->
        InMembers x vars.
    Proof.
      intros vars x e ck Hwc.
      induction Hwc; intros Hfree.
      - inversion Hfree.
      - inversion Hfree; subst.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
      - inversion Hfree; subst; eauto.
        match goal with
        | Hin : In (_, _) _ |- _ =>
            now apply In_InMembers in Hin
        end.
      - inversion Hfree; subst; eauto.
      - inversion Hfree; subst; eauto.
        destruct H1; eauto.
    Qed.

    Lemma Is_free_in_wc_aexp:
      forall vars x ck e,
        wc_env vars ->
        Is_free_in_aexp x ck e ->
        wc_exp vars e ck ->
        InMembers x vars.
    Proof.
      intros vars x ck e Hwcenv Hfree Hwc.
      inversion Hfree; subst.
      - eapply Is_free_in_wc_exp; eauto.
      - eapply Is_free_in_wc_clock.
        + eapply wc_clock_exp; eauto.
        + exact H.
    Qed.

    Lemma free_aexp_in_inputs_or_defined:
      forall P n x ck c0 e y,
        Clo.wc_node P n ->
        In (EqFby x ck c0 e) n.(n_eqs) ->
        Is_free_in_aexp y ck e ->
        In y (map fst n.(n_in)) \/ In y (vars_defined n.(n_eqs)).
    Proof.
      intros P n x ck c0 e y
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin Hfree.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      assert (Hy_mem : InMembers y (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { eapply Is_free_in_wc_aexp; eauto. }
      rewrite InMembers_idck in Hy_mem.
      rewrite InMembers_app in Hy_mem.
      destruct Hy_mem as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app.
            apply in_or_app.
            now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app.
            apply in_or_app.
            now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    Lemma free_aexp_low_eq_prefix_from_inputs_or_defined:
      forall P n ty_env dlt t H H' x ck c0 e y k,
        Clo.wc_node P n ->
        In (EqFby x ck c0 e) n.(n_eqs) ->
        Is_free_in_aexp y ck e ->
        low_var ty_env dlt t y ->
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' (S k) ->
        history_low_eq_upto ty_env dlt t (vars_defined n.(n_eqs)) H H' k ->
        forall j, j < S k -> Env.find y (H j) = Env.find y (H' j).
    Proof.
      intros P n ty_env dlt t H H' x ck c0 e y k
             Hwcnode Heqin Hfree Hlowy Hlowin Hprev j Hj.
      destruct (free_aexp_in_inputs_or_defined P n x ck c0 e y Hwcnode Heqin Hfree)
        as [Hin|Hdef].
      - eapply Hlowin; eauto.
        lia.
      - eapply Hprev; eauto.
        lia.
    Qed.

    Lemma free_exp_in_inputs_or_defined:
      forall P n xs ck f exps r y,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        Exists (Is_free_in_exp y) exps ->
        In y (map fst n.(n_in)) \/ In y (vars_defined n.(n_eqs)).
    Proof.
      intros P n xs ck f exps r y
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin Hfree.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      match goal with
      | Hins : Forall2 _ _ exps |- _ => rename Hins into Hwcins
      end.
      apply Exists_exists in Hfree as (e & Hine & Hfree_e).
      destruct (SecT.In_nth_error_ex _ _ _ Hine) as [i Hnthe].
      assert (Hi_in : i < List.length n0.(n_in)).
      {
        pose proof (Forall2_length _ _ _ Hwcins) as Hlen.
        assert (Hi_exp : i < List.length exps).
        {
          apply nth_error_Some.
          rewrite Hnthe.
          discriminate.
        }
        rewrite Hlen.
        exact Hi_exp.
      }
      destruct (nth_error n0.(n_in) i) as [in_pair|] eqn:Hnthin.
      2:{
        apply nth_error_None in Hnthin.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun '(x, (_, xck)) le =>
              SameVar (sub x) le
              /\ exists lck, wc_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) le lck
                       /\ instck ck sub xck = Some lck)
           n0.(n_in) exps i in_pair
           Hwcins Hnthin)
        as (e' & Hnthe' & Hwc_pair).
      rewrite Hnthe in Hnthe'.
      inversion Hnthe'; subst e'; clear Hnthe'.
      destruct in_pair as [xin [xty xck]].
      cbn in Hwc_pair.
      destruct Hwc_pair as [_ (lck & Hwc_e & _)].
      assert (Hy_mem : InMembers y (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { eapply Is_free_in_wc_exp; eauto. }
      rewrite InMembers_idck in Hy_mem.
      rewrite InMembers_app in Hy_mem.
      destruct Hy_mem as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    Lemma reset_var_in_inputs_or_defined:
      forall P n xs ck f exps r ckr,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
        In r (map fst n.(n_in)) \/ In r (vars_defined n.(n_eqs)).
    Proof.
      intros P n xs ck f exps r ckr
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      inversion Hwc_eqs; subst.
      match goal with
      | Hrst : forall yck, _ = Some yck -> In yck _ |- _ => rename Hrst into Hwcrst
      end.
      assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      {
        eapply Hwcrst.
        reflexivity.
      }
      apply In_InMembers in Hinr.
      rewrite InMembers_idck in Hinr.
      rewrite InMembers_app in Hinr.
      destruct Hinr as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In r (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In r (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    Lemma sem_var_low_eq_upto:
      forall H H' x ys ys' k,
        sem_var H x ys ->
        sem_var H' x ys' ->
        (forall j, j <= k -> Env.find x (H j) = Env.find x (H' j)) ->
        forall j, j <= k -> ys j = ys' j.
    Proof.
      intros H H' x ys ys' k Hvar Hvar' Heq j Hj.
      specialize (Hvar j).
      specialize (Hvar' j).
      unfold sem_var_instant in Hvar, Hvar'.
      pose proof (Heq j Hj) as Hfind_eq.
      rewrite Hvar in Hfind_eq.
      rewrite Hvar' in Hfind_eq.
      inversion Hfind_eq.
      reflexivity.
    Qed.

    Lemma bools_of_eq_upto:
      forall ys ys' rs rs' k,
        bools_of ys rs ->
        bools_of ys' rs' ->
        (forall j, j <= k -> ys j = ys' j) ->
        forall j, j <= k -> rs j = rs' j.
    Proof.
      intros ys ys' rs rs' k Hbool Hbool' Heq j Hj.
      specialize (Hbool j).
      specialize (Hbool' j).
      rewrite (Heq j Hj) in Hbool.
      rewrite Hbool in Hbool'.
      inversion Hbool'.
      reflexivity.
    Qed.

    Lemma count_eq_upto:
      forall rs rs' k,
        (forall j, j <= k -> rs j = rs' j) ->
        forall j, j <= k -> count rs j = count rs' j.
    Proof.
      intros rs rs' k Heq.
      induction j as [|j IH]; intros Hj.
      - simpl.
        rewrite (Heq 0 Hj).
        reflexivity.
      - simpl.
        rewrite (Heq (S j) Hj).
        rewrite (IH (Nat.le_trans _ _ _ (Nat.le_succ_diag_r j) Hj)).
        reflexivity.
    Qed.

    Lemma clock_var_in_inputs_or_defined:
      forall P n xs ck f exps r y,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        Is_free_in_clock y ck ->
        In y (map fst n.(n_in)) \/ In y (vars_defined n.(n_eqs)).
    Proof.
      intros P n xs ck f exps r y
             (Hwc_in & Hwc_io & Hwc_all & Hwc_eqs)
             Heqin Hfree.
      eapply Forall_forall in Hwc_eqs; [|exact Heqin].
      assert (Hy_mem : InMembers y (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      {
        eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto.
      }
      rewrite InMembers_idck in Hy_mem.
      rewrite InMembers_app in Hy_mem.
      destruct Hy_mem as [Hin|Hrest].
      - left.
        apply InMembers_In in Hin as (? & Hin).
        now apply in_map with (f := fst) in Hin.
      - right.
        rewrite InMembers_app in Hrest.
        destruct Hrest as [Hvars|Hout].
        + apply InMembers_In in Hvars as (? & Hvars).
          apply in_map with (f := fst) in Hvars.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now left. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
        + apply InMembers_In in Hout as (? & Hout).
          apply in_map with (f := fst) in Hout.
          assert (Hin_vo : In y (map fst (n.(n_vars) ++ n.(n_out)))).
          { rewrite map_app. apply in_or_app. now right. }
          eapply Permutation_in; [apply Permutation_sym, n.(n_defd)|exact Hin_vo].
    Qed.

    Lemma free_clock_low_eq_prefix_from_inputs_or_defined:
      forall P n ty_env dlt t H H' xs ck f exps r y k,
        Clo.wc_node P n ->
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        Is_free_in_clock y ck ->
        low_var ty_env dlt t y ->
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' (S k) ->
        history_low_eq_upto ty_env dlt t (vars_defined n.(n_eqs)) H H' k ->
        forall j, j < S k -> Env.find y (H j) = Env.find y (H' j).
    Proof.
      intros P n ty_env dlt t H H' xs ck f exps r y k
             Hwcnode Heqin Hfree Hlowy Hlowin Hprev j Hj.
      destruct (clock_var_in_inputs_or_defined P n xs ck f exps r y Hwcnode Heqin Hfree)
        as [Hin|Hdef].
      - eapply Hlowin; eauto.
        lia.
      - eapply Hprev; eauto.
        lia.
    Qed.

    Lemma assign_clk_type_free_var_in :
      forall env base ck ckty z ty,
        SECCETYPING.assign_clk_type env base ck = Some ckty ->
        Is_free_in_clock z ck ->
        Env.find z env = Some ty ->
        In ty ckty.
    Proof.
      intros env base ck.
      induction ck as [|ck IH x b]; intros ckty z ty Hassign Hfree Hfind.
      - inversion Hfree.
      - simpl in Hassign.
        destruct (SECCETYPING.assign_clk_type env base ck) as [ckty'|] eqn:Hck;
          try discriminate.
        destruct (Env.find x env) as [xty|] eqn:Hfindx; try discriminate.
        inversion Hassign; subst ckty; clear Hassign.
        inversion Hfree; subst.
        + rewrite Hfindx in Hfind.
          inversion Hfind; subst ty.
          eapply in_merge_right.
          simpl. now left.
        + eapply in_merge_left.
          eapply IH; eauto.
    Qed.

    Lemma sem_clock_eq_upto_from_env_eq :
      forall bk bk' H H' ck bs bs' k,
        sem_clock bk H ck bs ->
        sem_clock bk' H' ck bs' ->
        (forall j, j <= k -> bk j = bk' j) ->
        (forall z, Is_free_in_clock z ck -> forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        forall j, j <= k -> bs j = bs' j.
    Proof.
      intros bk bk' H H' ck bs bs' k Hsem Hsem' Hbk Heqenv j Hj.
      specialize (Hsem j).
      specialize (Hsem' j).
      rewrite <- (Hbk j Hj) in Hsem'.
      assert (Hswitch : sem_clock_instant (bk j) (H j) ck (bs' j)).
      {
        pose proof
          (sem_clock_instant_switch_env (bk j) (H j) (H' j) ck (bs' j))
          as Hswitch_iff.
        specialize (Hswitch_iff (fun z Hz => Heqenv z Hz j Hj)).
        destruct Hswitch_iff as [_ Hback].
        exact (Hback Hsem').
      }
      eapply sem_clock_instant_det; eauto.
    Qed.

    Lemma clock_of_mask_eq_upto :
      forall ls ls' rs rs' kr kr' k,
        kr = count rs k ->
        kr' = count rs' k ->
        (forall j, j <= k -> count rs j = count rs' j) ->
        (forall j, j <= k -> clock_of ls j = clock_of ls' j) ->
        forall j, j <= k ->
          clock_of (mask kr rs ls) j = clock_of (mask kr' rs' ls') j.
    Proof.
      intros ls ls' rs rs' kr kr' k Hkr Hkr' Hcount Hclk j Hj.
      unfold clock_of.
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount j Hj) as Hcntj.
          specialize (Hcount k (le_n k)) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        unfold mask.
        assert ((kr =? count rs j) = true) as ->.
        { apply Nat.eqb_eq. symmetry. exact Hactive. }
        assert ((kr' =? count rs' j) = true) as ->.
        { apply Nat.eqb_eq. symmetry. exact Hactive'. }
        exact (Hclk j Hj).
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          apply Hopaque.
          specialize (Hcount j Hj) as Hcntj.
          specialize (Hcount k (le_n k)) as Hcntk.
          rewrite Hcntj.
          rewrite Heq.
          rewrite Hkr'.
          rewrite <- Hcntk.
          symmetry.
          exact Hkr.
        }
        rewrite (mask_opaque ls kr rs j Hopaque).
        rewrite (mask_opaque ls' kr' rs' j Hopaque').
        rewrite (proj2 (clock_of_instant_false (all_absent (ls 0))) (@all_absent_spec value (ls 0))).
        rewrite (proj2 (clock_of_instant_false (all_absent (ls' 0))) (@all_absent_spec value (ls' 0))).
        reflexivity.
    Qed.

    Lemma node_scope_upper_bounded_from_local_env:
      forall n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals ty,
        NAMEGEN.generate_local_env_for_node n st = OK ((env, rec), st') ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
        exists m, ty = Ids.gensym Ids.sec m /\ (m < st')%positive.
    Proof.
      intros n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals ty
             Hlocal Hclk Hrst Hinp Hout Hlocals Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
          as (xinp & ainp & _ & Hfindinp).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindinp) as (m & Hm & Hlt).
        exists m. split; assumption.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
          as (xout & aout & _ & Hfindout).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindout) as (m & Hm & Hlt).
        exists m. split; assumption.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin)
          as (xlocal & alocal & _ & Hfindlocal).
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hfindlocal) as (m & Hm & Hlt).
        exists m. split; assumption.
      - subst ty.
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hclk) as (m & Hm & Hlt).
        exists m. split; assumption.
      - subst ty.
        eapply NAMEGEN.generate_local_env_for_node_bounded in Hlocal as Hbound.
        specialize (Hbound _ _ Hrst) as (m & Hm & Hlt).
        exists m. split; assumption.
    Qed.

    Inductive node_security
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
    | SecureNode :
        forall ty_env sig
               clk_id rst_id clk_type rst_type inp out locals raw st_n,
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
          signature_satisfied dlt_sig sig ->
          SecT.agree_on (signature_scope sig) dlt_sig dlt_raw ->
          SecT.listSatisfiable dlt_raw raw ->

          (forall xs ck f exps callee callee_sig
                  ckty inptyp outtyp st_clk st_inp,
              In (EqApp xs ck f exps None) nd.(n_eqs) ->
              find_node f all_nodes = Some callee ->
              SIG.find_signature f G = Some callee_sig ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
                SC.init_state = OK (ckty, st_clk) ->
              SC.mmap
                (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                exps st_clk = OK (inptyp, st_inp) ->
              get_mappings xs ty_env = Some outtyp ->
              callee_secure nd dlt_sig dlt_raw callee callee_sig
                (SIGPROOFS.lat_valuation dlt_sig callee_sig inptyp ckty
                   [sig.(s_reset)] outtyp)
                (SIGPROOFS.lat_valuation dlt_raw callee_sig inptyp ckty
                   [sig.(s_reset)] outtyp)) ->

          (forall xs ck f exps r ckr callee callee_sig
                  ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
              In (EqApp xs ck f exps (Some (r, ckr))) nd.(n_eqs) ->
              find_node f all_nodes = Some callee ->
              SIG.find_signature f G = Some callee_sig ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ck)
                SC.init_state = OK (ckty, st_clk) ->
              Env.find r ty_env = Some rty ->
              SC.option_to_sec
                (SECCETYPING.assign_clk_type ty_env sig.(s_clk) ckr)
                st_clk = OK (rstty, st_rst) ->
              SC.mmap
                (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
                exps st_rst = OK (inptyp, st_inp) ->
              get_mappings xs ty_env = Some outtyp ->
              callee_secure nd dlt_sig dlt_raw callee callee_sig
                (SIGPROOFS.lat_valuation dlt_sig callee_sig inptyp ckty
                   ([sig.(s_reset)] ⊔ ([rty] ⊔ rstty)) outtyp)
                (SIGPROOFS.lat_valuation dlt_raw callee_sig inptyp ckty
                   ([sig.(s_reset)] ⊔ ([rty] ⊔ rstty)) outtyp)) ->
          node_security nd dlt_sig dlt_raw

    (** A callee is secure at a call site when it is secure at a valuation
        [w] that agrees with the one the call induces on the callee's
        signature scope.  The callee's locals are not the caller's business:
        its interface is what the call sees, so each call instance takes its
        own valuation of them.  The callee is read at [(w, w)]: the
        signature-level valuation the call induces is arbitrary off the
        callee's scope (it holds whatever the caller's valuation holds at the
        callee's local names), so letting it reach the callee's own call
        clauses would make the predicate unsatisfiable. *)
    with callee_secure
      (nd : node) (dlt_sig dlt_raw : ground_instantiation)
      : node -> signature -> ground_instantiation -> ground_instantiation
        -> Prop :=
    | CalleeSecure :
        forall callee callee_sig dlt_sig_c dlt_raw_c dlt_w,
          SecT.agree_on (signature_scope callee_sig) dlt_raw_c dlt_w ->
          node_security callee dlt_w dlt_w ->
          callee_secure nd dlt_sig dlt_raw callee callee_sig dlt_sig_c dlt_raw_c.

  Scheme node_security_mind := Induction for node_security Sort Prop
    with callee_secure_mind := Induction for callee_secure Sort Prop.

  End GENERATED_NODE_SECURITY.

End SECNLUSNONINTERFERENCESUPPORT.
