From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSTYPINGCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Ord   : NLORDERED Ids Op CESyn SynNL)
  (Import Mem   : MEMORIES Ids Op CESyn SynNL)
  (Import IsD   : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo   : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo).

  (** Source-side naming inversion for generated auxiliary clock/reset names. *)
  Lemma get_node_aux_In:
    forall name aux clk_id rst_id,
      get_node_aux name aux = Some (clk_id, rst_id) ->
      exists rec,
        In rec aux
        /\ rec.(nname) = name
        /\ rec.(nclk) = clk_id
        /\ rec.(nrst) = rst_id.
  Proof.
    induction aux as [|rec aux IH]; intros clk_id rst_id Haux.
    - unfold get_node_aux in Haux. simpl in Haux. discriminate.
    - unfold get_node_aux in Haux. simpl in Haux.
      destruct (ident_eqb name rec.(nname)) eqn:Hname.
      + inversion Haux; subst clk_id rst_id.
        apply ident_eqb_eq in Hname.
        exists rec. split; [now left|].
        repeat split; auto.
      + eapply IH in Haux as (rec' & Hin & Hn & Hc & Hr).
        exists rec'. split; [now right|].
        repeat split; auto.
  Qed.

  Lemma generate_node_aux_sec_names:
    forall all_nodes env aux_names name clk_id rst_id,
      generate_node_env all_nodes = OK (env, aux_names) ->
      get_node_aux name aux_names = Some (clk_id, rst_id) ->
      exists i j,
        clk_id = Ids.gensym Ids.sec i
        /\ rst_id = Ids.gensym Ids.sec j.
  Proof.
    intros all_nodes env aux_names name clk_id rst_id Hgen Haux.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
      as [_ [_ Hauxsec]];
      eauto.
    - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
    - constructor.
    - intros rec Hin. contradiction.
    - eapply get_node_aux_In in Haux as (rec & Hin & _ & Hclk & Hrst).
      specialize (Hauxsec rec Hin) as (i & j & Hi & Hj).
      rewrite Hclk, Hrst in *. eauto.
  Qed.

  Lemma generate_node_env_sec_range:
    forall all_nodes env aux_names x ty,
      generate_node_env all_nodes = OK (env, aux_names) ->
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec n.
  Proof.
    intros all_nodes env aux_names x ty Hgen Hfind.
    unfold generate_node_env in Hgen.
    destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
      as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst env aux_names.
    destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
      as [Hbound _];
      eauto.
    - intros z tz Hz. rewrite Env.gempty in Hz. discriminate.
    - constructor.
    - intros rec Hin. contradiction.
    - specialize (Hbound _ _ Hfind) as [n [Hty _]].
      exists n. exact Hty.
  Qed.

  Lemma node_scope_sec_range:
    forall all_nodes env aux_names n
           clk_id rst_id clk_type rst_type inp out locals ty,
      generate_node_env all_nodes = OK (env, aux_names) ->
      get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
      exists m, ty = Ids.gensym Ids.sec m.
  Proof.
    intros all_nodes env aux_names n clk_id rst_id clk_type rst_type inp out locals ty
           Henvgen Haux Hclk Hrst Hinp Hout Hlocals Hin.
    repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin) as (x & a & _ & Hfind).
      eapply generate_node_env_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin) as (x & a & _ & Hfind).
      eapply generate_node_env_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin) as (x & a & _ & Hfind).
      eapply generate_node_env_sec_range; eauto.
    - subst. eapply generate_node_env_sec_range; eauto.
    - subst. eapply generate_node_env_sec_range; eauto.
  Qed.

  (** IDS-side naming invariant.

      The concrete [Ident] implementation satisfies this because the thesis
      prefix [sec] is distinct from Velus' existing gensym prefixes [elab],
      [norm1], and [norm2].  The abstract [IDS] interface does not expose that
      separation, so correctness lemmas that reason about generated helper
      names keep it explicit here. *)
  Hypothesis sec_not_in_gensym_prefs :
    ~In Ids.sec gensym_prefs.

  Lemma node_var_not_sec_gensym:
    forall n x i,
      In x (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros n x i Hin Heq.
    destruct n.(n_good) as [Hgood _].
    rewrite Forall_forall in Hgood.
    specialize (Hgood _ Hin).
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
      exact (sec_not_in_gensym_prefs Hinpre).
  Qed.

  (** Source-local scope reconstruction from shared env mappings.

      This lemma is purely NLustre-side: once the shared environment mappings
      for inputs, outputs, and locals have been recovered, the standard visible
      symbolic scope for the node contains the image of every source variable in
      the clocking environment [idck (n_in ++ n_vars ++ n_out)].

      The translation proof reuses this to feed target-side scopedness
      generators, but the statement itself only depends on source node
      structure. *)
  Lemma node_vars_env_scoped_from_mappings:
    forall n env inp out locals clk_type rst_type,
      get_mappings_from_node (n.(n_in)) env = Some inp ->
      get_mappings_from_node (n.(n_out)) env = Some out ->
      get_mappings_from_node (n.(n_vars)) env = Some locals ->
      SECNLUSTYPING.vars_env_scoped env
        (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
        (inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
  Proof.
    intros n env inp out locals clk_type rst_type Hinp Hout Hlocals x Hmem.
    apply InMembers_idck in Hmem.
    apply InMembers_app in Hmem.
    destruct Hmem as [Hin|Hin].
    - destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp)
        as (ty & Hfind & Hscope).
      exists ty. split; [exact Hfind|].
      apply in_or_app. left.
      exact Hscope.
    - apply InMembers_app in Hin.
      destruct Hin as [Hin|Hin].
      + destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals)
          as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app. right.
        apply in_or_app. right.
        apply in_or_app. left.
        exact Hscope.
      + destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout)
          as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app. right.
        apply in_or_app. left.
        exact Hscope.
  Qed.

  (** Structural side conditions for replaying [simplify_complete] on generated
      NLustre signatures.  This packages exactly the two source-side facts later
      needed by the translation proof: raw well-formedness and disjointness of
      eliminated locals from the visible signature scope. *)
  Definition generated_node_simplify_ready
    (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
    forall G1 n nsig
           clk_id rst_id clk_type rst_type inp out locals raw st_n,
      SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
      get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
      nsig = {| s_name := n.(n_name);
                s_in := inp;
                s_out := out;
                s_reset := rst_type;
                s_clk := clk_type;
                s_constraints := SymTypes.simplify raw locals |} ->
      wf_constraints raw
      /\ (forall x, In x locals -> ~ In x (signature_scope nsig)).

  Theorem generated_node_simplify_ready_from_generated_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      generated_node_simplify_ready env aux_names.
  Proof.
    intros all_nodes env aux_names Henvgen.
    intros G1 n nsig
           clk_id rst_id clk_type rst_type inp out locals raw st_n
           Hnsig Haux Hclk Hrst Hinp Hout Hlocals Hraw Hnsigdef.
    split.
    - eapply SECNLUSTYPING.generate_node_eqns_constraints_wf; eauto.
      eapply NAMEGEN.generate_node_env_injective; eauto.
    - intros ty Hinlocal Hinsig.
      subst nsig.
      unfold signature_scope in Hinsig.
      repeat rewrite in_app_iff in Hinsig.
      destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hinlocal)
        as (xlocal & alocal & Hxlocal & Hfindlocal).
      pose proof (NAMEGEN.generate_node_env_injective _ _ _ Henvgen) as Hinj.
      pose proof (generate_node_aux_sec_names _ _ _ _ _ _ Henvgen Haux)
        as (iclk & irst & Hclkid & Hrstid).
      assert (Hndvars : NoDup (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { apply fst_NoDupMembers. exact n.(n_nodup). }
      destruct Hinsig as [Hininput|[Hinoutput|[Hinclk|[Hinrst|[]]]]].
      + destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hininput)
          as (xinp & ainp & Hxinp & Hfindinp).
        assert (xlocal = xinp) by (eapply Hinj; eauto).
        subst xinp.
        repeat rewrite map_app in Hndvars.
        eapply (NoDup_app_In xlocal
                  (map fst (n.(n_in)))
                  (map fst (n.(n_vars)) ++ map fst (n.(n_out)))) in Hndvars.
        2:{ now apply in_map with (f := fst) in Hxinp. }
        apply Hndvars.
        apply in_or_app. left. now apply in_map with (f := fst) in Hxlocal.
      + destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hinoutput)
          as (xout & aout & Hxout & Hfindout).
        assert (xlocal = xout) by (eapply Hinj; eauto).
        subst xout.
        repeat rewrite map_app in Hndvars.
        eapply NoDup_app_r in Hndvars.
        eapply (NoDup_app_In xlocal
                  (map fst (n.(n_vars)))
                  (map fst (n.(n_out)))) in Hndvars.
        2:{ now apply in_map with (f := fst) in Hxlocal. }
        apply Hndvars.
        now apply in_map with (f := fst) in Hxout.
      + subst ty.
        assert (xlocal = clk_id) by (eapply Hinj; eauto).
        subst xlocal.
        eapply (node_var_not_sec_gensym n clk_id iclk).
        * rewrite map_app. apply in_or_app. right.
          rewrite map_app. apply in_or_app. left.
          now apply in_map with (f := fst) in Hxlocal.
        * exact Hclkid.
      + subst ty.
        assert (xlocal = rst_id) by (eapply Hinj; eauto).
        subst xlocal.
        eapply (node_var_not_sec_gensym n rst_id irst).
        * rewrite map_app. apply in_or_app. right.
          rewrite map_app. apply in_or_app. left.
          now apply in_map with (f := fst) in Hxlocal.
        * exact Hrstid.
  Qed.

  Definition generated_node_simplify_ready_global
    (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
    generated_node_simplify_ready env aux_names.

  Corollary generated_node_simplify_ready_global_from_env:
    forall all_nodes env aux_names,
      generate_node_env all_nodes = OK (env, aux_names) ->
      generated_node_simplify_ready_global env aux_names.
  Proof.
    intros all_nodes env aux_names Henvgen.
    exact (generated_node_simplify_ready_from_generated_env _ _ _ Henvgen).
  Qed.

  Corollary generate_all_source_signatures_scoped:
    forall all_nodes env aux_names G,
      Clo.wc_global all_nodes ->
      generate_node_env all_nodes = OK (env, aux_names) ->
      SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G ->
      secglobal_scoped G.
  Proof.
    intros all_nodes env aux_names G Hwc Henvgen Hgen.
    eapply SECNLUSTYPING.generate_all_signatures_scoped; eauto.
    eapply NAMEGEN.generate_node_env_injective; eauto.
  Qed.
End SECNLUSTYPINGCORRECTNESS.

Module SecNLusTypingCorrectness
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Ord   : NLORDERED Ids Op CESyn SynNL)
  (Import Mem   : MEMORIES Ids Op CESyn SynNL)
  (Import IsD   : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo   : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo)
  <: SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

Include SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

End SecNLusTypingCorrectness.
