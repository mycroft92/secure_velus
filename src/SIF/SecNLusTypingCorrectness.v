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
From Coq Require Import Sorting.Permutation.
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
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo).

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

  Lemma local_node_scope_sec_range:
    forall n st env rec st'
           clk_id rst_id clk_type rst_type inp out locals ty,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
      exists m, ty = Ids.gensym Ids.sec m.
  Proof.
    intros n st env rec st'
           clk_id rst_id clk_type rst_type inp out locals ty
           Hgen Hclk Hrst Hinp Hout Hlocals Hin.
    repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin) as (x & a & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin) as (x & a & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin) as (x & a & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
    - subst. eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
    - subst. eapply NAMEGEN.generate_local_env_for_node_sec_range; eauto.
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

  (** Source-local simplify replay side conditions.

      This is the node-scoped counterpart of
      [generated_node_simplify_ready_from_generated_env].  Once one node-local
      security env has been generated, the raw NLustre constraints produced for
      that node are:

      - well formed, by the same structural typing argument as before; and
      - safe to replay through [simplify_complete], because eliminated locals
        stay outside the visible interface scope.

      The translation proof uses this theorem when it reasons about one
      generated caller node against previously accumulated callee signatures
      under the node-scoped naming discipline. *)
  Theorem generated_node_simplify_ready_from_local_env:
    forall G1 n nsig env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
      Env.find rec.(nclk) env = Some clk_type ->
      Env.find rec.(nrst) env = Some rst_type ->
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
  Proof.
    intros G1 n nsig env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n
           Hlocal Hnsig Hclk Hrst Hinp Hout Hlocals Hraw Hnsigdef.
    split.
    - eapply SECNLUSTYPING.generate_node_eqns_constraints_wf; eauto.
      eapply NAMEGEN.generate_local_env_for_node_injective; eauto.
    - intros ty Hinlocal Hinsig.
      subst nsig.
      unfold signature_scope in Hinsig.
      repeat rewrite in_app_iff in Hinsig.
      destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hinlocal)
        as (xlocal & alocal & Hxlocal & Hfindlocal).
      pose proof (NAMEGEN.generate_local_env_for_node_injective _ _ _ _ _ Hlocal)
        as Hinj.
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
        2:{
          now apply in_map with (f := fst) in Hxinp.
        }
        apply Hndvars.
        apply in_or_app. left.
        now apply in_map with (f := fst) in Hxlocal.
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
        assert (xlocal = rec.(nclk)) by (eapply Hinj; eauto).
        subst xlocal.
        pose proof (NAMEGEN.generate_local_env_for_node_aux_sec_names
                      n st env rec st' Hlocal) as [Hclkid _].
        eapply (node_var_not_sec_gensym n rec.(nclk) st).
        * rewrite map_app. apply in_or_app. right.
          rewrite map_app. apply in_or_app. left.
          now apply in_map with (f := fst) in Hxlocal.
        * exact Hclkid.
      + subst ty.
        assert (xlocal = rec.(nrst)) by (eapply Hinj; eauto).
        subst xlocal.
        pose proof (NAMEGEN.generate_local_env_for_node_aux_sec_names
                      n st env rec st' Hlocal) as [_ Hrstid].
        eapply (node_var_not_sec_gensym n rec.(nrst) (Pos.succ st)).
        * rewrite map_app. apply in_or_app. right.
          rewrite map_app. apply in_or_app. left.
          now apply in_map with (f := fst) in Hxlocal.
        * exact Hrstid.
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

  Lemma subAll_rhs_in_local:
    forall cns d st rhs,
      In rhs (map snd (subAll cns d st)) ->
      In rhs (map snd cns).
  Proof.
    induction cns as [|(lhs, rhs0) cns IH]; intros d st rhs Hin; simpl in *.
    - contradiction.
    - destruct rhs0 as [|d0 rhs0'].
      + right. eapply IH; eauto.
      + destruct rhs0' as [|r rhs0'].
        * destruct (ident_eqb d0 d) eqn:Hd0.
          -- right. eapply IH; eauto.
          -- simpl in Hin. destruct Hin as [Heq|Hin].
             ++ subst rhs. left. reflexivity.
             ++ right. eapply IH; eauto.
        * right. eapply IH; eauto.
  Qed.

  Lemma subAll_preserves_other_rhs_local:
    forall cns d st d0,
      d0 <> d ->
      In (d0 :: nil) (map snd cns) ->
      In (d0 :: nil) (map snd (subAll cns d st)).
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d st d0 Hneq Hin; simpl in *.
    - contradiction.
    - destruct rhs as [|r rhs'].
      + destruct Hin as [Heq|Hin].
        * discriminate Heq.
        * apply IH; auto.
      + destruct rhs' as [|r' rhs''].
        * simpl in Hin.
          destruct Hin as [Heq|Hin].
          -- inversion Heq; subst r.
             destruct (ident_eqb d0 d) eqn:Hd.
             ++ apply ident_eqb_eq in Hd. contradiction.
             ++ simpl. left. reflexivity.
          -- destruct (ident_eqb r d) eqn:Hrd.
             ++ apply IH; auto.
             ++ simpl. right. apply IH; auto.
        * destruct Hin as [Heq|Hin].
          -- discriminate Heq.
          -- apply IH; auto.
  Qed.

  Lemma simplify_rhs_in:
    forall cns ds rhs,
      In rhs (map snd (SymTypes.simplify cns ds)) ->
      In rhs (map snd cns).
  Proof.
    intros cns ds.
    revert cns.
    induction ds as [|d ds IH]; intros cs rhs Hin; simpl in *.
    - exact Hin.
    - destruct (findST cs d) as [st|] eqn:Hfind.
      + specialize (IH (subAll cs d st) rhs Hin).
        eapply subAll_rhs_in_local. exact IH.
      + eapply (IH cs rhs). exact Hin.
  Qed.

  Lemma simplify_preserves_other_rhs:
    forall cns ds d0,
      (forall d, In d ds -> d0 <> d) ->
      In (d0 :: nil) (map snd cns) ->
      In (d0 :: nil) (map snd (SymTypes.simplify cns ds)).
  Proof.
    intros cns ds.
    revert cns.
    induction ds as [|d ds IH]; intros cs d0 Hneq Hin; simpl.
    - exact Hin.
    - destruct (findST cs d) as [st|] eqn:Hfind.
      + eapply (IH (subAll cs d st) d0).
        * intros d' Hin'. apply Hneq. now right.
        * eapply subAll_preserves_other_rhs_local; eauto.
          apply Hneq. now left.
      + eapply (IH cs d0); eauto.
        intros d' Hin'. apply Hneq. now right.
  Qed.

  Lemma get_mappings_In_here_local:
    forall xs env tys ty,
      get_mappings xs env = Some tys ->
      In ty tys ->
      exists x, In x xs /\ Env.find x env = Some ty.
  Proof.
    induction xs as [|x xs IH]; intros env tys ty Hmap Hin.
    - simpl in Hmap. inversion Hmap; subst. inversion Hin.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Htail; try discriminate.
      inversion Hmap; subst tys.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst ty. exists x. split; [left; reflexivity|exact Hfind].
      + destruct (IH _ _ _ Htail Hin) as (x' & Hinx' & Hfind').
        exists x'. split; [right; exact Hinx'|exact Hfind'].
  Qed.

  Lemma subAll_nodup_local:
    forall cns d st,
      NoDup (map snd cns) ->
      NoDup (map snd (subAll cns d st)).
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d st Hnd; simpl.
    - constructor.
    - apply NoDup_cons_iff in Hnd as [Hnin Hnd].
      destruct rhs as [|r rhs'].
      + exact (IH _ _ Hnd).
      + destruct rhs' as [|r' rhs''].
        * destruct (ident_eqb r d) eqn:Hr.
          -- exact (IH _ _ Hnd).
          -- apply NoDup_cons_iff. split.
             ++ intro Hin.
                apply Hnin.
                eapply subAll_rhs_in_local.
                exact Hin.
             ++ exact (IH _ _ Hnd).
        * exact (IH _ _ Hnd).
  Qed.

  Lemma subAll_singleton_rhs_local:
    forall cns d st,
      Forall (fun '(_, rhs) => length rhs = 1) cns ->
      Forall (fun '(_, rhs) => length rhs = 1) (subAll cns d st).
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d st Hlen; simpl.
    - constructor.
    - inversion Hlen as [|[lhs0 rhs0] cns0 Hhd Htl]; subst lhs0 rhs0 cns0.
      destruct rhs as [|r rhs'].
      + discriminate Hhd.
      + destruct rhs' as [|r' rhs''].
        * destruct (ident_eqb r d) eqn:Hr.
          -- exact (IH _ _ Htl).
          -- constructor.
             ++ simpl. reflexivity.
             ++ exact (IH _ _ Htl).
        * discriminate Hhd.
  Qed.

  Lemma simplify_nodup_local:
    forall cns ds,
      NoDup (map snd cns) ->
      NoDup (map snd (SymTypes.simplify cns ds)).
  Proof.
    intros cns ds.
    revert cns.
    induction ds as [|d ds IH]; intros cns Hnd; simpl.
    - exact Hnd.
    - destruct (findST cns d) as [st|] eqn:Hfind.
      + apply IH. eapply subAll_nodup_local. exact Hnd.
      + apply IH. exact Hnd.
  Qed.

  Lemma simplify_singleton_rhs_local:
    forall cns ds,
      Forall (fun '(_, rhs) => length rhs = 1) cns ->
      Forall (fun '(_, rhs) => length rhs = 1) (SymTypes.simplify cns ds).
  Proof.
    intros cns ds.
    revert cns.
    induction ds as [|d ds IH]; intros cns Hlen; simpl.
    - exact Hlen.
    - destruct (findST cns d) as [st|] eqn:Hfind.
      + apply IH. eapply subAll_singleton_rhs_local. exact Hlen.
      + apply IH. exact Hlen.
  Qed.

  Lemma get_mappings_perm:
    forall xs ys env txs tys,
      NoDup xs ->
      Permutation xs ys ->
      NAMEGEN.env_injective env ->
      get_mappings xs env = Some txs ->
      get_mappings ys env = Some tys ->
      Permutation txs tys.
  Proof.
    intros xs ys env txs tys Hnd Hperm Hinj Hxs Hys.
    apply NoDup_Permutation.
    - eapply SECNLUSTYPING.get_mappings_nodup with (xs := xs) (tys := txs); eauto.
    - eapply SECNLUSTYPING.get_mappings_nodup with (xs := ys) (tys := tys); eauto.
      eapply Permutation_NoDup; eauto.
    - intros ty; split; intro Hin.
      + destruct (get_mappings_In_here_local _ _ _ _ Hxs Hin) as (x & Hinx & Hfind).
        assert (Hiny : In x ys).
        { eapply Permutation_in; eauto. }
        destruct (get_mappings_in _ _ _ _ Hiny Hys) as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. exact Hin'.
      + destruct (get_mappings_In_here_local _ _ _ _ Hys Hin) as (x & Hinx & Hfind).
        assert (Hiny : In x xs).
        { eapply Permutation_in; [symmetry; eauto|exact Hinx]. }
        destruct (get_mappings_in _ _ _ _ Hiny Hxs) as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. exact Hin'.
  Qed.

  Lemma generate_node_sig_inv_local:
    forall G n env aux_names sig,
      SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
      exists clk_id rst_id clk_type rst_type inp out locals nconst st_n,
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
        /\ Env.find clk_id env = Some clk_type
        /\ Env.find rst_id env = Some rst_type
        /\ get_mappings_from_node n.(n_in) env = Some inp
        /\ get_mappings_from_node n.(n_out) env = Some out
        /\ get_mappings_from_node n.(n_vars) env = Some locals
        /\ generate_eqns_constraints G env clk_type rst_type n.(n_eqs) init_state = OK (nconst, st_n)
        /\ sig = {| s_name := n.(n_name);
                    s_in := inp;
                    s_out := out;
                    s_reset := rst_type;
                    s_clk := clk_type;
                    s_constraints := SymTypes.simplify nconst locals |}.
  Proof.
    intros G n env aux_names sig Hsig.
    unfold SECNLUSTYPING.generate_node_sig in Hsig.
    lazymatch type of Hsig with
    | context [match ?m with | OK _ => _ | Error _ => _ end = _] =>
        remember m as gen_res eqn:Hgen
    end.
    destruct gen_res as [[packed st_res]|]; try discriminate.
    destruct packed as [packed env0].
    destruct packed as [packed packed_constraints].
    destruct packed as [packed packed_clk_type].
    destruct packed as [packed packed_rst_type].
    destruct packed as [packed packed_out].
    destruct packed as [name packed_inp].
    simpl in Hsig.
    inversion Hsig; clear Hsig; subst.
    symmetry in Hgen.
    eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
    eapply sec_bind_inv in Hgen as (clk_type & st_clk & Hclk & Hgen).
    eapply sec_bind_inv in Hgen as (rst_type & st_rst & Hrst & Hgen).
    eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
    eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
    eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
    eapply sec_bind_inv in Hgen as (nconst & st_n & Hnconst & Hret).
    unfold option_to_sec in Haux.
    destruct (get_node_aux (n.(n_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
    inversion Haux; subst clk_id0 rst_id0 st_aux.
    unfold option_to_sec in Hclk.
    destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
    inversion Hclk; subst clk_type0 st_clk.
    unfold option_to_sec in Hrst.
    destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
    inversion Hrst; subst rst_type0 st_rst.
    unfold option_to_sec in Hinp.
    destruct (get_mappings_from_node (n.(n_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
    inversion Hinp; subst inp0 st_inp.
    unfold option_to_sec in Hout.
    destruct (get_mappings_from_node (n.(n_out)) env) as [out0|] eqn:Hout0; try discriminate.
    inversion Hout; subst out0 st_out.
    unfold option_to_sec in Hlocals.
    destruct (get_mappings_from_node (n.(n_vars)) env) as [locals0|] eqn:Hlocals0; try discriminate.
    inversion Hlocals; subst locals0 st_locals.
    unfold ret in Hret. inversion Hret; subst.
    exists clk_id, rst_id, packed_clk_type, packed_rst_type, packed_inp, packed_out, locals, nconst, st_res.
    repeat split; eauto.
  Qed.

  (** Generated source signatures are structurally good.

      Beyond scopedness, later call-preservation arguments need the stronger
      fact that a generated NLustre signature keeps exactly one visible
      defining constraint per output after simplifying away locals.  This is
      the source-side structural invariant behind the final call bridge. *)
  Theorem generate_node_sig_good_from_local_env:
    forall G1 P n env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst)) ->
      secglobal_scoped G1 ->
      wc_node P n ->
      Env.find rec.(nclk) env = Some clk_type ->
      Env.find rec.(nrst) env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
      signature_good
        {| s_name := n.(n_name);
           s_in := inp;
           s_out := out;
           s_reset := rst_type;
           s_clk := clk_type;
           s_constraints := SymTypes.simplify raw locals |}.
  Proof.
    intros G1 P n env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n
           Hlocal Hauxmatch Hglobsc Hwc Hclk0 Hrst0 Hinp0 Hout0 Hlocals0 Hraw.
    assert (Hsig :
              SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}).
    {
      unfold SECNLUSTYPING.generate_node_sig.
      unfold bind, bind2, option_to_sec, ret.
      rewrite Hauxmatch. simpl.
      rewrite Hclk0. simpl.
      rewrite Hrst0. simpl.
      rewrite Hinp0. simpl.
      rewrite Hout0. simpl.
      rewrite Hlocals0. simpl.
      rewrite Hraw. simpl.
      reflexivity.
    }
    assert (Hinj : SECNLUSTYPING.env_injective env).
    { eapply NAMEGEN.generate_local_env_for_node_injective; eauto. }
    pose proof
      (SECNLUSTYPING.generate_node_sig_scoped
         G1 P n env aux_names
         {| s_name := n.(n_name);
            s_in := inp;
            s_out := out;
            s_reset := rst_type;
            s_clk := clk_type;
            s_constraints := SymTypes.simplify raw locals |}
         Hglobsc Hinj Hwc Hsig)
      as Hsigscoped.
    pose proof
      (generated_node_simplify_ready_from_local_env
         G1 n
         {| s_name := n.(n_name);
            s_in := inp;
            s_out := out;
            s_reset := rst_type;
            s_clk := clk_type;
            s_constraints := SymTypes.simplify raw locals |}
         env rec aux_names st st'
         clk_type rst_type inp out locals raw st_n
         Hlocal Hsig Hclk0 Hrst0 Hinp0 Hout0 Hlocals0 Hraw eq_refl)
      as Hready.
    destruct Hready as [Hwfraw Hlocalsdisj].
    assert (Hexshape :
              exists tys,
                get_mappings (vars_defined n.(n_eqs)) env = Some tys /\
                map snd raw = map (fun ty => ty :: nil) tys /\
                wf_constraints raw).
    {
      eapply SECNLUSTYPING.generate_eqns_constraints_shape
        with (eqs := n.(n_eqs)) (cns := raw) (st := init_state) (st' := st_n).
      - exact Hinj.
      - apply NoDup_var_defined_n_eqs.
      - exact Hraw.
    }
    destruct Hexshape as (tys & Hmapdefs & Hsndraw & _).
    assert (Hmapvarsout :
              get_mappings (map fst (n.(n_vars) ++ n.(n_out))) env = Some (locals ++ out)).
    {
      rewrite map_app.
      eapply get_mappings_app.
      - eapply get_mappings_from_node_eq; exact Hlocals0.
      - eapply get_mappings_from_node_eq; exact Hout0.
    }
    assert (Hnddefs : NoDup (vars_defined n.(n_eqs))).
    { apply NoDup_var_defined_n_eqs. }
    assert (Hpermtys : Permutation tys (locals ++ out)).
    {
      eapply get_mappings_perm
        with (xs := vars_defined n.(n_eqs))
             (ys := map fst (n.(n_vars) ++ n.(n_out)))
             (env := env)
             (txs := tys)
             (tys := locals ++ out).
      - exact Hnddefs.
      - exact n.(n_defd).
      - exact Hinj.
      - exact Hmapdefs.
      - exact Hmapvarsout.
    }
    assert (Hpermraw : Permutation (map snd raw) (map (fun ty => ty :: nil) (locals ++ out))).
    {
      rewrite Hsndraw.
      eapply Permutation_map.
      exact Hpermtys.
    }
    assert (Hwf_simpl : wf_constraints (SymTypes.simplify raw locals)).
    {
      split.
      - eapply simplify_nodup_local.
        exact (proj1 Hwfraw).
      - eapply simplify_singleton_rhs_local.
        exact (proj2 Hwfraw).
    }
    unfold signature_good; cbn.
    split.
    - simpl. exact Hwf_simpl.
    - apply NoDup_Permutation.
      + exact (proj1 Hwf_simpl).
      + assert (Hndall : NoDup (locals ++ out)).
        {
          eapply NoDup_map_inv with (f := fun ty => ty :: nil).
          eapply Permutation_NoDup; [exact Hpermraw|].
          exact (proj1 Hwfraw).
        }
        apply nodup_singleton_map.
        eapply NoDup_app_r. exact Hndall.
      + intros rhs; split; intro Hin.
        * pose proof (simplify_rhs_in _ _ _ Hin) as Hinraw.
          eapply Permutation_in in Hinraw; [|exact Hpermraw].
          apply in_map_iff in Hinraw as (ty & Hrhs & Hinall).
          subst rhs.
          apply in_app_iff in Hinall.
          destruct Hinall as [Hinlocal|Hinout].
          -- exfalso.
             assert (Hfindrhs : exists stc, findST (SymTypes.simplify raw locals) ty = Some stc).
             { eapply findST_of_rhs_in. exact Hin. }
             destruct Hfindrhs as (stc & Hfindrhs).
             apply find_correct in Hfindrhs.
             unfold signature_scoped, constraints_scoped in Hsigscoped.
             rewrite Forall_forall in Hsigscoped.
             specialize (Hsigscoped _ Hfindrhs).
             assert (Hinscope : In ty (signature_scope
                               {| s_name := n.(n_name);
                                  s_in := inp;
                                  s_out := out;
                                  s_reset := rst_type;
                                  s_clk := clk_type;
                                  s_constraints := SymTypes.simplify raw locals |})).
             { eapply constraint_scoped_rhs with (lhs := stc) (rhs := ty :: nil); eauto.
               simpl. now left. }
             exact (Hlocalsdisj ty Hinlocal Hinscope).
          -- apply in_map_iff. exists ty. split; [reflexivity|exact Hinout].
        * apply in_map_iff in Hin as (ty & Hrhs & Hinout).
          subst rhs.
          assert (Hinsigscope : In ty (signature_scope
                                {| s_name := n.(n_name);
                                   s_in := inp;
                                   s_out := out;
                                   s_reset := rst_type;
                                   s_clk := clk_type;
                                   s_constraints := SymTypes.simplify raw locals |})).
          { unfold signature_scope.
            apply in_or_app. right.
            apply in_or_app. left.
            exact Hinout. }
          assert (Hinraw : In (ty :: nil) (map snd raw)).
          {
            eapply Permutation_in; [symmetry; exact Hpermraw|].
            apply in_map_iff. exists ty. split; [reflexivity|].
            apply in_or_app. right. exact Hinout.
          }
          eapply simplify_preserves_other_rhs.
          -- intros d Hd Htyeq.
             subst d.
             exact (Hlocalsdisj ty Hd Hinsigscope).
          -- exact Hinraw.
  Qed.

  (** Node-scoped source signature generation.

      The node-scoped naming pivot changes only how the local security env is
      recovered; once that env is projected out of the outer node-indexed
      table, the underlying NLustre typing proof is the same as for the older
      flat shared env.  This wrapper is the source-side correctness bridge used
      later by the translation preservation proof. *)
  Theorem generate_node_sig_scoped_env_scoped:
    forall all_nodes G P n envs aux_names sig,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      secglobal_scoped G ->
      wc_node P n ->
      find_node n.(n_name) all_nodes = Some n ->
      SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
      signature_scoped sig.
  Proof.
    intros all_nodes G P n envs aux_names sig
           Henvsgen Hscoped Hwc Hfind Hsig.
    unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsig.
    destruct (find_node_env n.(n_name) envs) as [env|] eqn:Hfindenv; try discriminate.
    eapply SECNLUSTYPING.generate_node_sig_scoped; eauto.
    pose proof (find_node_In _ _ _ Hfind) as [_ Hin].
    apply in_split in Hin as (prefix & suffix & Hall).
    subst all_nodes.
    edestruct NAMEGEN.generate_node_scoped_env_find_current
      as (local_env & rec & st_pref & st_local & Hlocalgen & Hlocalfind); eauto.
    rewrite Hfindenv in Hlocalfind. inversion Hlocalfind; subst local_env.
    eapply NAMEGEN.generate_local_env_for_node_injective; eauto.
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
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo)
  <: SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

Include SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

End SecNLusTypingCorrectness.
