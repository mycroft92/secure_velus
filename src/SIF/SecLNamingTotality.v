(** Totality and coverage for the *Lustre* naming pass.

    [SecNamingTotality.v] discharges the naming hypothesis for the NLustre
    pass.  Every Lustre-side theorem is conditioned on a
    [generate_lnode_scoped_env ns = OK (envs, aux_names)] in the same way,
    and that hypothesis has no discharge yet: without one the Lustre entry
    point is conditioned on something that has never been shown to happen.

    The two passes are structurally the same -- both allocate one fresh
    security name per auxiliary and per declared variable, from
    [Env.empty], refusing duplicates -- so the arguments mirror
    [SecNamingTotality.v] and reuse its generic parts.  What differs is the
    node record: a Lustre node's [n_nodup] and [n_good] also range over
    [anon_in_eqs], and its [n_prefixes] is a field rather than the fixed
    prefix set, so the two bridges below are where the Lustre spelling is
    paid for. *)

From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNamingTotality.
From Velus Require Import SIF.SecLNameInterface.

From compcert Require Import common.Errors.

Module Type SECLNAMINGTOTALITY
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import LSyn    : LSYNTAX  Ids Op)
  (CESyn          : CESYNTAX     Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Mem            : MEMORIES Ids Op CESyn NLSyn)
  (IsD            : ISDEFINED Ids Op CESyn NLSyn Mem)
  (Ord            : NLORDERED Ids Op CESyn NLSyn)
  (Import NAMEGEN : NAMEGEN  Ids Op CESyn NLSyn)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECLNG  : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (Import SECNT   : SECNAMINGTOTALITY Ids Op CESyn NLSyn Mem IsD Ord NAMEGEN)
  (LOrd           : LORDERED Ids Op LSyn).

  Import NAMEMONADNotations.

  (** * Two bridges from the Lustre node record

      A Lustre node carries its own prefix set, and its [n_nodup] and
      [n_good] range over [anon_in_eqs] as well as the declared variables.
      These two lemmas pay for both differences; everything after them is
      the NLustre argument unchanged. *)

  Lemma AtomOrGensym_mono :
    forall p q x, PS.Subset p q -> AtomOrGensym p x -> AtomOrGensym q x.
  Proof.
    intros p q x Hsub [Hat|(pre & Hin & Hex)]; [now left|].
    right. exists pre. split; [apply Hsub; exact Hin|exact Hex].
  Qed.

  Lemma lnode_var_not_sec :
    forall (n : node) x i,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      In x (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros n x i Hsub Hin.
    destruct n.(n_good) as [Hgood _].
    rewrite Forall_forall in Hgood.
    apply atom_or_gensym_not_sec_gensym.
    apply AtomOrGensym_mono with (p := n.(n_prefixes)); [exact Hsub|].
    apply Hgood. rewrite !map_app. rewrite !app_assoc.
    apply in_or_app. left.
    rewrite !map_app in Hin. rewrite !app_assoc in Hin. exact Hin.
  Qed.

  Lemma lnode_var_not_sec' :
    forall (n : node) x i,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      In x (List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))) ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros n x i Hsub Hin.
    apply (lnode_var_not_sec n x i Hsub).
    rewrite !map_app in Hin |- *.
    apply in_app_or in Hin as [Hin|Hin]; [now apply in_or_app; left|].
    apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; right;
      apply in_or_app; [now right|now left].
  Qed.

  Lemma lnode_declared_NoDup :
    forall (n : node),
      NoDup (List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))).
  Proof.
    intro n.
    assert (NoDupMembers (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) as Hnd.
    { pose proof n.(n_nodup) as H.
      rewrite !app_assoc in H.
      apply NoDupMembers_app_l in H.
      rewrite <- !app_assoc in H. exact H. }
    apply fst_NoDupMembers in Hnd.
    eapply Permutation_NoDup; [|exact Hnd].
    rewrite !map_app.
    apply Permutation_app_head, Permutation_app_comm.
  Qed.

  (** * The key list of one Lustre node is duplicate-free *)

  Lemma lnode_local_keys_NoDup :
    forall (n : node) st,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      NoDup ([Ids.gensym Ids.sec st; Ids.gensym Ids.sec (Pos.succ st)]
               ++ List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))).
  Proof.
    intros n st Hsub. simpl.
    constructor; [|constructor].
    - intros [Heq|Hin].
      + apply gensym_injective in Heq as [_ Hcnt].
        exact (Pos.succ_discr st (eq_sym Hcnt)).
      + eapply lnode_var_not_sec'; [exact Hsub|exact Hin|reflexivity].
    - intro Hin. eapply lnode_var_not_sec'; [exact Hsub|exact Hin|reflexivity].
    - apply lnode_declared_NoDup.
  Qed.

  (** * The instance keys of one Lustre node are duplicate-free

      [gather_linst_eq] names a call by the first variable its equation
      defines, so the instance keys are a sublist of the defined variables,
      which [n_defd] and [n_nodup] make duplicate-free. *)

  Lemma gather_linst_eq_in_fst :
    forall eq x,
      In x (List.map fst (gather_linst_eq eq)) -> In x (fst eq).
  Proof.
    intros (ys & fs) x Hin. simpl fst.
    destruct ys as [|y ys]; [simpl in Hin; contradiction|].
    destruct fs as [|f [|f2 fs2]].
    - simpl in Hin. contradiction.
    - destruct f; simpl in Hin; try contradiction.
      destruct Hin as [Hin|[]]. subst y. now left.
    - destruct f; simpl in Hin; contradiction.
  Qed.

  Lemma gather_linsts_in_vars_defined :
    forall eqs x,
      In x (List.map fst (gather_linsts eqs)) -> In x (vars_defined eqs).
  Proof.
    induction eqs as [|eq eqs IH]; intros x Hin; [inversion Hin|].
    unfold gather_linsts in Hin. simpl in Hin. rewrite map_app in Hin.
    unfold vars_defined. simpl. apply in_or_app.
    apply in_app_or in Hin as [Hin|Hin].
    - left. exact (gather_linst_eq_in_fst eq x Hin).
    - right. exact (IH x Hin).
  Qed.

  Lemma gather_linst_eq_shape :
    forall eq, gather_linst_eq eq = [] \/ exists p, gather_linst_eq eq = [p].
  Proof.
    intros (ys & fs). simpl.
    destruct ys as [|y ys]; [now left|].
    destruct fs as [|f [|f2 fs2]].
    - now left.
    - destruct f; try (now left). right. eexists. reflexivity.
    - destruct f; now left.
  Qed.

  Lemma gather_linsts_NoDup_of_vars_defined :
    forall eqs,
      NoDup (vars_defined eqs) ->
      NoDup (List.map fst (gather_linsts eqs)).
  Proof.
    induction eqs as [|eq eqs IH]; intro Hnd; [constructor|].
    unfold vars_defined in Hnd. simpl in Hnd.
    assert (NoDup (vars_defined eqs)) as Hndr
        by (unfold vars_defined; eapply NoDup_app_r; exact Hnd).
    unfold gather_linsts. simpl. rewrite map_app.
    apply NoDup_app'.
    - destruct (gather_linst_eq_shape eq) as [He|(pr & He)];
        rewrite He; simpl; repeat constructor. intros [].
    - exact (IH Hndr).
    - apply Forall_forall. intros z Hz Hin.
      apply (NoDup_app_In z (fst eq) (vars_defined eqs) Hnd).
      + exact (gather_linst_eq_in_fst eq z Hz).
      + exact (gather_linsts_in_vars_defined eqs z Hin).
  Qed.

  Lemma lnode_gather_linsts_NoDup :
    forall (n : node), NoDup (List.map fst (gather_linsts n.(n_eqs))).
  Proof.
    intro n. apply gather_linsts_NoDup_of_vars_defined.
    eapply Permutation_NoDup; [apply Permutation_sym, n.(n_defd)|].
    pose proof n.(n_nodup) as H.
    rewrite !app_assoc in H. apply NoDupMembers_app_l in H.
    rewrite <- !app_assoc in H.
    apply fst_NoDupMembers in H.
    rewrite map_app in H.
    eapply NoDup_app_r; exact H.
  Qed.

  Lemma lnode_keys_perm :
    forall (n : node),
      Permutation
        (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
        (List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))).
  Proof.
    intro n. rewrite !map_app.
    apply Permutation_app_head, Permutation_app_comm.
  Qed.

  (** * The Lustre naming pass succeeds on every node

      Both allocation lists are duplicate-free and the environment it fills
      starts empty, so neither [fresh_insert] nor [fresh_inst_insert] can
      refuse. *)

  Theorem generate_local_env_for_lnode_ok :
    forall (n : node) st,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      exists env rec st',
        generate_local_env_for_lnode n st = OK ((env, rec), st').
  Proof.
    intros n st Hsub.
    destruct (fresh_map_list_ok
                ([Ids.gensym Ids.sec st; Ids.gensym Ids.sec (Pos.succ st)]
                   ++ List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
                (Env.empty ident) (Pos.succ (Pos.succ st)))
      as (env' & st1 & Henv).
    { apply lnode_local_keys_NoDup. exact Hsub. }
    { intros k _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    destruct (fresh_inst_map_list_ok
                (List.map fst (gather_linsts n.(n_eqs)))
                (Env.empty ident) st1)
      as (ienv & st2 & Hienv).
    { apply lnode_gather_linsts_NoDup. }
    { intros k _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    do 3 eexists.
    unfold generate_local_env_for_lnode.
    eapply NMbind_ok; [reflexivity|].
    eapply NMbind_ok; [reflexivity|].
    eapply NMbind_ok; [exact Henv|].
    eapply NMbind_ok; [exact Hienv|reflexivity].
  Qed.

  (** * And covers what the generators look up *)

  Lemma generate_local_env_for_lnode_binds :
    forall (n : node) st env rec st',
      generate_local_env_for_lnode n st = OK ((env, rec), st') ->
      forall x,
        In x (rec.(nclk) :: rec.(nrst)
                :: List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
        exists ty, Env.find x env = Some ty.
  Proof.
    intros n st env rec st' Hgen x Hin.
    unfold generate_local_env_for_lnode in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Henv & Hgen).
    eapply name_bind_inv in Hgen as (ienv & st4 & Hienv & Hret).
    unfold NMret in Hret. inversion Hret; subst env rec st'.
    simpl in Hin.
    eapply fresh_map_list_binds; [exact Henv|].
    simpl. destruct Hin as [Hk|[Hk|Hk]]; auto.
    right; right.
    eapply Permutation_in; [apply lnode_keys_perm|exact Hk].
  Qed.

  Corollary generate_local_env_for_lnode_covers :
    forall (n : node) st env rec st',
      generate_local_env_for_lnode n st = OK ((env, rec), st') ->
      (exists ty, Env.find rec.(nclk) env = Some ty)
      /\ (exists ty, Env.find rec.(nrst) env = Some ty)
      /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
      /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
      /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys).
  Proof.
    intros n st env rec st' Hgen.
    pose proof (generate_local_env_for_lnode_binds n st env rec st' Hgen)
      as Hbind.
    assert (Hvars : forall x,
               In x (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
               exists ty, Env.find x env = Some ty)
      by (intros x Hx; apply Hbind; right; right; exact Hx).
    repeat rewrite map_app in Hvars.
    repeat split.
    - apply Hbind. now left.
    - apply Hbind. right. now left.
    - apply get_mappings_from_node_ok.
      intros x Hx. apply Hvars, in_or_app. now left.
    - apply get_mappings_from_node_ok.
      intros x Hx. apply Hvars, in_or_app. right. apply in_or_app. now left.
    - apply get_mappings_from_node_ok.
      intros x Hx. apply Hvars, in_or_app. right. apply in_or_app. now right.
  Qed.

  (** * The prefix hypothesis is satisfied, not merely assumed

      An elaborated node carries [PS.singleton elab]; [unnest_node] adds
      [norm1] and [normfby_node] adds [norm2].  All three sit inside
      [gensym_prefs], so the hypothesis above holds at every phase and the
      totality result is not vacuous. *)

  Lemma In_of_list_gensym_prefs :
    forall x, List.In x gensym_prefs -> PS.In x (PSP.of_list gensym_prefs).
  Proof.
    intros x Hin. apply PSP.of_list_1, SetoidList.InA_alt.
    exists x. split; [reflexivity|exact Hin].
  Qed.

  Lemma singleton_elab_subset :
    PS.Subset (PS.singleton Ids.elab) (PSP.of_list gensym_prefs).
  Proof.
    intros x Hin. apply PS.singleton_spec in Hin. subst x.
    apply In_of_list_gensym_prefs. unfold gensym_prefs. now left.
  Qed.

  Lemma add_prefix_subset :
    forall pre p,
      List.In pre gensym_prefs ->
      PS.Subset p (PSP.of_list gensym_prefs) ->
      PS.Subset (PS.add pre p) (PSP.of_list gensym_prefs).
  Proof.
    intros pre p Hpre Hsub x Hin.
    apply PS.add_spec in Hin as [Heq|Hin];
      [subst x; now apply In_of_list_gensym_prefs|now apply Hsub].
  Qed.

  Corollary unnested_prefixes_subset :
    forall p,
      PS.Subset p (PSP.of_list gensym_prefs) ->
      PS.Subset (PS.add Ids.norm1 p) (PSP.of_list gensym_prefs).
  Proof.
    intros p Hsub. apply add_prefix_subset; [|exact Hsub].
    unfold gensym_prefs. right. now left.
  Qed.

  Corollary normalized_prefixes_subset :
    forall p,
      PS.Subset p (PSP.of_list gensym_prefs) ->
      PS.Subset (PS.add Ids.norm2 p) (PSP.of_list gensym_prefs).
  Proof.
    intros p Hsub. apply add_prefix_subset; [|exact Hsub].
    unfold gensym_prefs. right. right. now left.
  Qed.

  (** * The pass succeeds on a whole program

      Node names are distinct, so no node's environment is inserted twice;
      and each node's own environment exists by the theorem above. *)

  Lemma lOrdered_nodes_NoDup_names :
    forall G, LOrd.Ordered_nodes G -> NoDup (List.map n_name G).
  Proof.
    induction 1 as [|nd nds Hord IH Hcalls Hdist]; simpl; constructor.
    - intro Hin. apply in_map_iff in Hin as (nd' & Heq & Hin').
      rewrite Forall_forall in Hdist.
      exact (Hdist nd' Hin' (@Coq.Init.Logic.eq_sym _ _ _ Heq)).
    - exact IH.
  Qed.

  Theorem generate_lnode_scoped_env'_ok :
    forall ns envs acc st,
      NoDup (List.map n_name ns) ->
      Forall (fun n => PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs)) ns ->
      (forall n, In n ns -> ~ Env.In n.(n_name) envs) ->
      exists envs' aux st',
        generate_lnode_scoped_env' ns envs acc st = OK ((envs', aux), st').
  Proof.
    induction ns as [|n ns IH]; intros envs acc st Hnd Hpre Hfresh.
    - simpl. unfold NMret. eauto.
    - simpl in Hnd. inversion Hnd as [|x xs Hnotin Hnd']; subst x xs.
      inversion Hpre as [|n0 ns0 Hsub Hpre']; subst n0 ns0.
      destruct (generate_local_env_for_lnode_ok n st Hsub)
        as (env & rec & st1 & Hlocal).
      assert (Hins : fresh_insert_node_env envs n.(n_name) env st1
                     = OK (Env.add n.(n_name) env envs, st1)).
      { unfold fresh_insert_node_env.
        destruct (Env.mem n.(n_name) envs) eqn:Hmem.
        - exfalso.
          apply (Hfresh n (or_introl (@Coq.Init.Logic.eq_refl _ n))).
          now apply Env.mem_2.
        - unfold insert_node_env, NMret. reflexivity. }
      destruct (IH (Env.add n.(n_name) env envs) (rec :: acc) st1 Hnd' Hpre')
        as (envs' & aux & st' & Hrec).
      { intros n' Hin' Hinenv.
        assert (Hne : n'.(n_name) <> n.(n_name)).
        { intro Heq. apply Hnotin. rewrite <- Heq. now apply in_map. }
        apply (Hfresh n' (or_intror Hin')).
        apply Env.Props.P.F.add_in_iff in Hinenv as [Heq|Hinenv];
          [contradiction (Hne (@Coq.Init.Logic.eq_sym _ _ _ Heq))|exact Hinenv]. }
      exists envs', aux, st'.
      cbn [generate_lnode_scoped_env'].
      eapply NMbind2_ok; [exact Hlocal|].
      eapply NMbind_ok; [exact Hins|].
      eapply NMbind2_ok; [exact Hrec|reflexivity].
  Qed.

  Theorem generate_lnode_scoped_env_ok :
    forall ns,
      NoDup (List.map n_name ns) ->
      Forall (fun n => PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs)) ns ->
      exists envs aux, generate_lnode_scoped_env ns = OK (envs, aux).
  Proof.
    intros ns Hnd Hpre.
    unfold generate_lnode_scoped_env.
    destruct (generate_lnode_scoped_env'_ok
                ns (Env.empty _) [] init_state Hnd Hpre)
      as (envs & aux & st' & Hgen).
    { intros n _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    rewrite Hgen. eauto.
  Qed.

  (** The form the Lustre entry point can use: its hypotheses are already
      there, [Ordered_nodes] for the names and the elaborated prefix set for
      the rest. *)
  Corollary generate_lnode_scoped_env_ok_from_ordered :
    forall ns,
      LOrd.Ordered_nodes ns ->
      Forall (fun n => PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs)) ns ->
      exists envs aux, generate_lnode_scoped_env ns = OK (envs, aux).
  Proof.
    intros ns Hord Hpre.
    apply generate_lnode_scoped_env_ok;
      [apply lOrdered_nodes_NoDup_names, Hord|exact Hpre].
  Qed.

End SECLNAMINGTOTALITY.

Module SecLNamingTotality
  (Ids     : IDS)
  (Op      : OPERATORS)
  (OpAux   : OPERATORS_AUX Op)
  (LSyn    : LSYNTAX  Ids Op)
  (CESyn   : CESYNTAX     Op)
  (NLSyn   : NLSYNTAX Ids Op CESyn)
  (Mem     : MEMORIES Ids Op CESyn NLSyn)
  (IsD     : ISDEFINED Ids Op CESyn NLSyn Mem)
  (Ord     : NLORDERED Ids Op CESyn NLSyn)
  (NAMEGEN : NAMEGEN  Ids Op CESyn NLSyn)
  (TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (SECLNG  : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (SECNT   : SECNAMINGTOTALITY Ids Op CESyn NLSyn Mem IsD Ord NAMEGEN)
  (LOrd    : LORDERED Ids Op LSyn)
  <: SECLNAMINGTOTALITY Ids Op OpAux LSyn CESyn NLSyn Mem IsD Ord NAMEGEN TR
       SECLNG SECNT LOrd.
  Include SECLNAMINGTOTALITY Ids Op OpAux LSyn CESyn NLSyn Mem IsD Ord NAMEGEN
            TR SECLNG SECNT LOrd.
End SecLNamingTotality.
