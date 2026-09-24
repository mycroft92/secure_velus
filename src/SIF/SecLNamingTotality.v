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

  (** * No key of a node's environment is one of its anonymous streams

      This is the composition the call case needs, and the last step of the
      argument that replaced what would otherwise have been a syntactic side
      condition on programs.

      A key of the environment is, by [generate_local_env_for_lnode_domain],
      either one of the two auxiliary names or a declared variable.  An
      auxiliary name is a [sec] gensym, and [n_good] puts every anonymous
      stream among the atoms and the node's own prefixes, which
      [gensym_prefs] excludes [sec] from.  A declared variable is kept apart
      from the anonymous streams by the node record's own [n_nodup].

      So a nested call's named output -- which lives in [anon_in_eqs] -- is
      never in the environment, and [assign_clk_type] cannot have succeeded
      on a clock naming it. *)

  Lemma anon_stream_not_sec :
    forall (n : node) w i,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      InMembers w (anon_in_eqs n.(n_eqs)) ->
      w <> Ids.gensym Ids.sec i.
  Proof.
    intros n w i Hsub Hin.
    destruct n.(n_good) as [Hgood _].
    rewrite Forall_forall in Hgood.
    apply atom_or_gensym_not_sec_gensym.
    apply AtomOrGensym_mono with (p := n.(n_prefixes)); [exact Hsub|].
    apply Hgood. rewrite !map_app. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right.
    now apply fst_InMembers.
  Qed.

  Lemma declared_not_anon :
    forall (n : node) w,
      In w (List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars))) ->
      ~ InMembers w (anon_in_eqs n.(n_eqs)).
  Proof.
    intros n w Hin.
    apply (NoDupMembers_app_InMembers w
             (n.(n_in) ++ n.(n_vars) ++ n.(n_out))
             (anon_in_eqs n.(n_eqs))).
    - rewrite <- !app_assoc. exact n.(n_nodup).
    - apply fst_InMembers.
      eapply Permutation_in; [apply Permutation_sym, lnode_keys_perm|exact Hin].
  Qed.

  Theorem env_key_not_anon :
    forall (n : node) st le aux st' w b,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      generate_local_env_for_lnode n st = OK ((le, aux), st') ->
      Env.find w le = Some b ->
      ~ InMembers w (anon_in_eqs n.(n_eqs)).
  Proof.
    intros n st le aux st' w b Hsub Hgen Hf.
    (** what the two auxiliary names are *)
    assert (aux.(nclk) = Ids.gensym Ids.sec st
            /\ aux.(nrst) = Ids.gensym Ids.sec (Pos.succ st)) as (Hclk & Hrst).
    { unfold generate_local_env_for_lnode in Hgen.
      apply name_bind_inv in Hgen as (c & s1 & Hc & Hgen).
      apply name_bind_inv in Hgen as (r & s2 & Hr & Hgen).
      apply name_bind_inv in Hgen as (e1 & s3 & He1 & Hgen).
      apply name_bind_inv in Hgen as (i1 & s4 & Hi1 & Hret).
      unfold NMret in Hret. inversion Hret; subst le aux st'.
      unfold fresh_ident_gen in Hc, Hr.
      inversion Hc; subst c s1. inversion Hr; subst r s2.
      simpl. split; reflexivity. }
    destruct (generate_local_env_for_lnode_domain n st le aux st' w b Hgen Hf)
      as [Hw|[Hw|Hw]].
    - rewrite Hclk in Hw. intro Hanon.
      exact (anon_stream_not_sec n w st Hsub Hanon Hw).
    - rewrite Hrst in Hw. intro Hanon.
      exact (anon_stream_not_sec n w (Pos.succ st) Hsub Hanon Hw).
    - exact (declared_not_anon n w Hw).
  Qed.

  (** * And so: a call argument's fresh streams are never environment keys

      [anon_in] of a call is the fresh streams of its arguments, so anything
      an argument introduces -- in particular the named output of a *nested*
      call -- reaches [anon_in_eqs], which the previous theorem keeps out of
      the environment.

      This is what the call case uses.  Clocking makes the actual at another
      input's clock position a *named* stream; of the Lustre forms only
      [Evar] and [Eapp] may be named; and if it were an [Eapp] its name
      would be one of these, so [assign_clk_type] could not have succeeded
      on the clock naming it.  The actual is therefore an [Evar], whose
      security type is exactly the name the clock mentions -- which is what
      the augmentation step needs. *)

  Lemma fresh_in_arg_in_anon_in :
    forall f es er anns e w a,
      In e es ->
      In (w, a) (fresh_in e) ->
      In (w, a) (anon_in (Eapp f es er anns)).
  Proof.
    intros f es er anns e w a He Hw.
    assert (In (w, a) (fresh_ins es)) as Hins.
    { unfold fresh_ins. apply in_concat.
      exists (fresh_in e). split; [exact Hw|exact (in_map fresh_in es e He)]. }
    destruct er as [r|]; simpl; [apply in_or_app; now left|exact Hins].
  Qed.

  Lemma anon_in_exp_in_eqs :
    forall (eqs : list equation) eq e w a,
      In eq eqs -> In e (snd eq) -> In (w, a) (anon_in e) ->
      InMembers w (anon_in_eqs eqs).
  Proof.
    intros eqs eq e w a Heq He Hw.
    apply In_InMembers with (b := a).
    unfold anon_in_eqs. apply in_concat.
    exists (anon_in_eq eq). split; [|exact (in_map anon_in_eq eqs eq Heq)].
    unfold anon_in_eq, anon_ins. apply in_concat.
    exists (anon_in e). split; [exact Hw|exact (in_map anon_in (snd eq) e He)].
  Qed.

  Theorem call_arg_fresh_not_env_key :
    forall (n : node) st le aux st' eq f es er anns e w a,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      generate_local_env_for_lnode n st = OK ((le, aux), st') ->
      In eq n.(n_eqs) ->
      In (Eapp f es er anns) (snd eq) ->
      In e es ->
      In (w, a) (fresh_in e) ->
      forall b, Env.find w le <> Some b.
  Proof.
    intros n st le aux st' eq f es er anns e w a Hsub Hgen Heq Hcall He Hw b Hf.
    apply (env_key_not_anon n st le aux st' w b Hsub Hgen Hf).
    apply (anon_in_exp_in_eqs n.(n_eqs) eq (Eapp f es er anns) w a);
      [exact Heq|exact Hcall|].
    exact (fresh_in_arg_in_anon_in f es er anns e w a He Hw).
  Qed.

  (** A named nested call is one such stream, by the definition of
      [fresh_in]. *)
  Lemma nested_call_name_fresh :
    forall g gs gr ganns w a,
      In (w, a) (anon_streams ganns) ->
      In (w, a) (fresh_in (Eapp g gs gr ganns)).
  Proof.
    intros g gs gr ganns w a Hw.
    destruct gr as [r|]; simpl.
    - apply in_or_app. right. apply in_or_app. now right.
    - apply in_or_app. now right.
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
