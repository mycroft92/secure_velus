(** Totality and coverage of the security naming pass.

    Every top-level theorem of the three SIF layers is conditioned on a
    successful run of the generators, and all of them share one root
    hypothesis:

      [generate_node_scoped_env ns = OK (envs, aux_names)].

    This file discharges that hypothesis.  The naming pass has exactly
    three failure modes, all of them [Env.mem] guards:

    - [fresh_insert] refuses a variable that is already mapped, so the
      keys of one node -- its clock and reset names together with its
      inputs, locals and outputs -- must be pairwise distinct;
    - [fresh_inst_insert] refuses a repeated instance, so the instance
      names a node's body gathers must be distinct;
    - [fresh_insert_node_env] refuses a repeated node name.

    The first two are properties of a single node and hold for *every*
    node, with no well-formedness hypothesis beyond the ones the [node]
    record already carries: [n_nodup] makes the declared variables
    distinct, [n_defd] and [n_nodup] together make the gathered
    instances distinct, and [n_good] keeps a source variable from ever
    being a [sec] gensym, which is what separates the minted clock and
    reset names from the declared ones.  Only the third needs anything
    of the program, and only that its node names are distinct -- which
    [Ordered_nodes] provides.

    The second half of the file is coverage: the environment the pass
    produces answers every lookup the signature generators make.  Both
    halves are stated so that the consumer never has to unfold the
    naming monad. *)

From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.NameInterface.

From compcert Require Import common.Errors.

Open Scope list_scope.

Module Type SECNAMINGTOTALITY
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import CESyn   : CESYNTAX Op)
  (Import SynNL   : NLSYNTAX Ids Op CESyn)
  (Import Mem     : MEMORIES Ids Op CESyn SynNL)
  (Import IsD     : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import Ord     : NLORDERED Ids Op CESyn SynNL)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL).

  Import NAMEMONADNotations.

  (** ** Forward composition in the naming monad

      [NameInterface.v] provides the inversion lemmas; totality needs
      the other direction, building a successful run out of successful
      steps.  Using these instead of [simpl] keeps the proofs below from
      depending on how far reduction unfolds the monad. *)

  Lemma NMbind_ok:
    forall {A B: Type} (x: Name A) (f: A -> Name B) st a st1 b st2,
      x st = OK (a, st1) ->
      f a st1 = OK (b, st2) ->
      NMbind x f st = OK (b, st2).
  Proof.
    intros A B x f st a st1 b st2 Hx Hf.
    unfold NMbind. rewrite Hx. exact Hf.
  Qed.

  Lemma NMbind2_ok:
    forall {A1 A2 B: Type} (x: Name (A1 * A2)) (f: A1 -> A2 -> Name B)
           st a1 a2 st1 b st2,
      x st = OK ((a1, a2), st1) ->
      f a1 a2 st1 = OK (b, st2) ->
      NMbind2 x f st = OK (b, st2).
  Proof.
    intros A1 A2 B x f st a1 a2 st1 b st2 Hx Hf.
    unfold NMbind2. rewrite Hx. exact Hf.
  Qed.

  (** ** The shape of one insertion

      Reading the two insertion steps back as plain [Env.add] is what
      lets the rest of the file reason about keys without ever unfolding
      the monad again. *)

  Lemma fresh_insert_shape:
    forall env k st env' st',
      fresh_insert env k st = OK (env', st') ->
      env' = Env.add k (Ids.gensym Ids.sec st) env /\ st' = Pos.succ st.
  Proof.
    intros env k st env' st' Hins.
    unfold fresh_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hins as (v & stv & Hfresh & Hins).
    eapply name_bind_inv in Hins as (e & ste & Hadd & Hret).
    unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v stv.
    unfold insert_env, NMret in Hadd. inversion Hadd; subst e ste.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    split; reflexivity.
  Qed.

  Lemma fresh_inst_insert_shape:
    forall env k st env' st',
      fresh_inst_insert env k st = OK (env', st') ->
      env' = Env.add k (Ids.gensym Ids.sec_reset st) env /\ st' = Pos.succ st.
  Proof.
    intros env k st env' st' Hins.
    unfold fresh_inst_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply name_bind_inv in Hins as (v & stv & Hfresh & Hins).
    eapply name_bind_inv in Hins as (e & ste & Hadd & Hret).
    unfold fresh_inst_ident_gen in Hfresh. inversion Hfresh; subst v stv.
    unfold insert_env, NMret in Hadd. inversion Hadd; subst e ste.
    unfold NMret in Hret. inversion Hret; subst env' st'.
    split; reflexivity.
  Qed.

  (** ** Insertion succeeds on a fresh key *)

  Lemma fresh_insert_ok:
    forall env k st,
      ~ Env.In k env ->
      fresh_insert env k st
      = OK (Env.add k (Ids.gensym Ids.sec st) env, Pos.succ st).
  Proof.
    intros env k st Hnotin.
    unfold fresh_insert.
    destruct (Env.mem k env) eqn:Hmem.
    - exfalso. apply Hnotin. now apply Env.mem_2.
    - reflexivity.
  Qed.

  Lemma fresh_inst_insert_ok:
    forall env k st,
      ~ Env.In k env ->
      fresh_inst_insert env k st
      = OK (Env.add k (Ids.gensym Ids.sec_reset st) env, Pos.succ st).
  Proof.
    intros env k st Hnotin.
    unfold fresh_inst_insert.
    destruct (Env.mem k env) eqn:Hmem.
    - exfalso. apply Hnotin. now apply Env.mem_2.
    - reflexivity.
  Qed.

  (** ** Mapping a whole key list succeeds

      The only hypotheses are that the keys are pairwise distinct and
      none of them is already mapped: [Env.add] of a key different from
      [k] cannot make [k] present. *)

  Lemma fresh_map_list_ok:
    forall ks env st,
      NoDup ks ->
      (forall k, In k ks -> ~ Env.In k env) ->
      exists env' st', fresh_map_list ks env st = OK (env', st').
  Proof.
    induction ks as [|k ks IH]; intros env st Hnd Hfresh.
    - simpl. unfold NMret. eauto.
    - inversion Hnd as [|k' ks' Hknotin Hnd']; subst k' ks'.
      destruct (IH (Env.add k (Ids.gensym Ids.sec st) env) (Pos.succ st) Hnd')
        as (env' & st' & Hrec).
      { intros k' Hin' Hinenv.
        assert (Hne : k' <> k) by (intro; subst; contradiction).
        apply (Hfresh k' (or_intror Hin')).
        apply Env.Props.P.F.add_in_iff in Hinenv as [Heq|Hinenv];
          [contradiction (Hne (eq_sym Heq))|exact Hinenv]. }
      exists env', st'.
      cbn [fresh_map_list].
      eapply NMbind_ok;
        [exact (fresh_insert_ok env k st (Hfresh k (or_introl eq_refl)))|].
      eapply NMbind_ok; [exact Hrec|reflexivity].
  Qed.

  Lemma fresh_inst_map_list_ok:
    forall ks env st,
      NoDup ks ->
      (forall k, In k ks -> ~ Env.In k env) ->
      exists env' st', fresh_inst_map_list ks env st = OK (env', st').
  Proof.
    induction ks as [|k ks IH]; intros env st Hnd Hfresh.
    - simpl. unfold NMret. eauto.
    - inversion Hnd as [|k' ks' Hknotin Hnd']; subst k' ks'.
      destruct (IH (Env.add k (Ids.gensym Ids.sec_reset st) env) (Pos.succ st) Hnd')
        as (env' & st' & Hrec).
      { intros k' Hin' Hinenv.
        assert (Hne : k' <> k) by (intro; subst; contradiction).
        apply (Hfresh k' (or_intror Hin')).
        apply Env.Props.P.F.add_in_iff in Hinenv as [Heq|Hinenv];
          [contradiction (Hne (eq_sym Heq))|exact Hinenv]. }
      exists env', st'.
      cbn [fresh_inst_map_list].
      eapply NMbind_ok;
        [exact (fresh_inst_insert_ok env k st (Hfresh k (or_introl eq_refl)))|].
      eapply NMbind_ok; [exact Hrec|reflexivity].
  Qed.

  (** ** Every key mapped is afterwards bound

      The counterpart of [fresh_inst_map_list_binds], which
      [NameInterface.v] already proves for the instance environment. *)

  Lemma fresh_map_list_binds:
    forall ks env st env' st',
      fresh_map_list ks env st = OK (env', st') ->
      forall x, In x ks -> exists ty, Env.find x env' = Some ty.
  Proof.
    induction ks as [|k ks IH]; intros env st env' st' Hmap x Hin.
    - inversion Hin.
    - simpl in Hmap.
      eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hmap).
      eapply name_bind_inv in Hmap as (env2 & st2 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst env' st'.
      destruct (fresh_insert_shape _ _ _ _ _ Hstep) as [Henv1 Hst1].
      destruct Hin as [Heq|Hin].
      + subst x.
        exists (Ids.gensym Ids.sec st).
        eapply fresh_map_list_preserves_find; [exact Hrec|].
        subst env1. now rewrite Env.gss.
      + eapply IH; eauto.
  Qed.

  (** ** The declared variables of a node are distinct from [sec] names

      A source variable is an atom or a gensym drawn from the
      elaboration prefixes, and [sec] is none of those.  This is the
      general form; [SecNLusTypingCorrectness.node_var_not_sec_gensym]
      is the same argument specialised to a node, and
      [SecStcTypingCorrectness.atom_or_gensym_not_sec] to a system. *)

  Lemma atom_or_gensym_not_sec_gensym:
    forall x i,
      AtomOrGensym (PSP.of_list gensym_prefs) x ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros x i Hgood Heq.
    destruct Hgood as [Hat|Hex].
    - rewrite Heq in Hat. eapply gensym_not_atom; eauto.
    - unfold PS.Exists in Hex.
      destruct Hex as (pre & Hinpre & m & Hm).
      rewrite Heq in Hm. symmetry in Hm.
      apply gensym_injective in Hm as [Hpre _]. subst pre.
      apply PSP.of_list_1 in Hinpre.
      apply SetoidList.InA_alt in Hinpre as (pre' & Heq' & Hinpre).
      subst pre'.
      exact (Ids.sec_not_in_gensym_prefs Hinpre).
  Qed.

  Lemma node_var_not_sec:
    forall n x i,
      In x (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      x <> Ids.gensym Ids.sec i.
  Proof.
    intros n x i Hin.
    destruct n.(n_good) as [Hgood _].
    rewrite Forall_forall in Hgood.
    apply atom_or_gensym_not_sec_gensym, Hgood, Hin.
  Qed.

  (** ** The key list of one node is duplicate-free

      Two minted names differ because [gensym] is injective in its
      counter and the counter advances; neither is a declared variable
      by the previous lemma; and the declared variables are distinct by
      [n_nodup]. *)

  Lemma node_local_keys_NoDup:
    forall n st,
      NoDup ([Ids.gensym Ids.sec st; Ids.gensym Ids.sec (Pos.succ st)]
               ++ map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
  Proof.
    intros n st. simpl.
    assert (Hvars : NoDup (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
      by (apply fst_NoDupMembers, n.(n_nodup)).
    constructor; [|constructor].
    - intros [Heq|Hin].
      + apply gensym_injective in Heq as [_ Hcnt].
        exact (Pos.succ_discr st (eq_sym Hcnt)).
      + eapply node_var_not_sec; [exact Hin|reflexivity].
    - intro Hin. eapply node_var_not_sec; [exact Hin|reflexivity].
    - exact Hvars.
  Qed.

  (** ** The gathered instances of a node are distinct

      [gather_insts] names an instance by the first variable its call
      defines, so distinct calls get distinct names exactly because a
      body defines each variable once. *)

  Lemma gather_insts_NoDupMembers:
    forall eqs,
      NoDup (vars_defined eqs) ->
      NoDupMembers (gather_insts eqs).
  Proof.
    induction eqs as [|eq eqs IH]; intro Hnd.
    - simpl. constructor.
    - assert (Hnd' : NoDup (vars_defined eqs)).
      { simpl in Hnd. eapply NoDup_app_r; exact Hnd. }
      specialize (IH Hnd').
      assert (Hhead : NoDupMembers (gather_inst_eq eq)).
      { destruct eq as [| xs ck f es r |]; simpl; try constructor.
        destruct xs; repeat constructor. inversion 1. }
      simpl. apply NoDupMembers_app; [exact Hhead|exact IH|].
      intros x Hinx Hinxs.
      destruct (NoDup_In_gather_insts eq eqs x Hnd) as [[_ Hno]|[Hno _]].
      + simpl. apply InMembers_app. now left.
      + apply Hno. exact Hinxs.
      + apply Hno. exact Hinx.
  Qed.

  Lemma node_vars_defined_NoDup:
    forall n, NoDup (vars_defined n.(n_eqs)).
  Proof.
    intro n.
    eapply Permutation_NoDup; [apply Permutation_sym, n.(n_defd)|].
    apply fst_NoDupMembers.
    pose proof n.(n_nodup) as Hnd.
    now apply NoDupMembers_app_r in Hnd.
  Qed.

  Lemma node_gather_insts_NoDup:
    forall n, NoDup (map fst (gather_insts n.(n_eqs))).
  Proof.
    intro n.
    apply fst_NoDupMembers, gather_insts_NoDupMembers, node_vars_defined_NoDup.
  Qed.

  (** ** One node's environment is always produced

      No hypothesis at all: everything the two [fresh_*_map_list] calls
      need is already in the [node] record. *)

  Theorem generate_local_env_for_node_ok:
    forall n st,
      exists env rec st',
        generate_local_env_for_node n st = OK ((env, rec), st').
  Proof.
    intros n st.
    destruct (fresh_map_list_ok
                ([Ids.gensym Ids.sec st; Ids.gensym Ids.sec (Pos.succ st)]
                   ++ map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                (Env.empty ident) (Pos.succ (Pos.succ st)))
      as (env' & st1 & Henv).
    { apply node_local_keys_NoDup. }
    { intros k _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    destruct (fresh_inst_map_list_ok
                (map fst (gather_insts n.(n_eqs))) (Env.empty ident) st1)
      as (ienv & st2 & Hienv).
    { apply node_gather_insts_NoDup. }
    { intros k _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    do 3 eexists.
    unfold generate_local_env_for_node.
    eapply NMbind_ok; [reflexivity|].
    eapply NMbind_ok; [reflexivity|].
    eapply NMbind_ok; [exact Henv|].
    eapply NMbind_ok; [exact Hienv|reflexivity].
  Qed.

  (** ** The whole program

      The one thing the program has to supply is that its node names are
      distinct; [fresh_insert_node_env] is the only guard left. *)

  Theorem generate_node_scoped_env'_ok:
    forall ns envs acc st,
      NoDup (map n_name ns) ->
      (forall n, In n ns -> ~ Env.In n.(n_name) envs) ->
      exists envs' aux st',
        generate_node_scoped_env' ns envs acc st = OK ((envs', aux), st').
  Proof.
    induction ns as [|n ns IH]; intros envs acc st Hnd Hfresh.
    - simpl. unfold NMret. eauto.
    - simpl in Hnd. inversion Hnd as [|x xs Hnotin Hnd']; subst x xs.
      destruct (generate_local_env_for_node_ok n st)
        as (env & rec & st1 & Hlocal).
      assert (Hins : fresh_insert_node_env envs n.(n_name) env st1
                     = OK (Env.add n.(n_name) env envs, st1)).
      { unfold fresh_insert_node_env.
        destruct (Env.mem n.(n_name) envs) eqn:Hmem.
        - exfalso. apply (Hfresh n (or_introl eq_refl)). now apply Env.mem_2.
        - unfold insert_node_env, NMret. reflexivity. }
      destruct (IH (Env.add n.(n_name) env envs) (rec :: acc) st1 Hnd')
        as (envs' & aux & st' & Hrec).
      { intros n' Hin' Hinenv.
        assert (Hne : n'.(n_name) <> n.(n_name)).
        { intro Heq. apply Hnotin. rewrite <- Heq. now apply in_map. }
        apply (Hfresh n' (or_intror Hin')).
        apply Env.Props.P.F.add_in_iff in Hinenv as [Heq|Hinenv];
          [contradiction (Hne (eq_sym Heq))|exact Hinenv]. }
      exists envs', aux, st'.
      cbn [generate_node_scoped_env'].
      eapply NMbind2_ok; [exact Hlocal|].
      eapply NMbind_ok; [exact Hins|].
      eapply NMbind2_ok; [exact Hrec|reflexivity].
  Qed.

  (** The public totality statement.  [Ordered_nodes] is the usual
      source of the name-distinctness side condition, and is discharged
      into it just below. *)

  Theorem generate_node_scoped_env_ok:
    forall ns,
      NoDup (map n_name ns) ->
      exists envs aux, generate_node_scoped_env ns = OK (envs, aux).
  Proof.
    intros ns Hnd.
    unfold generate_node_scoped_env.
    destruct (generate_node_scoped_env'_ok ns (Env.empty _) [] init_state Hnd)
      as (envs & aux & st' & Hgen).
    { intros n _ Hin. eapply Env.Props.P.F.empty_in_iff; exact Hin. }
    rewrite Hgen. eauto.
  Qed.

  Lemma Ordered_nodes_NoDup_names:
    forall ns, Ordered_nodes ns -> NoDup (map n_name ns).
  Proof.
    induction ns as [|n ns IH]; intro Hord.
    - constructor.
    - inversion Hord as [|nd nds Hord' _ Hdistinct]; subst nd nds.
      simpl. constructor; [|exact (IH Hord')].
      intro Hin. apply in_map_iff in Hin as (n' & Heq & Hin').
      rewrite Forall_forall in Hdistinct.
      exact (Hdistinct n' Hin' (eq_sym Heq)).
  Qed.

  (** An ordered program always has a naming run. *)

  Corollary generate_node_scoped_env_ok_from_ordered:
    forall ns,
      Ordered_nodes ns ->
      exists envs aux, generate_node_scoped_env ns = OK (envs, aux).
  Proof.
    intros ns Hord.
    apply generate_node_scoped_env_ok, Ordered_nodes_NoDup_names, Hord.
  Qed.

  (** The signature generators are run on [rev ns] (see
      [SecNLusConstraintExport.generate_nlustre_constraint_dump]), so
      that a callee -- which [Ordered_nodes] places after its caller --
      is generated first.  Reversal preserves name distinctness, so the
      naming pass is total there too. *)

  Corollary generate_node_scoped_env_ok_rev:
    forall ns,
      Ordered_nodes ns ->
      exists envs aux, generate_node_scoped_env (rev ns) = OK (envs, aux).
  Proof.
    intros ns Hord.
    apply generate_node_scoped_env_ok.
    rewrite map_rev.
    eapply Permutation_NoDup; [apply Permutation_rev|].
    apply Ordered_nodes_NoDup_names, Hord.
  Qed.

  (** * Coverage

      Totality of the naming pass is only half of what the generators
      need: the environment it produces must also *answer* every lookup
      they make.  For one node those lookups are its clock and reset
      names, its declared variables, and the instances its body gathers
      -- which is exactly the key list the pass inserted. *)

  Lemma get_mappings_from_node_ok:
    forall {A: Type} (xs: list (ident * A)) env,
      (forall x, In x (map fst xs) -> exists ty, Env.find x env = Some ty) ->
      exists tys, get_mappings_from_node xs env = Some tys.
  Proof.
    induction xs as [|[x a] xs IH]; intros env Hall.
    - exists []. reflexivity.
    - destruct (Hall x (or_introl eq_refl)) as (ty & Hx).
      destruct (IH env (fun y Hy => Hall y (or_intror Hy))) as (tys & Htys).
      exists (ty :: tys). simpl. rewrite Hx, Htys. reflexivity.
  Qed.

  (** Every key the pass inserted for a node is bound in the environment
      it returns.  The two aux names are the first two keys of the very
      list [fresh_map_list] walked, so they come out of the same
      lemma as the declared variables. *)

  Lemma generate_local_env_for_node_binds:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      forall x,
        In x (rec.(nclk) :: rec.(nrst)
                :: map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
        exists ty, Env.find x env = Some ty.
  Proof.
    intros n st env rec st' Hgen x Hin.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Henv & Hgen).
    eapply name_bind_inv in Hgen as (ienv & st4 & Hienv & Hret).
    unfold NMret in Hret. inversion Hret; subst env rec st'.
    simpl in Hin.
    eapply fresh_map_list_binds; [exact Henv|].
    exact Hin.
  Qed.

  Lemma generate_local_env_for_node_inst_binds:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      forall i,
        In i (map fst (gather_insts n.(n_eqs))) ->
        exists ty, Env.find i rec.(ninst) = Some ty.
  Proof.
    intros n st env rec st' Hgen i Hin.
    unfold generate_local_env_for_node in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Henv & Hgen).
    eapply name_bind_inv in Hgen as (ienv & st4 & Hienv & Hret).
    unfold NMret in Hret. inversion Hret; subst env rec st'.
    simpl.
    eapply fresh_inst_map_list_binds; [exact Hienv|exact Hin].
  Qed.

  (** The interface lists are read back through [get_mappings_from_node],
      so state the node's coverage in the form its consumers use. *)

  Corollary generate_local_env_for_node_covers:
    forall n st env rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      (exists ty, Env.find rec.(nclk) env = Some ty)
      /\ (exists ty, Env.find rec.(nrst) env = Some ty)
      /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
      /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
      /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys).
  Proof.
    intros n st env rec st' Hgen.
    pose proof (generate_local_env_for_node_binds n st env rec st' Hgen) as Hbind.
    assert (Hvars : forall x,
               In x (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
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

  (** ** The whole run

      For a node of the list, the run's environment and auxiliary table
      both have an entry, and that entry answers every lookup.  The
      [get_node_aux]/[get_node_inst] halves come from the record being
      pushed onto the accumulator at this node's step and carried
      forward unchanged, which the preservation lemmas in
      [NameInterface.v] already establish. *)

  Theorem generate_node_scoped_env_covers_split:
    forall prefix n suffix envs aux,
      generate_node_scoped_env (prefix ++ n :: suffix) = OK (envs, aux) ->
      exists env rec,
        find_node_env n.(n_name) envs = Some env
        /\ get_node_aux n.(n_name) aux = Some (rec.(nclk), rec.(nrst))
        /\ get_node_inst n.(n_name) aux = Some rec.(ninst)
        /\ (exists ty, Env.find rec.(nclk) env = Some ty)
        /\ (exists ty, Env.find rec.(nrst) env = Some ty)
        /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
        /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
        /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys)
        /\ (forall i, In i (map fst (gather_insts n.(n_eqs))) ->
                      exists ty, Env.find i rec.(ninst) = Some ty).
  Proof.
    intros prefix n suffix envs aux Hgen.
    unfold generate_node_scoped_env in Hgen.
    destruct (generate_node_scoped_env' (prefix ++ n :: suffix)
                (Env.empty _) [] init_state)
      as [[[envs' aux'] st']|] eqn:Hrun; try discriminate.
    inversion Hgen; subst envs aux; clear Hgen.
    eapply generate_node_scoped_env'_split_node in Hrun
      as (envs_pref & aux_pref & st_pref & local_env & rec & st_local
          & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail).
    pose proof (generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hname.
    assert (Hcur : find_node_env n.(n_name) envs_cur = Some local_env)
      by (eapply fresh_insert_node_env_finds_new; exact Hins).
    exists local_env, rec.
    (* the environment entry *)
    assert (Hfind : find_node_env n.(n_name) envs' = Some local_env)
      by (eapply generate_node_scoped_env'_preserves_find; eauto).
    (* this node's record heads the accumulator of the suffix run *)
    assert (Haux0 : get_node_aux n.(n_name) (rec :: aux_pref)
                    = Some (rec.(nclk), rec.(nrst))).
    { unfold get_node_aux. simpl.
      rewrite Hname, ident_eqb_refl. reflexivity. }
    assert (Hinst0 : get_node_inst n.(n_name) (rec :: aux_pref)
                     = Some rec.(ninst)).
    { unfold get_node_inst. simpl.
      rewrite Hname, ident_eqb_refl. reflexivity. }
    destruct (generate_local_env_for_node_covers _ _ _ _ _ Hlocal)
      as (Hclk & Hrst & Hinp & Hvars & Hout).
    repeat split; try assumption.
    - eapply generate_node_scoped_env'_preserves_get_node_aux; eauto.
    - eapply generate_node_scoped_env'_preserves_get_node_inst; eauto.
    - intros i Hi. eapply generate_local_env_for_node_inst_binds; eauto.
  Qed.

  (** The same, indexed by membership rather than by a split. *)

  Corollary generate_node_scoped_env_covers:
    forall ns envs aux n,
      generate_node_scoped_env ns = OK (envs, aux) ->
      In n ns ->
      exists env rec,
        find_node_env n.(n_name) envs = Some env
        /\ get_node_aux n.(n_name) aux = Some (rec.(nclk), rec.(nrst))
        /\ get_node_inst n.(n_name) aux = Some rec.(ninst)
        /\ (exists ty, Env.find rec.(nclk) env = Some ty)
        /\ (exists ty, Env.find rec.(nrst) env = Some ty)
        /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
        /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
        /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys)
        /\ (forall i, In i (map fst (gather_insts n.(n_eqs))) ->
                      exists ty, Env.find i rec.(ninst) = Some ty).
  Proof.
    intros ns envs aux n Hgen Hin.
    apply in_split in Hin as (prefix & suffix & Heq). subst ns.
    eapply generate_node_scoped_env_covers_split; exact Hgen.
  Qed.

  (** ** The root hypothesis, discharged

      An ordered program has a naming run, and that run covers every one
      of its nodes.  This is the statement the three layers' top-level
      theorems were conditioned on. *)

  Theorem naming_run_total_and_covering:
    forall ns,
      Ordered_nodes ns ->
      exists envs aux,
        generate_node_scoped_env ns = OK (envs, aux)
        /\ forall n, In n ns ->
             exists env rec,
               find_node_env n.(n_name) envs = Some env
               /\ get_node_aux n.(n_name) aux = Some (rec.(nclk), rec.(nrst))
               /\ get_node_inst n.(n_name) aux = Some rec.(ninst)
               /\ (exists ty, Env.find rec.(nclk) env = Some ty)
               /\ (exists ty, Env.find rec.(nrst) env = Some ty)
               /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
               /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
               /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys)
               /\ (forall i, In i (map fst (gather_insts n.(n_eqs))) ->
                             exists ty, Env.find i rec.(ninst) = Some ty).
  Proof.
    intros ns Hord.
    destruct (generate_node_scoped_env_ok_from_ordered ns Hord)
      as (envs & aux & Hgen).
    exists envs, aux. split; [exact Hgen|].
    intros n Hin. eapply generate_node_scoped_env_covers; eauto.
  Qed.

  (** And on the list the generators are actually run on. *)

  Corollary naming_run_total_and_covering_rev:
    forall ns,
      Ordered_nodes ns ->
      exists envs aux,
        generate_node_scoped_env (rev ns) = OK (envs, aux)
        /\ forall n, In n ns ->
             exists env rec,
               find_node_env n.(n_name) envs = Some env
               /\ get_node_aux n.(n_name) aux = Some (rec.(nclk), rec.(nrst))
               /\ get_node_inst n.(n_name) aux = Some rec.(ninst)
               /\ (exists ty, Env.find rec.(nclk) env = Some ty)
               /\ (exists ty, Env.find rec.(nrst) env = Some ty)
               /\ (exists tys, get_mappings_from_node n.(n_in) env = Some tys)
               /\ (exists tys, get_mappings_from_node n.(n_vars) env = Some tys)
               /\ (exists tys, get_mappings_from_node n.(n_out) env = Some tys)
               /\ (forall i, In i (map fst (gather_insts n.(n_eqs))) ->
                             exists ty, Env.find i rec.(ninst) = Some ty).
  Proof.
    intros ns Hord.
    destruct (generate_node_scoped_env_ok_rev ns Hord) as (envs & aux & Hgen).
    exists envs, aux. split; [exact Hgen|].
    intros n Hin. eapply generate_node_scoped_env_covers; [exact Hgen|].
    apply in_rev in Hin. exact Hin.
  Qed.

End SECNAMINGTOTALITY.

Module SecNamingTotality
  (Ids     : IDS)
  (Op      : OPERATORS)
  (CESyn   : CESYNTAX Op)
  (SynNL   : NLSYNTAX Ids Op CESyn)
  (Mem     : MEMORIES Ids Op CESyn SynNL)
  (IsD     : ISDEFINED Ids Op CESyn SynNL Mem)
  (Ord     : NLORDERED Ids Op CESyn SynNL)
  (NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  <: SECNAMINGTOTALITY Ids Op CESyn SynNL Mem IsD Ord NAMEGEN.
  Include SECNAMINGTOTALITY Ids Op CESyn SynNL Mem IsD Ord NAMEGEN.
End SecNamingTotality.
