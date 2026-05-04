(* Source-local correctness facts for generated NLustre signatures.

   This file owns the NLustre facts that are needed later by the
   cross-phase translation proof but do not themselves mention STC:
   - naming/range/injectivity consequences of [NameInterface],
   - generated source-signature structural goodness,
   - duplicate-freedom of the visible source interface scope,
   - caller-scope freshness facts for generated source accumulators.

   These theorems are the source-side discharge lemmas for the final
   [Signature_head_consistent] proof in [SecNLusStcTranslation]. *)
From Coq Require Import List.
Import List.ListNotations.
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
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
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
      eapply NAMEGEN.generate_node_env_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin) as (x & a & _ & Hfind).
      eapply NAMEGEN.generate_node_env_sec_range; eauto.
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin) as (x & a & _ & Hfind).
      eapply NAMEGEN.generate_node_env_sec_range; eauto.
    - subst. eapply NAMEGEN.generate_node_env_sec_range; eauto.
    - subst. eapply NAMEGEN.generate_node_env_sec_range; eauto.
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

  (** Source caller-scope freshness for one generated node environment.

      This packages the exact freshness condition used later in the
      translation-preservation head step: once the current node's visible
      source scope has been recovered from the shared naming environment, every
      signature already present in the source accumulator must stay disjoint
      from that caller scope.  It is source-only and belongs in the NLustre
      correctness layer rather than the cross-phase translation proof. *)
  Definition node_scope_fresh_in_env
    (n: node) (env: Env.t ident) (aux_names: list node_aux_names) (G: secglobal) : Prop :=
    forall clk_id rst_id clk_type rst_type inp out locals,
      get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      SIG.secglobal_scope_fresh
        (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) G.

  (** Global wrapper for source caller-scope freshness.

      Later global preservation theorems quantify over the whole NLustre
      program.  This wrapper turns the local node predicate above into the
      program-level invariant that every generated caller node is fresh against
      the current source accumulator. *)
  Definition generated_callers_scope_fresh
    (all_nodes: global) (env: Env.t ident) (aux_names: list node_aux_names)
    (G: secglobal) : Prop :=
    forall n,
      find_node n.(n_name) all_nodes = Some n ->
      node_scope_fresh_in_env n env aux_names G.

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
    - destruct (SymTypes.findST cs d) as [st|] eqn:Hfind.
      + simpl in Hin.
        specialize (IH (SymTypes.subAll cs d st) rhs Hin).
        eapply subAll_rhs_in_local. exact IH.
      + simpl in Hin.
        eapply (IH cs rhs). exact Hin.
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
    - destruct (SymTypes.findST cs d) as [st|] eqn:Hfind.
      + simpl.
        eapply (IH (SymTypes.subAll cs d st) d0).
        * intros d' Hin'. apply Hneq. now right.
        * eapply subAll_preserves_other_rhs_local; eauto.
          apply Hneq. now left.
      + simpl.
        eapply (IH cs d0); eauto.
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
    - destruct (SymTypes.findST cns d) as [st|] eqn:Hfind.
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
    - destruct (SymTypes.findST cns d) as [st|] eqn:Hfind.
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

  (** Public inversion view for generated source signatures.

      This is the source-local generator shape used by later preservation
      proofs.  It is just the reusable exported form of
      [generate_node_sig_inv_local]. *)
  Corollary generate_node_sig_inv:
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
    exact generate_node_sig_inv_local.
  Qed.

  (** Visible-field provenance for generated source signatures.

      Any identifier that appears in the visible scope of a generated source
      signature comes from a concrete key of the generating node: either one
      of its inputs/outputs or one of the node-specific clock/reset keys
      stored in [aux_names].  This is the source-local ingredient later used
      by translation to derive generated call freshness from the naming
      discipline. *)
  Lemma generated_node_sig_scope_key:
    forall G n env aux_names sig ty,
      SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
      In ty (signature_scope sig) ->
      exists clk_id rst_id x,
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
        /\ (In x (map fst n.(n_in))
            \/ In x (map fst n.(n_out))
            \/ x = clk_id
            \/ x = rst_id)
        /\ Env.find x env = Some ty.
  Proof.
    intros G n env aux_names sig ty Hsig Hin.
    edestruct generate_node_sig_inv_local as
        (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
         & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hsigdef); eauto.
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

  (** Generated visible source signatures live in the [sec] namespace. *)
  Lemma generated_node_sig_scope_sec:
    forall all_nodes G n env aux_names sig,
      generate_node_env all_nodes = OK (env, aux_names) ->
      SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
      signature_scope_sec sig.
  Proof.
    intros all_nodes G n env aux_names sig Henvgen Hsig ty Hin.
    destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    eapply NAMEGEN.generate_node_env_sec_range in Hfind; eauto.
  Qed.

  (** Local lower bound for visible source signature identifiers. *)
  Lemma generated_node_sig_scope_lower_bound_from_local_env:
    forall G n env aux_names sig st rec st' ty,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
      In ty (signature_scope sig) ->
      exists m, ty = Ids.gensym Ids.sec m /\ (Pos.succ (Pos.succ st) <= m)%positive.
  Proof.
    intros G n env aux_names sig st rec st' ty Hlocal Hsig Hin.
    destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    eapply NAMEGEN.generate_local_env_for_node_lower_bound in Hfind; eauto.
  Qed.

  (** Local upper bound for visible source signature identifiers. *)
  Lemma generated_node_sig_scope_upper_bound_from_local_env:
    forall G n env aux_names sig st rec st' ty,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
      In ty (signature_scope sig) ->
      exists m, ty = Ids.gensym Ids.sec m /\ (m < st')%positive.
  Proof.
    intros G n env aux_names sig st rec st' ty Hlocal Hsig Hin.
    destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
      as (_ & _ & x & _ & _ & Hfind).
    edestruct (NAMEGEN.generate_local_env_for_node_bounded
                 n st env rec st' Hlocal x ty Hfind)
      as (m & Hm & Hlt).
    exists m. split; assumption.
  Qed.

  Lemma node_scope_lower_bounded_from_local_env:
    forall n st env rec st'
           clk_id rst_id clk_type rst_type inp out locals,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      scope_lower_bounded (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) st.
  Proof.
    intros n st env rec st'
           clk_id rst_id clk_type rst_type inp out locals
           Hlocal Hclk Hrst Hinp Hout Hlocals ty Hin.
    repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
        as (xinp & ainp & _ & Hfindinp).
      edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                   n st env rec st' xinp ty Hlocal Hfindinp)
        as (m & Hm & Hlo).
      exists m. split; auto.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
        as (xout & aout & _ & Hfindout).
      edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                   n st env rec st' xout ty Hlocal Hfindout)
        as (m & Hm & Hlo).
      exists m. split; auto.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin)
        as (xlocal & alocal & _ & Hfindlocal).
      edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                   n st env rec st' xlocal ty Hlocal Hfindlocal)
        as (m & Hm & Hlo).
      exists m. split; auto.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    - subst ty.
      edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                   n st env rec st' clk_id clk_type Hlocal Hclk)
        as (m & Hm & Hlo).
      exists m. split; auto.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    - subst ty.
      edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                   n st env rec st' rst_id rst_type Hlocal Hrst)
        as (m & Hm & Hlo).
      exists m. split; auto.
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
      eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
  Qed.

  (** Source caller-scope freshness from local naming bounds.

      This is the source-side bridge from the node-scoped naming discipline to
      the freshness invariant consumed by the generated translation step.  The
      current caller scope is lower-bounded by the start state of local
      generation, while every already-generated callee signature in the source
      accumulator is upper-bounded by the earlier accumulator state; the
      signature-layer bound lemma then turns those two inequalities into
      disjointness. *)
  Lemma node_scope_fresh_in_env_from_bounds:
    forall n st env aux_names G rec st',
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      SIG.secglobal_scope_bounded_above G st ->
      node_scope_fresh_in_env n env aux_names G.
  Proof.
    intros n st env aux_names G rec st' Hlocal Hbound
           clk_id rst_id clk_type rst_type inp out locals
           Haux Hclk Hrst Hinp Hout Hlocals.
    intros f sig Hfindsig.
    eapply SIG.scope_fresh_from_bounds.
    - eapply node_scope_lower_bounded_from_local_env; eauto.
    - eapply Hbound; eauto.
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
      assert (Hsigshape :
                SECNLUSTYPING.generate_node_sig G1 n env aux_names =
                match
                  bind
                    (generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs))
                    (fun constraints' =>
                       ret
                         (n.(n_name), inp, out, rst_type, clk_type,
                          SymTypes.simplify constraints' locals, env))
                    init_state
                with
                | OK ((name, inp', out', rst_type', clk_type', constraints, _), _) =>
                    OK
                      {| s_name := name;
                         s_in := inp';
                         s_out := out';
                         s_reset := rst_type';
                         s_clk := clk_type';
                         s_constraints := constraints |}
                | Error e => Error e
                end).
      {
        unfold SECNLUSTYPING.generate_node_sig.
        cbn [bind bind2 option_to_sec ret].
        rewrite Hauxmatch. cbn [bind bind2 option_to_sec ret].
        rewrite Hclk0. cbn [bind bind2 option_to_sec ret].
        rewrite Hrst0. cbn [bind bind2 option_to_sec ret].
        rewrite Hinp0. cbn [bind bind2 option_to_sec ret].
        rewrite Hout0. cbn [bind bind2 option_to_sec ret].
        rewrite Hlocals0. cbn [bind bind2 option_to_sec ret].
        reflexivity.
      }
      rewrite Hsigshape.
      unfold bind, ret.
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
         Hlocal Hsig Hclk0 Hrst0 Hinp0 Hout0 Hlocals0 Hraw Logic.eq_refl)
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
             change
               (Forall
                  (constraint_scoped
                     (signature_scope
                        {| s_name := n.(n_name);
                           s_in := inp;
                           s_out := out;
                           s_reset := rst_type;
                           s_clk := clk_type;
                           s_constraints := SymTypes.simplify raw locals |}))
                  (SymTypes.simplify raw locals))
               in Hsigscoped.
             apply Forall_forall with (x := (stc, ty :: nil)) in Hsigscoped.
             2:{ exact Hfindrhs. }
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

  (** Low call outputs force the instantiated reset argument low.

      Relation to the paper:
      reset-aware call instantiation substitutes the caller-provided reset
      type into the callee signature.  Once the stored callee signature is
      known to mention its reset field in every output-defining constraint,
      any low caller-visible output slot of the instantiated call forces the
      instantiated reset argument low as well.  This is the typing-side fact
      later used by the indexed noninterference proof to align reset-control
      prefixes in reset calls. *)
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

  (** Low call outputs force the instantiated clock argument low.

      Relation to the paper:
      reset-aware indexed noninterference also has to keep call clocks aligned
      across the two executions.  Once the stored callee signature is known to
      mention its clock field in every output-defining constraint, any low
      caller-visible output slot of the instantiated call forces the
      instantiated clock argument low as well.  This is the clock-side
      companion of [call_output_low_implies_reset_low]. *)
  Lemma call_output_low_implies_clock_low:
    forall sig inptyp ckty rstty outtyp cns st st'
           dlt t i y v,
      signature_good sig ->
      (forall y lhs,
          findST sig.(s_constraints) y = Some lhs ->
          In sig.(s_clk) lhs) ->
      call_subst_fresh sig inptyp ckty rstty outtyp ->
      NoDup (signature_scope sig) ->
      List.length sig.(s_in) = List.length inptyp ->
      List.length sig.(s_out) = List.length outtyp ->
      generate_constraints sig inptyp ckty rstty outtyp st = OK (cns, st') ->
      listSatisfiable dlt cns ->
      nth_error sig.(s_out) i = Some y ->
      nth_error outtyp i = Some v ->
      dlt v ⊑ t ->
      hm_ext dlt ckty ⊑ t.
  Proof.
    intros sig inptyp ckty rstty outtyp cns st st'
           dlt t i y v
           Hgood Hclklhs Hfresh Hndscope HlenIn HlenOut Hgen Hsat
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
    assert (Hclkin : In sig.(s_clk) lhs).
    { eapply Hclklhs; eauto. }
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
    rewrite <- (inst_valuation_clk_eq
                  dlt sig inptyp ckty rstty outtyp
                  Hfresh Hndscope).
    apply order_trans with
        (y := hm_ext (inst_valuation dlt sig inptyp ckty rstty outtyp) lhs).
    - apply hm_ext_list_in1.
      exact Hclkin.
    - apply order_trans with
        (y := join (inst_valuation dlt sig inptyp ckty rstty outtyp y) bottom).
      + exact Hsat_sig.
      + apply join_least_upper_bound.
        * exact Hlowy.
        * apply bottom_is_bottom.
  Qed.

  (** Generated source signature interfaces are duplicate free.

      The call bridge only updates lattice mappings on the visible
      signature interface.  To show that those updates behave as intended, we
      need the source-side fact that the generated interface variables are
      pairwise distinct.  This comes entirely from the NLustre node-interface
      uniqueness discipline plus injectivity of the node-local naming
      environment. *)
  Theorem generate_node_sig_scope_nodup_from_local_env:
    forall n env rec st st' clk_type rst_type inp out,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      Env.find rec.(nclk) env = Some clk_type ->
      Env.find rec.(nrst) env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      NoDup
        (signature_scope
           {| s_name := n.(n_name);
              s_in := inp;
              s_out := out;
              s_reset := rst_type;
              s_clk := clk_type;
              s_constraints := nil |}).
  Proof.
    intros n env rec st st' clk_type rst_type inp out
           Hlocal Hclk Hrst Hinp Hout.
    unfold signature_scope.
    pose proof (NAMEGEN.generate_local_env_for_node_injective _ _ _ _ _ Hlocal)
      as Hinj.
    pose proof (NAMEGEN.generate_local_env_for_node_aux_sec_names
                  _ _ _ _ _ Hlocal) as [Hclkid Hrstid].
    assert (Hmapio :
              get_mappings (map fst (n.(n_in) ++ n.(n_out))) env = Some (inp ++ out)).
    {
      rewrite map_app.
      eapply get_mappings_app.
      - eapply get_mappings_from_node_eq; exact Hinp.
      - eapply get_mappings_from_node_eq; exact Hout.
    }
    assert (Hmapclk :
              get_mappings [rec.(nclk); rec.(nrst)] env = Some [clk_type; rst_type]).
    {
      simpl. rewrite Hclk, Hrst. reflexivity.
    }
    assert (Hmapall :
              get_mappings
                (map fst (n.(n_in) ++ n.(n_out)) ++ [rec.(nclk); rec.(nrst)]) env =
              Some (inp ++ out ++ [clk_type; rst_type])).
    {
      replace (inp ++ out ++ [clk_type; rst_type])
        with ((inp ++ out) ++ [clk_type; rst_type]) by now rewrite app_assoc.
      eapply get_mappings_app
        with (txs := inp ++ out) (tys := [clk_type; rst_type]); eauto.
    }
    assert (Hndio : NoDup (map fst (n.(n_in) ++ n.(n_out)))).
    {
      rewrite map_app.
      eapply NoDup_app'.
      - pose proof n.(n_nodup) as Hnodup.
        rewrite app_assoc in Hnodup.
        apply NoDupMembers_app_l in Hnodup.
        apply NoDupMembers_app_l in Hnodup.
        now apply fst_NoDupMembers.
      - pose proof n.(n_nodup) as Hnodup.
        rewrite app_assoc in Hnodup.
        apply NoDupMembers_app_r in Hnodup.
        now apply fst_NoDupMembers.
      - rewrite Forall_forall.
        intros x Hinx Hxout.
        pose proof n.(n_nodup) as Hndall.
        apply fst_NoDupMembers in Hndall.
        rewrite !map_app in Hndall.
        rewrite app_assoc in Hndall.
        apply NoDup_app'_iff in Hndall as [_ [_ Hfresh]].
        rewrite Forall_forall in Hfresh.
        eapply Hfresh.
        + apply in_or_app. left. exact Hinx.
        + exact Hxout.
    }
    assert (Hclkneqrst : rec.(nclk) <> rec.(nrst)).
    {
      intro Heq.
      rewrite Hclkid, Hrstid in Heq.
      apply gensym_injective in Heq as [_ Heq].
      pose proof (Pos.lt_succ_diag_r st) as Hlt.
      rewrite <- Heq in Hlt.
      exact (Pos.lt_irrefl _ Hlt).
    }
    assert (Hndkeys :
              NoDup (map fst (n.(n_in) ++ n.(n_out)) ++ [rec.(nclk); rec.(nrst)])).
    {
      eapply NoDup_app'.
      - exact Hndio.
      - repeat constructor.
        + intro Hin.
          simpl in Hin. destruct Hin as [Heq|[]].
          apply Hclkneqrst. symmetry. exact Heq.
        + intro Hin. inversion Hin.
      - rewrite Forall_forall.
        intros x Hinx Hinaux.
        simpl in Hinaux.
        destruct Hinaux as [Heqclk|[Heqrst|[]]].
        + subst x.
          apply in_map_iff in Hinx as (xraw & Hxraw & Hinxraw).
          inversion Hxraw; subst.
          eapply (node_var_not_sec_gensym n rec.(nclk) st).
          * rewrite app_assoc, !map_app.
            apply in_app_iff in Hinxraw.
            apply in_or_app.
            destruct Hinxraw as [Hinin|Hinout].
            -- left. apply in_or_app. left.
               apply in_map with (f := fst) in Hinin. simpl in Hinin.
               rewrite H0 in Hinin. exact Hinin.
            -- right.
               apply in_map with (f := fst) in Hinout. simpl in Hinout.
               rewrite H0 in Hinout. exact Hinout.
          * exact Hclkid.
        + subst x.
          apply in_map_iff in Hinx as (xraw & Hxraw & Hinxraw).
          inversion Hxraw; subst.
          eapply (node_var_not_sec_gensym n rec.(nrst) (Pos.succ st)).
          * rewrite app_assoc, !map_app.
            apply in_app_iff in Hinxraw.
            apply in_or_app.
            destruct Hinxraw as [Hinin|Hinout].
            -- left. apply in_or_app. left.
               apply in_map with (f := fst) in Hinin. simpl in Hinin.
               rewrite H0 in Hinin. exact Hinin.
            -- right.
               apply in_map with (f := fst) in Hinout. simpl in Hinout.
               rewrite H0 in Hinout. exact Hinout.
          * exact Hrstid.
    }
    eapply SECNLUSTYPING.get_mappings_nodup; eauto.
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
      pose proof (NAMEGEN.generate_node_aux_sec_names _ _ _ _ _ _ Henvgen Haux)
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

  Lemma generate_all_source_signatures_scope_sec':
    forall all_nodes nodes acc env aux_names G,
      generate_node_env all_nodes = OK (env, aux_names) ->
      secglobal_scope_sec acc ->
      SECNLUSTYPING.generate_all_signatures' acc nodes env aux_names = OK G ->
      secglobal_scope_sec G.
  Proof.
    intros all_nodes nodes.
    induction nodes as [|n nodes IH]; intros acc env aux_names G Henvgen Hacc Hgen.
    - simpl in Hgen. inversion Hgen; subst. exact Hacc.
    - simpl in Hgen.
      destruct (SECNLUSTYPING.generate_node_sig acc n env aux_names) as [sig|e] eqn:Hsig;
        simpl in Hgen; try discriminate.
      destruct (SECNLUSTYPING.generate_all_signatures' (sig :: acc) nodes env aux_names)
        as [G'|e] eqn:Htl; simpl in Hgen; try discriminate.
      inversion Hgen; subst.
      eapply IH with (acc := sig :: acc) (env := env) (aux_names := aux_names).
      + exact Henvgen.
      + eapply secglobal_scope_sec_cons; eauto.
        eapply generated_node_sig_scope_sec; eauto.
      + exact Htl.
  Qed.

  Corollary generate_all_source_signatures_scope_sec:
    forall all_nodes env aux_names G,
      generate_node_env all_nodes = OK (env, aux_names) ->
      SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G ->
      secglobal_scope_sec G.
  Proof.
    intros all_nodes env aux_names G Henvgen Hgen.
    unfold SECNLUSTYPING.generate_all_signatures in Hgen.
    eapply generate_all_source_signatures_scope_sec'; eauto.
    apply secglobal_scope_sec_nil.
  Qed.

  (** Generated scoped-env source signatures are structurally good.

      Relation to the paper:
      once the source naming pass has fixed the local environment of each
      node, every generated source signature should satisfy the structural
      invariant expected by call instantiation: exactly one visible
      singleton-RHS constraint per output, with well-formed stored
      constraints.  This theorem lifts the local head-node result
      [generate_node_sig_good_from_local_env] through the whole
      scoped-environment signature generation pass. *)
  Theorem generate_all_source_signatures_good_scoped_env':
    forall prefix nodes acc envs aux_names G,
      generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
      Clo.wc_global nodes ->
      secglobal_scoped acc ->
      secglobal_good acc ->
      SECNLUSTYPING.generate_all_signatures_scoped_env' acc nodes envs aux_names = OK G ->
      secglobal_good G.
  Proof.
    intros prefix nodes.
    revert prefix.
    induction nodes as [|n nodes IH];
      intros prefix acc envs aux_names G
             Henvsgen Hwc Hacc_scoped Hacc_good Hgen.
    - simpl in Hgen.
      inversion Hgen; subst G.
      exact Hacc_good.
    - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
      simpl in Hgen.
      destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc n envs aux_names)
        as [sig|e_sig] eqn:Hsig.
      + destruct (SECNLUSTYPING.generate_all_signatures_scoped_env' (sig :: acc) nodes envs aux_names)
          as [G'|e_tl] eqn:Htl.
        * inversion Hgen; subst. clear Hgen.
          assert (Hsig_good : signature_good sig).
          {
        unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsig.
        destruct (find_node_env n.(n_name) envs) as [local_env|] eqn:Hfindenv;
          try discriminate.
        pose proof Henvsgen as Henvsgen_cur.
        unfold generate_node_scoped_env in Henvsgen_cur.
        destruct
          (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nodes) (Env.empty _) [] NAMEGEN.init_state)
          as [[[envs0 aux0] st0]|] eqn:Hrun; try discriminate.
        inversion Henvsgen_cur; subst envs0 aux0. clear Henvsgen_cur.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref & aux_pref & st_pref & local_env' & rec & st_local
              & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
          eauto.
        assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env').
        {
          eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
          eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
        }
        rewrite Hfindenv in Hfindlocal.
        inversion Hfindlocal; subst local_env'. clear Hfindlocal.
        assert (Hrec_name : rec.(nname) = n.(n_name)).
        {
          eapply NAMEGEN.generate_local_env_for_node_name; eauto.
        }
        assert (Haux_cur :
                  get_node_aux n.(n_name) (rec :: aux_pref) =
                  Some (rec.(nclk), rec.(nrst))).
        {
          unfold get_node_aux.
          simpl.
          rewrite <- Hrec_name.
          rewrite ident_eqb_refl.
          reflexivity.
        }
        assert (Haux_match :
                  get_node_aux n.(n_name) aux_names =
                  Some (rec.(nclk), rec.(nrst))).
        {
          assert (Hfindcur :
                    find_node_env n.(n_name) envs_cur = Some local_env).
          {
            eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
          }
          eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux
            with (ns := nodes)
                 (envs := envs_cur)
                 (acc := rec :: aux_pref)
                 (st := st_cur)
                 (envs' := envs)
                 (st' := st0)
                 (clk_id := rec.(nclk))
                 (rst_id := rec.(nrst))
                 (local_env := local_env);
            eauto.
        }
        edestruct generate_node_sig_inv_local
          as (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
              & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef_local);
          eauto.
        rewrite Haux_match in Haux.
        inversion Haux. subst clk_id rst_id. clear Haux.
        rewrite Hsigdef_local.
        exact
          (generate_node_sig_good_from_local_env
             acc nodes n local_env rec aux_names st_pref st_local
             clk_type rst_type inp out locals raw st_n
             Hlocal Haux_match Hacc_scoped Hwc_head
             Hclk Hrst Hinp Hout Hlocals Hraw).
          }
          assert (Henvsgen_tail :
                generate_node_scoped_env ((prefix ++ [n]) ++ nodes) = OK (envs, aux_names)).
          {
        assert (Hprefix_app : ((prefix ++ [n]) ++ nodes) = prefix ++ n :: nodes).
        {
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite Hprefix_app.
        exact Henvsgen.
          }
          assert (Hnext_scoped : secglobal_scoped (sig :: acc)).
          {
        unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsig.
        destruct (find_node_env n.(n_name) envs) as [local_env|] eqn:Hfindenv;
          try discriminate.
        assert (Hinj_local : SECNLUSTYPING.env_injective local_env).
        {
          destruct
            (NAMEGEN.generate_node_scoped_env_find_current
               prefix n nodes envs aux_names Henvsgen)
            as (local_env' & rec' & st_pref' & st_local' & Hlocal' & Hfindlocal').
          rewrite Hfindenv in Hfindlocal'.
          inversion Hfindlocal'. subst local_env'. clear Hfindlocal'.
          eapply NAMEGEN.generate_local_env_for_node_injective; eauto.
        }
        assert (Hsig_scoped : signature_scoped sig).
        {
          exact
            (SECNLUSTYPING.generate_node_sig_scoped
               acc nodes n local_env aux_names sig
               Hacc_scoped Hinj_local Hwc_head Hsig).
        }
        exact (secglobal_scoped_cons sig acc Hsig_scoped Hacc_scoped).
          }
          assert (Hnext_good : secglobal_good (sig :: acc)).
          {
        exact (secglobal_good_cons sig acc Hsig_good Hacc_good).
          }
          exact
            (IH (prefix ++ [n]) (sig :: acc) envs aux_names G
                Henvsgen_tail Hwc_tail Hnext_scoped Hnext_good H0).
        * cbn [SECNLUSTYPING.generate_all_signatures_scoped_env'] in Hgen.
          simpl in Hgen.
          rewrite Htl in Hgen.
          discriminate.
      + cbn [SECNLUSTYPING.generate_all_signatures_scoped_env'] in Hgen.
        simpl in Hgen.
        discriminate.
  Qed.

  Corollary generate_all_source_signatures_good_scoped_env:
    forall all_nodes envs aux_names G,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
      secglobal_good G.
  Proof.
    intros all_nodes envs aux_names G Henvsgen Hwc Hgen.
    eapply generate_all_source_signatures_good_scoped_env'
      with (prefix := []) (acc := []); eauto.
    - apply secglobal_scoped_nil.
    - apply secglobal_good_nil.
  Qed.

  (** Visible generated constraints mention a chosen security identifier.

      This is the syntactic invariant needed by the reset-aware NLustre call
      proof: every visible singleton-RHS constraint stored in a signature (or
      intermediate call block) still carries the chosen identifier on its lhs. *)
  Definition constraints_mention (ty: ident) (cns: list constraint) : Prop :=
    forall lhs y,
      In (lhs, [y]) cns ->
      In ty lhs.

  Lemma in_merge_left:
    forall x a b,
      In x a ->
      In x (a ⊔ b).
  Proof.
    intros x a.
    induction a as [|a0 a IHa]; intros b Hin.
    - contradiction.
    - revert Hin.
      induction b as [|b0 b IHb]; intro Hin.
      + simpl. exact Hin.
      + simpl.
        destruct Hin as [Heq|Hin].
        * subst x.
          destruct (Pos.compare a0 b0) eqn:Hcmp; simpl.
          -- left; reflexivity.
          -- left; reflexivity.
          -- right. apply IHb. left; reflexivity.
        * destruct (Pos.compare a0 b0) eqn:Hcmp; simpl.
          -- right. eapply IHa. exact Hin.
          -- right. eapply IHa. exact Hin.
          -- right. apply IHb. right; exact Hin.
  Qed.

  Lemma in_merge_right:
    forall x a b,
      In x b ->
      In x (a ⊔ b).
  Proof.
    intros x a b Hin.
    rewrite MergeFacts.merge_comm.
    now apply in_merge_left.
  Qed.

  Lemma subST_preserves_other_in:
    forall lhs d st x,
      x <> d ->
      In x lhs ->
      In x (subST lhs d st).
  Proof.
    intros lhs d st x Hneq Hin.
    unfold subST.
    destruct (st_mem d lhs) eqn:Hmem.
    - destruct (st_mem d st) eqn:Hmemst.
      + apply in_merge_left.
        eapply st_remove_preserves_other_in; eauto.
      + apply in_merge_left.
        eapply st_remove_preserves_other_in; eauto.
    - exact Hin.
  Qed.

  Lemma subST_replaces_target_in:
    forall lhs d st x,
      In d lhs ->
      ~ In d st ->
      In x st ->
      In x (subST lhs d st).
  Proof.
    intros lhs d st x Hind Hnotin Hinx.
    unfold subST.
    assert (Hmemd : st_mem d lhs = true).
    { apply my_set_mem_correct. exact Hind. }
    rewrite Hmemd.
    destruct (st_mem d st) eqn:Hmemst.
    - apply my_set_mem_correct in Hmemst.
      contradiction.
    - apply in_merge_right.
      exact Hinx.
  Qed.

  (** Signature-instantiation membership replay.

      The paper's call-instantiation proof tracks how one visible identifier
      survives the symbolic type substitution used when replaying a stored
      signature inside a caller.  The implementation now uses
      [SIG.subst_ident_in_type] rather than the older simplify-specific
      [subST], so the mention-preservation lemmas below need the matching
      membership facts. *)
  Lemma subst_ident_in_type_preserves_other_in:
    forall lhs d st x,
      x <> d ->
      In x lhs ->
      In x (SIG.subst_ident_in_type lhs d st).
  Proof.
    intros lhs d st x Hneq Hin.
    unfold SIG.subst_ident_in_type.
    destruct (SymTypes.my_set_mem d lhs) eqn:Hmem; simpl.
    - change (In x ((SymTypes.st_remove d lhs) ⊔ (SymTypes.st_remove d st))).
      apply in_merge_left.
      eapply st_remove_preserves_other_in; eauto.
    - exact Hin.
  Qed.

  Lemma subst_ident_in_type_replaces_target_in:
    forall lhs d st x,
      In d lhs ->
      ~ In d st ->
      In x st ->
      In x (SIG.subst_ident_in_type lhs d st).
  Proof.
    intros lhs d st x Hind Hnotin Hinx.
    unfold SIG.subst_ident_in_type.
    assert (Hmemd : SymTypes.my_set_mem d lhs = true).
    { apply SymTypes.my_set_mem_correct. exact Hind. }
    rewrite Hmemd. simpl.
    apply in_merge_right.
    assert (Hxneq : x <> d).
    { intros Heq. subst x. contradiction. }
    eapply st_remove_preserves_other_in; eauto.
  Qed.

  Lemma subAll_mentions_other:
    forall ty cns d st,
      ty <> d ->
      constraints_mention ty cns ->
      constraints_mention ty (subAll cns d st).
  Proof.
    intros ty cns.
    induction cns as [|[lhs rhs] cns IH]; intros d st Hneq Hmention lhs' y Hin.
    - contradiction.
    - assert (Htail : constraints_mention ty cns).
      { intros lhs0 y0 Hin0. eapply Hmention. right; exact Hin0. }
      destruct rhs as [|r rhs'].
      + simpl in Hin. eapply IH; eauto.
      + destruct rhs' as [|r' rhs''].
        * simpl in Hin.
          destruct (ident_eqb r d) eqn:Hrd.
          -- eapply IH; eauto.
          -- destruct Hin as [Heq|Hin].
             ++ inversion Heq; subst lhs' y. clear Heq.
                eapply subST_preserves_other_in; eauto.
                eapply Hmention. left; reflexivity.
             ++ eapply IH; eauto.
        * simpl in Hin. eapply IH; eauto.
  Qed.

  Lemma subAll_mentions_subst:
    forall cns d st ty,
      constraints_mention d cns ->
      ~ In d st ->
      In ty st ->
      constraints_mention ty (subAll cns d st).
  Proof.
    intros cns d st ty Hmention Hnotin Hty.
    induction cns as [|[lhs rhs] cns IH]; intros lhs' y Hin.
    - contradiction.
    - assert (Htail : constraints_mention d cns).
      { intros lhs0 y0 Hin0. eapply Hmention. right; exact Hin0. }
      destruct rhs as [|r rhs'].
      + simpl in Hin. eapply IH; eauto.
      + destruct rhs' as [|r' rhs''].
        * simpl in Hin.
          destruct (ident_eqb r d) eqn:Hrd.
          -- eapply IH; eauto.
          -- destruct Hin as [Heq|Hin].
             ++ inversion Heq; subst lhs' y. clear Heq.
                eapply subST_replaces_target_in; eauto.
                eapply Hmention. left; reflexivity.
             ++ eapply IH; eauto.
        * simpl in Hin. eapply IH; eauto.
  Qed.

  Lemma simplify_mentions_other:
    forall ty cns ds,
      (forall d, In d ds -> ty <> d) ->
      constraints_mention ty cns ->
      constraints_mention ty (SymTypes.simplify cns ds).
  Proof.
    intros ty cns ds Hfresh.
    revert cns.
    induction ds as [|d ds IH]; intros cns Hmention; simpl.
    - exact Hmention.
    - destruct (SymTypes.findST cns d) as [st|] eqn:Hfind.
      + eapply IH.
        * intros d' Hin. apply Hfresh. now right.
        * eapply subAll_mentions_other; eauto.
          apply Hfresh. now left.
      + eapply IH.
        * intros d' Hin. apply Hfresh. now right.
        * exact Hmention.
  Qed.

  Lemma subst_ident_in_constraints_mentions_other:
    forall ty cs x v cs' st st',
      ty <> x ->
      constraints_mention ty cs ->
      subst_ident_in_constraints cs x v st = OK (cs', st') ->
      constraints_mention ty cs'.
  Proof.
    intros ty cs.
    induction cs as [|[lhs rhs] cs IH]; intros x v cs' st st' Hneq Hmention Hsub lhs' y Hin.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. contradiction.
    - assert (Htail : constraints_mention ty cs).
      { intros lhs0 y0 Hin0. eapply Hmention. right; exact Hin0. }
      simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'; clear Hret.
      destruct rhs as [|r rhs0]; try discriminate.
      destruct rhs0 as [|r' rhs1]; try discriminate.
      unfold subst_inp_ident_in_constraint in Hhd.
      destruct (ident_eqb x r) eqn:Hxr; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst c1 st1; clear Hhd.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst lhs' y. clear Heq.
        eapply subst_ident_in_type_preserves_other_in; eauto.
        eapply Hmention. left; reflexivity.
      + eapply IH; eauto.
  Qed.

  Lemma subst_ident_in_constraints_mentions_subst:
    forall cs x v cs' st st' ty,
      constraints_mention x cs ->
      ~ In x v ->
      In ty v ->
      subst_ident_in_constraints cs x v st = OK (cs', st') ->
      constraints_mention ty cs'.
  Proof.
    intros cs.
    induction cs as [|[lhs rhs] cs IH]; intros x v cs' st st' ty Hmention Hnotin Hty Hsub lhs' y Hin.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. contradiction.
    - assert (Htail : constraints_mention x cs).
      { intros lhs0 y0 Hin0. eapply Hmention. right; exact Hin0. }
      simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'; clear Hret.
      destruct rhs as [|r rhs0]; try discriminate.
      destruct rhs0 as [|r' rhs1]; try discriminate.
      unfold subst_inp_ident_in_constraint in Hhd.
      destruct (ident_eqb x r) eqn:Hxr; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst c1 st1; clear Hhd.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst lhs' y. clear Heq.
        eapply subst_ident_in_type_replaces_target_in; eauto.
        eapply Hmention. left; reflexivity.
      + eapply IH; eauto.
  Qed.

  Lemma subst_constraints_inp_map_mentions_other:
    forall ty xs vs cs cs' st st',
      (forall x, In x xs -> ty <> x) ->
      constraints_mention ty cs ->
      subst_constraints_inp_map cs xs vs st = OK (cs', st') ->
      constraints_mention ty cs'.
  Proof.
    intros ty xs.
    revert ty.
    induction xs as [|x xs IH]; intros ty vs cs cs' st st' Hneq Hmention Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hmention.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      assert (Hmention1 : constraints_mention ty cs1).
      { eapply subst_ident_in_constraints_mentions_other; eauto.
        apply Hneq. now left. }
      eapply IH with (st := st1); eauto.
      intros x' Hin. apply Hneq. now right.
  Qed.

  Lemma subst_ident_constraints_mentions_other:
    forall ty cs x v cs' st st',
      ty <> x ->
      constraints_mention ty cs ->
      subst_ident_constraints cs x v st = OK (cs', st') ->
      constraints_mention ty cs'.
  Proof.
    intros ty cs.
    induction cs as [|[lhs rhs] cs IH]; intros x v cs' st st' Hneq Hmention Hsub lhs' y Hin.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. contradiction.
    - assert (Htail : constraints_mention ty cs).
      { intros lhs0 y0 Hin0. eapply Hmention. right; exact Hin0. }
      simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'; clear Hret.
      unfold subst_ident_constraint in Hhd.
      destruct (ident_eqb x v) eqn:Hxv; try discriminate.
      destruct rhs as [|r rhs0]; try discriminate.
      destruct rhs0 as [|r' rhs1]; try discriminate.
      destruct (ident_eqb x r) eqn:Hxr;
        unfold ret in Hhd; inversion Hhd; subst c1 st1; clear Hhd.
      + simpl in Hin.
        destruct Hin as [Heq|Hin].
        * inversion Heq; subst lhs' y. clear Heq.
          eapply subst_ident_in_type_preserves_other_in; eauto.
          eapply Hmention. left; reflexivity.
        * eapply IH; eauto.
      + simpl in Hin.
        destruct Hin as [Heq|Hin].
        * inversion Heq; subst lhs' y. clear Heq.
          eapply subst_ident_in_type_preserves_other_in; eauto.
          eapply Hmention. left; reflexivity.
        * eapply IH; eauto.
  Qed.

  Lemma subst_constraints_out_map_mentions_other:
    forall ty xs vs cs cs' st st',
      (forall x, In x xs -> ty <> x) ->
      constraints_mention ty cs ->
      subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      constraints_mention ty cs'.
  Proof.
    intros ty xs.
    revert ty.
    induction xs as [|x xs IH]; intros ty vs cs cs' st st' Hneq Hmention Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hmention.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      destruct (SymTypes.findST cs v) as [stx|] eqn:Hfind in Hsub; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      assert (Hmention1 : constraints_mention ty cs1).
      { eapply subst_ident_constraints_mentions_other; eauto.
        apply Hneq. now left. }
      eapply IH with (st := st1); eauto.
      intros x' Hin. apply Hneq. now right.
  Qed.

  Lemma reorder_constraints_mentions:
    forall ty src outs cns st st',
      constraints_mention ty src ->
      SC.mmap
        (fun x : ident =>
           SC.bind (SC.option_to_sec (findST src x))
             (fun st0 => SC.ret (st0, [x]))) outs st = OK (cns, st') ->
      constraints_mention ty cns.
  Proof.
    intros ty src outs.
    induction outs as [|x outs IH]; intros cns st st' Hmention Hmap lhs y Hin.
    - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. contradiction.
    - simpl in Hmap.
      eapply sec_bind_inv in Hmap as (cx & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (cxs & st2 & Htl & Hret).
      unfold SC.option_to_sec in Hhd.
      destruct (findST src x) as [stx|] eqn:Hfind; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst cx st1.
      unfold ret in Hret. inversion Hret; subst cns st'; clear Hret.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst lhs y. clear Heq.
        eapply Hmention.
        exact (find_correct _ _ _ Hfind).
      + eapply IH; eauto.
  Qed.

  (** Call-constraint reset propagation.

      Relation to the paper:
      once a callee signature stores its reset field in every visible
      constraint lhs, the call instantiation pipeline must preserve that fact
      syntactically when substituting actual inputs/clock/reset and caller
      outputs.  The reset-aware NLustre call proof later applies this with the
      caller's current reset type as the instantiated reset argument. *)
  Lemma generate_constraints_mentions_reset:
    forall sig inp clk rst out cns st st' ty,
      NoDup (signature_scope sig) ->
      constraints_mention sig.(s_reset) sig.(s_constraints) ->
      type_fresh (signature_scope sig) rst ->
      In ty rst ->
      generate_constraints sig inp clk rst out st = OK (cns, st') ->
      constraints_mention ty cns.
  Proof.
    intros sig inp clk rst out cns st st' ty
           Hndscope Hmention Hrstfresh Htyin Hgen.
    destruct (SIGPROOFS.sig_scope_nodup_decomp sig Hndscope)
      as (Hndin & Hndout & Hfreshin & Hfreshout & Hclkneqrst).
    unfold generate_constraints in Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hreorder).
    assert (Hmention1 : constraints_mention sig.(s_reset) c1).
    {
      eapply subst_constraints_inp_map_mentions_other; eauto.
      intros x Hin Heq.
      apply Forall_forall with (x := x) in Hfreshin; auto.
      simpl in Hfreshin.
      apply Hfreshin.
      rewrite Heq.
      apply in_or_app. right.
      simpl. right. left. reflexivity.
    }
    assert (Hmention2 : constraints_mention sig.(s_reset) c2).
    {
      eapply subst_ident_in_constraints_mentions_other; eauto.
    }
    assert (Hreset_notin : ~ In sig.(s_reset) rst).
    {
      unfold type_fresh in Hrstfresh.
      rewrite Forall_forall in Hrstfresh.
      intro Hin.
      specialize (Hrstfresh _ Hin).
      apply Hrstfresh.
      unfold signature_scope.
      repeat rewrite in_app_iff.
      simpl. auto.
    }
    assert (Hmention3 : constraints_mention ty c3).
    {
      eapply subst_ident_in_constraints_mentions_subst; eauto.
    }
    assert (Hmention4 : constraints_mention ty c4).
    {
      eapply subst_constraints_out_map_mentions_other; eauto.
      intros x Hin Heq.
      unfold type_fresh in Hrstfresh.
      rewrite Forall_forall in Hrstfresh.
      specialize (Hrstfresh _ Htyin).
      apply Hrstfresh.
      subst x.
      unfold signature_scope.
      repeat rewrite in_app_iff.
      auto.
    }
    eapply reorder_constraints_mentions; eauto.
  Qed.

  (** Local inversion helpers copied from the indexed noninterference support.

      These are source-local monadic shape views of one generated equation
      block.  They are duplicated here to avoid an import cycle from the
      noninterference helper layer back into this correctness module. *)
  Lemma generate_eqdef_constraint_inv:
    forall G ty_env base_ty rst_ty x ck ce cns st st',
      SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqDef x ck ce) st =
      OK (cns, st') ->
      exists ckty cety xty,
        cns = [((([rst_ty] ⊔ ckty) ⊔ cety), [xty])]
        /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
        /\ SECCETYPING.assign_cexp_type ty_env ce = Some cety
        /\ Env.find x ty_env = Some xty.
  Proof.
    intros G ty_env base_ty rst_ty x ck ce cns st st' Hgen.
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
    forall G ty_env base_ty rst_ty x ck c0 e cns st st',
      SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqFby x ck c0 e) st =
      OK (cns, st') ->
      exists ckty ety xty,
        cns = [((([rst_ty] ⊔ ckty) ⊔ ety), [xty])]
        /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
        /\ SECCETYPING.assign_exp_type ty_env e = Some ety
        /\ Env.find x ty_env = Some xty.
  Proof.
    intros G ty_env base_ty rst_ty x ck c0 e cns st st' Hgen.
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
    forall G ty_env base_ty rst_ty x xs ck f exps cns st st',
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
    intros G ty_env base_ty rst_ty x xs ck f exps cns st st' Hgen.
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
    specialize (SECNLUSTYPING.mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl)
      as [Hst_tl Hmaps_tl].
    subst st_tl.
    unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
    assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
    { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
    exists callee_sig, ckty, inptyp, (xty' :: tys'), st_clk, st_inp.
    repeat split; auto.
  Qed.

  Lemma generate_eqreset_constraint_inv:
    forall G ty_env base_ty rst_ty x xs ck f exps r ckr cns st st',
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
    intros G ty_env base_ty rst_ty x xs ck f exps r ckr cns st st' Hgen.
    simpl in Hgen.
    destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
      try discriminate.
    eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
    eapply sec_bind_inv in Hgen as (rty & st_rty & Hrty & Hgen).
    eapply sec_bind_inv in Hgen as (rstty & st_rst & Hrst & Hgen).
    eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
    eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
    unfold SC.find_env in Hrty.
    destruct (Env.find r ty_env) as [rty'|] eqn:Hfindr; try discriminate.
    unfold SC.ret in Hrty. inversion Hrty; subst rty st_rty.
    simpl in Hout.
    eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
    eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
    unfold SC.find_env in Hfindx.
    destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
    unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
    specialize (SECNLUSTYPING.mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl)
      as [Hst_tl Hmaps_tl].
    subst st_tl.
    unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
    assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
    { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
    exists callee_sig, ckty, rty', rstty, inptyp, (xty' :: tys'),
           st_clk, st_rst, st_inp.
    repeat split; auto.
  Qed.

  Lemma assign_clk_type_contains_base:
    forall env base ck st,
      SECCETYPING.assign_clk_type env base ck = Some st ->
      In base st.
  Proof.
    intros env base ck.
    induction ck as [|ck IH x b]; intros st Hassign.
    - simpl in Hassign. inversion Hassign; subst. simpl. auto.
    - simpl in Hassign.
      destruct (SECCETYPING.assign_clk_type env base ck) as [ckty|] eqn:Hck;
        try discriminate.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      inversion Hassign; subst st.
      apply in_merge_left.
      eapply IH; eauto.
  Qed.

  (** Node-local raw reset-mention fact.

      Relation to the paper:
      this is the source-local half of the final theorem.  It states that the
      raw NLustre constraints generated for one node already thread the current
      node reset through every visible singleton-RHS constraint, including the
      constraints imported from previously generated callee signatures. *)
  Lemma generate_node_sig_constraints_mention_reset_from_local_env:
    forall G P n env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n,
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst)) ->
      node_scope_fresh_in_env n env aux_names G ->
      (forall f sig, SIG.find_signature f G = Some sig -> NoDup (signature_scope sig)) ->
      (forall f sig lhs y,
          SIG.find_signature f G = Some sig ->
          In (lhs, [y]) sig.(s_constraints) ->
          In sig.(s_reset) lhs) ->
      wc_node P n ->
      Env.find rec.(nclk) env = Some clk_type ->
      Env.find rec.(nrst) env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      generate_eqns_constraints G env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
      constraints_mention rst_type (SymTypes.simplify raw locals).
  Proof.
    intros G P n env rec aux_names st st'
           clk_type rst_type inp out locals raw st_n
           Hlocal Haux Hscopefresh Hndacc Hmentionacc
           Hwc Hclk Hrst Hinp Hout Hlocals Hraw.
    set (scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
    assert (Hvars :
              SECNLUSTYPING.vars_env_scoped env
                (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) scope).
    { unfold scope.
      eapply node_vars_env_scoped_from_mappings; eauto. }
    assert (Hraw_mentions : constraints_mention rst_type raw).
    {
      pose proof (NAMEGEN.generate_local_env_for_node_injective _ _ _ _ _ Hlocal)
        as Hinj.
      destruct Hwc as [_ [_ [Hwcenv Hweqs]]].
      assert (Hndeqs : NoDup (vars_defined n.(n_eqs))).
      { apply NoDup_var_defined_n_eqs. }
      assert (Hmentions_eqs :
                forall eqs st0 raw0 st_n0,
                  generate_eqns_constraints G env clk_type rst_type eqs st0 = OK (raw0, st_n0) ->
                  Forall (wc_equation P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) eqs ->
                  NoDup (vars_defined eqs) ->
                  constraints_mention rst_type raw0).
      {
        induction eqs as [|eq eqs IH]; intros st0 raw0 st_n0 Hgen Hweqs0 Hndeqs0 lhs y Hin.
        - simpl in Hgen. inversion Hgen; subst. contradiction.
        - simpl in Hgen.
          eapply sec_bind_inv in Hgen as (c1 & st1 & Hc1 & Hgen).
          eapply sec_bind_inv in Hgen as (c2 & st2 & Hc2 & Hret).
          unfold ret in Hret. inversion Hret; subst raw0 st_n0; clear Hret.
          inversion Hweqs0 as [|eq0 eqs0 Hweq Hweqs']; subst eq0 eqs0.
          assert (Hndsplit : NoDup (var_defined eq ++ vars_defined eqs)).
          { exact Hndeqs0. }
          apply NoDup_app'_iff in Hndsplit as [Hndeq [Hndtail _]].
          apply in_app_iff in Hin.
          destruct Hin as [Hin1|Hin2].
          + destruct eq as [x ck ce|xs ck f exps r|x ck c0 e].
            * destruct (generate_eqdef_constraint_inv _ _ _ _ _ _ _ _ _ _ Hc1)
                as (ckty & cety & xty & Hcns & _ & _ & _).
              rewrite Hcns in Hin1. simpl in Hin1.
              destruct Hin1 as [Heq|[]]. inversion Heq; subst.
              eapply in_merge_left.
              change (In rst_type ([rst_type] ⊔ ckty)).
              eapply in_merge_left.
              simpl. auto.
            * destruct xs as [|x xs].
              { simpl in Hc1. unfold ret in Hc1. inversion Hc1; subst.
                simpl in Hin1. contradiction. }
              destruct r as [[rx rck]|].
              -- destruct (generate_eqreset_constraint_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1)
                   as (callee_sig & ckty & rty & rstty_call & inptyp & outtyp
                       & st_clk & st_rst & st_inp
                       & Hfindsigc & Hckc & Hrty & Hrstc & Hinpc & Houtc & Hcallc).
                 assert (Hfreshcallee : SIG.scope_fresh scope callee_sig).
                 {
                   unfold node_scope_fresh_in_env in Hscopefresh.
                   eapply Hscopefresh; eauto.
                 }
                 assert (Hrst_scope : st_scoped scope ((rty :: nil) ⊔ rstty_call)).
                 {
                  inversion Hweq as [|xs0 ck0 f0 les0 r0 callee sub Hfindn Hins Houts Hreset|];
                    subst; try contradiction.
                   assert (Hinr : In (rx, rck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                   { eapply Hreset. reflexivity. }
                   assert (Hwc_ckr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) rck).
                   { eapply wc_env_var; eauto. }
                   eapply st_scoped_merge.
                   - apply st_scoped_singleton.
                     destruct (Hvars rx (In_InMembers _ _ _ Hinr)) as (ty & Hfind & Hscope_r).
                     rewrite Hfind in Hrty. inversion Hrty; subst. exact Hscope_r.
                   - unfold SC.option_to_sec in Hrstc.
                     destruct (SECCETYPING.assign_clk_type env rst_type rck) as [rstty'|]
                       eqn:Hrstopt; try discriminate.
                     unfold SC.ret in Hrstc. inversion Hrstc; subst rstty_call st_rst.
                     eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_type) (ck := rck).
                     + unfold scope. repeat rewrite in_app_iff. right. right. right.
                       simpl. right. left. reflexivity.
                     + intros z Hz.
                       assert (Hinz : InMembers z (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
                       { eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto. }
                       destruct (Hvars z Hinz) as (ty & Hfind & Hscopez).
                       exists ty. split; [exact Hfind|exact Hscopez].
                     + exact Hrstopt.
                 }
                 assert (Hrstfresh_c :
                           type_fresh (signature_scope callee_sig) ((rty :: nil) ⊔ rstty_call)).
                 {
                   eapply SIG.type_fresh_from_scope_fresh; eauto.
                 }
                 assert (Hndscope_c : NoDup (signature_scope callee_sig)).
                 { eapply Hndacc; eauto. }
                 assert (Hcallee_mentions : constraints_mention callee_sig.(s_reset) callee_sig.(s_constraints)).
                 {
                   intros lhs0 y0 Hin0.
                   eapply Hmentionacc; eauto.
                 }
                 assert (Hrstin : In rst_type ((rty :: nil) ⊔ rstty_call)).
                 {
                   assert (Hrstassign : SECCETYPING.assign_clk_type env rst_type rck = Some rstty_call).
                   {
                     unfold SC.option_to_sec in Hrstc.
                     destruct (SECCETYPING.assign_clk_type env rst_type rck) as [rstty'|] eqn:Hrstopt;
                       try discriminate.
                     inversion Hrstc; subst rstty_call st_rst. reflexivity.
                   }
                   apply in_merge_right.
                   eapply assign_clk_type_contains_base.
                   exact Hrstassign.
                 }
                 eapply (generate_constraints_mentions_reset
                           callee_sig inptyp ckty ((rty :: nil) ⊔ rstty_call) outtyp
                           c1 st_inp st1 rst_type); eauto.
              -- destruct (generate_eqapp_constraint_inv _ _ _ _ _ _ _ _ _ _ _ _ Hc1)
                   as (callee_sig & ckty & inptyp & outtyp & st_clk & st_inp
                       & Hfindsigc & _ & _ & Houtc & Hcallc).
                 assert (Hfreshcallee : SIG.scope_fresh scope callee_sig).
                 {
                   unfold node_scope_fresh_in_env in Hscopefresh.
                   eapply Hscopefresh; eauto.
                 }
                 assert (Hrstfresh_c : type_fresh (signature_scope callee_sig) [rst_type]).
                 {
                   eapply SIG.type_fresh_from_scope_fresh.
                   - exact Hfreshcallee.
                   - apply st_scoped_singleton.
                     unfold scope. repeat rewrite in_app_iff. right. right. right.
                     simpl. right. left. reflexivity.
                 }
                 assert (Hndscope_c : NoDup (signature_scope callee_sig)).
                 { eapply Hndacc; eauto. }
                 assert (Hcallee_mentions : constraints_mention callee_sig.(s_reset) callee_sig.(s_constraints)).
                 {
                   intros lhs0 y0 Hin0.
                   eapply Hmentionacc; eauto.
                 }
                 eapply (generate_constraints_mentions_reset
                           callee_sig inptyp ckty [rst_type] outtyp
                           c1 st_inp st1 rst_type); eauto.
                 simpl. auto.
            * destruct (generate_eqfby_constraint_inv _ _ _ _ _ _ _ _ _ _ _ Hc1)
                as (ckty & ety & xty & Hcns & _ & _ & _).
              rewrite Hcns in Hin1. simpl in Hin1.
              destruct Hin1 as [Heq|[]]. inversion Heq; subst.
              eapply in_merge_left.
              change (In rst_type ([rst_type] ⊔ ckty)).
              eapply in_merge_left.
              simpl. auto.
          + eapply IH; eauto.
      }
      eapply Hmentions_eqs; eauto.
    }
    assert (Hrst_not_local :
              forall x, In x locals -> rst_type <> x).
    {
      pose proof (NAMEGEN.generate_local_env_for_node_injective _ _ _ _ _ Hlocal)
        as Hinj.
      pose proof (NAMEGEN.generate_local_env_for_node_aux_sec_names _ _ _ _ _ Hlocal)
        as [Hclkid Hrstid].
      intros x Hin Heq.
      destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin)
        as (xraw & araw & Hxraw & Hfindx).
      assert (Hxeq : xraw = rec.(nrst)).
      { eapply Hinj; eauto. }
      subst xraw.
      eapply (node_var_not_sec_gensym n rec.(nrst) (Pos.succ st)).
      - rewrite map_app. apply in_or_app. right.
        rewrite map_app. apply in_or_app. left.
        now apply in_map with (f := fst) in Hxraw.
      - exact Hrstid.
    }
    eapply simplify_mentions_other; eauto.
  Qed.

  Theorem generated_signature_constraints_mention_reset_scoped_env':
    forall prefix nodes acc envs aux_names envs_pref aux_pref st G,
      NAMEGEN.generate_node_scoped_env' prefix (Env.empty _) nil NAMEGEN.init_state
        = OK ((envs_pref, aux_pref), st) ->
      generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
      Clo.wc_global nodes ->
      (forall f sig lhs y,
          SIG.find_signature f acc = Some sig ->
          In (lhs, [y]) sig.(s_constraints) ->
          In sig.(s_reset) lhs) ->
      (forall f sig,
          SIG.find_signature f acc = Some sig ->
          NoDup (signature_scope sig)) ->
      SIG.secglobal_scope_bounded_above acc st ->
      SECNLUSTYPING.generate_all_signatures_scoped_env' acc nodes envs aux_names = OK G ->
      forall f sig lhs y,
        SIG.find_signature f G = Some sig ->
        In (lhs, [y]) sig.(s_constraints) ->
        In sig.(s_reset) lhs.
  Proof.
    intros prefix nodes.
    revert prefix.
    induction nodes as [|n nodes IH];
      intros prefix acc envs aux_names envs_pref aux_pref st G
             Hprefgen Henvsgen Hwc Hmentionacc Hndacc Hbound Hgen
             f sig lhs y Hfindsig Hin.
    - simpl in Hgen. inversion Hgen; subst G.
      eapply Hmentionacc; eauto.
    - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
      simpl in Hgen.
      destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc n envs aux_names)
        as [nsig|e_sig] eqn:Hnsig; try discriminate.
      destruct (SECNLUSTYPING.generate_all_signatures_scoped_env' (nsig :: acc) nodes envs aux_names)
        as [G'|e_tl] eqn:Htl; simpl in Hgen.
      2:{ rewrite Hgen in Htl. discriminate. }
      inversion Hgen; subst; clear Hgen.
      pose proof Henvsgen as Henvsgen_full.
      unfold generate_node_scoped_env in Henvsgen_full.
      destruct
        (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nodes) (Env.empty _) nil NAMEGEN.init_state)
        as [[[envs_full aux_full] st_full]|] eqn:Hrun; try discriminate.
      inversion Henvsgen_full; subst envs_full aux_full; clear Henvsgen_full.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
            & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
        eauto.
      rewrite Hprefgen in Hpref. inversion Hpref; subst envs_pref' aux_pref' st_pref.
      assert (Hcur : st_cur = st_local).
      {
        unfold NAMEGEN.fresh_insert_node_env in Hins.
        destruct (Env.mem n.(n_name) envs_pref) eqn:Hmem; try discriminate.
        unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
        inversion Hins. reflexivity.
      }
      subst st_cur.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
        eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
        - pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
          unfold get_node_aux. simpl. rewrite <- Hrecname, ident_eqb_refl. reflexivity.
        - eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
      rewrite Hfindlocal in Hnsig.
      edestruct generate_node_sig_inv_local
        as (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
            & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef);
        eauto.
      rewrite Hauxlocal in Haux.
      inversion Haux. subst clk_id rst_id. clear Haux.
      assert (Hscopefresh_cur :
                node_scope_fresh_in_env n local_env aux_names acc).
      {
        eapply node_scope_fresh_in_env_from_bounds; eauto.
      }
      assert (Hnsigmention :
                constraints_mention rst_type (SymTypes.simplify raw locals)).
      {
        eapply generate_node_sig_constraints_mention_reset_from_local_env
          with (P := nodes) (rec := rec) (st := st) (st' := st_local); eauto.
      }
      assert (Hnsigprop :
                forall lhs0 y0,
                  In (lhs0, [y0]) nsig.(s_constraints) ->
                  In nsig.(s_reset) lhs0).
      {
        rewrite Hsigdef.
        exact Hnsigmention.
      }
      assert (Hnsignd :
                NoDup (signature_scope nsig)).
      {
        rewrite Hsigdef.
        eapply generate_node_sig_scope_nodup_from_local_env
          with (rec := rec) (st := st) (st' := st_local)
               (clk_type := clk_type) (rst_type := rst_type)
               (inp := inp) (out := out); eauto.
      }
      assert (Hnsigbound : SIG.signature_scope_bounded_above nsig st_local).
      {
        intros ty Hin'.
        eapply (generated_node_sig_scope_upper_bound_from_local_env
                  acc n local_env aux_names nsig st rec st_local ty); eauto.
      }
      assert (Hle : (st <= st_local)%positive).
      { eapply NAMEGEN.generate_local_env_for_node_state_monotone; eauto. }
      assert (Hmention' :
                forall f0 sig0 lhs0 y0,
                  SIG.find_signature f0 (nsig :: acc) = Some sig0 ->
                  In (lhs0, [y0]) sig0.(s_constraints) ->
                  In sig0.(s_reset) lhs0).
      {
        intros f0 sig0 lhs0 y0 Hfind0 Hin0.
        simpl in Hfind0.
        destruct (ident_eqb nsig.(s_name) f0) eqn:Hname.
        - inversion Hfind0; subst sig0. eapply Hnsigprop; eauto.
        - eapply Hmentionacc; eauto.
      }
      assert (Hnd' :
                forall f0 sig0,
                  SIG.find_signature f0 (nsig :: acc) = Some sig0 ->
                  NoDup (signature_scope sig0)).
      {
        intros f0 sig0 Hfind0.
        simpl in Hfind0.
        destruct (ident_eqb nsig.(s_name) f0) eqn:Hname.
        - inversion Hfind0; subst sig0. exact Hnsignd.
        - eapply Hndacc; eauto.
      }
      assert (Hbound' : SIG.secglobal_scope_bounded_above (nsig :: acc) st_local).
      {
        eapply SIG.secglobal_scope_bounded_above_cons; eauto.
        eapply SIG.secglobal_scope_bounded_above_monotone; eauto.
      }
      assert (Hstep :
                NAMEGEN.generate_node_scoped_env' (n :: nil) envs_pref aux_pref st =
                OK ((envs_cur, rec :: aux_pref), st_local)).
      {
        simpl.
        unfold NMbind2.
        rewrite Hlocal.
        simpl.
        unfold NMbind.
        rewrite Hins.
        simpl.
        reflexivity.
      }
      assert (Hprefgen' :
                NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nil) (Env.empty _) nil NAMEGEN.init_state =
                OK ((envs_cur, rec :: aux_pref), st_local)).
      {
        eapply NAMEGEN.generate_node_scoped_env'_app; eauto.
      }
      assert (Henvsgen' :
                generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes) = OK (envs, aux_names)).
      {
        assert (Heqlist : (prefix ++ n :: nil) ++ nodes = prefix ++ n :: nodes).
        {
          clear - prefix n nodes.
          induction prefix as [|a prefix IHprefix]; simpl.
          - reflexivity.
          - now f_equal.
        }
        rewrite Heqlist. exact Henvsgen.
      }
      assert (HG : G' = G).
      {
        rewrite Htl in H0.
        inversion H0. reflexivity.
      }
      subst G.
      exact (IH (prefix ++ n :: nil) (nsig :: acc) envs aux_names envs_cur
                (rec :: aux_pref) st_local G'
                Hprefgen' Henvsgen' Hwc_tail Hmention' Hnd' Hbound' Htl
                f sig lhs y Hfindsig Hin).
  Qed.

  (** Generated source signatures mention reset in every visible constraint.

      Relation to the paper:
      the reset-aware noninterference proof for NLustre reset calls needs a
      purely typing-side fact: whenever a generated source signature exposes a
      visible output constraint through [findST], that visible constraint still
      mentions the node reset field.  This is what lets
      [call_output_low_implies_reset_low] turn a low caller-visible reset-call
      output into a low instantiated reset argument.

      Planned proof route:
      1. Prove the node-local version first, starting from
         [generate_node_sig_good_from_local_env] and the raw equation
         generation witnesses from [generate_node_sig_inv_local].
      2. Show directly on the raw NLustre constraints that every output-facing
         constraint lhs contains the current node reset type:
         - [EqDef] and [EqFby] now include [rst_type] explicitly;
         - [EqApp] and reset [EqApp] inherit reset through
           [generate_constraints].
      3. Lift that raw fact through [SymTypes.simplify]:
         local eliminations may remove local identifiers, but they should not
         eliminate the node reset identifier from a surviving visible
         constraint.  The existing [simplify_rhs_in] and
         [simplify_preserves_other_rhs] lemmas are the intended starting point.
      4. Finally lift the local result through the scoped-environment/global
         signature generation pass, using the same local-environment splitting
         pattern as [generate_all_source_signatures_good_scoped_env'].

      The proof below follows that route directly inside the source-local
      correctness layer so the indexed noninterference development can consume
      it without depending back on the helper file. *)
  Theorem generated_signature_constraints_mention_reset_scoped_env:
    forall all_nodes envs aux_names G f sig y lhs,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
      SIG.find_signature f G = Some sig ->
      findST sig.(s_constraints) y = Some lhs ->
      In sig.(s_reset) lhs.
  Proof.
    intros all_nodes envs aux_names G f sig y lhs
           Henvsgen Hwc Hgen Hfindsig Hfindlhs.
    unfold SECNLUSTYPING.generate_all_signatures_scoped_env in Hgen.
    assert (Hpref0 :
              NAMEGEN.generate_node_scoped_env' [] (Env.empty _) [] NAMEGEN.init_state =
              OK ((Env.empty _ , []), NAMEGEN.init_state)).
    { reflexivity. }
    assert (Hmention0 :
              forall f0 sig0 lhs0 y0,
                SIG.find_signature f0 [] = Some sig0 ->
                In (lhs0, [y0]) sig0.(s_constraints) ->
                In sig0.(s_reset) lhs0).
    { intros f0 sig0 lhs0 y0 Hfind0. simpl in Hfind0. discriminate. }
    assert (Hnd0 :
              forall f0 sig0,
                SIG.find_signature f0 [] = Some sig0 ->
                NoDup (signature_scope sig0)).
    { intros f0 sig0 Hfind0. simpl in Hfind0. discriminate. }
    pose proof
      (generated_signature_constraints_mention_reset_scoped_env'
         [] all_nodes [] envs aux_names (Env.empty _) [] NAMEGEN.init_state G
         Hpref0 Henvsgen Hwc
         Hmention0 Hnd0
         (SIG.secglobal_scope_bounded_above_nil NAMEGEN.init_state)
         Hgen
         f sig lhs y Hfindsig (find_correct _ _ _ Hfindlhs))
      as Hreset.
    exact Hreset.
  Qed.
End SECNLUSTYPINGCORRECTNESS.

Module SecNLusTypingCorrectness
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
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
  <: SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

Include SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING.

End SecNLusTypingCorrectness.
