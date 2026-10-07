(** The program level, for Lustre.

    Legs U and I reduce preservation across normalisation to two per-node
    steps, and those steps are conditioned on facts about the *program*: that
    the naming pass covers the node, that a generated signature is good and
    scoped, and that the scope keeps the published interface apart from
    everything a pass or a generator creates.  None of those can be stated in
    the files that need them -- they are about
    [generate_all_lsignatures_scoped_env] and about the naming pass, and the
    two sides only meet here.

    This is the Lustre counterpart of [SecNLusTypingCorrectness.v], and the
    arguments mirror it; what differs is the node record and the two passes
    that stand between the source program and the one transcription sees. *)

From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Lia.
From Coq Require Import Sorting.Permutation.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import Lustre.Normalization.NormFby.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNamingTotality.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLNamingTotality.
From Velus Require Import SIF.SecLusNormFby.

From compcert Require Import common.Errors.

Module SecLusTypingCorrectness
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import Lat     : Lattice)
  (Import SecT    : SECTYPES Lat)
  (Import SLT     : SECLUSTYPES Lat SecT)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX Ids Op)
  (Import LClo    : LCLOCKING Ids Op LSyn)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Mem            : MEMORIES Ids Op CESyn NLSyn)
  (IsD            : ISDEFINED Ids Op CESyn NLSyn Mem)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import UNN     : UNNESTING Ids Op OpAux LSyn)
  (Import NF      : NORMFBY Ids Op OpAux LSyn UNN)
  (Import SECLNG  : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (Import SECNT   : SECNAMINGTOTALITY Ids Op CESyn NLSyn Mem IsD NLOrd NAMEGEN)
  (Import LOrd    : LORDERED Ids Op LSyn)
  (Import SECLNT  : SECLNAMINGTOTALITY Ids Op OpAux LSyn CESyn NLSyn Mem IsD
                      NLOrd NAMEGEN TR SECLNG SECNT LOrd)
.

Module NFB := SecLusNormFby Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn
                STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN NF.
Include NFB.

Import SECMONADNotations.

  (** * The published interface, as a list of security names

      [get_mappings_from_node] and [sec_of] compute the same list whenever the
      first succeeds, and the node theorems are stated in terms of the second.
      Having both is what lets a premise about *variables* be turned into one
      about the names a signature publishes. *)

  Lemma get_mappings_from_node_sec_of :
    forall {A : Type} (xs : list (ident * A)) env tys,
      get_mappings_from_node xs env = Some tys ->
      tys = CALLS.sec_of env (List.map fst xs).
  Proof.
    intros A xs. induction xs as [|p xs IH]; intros env tys Hget.
    - cbn in Hget. inversion Hget. reflexivity.
    - destruct p as (x & a). cbn in Hget.
      destruct (Env.find x env) as [t|] eqn:Ex; [|discriminate Hget].
      destruct (get_mappings_from_node xs env) as [ts|] eqn:Ets;
        [|discriminate Hget].
      cbn in Hget. inversion Hget; subst tys.
      rewrite (IH env ts Ets).
      unfold CALLS.sec_of. cbn [List.map flat_map fst].
      rewrite Ex. reflexivity.
  Qed.

  Lemma sec_of_app :
    forall env (xs ys : list ident),
      CALLS.sec_of env (xs ++ ys)
      = CALLS.sec_of env xs ++ CALLS.sec_of env ys.
  Proof.
    intros env xs ys. unfold CALLS.sec_of. symmetry. apply flat_map_app.
  Qed.

  (** * Item 4, assembled: the scope keeps the published interface apart from
        everything the unnesting run created

      Taking the scope to be the published signature's own scope, the moved
      names fall outside it for two reasons, one per part of the scope.

      Against the *interface* part it is [sec_of_disjoint] over
      [unnest_node_new_not_interface]: a variable the run created is not an
      interface variable, and [env] is injective, so its security name is not
      one of the interface's.

      Against the *base and reset* part it is [declared_not_sec] against
      [generate_lnode_scoped_env_aux_sec_names]: the two auxiliary names are
      [sec] gensyms, a variable the unnested node declares is not, and
      injectivity again carries that to the names. *)

  Lemma unnest_run_declared :
    forall P (n : node) (Hwl : wl_node P n)
           (Hpref : n_prefixes n = elab_prefs) x,
      In x (st_ids (snd (unnest_equations P n.(n_eqs) init_st))) ->
      In x (List.map fst ((unnest_node P n Hwl Hpref).(n_in)
                            ++ (unnest_node P n Hwl Hpref).(n_vars)
                            ++ (unnest_node P n Hwl Hpref).(n_out))).
  Proof.
    intros P n Hwl Hpref x Hx.
    unfold st_ids in Hx. apply in_map_iff in Hx as (p & Hfst & Hp).
    destruct p as (z & an). cbn [fst] in Hfst. subst z.
    destruct (unnest_node_fields P n Hwl Hpref) as (_ & Hv).
    apply in_map_iff. exists (x, an). split; [reflexivity|].
    apply in_or_app. right. apply in_or_app. left.
    rewrite Hv. apply in_or_app. now right.
  Qed.

  Theorem unnest_moved_not_sig_scope :
    forall (G : secglobal) (env : Env.t ident) (n : node)
           (aux : list node_aux_names) sg st st'
           P (Hwl : wl_node P n) (Hpref : n_prefixes n = elab_prefs)
           ns envs,
      env_injective env ->
      PS.Subset (unnest_node P n Hwl Hpref).(n_prefixes)
        (PSP.of_list gensym_prefs) ->
      generate_lnode_scoped_env ns = OK (envs, aux) ->
      generate_lnode_sig G n env aux st = OK (sg, st') ->
      forall y,
        In y (CALLS.moved_by env init_st
                (snd (unnest_equations P n.(n_eqs) init_st))) ->
        ~ In y (signature_scope sg).
  Proof.
    intros G env n aux sg st st' P Hwl Hpref ns envs
      Hinj Hsub Hnames Hsig y Hy.
    destruct (lnode_sig_inv env G n aux sg st st' Hsig)
      as (clk_id & rst_id & clk_type & rst_type & inp & out & locals & cns
          & Haux & Hclk & Hrst & Hinp & Hout & _ & _ & Esg).
    subst sg. unfold signature_scope. cbn [s_in s_out s_clk s_reset].
    rewrite (get_mappings_from_node_sec_of n.(n_in) env inp Hinp).
    rewrite (get_mappings_from_node_sec_of n.(n_out) env out Hout).
    unfold CALLS.moved_by in Hy.

    (** the interface part *)
    assert (~ In y (CALLS.sec_of env (List.map fst n.(n_in))
                      ++ CALLS.sec_of env (List.map fst n.(n_out)))) as Hiface.
    { rewrite <- sec_of_app.
      eapply (sec_of_disjoint env Hinj
                (CALLS.new_ids init_st
                   (snd (unnest_equations P n.(n_eqs) init_st)))
                (List.map fst n.(n_in) ++ List.map fst n.(n_out)) y);
        [|exact Hy].
      intros x Hx Hc.
      apply CALLS.new_ids_spec in Hx as (Hx & _).
      eapply (unnest_node_new_not_interface P n Hwl Hpref x Hx).
      rewrite map_app. exact Hc. }

    (** and the two auxiliary names *)
    assert (forall z, In z [clk_type; rst_type] -> y <> z) as Haux'.
    { intros z Hz Heq. subst z.
      unfold CALLS.sec_of in Hy. apply in_flat_map in Hy as (x & Hx & Hyx).
      destruct (Env.find x env) as [b|] eqn:Ex; [|contradiction].
      destruct Hyx as [Hyx|[]]; subst b.
      apply CALLS.new_ids_spec in Hx as (Hx & _).
      assert (forall i, x <> Ids.gensym Ids.sec i) as Hxns
          by (intros i; eapply SECLNT.declared_not_sec;
              [exact Hsub|exact (unnest_run_declared P n Hwl Hpref x Hx)]).
      destruct (SECLNT.generate_lnode_scoped_env_aux_sec_names
                  ns envs aux n.(n_name) clk_id rst_id Hnames Haux)
        as (i & j & Hi & Hj).
      destruct Hz as [Hz|[Hz|[]]].
      - (** the base name *)
        assert (x = clk_id) as ? by (eapply Hinj; [exact Ex|exact Hclk|
                                     exact (@Coq.Init.Logic.eq_sym _ _ _ Hz)]).
        subst x. exact (Hxns i Hi).
      - (** the reset name *)
        assert (x = rst_id) as ? by (eapply Hinj; [exact Ex|exact Hrst|
                                     exact (@Coq.Init.Logic.eq_sym _ _ _ Hz)]).
        subst x. exact (Hxns j Hj). }

    intro Hc. apply in_app_or in Hc as [Hc|Hc].
    - apply Hiface. apply in_or_app. now left.
    - apply in_app_or in Hc as [Hc|Hc].
      + apply Hiface. apply in_or_app. now right.
      + exact (Haux' y Hc (@Coq.Init.Logic.eq_refl _ y)).
  Qed.

  (** * Towards item 7: singleton targets

      [wf_constraints] is two things -- every constraint has a one-element
      target, and the targets are pairwise distinct -- and they have quite
      different costs.  The first is structural: every rule the generator has
      emits [lconstrain _ b], whose target is [[b]], over whatever the
      expression carried, and an instantiated call block's targets are its
      outputs.  The second needs the minted window, and is where the real
      work is.

      These two are the first half's plumbing: [cmerge] is a sorted merge
      with dedup rather than an append, so a [Forall] property has to be
      pushed through it by membership, and an instantiated block's targets are
      singletons because they are exactly its outputs. *)

  Lemma singleton_targets_cmerge :
    forall c1 c2,
      SIGPROOFS.singleton_targets c1 ->
      SIGPROOFS.singleton_targets c2 ->
      SIGPROOFS.singleton_targets (cmerge c1 c2).
  Proof.
    intros c1 c2 H1 H2.
    unfold SIGPROOFS.singleton_targets in H1, H2 |- *.
    rewrite Forall_forall in H1, H2 |- *.
    intros c Hin. apply cmerge_In in Hin as [Hin|Hin]; auto.
  Qed.

  Lemma singleton_targets_app :
    forall c1 c2,
      SIGPROOFS.singleton_targets c1 ->
      SIGPROOFS.singleton_targets c2 ->
      SIGPROOFS.singleton_targets (c1 ++ c2).
  Proof.
    intros c1 c2 H1 H2. unfold SIGPROOFS.singleton_targets in *.
    apply Forall_app. split; assumption.
  Qed.

  Lemma generate_constraints_singleton_targets :
    forall sg inp clk rst out cns sa sa',
      generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
      SIGPROOFS.singleton_targets cns.
  Proof.
    intros sg inp clk rst out cns sa sa' Hgen.
    pose proof (CALLS.generate_constraints_targets sg inp clk rst out cns
                  sa sa' Hgen) as Hsnd.
    unfold SIGPROOFS.singleton_targets. apply Forall_forall.
    intros c Hc.
    assert (In (snd c) (List.map (fun ty => [ty]) out)) as Hin
        by (rewrite <- Hsnd; apply in_map_iff; exists c;
            split; [reflexivity|exact Hc]).
    apply in_map_iff in Hin as (d & Hd & _). now exists d.
  Qed.

  (** * 7a: every constraint the generator emits has a one-element target

      The expression induction.  Nine of the ten cases are immediate -- the
      carried component is empty, or a [cmerge]/[ljoin_list] of the
      sub-expressions' -- and the call case is the instantiated block, whose
      targets are its outputs. *)

  Lemma singleton_targets_cmerge_inv :
    forall c1 c2,
      SIGPROOFS.singleton_targets (cmerge c1 c2) ->
      SIGPROOFS.singleton_targets c1 /\ SIGPROOFS.singleton_targets c2.
  Proof.
    intros c1 c2 H.
    unfold SIGPROOFS.singleton_targets in H |- *.
    rewrite Forall_forall in H. split; rewrite Forall_forall;
      intros c Hc; apply H, cmerge_In; tauto.
  Qed.

  Lemma singleton_targets_carried_map_ljoin :
    forall h ts,
      SIGPROOFS.singleton_targets (snd h) ->
      SIGPROOFS.singleton_targets (carried ts) ->
      SIGPROOFS.singleton_targets
        (carried (List.map (fun t => ljoin h t) ts)).
  Proof.
    intros h ts Hh. induction ts as [|t ts IH]; intros Hts.
    - cbn [List.map carried]. constructor.
    - cbn [List.map]. rewrite carried_cons.
      rewrite carried_cons in Hts.
      apply singleton_targets_cmerge_inv in Hts as (Ht & Htr).
      apply singleton_targets_cmerge; [|exact (IH Htr)].
      rewrite snd_ljoin. apply singleton_targets_cmerge; assumption.
  Qed.

  (** * Towards 7b: where a target comes from

      The second half of [wf_constraints] needs to know *which* names the
      targets are, not just that there is one of them each.  They are the
      security names of the variables an equation defines, together with the
      names the generator minted for the calls inside its expressions -- and
      the second group is what has to be located, in the window the run moved
      through.

      These three are the generic forms of the [cmerge] plumbing above: the
      property is now a parameter, because the window is. *)

  Lemma Forall_cmerge :
    forall (Q : SymTypes.constraint -> Prop) c1 c2,
      Forall Q c1 -> Forall Q c2 -> Forall Q (cmerge c1 c2).
  Proof.
    intros Q c1 c2 H1 H2.
    rewrite Forall_forall in H1, H2 |- *.
    intros c Hc. apply cmerge_In in Hc as [Hc|Hc]; auto.
  Qed.

  Lemma Forall_cmerge_inv :
    forall (Q : SymTypes.constraint -> Prop) c1 c2,
      Forall Q (cmerge c1 c2) -> Forall Q c1 /\ Forall Q c2.
  Proof.
    intros Q c1 c2 H. rewrite Forall_forall in H.
    split; rewrite Forall_forall; intros c Hc; apply H, cmerge_In; tauto.
  Qed.

  Lemma Forall_carried_map_ljoin :
    forall (Q : SymTypes.constraint -> Prop) h ts,
      Forall Q (snd h) ->
      Forall Q (carried ts) ->
      Forall Q (carried (List.map (fun t => ljoin h t) ts)).
  Proof.
    intros Q h ts Hh. induction ts as [|t ts IH]; intros Hts.
    - cbn [List.map carried]. constructor.
    - cbn [List.map]. rewrite carried_cons.
      rewrite carried_cons in Hts.
      apply Forall_cmerge_inv in Hts as (Ht & Htr).
      apply Forall_cmerge; [|exact (IH Htr)].
      rewrite snd_ljoin. apply Forall_cmerge; assumption.
  Qed.

  (** * 7c: the exact target multiset

      7a and 7b say what a target looks like and where it comes from; what
      [signature_good] needs is how *many* times each one occurs.  The answer
      is: once per variable the equation list defines, and once per
      constraint an expression carried -- and [simplify] drops the second
      group wholesale, so the published set is one constraint per output.

      [cmerge] is a sorted union with deduplication, so it is a permutation
      of the append only when the two sides share no constraint.  Every merge
      the generator performs is of that kind: the two sides' targets are
      drawn from disjoint stretches of the fresh state, or one is a declared
      name and the other was minted. *)

  Lemma cmerge_perm :
    forall r1 r2,
      (forall c1 c2, In c1 r1 -> In c2 r2 -> c1 <> c2) ->
      Permutation (cmerge r1 r2) (r1 ++ r2).
  Proof.
    induction r1 as [|x xs IHxs]; intros r2 Hdisj.
    - rewrite cmerge_nil2. reflexivity.
    - induction r2 as [|y ys IHys].
      + rewrite cmerge_nil, app_nil_r. reflexivity.
      + destruct (ccmp x y) eqn:Hc.
        * apply ccmp_eq in Hc. subst y.
          exfalso. eapply Hdisj;
            [left; reflexivity|left; reflexivity|reflexivity].
        * rewrite cmerge1 by exact Hc. simpl.
          apply perm_skip. apply IHxs.
          intros c1 c2 Hc1 Hc2. apply Hdisj; [right|]; assumption.
        * rewrite cmerge2 by exact Hc.
          etransitivity; [apply perm_skip, IHys|].
          { intros c1 c2 Hc1 Hc2. apply Hdisj; [|right]; assumption. }
          apply Permutation_middle.
  Qed.

  (** Two stretches of the fresh state that meet but do not overlap mint
      disjoint sets of names: the generated name determines the state it was
      generated at. *)
  Lemma minted_disjoint :
    forall s s1 s2 d, In d (minted s s1) -> In d (minted s1 s2) -> False.
  Proof.
    intros s s1 s2 d H1 H2.
    apply minted_spec in H1 as (j & _ & Hj & Hdj).
    apply minted_spec in H2 as (k & Hk & _ & Hdk).
    rewrite Hdj in Hdk.
    apply Ids.gensym_injective in Hdk as (_ & ?); subst k.
    exact (Pos.lt_irrefl j (Pos.lt_le_trans j s1 j Hj Hk)).
  Qed.

  Lemma minted_refl : forall s, minted s s = [].
  Proof.
    intros s. unfold minted. now rewrite PeanoNat.Nat.sub_diag.
  Qed.


  (** * The window, by index

      Four facts [signature_scoped] needs and item 7 did not: the window
      splits at any intermediate state, it peels one name at a time, it is
      duplicate-free, and [fresh_idents] produces *exactly* a window rather
      than a subset of one. *)

  Lemma minted_cons :
    forall s s',
      Pos.lt s s' ->
      minted s s' = Ids.gensym Ids.sec s :: minted (Pos.succ s) s'.
  Proof.
    intros s s' Hlt. unfold minted.
    replace (Pos.to_nat s' - Pos.to_nat s)%nat
      with (S (Pos.to_nat s' - Pos.to_nat (Pos.succ s)))%nat
      by (rewrite Pos2Nat.inj_succ; apply Pos2Nat.inj_lt in Hlt; lia).
    reflexivity.
  Qed.

  Lemma minted_split :
    forall s s1 s2 d,
      In d (minted s s2) ->
      In d (minted s s1) \/ In d (minted s1 s2).
  Proof.
    intros s s1 s2 d Hd.
    apply minted_spec in Hd as (j & Hsj & Hjs2 & Hdj).
    destruct (Pos.ltb_spec j s1) as [Hlt|Hge].
    - left. apply minted_spec. exists j. repeat split; assumption.
    - right. apply minted_spec. exists j. repeat split; assumption.
  Qed.

  Lemma sec_span_NoDup : forall k s, NoDup (sec_span s k).
  Proof.
    induction k as [|k IH]; intros s; [constructor|].
    cbn [sec_span]. constructor; [|apply IH].
    intros Hin. apply sec_span_spec in Hin as (j & Hj & _ & Hij).
    apply Ids.gensym_injective in Hij as (_ & ?); subst j.
    exact (Pos.lt_irrefl s
             (Pos.lt_le_trans s (Pos.succ s) s (Pos.lt_succ_diag_r s) Hj)).
  Qed.

  Corollary minted_NoDup : forall s s', NoDup (minted s s').
  Proof. intros s s'. apply sec_span_NoDup. Qed.

  Lemma fresh_idents_window :
    forall n s xs s', fresh_idents n s = OK (xs, s') -> xs = minted s s'.
  Proof.
    induction n as [|n IH]; intros s xs s' H; cbn [fresh_idents] in H.
    - unfold SC.ret in H.
      destruct (OK_pair_inv _ _ _ _ H) as (Hx & ?); subst xs s'.
      symmetry. apply minted_refl.
    - apply sec_bind_inv in H as (x & s1 & Hx & H).
      apply sec_bind_inv in H as (ys & s2 & Hys & Hret).
      unfold SC.ret in Hret.
      destruct (OK_pair_inv _ _ _ _ Hret) as (Hxs & ?); subst xs s2.
      unfold SC.fresh_ident in Hx.
      destruct (OK_pair_inv _ _ _ _ Hx) as (Hxe & ?); subst x s1.
      rewrite (IH (Pos.succ s) ys s' Hys).
      rewrite (minted_cons s s'); [reflexivity|].
      apply Pos.lt_le_trans with (m := Pos.succ s);
        [apply Pos.lt_succ_diag_r
        |exact (fresh_idents_sec_le n ys (Pos.succ s) s' Hys)].
  Qed.


  (** * Eliminating a name that is not there

      [SymTypes.v]'s [simplify_scoped] asks that every eliminated name be the
      target of a constraint.  For a generated set that is too strong: a call
      with no outputs, or a branch with no streams, has its carried set
      discarded by [carried_uniform]/[carried_map_ljoin], so the names its
      run minted appear nowhere at all.  They need no eliminating, and
      [simplify] skips them -- [findST] returns [None] and the step is the
      identity.  So the premise that is both true and sufficient is the
      dichotomy: an eliminated name is a target, or it does not occur. *)

  Definition occurs (d : ident) (cns : list SymTypes.constraint) : Prop :=
    exists c, In c cns /\ In d (constraint_scope c).

  (** [constraints_scoped] wraps a [Forall] in a [Definition], and
      [rewrite Forall_forall in H] does not see through it.  These two cross
      the wrapper by conversion, once, so no proof below has to. *)
  Lemma constraints_scoped_In :
    forall S cns c x,
      constraints_scoped S cns -> In c cns ->
      In x (constraint_scope c) -> In x S.
  Proof.
    intros S cns c x Hsc Hc Hx.
    assert (Forall (constraint_scoped S) cns) as Hf by exact Hsc.
    rewrite Forall_forall in Hf. exact (Hf c Hc x Hx).
  Qed.

  Lemma constraints_scoped_of_In :
    forall S cns,
      (forall c x, In c cns -> In x (constraint_scope c) -> In x S) ->
      constraints_scoped S cns.
  Proof.
    intros S cns H.
    assert (Forall (constraint_scoped S) cns) as Hf
        by (apply Forall_forall; intros c Hc x Hx; exact (H c x Hc Hx)).
    exact Hf.
  Qed.

  Lemma constraints_scoped_self :
    forall cns, constraints_scoped (flat_map constraint_scope cns) cns.
  Proof.
    intros cns. apply constraints_scoped_of_In. intros c x Hc Hx.
    apply in_flat_map. exists c. split; [exact Hc|exact Hx].
  Qed.

  Lemma findST_scoped_self :
    forall cns d st,
      findST cns d = Some st ->
      st_scoped (flat_map constraint_scope cns) st.
  Proof.
    intros cns d st Hf x Hx.
    apply in_flat_map. exists (st, [d]).
    split; [apply find_correct; exact Hf|].
    unfold constraint_scope. cbn [fst]. apply in_or_app. now left.
  Qed.

  Lemma subAll_occurs_mono :
    forall cns d st d',
      findST cns d = Some st ->
      ~ occurs d' cns -> ~ occurs d' (subAll cns d st).
  Proof.
    intros cns d st d' Hf Hno (c & Hc & Hx).
    assert (constraints_scoped (flat_map constraint_scope cns ++ [])
              (subAll cns d st)) as Hsc.
    { eapply (subAll_scoped_elim (flat_map constraint_scope cns) []).
      - eapply constraints_scoped_weaken;
          [|apply constraints_scoped_self].
        intros y Hy. apply in_or_app. now left.
      - eapply st_scoped_weaken;
          [|eapply findST_scoped_self; exact Hf].
        intros y Hy. apply in_or_app. now left. }
    rewrite app_nil_r in Hsc.
    pose proof (constraints_scoped_In _ _ c d' Hsc Hc Hx) as Hin.
    apply in_flat_map in Hin as (c0 & Hc0 & Hx0).
    exact (Hno (ex_intro _ c0 (conj Hc0 Hx0))).
  Qed.

  Theorem simplify_scoped_weak :
    forall scope ds cns,
      NoDup ds ->
      constraints_scoped (scope ++ ds) cns ->
      (forall d, In d ds -> In [d] (List.map snd cns) \/ ~ occurs d cns) ->
      constraints_scoped scope (simplify cns ds).
  Proof.
    intros scope ds. revert scope.
    induction ds as [|d ds IH]; intros scope cns Hnd Hsc Hdefs.
    - rewrite app_nil_r in Hsc. rewrite simplify_nil_eq. exact Hsc.
    - apply NoDup_cons_iff in Hnd as (Hdnin & Hnd).
      rewrite simplify_cons_eq.
      remember (SymTypes.findST cns d) as fo eqn:Hfind.
      destruct fo as [st|]; symmetry in Hfind.
      + apply IH; [exact Hnd| |].
        * assert (Hst : st_scoped (scope ++ d :: ds) st).
          { intros x Hin.
            eapply constraints_scoped_In;
              [exact Hsc|apply find_correct; exact Hfind|].
            unfold constraint_scope. cbn [fst snd].
            apply in_or_app. left. exact Hin. }
          eapply subAll_scoped_elim; [exact Hsc|exact Hst].
        * intros d' Hin'.
          assert (Hne : d' <> d) by (intros ?; subst d'; contradiction).
          destruct (Hdefs d' (in_cons d d' ds Hin')) as [Htgt|Hno].
          -- left. eapply subAll_preserves_other_rhs; [exact Hne|exact Htgt].
          -- right. eapply subAll_occurs_mono; [exact Hfind|exact Hno].
      + apply IH; [exact Hnd| |].
        * assert (Hno : ~ occurs d cns).
          { destruct (Hdefs d (in_eq d ds)) as [Htgt|Hno]; [|exact Hno].
            exfalso. exact (findST_None cns d Hfind Htgt). }
          apply constraints_scoped_of_In. intros c x Hc Hx.
          destruct (in_app_or _ _ _
                      (constraints_scoped_In _ _ c x Hsc Hc Hx)) as [Hs|Hs];
            [apply in_or_app; now left|].
          destruct Hs as [Hs|Hs];
            [exfalso; subst x; exact (Hno (ex_intro _ c (conj Hc Hx)))
            |apply in_or_app; now right].
        * intros d' Hin'. exact (Hdefs d' (in_cons d d' ds Hin')).
  Qed.

  (** [SecLTyping.v]'s [simplify_map_snd] restated here.  Its statement is
      the same one, but elaborated in *this* file: [SymTypes.ST] is
      [list ident] by [Definition], so [@snd ST ST] and
      [@snd ST (list ident)] are convertible without being syntactically
      equal, and a [rewrite] with a fact stated in another file can fail to
      match a goal that prints identically.  [exact] goes through conversion,
      so the restatement costs one line and makes the rewrites below
      reliable. *)
  Lemma simplify_map_snd_here :
    forall ds cns,
      Forall singleton_rhs cns ->
      List.map snd (simplify cns ds) = filter (kept ds) (List.map snd cns).
  Proof. exact simplify_map_snd. Qed.

  (** The target multiset of a constraint list, named so the merges below
      read as one line each. *)
  Definition targets_of (ms : list ident) (cs : list SymTypes.constraint) : Prop :=
    Permutation (List.map snd cs) (List.map (fun d => [d]) ms).

  Lemma targets_of_nil : targets_of [] [].
  Proof. unfold targets_of. reflexivity. Qed.

  Lemma targets_of_perm :
    forall ms ms' cs, Permutation ms ms' -> targets_of ms cs -> targets_of ms' cs.
  Proof.
    intros ms ms' cs Hp H. unfold targets_of in H |- *.
    etransitivity; [exact H|now apply Permutation_map].
  Qed.

  Lemma targets_of_In :
    forall ms cs c,
      targets_of ms cs -> In c cs -> exists d, In d ms /\ snd c = [d].
  Proof.
    intros ms cs c H Hc. unfold targets_of in H.
    assert (In (snd c) (List.map (fun d => [d]) ms)) as Hin.
    { eapply Permutation_in; [exact H|].
      apply in_map_iff. exists c. split; [reflexivity|exact Hc]. }
    apply in_map_iff in Hin as (d & Hd & Hdm).
    exists d. split; [exact Hdm|now rewrite <- Hd].
  Qed.

  Lemma targets_of_app :
    forall ms1 ms2 cs1 cs2,
      targets_of ms1 cs1 -> targets_of ms2 cs2 ->
      targets_of (ms1 ++ ms2) (cs1 ++ cs2).
  Proof.
    intros ms1 ms2 cs1 cs2 H1 H2. unfold targets_of in *.
    rewrite map_app, map_app. now apply Permutation_app.
  Qed.

  (** The merge, which is where the hypothesis is needed: two constraints
      with different targets are different constraints, so nothing is
      deduplicated and the union is the append. *)
  Lemma targets_of_cmerge :
    forall ms1 ms2 cs1 cs2,
      targets_of ms1 cs1 -> targets_of ms2 cs2 ->
      (forall d1 d2, In d1 ms1 -> In d2 ms2 -> d1 <> d2) ->
      targets_of (ms1 ++ ms2) (cmerge cs1 cs2).
  Proof.
    intros ms1 ms2 cs1 cs2 H1 H2 Hd.
    assert (Permutation (cmerge cs1 cs2) (cs1 ++ cs2)) as Hp.
    { apply cmerge_perm. intros c1 c2 Hc1 Hc2.
      destruct (targets_of_In ms1 cs1 c1 H1 Hc1) as (d1 & Hd1 & He1).
      destruct (targets_of_In ms2 cs2 c2 H2 Hc2) as (d2 & Hd2 & He2).
      intros Heq. rewrite Heq, He2 in He1.
      injection He1 as He1. symmetry in He1. exact (Hd d1 d2 Hd1 Hd2 He1). }
    unfold targets_of.
    eapply Permutation_trans; [apply (Permutation_map snd Hp)|].
    exact (targets_of_app ms1 ms2 cs1 cs2 H1 H2).
  Qed.

  (** Joining one head onto every stream of a list.  The head's constraints
      are merged in once per stream, and [cmerge] deduplicates them, so the
      result is the head's set together with the list's -- each once. *)
  Lemma carried_map_ljoin_eq :
    forall h ts,
      ts <> [] ->
      carried (List.map (fun t => ljoin h t) ts) = cmerge (snd h) (carried ts).
  Proof.
    intros h ts. induction ts as [|t ts IH]; intros Hne; [contradiction|].
    destruct ts as [|t2 ts].
    - cbn [List.map]. rewrite !carried_single, snd_ljoin. reflexivity.
    - cbn [List.map] in IH |- *. rewrite carried_cons.
      rewrite IH by (intros HF; discriminate).
      rewrite snd_ljoin, cmerge_assoc, (carried_cons t (t2 :: ts)).
      rewrite (cmerge_shuffle (snd t) (snd h) (carried (t2 :: ts))).
      rewrite cmerge_dedup_l. reflexivity.
  Qed.

  (** Two stretches of the fresh state that do not overlap mint disjoint
      sets, whichever order they are merged in. *)
  Lemma minted_apart :
    forall a b c d x,
      sec_le b c -> In x (minted a b) -> In x (minted c d) -> False.
  Proof.
    intros a b c d x Hbc H1 H2.
    apply minted_spec in H1 as (j & _ & Hj & Hdj).
    apply minted_spec in H2 as (k & Hk & _ & Hdk).
    rewrite Hdj in Hdk.
    apply Ids.gensym_injective in Hdk as (_ & ?); subst k.
    apply (Pos.lt_irrefl j).
    exact (Pos.lt_le_trans j b j Hj (Pos.le_trans b c j Hbc Hk)).
  Qed.

  (** The shape of one merge, which is the step every case of the expression
      induction takes: the two sides were minted over stretches that do not
      overlap, so nothing is deduplicated and the targets append. *)
  Lemma shape_cmerge :
    forall ms1 ms2 cs1 cs2 a b c d ns,
      sec_le b c ->
      targets_of ms1 cs1 -> incl ms1 (minted a b) ->
      targets_of ms2 cs2 -> incl ms2 (minted c d) ->
      incl (minted a b) ns -> incl (minted c d) ns ->
      exists ms, targets_of ms (cmerge cs1 cs2) /\ incl ms ns.
  Proof.
    intros ms1 ms2 cs1 cs2 a b c d ns Hbc H1 Hi1 H2 Hi2 Hn1 Hn2.
    exists (ms1 ++ ms2). split.
    - apply targets_of_cmerge; [exact H1|exact H2|].
      intros d1 d2 Hd1 Hd2 Heq. subst d2.
      exact (minted_apart a b c d d1 Hbc (Hi1 d1 Hd1) (Hi2 d1 Hd2)).
    - intros x Hx. apply in_app_or in Hx as [Hx|Hx];
        [apply Hn1, Hi1, Hx|apply Hn2, Hi2, Hx].
  Qed.


  Section RawTargets.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.

    Definition lexp_carried_singleton (e : exp) : Prop :=
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        SIGPROOFS.singleton_targets (carried ts).

    Definition lexps_carried_singleton (es : list exp) : Prop :=
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        SIGPROOFS.singleton_targets (carried ts).

    Lemma lexps_carried_singleton_intro :
      forall es,
        Forall lexp_carried_singleton es -> lexps_carried_singleton es.
    Proof.
      intros es Hall. induction Hall as [|e es He Hes IH];
        intros ts st st' H.
      - rewrite assign_lexps_nil in H. unfold SC.ret in H. inv H.
        constructor.
      - rewrite assign_lexps_cons in H.
        apply sec_bind_inv in H as (t & s1 & Ht & H).
        apply sec_bind_inv in H as (r & s2 & Hr & Hret).
        unfold SC.ret in Hret. inv Hret.
        rewrite carried_app.
        apply singleton_targets_cmerge;
          [exact (He t st s1 Ht)|exact (IH r s1 st' Hr)].
    Qed.

    Theorem lexp_carried_singleton_all :
      forall e, lexp_carried_singleton e.
    Proof.
      intros e. induction e using exp_ind2;
        intros ts st st' Hgen.
      - (** a constant carries nothing *)
        rewrite assign_lexp_Econst in Hgen. unfold SC.ret in Hgen. inv Hgen.
        cbn [carried lbot snd]. constructor.
      - (** nor a variable *)
        apply assign_lexp_Evar_inv in Hgen as (a0 & _ & Hts & _). subst ts.
        cbn [carried snd]. constructor.
      - (** the unary operator is its operand *)
        exact (IHe ts st st' Hgen).
      - (** the binary one joins its two, each pinned by [single] *)
        rewrite assign_lexp_Ebinop in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (t2 & s2 & Ht2 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s3 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (a2 & s4 & Ha2 & Hret).
        unfold SC.ret in Hret. inv Hret.
        apply single_inv in Ha1 as (? & ?); subst t1 s3.
        apply single_inv in Ha2 as (? & ?); subst t2.
        rewrite carried_single, snd_ljoin.
        apply singleton_targets_cmerge.
        + rewrite <- carried_single. exact (IHe1 [a1] st s1 Ht1).
        + rewrite <- carried_single. exact (IHe2 [a2] s1 s2 Ht2).
      - (** the delay, and the initialised delay: a pointwise join *)
        rewrite assign_lexp_Efby in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        rewrite (ljoin_list_carried ts0 us ts s2 st' Hj).
        apply singleton_targets_cmerge.
        + eapply lexps_carried_singleton_intro; [exact H|exact Hts0].
        + eapply lexps_carried_singleton_intro; [exact H0|exact Hus].
      - rewrite assign_lexp_Earrow in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        rewrite (ljoin_list_carried ts0 us ts s2 st' Hj).
        apply singleton_targets_cmerge.
        + eapply lexps_carried_singleton_intro; [exact H|exact Hts0].
        + eapply lexps_carried_singleton_intro; [exact H0|exact Hus].
      - (** sampling adds a name and no constraint *)
        rewrite assign_lexp_Ewhen in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (g & s2 & Hg & Hret).
        apply find_env_inv in Hg as (_ & ?); subst s2.
        unfold SC.ret in Hret. inv Hret.
        rewrite carried_map_when.
        eapply lexps_carried_singleton_intro; [exact H|exact Hts0].
      - (** the merge, and the conditional, join their two branch lists *)
        destruct a as (tys & cl).
        rewrite assign_lexp_Emerge in Hgen.
        apply sec_bind_inv in Hgen as (g & s1 & Hg & Hgen).
        apply find_env_inv in Hg as (_ & ?); subst s1.
        apply sec_bind_inv in Hgen as (ts0 & s2 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s3 & Hus & Hj).
        rewrite (ljoin_list_carried _ us ts s3 st' Hj).
        apply singleton_targets_cmerge.
        + rewrite carried_map_merge_l.
          eapply lexps_carried_singleton_intro; [exact H|exact Hts0].
        + eapply lexps_carried_singleton_intro; [exact H0|exact Hus].
      - destruct a as (tys & cl).
        rewrite assign_lexp_Eite in Hgen.
        apply sec_bind_inv in Hgen as (t0 & s1 & Ht0 & Hgen).
        apply sec_bind_inv in Hgen as (th & s2 & Hth & Hgen).
        apply single_inv in Hth as (? & ?); subst t0 s2.
        apply sec_bind_inv in Hgen as (ts0 & s3 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s4 & Hus & Hj).
        rewrite (ljoin_list_carried _ us ts s4 st' Hj).
        apply singleton_targets_cmerge.
        + apply singleton_targets_carried_map_ljoin.
          * rewrite <- carried_single. exact (IHe [th] st s1 Ht0).
          * eapply lexps_carried_singleton_intro; [exact H|exact Hts0].
        + eapply lexps_carried_singleton_intro; [exact H0|exact Hus].
      - (** and the call: the instantiated block over what the arguments and
            the reset were carrying *)
        apply assign_lexp_Eapp_inv in Hgen
          as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & _ & Hrst & _ & _ & Hcs & Hts).
        subst ts. rewrite carried_uniform.
        destruct outs as [|o os]; [constructor|].
        apply singleton_targets_cmerge;
          [exact (generate_constraints_singleton_targets sg
                    (List.map fst argts) ckty (fst rstty) (o :: os) cs
                    stc st' Hcs)|].
        apply singleton_targets_cmerge.
        + eapply lexps_carried_singleton_intro; [exact H0|exact Hargs].
        + destruct ro as [e1|].
          * destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg1 & _ & Hr).
            apply single_inv in Hsg1 as (? & ?); subst t1 stb.
            subst rstty. rewrite !snd_ljoin, snd_lvar.
            cbn [snd]. rewrite cmerge_nil, cmerge_nil2.
            rewrite <- carried_single.
            exact (H [a1] sta stm Ht1).
          * destruct Hrst as (Hr & _). subst rstty.
            rewrite snd_lvar. constructor.
    Qed.

    (** The carried component, element by element: membership in one flow
        type's constraints is membership in the list's, so a [singleton_targets]
        for the whole is one for each. *)

    Lemma In_carried :
      forall (ts : list LST) t c,
        In t ts -> In c (snd t) -> In c (carried ts).
    Proof.
      induction ts as [|t0 ts IH]; intros t c Ht Hc; [contradiction|].
      rewrite carried_cons. apply cmerge_In.
      destruct Ht as [Ht|Ht]; [subst t0; now left|right; exact (IH t c Ht Hc)].
    Qed.

    Lemma singleton_targets_carried_elements :
      forall ts,
        SIGPROOFS.singleton_targets (carried ts) ->
        Forall (fun t => SIGPROOFS.singleton_targets (snd t)) ts.
    Proof.
      intros ts H. apply Forall_forall. intros t Ht.
      unfold SIGPROOFS.singleton_targets in H |- *.
      rewrite Forall_forall in H |- *. intros c Hc.
      apply H. exact (In_carried ts t c Ht Hc).
    Qed.

    (** The hoisting rule's own constraint targets the one generated name, and
        the rest is what the flow carried.  Proved through membership rather
        than by unfolding, because [cmerge] with a literal first argument
        reduces into its inner [fix] and then no lemma about [cmerge] matches
        any more. *)
    Lemma singleton_targets_lconstrain :
      forall p b,
        SIGPROOFS.singleton_targets (snd p) ->
        SIGPROOFS.singleton_targets (lconstrain p b).
    Proof.
      intros p b Hp.
      unfold SIGPROOFS.singleton_targets in Hp |- *.
      rewrite Forall_forall in Hp |- *. intros c Hc.
      apply (cmerge_In [(fst p, [b])] (snd p) c) in Hc as [Hc|Hc].
      - destruct Hc as [Hc|[]]; subst c. cbn [snd]. now exists b.
      - exact (Hp c Hc).
    Qed.

    (** And the general rule: its own constraint targets the defined variable,
        over whatever the defining flow carried. *)

    Lemma generate_lvars_constraints_singleton :
      forall ckenv xs bs ts c s s',
        Forall (fun t => SIGPROOFS.singleton_targets (snd t)) ts ->
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        SIGPROOFS.singleton_targets c.
    Proof.
      intros ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' Hts Hgen.
      - destruct bs as [|b bs]; [|destruct ts; cbn in Hgen; discriminate].
        destruct ts; cbn in Hgen; [|discriminate].
        unfold SC.ret in Hgen. inv Hgen. constructor.
      - destruct bs as [|b bs];
          [destruct ts; cbn in Hgen; discriminate|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        inversion Hts as [|t0 ts0 Ht Htr]; subst.
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & ?); subst s'.
        rewrite Hc.
        apply singleton_targets_app; [|exact (IH bs ts rest s1 s2 Htr Hr)].
        apply singleton_targets_lconstrain.
        rewrite snd_ljoin. unfold ambient.
        rewrite snd_ljoin, snd_lvar. cbn [snd].
        rewrite cmerge_nil, cmerge_nil2. exact Ht.
    Qed.

    (** * 7a's dispatch

        Every rule the equation generator has, in turn.  No new idea: each one
        is a [cmerge] or an append of pieces already covered -- an
        instantiated block, what an expression carried, or one
        [lconstrain]. *)

    Corollary assign_lexps_carried_singleton :
      forall es ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        SIGPROOFS.singleton_targets (carried ts).
    Proof.
      intros es. apply lexps_carried_singleton_intro.
      apply Forall_forall. intros e _. apply lexp_carried_singleton_all.
    Qed.

    Lemma generate_lcall_constraint_singleton :
      forall xs f es rstty cs s s',
        SIGPROOFS.singleton_targets (snd rstty) ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros xs f es rstty cs s s' Hrst Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      rewrite Hcs.
      apply singleton_targets_cmerge;
        [exact (generate_constraints_singleton_targets sg (List.map fst argts)
                  ckty (fst rstty) outs cs0 sti s' Hgc)|].
      apply singleton_targets_cmerge;
        [exact (assign_lexps_carried_singleton es argts s sti Hargs)
        |exact Hrst].
    Qed.

    Lemma generate_ldef_constraint_singleton :
      forall ckenv x e cs s s',
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv x e cs s s' Hgen.
      apply generate_ldef_constraint_inv in Hgen
        as (ck & ckty & tf & b & s1 & _ & _ & Hte & _ & _ & Hcs).
      rewrite Hcs.
      change (cmerge [(merge (merge [rst_ty] ckty) (fst tf), [b])] (snd tf))
        with (lconstrain (merge (merge [rst_ty] ckty) (fst tf), snd tf) b).
      apply singleton_targets_lconstrain. cbn [snd].
      rewrite <- (carried_single tf).
      exact (lexp_carried_singleton_all e [tf] s s1 Hte).
    Qed.

    Lemma generate_lgen_constraint_singleton :
      forall ckenv xs es cs s s',
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv xs es cs s s' Hgen.
      unfold generate_lgen_constraint in Hgen.
      apply sec_bind_inv in Hgen as (ts & s1 & Hts & Hgen).
      apply sec_bind_inv in Hgen as (bs & s2 & Hbs & Hlv).
      apply option_to_sec_inv in Hbs as (_ & ?); subst s2.
      eapply generate_lvars_constraints_singleton; [|exact Hlv].
      apply singleton_targets_carried_elements.
      exact (assign_lexps_carried_singleton es ts s s1 Hts).
    Qed.

    Lemma generate_lone_constraint_singleton :
      forall ckenv ys e cs s s',
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv ys e cs s s' Hgen.
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      (** the nine forms an equation can bind directly *)
      1-9: destruct ys as [|x [|y ys]];
        [eapply generate_lgen_constraint_singleton; exact Hgen
        |eapply generate_ldef_constraint_singleton; exact Hgen
        |eapply generate_lgen_constraint_singleton; exact Hgen].
      (** and the call, with or without a reset *)
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc. constructor.
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
        eapply generate_lcall_constraint_singleton; [|exact Hgen].
        rewrite !snd_ljoin, snd_lvar. cbn [snd].
        rewrite cmerge_nil, cmerge_nil2.
        rewrite <- (carried_single a1).
        exact (lexp_carried_singleton_all e1 [a1] s s1 Ht1).
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc. constructor.
      - eapply generate_lcall_constraint_singleton; [|exact Hgen].
        rewrite snd_lvar. constructor.
    Qed.

    Lemma generate_lsplit_constraints_singleton :
      forall ckenv es xs cs s s',
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv es. induction es as [|e es IH]; intros xs cs s s' Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
        rewrite Hc. constructor.
      - rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & _). rewrite Heq.
        apply singleton_targets_app.
        + eapply generate_lone_constraint_singleton; exact Hc.
        + exact (IH (skipn (numstreams e) xs) cr s1 s2 Hcr).
    Qed.

    Lemma generate_leqn_constraint_singleton :
      forall ckenv eqn cs s s',
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv eqn cs s s' Hgen.
      destruct eqn as (xs & es).
      destruct es as [|e [|e2 es2]].
      - (** nothing on the right: the general rule, vacuously *)
        eapply generate_lgen_constraint_singleton; exact Hgen.
      - (** one expression: a call, a single definition, or the general rule *)
        destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                      |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
        1-9: destruct xs as [|x [|y xs]];
          [eapply generate_lgen_constraint_singleton; exact Hgen
          |eapply generate_ldef_constraint_singleton; exact Hgen
          |eapply generate_lgen_constraint_singleton; exact Hgen].
        destruct ro as [e1|]; destruct xs as [|y xs].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
          rewrite Hc. constructor.
        + cbn [generate_leqn_constraint] in Hgen.
          apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
          apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
          apply single_inv in Ha1 as (? & ?); subst t1 s2.
          apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
          apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
          eapply generate_lcall_constraint_singleton; [|exact Hgen].
          rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2.
          rewrite <- (carried_single a1).
          exact (lexp_carried_singleton_all e1 [a1] s s1 Ht1).
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
          rewrite Hc. constructor.
        + eapply generate_lcall_constraint_singleton; [|exact Hgen].
          rewrite snd_lvar. constructor.
      - (** two or more: chunked if one of them is a call *)
        destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            eapply generate_lsplit_constraints_singleton; exact Hgen.
        + destruct e; try destruct o;
            eapply generate_lgen_constraint_singleton; exact Hgen.
    Qed.

    Theorem generate_leqns_constraints_singleton :
      forall ckenv eqs cs s s',
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        SIGPROOFS.singleton_targets cs.
    Proof.
      intros ckenv eqs. induction eqs as [|eqn eqs IH]; intros cs s s' Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc. constructor.
      - rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & _). rewrite Heq.
        apply singleton_targets_app.
        + eapply generate_leqn_constraint_singleton; exact Hc1.
        + exact (IH c2 s1 s2 Hc2).
    Qed.

    (** * 7b, the expression half: a carried target was minted by the run

        Every target of what an expression carries is a name the run minted.
        Stated against an arbitrary superset of the window rather than the
        window itself, because that is what keeps the induction's conclusion
        stable under sub-runs -- the same device
        [assign_lexp_type_clock_closed] uses. *)

    Definition lexp_carried_minted (e : exp) : Prop :=
      forall ts s s' ns,
        incl (minted s s') ns ->
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        Forall (fun c => incl (snd c) ns) (carried ts).

    Lemma lexps_carried_minted_of :
      forall es,
        Forall lexp_carried_minted es ->
        forall ts s s' ns,
          incl (minted s s') ns ->
          assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
          Forall (fun c => incl (snd c) ns) (carried ts).
    Proof.
      intros es Hall. induction Hall as [|e es He Hes IH];
        intros ts s s' ns Hns H.
      - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
          as (? & _ & ?); subst ts. constructor.
      - apply assign_lexps_carried_cons in H
          as (t & r & sa & Ht & Hr & ? & _); subst ts.
        rewrite carried_app. apply Forall_cmerge.
        + apply (He t s sa ns); [|exact Ht].
          apply (minted_incl_sub s s sa s' ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hr|exact Hns].
        + apply (IH r sa s' ns); [|exact Hr].
          apply (minted_incl_sub s sa s' s' ns);
            [eapply assign_lexp_type_sec_le; exact Ht
            |apply sec_le_refl|exact Hns].
    Qed.

    Theorem lexp_carried_minted_all : forall e, lexp_carried_minted e.
    Proof.
      intros e. induction e using exp_ind2;
        intros ts s s' ns Hns Hgen.
      - (** a constant and a variable carry nothing *)
        rewrite assign_lexp_Econst in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hts & _); subst ts.
        cbn [carried lbot snd]. constructor.
      - apply assign_lexp_Evar_inv in Hgen as (a0 & _ & Hts & _). subst ts.
        cbn [carried snd]. constructor.
      - (** the unary operator is its operand *)
        exact (IHe ts s s' ns Hns Hgen).
      - (** the binary one, each operand pinned by [single] *)
        rewrite assign_lexp_Ebinop in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (t2 & s2 & Ht2 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s3 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (a2 & s4 & Ha2 & Hret).
        apply single_inv in Ha1 as (? & ?); subst t1 s3.
        apply single_inv in Ha2 as (? & ?); subst t2 s4.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        rewrite carried_single, snd_ljoin. apply Forall_cmerge.
        + rewrite <- (carried_single a1).
          apply (IHe1 [a1] s s1 ns); [|exact Ht1].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexp_type_sec_le; exact Ht2
            |exact Hns].
        + rewrite <- (carried_single a2).
          apply (IHe2 [a2] s1 s2 ns); [|exact Ht2].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexp_type_sec_le; exact Ht1
            |apply sec_le_refl|exact Hns].
      - (** the two delays: a pointwise join of two lists *)
        rewrite assign_lexp_Efby in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        apply Forall_cmerge.
        + apply (lexps_carried_minted_of e0s H ts0 s s1 ns); [|exact Hts0].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_carried_minted_of es H0 us s1 s2 ns); [|exact Hus].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - rewrite assign_lexp_Earrow in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        apply Forall_cmerge.
        + apply (lexps_carried_minted_of e0s H ts0 s s1 ns); [|exact Hts0].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_carried_minted_of es H0 us s1 s2 ns); [|exact Hus].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - (** sampling adds a name and no constraint *)
        rewrite assign_lexp_Ewhen in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (g & s2 & Hg & Hret).
        apply find_env_inv in Hg as (_ & ?); subst s2.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        rewrite carried_map_when.
        exact (lexps_carried_minted_of es H ts0 s s1 ns Hns Hts0).
      - (** the merge and the conditional *)
        destruct a as (tys & cl).
        rewrite assign_lexp_Emerge in Hgen.
        apply sec_bind_inv in Hgen as (g & s1 & Hg & Hgen).
        apply find_env_inv in Hg as (_ & ?); subst s1.
        apply sec_bind_inv in Hgen as (ts0 & s2 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s3 & Hus & Hj).
        assert (s' = s3) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried _ us ts s3 s3 Hj).
        apply Forall_cmerge.
        + rewrite carried_map_merge_l.
          apply (lexps_carried_minted_of ets H ts0 s s2 ns); [|exact Hts0].
          apply (minted_incl_sub s s s2 s3 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_carried_minted_of efs H0 us s2 s3 ns); [|exact Hus].
          apply (minted_incl_sub s s2 s3 s3 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - destruct a as (tys & cl).
        rewrite assign_lexp_Eite in Hgen.
        apply sec_bind_inv in Hgen as (t0 & s1 & Ht0 & Hgen).
        apply sec_bind_inv in Hgen as (th & s2 & Hth & Hgen).
        apply single_inv in Hth as (? & ?); subst t0 s2.
        apply sec_bind_inv in Hgen as (ts0 & s3 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s4 & Hus & Hj).
        assert (s' = s4) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried _ us ts s4 s4 Hj).
        apply Forall_cmerge.
        + apply Forall_carried_map_ljoin.
          * rewrite <- (carried_single th).
            apply (IHe [th] s s1 ns); [|exact Ht0].
            apply (minted_incl_sub s s s1 s3 ns);
              [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hts0|].
            apply (minted_incl_sub s s s3 s4 ns);
              [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
              |exact Hns].
          * apply (lexps_carried_minted_of ets H ts0 s1 s3 ns); [|exact Hts0].
            apply (minted_incl_sub s1 s1 s3 s4 ns);
              [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus|].
            apply (minted_incl_sub s s1 s4 s4 ns);
              [eapply assign_lexp_type_sec_le; exact Ht0
              |apply sec_le_refl|exact Hns].
        + apply (lexps_carried_minted_of efs H0 us s3 s4 ns); [|exact Hus].
          apply (minted_incl_sub s s3 s4 s4 ns);
            [eapply sec_le_trans;
             [eapply assign_lexp_type_sec_le; exact Ht0
             |eapply assign_lexps_sec_le; exact Hts0]
            |apply sec_le_refl|exact Hns].
      - (** the call: its results are exactly what this run minted *)
        pose proof Hgen as Hgen0.
        apply assign_lexp_Eapp_inv in Hgen
          as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & _ & Hrst & _ & Houts & Hcs & Hts).
        destruct (assign_lexp_Eapp_stages_le G env base_ty rst_ty es ro _
                    s s' sg argts rstty ckty outs cs sta stb stc
                    Hargs Hrst Houts Hcs) as (Hlab & Hlbc & Hlcs).
        assert (sec_le s sta) as Hlsa
            by (eapply assign_lexps_sec_le; exact Hargs).
        assert (sec_le s stb) as Hlsb by (eapply sec_le_trans; eauto).
        subst ts. rewrite carried_uniform.
        destruct outs as [|o os]; [constructor|].
        apply Forall_cmerge.
        + (** the instantiated block's targets are the minted results *)
          assert (incl (o :: os) ns) as Houtsns.
          { eapply incl_tran;
              [eapply fresh_idents_minted; exact Houts|].
            apply (minted_incl_sub s stb stc s' ns);
              [exact Hlsb|exact Hlcs|exact Hns]. }
          pose proof (CALLS.generate_constraints_targets sg
                        (List.map fst argts) ckty (fst rstty) (o :: os) cs
                        stc s' Hcs) as Hsnd.
          apply Forall_forall. intros c Hc.
          assert (In (snd c) (List.map (fun ty => [ty]) (o :: os))) as Hin
              by (rewrite <- Hsnd; apply in_map_iff; exists c;
                  split; [reflexivity|exact Hc]).
          apply in_map_iff in Hin as (d & Hd & Hdo).
          intros z Hz. apply Houtsns.
          assert (In z [d]) as Hz' by (rewrite Hd; exact Hz).
          destruct Hz' as [Hz'|[]]; subst z. exact Hdo.
        + apply Forall_cmerge.
          * apply (lexps_carried_minted_of es H0 argts s sta ns); [|exact Hargs].
            apply (minted_incl_sub s s sta s' ns);
              [apply sec_le_refl
              |eapply sec_le_trans; [exact Hlab|
               eapply sec_le_trans; [exact Hlbc|exact Hlcs]]
              |exact Hns].
          * destruct ro as [e1|].
            -- destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg1 & _ & Hr).
               apply single_inv in Hsg1 as (? & ?); subst t1 stb.
               subst rstty. rewrite !snd_ljoin, snd_lvar.
               cbn [snd]. rewrite cmerge_nil, cmerge_nil2.
               rewrite <- (carried_single a1).
               apply (H [a1] sta stm ns); [|exact Ht1].
               apply (minted_incl_sub s sta stm s' ns);
                 [exact Hlsa
                 |eapply sec_le_trans; [exact Hlbc|exact Hlcs]
                 |exact Hns].
            -- destruct Hrst as (Hr & _). subst rstty.
               rewrite snd_lvar. constructor.
    Qed.

    (** * 7b, the equation level: a target is a defined name or a minted one

        Every rule's own constraint targets a variable the equation defines;
        everything else it emits came from an expression, and so was minted.
        [targets_in] is the two possibilities as one set, which is what lets
        the dispatch be uniform. *)

    Definition targets_in (ds : list ident)
        (cs : list SymTypes.constraint) : Prop :=
      Forall (fun c => incl (snd c) ds) cs.

    Lemma targets_in_incl :
      forall ds ds' cs, incl ds ds' -> targets_in ds cs -> targets_in ds' cs.
    Proof.
      intros ds ds' cs Hincl H. unfold targets_in in H |- *.
      eapply Forall_impl; [|exact H]. intros c Hc.
      eapply incl_tran; [exact Hc|exact Hincl].
    Qed.

    Lemma targets_in_carried_elements :
      forall ns ts,
        targets_in ns (carried ts) ->
        Forall (fun t => targets_in ns (snd t)) ts.
    Proof.
      intros ns ts H. apply Forall_forall. intros t Ht.
      unfold targets_in in H |- *.
      rewrite Forall_forall in H |- *. intros c Hc.
      apply H. exact (In_carried ts t c Ht Hc).
    Qed.

    Lemma generate_lvars_constraints_targets :
      forall ckenv xs bs ts c s s' ns,
        Forall2 (fun x b => Env.find x env = Some b) xs bs ->
        Forall (fun t => targets_in ns (snd t)) ts ->
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        targets_in (CALLS.sec_of env xs ++ ns) c.
    Proof.
      intros ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' ns Hbs Hts Hgen.
      - destruct bs as [|b bs]; [|inversion Hbs].
        destruct ts; cbn in Hgen; [|discriminate].
        unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
        constructor.
      - destruct bs as [|b bs]; [inversion Hbs|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        inversion Hbs as [|x0 b0 xs0 bs0 Hxb Hbsr]; subst.
        inversion Hts as [|t0 ts0 Ht Htr]; subst.
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & ?); subst s'.
        rewrite Hc. unfold targets_in. apply Forall_app. split.
        + (** the rule's own constraint, at the variable it defines *)
          apply Forall_forall. intros cc Hcc.
          apply (cmerge_In [(fst (ljoin (ambient rst_ty ckty) t), [b])]
                   (snd (ljoin (ambient rst_ty ckty) t)) cc) in Hcc
            as [Hcc|Hcc].
          * destruct Hcc as [Hcc|[]]; subst cc. cbn [snd].
            intros z [Hz|[]]; subst z. apply in_or_app. left.
            unfold CALLS.sec_of. apply in_flat_map.
            exists x. split; [now left|rewrite Hxb; now left].
          * rewrite snd_ljoin in Hcc. unfold ambient in Hcc.
            rewrite snd_ljoin, snd_lvar in Hcc. cbn [snd] in Hcc.
            rewrite cmerge_nil, cmerge_nil2 in Hcc.
            unfold targets_in in Ht. rewrite Forall_forall in Ht.
            intros z Hz. apply in_or_app. right. exact (Ht cc Hcc z Hz).
        + (** and the rest, by the induction hypothesis *)
          eapply (targets_in_incl (CALLS.sec_of env xs ++ ns));
            [|exact (IH bs ts rest s1 s2 ns Hbsr Htr Hr)].
          apply incl_app; [|apply incl_appr, incl_refl].
          apply incl_appl. apply sec_of_incl. intros y Hy. now right.
    Qed.

    Lemma targets_in_cmerge :
      forall ds c1 c2,
        targets_in ds c1 -> targets_in ds c2 -> targets_in ds (cmerge c1 c2).
    Proof.
      intros ds c1 c2 H1 H2. unfold targets_in in H1, H2 |- *.
      apply Forall_cmerge; assumption.
    Qed.

    Lemma generate_constraints_targets_in :
      forall sg inp clk rst out cns sa sa' ds,
        incl out ds ->
        generate_constraints sg inp clk rst out sa = OK (cns, sa') ->
        targets_in ds cns.
    Proof.
      intros sg inp clk rst out cns sa sa' ds Hout Hgen.
      pose proof (CALLS.generate_constraints_targets sg inp clk rst out cns
                    sa sa' Hgen) as Hsnd.
      unfold targets_in. apply Forall_forall. intros c Hc.
      assert (In (snd c) (List.map (fun ty => [ty]) out)) as Hin
          by (rewrite <- Hsnd; apply in_map_iff; exists c;
              split; [reflexivity|exact Hc]).
      apply in_map_iff in Hin as (d & Hd & Hdo).
      intros z Hz.
      assert (In z [d]) as Hz' by (rewrite Hd; exact Hz).
      destruct Hz' as [Hz'|[]]; subst z. exact (Hout d Hdo).
    Qed.

    Lemma generate_lcall_constraint_targets :
      forall xs f es rstty cs s s' ns,
        incl (minted s s') ns ->
        targets_in ns (snd rstty) ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env xs ++ ns) cs.
    Proof.
      intros xs f es rstty cs s s' ns Hns Hrst Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      assert (sec_le s sti) as Hlsi
          by (eapply assign_lexps_sec_le; exact Hargs).
      assert (s' = sti) as ?
          by (destruct (state_pure_generate_constraints sg
                          (List.map fst argts) ckty (fst rstty) outs
                          sti sti _ _ Hgc) as (Hp & _); exact Hp).
      subst s'.
      rewrite Hcs. apply targets_in_cmerge.
      - (** the block's targets are the equation's own variables *)
        eapply generate_constraints_targets_in; [|exact Hgc].
        intros d Hd. apply in_or_app. left.
        eapply CALLS.Forall2_in_sec_of;
          [eapply CALLS.mmap_find_env_Forall2; exact Houts|exact Hd].
      - apply targets_in_cmerge.
        + eapply targets_in_incl; [apply incl_appr, incl_refl|].
          assert (Forall lexp_carried_minted es) as Hall
              by (apply Forall_forall; intros e0 _;
                  apply lexp_carried_minted_all).
          exact (lexps_carried_minted_of es Hall argts s sti ns Hns Hargs).
        + eapply targets_in_incl; [apply incl_appr, incl_refl|exact Hrst].
    Qed.

    Lemma generate_ldef_constraint_targets :
      forall ckenv x e cs s s' ns,
        incl (minted s s') ns ->
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env [x] ++ ns) cs.
    Proof.
      intros ckenv x e cs s s' ns Hns Hgen.
      apply generate_ldef_constraint_inv in Hgen
        as (ck & ckty & tf & b & s1 & _ & _ & Hte & Hb & Hs1 & Hcs).
      subst s1. rewrite Hcs.
      change (cmerge [(merge (merge [rst_ty] ckty) (fst tf), [b])] (snd tf))
        with (lconstrain (merge (merge [rst_ty] ckty) (fst tf), snd tf) b).
      unfold lconstrain. apply targets_in_cmerge.
      - constructor; [|constructor]. cbn [snd].
        intros z [Hz|[]]; subst z. apply in_or_app. left.
        unfold CALLS.sec_of. apply in_flat_map.
        exists x. split; [now left|rewrite Hb; now left].
      - cbn [snd]. eapply targets_in_incl; [apply incl_appr, incl_refl|].
        rewrite <- (carried_single tf).
        exact (lexp_carried_minted_all e [tf] s s' ns Hns Hte).
    Qed.

    Lemma generate_lgen_constraint_targets :
      forall ckenv xs es cs s s' ns,
        incl (minted s s') ns ->
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env xs ++ ns) cs.
    Proof.
      intros ckenv xs es cs s s' ns Hns Hgen.
      unfold generate_lgen_constraint in Hgen.
      apply sec_bind_inv in Hgen as (ts & s1 & Hts & Hgen).
      apply sec_bind_inv in Hgen as (bs & s2 & Hbs & Hlv).
      apply option_to_sec_inv in Hbs as (Hbs & ?); subst s2.
      assert (s' = s1) as ?
          by (destruct (state_pure_generate_lvars_constraints env base_ty
                          rst_ty ckenv xs bs ts s1 s1 _ _ Hlv) as (Hp & _);
              exact Hp).
      subst s'.
      eapply generate_lvars_constraints_targets;
        [eapply (get_mappings_Forall2 env xs bs); exact Hbs| |exact Hlv].
      apply targets_in_carried_elements.
      assert (Forall lexp_carried_minted es) as Hall
          by (apply Forall_forall; intros e0 _; apply lexp_carried_minted_all).
      exact (lexps_carried_minted_of es Hall ts s s1 ns Hns Hts).
    Qed.

    Lemma generate_lone_constraint_targets :
      forall ckenv ys e cs s s' ns,
        incl (minted s s') ns ->
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env ys ++ ns) cs.
    Proof.
      intros ckenv ys e cs s s' ns Hns Hgen.
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      1-9: destruct ys as [|x [|y ys]];
        [eapply generate_lgen_constraint_targets; [exact Hns|exact Hgen]
        |eapply generate_ldef_constraint_targets; [exact Hns|exact Hgen]
        |eapply generate_lgen_constraint_targets; [exact Hns|exact Hgen]].
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
        rewrite Hc. constructor.
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
        assert (sec_le s1 s') as Hl1
            by (eapply generate_lcall_constraint_sec_le; exact Hgen).
        eapply generate_lcall_constraint_targets; [| |exact Hgen].
        + apply (minted_incl_sub s s1 s' s' ns);
            [eapply assign_lexp_type_sec_le; exact Ht1
            |apply sec_le_refl|exact Hns].
        + rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2.
          rewrite <- (carried_single a1).
          apply (lexp_carried_minted_all e1 [a1] s s1 ns); [|exact Ht1].
          apply (minted_incl_sub s s s1 s' ns);
            [apply sec_le_refl|exact Hl1|exact Hns].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
        rewrite Hc. constructor.
      - eapply generate_lcall_constraint_targets; [exact Hns| |exact Hgen].
        rewrite snd_lvar. constructor.
    Qed.

    Lemma generate_lsplit_constraints_targets :
      forall ckenv es xs cs s s' ns,
        incl (minted s s') ns ->
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env xs ++ ns) cs.
    Proof.
      intros ckenv es. induction es as [|e es IH];
        intros xs cs s s' ns Hns Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
        rewrite Hc. constructor.
      - rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst s'.
        rewrite Heq. unfold targets_in. apply Forall_app. split.
        + eapply targets_in_incl;
            [|eapply generate_lone_constraint_targets; [|exact Hc]].
          * apply incl_app; [|apply incl_appr, incl_refl].
            apply incl_appl, sec_of_incl. intros y Hy.
            exact (In_firstn_any ident (numstreams e) xs y Hy).
          * apply (minted_incl_sub s s s1 s2 ns);
              [apply sec_le_refl
              |eapply generate_lsplit_constraints_sec_le; exact Hcr
              |exact Hns].
        + eapply targets_in_incl;
            [|eapply (IH (skipn (numstreams e) xs) cr s1 s2 ns); [|exact Hcr]].
          * apply incl_app; [|apply incl_appr, incl_refl].
            apply incl_appl, sec_of_incl. intros y Hy.
            exact (In_skipn_any ident (numstreams e) xs y Hy).
          * apply (minted_incl_sub s s1 s2 s2 ns);
              [eapply generate_lone_constraint_sec_le; exact Hc
              |apply sec_le_refl|exact Hns].
    Qed.

    Lemma generate_leqn_constraint_targets :
      forall ckenv eqn cs s s' ns,
        incl (minted s s') ns ->
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env (fst eqn) ++ ns) cs.
    Proof.
      intros ckenv eqn cs s s' ns Hns Hgen.
      destruct eqn as (xs & es). cbn [fst].
      destruct es as [|e [|e2 es2]].
      - eapply generate_lgen_constraint_targets; [exact Hns|exact Hgen].
      - destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                      |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0
                      |f args ro anns].
        1-9: destruct xs as [|x [|y xs]];
          [eapply generate_lgen_constraint_targets; [exact Hns|exact Hgen]
          |eapply generate_ldef_constraint_targets; [exact Hns|exact Hgen]
          |eapply generate_lgen_constraint_targets; [exact Hns|exact Hgen]].
        destruct ro as [e1|]; destruct xs as [|y xs].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
          rewrite Hc. constructor.
        + cbn [generate_leqn_constraint] in Hgen.
          apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
          apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
          apply single_inv in Ha1 as (? & ?); subst t1 s2.
          apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
          apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
          assert (sec_le s1 s') as Hl1
              by (eapply generate_lcall_constraint_sec_le; exact Hgen).
          eapply generate_lcall_constraint_targets; [| |exact Hgen].
          * apply (minted_incl_sub s s1 s' s' ns);
              [eapply assign_lexp_type_sec_le; exact Ht1
              |apply sec_le_refl|exact Hns].
          * rewrite !snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2.
            rewrite <- (carried_single a1).
            apply (lexp_carried_minted_all e1 [a1] s s1 ns); [|exact Ht1].
            apply (minted_incl_sub s s s1 s' ns);
              [apply sec_le_refl|exact Hl1|exact Hns].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _).
          rewrite Hc. constructor.
        + eapply generate_lcall_constraint_targets; [exact Hns| |exact Hgen].
          rewrite snd_lvar. constructor.
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            eapply generate_lsplit_constraints_targets;
            [exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen].
        + destruct e; try destruct o;
            eapply generate_lgen_constraint_targets;
            [exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen|exact Hns|exact Hgen
            |exact Hns|exact Hgen|exact Hns|exact Hgen].
    Qed.

    Theorem generate_leqns_constraints_targets :
      forall ckenv eqs cs s s' ns,
        incl (minted s s') ns ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        targets_in (CALLS.sec_of env (vars_defined eqs) ++ ns) cs.
    Proof.
      intros ckenv eqs. induction eqs as [|eqn eqs IH];
        intros cs s s' ns Hns Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc. constructor.
      - rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst s'.
        rewrite Heq, vars_defined_cons_eq, sec_of_app.
        unfold targets_in. apply Forall_app. split.
        + eapply targets_in_incl;
            [|eapply generate_leqn_constraint_targets; [|exact Hc1]].
          * apply incl_app;
              [apply incl_appl, incl_appl, incl_refl
              |apply incl_appr, incl_refl].
          * apply (minted_incl_sub s s s1 s2 ns);
              [apply sec_le_refl
              |eapply generate_leqns_constraints_sec_le; exact Hc2
              |exact Hns].
        + eapply targets_in_incl;
            [|eapply (IH c2 s1 s2 ns); [|exact Hc2]].
          * apply incl_app;
              [apply incl_appl, incl_appr, incl_refl
              |apply incl_appr, incl_refl].
          * apply (minted_incl_sub s s1 s2 s2 ns);
              [eapply generate_leqn_constraint_sec_le; exact Hc1
              |apply sec_le_refl|exact Hns].
    Qed.


    (** 7a and 7b together already fix the multiset: if every constraint of a
        list targets one name, and every such name lies in [ns], then reading
        the targets off in order gives the multiset, and it lies in [ns].  So
        the expression level needs no induction of its own here -- all the
        counting that is left to do is at the equation level, where a defined
        variable must be targeted exactly once. *)
    Lemma shape_of_singleton_minted :
      forall cs ns,
        SIGPROOFS.singleton_targets cs ->
        Forall (fun c => incl (snd c) ns) cs ->
        exists ms, targets_of ms cs /\ incl ms ns.
    Proof.
      intros cs ns Hs Hm.
      unfold SIGPROOFS.singleton_targets in Hs.
      rewrite Forall_forall in Hs. rewrite Forall_forall in Hm.
      revert Hs Hm. induction cs as [|c cs IH]; intros Hs Hm.
      - exists []. split; [apply targets_of_nil|intros ? []].
      - destruct (Hs c (in_eq c cs)) as (d & Hd).
        assert (incl (snd c) ns) as Hc by (exact (Hm c (in_eq c cs))).
        destruct (IH (fun y Hy => Hs y (in_cons c y cs Hy))
                     (fun y Hy => Hm y (in_cons c y cs Hy)))
          as (ms & Hms & Hims).
        destruct c as (lhs, rhs). cbn [snd] in Hd, Hc. subst rhs.
        exists (d :: ms). split.
        + unfold targets_of. cbn [List.map snd].
          apply perm_skip. exact Hms.
        + intros z [Hz|Hz]; [subst z; apply Hc; now left|exact (Hims z Hz)].
    Qed.

    Corollary lexp_carried_shape :
      forall e ts s s' ns,
        incl (minted s s') ns ->
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        exists ms, targets_of ms (carried ts) /\ incl ms ns.
    Proof.
      intros e ts s s' ns Hns Hgen. apply shape_of_singleton_minted.
      - exact (lexp_carried_singleton_all e ts s s' Hgen).
      - exact (lexp_carried_minted_all e ts s s' ns Hns Hgen).
    Qed.

    Corollary lexps_carried_shape :
      forall es ts s s' ns,
        incl (minted s s') ns ->
        assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
        exists ms, targets_of ms (carried ts) /\ incl ms ns.
    Proof.
      intros es ts s s' ns Hns Hgen. apply shape_of_singleton_minted.
      - exact (assign_lexps_carried_singleton es ts s s' Hgen).
      - assert (Forall lexp_carried_minted es) as Hall
            by (apply Forall_forall; intros e0 _; apply lexp_carried_minted_all).
        exact (lexps_carried_minted_of es Hall ts s s' ns Hns Hgen).
    Qed.

    (** * 7c, the equation level: one constraint per defined variable

        The counting argument.  A rule's own constraint targets the variable
        it defines, and [lconstrain] merges it onto what the flow carried --
        a merge that deduplicates nothing, because a declared security name
        is never one the generator minted.  That separation is the premise
        [Hsep] below; the naming pass supplies it at the program level. *)

    Lemma Forall2_sec_of :
      forall xs bs,
        Forall2 (fun x b => Env.find x env = Some b) xs bs ->
        CALLS.sec_of env xs = bs.
    Proof.
      induction 1 as [|x b xs bs Hxb Hr IH]; [reflexivity|].
      unfold CALLS.sec_of. simpl. rewrite Hxb.
      simpl. f_equal. exact IH.
    Qed.

    Lemma Forall2_env_image :
      forall xs bs b,
        Forall2 (fun x b => Env.find x env = Some b) xs bs ->
        In b bs -> exists x, Env.find x env = Some b.
    Proof.
      induction 1 as [|x b0 xs bs Hxb Hr IH]; intros Hin; [contradiction|].
      destruct Hin as [Hin|Hin]; [subst b0; now exists x|exact (IH Hin)].
    Qed.

    Lemma shape_lconstrain :
      forall p b ms ns,
        targets_of ms (snd p) -> incl ms ns -> ~ In b ns ->
        targets_of (b :: ms) (lconstrain p b).
    Proof.
      intros p b ms ns Hm Hi Hb.
      unfold lconstrain.
      apply (targets_of_cmerge [b] ms); [|exact Hm|].
      - unfold targets_of. simpl. reflexivity.
      - intros d1 d2 [Hd1|[]] Hd2 Heq; subst d1 d2.
        exact (Hb (Hi _ Hd2)).
    Qed.

    Lemma perm_mid3 :
      forall {A : Type} (m bs ms : list A),
        Permutation (m ++ bs ++ ms) (bs ++ m ++ ms).
    Proof.
      intros A m bs ms. rewrite !app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    Qed.

    Lemma perm_app4 :
      forall {A : Type} (a b c d : list A),
        Permutation ((a ++ b) ++ c ++ d) ((a ++ c) ++ b ++ d).
    Proof.
      intros A a b c d. rewrite <- (app_assoc a b (c ++ d)).
      rewrite <- (app_assoc a c (b ++ d)).
      apply Permutation_app_head. apply perm_mid3.
    Qed.

    Lemma generate_lvars_constraints_shape :
      forall ckenv xs bs ts c s s' ns,
        Forall2 (fun x b => Env.find x env = Some b) xs bs ->
        SIGPROOFS.singleton_targets (carried ts) ->
        Forall (fun c => incl (snd c) ns) (carried ts) ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        exists ms, targets_of (bs ++ ms) c /\ incl ms ns.
    Proof.
      intros ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' ns Hbs Hsg Hmt Hsep Hgen.
      - destruct bs as [|b bs]; [|inversion Hbs].
        destruct ts; cbn in Hgen; [|discriminate].
        unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
        exists []. split; [apply targets_of_nil|intros ? []].
      - destruct bs as [|b bs]; [inversion Hbs|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        inversion Hbs as [|x0 b0 xs0 bs0 Hxb Hbsr]; subst.
        rewrite carried_cons in Hsg, Hmt.
        apply singleton_targets_cmerge_inv in Hsg as (Hsgt & Hsgr).
        apply Forall_cmerge_inv in Hmt as (Hmtt & Hmtr).
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & ?); subst s'.
        rewrite Hc.
        destruct (shape_of_singleton_minted (snd t) ns Hsgt Hmtt)
          as (m & Hm & Hi).
        destruct (IH bs ts rest s1 s2 ns Hbsr Hsgr Hmtr Hsep Hr)
          as (ms & Hms & Hims).
        exists (m ++ ms). split; [|apply incl_app; [exact Hi|exact Hims]].
        eapply targets_of_perm;
          [apply perm_skip, (perm_mid3 m bs ms)|].
        apply (targets_of_app (b :: m) (bs ++ ms)
                 (lconstrain (ljoin (ambient rst_ty ckty) t) b) rest);
          [|exact Hms].
        apply (shape_lconstrain _ b m ns); [|exact Hi|].
        + rewrite snd_ljoin. unfold ambient.
          rewrite snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hm.
        + exact (Hsep x b Hxb).
    Qed.


    Lemma generate_lcall_constraint_shape :
      forall xs f es rstty cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        SIGPROOFS.singleton_targets (snd rstty) ->
        targets_in ns (snd rstty) ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env xs ++ ms) cs /\ incl ms ns.
    Proof.
      intros xs f es rstty cs s s' ns Hns Hsep Hrs Hrt Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      assert (s' = sti) as ?
          by (destruct (state_pure_generate_constraints sg
                          (List.map fst argts) ckty (fst rstty) outs
                          sti sti _ _ Hgc) as (Hp & _); exact Hp).
      subst s'.
      assert (Forall2 (fun x b => Env.find x env = Some b) xs outs) as Hf2
          by (eapply CALLS.mmap_find_env_Forall2; exact Houts).
      rewrite Hcs, (Forall2_sec_of xs outs Hf2).
      assert (targets_of outs cs0) as Hm0.
      { unfold targets_of.
        rewrite (CALLS.generate_constraints_targets sg (List.map fst argts)
                   ckty (fst rstty) outs cs0 sti sti Hgc).
        reflexivity. }
      assert (exists ms, targets_of ms (cmerge (carried argts) (snd rstty))
                         /\ incl ms ns) as (ms & Hm & Hi).
      { apply shape_of_singleton_minted.
        - apply singleton_targets_cmerge;
            [exact (assign_lexps_carried_singleton es argts s sti Hargs)
            |exact Hrs].
        - apply Forall_cmerge; [|exact Hrt].
          assert (Forall lexp_carried_minted es) as Hall
              by (apply Forall_forall; intros e0 _;
                  apply lexp_carried_minted_all).
          exact (lexps_carried_minted_of es Hall argts s sti ns Hns Hargs). }
      exists ms. split; [|exact Hi].
      apply (targets_of_cmerge outs ms); [exact Hm0|exact Hm|].
      intros d1 d2 Hd1 Hd2 Heq. subst d2.
      destruct (Forall2_env_image xs outs d1 Hf2 Hd1) as (y & Hy).
      exact (Hsep y d1 Hy (Hi d1 Hd2)).
    Qed.

    Lemma generate_ldef_constraint_shape :
      forall ckenv x e cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env [x] ++ ms) cs /\ incl ms ns.
    Proof.
      intros ckenv x e cs s s' ns Hns Hsep Hgen.
      apply generate_ldef_constraint_inv in Hgen
        as (ck & ckty & tf & b & s1 & _ & _ & Hte & Hb & Hs1 & Hcs).
      subst s1. rewrite Hcs.
      change (cmerge [(merge (merge [rst_ty] ckty) (fst tf), [b])] (snd tf))
        with (lconstrain (merge (merge [rst_ty] ckty) (fst tf), snd tf) b).
      assert (exists m, targets_of m (snd tf) /\ incl m ns) as (m & Hm & Hi).
      { apply shape_of_singleton_minted.
        - rewrite <- (carried_single tf).
          exact (lexp_carried_singleton_all e [tf] s s' Hte).
        - rewrite <- (carried_single tf).
          exact (lexp_carried_minted_all e [tf] s s' ns Hns Hte). }
      assert (CALLS.sec_of env [x] = [b]) as Hso
          by (unfold CALLS.sec_of; simpl; rewrite Hb; reflexivity).
      rewrite Hso. exists m. split; [|exact Hi].
      apply (shape_lconstrain
               (merge (merge [rst_ty] ckty) (fst tf), snd tf) b m ns Hm Hi).
      exact (Hsep x b Hb).
    Qed.

    Lemma generate_lgen_constraint_shape :
      forall ckenv xs es cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env xs ++ ms) cs /\ incl ms ns.
    Proof.
      intros ckenv xs es cs s s' ns Hns Hsep Hgen.
      unfold generate_lgen_constraint in Hgen.
      apply sec_bind_inv in Hgen as (ts & s1 & Hts & Hgen).
      apply sec_bind_inv in Hgen as (bs & s2 & Hbs & Hlv).
      apply option_to_sec_inv in Hbs as (Hbs & ?); subst s2.
      assert (s' = s1) as ?
          by (destruct (state_pure_generate_lvars_constraints env base_ty
                          rst_ty ckenv xs bs ts s1 s1 _ _ Hlv) as (Hp & _);
              exact Hp).
      subst s'.
      assert (Forall2 (fun x b => Env.find x env = Some b) xs bs) as Hf2
          by (eapply (get_mappings_Forall2 env xs bs); exact Hbs).
      rewrite (Forall2_sec_of xs bs Hf2).
      eapply generate_lvars_constraints_shape;
        [exact Hf2| | |exact Hsep|exact Hlv].
      - exact (assign_lexps_carried_singleton es ts s s1 Hts).
      - assert (Forall lexp_carried_minted es) as Hall
            by (apply Forall_forall; intros e0 _;
                apply lexp_carried_minted_all).
        exact (lexps_carried_minted_of es Hall ts s s1 ns Hns Hts).
    Qed.

    Lemma generate_lone_constraint_shape :
      forall ckenv ys e cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env ys ++ ms) cs /\ incl ms ns.
    Proof.
      intros ckenv ys e cs s s' ns Hns Hsep Hgen.
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      1-9: destruct ys as [|x [|y ys]];
        [eapply generate_lgen_constraint_shape; [exact Hns|exact Hsep|exact Hgen]
        |eapply generate_ldef_constraint_shape; [exact Hns|exact Hsep|exact Hgen]
        |eapply generate_lgen_constraint_shape;
           [exact Hns|exact Hsep|exact Hgen]].
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
        exists []. split; [apply targets_of_nil|intros ? []].
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
        assert (sec_le s1 s') as Hl1
            by (eapply generate_lcall_constraint_sec_le; exact Hgen).
        eapply generate_lcall_constraint_shape; [| | | |exact Hgen].
        + apply (minted_incl_sub s s1 s' s' ns);
            [eapply assign_lexp_type_sec_le; exact Ht1
            |apply sec_le_refl|exact Hns].
        + exact Hsep.
        + rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2.
          rewrite <- (carried_single a1).
          exact (lexp_carried_singleton_all e1 [a1] s s1 Ht1).
        + rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2.
          rewrite <- (carried_single a1).
          apply (lexp_carried_minted_all e1 [a1] s s1 ns); [|exact Ht1].
          apply (minted_incl_sub s s s1 s' ns);
            [apply sec_le_refl|exact Hl1|exact Hns].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
        exists []. split; [apply targets_of_nil|intros ? []].
      - eapply generate_lcall_constraint_shape;
          [exact Hns|exact Hsep| | |exact Hgen];
          rewrite snd_lvar; constructor.
    Qed.

    Lemma generate_lsplit_constraints_shape :
      forall ckenv es xs cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        length xs = length (LSyn.annots es) ->
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env xs ++ ms) cs /\ incl ms ns.
    Proof.
      intros ckenv es. induction es as [|e es IH];
        intros xs cs s s' ns Hns Hsep Hlen Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
        assert (xs = []) as ?
            by (apply length_zero_iff_nil; rewrite Hlen; reflexivity).
        subst xs.
        exists []. split; [apply targets_of_nil|intros ? []].
      - rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst s'.
        rewrite Heq.
        assert (length (skipn (numstreams e) xs) = length (LSyn.annots es))
          as Hls.
        { rewrite skipn_length, Hlen.
          unfold LSyn.annots. cbn [flat_map]. rewrite app_length.
          rewrite length_annot_numstreams. lia. }
        assert (sec_le s s1) as Hla
            by (eapply generate_lone_constraint_sec_le; exact Hc).
        assert (sec_le s1 s2) as Hlb
            by (eapply generate_lsplit_constraints_sec_le; exact Hcr).
        destruct (generate_lone_constraint_shape ckenv
                    (firstn (numstreams e) xs) e c s s1 ns
                    (minted_incl_sub s s s1 s2 ns (sec_le_refl s) Hlb Hns)
                    Hsep Hc)
          as (ms1 & Hm1 & Hi1).
        destruct (IH (skipn (numstreams e) xs) cr s1 s2 ns
                    (minted_incl_sub s s1 s2 s2 ns Hla (sec_le_refl s2) Hns)
                    Hsep Hls Hcr)
          as (ms2 & Hm2 & Hi2).
        assert (CALLS.sec_of env xs
                = CALLS.sec_of env (firstn (numstreams e) xs)
                  ++ CALLS.sec_of env (skipn (numstreams e) xs)) as Hsplit
            by (rewrite <- sec_of_app, firstn_skipn; reflexivity).
        rewrite Hsplit.
        exists (ms1 ++ ms2). split; [|apply incl_app; [exact Hi1|exact Hi2]].
        eapply targets_of_perm; [apply perm_app4|].
        apply targets_of_app; [exact Hm1|exact Hm2].
    Qed.

    Lemma generate_leqn_constraint_shape :
      forall ckenv eqn cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        length (fst eqn) = length (LSyn.annots (snd eqn)) ->
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env (fst eqn) ++ ms) cs
                   /\ incl ms ns.
    Proof.
      intros ckenv eqn cs s s' ns Hns Hsep Hlen Hgen.
      destruct eqn as (xs & es). cbn [fst snd] in Hlen |- *.
      destruct es as [|e [|e2 es2]].
      - eapply generate_lgen_constraint_shape;
          [exact Hns|exact Hsep|exact Hgen].
      - destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                      |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0
                      |f args ro anns].
        1-9: destruct xs as [|x [|y xs]];
          [eapply generate_lgen_constraint_shape;
             [exact Hns|exact Hsep|exact Hgen]
          |eapply generate_ldef_constraint_shape;
             [exact Hns|exact Hsep|exact Hgen]
          |eapply generate_lgen_constraint_shape;
             [exact Hns|exact Hsep|exact Hgen]].
        destruct ro as [e1|]; destruct xs as [|y xs].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
          exists []. split; [apply targets_of_nil|intros ? []].
        + cbn [generate_leqn_constraint] in Hgen.
          apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
          apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
          apply single_inv in Ha1 as (? & ?); subst t1 s2.
          apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
          apply option_to_sec_inv in Hrck as (_ & ?); subst s3.
          assert (sec_le s1 s') as Hl1
              by (eapply generate_lcall_constraint_sec_le; exact Hgen).
          eapply generate_lcall_constraint_shape; [| | | |exact Hgen].
          * apply (minted_incl_sub s s1 s' s' ns);
              [eapply assign_lexp_type_sec_le; exact Ht1
              |apply sec_le_refl|exact Hns].
          * exact Hsep.
          * rewrite !snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2.
            rewrite <- (carried_single a1).
            exact (lexp_carried_singleton_all e1 [a1] s s1 Ht1).
          * rewrite !snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2.
            rewrite <- (carried_single a1).
            apply (lexp_carried_minted_all e1 [a1] s s1 ns); [|exact Ht1].
            apply (minted_incl_sub s s s1 s' ns);
              [apply sec_le_refl|exact Hl1|exact Hns].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _). rewrite Hc.
          exists []. split; [apply targets_of_nil|intros ? []].
        + eapply generate_lcall_constraint_shape;
            [exact Hns|exact Hsep| | |exact Hgen];
            rewrite snd_lvar; constructor.
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            (eapply generate_lsplit_constraints_shape;
             [exact Hns|exact Hsep|exact Hlen|exact Hgen]).
        + destruct e; try destruct o;
            (eapply generate_lgen_constraint_shape;
             [exact Hns|exact Hsep|exact Hgen]).
    Qed.

    (** * 7c, assembled: the raw constraint set, name by name

        One constraint per variable the equation list defines, and the rest
        targeting names the run minted.  This is the shape [signature_good]
        needs: [simplify] drops the second group -- every occurrence of it --
        and what is left is one constraint per output. *)
    Theorem generate_leqns_constraints_shape :
      forall ckenv eqs cs s s' ns,
        incl (minted s s') ns ->
        (forall x b, Env.find x env = Some b -> ~ In b ns) ->
        Forall (fun eq => length (fst eq) = length (LSyn.annots (snd eq))) eqs ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        exists ms, targets_of (CALLS.sec_of env (vars_defined eqs) ++ ms) cs
                   /\ incl ms ns.
    Proof.
      intros ckenv eqs. induction eqs as [|eqn eqs IH];
        intros cs s s' ns Hns Hsep Hl Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc.
        exists []. split; [apply targets_of_nil|intros ? []].
      - assert (length (fst eqn) = length (LSyn.annots (snd eqn))) as Hle
            by (rewrite Forall_forall in Hl; apply Hl; now left).
        assert (Forall (fun eq => length (fst eq)
                                  = length (LSyn.annots (snd eq))) eqs) as Hlr
            by (rewrite Forall_forall in Hl |- *;
                intros y Hy; apply Hl; now right).
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst s'.
        assert (sec_le s s1) as Hla
            by (eapply generate_leqn_constraint_sec_le; exact Hc1).
        assert (sec_le s1 s2) as Hlb
            by (eapply generate_leqns_constraints_sec_le; exact Hc2).
        destruct (generate_leqn_constraint_shape ckenv eqn c1 s s1 ns
                    (minted_incl_sub s s s1 s2 ns (sec_le_refl s) Hlb Hns)
                    Hsep Hle Hc1)
          as (ms1 & Hm1 & Hi1).
        destruct (IH c2 s1 s2 ns
                    (minted_incl_sub s s1 s2 s2 ns Hla (sec_le_refl s2) Hns)
                    Hsep Hlr Hc2)
          as (ms2 & Hm2 & Hi2).
        rewrite Heq, vars_defined_cons_eq, sec_of_app.
        exists (ms1 ++ ms2). split; [|apply incl_app; [exact Hi1|exact Hi2]].
        eapply targets_of_perm; [apply perm_app4|].
        apply targets_of_app; [exact Hm1|exact Hm2].
    Qed.


    Lemma NoDup_map_singleton :
      forall (l : list ident), NoDup l -> NoDup (List.map (fun d => [d]) l).
    Proof.
      induction 1 as [|x l Hx Hnd IH]; [constructor|].
      cbn [List.map]. constructor; [|exact IH].
      intros Hin. apply in_map_iff in Hin as (d & Hd & Hdl).
      injection Hd as Hd. subst d. exact (Hx Hdl).
    Qed.

    Lemma NoDup_filter_list :
      forall {A : Type} (f : A -> bool) (l : list A),
        NoDup l -> NoDup (filter f l).
    Proof.
      intros A f l H. induction H as [|x l Hx Hnd IH]; [constructor|].
      cbn [filter]. destruct (f x); [|exact IH].
      constructor; [|exact IH].
      intros Hin. apply filter_In in Hin as (Hin & _). exact (Hx Hin).
    Qed.

    Lemma generate_leqns_constraints_len1 :
      forall ckenv eqs cs s s',
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        Forall (fun c => List.length (snd c) = 1%nat) cs.
    Proof.
      intros ckenv eqs cs s s' Hgen.
      pose proof (generate_leqns_constraints_singleton ckenv eqs cs s s' Hgen)
        as Hsing.
      unfold SIGPROOFS.singleton_targets in Hsing.
      rewrite Forall_forall in Hsing. apply Forall_forall. intros c Hc.
      destruct (Hsing c Hc) as (b & Hb).
      destruct c as (lhs, rhs). cbn [snd] in Hb |- *.
      rewrite Hb. reflexivity.
    Qed.

    Lemma kept_spec : forall ds d, kept ds [d] = true <-> ~ In d ds.
    Proof.
      intros ds d. unfold kept. split.
      - intros Hk Hin.
        assert (existsb (fun d0 => ident_eqb d d0) ds = true) as HT
            by (apply existsb_exists; exists d;
                split; [exact Hin|apply ident_eqb_refl]).
        rewrite HT in Hk. discriminate Hk.
      - intros Hin.
        destruct (existsb (fun d0 => ident_eqb d d0) ds) eqn:He;
          [|reflexivity].
        exfalso. apply existsb_exists in He as (y & Hy & Heq).
        apply ident_eqb_eq in Heq. subst y. exact (Hin Hy).
    Qed.

    (** * Item 7, the conclusion: the published constraint set

        Signature generation collapses before simplifying -- it must, because
        a Lustre equation can emit two constraints on the same target and
        [simplify] assumes it does not (see the correction in the plan).
        After the collapse the targets are distinct, so the set of them
        determines the multiset; [simplify] then drops every target in
        [locals ++ minted], and what is left is one constraint per output,
        which is [signature_good]'s second half. *)
    Theorem generate_leqns_constraints_published :
      forall ckenv eqs cs s s' locals out,
        (forall x b, Env.find x env = Some b -> ~ In b (minted s s')) ->
        Forall (fun eq => length (fst eq) = length (LSyn.annots (snd eq))) eqs ->
        Permutation (CALLS.sec_of env (vars_defined eqs)) (locals ++ out) ->
        NoDup (locals ++ out) ->
        (forall o, In o out -> exists x, Env.find x env = Some o) ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        targets_of out (simplify (collapse cs) (locals ++ minted s s')).
    Proof.
      intros ckenv eqs cs s s' locals out Hsep Hl Hperm Hnd Hout Hgen.
      destruct (generate_leqns_constraints_shape ckenv eqs cs s s'
                  (minted s s') (incl_refl _) Hsep Hl Hgen)
        as (ms & Hm & Hi).
      pose proof (generate_leqns_constraints_len1 ckenv eqs cs s s' Hgen)
        as Hlen1.
      destruct (collapse_wf cs Hlen1) as (Hndc & Hlenc).
      assert (Forall singleton_rhs (collapse cs)) as Hsingc.
      { rewrite Forall_forall in Hlenc. apply Forall_forall.
        intros c Hc. specialize (Hlenc c Hc).
        destruct c as (lhs, rhs). cbn [snd] in Hlenc |- *.
        destruct rhs as [|b [|? ?]];
          [discriminate Hlenc|now exists b|discriminate Hlenc]. }
      unfold targets_of.
      rewrite (simplify_map_snd_here (locals ++ minted s s') (collapse cs)
                 Hsingc).
      apply NoDup_Permutation.
      - apply NoDup_filter_list. exact Hndc.
      - apply NoDup_map_singleton. eapply NoDup_app_r; exact Hnd.
      - intros r. rewrite filter_In, collapse_rhs_in. split.
        + intros (Hin & Hk).
          assert (In r (List.map (fun d => [d])
                          (CALLS.sec_of env (vars_defined eqs) ++ ms))) as Hin'
              by (eapply Permutation_in; [exact Hm|exact Hin]).
          apply in_map_iff in Hin' as (d & Hd & Hdin). subst r.
          apply kept_spec in Hk.
          apply in_map_iff. exists d. split; [reflexivity|].
          apply in_app_or in Hdin as [Hdin|Hdin].
          * assert (In d (locals ++ out)) as Hdlo
                by (eapply Permutation_in; [exact Hperm|exact Hdin]).
            apply in_app_or in Hdlo as [Hdlo|Hdlo]; [|exact Hdlo].
            exfalso. apply Hk, in_or_app. now left.
          * exfalso. apply Hk, in_or_app. right. exact (Hi d Hdin).
        + intros Hin. apply in_map_iff in Hin as (o & Ho & Hoin). subst r.
          split.
          * eapply Permutation_in; [apply Permutation_sym; exact Hm|].
            apply in_map_iff. exists o. split; [reflexivity|].
            apply in_or_app. left.
            eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
            apply in_or_app. now right.
          * apply kept_spec. intros Hin.
            apply in_app_or in Hin as [Hin|Hin].
            -- exact (NoDup_app_In o locals out Hnd Hin Hoin).
            -- destruct (Hout o Hoin) as (y & Hy). exact (Hsep y o Hy Hin).
    Qed.

    (** And the first half, which the collapse makes immediate. *)
    Corollary generate_leqns_constraints_published_wf :
      forall ckenv eqs cs s s' locals out,
        (forall x b, Env.find x env = Some b -> ~ In b (minted s s')) ->
        Forall (fun eq => length (fst eq) = length (LSyn.annots (snd eq))) eqs ->
        Permutation (CALLS.sec_of env (vars_defined eqs)) (locals ++ out) ->
        NoDup (locals ++ out) ->
        (forall o, In o out -> exists x, Env.find x env = Some o) ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        wf_constraints (simplify (collapse cs) (locals ++ minted s s'))
        /\ Permutation
             (List.map snd (simplify (collapse cs) (locals ++ minted s s')))
             (List.map (fun ty => [ty]) out).
    Proof.
      intros ckenv eqs cs s s' locals out Hsep Hl Hperm Hnd Hout Hgen.
      split.
      - apply simplify_wf, collapse_wf.
        exact (generate_leqns_constraints_len1 ckenv eqs cs s s' Hgen).
      - exact (generate_leqns_constraints_published ckenv eqs cs s s'
                 locals out Hsep Hl Hperm Hnd Hout Hgen).
    Qed.


    (** * Declared, or carried as a target

        Every name a generated type or carried constraint mentions is either
        *declared* -- a program variable's security name, or one of the two
        auxiliary levels -- or the target of a constraint the flow carries.
        That is the dichotomy [simplify_scoped_weak] needs: a minted name is
        not declared, so if it occurs at all it is a target.  It also
        discharges Leg U's three [*_scoped_upto] hypotheses, since a carried
        target lies in the run's window.

        Scoping is membership, not multiplicity, so [cmerge]'s deduplication
        costs nothing here and every case is a widening. *)

    Definition tgt_names (cs : list SymTypes.constraint) : list ident :=
      flat_map snd cs.

    Lemma tgt_names_cmerge_l :
      forall c1 c2, incl (tgt_names c1) (tgt_names (cmerge c1 c2)).
    Proof.
      intros c1 c2 d Hd. unfold tgt_names in Hd |- *.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      apply in_flat_map. exists c. split; [apply cmerge_In; now left|exact Hdc].
    Qed.

    Lemma tgt_names_cmerge_r :
      forall c1 c2, incl (tgt_names c2) (tgt_names (cmerge c1 c2)).
    Proof.
      intros c1 c2 d Hd. unfold tgt_names in Hd |- *.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      apply in_flat_map. exists c. split; [apply cmerge_In; now right|exact Hdc].
    Qed.

    Lemma incl_decl_tgt_raw :
      forall decl (X Y : list ident),
        incl X Y -> incl (decl ++ X) (decl ++ Y).
    Proof.
      intros decl X Y Hi d Hd.
      apply in_app_or in Hd as [Hd|Hd];
        [apply in_or_app; now left|apply in_or_app; right; exact (Hi d Hd)].
    Qed.

    Lemma incl_decl_tgt :
      forall decl cs1 cs2,
        incl (tgt_names cs1) (tgt_names cs2) ->
        incl (decl ++ tgt_names cs1) (decl ++ tgt_names cs2).
    Proof.
      intros decl cs1 cs2 Hi d Hd.
      apply in_app_or in Hd as [Hd|Hd];
        [apply in_or_app; now left|apply in_or_app; right; exact (Hi d Hd)].
    Qed.

    Lemma tgt_names_of_targets :
      forall cs out,
        List.map snd cs = List.map (fun ty => [ty]) out ->
        forall d, In d out -> In d (tgt_names cs).
    Proof.
      intros cs out Heq d Hd.
      assert (In [d] (List.map snd cs)) as Hin
          by (rewrite Heq; apply in_map_iff; exists d;
              split; [reflexivity|exact Hd]).
      apply in_map_iff in Hin as (c & Hc & Hcin).
      unfold tgt_names. apply in_flat_map. exists c.
      split; [exact Hcin|rewrite Hc; now left].
    Qed.

    Definition decl_ok (decl : list ident) : Prop :=
      In base_ty decl
      /\ In rst_ty decl
      /\ (forall x b, Env.find x env = Some b -> In b decl).

    Definition clk_scoped (decl : list ident) : Prop :=
      forall ck ckty,
        assign_clk_type env base_ty ck = Some ckty -> st_scoped decl ckty.

    Definition lexp_scoped_tgt (decl : list ident) (e : exp) : Prop :=
      forall ts s s',
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        Forall (fun t => st_scoped (decl ++ tgt_names (carried ts)) (fst t)) ts
        /\ constraints_scoped (decl ++ tgt_names (carried ts)) (carried ts).

    Lemma scoped_tgt_widen :
      forall decl cs1 cs2 (ts : list LST),
        incl (tgt_names cs1) (tgt_names cs2) ->
        Forall (fun t => st_scoped (decl ++ tgt_names cs1) (fst t)) ts ->
        Forall (fun t => st_scoped (decl ++ tgt_names cs2) (fst t)) ts.
    Proof.
      intros decl cs1 cs2 ts Hi H.
      eapply Forall_impl; [|exact H]. intros a Ha.
      eapply st_scoped_weaken; [apply incl_decl_tgt, Hi|exact Ha].
    Qed.

    Lemma cscoped_tgt_widen :
      forall decl cs1 cs2 cs,
        incl (tgt_names cs1) (tgt_names cs2) ->
        constraints_scoped (decl ++ tgt_names cs1) cs ->
        constraints_scoped (decl ++ tgt_names cs2) cs.
    Proof.
      intros decl cs1 cs2 cs Hi H.
      eapply constraints_scoped_weaken; [apply incl_decl_tgt, Hi|exact H].
    Qed.

    Lemma cscoped_cmerge :
      forall S c1 c2,
        constraints_scoped S c1 -> constraints_scoped S c2 ->
        constraints_scoped S (cmerge c1 c2).
    Proof.
      intros S c1 c2 H1 H2. apply constraints_scoped_of_In.
      intros c x Hc Hx. apply cmerge_In in Hc as [Hc|Hc];
        [exact (constraints_scoped_In S c1 c x H1 Hc Hx)
        |exact (constraints_scoped_In S c2 c x H2 Hc Hx)].
    Qed.

    Lemma lexps_scoped_tgt_of :
      forall decl es,
        Forall (lexp_scoped_tgt decl) es ->
        forall ts s s',
          assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
          Forall (fun t => st_scoped (decl ++ tgt_names (carried ts)) (fst t))
            ts
          /\ constraints_scoped (decl ++ tgt_names (carried ts)) (carried ts).
    Proof.
      intros decl es Hall. induction Hall as [|e es He Hes IH];
        intros ts s s' H.
      - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
          as (? & _ & _); subst ts. split; constructor.
      - apply assign_lexps_carried_cons in H
          as (t & r & sa & Ht & Hr & ? & _); subst ts.
        destruct (He t s sa Ht) as (Hf1 & Hc1).
        destruct (IH r sa s' Hr) as (Hf2 & Hc2).
        rewrite carried_app in *.
        split.
        + apply Forall_app. split.
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
    Qed.

    Theorem lexp_scoped_tgt_all :
      forall decl,
        decl_ok decl ->
        clk_scoped decl ->
        secglobal_scoped G ->
        forall e, lexp_scoped_tgt decl e.
    Proof.
      intros decl (Hbase & Hrstd & Henv) Hclk Hsg e.
      induction e using exp_ind2; intros ts s s' Hgen.
      - rewrite assign_lexp_Econst in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hts & _); subst ts.
        split.
        + constructor; [|constructor]. cbn [fst lbot]. intros ? [].
        + cbn [carried lbot snd]. constructor.
      - apply assign_lexp_Evar_inv in Hgen as (xt & Hxt & Hts & _); subst ts.
        split.
        + constructor; [|constructor]. cbn [fst].
          intros y [Hy|[]]; subst y. apply in_or_app. left.
          exact (Henv _ _ Hxt).
        + cbn [carried snd]. constructor.
      - exact (IHe ts s s' Hgen).
      - rewrite assign_lexp_Ebinop in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (t2 & s2 & Ht2 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s3 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (a2 & s4 & Ha2 & Hret).
        apply single_inv in Ha1 as (? & ?); subst t1 s3.
        apply single_inv in Ha2 as (? & ?); subst t2 s4.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        destruct (IHe1 [a1] s s1 Ht1) as (Hf1 & Hc1).
        destruct (IHe2 [a2] s1 s2 Ht2) as (Hf2 & Hc2).
        rewrite carried_single in Hf1, Hc1, Hf2, Hc2.
        rewrite carried_single, snd_ljoin.
        inversion Hf1 as [|? ? Hs1 ?]; subst.
        inversion Hf2 as [|? ? Hs2 ?]; subst.
        split.
        + constructor; [|constructor]. rewrite fst_ljoin.
          apply st_scoped_merge.
          * eapply st_scoped_weaken;
              [apply incl_decl_tgt, tgt_names_cmerge_l|exact Hs1].
          * eapply st_scoped_weaken;
              [apply incl_decl_tgt, tgt_names_cmerge_r|exact Hs2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Efby in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (lexps_scoped_tgt_of decl e0s H ts0 s s1 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of decl es H0 us s1 s2 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        split.
        + eapply CALLS.ljoin_list_scoped_plain; [exact Hj| |].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Earrow in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (lexps_scoped_tgt_of decl e0s H ts0 s s1 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of decl es H0 us s1 s2 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        split.
        + eapply CALLS.ljoin_list_scoped_plain; [exact Hj| |].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Ewhen in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (g & s2 & Hg & Hret).
        apply find_env_inv in Hg as (Hg & ?); subst s2.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        destruct (lexps_scoped_tgt_of decl es H ts0 s s1 Hts0) as (Hf1 & Hc1).
        rewrite carried_map_when.
        split; [|exact Hc1].
        apply Forall_forall. intros t Ht.
        apply in_map_iff in Ht as (t0 & Ht0 & Hin0); subst t.
        rewrite fst_ljoin, fst_lvar. apply st_scoped_merge.
        + rewrite Forall_forall in Hf1. exact (Hf1 t0 Hin0).
        + intros y [Hy|[]]; subst y. apply in_or_app. left.
          exact (Henv _ _ Hg).
      - destruct a as (tys & cl).
        rewrite assign_lexp_Emerge in Hgen.
        apply sec_bind_inv in Hgen as (g & s1 & Hg & Hgen).
        apply find_env_inv in Hg as (Hg & ?); subst s1.
        apply sec_bind_inv in Hgen as (ts0 & s2 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s3 & Hus & Hj).
        assert (s' = s3) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (lexps_scoped_tgt_of decl ets H ts0 s s2 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of decl efs H0 us s2 s3 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried _ us ts s3 s3 Hj), carried_map_merge_l.
        split.
        + eapply CALLS.ljoin_list_scoped; [|exact Hj| |].
          * apply in_or_app. left. exact (Henv _ _ Hg).
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - destruct a as (tys & cl).
        rewrite assign_lexp_Eite in Hgen.
        apply sec_bind_inv in Hgen as (t0 & s1 & Ht0 & Hgen).
        apply sec_bind_inv in Hgen as (th & s2 & Hth & Hgen).
        apply single_inv in Hth as (? & ?); subst t0 s2.
        apply sec_bind_inv in Hgen as (ts0 & s3 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s4 & Hus & Hj).
        assert (s' = s4) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (IHe [th] s s1 Ht0) as (Hfh & Hch).
        rewrite carried_single in Hfh, Hch.
        inversion Hfh as [|? ? Hsh ?]; subst.
        destruct (lexps_scoped_tgt_of decl ets H ts0 s1 s3 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of decl efs H0 us s3 s4 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried _ us ts s4 s4 Hj).
        destruct ts0 as [|t00 ts0'].
        + cbn [List.map carried]. rewrite cmerge_nil2.
          split.
          * eapply CALLS.ljoin_list_scoped_plain; [exact Hj|constructor|].
            exact Hf2.
          * exact Hc2.
        + rewrite carried_map_ljoin_eq by (intros HF; inversion HF).
          split.
          * eapply CALLS.ljoin_list_scoped_head; [|exact Hj| |].
            -- eapply st_scoped_weaken; [|exact Hsh].
               apply incl_decl_tgt.
               eapply incl_tran;
                 [apply tgt_names_cmerge_l|apply tgt_names_cmerge_l].
            -- eapply scoped_tgt_widen; [|exact Hf1].
               eapply incl_tran;
                 [apply tgt_names_cmerge_r|apply tgt_names_cmerge_l].
            -- eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
          * apply cscoped_cmerge; [apply cscoped_cmerge|].
            -- eapply cscoped_tgt_widen; [|exact Hch].
               eapply incl_tran;
                 [apply tgt_names_cmerge_l|apply tgt_names_cmerge_l].
            -- eapply cscoped_tgt_widen; [|exact Hc1].
               eapply incl_tran;
                 [apply tgt_names_cmerge_r|apply tgt_names_cmerge_l].
            -- eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2].
      - apply assign_lexp_Eapp_inv in Hgen
          as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & Hck & Hrst & Hsgf & Houts & Hcs & Hts).
        destruct (lexps_scoped_tgt_of decl es H0 argts s sta Hargs)
          as (Hfa & Hca).
        assert (exists rs, st_scoped (decl ++ tgt_names rs) (fst rstty)
                           /\ constraints_scoped (decl ++ tgt_names rs)
                                (snd rstty)
                           /\ incl (tgt_names rs) (tgt_names (snd rstty)))
          as (rs & Hfr & Hcr & Hir).
        { destruct ro as [e1|].
          - destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg1 & Hrck & Hr).
            apply single_inv in Hsg1 as (? & ?); subst t1 stb.
            destruct (H [a1] sta stm Ht1) as (Hf1 & Hc1).
            rewrite carried_single in Hf1, Hc1.
            inversion Hf1 as [|? ? Hs1 ?]; subst.
            exists (snd a1). try subst rstty.
            rewrite !fst_ljoin, !snd_ljoin, fst_lvar, snd_lvar.
            cbn [fst snd]. rewrite cmerge_nil, cmerge_nil2.
            split; [|split; [exact Hc1|apply incl_refl]].
            apply st_scoped_merge;
              [intros y [Hy|[]]; subst y; apply in_or_app; now left|].
            apply st_scoped_merge; [exact Hs1|].
            eapply st_scoped_weaken; [|exact (Hclk _ _ Hrck)].
            intros y Hy. apply in_or_app. left. exact Hy.
          - destruct Hrst as (Hr & _). subst rstty.
            exists []. rewrite fst_lvar, snd_lvar.
            split; [intros y [Hy|[]]; subst y; apply in_or_app; now left|].
            split; [constructor|intros y []]. }
        pose proof (CALLS.generate_constraints_targets sg
                      (List.map fst argts) ckty (fst rstty) outs cs
                      stc s' Hcs) as Hsnd.
        subst ts. rewrite carried_uniform.
        destruct outs as [|o os].
        + split; [constructor|constructor].
        + assert (Hcsi : incl (tgt_names cs)
                           (tgt_names (cmerge cs
                              (cmerge (carried argts) (snd rstty)))))
              by apply tgt_names_cmerge_l.
          assert (Hargi : incl (tgt_names (carried argts))
                            (tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty))))).
          { eapply incl_tran;
              [apply tgt_names_cmerge_l|apply tgt_names_cmerge_r]. }
          assert (Hrsti : incl (tgt_names (snd rstty))
                            (tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty))))).
          { eapply incl_tran;
              [apply tgt_names_cmerge_r|apply tgt_names_cmerge_r]. }
          assert (Hoin : forall d, In d (o :: os) ->
                           In d (decl ++ tgt_names (cmerge cs
                                   (cmerge (carried argts) (snd rstty))))).
          { intros d Hd. apply in_or_app. right.
            apply Hcsi. exact (tgt_names_of_targets cs (o :: os) Hsnd d Hd). }
          assert (Hcscs : constraints_scoped
                            (decl ++ tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty)))) cs).
          { eapply generate_constraints_scoped;
              [exact (Hsg _ _ Hsgf)| | | | |exact Hcs].
            - apply Forall_forall. intros X HX.
              apply in_map_iff in HX as (t & Ht & Htin); subst X.
              eapply st_scoped_weaken; [apply incl_decl_tgt, Hargi|].
              rewrite Forall_forall in Hfa. exact (Hfa t Htin).
            - eapply st_scoped_weaken; [|exact (Hclk _ _ Hck)].
              intros y Hy. apply in_or_app. left. exact Hy.
            - eapply st_scoped_weaken; [apply incl_decl_tgt, Hrsti|].
              eapply st_scoped_weaken; [apply incl_decl_tgt, Hir|exact Hfr].
            - apply Forall_forall. exact Hoin. }
          split.
          * apply Forall_forall. intros t Ht.
            apply in_map_iff in Ht as (d & Hd & Hdin); subst t.
            cbn [fst]. intros y [Hy|[]]; subst y. exact (Hoin d Hdin).
          * apply cscoped_cmerge; [exact Hcscs|].
            apply cscoped_cmerge.
            -- eapply cscoped_tgt_widen; [exact Hargi|exact Hca].
            -- eapply cscoped_tgt_widen; [exact Hrsti|].
               eapply cscoped_tgt_widen; [exact Hir|exact Hcr].
    Qed.


    (** * The equation level of the dichotomy

        One abstract scope [S], not [decl ++ tgt_names c]: a rule's output
        *contains* the constraints the flow carried, so the second form would
        force an [incl (tgt_names (carried ts)) (tgt_names c)] side lemma for
        every rule.  What the rules need of the expressions inside them is
        [exps_scoped_in], which the node level discharges from
        [lexp_scoped_tgt_all] -- the carried targets are minted
        ([lexp_carried_minted_all]), and the node's [S] contains the whole
        window. *)

    (** * The equation level, a second time, with the targets in the scope

        The abstract-scope version above proves [constraints_scoped S cs] and
        so gives [simplify_scoped_weak]'s second premise.  Its third needs
        the *dichotomy* -- a name is declared or a target *of this very set* --
        and that does not follow: the window contains names a discarded
        carried set minted, which are not targets.  So the level is done
        again at scope [decl ++ tgt_names c], where the expression premise is
        the unconditional [lexp_scoped_tgt] and the price is one containment
        per rule: a rule's output contains the constraints the flow carried. *)

    Lemma tgt_names_app :
      forall c1 c2, tgt_names (c1 ++ c2) = tgt_names c1 ++ tgt_names c2.
    Proof. intros. unfold tgt_names. symmetry. apply flat_map_app. Qed.

    Lemma tgt_names_incl_of_In :
      forall c1 c2,
        (forall cc, In cc c1 -> In cc c2) ->
        incl (tgt_names c1) (tgt_names c2).
    Proof.
      intros c1 c2 H d Hd. unfold tgt_names in Hd |- *.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      apply in_flat_map. exists c. split; [exact (H c Hc)|exact Hdc].
    Qed.

    Lemma generate_lvars_constraints_carried_in :
      forall ckenv xs bs ts c s s',
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        forall cc, In cc (carried ts) -> In cc c.
    Proof.
      intros ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' Hgen cc Hcc.
      - destruct bs as [|b bs]; destruct ts as [|t ts];
          cbn in Hgen; try discriminate.
        cbn [carried] in Hcc. contradiction.
      - destruct bs as [|b bs]; [destruct ts; cbn in Hgen; discriminate|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & _); subst c.
        rewrite carried_cons in Hcc.
        apply cmerge_In in Hcc as [Hcc|Hcc].
        + apply in_or_app. left. unfold lconstrain. apply cmerge_In. right.
          rewrite snd_ljoin. unfold ambient.
          rewrite snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hcc.
        + apply in_or_app. right. exact (IH bs ts rest s1 s2 Hr cc Hcc).
    Qed.

    Definition exps_scoped_in (S : list ident) : Prop :=
      (forall e ts s0 s1,
          incl (tgt_names (carried ts)) S ->
          assign_lexp_type G env base_ty rst_ty e s0 = OK (ts, s1) ->
          Forall (fun t => st_scoped S (fst t)) ts
          /\ constraints_scoped S (carried ts))
      /\ (forall es ts s0 s1,
             incl (tgt_names (carried ts)) S ->
             assign_lexps G env base_ty rst_ty es s0 = OK (ts, s1) ->
             Forall (fun t => st_scoped S (fst t)) ts
             /\ constraints_scoped S (carried ts)).

    (** A sub-run's window sits inside its parent's, so one line moves a
        bound down into a rule's sub-expressions. *)
    Lemma minted_sub_incl :
      forall s0 s1 s s' S,
        sec_le s s0 -> sec_le s1 s' ->
        incl (minted s s') S -> incl (minted s0 s1) S.
    Proof.
      intros s0 s1 s s' S H1 H2 H.
      eapply incl_tran; [apply minted_window; [exact H1|exact H2]|exact H].
    Qed.

    Lemma cscoped_app :
      forall S c1 c2,
        constraints_scoped S c1 -> constraints_scoped S c2 ->
        constraints_scoped S (c1 ++ c2).
    Proof.
      intros S c1 c2 H1 H2. apply constraints_scoped_of_In.
      intros c x Hc Hx. apply in_app_or in Hc as [Hc|Hc];
        [exact (constraints_scoped_In S c1 c x H1 Hc Hx)
        |exact (constraints_scoped_In S c2 c x H2 Hc Hx)].
    Qed.

    Lemma cscoped_cmerge_inv :
      forall S c1 c2,
        constraints_scoped S (cmerge c1 c2) ->
        constraints_scoped S c1 /\ constraints_scoped S c2.
    Proof.
      intros S c1 c2 H. split; apply constraints_scoped_of_In;
        intros c x Hc Hx;
        [exact (constraints_scoped_In S _ c x H
                  (proj2 (cmerge_In c1 c2 c) (or_introl Hc)) Hx)
        |exact (constraints_scoped_In S _ c x H
                  (proj2 (cmerge_In c1 c2 c) (or_intror Hc)) Hx)].
    Qed.

    Lemma cscoped_carried_elem :
      forall S ts t,
        constraints_scoped S (carried ts) -> In t ts ->
        constraints_scoped S (snd t).
    Proof.
      intros S ts t H Ht. apply constraints_scoped_of_In.
      intros c x Hc Hx.
      exact (constraints_scoped_In S _ c x H (In_carried ts t c Ht Hc) Hx).
    Qed.

    Lemma cscoped_one :
      forall S lhs rhs,
        st_scoped S lhs -> st_scoped S rhs ->
        constraints_scoped S [(lhs, rhs)].
    Proof.
      intros S lhs rhs Hl Hr. apply constraints_scoped_of_In.
      intros c x Hc Hx. destruct Hc as [Hc|[]]; subst c.
      unfold constraint_scope in Hx. cbn [fst snd] in Hx.
      apply in_app_or in Hx as [Hx|Hx]; [exact (Hl x Hx)|exact (Hr x Hx)].
    Qed.

    Lemma generate_lvars_constraints_scoped_tgt :
      forall S ckenv xs bs ts c s s',
        clk_scoped S ->
        In rst_ty S ->
        incl bs S ->
        Forall (fun t => st_scoped S (fst t)) ts ->
        constraints_scoped S (carried ts) ->
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        constraints_scoped S c.
    Proof.
      intros S ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' Hclk Hrs Hbs Hfs Hcs Hgen.
      - destruct bs as [|b bs]; destruct ts as [|t ts];
          cbn in Hgen; try discriminate.
        unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst c.
        constructor.
      - destruct bs as [|b bs]; [destruct ts; cbn in Hgen; discriminate|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        rewrite carried_cons in Hcs.
        apply cscoped_cmerge_inv in Hcs as (Hct & Hctr).
        inversion Hfs as [|? ? Hft Hfr]; subst.
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & _); subst c.
        apply cscoped_app.
        + unfold lconstrain. apply cscoped_cmerge.
          * apply cscoped_one; [|intros y [Hy|[]]; subst y; apply Hbs; now left].
            rewrite fst_ljoin. unfold ambient.
            rewrite fst_ljoin, fst_lvar.
            apply st_scoped_merge; [|exact Hft].
            apply st_scoped_merge;
              [intros y [Hy|[]]; subst y; exact Hrs|].
            unfold eqn_clock_type in Hck.
            apply sec_bind_inv in Hck as (ck & sa & Hfc & Hck).
            apply option_to_sec_inv in Hck as (Hck & _).
            exact (Hclk _ _ Hck).
          * rewrite snd_ljoin. unfold ambient.
            rewrite snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2. exact Hct.
        + eapply IH;
            [exact Hclk|exact Hrs| |exact Hfr|exact Hctr|exact Hr].
          intros y Hy. apply Hbs. now right.
    Qed.

    Lemma generate_ldef_constraint_scoped :
      forall S ckenv x e cs s s',
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env [x]) S ->
        incl (tgt_names cs) S ->
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv x e cs s s' Hclk Hrs (Hexp & _) Hxs Htc Hgen.
      apply generate_ldef_constraint_inv in Hgen
        as (ck & ckty & tf & b & s1 & Hfc & Hck & Hte & Hb & Hs1 & Hcs).
      subst s1.
      assert (incl (tgt_names (carried [tf])) S) as Hci.
      { rewrite carried_single. eapply incl_tran; [|exact Htc].
        apply tgt_names_incl_of_In. intros cc Hcc. rewrite Hcs.
        apply (proj2 (cmerge_In _ _ cc)). now right. }
      destruct (Hexp e [tf] s s' Hci Hte) as (Hft & Hct).
      rewrite carried_single in Hct. rewrite Hcs.
      inversion Hft as [|? ? Hf1 ?]; subst.
      apply cscoped_cmerge; [|exact Hct].
      apply cscoped_one; [|intros y [Hy|[]]; subst y].
      - apply st_scoped_merge; [|exact Hf1].
        apply st_scoped_merge;
          [intros y [Hy|[]]; subst y; exact Hrs|exact (Hclk _ _ Hck)].
      - apply Hxs. unfold CALLS.sec_of. cbn [flat_map].
        rewrite Hb. now left.
    Qed.

    Lemma generate_lgen_constraint_scoped :
      forall S ckenv xs es cs s s',
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env xs) S ->
        incl (tgt_names cs) S ->
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv xs es cs s s' Hclk Hrs (_ & Hexps) Hxs Htc Hgen.
      unfold generate_lgen_constraint in Hgen.
      apply sec_bind_inv in Hgen as (ts & s1 & Hts & Hgen).
      apply sec_bind_inv in Hgen as (bs & s2 & Hbs & Hlv).
      apply option_to_sec_inv in Hbs as (Hbs & ?); subst s2.
      assert (s' = s1) as ?
          by (destruct (state_pure_generate_lvars_constraints env base_ty
                          rst_ty ckenv xs bs ts s1 s1 _ _ Hlv) as (Hp & _);
              exact Hp).
      subst s'.
      assert (incl (tgt_names (carried ts)) S) as Hci.
      { eapply incl_tran; [|exact Htc]. apply tgt_names_incl_of_In.
        intros cc Hcc.
        exact (generate_lvars_constraints_carried_in ckenv xs bs ts cs s1 s1
                 Hlv cc Hcc). }
      destruct (Hexps es ts s s1 Hci Hts) as (Hfs & Hcs).
      eapply generate_lvars_constraints_scoped_tgt;
        [exact Hclk|exact Hrs| |exact Hfs|exact Hcs|exact Hlv].
      assert (Forall2 (fun x b => Env.find x env = Some b) xs bs) as Hf2
          by (eapply (get_mappings_Forall2 env xs bs); exact Hbs).
      rewrite <- (Forall2_sec_of xs bs Hf2). exact Hxs.
    Qed.

    Lemma generate_lcall_constraint_scoped :
      forall S xs f es rstty cs s s',
        secglobal_scoped G ->
        clk_scoped S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env xs) S ->
        st_scoped S (fst rstty) ->
        constraints_scoped S (snd rstty) ->
        incl (tgt_names cs) S ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S xs f es rstty cs s s' Hsg Hclk (_ & Hexps) Hxs Hfr Hcr
        Htc Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      assert (s' = sti) as ?
          by (destruct (state_pure_generate_constraints sg
                          (List.map fst argts) ckty (fst rstty) outs
                          sti sti _ _ Hgc) as (Hp & _); exact Hp).
      subst s'.
      assert (incl (tgt_names (carried argts)) S) as Hci.
      { eapply incl_tran; [|exact Htc]. apply tgt_names_incl_of_In.
        intros cc Hcc. rewrite Hcs.
        apply (proj2 (cmerge_In _ _ cc)). right.
        apply (proj2 (cmerge_In _ _ cc)). now left. }
      destruct (Hexps es argts s sti Hci Hargs) as (Hfa & Hca).
      assert (Forall2 (fun x b => Env.find x env = Some b) xs outs) as Hf2
          by (eapply CALLS.mmap_find_env_Forall2; exact Houts).
      rewrite Hcs. apply cscoped_cmerge; [|apply cscoped_cmerge].
      - eapply generate_constraints_scoped;
          [exact (Hsg _ _ Esg)| |exact (Hclk _ _ Hck)|exact Hfr| |exact Hgc].
        + apply Forall_forall. intros X HX.
          apply in_map_iff in HX as (t & Ht & Htin); subst X.
          rewrite Forall_forall in Hfa. exact (Hfa t Htin).
        + apply Forall_forall. intros d Hd. apply Hxs.
          rewrite (Forall2_sec_of xs outs Hf2). exact Hd.
      - exact Hca.
      - exact Hcr.
    Qed.

    Lemma generate_lone_constraint_scoped :
      forall S ckenv ys e cs s s',
        secglobal_scoped G ->
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env ys) S ->
        incl (tgt_names cs) S ->
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv ys e cs s s' Hsg Hclk Hrs Hexp Hys Htc Hgen.
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      1-9: destruct ys as [|x [|y ys]];
        [eapply generate_lgen_constraint_scoped;
           [exact Hclk|exact Hrs|exact Hexp|exact Hys|exact Htc|exact Hgen]
        |eapply generate_ldef_constraint_scoped;
           [exact Hclk|exact Hrs|exact Hexp|exact Hys|exact Htc|exact Hgen]
        |eapply generate_lgen_constraint_scoped;
           [exact Hclk|exact Hrs|exact Hexp|exact Hys|exact Htc|exact Hgen]].
      destruct Hexp as (Hexp1 & Hexps).
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (Hrck & ?); subst s3.
        pose proof Hgen as Hgen0.
        apply generate_lcall_constraint_inv in Hgen0
          as (sg0 & ckty0 & argts0 & outs0 & sti0 & cs00
              & _ & _ & _ & _ & _ & Hshape).
        assert (incl (tgt_names (carried [a1])) S) as Hci.
        { rewrite carried_single. eapply incl_tran; [|exact Htc].
          apply tgt_names_incl_of_In. intros cc Hcc. rewrite Hshape.
          apply (proj2 (cmerge_In _ _ cc)). right.
          apply (proj2 (cmerge_In _ _ cc)). right.
          rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hcc. }
        destruct (Hexp1 e1 [a1] s s1 Hci Ht1) as (Hf1 & Hc1).
        rewrite carried_single in Hc1.
        inversion Hf1 as [|? ? Hs1 ?]; subst.
        eapply generate_lcall_constraint_scoped;
          [exact Hsg|exact Hclk|exact (conj Hexp1 Hexps)|exact Hys| | |
           exact Htc|exact Hgen].
        + rewrite !fst_ljoin, fst_lvar.
          apply st_scoped_merge;
            [intros y0 [Hy0|[]]; subst y0; exact Hrs|].
          apply st_scoped_merge; [exact Hs1|exact (Hclk _ _ Hrck)].
        + rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hc1.
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - eapply generate_lcall_constraint_scoped;
          [exact Hsg|exact Hclk|exact (conj Hexp1 Hexps)|exact Hys| | |
           exact Htc|exact Hgen].
        + rewrite fst_lvar. intros y0 [Hy0|[]]; subst y0; exact Hrs.
        + rewrite snd_lvar. constructor.
    Qed.

    Lemma generate_lsplit_constraints_scoped :
      forall S ckenv es xs cs s s',
        secglobal_scoped G ->
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env xs) S ->
        incl (tgt_names cs) S ->
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv es. induction es as [|e es IH];
        intros xs cs s s' Hsg Hclk Hrs Hexp Hxs Htc Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        rewrite tgt_names_app in Htc.
        apply cscoped_app.
        + eapply generate_lone_constraint_scoped;
            [exact Hsg|exact Hclk|exact Hrs|exact Hexp| | |exact Hc].
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_firstn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Htc]. apply incl_appl, incl_refl.
        + eapply IH;
            [exact Hsg|exact Hclk|exact Hrs|exact Hexp| | |exact Hcr].
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_skipn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Htc]. apply incl_appr, incl_refl.
    Qed.

    Lemma generate_leqn_constraint_scoped :
      forall S ckenv eqn cs s s',
        secglobal_scoped G ->
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env (fst eqn)) S ->
        incl (tgt_names cs) S ->
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv eqn cs s s' Hsg Hclk Hrs Hexp Hxs Htc Hgen.
      destruct eqn as (xs & es). cbn [fst] in Hxs.
      destruct es as [|e [|e2 es2]].
      - eapply generate_lgen_constraint_scoped;
          [exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc|exact Hgen].
      - destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                      |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0
                      |f args ro anns].
        1-9: destruct xs as [|x [|y xs]];
          [eapply generate_lgen_constraint_scoped;
             [exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc|exact Hgen]
          |eapply generate_ldef_constraint_scoped;
             [exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc|exact Hgen]
          |eapply generate_lgen_constraint_scoped;
             [exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc
             |exact Hgen]].
        destruct Hexp as (Hexp1 & Hexps).
        destruct ro as [e1|]; destruct xs as [|y xs].
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
        + cbn [generate_leqn_constraint] in Hgen.
          apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
          apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
          apply single_inv in Ha1 as (? & ?); subst t1 s2.
          apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
          apply option_to_sec_inv in Hrck as (Hrck & ?); subst s3.
          pose proof Hgen as Hgen0.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg0 & ckty0 & argts0 & outs0 & sti0 & cs00
                & _ & _ & _ & _ & _ & Hshape).
          assert (incl (tgt_names (carried [a1])) S) as Hci.
          { rewrite carried_single. eapply incl_tran; [|exact Htc].
            apply tgt_names_incl_of_In. intros cc Hcc. rewrite Hshape.
            apply (proj2 (cmerge_In _ _ cc)). right.
            apply (proj2 (cmerge_In _ _ cc)). right.
            rewrite !snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2. exact Hcc. }
          destruct (Hexp1 e1 [a1] s s1 Hci Ht1) as (Hf1 & Hc1).
          rewrite carried_single in Hc1.
          inversion Hf1 as [|? ? Hs1 ?]; subst.
          eapply generate_lcall_constraint_scoped;
            [exact Hsg|exact Hclk|exact (conj Hexp1 Hexps)|exact Hxs| |
             |exact Htc|exact Hgen].
          * rewrite !fst_ljoin, fst_lvar.
            apply st_scoped_merge;
              [intros y0 [Hy0|[]]; subst y0; exact Hrs|].
            apply st_scoped_merge; [exact Hs1|exact (Hclk _ _ Hrck)].
          * rewrite !snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2. exact Hc1.
        + unfold SC.ret in Hgen.
          destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
        + eapply generate_lcall_constraint_scoped;
            [exact Hsg|exact Hclk|exact (conj Hexp1 Hexps)|exact Hxs| |
             |exact Htc|exact Hgen].
          * rewrite fst_lvar. intros y0 [Hy0|[]]; subst y0; exact Hrs.
          * rewrite snd_lvar. constructor.
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            (eapply generate_lsplit_constraints_scoped;
             [exact Hsg|exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc
             |exact Hgen]).
        + destruct e; try destruct o;
            (eapply generate_lgen_constraint_scoped;
             [exact Hclk|exact Hrs|exact Hexp|exact Hxs|exact Htc
             |exact Hgen]).
    Qed.

    Theorem generate_leqns_constraints_scoped :
      forall S ckenv eqs cs s s',
        secglobal_scoped G ->
        clk_scoped S ->
        In rst_ty S ->
        exps_scoped_in S ->
        incl (CALLS.sec_of env (vars_defined eqs)) S ->
        incl (tgt_names cs) S ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv eqs. induction eqs as [|eqn eqs IH];
        intros cs s s' Hsg Hclk Hrs Hexp Hxs Htc Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc. constructor.
      - rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        rewrite vars_defined_cons_eq, sec_of_app in Hxs.
        rewrite tgt_names_app in Htc.
        apply cscoped_app.
        + eapply generate_leqn_constraint_scoped;
            [exact Hsg|exact Hclk|exact Hrs|exact Hexp| | |exact Hc1].
          * eapply incl_tran; [|exact Hxs]. apply incl_appl, incl_refl.
          * eapply incl_tran; [|exact Htc]. apply incl_appl, incl_refl.
        + eapply IH;
            [exact Hsg|exact Hclk|exact Hrs|exact Hexp| | |exact Hc2].
          * eapply incl_tran; [|exact Hxs]. apply incl_appr, incl_refl.
          * eapply incl_tran; [|exact Htc]. apply incl_appr, incl_refl.
    Qed.

    Lemma collapse_occurs_mono :
      forall cns d', ~ occurs d' cns -> ~ occurs d' (collapse cns).
    Proof.
      intros cns d' Hno (c & Hc & Hx).
      assert (constraints_scoped (flat_map constraint_scope cns)
                (collapse cns)) as Hsc
          by (apply collapse_scoped, constraints_scoped_self).
      pose proof (constraints_scoped_In _ _ c d' Hsc Hc Hx) as Hin.
      apply in_flat_map in Hin as (c0 & Hc0 & Hx0).
      exact (Hno (ex_intro _ c0 (conj Hc0 Hx0))).
    Qed.


    Lemma tgt_names_of_targets_of :
      forall ds cs, targets_of ds cs -> incl (tgt_names cs) ds.
    Proof.
      intros ds cs H d Hd. unfold tgt_names in Hd.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      destruct (targets_of_In ds cs c H Hc) as (b & Hb & Hsc).
      destruct c as (lhs, rhs). cbn [snd] in Hsc, Hdc. subst rhs.
      destruct Hdc as [Hdc|[]]; subst d. exact Hb.
    Qed.

    Lemma In_tgt_names_target :
      forall cs d,
        Forall singleton_rhs cs ->
        In d (tgt_names cs) ->
        In [d] (List.map snd cs).
    Proof.
      intros cs d Hs Hd. unfold tgt_names in Hd.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      rewrite Forall_forall in Hs. destruct (Hs c Hc) as (b & Hb).
      destruct c as (lhs, rhs). cbn [snd] in Hb, Hdc. subst rhs.
      destruct Hdc as [Hdc|[]]; subst b.
      apply in_map_iff. exists (lhs, [d]). split; [reflexivity|exact Hc].
    Qed.

    (** The dichotomy, packaged the way the equation rules consume it.  No
        window reasoning is left: the rules ask only that the targets a flow
        carries lie in the scope, and they supply that themselves. *)
    Lemma exps_scoped_in_of_decl :
      forall decl S,
        decl_ok decl ->
        clk_scoped decl ->
        secglobal_scoped G ->
        incl decl S ->
        exps_scoped_in S.
    Proof.
      intros decl S Hdk Hclk Hsg Hds. split.
      - intros e ts s0 s1 Hci Hgen.
        destruct (lexp_scoped_tgt_all decl Hdk Hclk Hsg e ts s0 s1 Hgen)
          as (Hf & Hc).
        assert (incl (decl ++ tgt_names (carried ts)) S) as Hi
            by (apply incl_app; [exact Hds|exact Hci]).
        split;
          [eapply Forall_impl; [|exact Hf]; intros t Ht;
           eapply st_scoped_weaken; [exact Hi|exact Ht]
          |eapply constraints_scoped_weaken; [exact Hi|exact Hc]].
      - intros es ts s0 s1 Hci Hgen.
        assert (Forall (lexp_scoped_tgt decl) es) as Hall
            by (apply Forall_forall; intros e0 _;
                apply (lexp_scoped_tgt_all decl Hdk Hclk Hsg)).
        destruct (lexps_scoped_tgt_of decl es Hall ts s0 s1 Hgen) as (Hf & Hc).
        assert (incl (decl ++ tgt_names (carried ts)) S) as Hi
            by (apply incl_app; [exact Hds|exact Hci]).
        split;
          [eapply Forall_impl; [|exact Hf]; intros t Ht;
           eapply st_scoped_weaken; [exact Hi|exact Ht]
          |eapply constraints_scoped_weaken; [exact Hi|exact Hc]].
    Qed.

    Lemma target_In_tgt_names :
      forall cs d, In [d] (List.map snd cs) -> In d (tgt_names cs).
    Proof.
      intros cs d Hd. apply in_map_iff in Hd as (c & Hc & Hcin).
      unfold tgt_names. apply in_flat_map. exists c.
      split; [exact Hcin|].
      destruct c as (lhs, rhs). cbn [snd] in Hc |- *. subst rhs. now left.
    Qed.

  End RawTargets.

  (** * Item 1: every constraint of a published signature is rooted

      The carried half is the dichotomy's sibling and goes by the same
      induction as [lexp_carried_minted_all], window threaded: rootedness is a
      [Forall], so it survives every [cmerge] and [ljoin] the typing performs,
      and the only expression with content is the call, whose block is rooted
      by [generate_constraints_rooted] against the callee's own rootedness.

      That lemma needs the instantiation to be fresh against the callee's
      scope, and it is stated here the way it can be true: about the call the
      run actually makes.  Its actuals are scoped in [ns] -- the declared names
      and what the window minted -- and [ns] is fresh against every callee.
      (Freshness for *every* instantiation [generate_constraints] accepts is
      not provable: it accepts an actual that contains a callee formal.) *)

  Section RawRooted.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable decl    : list ident.
    Variable ns      : list ident.

    Hypothesis Hdk   : decl_ok env base_ty rst_ty decl.
    Hypothesis Hclk  : clk_scoped env base_ty decl.
    Hypothesis Hsgs  : secglobal_scoped G.
    Hypothesis Hdns  : incl decl ns.
    Hypothesis ns_fresh :
      forall f sg, find_signature f G = Some sg -> scope_fresh ns sg.
    Hypothesis sig_nodup :
      forall f sg,
        find_signature f G = Some sg ->
        NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)).
    Hypothesis sig_rooted :
      forall f sg,
        find_signature f G = Some sg ->
        CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
        /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints).

    Lemma rooted_cmerge :
      forall c1 c2,
        constraints_rooted base_ty rst_ty c1 ->
        constraints_rooted base_ty rst_ty c2 ->
        constraints_rooted base_ty rst_ty (cmerge c1 c2).
    Proof.
      intros c1 c2 H1 H2. apply constraints_rooted_cmerge. split; assumption.
    Qed.

    Lemma rooted_carried_map_ljoin :
      forall h ts,
        constraints_rooted base_ty rst_ty (snd h) ->
        constraints_rooted base_ty rst_ty (carried ts) ->
        constraints_rooted base_ty rst_ty
          (carried (List.map (fun t => ljoin h t) ts)).
    Proof.
      intros h ts. exact (Forall_carried_map_ljoin _ h ts).
    Qed.

    Lemma carried_rooted_iff :
      forall ts,
        Forall (fun t => constraints_rooted base_ty rst_ty (snd t)) ts
        <-> constraints_rooted base_ty rst_ty (carried ts).
    Proof.
      induction ts as [|t ts IH]; [split; constructor|].
      rewrite carried_cons, constraints_rooted_cmerge, <- IH. split.
      - intros H. inversion H; subst. auto.
      - intros (H1 & H2). constructor; assumption.
    Qed.

    Lemma tgt_names_incl_of_Forall :
      forall cs, Forall (fun c => incl (snd c) ns) cs ->
                 incl (tgt_names cs) ns.
    Proof.
      intros cs H d Hd. unfold tgt_names in Hd.
      apply in_flat_map in Hd as (c & Hc & Hdc).
      rewrite Forall_forall in H. exact (H c Hc d Hdc).
    Qed.

    (** The window-bounded form of the rootedness contract. *)
    Definition exp_rooted_win (e : exp) : Prop :=
      forall ts s s',
        incl (minted s s') ns ->
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
        constraints_rooted base_ty rst_ty (carried ts).

    Lemma lexps_rooted_win_intro :
      forall es,
        Forall exp_rooted_win es ->
        forall ts s s',
          incl (minted s s') ns ->
          assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
          constraints_rooted base_ty rst_ty (carried ts).
    Proof.
      intros es Hall. induction Hall as [|e es He Hes IH];
        intros ts s s' Hns H.
      - apply (assign_lexps_carried_nil G env base_ty rst_ty) in H
          as (? & _ & ?); subst ts. constructor.
      - apply assign_lexps_carried_cons in H
          as (t & r & sa & Ht & Hr & ? & _); subst ts.
        rewrite carried_app. apply rooted_cmerge.
        + apply (He t s sa); [|exact Ht].
          apply (minted_incl_sub s s sa s' ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hr|exact Hns].
        + apply (IH r sa s'); [|exact Hr].
          apply (minted_incl_sub s sa s' s' ns);
            [eapply assign_lexp_type_sec_le; exact Ht
            |apply sec_le_refl|exact Hns].
    Qed.

    Theorem exp_rooted_win_all : forall e, exp_rooted_win e.
    Proof.
      intros e. induction e using exp_ind2;
        intros ts s s' Hns Hgen.
      - rewrite assign_lexp_Econst in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hts & _); subst ts.
        cbn [carried lbot snd]. constructor.
      - apply assign_lexp_Evar_inv in Hgen as (a0 & _ & Hts & _). subst ts.
        cbn [carried snd]. constructor.
      - exact (IHe ts s s' Hns Hgen).
      - rewrite assign_lexp_Ebinop in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (t2 & s2 & Ht2 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s3 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (a2 & s4 & Ha2 & Hret).
        apply single_inv in Ha1 as (? & ?); subst t1 s3.
        apply single_inv in Ha2 as (? & ?); subst t2 s4.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        rewrite carried_single, snd_ljoin. apply rooted_cmerge.
        + rewrite <- (carried_single a1).
          apply (IHe1 [a1] s s1); [|exact Ht1].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexp_type_sec_le; exact Ht2
            |exact Hns].
        + rewrite <- (carried_single a2).
          apply (IHe2 [a2] s1 s2); [|exact Ht2].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexp_type_sec_le; exact Ht1
            |apply sec_le_refl|exact Hns].
      - rewrite assign_lexp_Efby in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        apply rooted_cmerge.
        + apply (lexps_rooted_win_intro e0s H ts0 s s1); [|exact Hts0].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_rooted_win_intro es H0 us s1 s2); [|exact Hus].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - rewrite assign_lexp_Earrow in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        apply rooted_cmerge.
        + apply (lexps_rooted_win_intro e0s H ts0 s s1); [|exact Hts0].
          apply (minted_incl_sub s s s1 s2 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_rooted_win_intro es H0 us s1 s2); [|exact Hus].
          apply (minted_incl_sub s s1 s2 s2 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - rewrite assign_lexp_Ewhen in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (g & s2 & Hg & Hret).
        apply find_env_inv in Hg as (_ & ?); subst s2.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        rewrite carried_map_when.
        exact (lexps_rooted_win_intro es H ts0 s s1 Hns Hts0).
      - destruct a as (tys & cl).
        rewrite assign_lexp_Emerge in Hgen.
        apply sec_bind_inv in Hgen as (g & s1 & Hg & Hgen).
        apply find_env_inv in Hg as (_ & ?); subst s1.
        apply sec_bind_inv in Hgen as (ts0 & s2 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s3 & Hus & Hj).
        assert (s' = s3) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried _ us ts s3 s3 Hj).
        apply rooted_cmerge.
        + rewrite carried_map_merge_l.
          apply (lexps_rooted_win_intro ets H ts0 s s2); [|exact Hts0].
          apply (minted_incl_sub s s s2 s3 ns);
            [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
            |exact Hns].
        + apply (lexps_rooted_win_intro efs H0 us s2 s3); [|exact Hus].
          apply (minted_incl_sub s s2 s3 s3 ns);
            [eapply assign_lexps_sec_le; exact Hts0
            |apply sec_le_refl|exact Hns].
      - destruct a as (tys & cl).
        rewrite assign_lexp_Eite in Hgen.
        apply sec_bind_inv in Hgen as (t0 & s1 & Ht0 & Hgen).
        apply sec_bind_inv in Hgen as (th & s2 & Hth & Hgen).
        apply single_inv in Hth as (? & ?); subst t0 s2.
        apply sec_bind_inv in Hgen as (ts0 & s3 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s4 & Hus & Hj).
        assert (s' = s4) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        rewrite (ljoin_list_carried _ us ts s4 s4 Hj).
        apply rooted_cmerge.
        + apply rooted_carried_map_ljoin.
          * assert (Hw : incl (minted s s1) ns).
            { apply (minted_incl_sub s s s1 s3 ns);
                [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hts0|].
              apply (minted_incl_sub s s s3 s4 ns);
                [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus
                |exact Hns]. }
            pose proof (IHe [th] s s1 Hw Ht0) as Hth.
            rewrite carried_single in Hth. exact Hth.
          * apply (lexps_rooted_win_intro ets H ts0 s1 s3); [|exact Hts0].
            apply (minted_incl_sub s1 s1 s3 s4 ns);
              [apply sec_le_refl|eapply assign_lexps_sec_le; exact Hus|].
            apply (minted_incl_sub s s1 s4 s4 ns);
              [eapply assign_lexp_type_sec_le; exact Ht0
              |apply sec_le_refl|exact Hns].
        + apply (lexps_rooted_win_intro efs H0 us s3 s4); [|exact Hus].
          apply (minted_incl_sub s s3 s4 s4 ns);
            [eapply sec_le_trans;
             [eapply assign_lexp_type_sec_le; exact Ht0
             |eapply assign_lexps_sec_le; exact Hts0]
            |apply sec_le_refl|exact Hns].
      - (** the call *)
        apply assign_lexp_Eapp_inv in Hgen
          as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & Hck & Hrst & Hsg & Houts & Hcs & Hts).
        destruct (assign_lexp_Eapp_stages_le G env base_ty rst_ty es ro _
                    s s' sg argts rstty ckty outs cs sta stb stc
                    Hargs Hrst Houts Hcs) as (Hlab & Hlbc & Hlcs).
        assert (sec_le s sta) as Hlsa
            by (eapply assign_lexps_sec_le; exact Hargs).
        assert (sec_le s stb) as Hlsb by (eapply sec_le_trans; eauto).
        (** what the actuals are scoped in *)
        assert (Hwa : incl (minted s sta) ns).
        { apply (minted_incl_sub s s sta s' ns);
            [apply sec_le_refl
            |eapply sec_le_trans; [exact Hlab|
             eapply sec_le_trans; [exact Hlbc|exact Hlcs]]
            |exact Hns]. }
        assert (Hall : Forall (lexp_scoped_tgt G env base_ty rst_ty decl) es).
        { apply Forall_forall. intros e0 _.
          apply (lexp_scoped_tgt_all G env base_ty rst_ty decl Hdk Hclk Hsgs). }
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es Hall argts
                    s sta Hargs) as (Hfa & _).
        assert (Hmin : Forall (lexp_carried_minted G env base_ty rst_ty) es)
          by (apply Forall_forall; intros e0 _;
              apply (lexp_carried_minted_all G env base_ty rst_ty)).
        assert (Hca : Forall (fun c => incl (snd c) ns) (carried argts))
          by exact (lexps_carried_minted_of G env base_ty rst_ty es Hmin argts
                      s sta ns Hwa Hargs).
        assert (Htg : incl (tgt_names (carried argts)) ns)
          by exact (tgt_names_incl_of_Forall _ Hca).
        assert (Hinc : incl (decl ++ tgt_names (carried argts)) ns)
          by (apply incl_app; assumption).
        assert (Hargsc : Forall (st_scoped ns) (List.map fst argts)).
        { apply Forall_forall. intros X HX.
          apply in_map_iff in HX as (t & Ht & Htin); subst X.
          rewrite Forall_forall in Hfa.
          exact (st_scoped_weaken _ _ _ Hinc (Hfa t Htin)). }
        assert (Hck' : st_scoped ns ckty)
          by exact (st_scoped_weaken _ _ _ Hdns (Hclk _ _ Hck)).
        assert (Hout' : Forall (fun x => In x ns) outs).
        { apply Forall_forall. intros x Hx. apply 
            (minted_incl_sub s stb stc s' ns Hlsb Hlcs Hns).
          exact (fresh_idents_minted _ _ _ _ Houts x Hx). }
        (** the reset's flow type: rooted, containing the level, scoped *)
        assert (constraints_rooted base_ty rst_ty (snd rstty) /\
                In rst_ty (fst rstty) /\ st_scoped ns (fst rstty))
          as (Hrr & Hrin & Hrsc).
        { destruct ro as [e1|].
          - destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg1 & Hrck & Hr).
            apply single_inv in Hsg1 as (? & ?); subst t1 stb.
            assert (Hw1 : incl (minted sta stm) ns).
            { apply (minted_incl_sub s sta stm s' ns);
                [exact Hlsa
                |eapply sec_le_trans; [exact Hlbc|exact Hlcs]|exact Hns]. }
            destruct (lexp_scoped_tgt_all G env base_ty rst_ty decl Hdk Hclk
                        Hsgs e1 [a1] sta stm Ht1) as (Hfa1 & _).
            inversion Hfa1 as [|? ? Hsa1 ?]; subst.
            pose proof (tgt_names_incl_of_Forall _
                          (lexp_carried_minted_all G env base_ty rst_ty e1
                             [a1] sta stm ns Hw1 Ht1)) as Htg1.
            rewrite !snd_ljoin, snd_lvar, !fst_ljoin, fst_lvar.
            cbn [snd]. rewrite cmerge_nil, cmerge_nil2. repeat split.
            + rewrite <- (carried_single a1).
              exact (H [a1] sta stm Hw1 Ht1).
            + apply in_merge_left. now left.
            + apply st_scoped_merge;
                [intros y0 [Hy0|[]]; subst y0; apply Hdns; exact (proj1 (proj2 Hdk))|].
              apply st_scoped_merge.
              * eapply st_scoped_weaken;
                  [apply incl_app; [exact Hdns|exact Htg1]|exact Hsa1].
              * exact (st_scoped_weaken _ _ _ Hdns (Hclk _ _ Hrck)).
          - destruct Hrst as (Hr & _). subst rstty.
            rewrite snd_lvar, fst_lvar. repeat split.
            + constructor.
            + now left.
            + intros y0 [Hy0|[]]; subst y0. apply Hdns.
              exact (proj1 (proj2 Hdk)). }
        subst ts. rewrite carried_uniform.
        destruct outs as [|o os]; [constructor|].
        assert (Hbk : In base_ty ckty)
          by exact (assign_clk_type_base env base_ty _ ckty Hck).
        apply rooted_cmerge.
        + exact (generate_constraints_rooted base_ty rst_ty sg
                   (List.map fst argts) ckty (fst rstty) (o :: os) cs stc s'
                   (sig_nodup _ _ Hsg)
                   (call_subst_fresh_from_scope_fresh ns sg _ _ _ _
                      (ns_fresh _ _ Hsg) Hargsc Hck' Hrsc Hout')
                   (proj1 (sig_rooted _ _ Hsg)) (proj2 (sig_rooted _ _ Hsg))
                   Hbk Hrin Hcs).
        + apply rooted_cmerge; [|exact Hrr].
          exact (lexps_rooted_win_intro es H0 argts s sta Hwa Hargs).
    Qed.

    (** The equation level.  The window of the whole rule bounds every
        sub-run's, and the equation's left-hand names are in [ns]. *)

    Lemma exp_rooted_win_list :
      forall es, Forall exp_rooted_win es.
    Proof.
      intros es. induction es as [|e es IH]; constructor;
        [exact (exp_rooted_win_all e)|exact IH].
    Qed.

    Lemma generate_lcall_constraint_rooted_win :
      forall xs f es rstty cs s s',
        incl (minted s s') ns ->
        incl (CALLS.sec_of env xs) ns ->
        constraints_rooted base_ty rst_ty (snd rstty) ->
        In rst_ty (fst rstty) ->
        st_scoped ns (fst rstty) ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros xs f es rstty cs s s' Hns Hxs Hrr Hrin Hrsc Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      assert (s' = sti) as ?
          by (destruct (state_pure_generate_constraints sg
                          (List.map fst argts) ckty (fst rstty) outs
                          sti sti _ _ Hgc) as (Hp & _); exact Hp).
      subst s'.
      assert (Hall : Forall (lexp_scoped_tgt G env base_ty rst_ty decl) es).
      { apply Forall_forall. intros e0 _.
        apply (lexp_scoped_tgt_all G env base_ty rst_ty decl Hdk Hclk Hsgs). }
      destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es Hall argts
                  s sti Hargs) as (Hfa & _).
      assert (Hmin : Forall (lexp_carried_minted G env base_ty rst_ty) es)
        by (apply Forall_forall; intros e0 _;
            apply (lexp_carried_minted_all G env base_ty rst_ty)).
      assert (Hca : Forall (fun c => incl (snd c) ns) (carried argts))
        by exact (lexps_carried_minted_of G env base_ty rst_ty es Hmin argts
                    s sti ns Hns Hargs).
      assert (Htg : incl (tgt_names (carried argts)) ns)
        by exact (tgt_names_incl_of_Forall _ Hca).
      assert (Hinc : incl (decl ++ tgt_names (carried argts)) ns)
        by (apply incl_app; assumption).
      assert (Hargsc : Forall (st_scoped ns) (List.map fst argts)).
      { apply Forall_forall. intros X HX.
        apply in_map_iff in HX as (t & Ht & Htin); subst X.
        rewrite Forall_forall in Hfa.
        exact (st_scoped_weaken _ _ _ Hinc (Hfa t Htin)). }
      assert (Hck' : st_scoped ns ckty)
        by exact (st_scoped_weaken _ _ _ Hdns (Hclk _ _ Hck)).
      assert (Hf2 : Forall2 (fun x b => Env.find x env = Some b) xs outs)
        by (eapply CALLS.mmap_find_env_Forall2; exact Houts).
      assert (Hout' : Forall (fun x => In x ns) outs).
      { apply Forall_forall. intros x Hx. apply Hxs.
        rewrite (Forall2_sec_of env xs outs Hf2). exact Hx. }
      assert (Hbk : In base_ty ckty)
        by exact (assign_clk_type_base env base_ty _ ckty Hck).
      rewrite Hcs. apply rooted_cmerge.
      - exact (generate_constraints_rooted base_ty rst_ty sg
                 (List.map fst argts) ckty (fst rstty) outs cs0 sti sti
                 (sig_nodup _ _ Esg)
                 (call_subst_fresh_from_scope_fresh ns sg _ _ _ _
                    (ns_fresh _ _ Esg) Hargsc Hck' Hrsc Hout')
                 (proj1 (sig_rooted _ _ Esg)) (proj2 (sig_rooted _ _ Esg))
                 Hbk Hrin Hgc).
      - apply rooted_cmerge; [|exact Hrr].
        exact (lexps_rooted_win_intro es (exp_rooted_win_list es) argts s sti
                 Hns Hargs).
    Qed.

    Lemma generate_lgen_constraint_rooted_win :
      forall ckenv xs es cs s s',
        incl (minted s s') ns ->
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv xs es cs s s' Hns H.
      unfold generate_lgen_constraint in H.
      apply sec_bind_inv in H as (ts & s1 & Hts & H).
      apply sec_bind_inv in H as (bs & s2 & Hbs & H).
      apply option_to_sec_inv in Hbs as (_ & ?); subst s2.
      assert (Hl : sec_le s1 s')
        by (eapply generate_lvars_constraints_sec_le; exact H).
      eapply generate_lvars_constraints_rooted; [|exact H].
      apply carried_rooted_iff.
      apply (lexps_rooted_win_intro es (exp_rooted_win_list es) ts s s1);
        [|exact Hts].
      apply (minted_incl_sub s s s1 s' ns);
        [apply sec_le_refl|exact Hl|exact Hns].
    Qed.

    Lemma generate_ldef_constraint_rooted_win :
      forall ckenv x e cs s s',
        incl (minted s s') ns ->
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv x e cs s s' Hns H.
      apply generate_ldef_constraint_inv in H
        as (ck & ckty & tf & b & s1 & Hfc & Hcka & Hte & Hb & Hs1 & Hcs).
      subst s1. rewrite Hcs.
      apply constraints_rooted_cmerge. split.
      - constructor; [|constructor].
        exact (constraint_rooted_head env base_ty rst_ty ck ckty tf [b] Hcka).
      - pose proof (exp_rooted_win_all e [tf] s s' Hns Hte) as Hr.
        rewrite carried_single in Hr. exact Hr.
    Qed.

    (** What the reset of a call contributes: rooted, at the level, scoped. *)
    Lemma reset_facts :
      forall e1 s s1 a1 rck,
        incl (minted s s1) ns ->
        assign_lexp_type G env base_ty rst_ty e1 s = OK ([a1], s1) ->
        assign_clk_type env base_ty (hd Cbase (LSyn.clockof e1)) = Some rck ->
        constraints_rooted base_ty rst_ty
          (snd (ljoin (lvar rst_ty) (ljoin a1 (rck, []))))
        /\ In rst_ty (fst (ljoin (lvar rst_ty) (ljoin a1 (rck, []))))
        /\ st_scoped ns (fst (ljoin (lvar rst_ty) (ljoin a1 (rck, [])))).
    Proof.
      intros e1 s s1 a1 rck Hw1 Ht1 Hrck.
      destruct (lexp_scoped_tgt_all G env base_ty rst_ty decl Hdk Hclk
                  Hsgs e1 [a1] s s1 Ht1) as (Hfa1 & _).
      inversion Hfa1 as [|? ? Hsa1 ?]; subst.
      pose proof (tgt_names_incl_of_Forall _
                    (lexp_carried_minted_all G env base_ty rst_ty e1
                       [a1] s s1 ns Hw1 Ht1)) as Htg1.
      rewrite !snd_ljoin, snd_lvar, !fst_ljoin, fst_lvar.
      cbn [snd]. rewrite cmerge_nil, cmerge_nil2. repeat split.
      - pose proof (exp_rooted_win_all e1 [a1] s s1 Hw1 Ht1) as Hr.
        rewrite carried_single in Hr. exact Hr.
      - apply in_merge_left. now left.
      - apply st_scoped_merge;
          [intros y0 [Hy0|[]]; subst y0; apply Hdns; exact (proj1 (proj2 Hdk))|].
        apply st_scoped_merge.
        + eapply st_scoped_weaken;
            [apply incl_app; [exact Hdns|exact Htg1]|exact Hsa1].
        + exact (st_scoped_weaken _ _ _ Hdns (Hclk _ _ Hrck)).
    Qed.

    Lemma rst_ty_in_ns : In rst_ty ns.
    Proof. apply Hdns. exact (proj1 (proj2 Hdk)). Qed.

    Lemma generate_lone_constraint_rooted_win :
      forall ckenv ys e cs s s',
        incl (minted s s') ns ->
        incl (CALLS.sec_of env ys) ns ->
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv ys e cs s s' Hns Hys Hgen.
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      1-9: destruct ys as [|x [|y ys]];
        [eapply generate_lgen_constraint_rooted_win; [exact Hns|exact Hgen]
        |eapply generate_ldef_constraint_rooted_win; [exact Hns|exact Hgen]
        |eapply generate_lgen_constraint_rooted_win; [exact Hns|exact Hgen]].
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (Hrck & ?); subst s3.
        assert (Hl1 : sec_le s s1)
          by (eapply assign_lexp_type_sec_le; exact Ht1).
        assert (Hl2 : sec_le s1 s')
          by (eapply generate_lcall_constraint_sec_le; exact Hgen).
        assert (Hw1 : incl (minted s s1) ns)
          by (apply (minted_incl_sub s s s1 s' ns);
              [apply sec_le_refl|exact Hl2|exact Hns]).
        assert (Hw2 : incl (minted s1 s') ns)
          by (apply (minted_incl_sub s s1 s' s' ns);
              [exact Hl1|apply sec_le_refl|exact Hns]).
        destruct (reset_facts e1 s s1 a1 rck Hw1 Ht1 Hrck)
          as (Hr1 & Hr2 & Hr3).
        eapply generate_lcall_constraint_rooted_win;
          [exact Hw2|exact Hys|exact Hr1|exact Hr2|exact Hr3|exact Hgen].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - eapply generate_lcall_constraint_rooted_win;
          [exact Hns|exact Hys| | |  |exact Hgen].
        + rewrite snd_lvar. constructor.
        + rewrite fst_lvar. now left.
        + rewrite fst_lvar. intros y0 [Hy0|[]]; subst y0. exact rst_ty_in_ns.
    Qed.

    Lemma generate_lsplit_constraints_rooted_win :
      forall ckenv es xs cs s s',
        incl (minted s s') ns ->
        incl (CALLS.sec_of env xs) ns ->
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv es. induction es as [|e es IH]; intros xs cs s s' Hns Hxs Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        assert (Hl1 : sec_le s s1)
          by (eapply generate_lone_constraint_sec_le; exact Hc).
        assert (Hl2 : sec_le s1 s2)
          by (eapply generate_lsplit_constraints_sec_le; exact Hcr).
        apply constraints_rooted_app.
        + eapply generate_lone_constraint_rooted_win; [| |exact Hc].
          * apply (minted_incl_sub s s s1 s2 ns);
              [apply sec_le_refl|exact Hl2|exact Hns].
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_firstn_any ident (numstreams e) xs y Hy).
        + eapply IH; [| |exact Hcr].
          * apply (minted_incl_sub s s1 s2 s2 ns);
              [exact Hl1|apply sec_le_refl|exact Hns].
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_skipn_any ident (numstreams e) xs y Hy).
    Qed.

    Lemma generate_leqn_constraint_rooted_win :
      forall ckenv eqn cs s s',
        incl (minted s s') ns ->
        incl (CALLS.sec_of env (fst eqn)) ns ->
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv eqn cs s s' Hns Hxs Hgen.
      destruct eqn as (xs & es). cbn [fst] in Hxs.
      destruct es as [|e [|e2 es2]].
      - eapply generate_lgen_constraint_rooted_win; [exact Hns|exact Hgen].
      - rewrite <- generate_lone_is_leqn in Hgen.
        eapply generate_lone_constraint_rooted_win; [exact Hns|exact Hxs|exact Hgen].
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            (eapply generate_lsplit_constraints_rooted_win;
             [exact Hns|exact Hxs|exact Hgen]).
        + destruct e; try destruct o;
            (eapply generate_lgen_constraint_rooted_win;
             [exact Hns|exact Hgen]).
    Qed.

    Theorem generate_leqns_constraints_rooted_win :
      forall ckenv eqs cs s s',
        incl (minted s s') ns ->
        incl (CALLS.sec_of env (vars_defined eqs)) ns ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        constraints_rooted base_ty rst_ty cs.
    Proof.
      intros ckenv eqs. induction eqs as [|eqn eqs IH];
        intros cs s s' Hns Hxs Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc. constructor.
      - rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        assert (Hl1 : sec_le s s1)
          by (eapply generate_leqn_constraint_sec_le; exact Hc1).
        assert (Hl2 : sec_le s1 s2)
          by (eapply generate_leqns_constraints_sec_le; exact Hc2).
        rewrite vars_defined_cons_eq, sec_of_app in Hxs.
        apply constraints_rooted_app.
        + eapply generate_leqn_constraint_rooted_win; [| |exact Hc1].
          * apply (minted_incl_sub s s s1 s2 ns);
              [apply sec_le_refl|exact Hl2|exact Hns].
          * eapply incl_tran; [|exact Hxs]. apply incl_appl, incl_refl.
        + eapply IH; [| |exact Hc2].
          * apply (minted_incl_sub s s1 s2 s2 ns);
              [exact Hl1|apply sec_le_refl|exact Hns].
          * eapply incl_tran; [|exact Hxs]. apply incl_appr, incl_refl.
    Qed.

  End RawRooted.

  (** * Item 6: a generated signature is good

      [signature_good] for one node is item 7 instantiated at that node.  The
      three list facts it asks for come from the node record and the naming
      pass: the defined variables are the locals and the outputs by [n_defd],
      they are distinct by [NoDup_vars_defined_n_eqs], and the separation of
      declared names from minted ones is
      [generate_lnode_scoped_env_st_fresh_sec], read at the window. *)

  Lemma Permutation_flat_map :
    forall {A B : Type} (f : A -> list B) xs ys,
      Permutation xs ys -> Permutation (flat_map f xs) (flat_map f ys).
  Proof.
    intros A B f xs ys H.
    induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
    - reflexivity.
    - cbn [flat_map]. apply Permutation_app_head. exact IH.
    - cbn [flat_map]. rewrite !app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    - etransitivity; [exact IH1|exact IH2].
  Qed.

  Lemma sec_of_Permutation :
    forall env xs ys,
      Permutation xs ys ->
      Permutation (CALLS.sec_of env xs) (CALLS.sec_of env ys).
  Proof.
    intros env xs ys H. unfold CALLS.sec_of. now apply Permutation_flat_map.
  Qed.

  (** The arity half of [wl_equation], which is the one item 7's split rule
      needs; the other half is about the expressions. *)
  Lemma wl_node_arity :
    forall (P : global) (n : node),
      wl_node P n ->
      Forall (fun eq => length (fst eq) = length (LSyn.annots (snd eq)))
        n.(n_eqs).
  Proof.
    intros P n Hwl. unfold wl_node in Hwl.
    rewrite Forall_forall in Hwl. apply Forall_forall.
    intros eq Hin. destruct eq as (xs, es). cbn [fst snd].
    destruct (Hwl (xs, es) Hin) as (_ & Hlen). exact Hlen.
  Qed.

  (** The naming pass allocates below its final state and the generator mints
      from there upwards, so a declared security name is never a minted one.
      Both namespaces are [sec]: the separation is by index. *)
  Lemma env_apart_from_minted :
    forall ns envs names stN name env s s',
      SECLNG.generate_lnode_scoped_env_st ns = OK (envs, names, stN) ->
      find_node_env name envs = Some env ->
      sec_le stN s ->
      forall x b, Env.find x env = Some b -> ~ In b (minted s s').
  Proof.
    intros ns envs names stN name env s s' Hgen Henv Hle x b Hb Hin.
    apply minted_spec in Hin as (j & Hsj & _ & Hbj).
    exact (SECLNG.generate_lnode_scoped_env_st_fresh_sec ns envs names stN
             name env x b j Hgen Henv Hb (Pos.le_trans stN s j Hle Hsj) Hbj).
  Qed.

  Theorem generate_lnode_sig_good :
    forall (G : secglobal) (P : global) (n : node) env aux sg st0 st1,
      env_injective env ->
      wl_node P n ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      signature_good sg.
  Proof.
    intros G P n env aux sg st0 st1 Hinj Hwl Hsep Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & cty & rty & inp & out & locals & cns
          & _ & _ & _ & _ & Hout & Hloc & Hcns & ?); subst sg.
    assert (get_mappings (List.map fst n.(n_vars)) env = Some locals) as Hgl
        by (eapply get_mappings_from_node_eq; exact Hloc).
    assert (get_mappings (List.map fst n.(n_out)) env = Some out) as Hgo
        by (eapply get_mappings_from_node_eq; exact Hout).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hlo
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Hou
        by (eapply get_mappings_from_node_sec_of; exact Hout).
    (** the defined variables are the locals and the outputs *)
    assert (Permutation (CALLS.sec_of env (vars_defined n.(n_eqs)))
                        (locals ++ out)) as Hperm.
    { rewrite Hlo, Hou, <- sec_of_app, <- map_app.
      apply sec_of_Permutation. exact (n_defd n). }
    (** and they are distinct, which [env] injectivity carries to the names *)
    assert (NoDup (List.map fst n.(n_vars) ++ List.map fst n.(n_out)))
      as Hndv.
    { rewrite <- map_app.
      eapply Permutation_NoDup; [|exact (NoDup_vars_defined_n_eqs n)].
      exact (n_defd n). }
    assert (NoDup (locals ++ out)) as Hnd.
    { eapply get_mappings_nodup_gen; [exact Hndv|exact Hinj|].
      exact (get_mappings_app (List.map fst n.(n_vars))
               (List.map fst n.(n_out)) env locals out Hgl Hgo). }
    assert (forall o, In o out -> exists x, Env.find x env = Some o) as Hoe.
    { intros o Ho.
      destruct (get_mappings_In (List.map fst n.(n_out)) env out o Hgo Ho)
        as (x & _ & Hx).
      now exists x. }
    unfold signature_good. cbn [s_constraints s_out].
    exact (generate_leqns_constraints_published_wf G env cty rty
             (lnode_clock_env n) n.(n_eqs) cns st0 st1 locals out
             Hsep (wl_node_arity P n Hwl) Hperm Hnd Hoe Hcns).
  Qed.

  (** * Item 6: a generated signature is scoped

      [simplify_scoped_weak] at [scope := signature_scope sg] and
      [ds := locals ++ minted st0 st1].  One instantiation of the equation
      dispatch serves both of its premises: at [S := decl ++ tgt_names cns],
      where [decl] is the node's declared security names together with its
      two auxiliary levels.  The second premise is that, weakened along
      [tgt_names cns ⊆ decl ++ minted] -- item 7.  The third splits: a local
      is a target, also by item 7, and a minted name is a target *if it
      occurs*, because the same scoping says an occurring name is declared
      or a target and a minted name is not declared. *)

  Lemma clk_scoped_of_env :
    forall (env0 : Env.t ident) D ct ck ckty,
      In ct D ->
      (forall x b, Env.find x env0 = Some b -> In b D) ->
      assign_clk_type env0 ct ck = Some ckty ->
      st_scoped D ckty.
  Proof.
    intros env0 D ct ck. induction ck as [|ck IH x b]; intros ckty Hct Henv H.
    - cbn in H. inversion H; subst ckty.
      intros y [Hy|[]]; subst y; exact Hct.
    - cbn in H.
      destruct (assign_clk_type env0 ct ck) as [c0|] eqn:Hc0; [|discriminate H].
      destruct (Env.find x env0) as [xty|] eqn:Hx; [|discriminate H].
      cbn in H. inversion H; subst ckty.
      apply st_scoped_merge;
        [apply (IH c0 Hct Henv); reflexivity
        |intros y [Hy|[]]; subst y; exact (Henv _ _ Hx)].
  Qed.

  Theorem generate_lnode_sig_scoped :
    forall (G : secglobal) (P : global) (n : node) env aux sg st0 st1,
      env_injective env ->
      secglobal_scoped G ->
      wl_node P n ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      (forall clk_id rst_id ct rt,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          Env.find clk_id env = Some ct ->
          Env.find rst_id env = Some rt ->
          forall x b, Env.find x env = Some b ->
            In b (CALLS.sec_of env
                    (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  ++ [ct; rt])) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      signature_scoped sg.
  Proof.
    intros G P n env aux sg st0 st1 Hinj Hsgs Hwl Hsep Hrange Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    pose proof (Hrange ci ri ct rt Haux Hct Hrt) as Hrg.
    assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
        by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
        by (eapply get_mappings_from_node_sec_of; exact Hout).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt]).
    assert (Hsplit : decl = (inp ++ locals ++ out) ++ [ct; rt])
        by (unfold decl; rewrite Hi, Hl, Ho, !map_app, !sec_of_app;
            reflexivity).
    (** no declared name was minted *)
    assert (Hdm : forall d, In d decl -> ~ In d (minted st0 st1)).
    { intros d Hd. unfold decl in Hd. apply in_app_or in Hd as [Hd|Hd].
      - unfold CALLS.sec_of in Hd. apply in_flat_map in Hd as (x & _ & Hd).
        destruct (Env.find x env) as [b|] eqn:Hx; [|contradiction].
        destruct Hd as [Hd|[]]; subst b. exact (Hsep x d Hx).
      - destruct Hd as [Hd|[Hd|[]]]; subst d;
          [exact (Hsep ci ct Hct)|exact (Hsep ri rt Hrt)]. }
    assert (Hdk : decl_ok env ct rt decl).
    { split; [|split].
      - unfold decl. apply in_or_app. right. now left.
      - unfold decl. apply in_or_app. right. right. now left.
      - exact Hrg. }
    assert (Hclk : clk_scoped env ct decl).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env; [|exact Hrg|exact Hck].
      unfold decl. apply in_or_app. right. now left. }
    (** item 7: every target is a defined name or a minted one *)
    destruct (generate_leqns_constraints_shape G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (minted st0 st1)
                (incl_refl _) Hsep (wl_node_arity P n Hwl) Hcns)
      as (ms & Hm & Hms).
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) decl).
    { unfold decl. eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    assert (Htb : incl (tgt_names cns) (decl ++ minted st0 st1)).
    { eapply incl_tran; [eapply tgt_names_of_targets_of; exact Hm|].
      apply incl_app;
        [eapply incl_tran; [exact Hdefd|apply incl_appl, incl_refl]
        |eapply incl_tran; [exact Hms|apply incl_appr, incl_refl]]. }
    (** the scoping, at the scope that carries the dichotomy *)
    set (S := decl ++ tgt_names cns).
    assert (HclkS : clk_scoped env ct S).
    { intros ck ckty Hck.
      eapply st_scoped_weaken;
        [unfold S; apply incl_appl, incl_refl|exact (Hclk ck ckty Hck)]. }
    assert (Hcsc : constraints_scoped S cns).
    { eapply generate_leqns_constraints_scoped;
        [exact Hsgs|exact HclkS| |eapply exps_scoped_in_of_decl;
           [exact Hdk|exact Hclk|exact Hsgs|unfold S; apply incl_appl,
            incl_refl]
        |eapply incl_tran; [exact Hdefd|unfold S; apply incl_appl, incl_refl]
        |unfold S; apply incl_appr, incl_refl|exact Hcns].
      unfold S, decl. apply in_or_app. left. apply in_or_app. right.
      right. now left. }
    assert (Hcol : constraints_scoped S (collapse cns))
        by (apply collapse_scoped; exact Hcsc).
    assert (Hlen1c : Forall singleton_rhs cns).
    { pose proof (generate_leqns_constraints_len1 G env ct rt
                    (lnode_clock_env n) n.(n_eqs) cns st0 st1 Hcns) as Hl1.
      rewrite Forall_forall in Hl1. apply Forall_forall.
      intros c Hc. specialize (Hl1 c Hc).
      destruct c as (lhs, rhs). cbn [snd] in Hl1 |- *.
      destruct rhs as [|b [|? ?]]; [discriminate Hl1|now exists b
                                   |discriminate Hl1]. }
    assert (Hlen1 : Forall singleton_rhs (collapse cns))
        by (apply collapse_singleton_rhs;
            exact (generate_leqns_constraints_len1 G env ct rt
                     (lnode_clock_env n) n.(n_eqs) cns st0 st1 Hcns)).
    (** and the elimination *)
    unfold signature_scoped. cbn [s_constraints s_in s_out s_clk s_reset].
    eapply simplify_scoped_weak.
    - (** distinct *)
      apply NoDup_app'.
      + rewrite Hl, <- (get_mappings_from_node_sec_of _ _ _ Hloc).
        eapply get_mappings_nodup_gen;
          [|exact Hinj|eapply get_mappings_from_node_eq; exact Hloc].
        rewrite <- fst_NoDupMembers.
        pose proof (n_nodup n) as Hnd.
        repeat rewrite app_assoc in Hnd.
        apply NoDupMembers_app_l in Hnd.
        apply NoDupMembers_app_l in Hnd.
        apply NoDupMembers_app_r in Hnd. exact Hnd.
      + apply minted_NoDup.
      + apply Forall_forall. intros y Hy Hin. apply (Hdm y); [|exact Hin].
        rewrite Hsplit. apply in_or_app. left.
        apply in_or_app. right. apply in_or_app. left. exact Hy.
    - (** scoped, after moving [decl ++ tgt_names cns] into place *)
      eapply constraints_scoped_weaken; [|exact Hcol].
      intros y Hy. unfold S in Hy. apply in_app_or in Hy as [Hy|Hy].
      + rewrite Hsplit in Hy. apply in_app_or in Hy as [Hy|Hy].
        * apply in_app_or in Hy as [Hy|Hy];
            [apply in_or_app; left; apply in_or_app; now left|].
          apply in_app_or in Hy as [Hy|Hy];
            [apply in_or_app; right; apply in_or_app; now left
            |apply in_or_app; left; apply in_or_app; right;
             apply in_or_app; now left].
        * apply in_or_app. left. apply in_or_app. right.
          apply in_or_app. now right.
      + apply Htb in Hy. apply in_app_or in Hy as [Hy|Hy].
        * rewrite Hsplit in Hy. apply in_app_or in Hy as [Hy|Hy].
          -- apply in_app_or in Hy as [Hy|Hy];
               [apply in_or_app; left; apply in_or_app; now left|].
             apply in_app_or in Hy as [Hy|Hy];
               [apply in_or_app; right; apply in_or_app; now left
               |apply in_or_app; left; apply in_or_app; right;
                apply in_or_app; now left].
          -- apply in_or_app. left. apply in_or_app. right.
             apply in_or_app. now right.
        * apply in_or_app. right. apply in_or_app. now right.
    - (** a target, or absent *)
      intros d Hd. apply in_app_or in Hd as [Hd|Hd].
      + (** a local: defined by some equation, so item 7 gives it a
            constraint, and [collapse] keeps the target *)
        left. apply collapse_rhs_in.
        eapply Permutation_in; [apply Permutation_sym; exact Hm|].
        apply in_map_iff. exists d. split; [reflexivity|].
        apply in_or_app. left.
        rewrite Hl in Hd. unfold CALLS.sec_of in Hd |- *.
        apply in_flat_map in Hd as (x & Hx & Hdx).
        apply in_flat_map. exists x. split; [|exact Hdx].
        eapply Permutation_in; [apply Permutation_sym; exact (n_defd n)|].
        rewrite map_app. apply in_or_app. now left.
      + (** a minted name: a target if it occurs at all *)
        destruct (In_dec ident_eq_dec d (tgt_names (collapse cns)))
          as [Ht|Ht].
        * left. exact (In_tgt_names_target (collapse cns) d Hlen1 Ht).
        * right. intros (c & Hc & Hx).
          assert (In d S) as Hin
              by (eapply constraints_scoped_In; [exact Hcol|exact Hc|exact Hx]).
          unfold S in Hin. apply in_app_or in Hin as [Hin|Hin].
          -- exact (Hdm d Hin Hd).
          -- apply Ht. apply target_In_tgt_names. apply collapse_rhs_in.
             exact (In_tgt_names_target cns d Hlen1c Hin).
  Qed.

  (** * Item 6: the published scope is duplicate-free

      The interface names are distinct because the node's variables are
      ([node_NoDup]) and [env] is injective; the two auxiliary levels are
      distinct from them, and from each other, because their *ids* are --
      which is what the naming pass gives -- and injectivity carries that to
      the levels. *)

  Lemma NoDup_app_mid :
    forall {A : Type} (a b c : list A),
      NoDup (a ++ b ++ c) -> NoDup (a ++ c).
  Proof.
    intros A a b c H.
    eapply NoDup_app_r with (xs := b).
    eapply Permutation_NoDup; [|exact H].
    apply perm_mid3.
  Qed.

  Theorem generate_lnode_sig_scope_nodup :
    forall (G : secglobal) (n : node) env aux sg st0 st1,
      env_injective env ->
      (forall clk_id rst_id,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          clk_id <> rst_id
          /\ ~ In clk_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
          /\ ~ In rst_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      NoDup (signature_scope sg).
  Proof.
    intros G n env aux sg st0 st1 Hinj Haux0 Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    destruct (Haux0 ci ri Haux) as (Hne & Hnc & Hnr).
    assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
        by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
        by (eapply get_mappings_from_node_sec_of; exact Hout).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    (** the whole interface, as one duplicate-free list *)
    assert (Hall : NoDup (inp ++ locals ++ out)).
    { rewrite Hi, Hl, Ho, <- !sec_of_app, <- !map_app.
      rewrite <- (get_mappings_from_node_sec_of
                    (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) env _
                    (get_mappings_from_node_app _ _ _ _ _ _ Hinp
                       (get_mappings_from_node_app _ _ _ _ _ _ Hloc Hout))).
      eapply get_mappings_nodup_gen;
        [apply node_NoDup|exact Hinj
        |eapply get_mappings_from_node_eq;
         exact (get_mappings_from_node_app _ _ _ _ _ _ Hinp
                  (get_mappings_from_node_app _ _ _ _ _ _ Hloc Hout))]. }
    assert (Hio : NoDup (inp ++ out))
        by (eapply NoDup_app_mid; exact Hall).
    (** and the two levels, which injectivity separates from the rest *)
    assert (Hnotin : forall d, In d (inp ++ out) -> d <> ct /\ d <> rt).
    { intros d Hd.
      assert (exists x,
                 In x (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 /\ Env.find x env = Some d) as (x & Hx & Hxe).
      { apply in_app_or in Hd as [Hd|Hd].
        - rewrite Hi in Hd. unfold CALLS.sec_of in Hd.
          apply in_flat_map in Hd as (x & Hx & Hdx).
          destruct (Env.find x env) as [b|] eqn:Hxe; [|contradiction].
          destruct Hdx as [Hdx|[]]; subst b.
          exists x. split; [|exact Hxe].
          rewrite !map_app. apply in_or_app. now left.
        - rewrite Ho in Hd. unfold CALLS.sec_of in Hd.
          apply in_flat_map in Hd as (x & Hx & Hdx).
          destruct (Env.find x env) as [b|] eqn:Hxe; [|contradiction].
          destruct Hdx as [Hdx|[]]; subst b.
          exists x. split; [|exact Hxe].
          rewrite !map_app. apply in_or_app. right.
          apply in_or_app. now right. }
      split; intros Heq; subst d.
      - apply Hnc. replace ci with x;
          [exact Hx|eapply Hinj; [exact Hxe|exact Hct|reflexivity]].
      - apply Hnr. replace ri with x;
          [exact Hx|eapply Hinj; [exact Hxe|exact Hrt|reflexivity]]. }
    unfold signature_scope. cbn [s_in s_out s_clk s_reset].
    rewrite app_assoc.
    apply NoDup_app'; [exact Hio| |].
    - constructor; [|constructor; [intros []|constructor]].
      intros [Hc|[]]. apply Hne. symmetry in Hc.
      eapply Hinj; [exact Hct|exact Hrt|exact Hc].
    - apply Forall_forall. intros d Hd.
      destruct (Hnotin d Hd) as (Hdc & Hdr).
      intros [Hx|[Hx|[]]]; symmetry in Hx;
        [exact (Hdc Hx)|exact (Hdr Hx)].
  Qed.

  (** * Item 1: a generated signature is rooted

      The raw constraints are rooted at the node's two auxiliary levels
      ([generate_leqns_constraints_rooted_all]); [collapse] only joins sources,
      and [simplify] only substitutes an eliminated name by its own source,
      which is rooted too.  What makes the substitution safe is that neither
      level is ever a target or an eliminated name: both are the images of
      auxiliary ids that are not declared variables of the node. *)

  Lemma join_into_rooted :
    forall b r lhs rhs acc,
      In b lhs -> In r lhs ->
      constraints_rooted b r acc ->
      constraints_rooted b r (join_into lhs rhs acc).
  Proof.
    intros b r lhs rhs acc Hb Hr.
    induction acc as [|[l rr] acc IH]; intros Hacc.
    - simpl. constructor; [|constructor]. split; assumption.
    - inversion Hacc as [|? ? Hc Hcs]; subst. simpl.
      destruct (st_eq_dec rhs rr) as [Heq|Hneq].
      + constructor; [|exact Hcs].
        destruct Hc as (Hc1 & Hc2). cbn [fst] in Hc1, Hc2 |- *.
        split; apply in_merge_left; assumption.
      + constructor; [exact Hc|exact (IH Hcs)].
  Qed.

  Lemma collapse_rooted :
    forall b r cns,
      constraints_rooted b r cns ->
      constraints_rooted b r (collapse cns).
  Proof.
    intros b r cns. induction cns as [|[l rr] cns IH]; intros H; simpl.
    - constructor.
    - inversion H as [|? ? Hc Hcs]; subst.
      destruct Hc as (Hc1 & Hc2). cbn [fst] in Hc1, Hc2.
      apply join_into_rooted; [exact Hc1|exact Hc2|exact (IH Hcs)].
  Qed.

  Lemma sec_of_apart :
    forall env ci ct xs,
      env_injective env ->
      Env.find ci env = Some ct ->
      ~ In ci xs ->
      ~ In ct (CALLS.sec_of env xs).
  Proof.
    intros env ci ct xs Hinj Hci Hn Hin.
    unfold CALLS.sec_of in Hin. apply in_flat_map in Hin as (x & Hx & Hd).
    destruct (Env.find x env) as [b|] eqn:Hxe; [|contradiction].
    destruct Hd as [Hd|[]]; subst b.
    apply Hn. replace ci with x; [exact Hx|].
    eapply Hinj; [exact Hxe|exact Hci|reflexivity].
  Qed.

  Theorem generate_lnode_sig_rooted :
    forall (G : secglobal) (P : global) (n : node) env aux sg st0 st1,
      env_injective env ->
      secglobal_scoped G ->
      (forall f sg,
          find_signature f G = Some sg ->
          NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out))) ->
      (forall f sg,
          find_signature f G = Some sg ->
          CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
          /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints)) ->
      wl_node P n ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      (forall clk_id rst_id ct rt,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          Env.find clk_id env = Some ct ->
          Env.find rst_id env = Some rt ->
          (forall x b, Env.find x env = Some b ->
             In b (CALLS.sec_of env
                     (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                   ++ [ct; rt]))
          /\ (forall f sg,
                 find_signature f G = Some sg ->
                 scope_fresh
                   ((CALLS.sec_of env
                       (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                     ++ [ct; rt]) ++ minted st0 st1) sg)) ->
      (forall clk_id rst_id,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          ~ In clk_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
          /\ ~ In rst_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
      /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints).
  Proof.
    intros G P n env aux sg st0 st1 Hinj Hsgs Hnd Hroot Hwl Hsep Hrf Haux0 Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    destruct (Haux0 ci ri Haux) as (Hnc & Hnr).
    destruct (Hrf ci ri ct rt Haux Hct Hrt) as (Hrg & Hnsf).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt]).
    assert (Hdk : decl_ok env ct rt decl).
    { split; [|split].
      - unfold decl. apply in_or_app. right. now left.
      - unfold decl. apply in_or_app. right. right. now left.
      - exact Hrg. }
    assert (Hclk : clk_scoped env ct decl).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env; [|exact Hrg|exact Hck].
      unfold decl. apply in_or_app. right. now left. }
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) decl).
    { unfold decl. eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    assert (Hcr : constraints_rooted ct rt cns).
    { eapply (generate_leqns_constraints_rooted_win G env ct rt decl
                (decl ++ minted st0 st1) Hdk Hclk Hsgs);
        [apply incl_appl, incl_refl|exact Hnsf|exact Hnd|exact Hroot
        |apply incl_appr, incl_refl
        |eapply incl_tran; [exact Hdefd|apply incl_appl, incl_refl]
        |exact Hcns]. }
    (** the levels are neither declared names nor minted ones *)
    assert (Hav : forall y, In y (CALLS.sec_of env (List.map fst n.(n_vars)))
                            -> y <> ct /\ y <> rt).
    { intros y Hy. split; intros ->.
      - eapply (sec_of_apart env ci ct); [exact Hinj|exact Hct| |exact Hy].
        intros Hin. apply Hnc. rewrite !map_app.
        apply in_or_app. right. apply in_or_app. now left.
      - eapply (sec_of_apart env ri rt); [exact Hinj|exact Hrt| |exact Hy].
        intros Hin. apply Hnr. rewrite !map_app.
        apply in_or_app. right. apply in_or_app. now left. }
    destruct (generate_leqns_constraints_shape G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (minted st0 st1)
                (incl_refl _) Hsep (wl_node_arity P n Hwl) Hcns)
      as (ms & Hm & Hms).
    assert (Htg : forall y, In y (tgt_names cns) -> y <> ct /\ y <> rt).
    { intros y Hy.
      apply (tgt_names_of_targets_of _ _ Hm) in Hy.
      apply in_app_or in Hy as [Hy|Hy].
      - assert (In y (CALLS.sec_of env (List.map fst (n.(n_vars) ++ n.(n_out)))))
          as Hy'
            by (eapply Permutation_in;
                [apply sec_of_Permutation; exact (n_defd n)|exact Hy]).
        split; intros ->.
        + eapply (sec_of_apart env ci ct); [exact Hinj|exact Hct| |exact Hy'].
          intros Hin. apply Hnc. rewrite map_app in Hin. rewrite !map_app.
          apply in_or_app. right. exact Hin.
        + eapply (sec_of_apart env ri rt); [exact Hinj|exact Hrt| |exact Hy'].
          intros Hin. apply Hnr. rewrite map_app in Hin. rewrite !map_app.
          apply in_or_app. right. exact Hin.
      - apply Hms in Hy. split; intros ->;
          [exact (Hsep ci _ Hct Hy)|exact (Hsep ri _ Hrt Hy)]. }
    assert (Hrs : constraints_rooted ct rt
                    (simplify (collapse cns) (locals ++ minted st0 st1))).
    { apply simplify_rooted with (keep := [ct; rt]).
      - now left.
      - right. now left.
      - intros d Hd [Hdc|[Hdr|[]]]; subst d; apply in_app_or in Hd as [Hd|Hd].
        + rewrite Hl in Hd. exact (proj1 (Hav _ Hd) Logic.eq_refl).
        + exact (Hsep ci _ Hct Hd).
        + rewrite Hl in Hd. exact (proj2 (Hav _ Hd) Logic.eq_refl).
        + exact (Hsep ri _ Hrt Hd).
      - intros c Hc y Hy [Hyc|[Hyr|[]]].
        + assert (In (snd c) (List.map snd (collapse cns)))
            by (apply in_map; exact Hc).
          apply (proj1 (collapse_rhs_in cns _)) in H.
          apply in_map_iff in H as (c' & Hc'e & Hc').
          assert (In y (tgt_names cns)) as Hyt.
          { unfold tgt_names. apply in_flat_map. exists c'.
            split; [exact Hc'|].
            destruct c' as (l', r'). destruct c as (l, r).
            cbn [snd] in Hc'e, Hy |- *. subst r'. exact Hy. }
          exact (proj1 (Htg y Hyt) (Logic.eq_sym Hyc)).
        + assert (In (snd c) (List.map snd (collapse cns)))
            by (apply in_map; exact Hc).
          apply (proj1 (collapse_rhs_in cns _)) in H.
          apply in_map_iff in H as (c' & Hc'e & Hc').
          assert (In y (tgt_names cns)) as Hyt.
          { unfold tgt_names. apply in_flat_map. exists c'.
            split; [exact Hc'|].
            destruct c' as (l', r'). destruct c as (l, r).
            cbn [snd] in Hc'e, Hy |- *. subst r'. exact Hy. }
          exact (proj2 (Htg y Hyt) (Logic.eq_sym Hyr)).
      - apply collapse_rooted. exact Hcr. }
    cbn [s_constraints s_clk s_reset]. split.
    - unfold CALLS.all_sources_have. eapply Forall_impl; [|exact Hrs].
      intros c (Hc1 & Hc2). exact Hc1.
    - unfold CALLS.all_sources_have. eapply Forall_impl; [|exact Hrs].
      intros c (Hc1 & Hc2). exact Hc2.
  Qed.

  (** * Item 3: what the naming pass delivers, node by node

      Everything the signature fold needs of an environment, read off the run
      that built it: the environment is injective, its values are [sec] names
      allocated inside the node's own stretch of the counter, and the two
      auxiliary names are the first two of that stretch. *)

  Lemma generate_local_env_for_lnode_facts :
    forall (n : node) st env rec st',
      generate_local_env_for_lnode n st = OK ((env, rec), st') ->
      env_injective env
      /\ (forall x b, Env.find x env = Some b ->
            exists k, b = Ids.gensym Ids.sec k
                      /\ (st <= k)%positive /\ (k < st')%positive)
      /\ rec.(nclk) = Ids.gensym Ids.sec st
      /\ rec.(nrst) = Ids.gensym Ids.sec (Pos.succ st).
  Proof.
    intros n st env rec st' Hgen.
    unfold generate_local_env_for_lnode in Hgen.
    eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
    eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
    eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hgen).
    eapply name_bind_inv in Hgen as (inst_env0 & st3i & Hinstgen & Hret).
    unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
    unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
    unfold NMret in Hret. inversion Hret; subst env rec st'.
    repeat split.
    - destruct (fresh_map_list_env_props
                  ([Ids.gensym Ids.sec st; Ids.gensym Ids.sec (Pos.succ st)]
                     ++ List.map fst (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))
                  (Env.empty _) (Pos.succ (Pos.succ st)) env0 st3)
        as [_ Hnodup].
      + intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
      + constructor.
      + exact Hmap.
      + eapply env_values_nodup_injective; eauto.
    - intros x b Hfind.
      destruct (fresh_map_list_find_ge_start_from_empty _ _ _ _ _ _ Hmap Hfind)
        as (k & Hk & Hlo & Hhi).
      exists k. split; [exact Hk|]. split.
      + eapply Pos.le_trans; [|exact Hlo].
        eapply Pos.le_trans; apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
      + eapply Pos.lt_le_trans; [exact Hhi|].
        eapply fresh_inst_map_list_state_monotone; eauto.
  Qed.

  Lemma generate_lnode_scoped_env'_state_mono :
    forall ns envs acc st envs' aux st',
      generate_lnode_scoped_env' ns envs acc st = OK ((envs', aux), st') ->
      (st <= st')%positive.
  Proof.
    induction ns as [|n ns IH]; intros envs acc st envs' aux st' Hgen.
    - cbn in Hgen. unfold NMret in Hgen. inversion Hgen; subst.
      apply Pos.le_refl.
    - cbn in Hgen.
      eapply name_bind2_inv in Hgen as (local_env & rec & st1 & Hlocal & Hgen).
      eapply name_bind_inv in Hgen as (envs1 & st2 & Hins & Hgen).
      eapply name_bind2_inv in Hgen as (envs2 & aux2 & st3 & Hrec & Hret).
      unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
      unfold fresh_insert_node_env in Hins.
      destruct (Env.mem n.(n_name) envs); [discriminate Hins|].
      unfold insert_node_env, NMret in Hins. inversion Hins; subst envs1 st2.
      eapply Pos.le_trans;
        [eapply generate_local_env_for_lnode_state_monotone; exact Hlocal
        |eapply IH; exact Hrec].
  Qed.

  (** * Item 2: the program fold

      The invariant of the accumulator, and the step that preserves it.  The
      per-node theorems take a handful of facts about the node's environment;
      each is read off the naming run here, and the three that are about the
      accumulator -- scoped, rooted, duplicate-free -- are carried as
      invariants.  What keeps a later node's names off an earlier node's scope
      is the counter: the accumulator's scopes lie below the state the naming
      pass was in when it reached this node, and this node's names lie above
      it. *)

  Definition secglobal_all (Q : signature -> Prop) (G : secglobal) : Prop :=
    forall f sg, find_signature f G = Some sg -> Q sg.

  Lemma secglobal_all_cons :
    forall (Q : signature -> Prop) (sg : signature) (G : secglobal),
      Q sg -> secglobal_all Q G -> secglobal_all Q (sg :: G).
  Proof.
    intros Q sg G Hq HG f sg' Hf. simpl in Hf.
    destruct (ident_eqb sg.(s_name) f) eqn:E.
    - inversion Hf; subst. exact Hq.
    - eapply HG; eauto.
  Qed.

  Definition sig_nd (sg : signature) : Prop :=
    NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)).

  Definition sig_rt (sg : signature) : Prop :=
    CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
    /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints).

  Lemma sig_nd_of_scope :
    forall sg, NoDup (signature_scope sg) -> sig_nd sg.
  Proof.
    intros sg H. unfold sig_nd. unfold signature_scope in H.
    eapply Permutation_NoDup; [|exact H].
    apply Permutation_app_head.
    exact (Permutation_sym
             (Permutation_app_comm [sg.(s_clk); sg.(s_reset)] sg.(s_out))).
  Qed.

  Lemma sec_of_In_intro :
    forall env xs w b,
      In w xs -> Env.find w env = Some b -> In b (CALLS.sec_of env xs).
  Proof.
    intros env xs w b Hw Hf. unfold CALLS.sec_of.
    apply in_flat_map. exists w. split; [exact Hw|].
    rewrite Hf. now left.
  Qed.

  Definition lsig_inv (stN low : positive) (acc : secglobal)
    (st : sec_state) : Prop :=
    secglobal_good acc /\ secglobal_scoped acc
    /\ secglobal_all sig_nd acc /\ secglobal_all sig_rt acc
    /\ secglobal_scope_bounded_above acc low
    /\ sec_le stN st.

  Lemma lsig_inv_nil :
    forall stN low st, sec_le stN st -> lsig_inv stN low [] st.
  Proof.
    intros stN low st Hle. unfold lsig_inv.
    refine (conj secglobal_good_nil (conj secglobal_scoped_nil
              (conj _ (conj _ (conj (secglobal_scope_bounded_above_nil low)
                                    Hle))))).
    - intros f sg H. discriminate H.
    - intros f sg H. discriminate H.
  Qed.

  Lemma sec_of_In_inv :
    forall env xs b,
      In b (CALLS.sec_of env xs) ->
      exists x, In x xs /\ Env.find x env = Some b.
  Proof.
    intros env xs b Hb. unfold CALLS.sec_of in Hb.
    apply in_flat_map in Hb as (x & Hx & Hb).
    destruct (Env.find x env) as [b0|] eqn:Hf; [|contradiction].
    destruct Hb as [Hb|[]]. subst b0. exists x. split; assumption.
  Qed.

  Lemma lsig_step :
    forall (P : global) (all : list node) envs aux stN
           (n : node) env (r : node_aux_names) st0 stl
           acc st sg st1,
      generate_lnode_scoped_env_st all = OK (envs, aux, stN) ->
      find_node_env n.(n_name) envs = Some env ->
      get_node_aux n.(n_name) aux = Some (r.(nclk), r.(nrst)) ->
      generate_local_env_for_lnode n st0 = OK ((env, r), stl) ->
      (st0 <= stN)%positive ->
      wl_node P n ->
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      lsig_inv stN st0 acc st ->
      generate_lnode_sig acc n env aux st = OK (sg, st1) ->
      lsig_inv stN stl (sg :: acc) st1.
  Proof.
    intros P all envs aux stN n env r st0 stl acc st sg st1
           Hfull Hfind Haux Hloc Hst0 Hwl Hsub
           (Hgood & Hsc & Hnd & Hroot & Hbd & Hle) Hsig.
    destruct (generate_local_env_for_lnode_facts n st0 env r stl Hloc)
      as (Hinj & Hrng & Hclk & Hrst).
    assert (Hsep : forall x b, Env.find x env = Some b ->
                               ~ In b (minted st st1))
      by (intros x b Hb;
          exact (env_apart_from_minted all envs aux stN n.(n_name) env st st1
                   Hfull Hfind Hle x b Hb)).
    assert (Hlev : forall ci ri,
               get_node_aux n.(n_name) aux = Some (ci, ri) ->
               ci = r.(nclk) /\ ri = r.(nrst)).
    { intros ci ri Ha. rewrite Haux in Ha. inversion Ha. split; reflexivity. }
    assert (Hrange : forall ct rt,
               Env.find r.(nclk) env = Some ct ->
               Env.find r.(nrst) env = Some rt ->
               forall x b, Env.find x env = Some b ->
                 In b (CALLS.sec_of env
                         (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                       ++ [ct; rt])).
    { intros ct rt Hct Hrt x b Hb.
      destruct (generate_local_env_for_lnode_domain n st0 env r stl x b Hloc Hb)
        as [Hx|[Hx|Hx]].
      - subst x. rewrite Hct in Hb. inversion Hb; subst b.
        apply in_or_app. right. now left.
      - subst x. rewrite Hrt in Hb. inversion Hb; subst b.
        apply in_or_app. right. right. now left.
      - apply in_or_app. left. eapply sec_of_In_intro; [|exact Hb].
        rewrite !map_app in Hx |- *.
        apply in_app_or in Hx as [Hx|Hx]; [apply in_or_app; now left|].
        apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; right;
          apply in_or_app; [now right|now left]. }
    assert (Hfr : forall ct rt,
               Env.find r.(nclk) env = Some ct ->
               Env.find r.(nrst) env = Some rt ->
               forall f sg0, find_signature f acc = Some sg0 ->
                 scope_fresh
                   ((CALLS.sec_of env
                       (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                     ++ [ct; rt]) ++ minted st st1) sg0).
    { intros ct rt Hct Hrt f sg0 Hf.
      eapply scope_fresh_from_bounds; [|eapply Hbd; exact Hf].
      intros ty Hty. apply in_app_or in Hty as [Hty|Hty].
      - apply in_app_or in Hty as [Hty|Hty].
        + apply sec_of_In_inv in Hty as (x & _ & Hx).
          destruct (Hrng x ty Hx) as (k & Hk & Hlo & _). eauto.
        + destruct Hty as [Hty|[Hty|[]]]; subst ty.
          * destruct (Hrng _ _ Hct) as (k & Hk & Hlo & _). eauto.
          * destruct (Hrng _ _ Hrt) as (k & Hk & Hlo & _). eauto.
      - apply minted_spec in Hty as (k & Hlo & _ & Hk).
        exists k. split; [exact Hk|].
        eapply Pos.le_trans; [exact Hst0|].
        eapply Pos.le_trans; [exact Hle|exact Hlo]. }
    assert (Haux0 : forall ci ri,
               get_node_aux n.(n_name) aux = Some (ci, ri) ->
               ci <> ri
               /\ ~ In ci (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
               /\ ~ In ri (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { intros ci ri Ha. destruct (Hlev ci ri Ha) as (-> & ->).
      rewrite Hclk, Hrst. repeat split.
      - intros Heq. apply gensym_injective in Heq as [_ Heq].
        exact (Pos.succ_discr st0 Heq).
      - intros Hin. exact (lnode_var_not_sec n _ st0 Hsub Hin Logic.eq_refl).
      - intros Hin. exact (lnode_var_not_sec n _ (Pos.succ st0) Hsub Hin
                             Logic.eq_refl). }
    assert (Hgd : signature_good sg)
      by exact (generate_lnode_sig_good acc P n env aux sg st st1 Hinj Hwl
                  Hsep Hsig).
    assert (Hscd : signature_scoped sg).
    { eapply generate_lnode_sig_scoped;
        [exact Hinj|exact Hsc|exact Hwl|exact Hsep| |exact Hsig].
      intros ci ri ct rt Ha Hct Hrt.
      destruct (Hlev ci ri Ha) as (-> & ->).
      exact (Hrange ct rt Hct Hrt). }
    assert (Hnodup : NoDup (signature_scope sg)).
    { eapply generate_lnode_sig_scope_nodup;
        [exact Hinj| |exact Hsig].
      exact Haux0. }
    assert (Hrooted : sig_rt sg).
    { eapply generate_lnode_sig_rooted;
        [exact Hinj|exact Hsc|exact Hnd|exact Hroot|exact Hwl|exact Hsep| |
         |exact Hsig].
      - intros ci ri ct rt Ha Hct Hrt0.
        destruct (Hlev ci ri Ha) as (-> & ->). split.
        + exact (Hrange ct rt Hct Hrt0).
        + exact (Hfr ct rt Hct Hrt0).
      - intros ci ri Ha. destruct (Haux0 ci ri Ha) as (_ & H1 & H2).
        split; assumption. }
    destruct (lnode_sig_inv env acc n aux sg st st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux' & Hct & Hrt' & Hinp & Hout & Hloc' & Hcns & Hsg).
    destruct (Hlev ci ri Haux') as (-> & ->).
    refine (conj (secglobal_good_cons sg acc Hgd Hgood)
              (conj (secglobal_scoped_cons sg acc Hscd Hsc)
                 (conj (secglobal_all_cons sig_nd sg acc
                          (sig_nd_of_scope sg Hnodup) Hnd)
                    (conj (secglobal_all_cons sig_rt sg acc Hrooted Hroot)
                       (conj _ _))))).
    - apply secglobal_scope_bounded_above_cons.
      + intros ty Hty. subst sg. cbn [signature_scope s_in s_out s_clk s_reset]
          in Hty.
        assert (Hall : forall x b, Env.find x env = Some b ->
                         exists k, b = Ids.gensym Ids.sec k
                                   /\ (k < stl)%positive)
          by (intros x b Hb; destruct (Hrng x b Hb) as (k & Hk & _ & Hhi);
              eauto).
        assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
            by (eapply get_mappings_from_node_sec_of; exact Hinp).
        assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
            by (eapply get_mappings_from_node_sec_of; exact Hout).
        apply in_app_or in Hty as [Hty|Hty].
        * rewrite Hi in Hty. apply sec_of_In_inv in Hty as (x & _ & Hx).
          exact (Hall x ty Hx).
        * apply in_app_or in Hty as [Hty|Hty].
          -- rewrite Ho in Hty. apply sec_of_In_inv in Hty as (x & _ & Hx).
             exact (Hall x ty Hx).
          -- destruct Hty as [Hty|[Hty|[]]]; subst ty;
               [exact (Hall _ _ Hct)|exact (Hall _ _ Hrt')].
      + eapply secglobal_scope_bounded_above_monotone; [exact Hbd|].
        eapply generate_local_env_for_lnode_state_monotone; exact Hloc.
    - subst sg.
      eapply Pos.le_trans; [exact Hle|].
      eapply generate_leqns_constraints_sec_le; exact Hcns.
  Qed.

  Theorem generate_all_lsignatures'_inv :
    forall (P : global) (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall ns envs0 acc0 st0,
        NoDup (List.map n_name ns) ->
        Forall (wl_node P) ns ->
        Forall (fun n => PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs))
          ns ->
        generate_lnode_scoped_env' ns envs0 acc0 st0
          = OK ((envsF, auxF), stN) ->
        forall acc st G stf,
          lsig_inv stN st0 acc st ->
          generate_all_lsignatures' acc ns envsF auxF st = OK (G, stf) ->
          lsig_inv stN stN G stf.
  Proof.
    intros P all envsF auxF stN Hfull.
    induction ns as [|n ns IH];
      intros envs0 acc0 st0 Hnd Hwl Hsub Hrun acc st G stf Hinv Hgen.
    - cbn in Hrun. unfold NMret in Hrun. inversion Hrun; subst.
      cbn in Hgen. inversion Hgen; subst. exact Hinv.
    - cbn in Hrun.
      apply name_bind_inv in Hrun as (p & stl & Hloc & Hrun).
      destruct p as (le0 & r0).
      apply name_bind_inv in Hrun as (envs1 & st2 & Hins & Hrun).
      apply name_bind_inv in Hrun as (q & st3 & Hrec & Hret).
      destruct q as (envs2 & aux2).
      unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
      assert (envs1 = Env.add n.(n_name) le0 envs0 /\ st2 = stl)
        as (? & ?).
      { unfold fresh_insert_node_env in Hins.
        destruct (Env.mem n.(n_name) envs0); [discriminate Hins|].
        unfold insert_node_env, NMret in Hins.
        inversion Hins; split; reflexivity. }
      subst envs1 st2.
      inversion Hnd as [|z zs Hnotin Hnd']; subst z zs.
      inversion Hwl as [|n' ns' Hwln Hwl']; subst n' ns'.
      inversion Hsub as [|n' ns' Hsubn Hsub']; subst n' ns'.
      assert (Hrname : r0.(nname) = n.(n_name)).
      { unfold generate_local_env_for_lnode in Hloc.
        apply name_bind_inv in Hloc as (c1 & s1 & _ & Hl).
        apply name_bind_inv in Hl as (c2 & s2 & _ & Hl).
        apply name_bind_inv in Hl as (c3 & s3 & _ & Hl).
        apply name_bind_inv in Hl as (c4 & s4 & _ & Hret0).
        unfold NMret in Hret0. inversion Hret0. reflexivity. }
      assert (Hfind : find_node_env n.(n_name) envsF = Some le0).
      { eapply generate_lnode_scoped_env'_envs_mono;
          [exact Hrec|exact Hnotin|].
        unfold find_node_env. apply Env.gss. }
      assert (Haux : get_node_aux n.(n_name) auxF
                     = Some (r0.(nclk), r0.(nrst))).
      { rewrite (generate_lnode_scoped_env'_aux_mono ns
                   (Env.add n.(n_name) le0 envs0) (r0 :: acc0) stl
                   envsF auxF stN n.(n_name) Hrec Hnotin).
        unfold get_node_aux. cbn [find_node_names].
        rewrite Hrname, ident_eqb_refl. reflexivity. }
      assert (Hst0 : (st0 <= stN)%positive).
      { eapply Pos.le_trans;
          [eapply generate_local_env_for_lnode_state_monotone; exact Hloc
          |eapply generate_lnode_scoped_env'_state_mono; exact Hrec]. }
      cbn in Hgen.
      destruct (generate_lnode_sig_scoped_env acc n envsF auxF st)
        as [[sg stg]|e] eqn:Hs; [|discriminate Hgen].
      unfold generate_lnode_sig_scoped_env in Hs. rewrite Hfind in Hs.
      eapply (IH (Env.add n.(n_name) le0 envs0) (r0 :: acc0) stl Hnd' Hwl'
                 Hsub' Hrec (sg :: acc) stg G stf); [|exact Hgen].
      eapply lsig_step;
        [exact Hfull|exact Hfind|exact Haux|exact Hloc|exact Hst0
        |exact Hwln|exact Hsubn|exact Hinv|exact Hs].
  Qed.

  (** * The program, in the shape the consumers ask for

      The four per-signature families -- [signature_good], scoped, the
      duplicate-free scope, rooted -- for every signature the program driver
      publishes, given the naming run and the node-level hygiene the pipeline
      already establishes ([wl_node], the prefix inclusion). *)
  Theorem generate_all_lsignatures_inv :
    forall (P : global) ns envs aux stN st GL,
      generate_lnode_scoped_env_st ns = OK (envs, aux, stN) ->
      NoDup (List.map n_name ns) ->
      Forall (wl_node P) ns ->
      Forall (fun n => PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs)) ns ->
      sec_le stN st ->
      generate_all_lsignatures_scoped_env ns envs aux st = OK GL ->
      secglobal_good GL /\ secglobal_scoped GL
      /\ secglobal_all sig_nd GL /\ secglobal_all sig_rt GL.
  Proof.
    intros P ns envs aux stN st GL Hfull Hnd Hwl Hsub Hle Hgen.
    pose proof Hfull as Hfull0.
    unfold generate_all_lsignatures_scoped_env in Hgen.
    destruct (generate_all_lsignatures' [] ns envs aux st)
      as [[G stf]|e] eqn:Hall; [|discriminate Hgen].
    inversion Hgen; subst G.
    unfold generate_lnode_scoped_env_st in Hfull.
    destruct (generate_lnode_scoped_env' ns (Env.empty _) [] init_state)
      as [[[envs0 aux0] st0]|e] eqn:Hrun; [|discriminate Hfull].
    inversion Hfull; subst envs0 aux0 st0.
    destruct (generate_all_lsignatures'_inv P ns envs aux stN Hfull0 ns
                (Env.empty _) [] init_state Hnd Hwl Hsub Hrun [] st GL stf
                (lsig_inv_nil stN init_state st Hle) Hall)
      as (Hg & Hs & Hn & Hr & _).
    exact (conj Hg (conj Hs (conj Hn Hr))).
  Qed.

End SecLusTypingCorrectness.
