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

  End RawTargets.

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

End SecLusTypingCorrectness.
