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

  End RawTargets.

End SecLusTypingCorrectness.
