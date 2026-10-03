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

  End RawTargets.

End SecLusTypingCorrectness.
