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

End SecLusTypingCorrectness.
