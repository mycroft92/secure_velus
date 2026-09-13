(** Leg A: transcription preserves generated constraints exactly.

    Of the three passes between Lustre and NLustre, transcription is the one
    that introduces no variables and preserves a node's interface
    definitionally.  So on the normalized fragment the two constraint
    generators do not merely preserve satisfiability -- they agree.  That is
    what this file proves, and it is the reason the Lustre leg can be stated
    as an equality where the NLustre-to-Stc leg needs [preserves_on].

    The expression-level halves live in [SecLTyping.v], next to the generator
    they are about.  What is here is the equation level and above, which needs
    both generators in scope. *)

From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Lia.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLUSNLUSTRANSLATION
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX  Ids Op)
  (CESyn          : CESYNTAX     Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Lat            : Lattice)
  (Import SecT    : SECTYPES Lat)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE  Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (NLMem          : MEMORIES Ids Op CESyn NLSyn)
  (NLIsD          : ISDEFINED Ids Op CESyn NLSyn NLMem)
  (NLIsF          : ISFREE Ids Op CESyn NLSyn CEIsF)
  (NLClo          : NLCLOCKING Ids Op CESyn NLSyn NLOrd NLMem NLIsD CEIsF NLIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import SECNL   : SECNLUSTYPING Ids Op SC CESyn NLSyn SIG NAMEGEN CEIsF CEClo
                      SECCET NLOrd NLMem NLIsD NLIsF NLClo).

  Import SECMONADNotations.

  Lemma res_to_sec_OK : forall {A : Type} (a : A) st,
      res_to_sec (OK a) st = OK (a, st).
  Proof. reflexivity. Qed.

  (** * Inverting the NLustre side

      What the NLustre generator computed, read back out of a successful run.
      It is state-pure, so the state comes back unchanged. *)

  Lemma nl_EqDef_inv : forall G env base_ty rst_ty x ck ce cs st st',
      generate_eqn_constraint G env base_ty rst_ty (NLSyn.EqDef x ck ce) st
        = OK (cs, st') ->
      exists ckty sa b,
        assign_clk_type env base_ty ck = Some ckty
        /\ assign_cexp_type env ce = Some sa
        /\ Env.find x env = Some b
        /\ cs = [(merge (merge [rst_ty] ckty) sa, [b])]
        /\ st' = st.
  Proof.
    intros G env base_ty rst_ty x ck ce cs st st' H.
    unfold generate_eqn_constraint in H.
    eapply sec_bind_inv in H as (ckty & st1 & Hck & H).
    eapply sec_bind_inv in H as (sa & st2 & Hsa & H).
    eapply sec_bind_inv in H as (b & st3 & Hb & Hret).
    unfold ret in Hret. inv Hret.
    unfold option_to_sec in Hck.
    destruct (assign_clk_type env base_ty ck) eqn:E1; try discriminate.
    unfold ret in Hck. inv Hck.
    unfold option_to_sec in Hsa.
    destruct (assign_cexp_type env ce) eqn:E2; try discriminate.
    unfold ret in Hsa. inv Hsa.
    unfold find_env in Hb.
    destruct (Env.find x env) eqn:E3; try discriminate.
    unfold ret in Hb. inv Hb.
    exists ckty, sa, b. repeat split; auto.
  Qed.

  Lemma nl_EqFby_inv : forall G env base_ty rst_ty x ck c0 le cs st st',
      generate_eqn_constraint G env base_ty rst_ty (NLSyn.EqFby x ck c0 le) st
        = OK (cs, st') ->
      exists ckty sa b,
        assign_clk_type env base_ty ck = Some ckty
        /\ assign_exp_type env le = Some sa
        /\ Env.find x env = Some b
        /\ cs = [(merge (merge [rst_ty] ckty) sa, [b])]
        /\ st' = st.
  Proof.
    intros G env base_ty rst_ty x ck c0 le cs st st' H.
    unfold generate_eqn_constraint in H.
    eapply sec_bind_inv in H as (ckty & st1 & Hck & H).
    eapply sec_bind_inv in H as (sa & st2 & Hsa & H).
    eapply sec_bind_inv in H as (b & st3 & Hb & Hret).
    unfold ret in Hret. inv Hret.
    unfold option_to_sec in Hck.
    destruct (assign_clk_type env base_ty ck) eqn:E1; try discriminate.
    unfold ret in Hck. inv Hck.
    unfold option_to_sec in Hsa.
    destruct (assign_exp_type env le) eqn:E2; try discriminate.
    unfold ret in Hsa. inv Hsa.
    unfold find_env in Hb.
    destruct (Env.find x env) eqn:E3; try discriminate.
    unfold ret in Hb. inv Hb.
    exists ckty, sa, b. repeat split; auto.
  Qed.

  (** * Inverting the Lustre side

      What [to_equation] produced from a single-variable equation whose
      expression is neither a call nor a delay.  Isolating this is what keeps
      the theorem below uniform in the expression: [simpl] computes [to_cexp]
      away on the leaves, so the hypothesis a proof wants to use is not always
      there to be used, and each case has to rebuild it. *)

  Lemma to_equation_def_inv : forall cenv envo x e eq',
      (forall f args ro a, e <> Eapp f args ro a) ->
      (forall e0s es an, e <> Efby e0s es an) ->
      to_equation cenv envo ([x], [e]) = OK eq' ->
      exists ck ce,
        find_clock cenv x = OK ck
        /\ to_cexp e = OK ce
        /\ eq' = NLSyn.EqDef x ck ce.
  Proof.
    intros cenv envo x e eq' Hnapp Hnfby H.
    destruct e;
      try (exfalso; eapply Hnapp; reflexivity);
      try (exfalso; eapply Hnfby; reflexivity);
      (simpl in H; monadInv H; eexists; eexists;
       repeat split; try eassumption;
       first [ eassumption
             | simpl;
               repeat match goal with
                      | Hl : to_lexp _ = OK _ |- _ => rewrite Hl
                      end;
               reflexivity
             | reflexivity ]).
  Qed.

  Lemma to_equation_fby_inv : forall cenv envo x e0 e ans eq',
      to_equation cenv envo ([x], [Efby [e0] [e] ans]) = OK eq' ->
      exists ck c0 le,
        find_clock cenv x = OK ck
        /\ to_constant e0 = OK c0
        /\ to_lexp e = OK le
        /\ eq' = NLSyn.EqFby x ck c0 le.
  Proof.
    intros cenv envo x e0 e ans eq' H.
    simpl in H. monadInv H.
    eexists; eexists; eexists. repeat split; eassumption.
  Qed.

  (** * One equation, the definition shapes

      Stated NLustre-to-Lustre, not as an equality of the two [Sec]
      computations: equality is false where generation fails, since the two
      generators report different messages.  This is also the direction the
      expression lemmas give, and it is sufficient, because
      [SecNLusTypingTotality.source_signature_generation_total] says the
      NLustre generator succeeds on any ordered, well-clocked program and
      transcription supplies both.  So on a program that transcribes the
      NLustre side always succeeds, this hands the Lustre side the same
      constraints, and the two sets are then equal. *)

  Theorem to_equation_constraint_eq_def :
    forall G env base_ty rst_ty cenv envo x e eq' cs st st',
      to_equation cenv envo ([x], [e]) = OK eq' ->
      (forall f args ro a, e <> Eapp f args ro a) ->
      (forall e0s es an, e <> Efby e0s es an) ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv ([x], [e]) st
        = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo x e eq' cs st st' Htr Hnapp Hnfby Hnl.
    edestruct to_equation_def_inv as (ck & ce & Hck & Hce & Heq); eauto.
    subst eq'.
    eapply nl_EqDef_inv in Hnl
      as (cky & sy & by0 & Hcky & Hsy & Hby & Hcs & Hst).
    subst cs st'.
    destruct e;
      try (exfalso; eapply Hnapp; reflexivity);
      try (exfalso; eapply Hnfby; reflexivity);
      (eapply generate_ldef_constraint_eq; try eassumption;
       eapply to_cexp_assign_eq; eassumption).
  Qed.

  (** The delayed definition is where the equality stops, now that the
      generator types *both* operands of an [Efby].

      [to_constant] strips the [when]s off a normalized initial value and the
      NLustre rule types a literal constant, so the target constraint mentions
      only the second operand while the source mentions both.  The source is
      strictly stronger, which is the right way round for preservation, but
      the two constraint lists are no longer equal and neither is the
      signature global.

      Reaching preservation needs two things this file does not yet have.

      First, the leg has to run *Lustre to NLustre*.  The theorems below run
      the other way -- NLustre success hands the Lustre side the same result
      -- which was sound while the two agreed, and was justified by the
      NLustre generator being total on ordered well-clocked programs.  It no
      longer suffices: the Lustre fby rule looks up the [when] variables of
      the initial value, which the NLustre rule never mentions, so NLustre
      success does not imply Lustre success.  What the noninterference
      pull-back actually needs is the other direction anyway -- a secure
      Lustre node is one whose generated constraints are satisfied, and the
      NLustre node's must follow.  So [to_lexp_assign_eq] and
      [to_cexp_assign_eq] need their converses, which is the same induction.

      Second, [simplify] has to be crossed.  Both halves exist:
      [SecTypes.simplify_complete] recovers a valuation of the raw
      constraints from one of the simplified ones, and [simplify_is_correct]
      pushes a raw valuation forward.  Their side conditions --
      [wf_constraints] of the Lustre raw list, and the locals being disjoint
      from the signature scope -- are the Lustre analogues of what
      [SecNLusTypingCorrectness.v] proves for NLustre, and are not yet
      available.

      Kept below: the three shapes where the generators still agree exactly,
      and the inversion lemmas for both sides, which the preservation proof
      will reuse unchanged. *)

  (** * Preservation, one equation at a time

      [entails] is the relation the leg now proves: any ground instantiation
      satisfying the Lustre constraints satisfies the NLustre ones.  Three of
      the four shapes give it by the two lists being equal; the delayed
      definition gives it by the source constraint being strictly stronger. *)

  Definition entails (cs' cs : list constraint) : Prop :=
    map snd cs' = map snd cs
    /\ (forall dlt, listSatisfiable dlt cs' -> listSatisfiable dlt cs).

  (** The right-hand sides coincide as well as the satisfaction implication.
      That is free -- every shape constrains exactly the variables the
      equation defines, and only the fby's left-hand side differs -- and it is
      what carries [wf_constraints] from the NLustre side, which
      [SecNLusTypingCorrectness.v] already proves, to the Lustre one, which
      the [simplify] bridge needs. *)

  Lemma entails_refl : forall cs, entails cs cs.
  Proof. intros cs. split; [reflexivity|intros dlt H; exact H]. Qed.

  Lemma entails_rhs : forall cs' cs, entails cs' cs -> map snd cs' = map snd cs.
  Proof. intros cs' cs [H _]. exact H. Qed.

  Lemma entails_sat : forall cs' cs dlt,
      entails cs' cs -> listSatisfiable dlt cs' -> listSatisfiable dlt cs.
  Proof. intros cs' cs dlt [_ H]. apply H. Qed.

  Theorem to_equation_entails_def :
    forall GL GN env base_ty rst_ty cenv envo x e eq' cs' st st',
      to_equation cenv envo ([x], [e]) = OK eq' ->
      (forall f args ro a, e <> Eapp f args ro a) ->
      (forall e0s es an, e <> Efby e0s es an) ->
      generate_leqn_constraint GL env base_ty rst_ty cenv ([x], [e]) st
        = OK (cs', st') ->
      exists cs,
        generate_eqn_constraint GN env base_ty rst_ty eq' st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    intros GL GN env base_ty rst_ty cenv envo x e eq' cs' st st' Htr Hnapp Hnfby Hl.
    edestruct to_equation_def_inv as (ck & ce & Hck & Hce & Heq); eauto.
    subst eq'.
    assert (Hld : generate_ldef_constraint GL env base_ty rst_ty cenv x e st
                  = OK (cs', st')).
    { destruct e;
        try (exfalso; eapply Hnapp; reflexivity);
        try (exfalso; eapply Hnfby; reflexivity);
        exact Hl. }
    eapply generate_ldef_constraint_inv in Hld
      as (ck2 & ckty & sa & rho & b & Hck2 & Hckty & He & Hb & Hcs').
    rewrite Hck in Hck2. inv Hck2.
    destruct (to_cexp_assign_rev _ _ _ _ _ _ _ _ _ Hce He)
      as (sa2 & Hts & Hnl & Hst).
    inv Hts; subst.
    eexists. split.
    - unfold generate_eqn_constraint.
      osec Hckty. osec Hnl. fsec Hb. reflexivity.
    - rewrite ?cmerge_nil, ?cmerge_nil2. apply entails_refl.
  Qed.

  (** The delayed definition: the one shape where the two disagree.  The
      source constraint joins in the initial value's type, which the target
      never mentions, so it is strictly stronger -- and all that is needed is
      monotonicity of satisfaction in the left-hand side. *)

  Lemma satisfiable_drop_middle : forall dlt X s0 s1 b,
      satisfiable dlt (merge X (merge s0 s1)) b ->
      satisfiable dlt (merge X s1) b.
  Proof.
    intros dlt X s0 s1 b H. unfold satisfiable in *.
    rewrite hm_ext_merge_eq in H |- *.
    rewrite hm_ext_merge_eq in H.
    eapply Lat.order_trans; [|exact H].
    apply Lat.join_least_upper_bound.
    - apply Lat.join_bound1.
    - eapply Lat.order_trans; [apply Lat.join_bound2|].
      apply Lat.join_bound2.
  Qed.

  Theorem to_equation_entails_fby :
    forall GL GN env base_ty rst_ty cenv envo x e0 e ans eq' cs' st st',
      to_equation cenv envo ([x], [Efby [e0] [e] ans]) = OK eq' ->
      generate_leqn_constraint GL env base_ty rst_ty cenv
        ([x], [Efby [e0] [e] ans]) st = OK (cs', st') ->
      exists cs,
        generate_eqn_constraint GN env base_ty rst_ty eq' st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    intros GL GN env base_ty rst_ty cenv envo x e0 e ans eq' cs' st st' Htr Hl.
    edestruct to_equation_fby_inv as (ck & c0 & le & Hck & Hc0 & Hle & Heq); eauto.
    subst eq'.
    rewrite gen_leqn_Efby in Hl.
    eapply generate_ldef_constraint_inv in Hl
      as (ck2 & ckty & sa & rho & b & Hck2 & Hckty & He & Hb & Hcs').
    rewrite Hck in Hck2. inv Hck2.
    (* decompose the fby's own type: both operands, joined *)
    rewrite assign_lexp_Efby in He.
    eapply sec_bind_inv in He as (ts0 & st1 & Hts0 & He).
    eapply sec_bind_inv in He as (us0 & st2 & Hus0 & He).
    destruct (ljoin_list_inv_single _ _ _ _ _ He)
      as (p & q & Hp & Hq & Hr & Hst2).
    subst ts0 us0 st2.
    apply assign_lexps_single_inv in Hts0.
    apply assign_lexps_single_inv in Hus0.
    destruct p as [s0 rho0]. destruct q as [s1 rho1].
    unfold ljoin in Hr. cbn [fst snd] in Hr. inv Hr.
    destruct (to_lexp_assign_rev _ _ _ _ _ _ _ _ _ Hle Hus0)
      as (s1' & Hq' & Hnl1 & Hst1). inv Hq'. subst.
    assert (Hst0 : st1 = st)
      by (eapply to_constant_assign_state; eassumption).
    subst st1.
    assert (Hplain : rho0 = []).
    { assert (Hp := to_constant_assign_plain _ _ _ _ _ _ _ _ _ Hc0 Hts0).
      apply Forall_inv in Hp. exact Hp. }
    subst rho0.
    eexists. split.
    - unfold generate_eqn_constraint.
      osec Hckty. osec Hnl1. fsec Hb. reflexivity.
    - split; [now rewrite cmerge_nil|]. intros dlt Hsat. constructor; [|constructor].
      unfold constraintSatisfiable.
      eapply satisfiable_drop_middle with (s0 := s0).
      unfold listSatisfiable in Hsat. rewrite Forall_forall in Hsat.
      apply (Hsat (merge (merge [rst_ty] ckty) (merge s0 s1'), [b])).
      apply cmerge_In. left. now left.
  Qed.

  (** * From [preserves_on] back to [entails]

      The call-site theorems in [SIFSignature.v] conclude [preserves_on],
      which allows the witness valuation to differ off the visible scope.  On
      this leg nothing needs that freedom: transcription introduces no
      variables, and an instantiated call block is scoped to the caller's own
      scope, so the witness can be transported back and the whole leg stays in
      [entails].  That is what avoids the private-extras discipline the
      NLustre-to-Stc leg has to carry. *)

  Lemma preserves_on_entails_sat : forall scope a b,
      constraints_scoped scope b ->
      preserves_on scope a b ->
      forall dlt, listSatisfiable dlt a -> listSatisfiable dlt b.
  Proof.
    intros scope a b Hsc Hp dlt Hsat.
    destruct (Hp dlt Hsat) as (dlt' & Hagree & Hsat').
    eapply listSatisfiable_ext; [exact Hsc | | exact Hsat'].
    intros x Hin. symmetry. now apply Hagree.
  Qed.

  (** * Two signature globals

      Up to here one signature global served both generators, which was right
      while the two agreed.  It is not right any more.  A callee whose body
      holds an [fby] with a non-constant initial value gets a strictly
      stronger Lustre signature than NLustre one -- that is the whole point of
      the corrected [fby] rule -- so the two accumulators diverge and a call
      site reads a different signature on each side.

      What survives is a relation between the two globals: name and interface
      fields agree, and the instantiated call blocks stand in the same
      entailment the leg proves everywhere else.  This is the Lustre analogue
      of [Signature_consistent] on the NLustre-to-Stc leg, and it is weaker in
      exactly one place: the reset actual is the same expression on both sides
      here, so only the equal-actuals call clause is needed. *)

  Definition Signature_call_entails (n1 n2 : signature) : Prop :=
    forall scope inptyp ckty rstty outtyp c1 c2 sa sa' sb sb',
      scope_fresh scope n1 ->
      call_subst_scoped scope inptyp ckty rstty outtyp ->
      call_subst_fresh n1 inptyp ckty rstty outtyp ->
      generate_constraints n1 inptyp ckty rstty outtyp sa = OK (c1, sa') ->
      generate_constraints n2 inptyp ckty rstty outtyp sb = OK (c2, sb') ->
      preserves_on scope c1 c2.

  Definition Signature_head_entails (n1 n2 : signature) : Prop :=
    n1.(s_name) = n2.(s_name)
    /\ signature_fields_agree n1 n2
    /\ Signature_call_entails n1 n2.

  Definition Signature_entails (G1 G2 : secglobal) : Prop :=
    forall f n1,
      find_signature f G1 = Some n1 ->
      exists n2,
        find_signature f G2 = Some n2
        /\ Signature_head_entails n1 n2.

  (** The call clause is not proved by hand: it is what
      [signatures_preserved_equal_calls_from_good] says about a pair of
      signatures already known to be preserved, and the node level supplies
      that pair. *)
  Lemma Signature_call_entails_from_preserved :
    forall n1 n2,
      signature_good n1 ->
      NoDup (signature_scope n1) ->
      signature_scoped n2 ->
      SIGPROOFS.signatures_preserved n1 n2 ->
      Signature_call_entails n1 n2.
  Proof.
    intros n1 n2 Hgood Hnd Hsc Hpres
           scope inptyp ckty rstty outtyp c1 c2 sa sa' sb sb'
           Hfresh Hscoped Hcf Hg1 Hg2.
    eapply SIGPROOFS.signatures_preserved_equal_calls_from_good; eauto.
  Qed.

  (** One instantiated call block entails the other.  The satisfaction half is
      the call clause, transported off [preserves_on] by
      [preserves_on_entails_sat]: the target block is scoped to the caller, so
      the witness valuation can be carried back.  The right-hand-side half
      does not look at either signature at all -- by
      [generate_constraints_shape] an instantiated block constrains exactly
      the caller's own result variables, one constraint each, whichever
      signature it came from. *)
  Lemma call_block_entails :
    forall scope n1 n2 inptyp ckty rstty outtyp c1 c2 sa sa' sb sb',
      Signature_call_entails n1 n2 ->
      signature_scoped n2 ->
      scope_fresh scope n1 ->
      call_subst_scoped scope inptyp ckty rstty outtyp ->
      call_subst_fresh n1 inptyp ckty rstty outtyp ->
      NoDup outtyp ->
      generate_constraints n1 inptyp ckty rstty outtyp sa = OK (c1, sa') ->
      generate_constraints n2 inptyp ckty rstty outtyp sb = OK (c2, sb') ->
      entails c1 c2.
  Proof.
    intros scope n1 n2 inptyp ckty rstty outtyp c1 c2 sa sa' sb sb'
           Hcall Hsc2 Hfresh Hscoped Hcf Hnd Hg1 Hg2.
    destruct Hscoped as [[Hinp [Hck Hout]] Hrst].
    split.
    - destruct (generate_constraints_shape _ _ _ _ _ _ _ _ Hnd Hg1) as [_ H1].
      destruct (generate_constraints_shape _ _ _ _ _ _ _ _ Hnd Hg2) as [_ H2].
      etransitivity; [exact H1|symmetry; exact H2].
    - eapply preserves_on_entails_sat with (scope := scope).
      + exact (generate_constraints_scoped n2 scope inptyp ckty rstty outtyp c2 sb sb'
                 Hsc2 Hinp Hck Hrst Hout Hg2).
      + eapply Hcall; eauto. split; [split; [|split]|]; eauto.
  Qed.

  (** * The call shapes

      Both NLustre call cases special-case an empty result list, and their
      match is flat, so a proof has to split [xs] before either side will
      reduce.  On the empty list both generators return the empty constraint
      list. *)

  Lemma Forall2_sec_mmap_assign_exp : forall env les tys st,
      Forall2 (fun le t => assign_exp_type env le = Some t) les tys ->
      SC.mmap (fun e => option_to_sec (assign_exp_type env e)) les st
      = OK (tys, st).
  Proof.
    intros env les tys st H. revert st.
    induction H as [|le t les tys Hle Hall IH]; intros st; simpl.
    - reflexivity.
    - osec Hle. ssec (IH st). reflexivity.
  Qed.

  Lemma nl_EqApp_inv : forall G env base_ty rst_ty x xs ck f les cs st st',
      generate_eqn_constraint G env base_ty rst_ty
        (NLSyn.EqApp (x :: xs) ck f les None) st = OK (cs, st') ->
      exists sg ckty inptyp outtyp sti,
        find_signature f G = Some sg
        /\ assign_clk_type env base_ty ck = Some ckty
        /\ Forall2 (fun le t => assign_exp_type env le = Some t) les inptyp
        /\ SC.mmap (fun y => find_env y env) (x :: xs) st = OK (outtyp, sti)
        /\ generate_constraints sg inptyp ckty [rst_ty] outtyp sti = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty x xs ck f les cs st st' H.
    unfold generate_eqn_constraint in H.
    destruct (find_signature f G) as [sg|] eqn:Esg; [|discriminate].
    eapply sec_bind_inv in H as (ckty & st1 & Hck & H).
    eapply sec_bind_inv in H as (inptyp & st2 & Hin & H).
    eapply sec_bind_inv in H as (outtyp & st3 & Hout & H).
    unfold option_to_sec in Hck.
    destruct (assign_clk_type env base_ty ck) eqn:E1; try discriminate.
    unfold ret in Hck. inv Hck.
    eapply sec_mmap_assign_exp_Forall2 in Hin as [Hst Hall]; subst st2.
    exists sg, ckty, inptyp, outtyp, st3.
    repeat split; auto.
  Qed.

  Lemma nl_EqApp_reset_inv :
    forall G env base_ty rst_ty x xs ck f les r ckr cs st st',
      generate_eqn_constraint G env base_ty rst_ty
        (NLSyn.EqApp (x :: xs) ck f les (Some (r, ckr))) st = OK (cs, st') ->
      exists sg ckty rty rstty inptyp outtyp sti,
        find_signature f G = Some sg
        /\ assign_clk_type env base_ty ck = Some ckty
        /\ Env.find r env = Some rty
        /\ assign_clk_type env base_ty ckr = Some rstty
        /\ Forall2 (fun le t => assign_exp_type env le = Some t) les inptyp
        /\ SC.mmap (fun y => find_env y env) (x :: xs) st = OK (outtyp, sti)
        /\ generate_constraints sg inptyp ckty
             (merge [rst_ty] (merge [rty] rstty)) outtyp sti = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty x xs ck f les r ckr cs st st' H.
    unfold generate_eqn_constraint in H.
    destruct (find_signature f G) as [sg|] eqn:Esg; [|discriminate].
    eapply sec_bind_inv in H as (ckty & st1 & Hck & H).
    eapply sec_bind_inv in H as (rty & st2 & Hrty & H).
    eapply sec_bind_inv in H as (rstty & st3 & Hrst & H).
    eapply sec_bind_inv in H as (inptyp & st4 & Hin & H).
    eapply sec_bind_inv in H as (outtyp & st5 & Hout & H).
    unfold option_to_sec in Hck.
    destruct (assign_clk_type env base_ty ck) eqn:E1; try discriminate.
    unfold ret in Hck. inv Hck.
    unfold find_env in Hrty.
    destruct (Env.find r env) eqn:E2; try discriminate.
    unfold ret in Hrty. inv Hrty.
    unfold option_to_sec in Hrst.
    destruct (assign_clk_type env base_ty ckr) eqn:E3; try discriminate.
    unfold ret in Hrst. inv Hrst.
    eapply sec_mmap_assign_exp_Forall2 in Hin as [Hst Hall]; subst st4.
    exists sg, ckty, rty, rstty, inptyp, outtyp, st5.
    repeat split; auto.
  Qed.

  Lemma to_equation_app_inv : forall cenv envo xs f args a eq',
      to_equation cenv envo (xs, [Eapp f args None a]) = OK eq' ->
      exists les,
        Errors.mmap to_lexp args = OK les
        /\ eq' = NLSyn.EqApp xs (find_base_clock (LSyn.clocksof args)) f les None.
  Proof.
    intros cenv envo xs f args a eq' H. simpl in H. monadInv H. eauto.
  Qed.

  Lemma to_equation_app_reset_inv :
    forall cenv envo xs f args r ty ckr nm a eq',
      to_equation cenv envo (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a])
        = OK eq' ->
      exists les,
        Errors.mmap to_lexp args = OK les
        /\ eq' = NLSyn.EqApp xs (find_base_clock (LSyn.clocksof args)) f les
                   (Some (r, ckr)).
  Proof.
    intros cenv envo xs f args r ty ckr nm a eq' H. simpl in H. monadInv H. eauto.
  Qed.

  Theorem to_equation_entails_app :
    forall G env base_ty rst_ty cenv envo xs f args a eq' cs' st st',
      to_equation cenv envo (xs, [Eapp f args None a]) = OK eq' ->
      generate_leqn_constraint G env base_ty rst_ty cenv
        (xs, [Eapp f args None a]) st = OK (cs', st') ->
      exists cs,
        generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    intros G env base_ty rst_ty cenv envo xs f args a eq' cs' st st' Htr Hl.
    edestruct to_equation_app_inv as (les & Hles & Heq); eauto. subst eq'.
    destruct xs as [|x xs'].
    - simpl in Hl. unfold ret in Hl. inv Hl.
      exists []. split; [reflexivity | apply entails_refl].
    - rewrite gen_leqn_Eapp in Hl.
      eapply generate_lcall_constraint_inv in Hl
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      destruct (to_lexps_assign_rev _ _ _ _ _ _ _ _ _ Hles Hargs)
        as (tys & Hargts & Hall & Hsti). subst argts sti.
      exists cs0. split.
      + unfold generate_eqn_constraint. rewrite Esg.
        osec Hck.
        ssec (Forall2_sec_mmap_assign_exp env les tys st Hall).
        ssec Houts.
        rewrite map_fst_plain in Hgc.
        unfold lvar in Hgc. cbn [fst] in Hgc. exact Hgc.
      + subst cs'. rewrite carried_plain.
        unfold lvar. cbn [snd]. rewrite !cmerge_nil. apply entails_refl.
  Qed.

  Theorem to_equation_entails_app_reset :
    forall G env base_ty rst_ty cenv envo xs f args r ty ckr nm a eq' cs' st st',
      to_equation cenv envo (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a])
        = OK eq' ->
      generate_leqn_constraint G env base_ty rst_ty cenv
        (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a]) st = OK (cs', st') ->
      exists cs,
        generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    intros G env base_ty rst_ty cenv envo xs f args r ty ckr nm a eq' cs' st st'
           Htr Hl.
    edestruct to_equation_app_reset_inv as (les & Hles & Heq); eauto. subst eq'.
    destruct xs as [|x xs'].
    - simpl in Hl. unfold ret in Hl. inv Hl.
      exists []. split; [reflexivity | apply entails_refl].
    - rewrite gen_leqn_Eapp_reset in Hl.
      eapply sec_bind_inv in Hl as (rty & sta & Hrty & Hl).
      eapply sec_bind_inv in Hl as (rstck & stb & Hrstck & Hl).
      apply find_env_inv in Hrty as [Hrty ?]; subst sta.
      apply option_to_sec_inv in Hrstck as [Hrstck ?]; subst stb.
      eapply generate_lcall_constraint_inv in Hl
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      destruct (to_lexps_assign_rev _ _ _ _ _ _ _ _ _ Hles Hargs)
        as (tys & Hargts & Hall & Hsti). subst argts sti.
      exists cs0. split.
      + unfold generate_eqn_constraint. rewrite Esg.
        osec Hck. fsec Hrty. osec Hrstck.
        ssec (Forall2_sec_mmap_assign_exp env les tys st Hall).
        ssec Houts.
        rewrite map_fst_plain in Hgc.
        unfold ljoin, lvar in Hgc. cbn [fst snd] in Hgc. exact Hgc.
      + subst cs'. rewrite carried_plain.
        unfold ljoin, lvar. cbn [snd]. rewrite !cmerge_nil. apply entails_refl.
  Qed.

  Theorem to_equation_constraint_eq_app :
    forall G env base_ty rst_ty cenv envo xs f args a eq' cs st st',
      to_equation cenv envo (xs, [Eapp f args None a]) = OK eq' ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv
        (xs, [Eapp f args None a]) st = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo xs f args a eq' cs st st' Htr Hnl.
    edestruct to_equation_app_inv as (les & Hles & Heq); eauto. subst eq'.
    destruct xs as [|x xs'].
    - (* a call defining nothing: both sides give the empty list *)
      simpl in Hnl. unfold ret in Hnl. inv Hnl. reflexivity.
    - eapply nl_EqApp_inv in Hnl
        as (sg & ckty & inptyp & outtyp & sti & Esg & Hck & Hall & Hout & Hgc).
      rewrite gen_leqn_Eapp.
      unfold generate_lcall_constraint. rewrite Esg.
      erewrite bind_OK by (unfold option_to_sec; rewrite Hck; reflexivity).
      erewrite bind_OK by (eapply to_lexps_assign_eq; eassumption).
      erewrite bind_OK by exact Hout.
      rewrite map_fst_plain.
      erewrite bind_OK by (unfold lvar; cbn [fst]; exact Hgc).
      unfold ret. rewrite carried_plain.
      unfold lvar. cbn [snd]. now rewrite !cmerge_nil.
  Qed.

  Theorem to_equation_constraint_eq_app_reset :
    forall G env base_ty rst_ty cenv envo xs f args r ty ckr nm a eq' cs st st',
      to_equation cenv envo (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a])
        = OK eq' ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv
        (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a]) st = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo xs f args r ty ckr nm a eq' cs st st'
           Htr Hnl.
    edestruct to_equation_app_reset_inv as (les & Hles & Heq); eauto. subst eq'.
    destruct xs as [|x xs'].
    - simpl in Hnl. unfold ret in Hnl. inv Hnl. reflexivity.
    - eapply nl_EqApp_reset_inv in Hnl
        as (sg & ckty & rty & rstty & inptyp & outtyp & sti
            & Esg & Hck & Hrty & Hrst & Hall & Hout & Hgc).
      rewrite gen_leqn_Eapp_reset.
      erewrite bind_OK by (unfold find_env; rewrite Hrty; reflexivity).
      erewrite bind_OK by (unfold option_to_sec; rewrite Hrst; reflexivity).
      unfold generate_lcall_constraint. rewrite Esg.
      erewrite bind_OK by (unfold option_to_sec; rewrite Hck; reflexivity).
      erewrite bind_OK by (eapply to_lexps_assign_eq; eassumption).
      erewrite bind_OK by exact Hout.
      rewrite map_fst_plain.
      erewrite bind_OK by (unfold ljoin, lvar; cbn [fst snd]; exact Hgc).
      unfold ret. rewrite carried_plain.
      unfold ljoin, lvar. cbn [snd]. now rewrite !cmerge_nil.
  Qed.

  (** * One equation, all shapes

      Every equation that transcribes is one of the four; the rest is case
      analysis. *)

  Lemma map_snd_app : forall (a b : list constraint),
      map snd (a ++ b) = map snd a ++ map snd b.
  Proof. induction a as [|c a IH]; intros b; simpl; auto. now rewrite IH. Qed.

  Lemma entails_app : forall a b a' b',
      entails a a' -> entails b b' -> entails (a ++ b) (a' ++ b').
  Proof.
    intros a b a' b' [Hra Hsa] [Hrb Hsb]. split.
    - rewrite !map_snd_app, Hra, Hrb. reflexivity.
    - intros dlt H.
      unfold listSatisfiable in *. rewrite Forall_app in H |- *.
      destruct H as [H1 H2]. split; [now apply Hsa | now apply Hsb].
  Qed.

  Ltac def_shape_e Htr Hl :=
    eapply to_equation_entails_def;
    [ exact Htr | intros; discriminate | intros; discriminate | exact Hl ].

  Theorem to_equation_entails :
    forall G env base_ty rst_ty cenv envo eq eq' cs' st st',
      to_equation cenv envo eq = OK eq' ->
      generate_leqn_constraint G env base_ty rst_ty cenv eq st = OK (cs', st') ->
      exists cs,
        generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    intros G env base_ty rst_ty cenv envo [xs es] eq' cs' st st' Htr Hl.
    destruct es as [|e [|e' es']];
      [simpl in Htr; discriminate | | simpl in Htr; discriminate].
    destruct e.
    1-4,6-9: (destruct xs as [|x [|]];
              [simpl in Htr; discriminate | | simpl in Htr; discriminate];
              def_shape_e Htr Hl).
    - (* Efby *)
      destruct l as [|e0 [|e0' l']]; destruct l0 as [|e1 [|e1' l0']];
        try (destruct xs as [|x [|]];
             [simpl in Htr; discriminate | | simpl in Htr; discriminate];
             solve [ def_shape_e Htr Hl
                   | (simpl in Htr; monadInv Htr)
                   | (simpl in Htr; discriminate) ]).
      destruct xs as [|x [|]];
        [simpl in Htr; discriminate | | simpl in Htr; discriminate].
      eapply to_equation_entails_fby; eassumption.
    - (* Eapp *)
      destruct o as [er|].
      + destruct er;
          try solve [ (simpl in Htr; monadInv Htr)
                    | (simpl in Htr; discriminate) ].
        match goal with an : ann |- _ => destruct an as [ty [ckr nm]] end.
        eapply to_equation_entails_app_reset; eassumption.
      + eapply to_equation_entails_app; eassumption.
  Qed.

  (** * Equation lists

      Both generators fold with [++] in the same order, so the lift is an
      induction and [entails] composes. *)

  Theorem to_equations_entails :
    forall G env base_ty rst_ty cenv envo eqs neqs cs' st st',
      Errors.mmap (to_equation cenv envo) eqs = OK neqs ->
      generate_leqns_constraints G env base_ty rst_ty cenv eqs st
        = OK (cs', st') ->
      exists cs,
        generate_eqns_constraints G env base_ty rst_ty neqs st = OK (cs, st')
        /\ entails cs' cs.
  Proof.
    induction eqs as [|eq eqs IH]; intros neqs cs' st st' Htr Hl; simpl in Htr.
    - inv Htr. simpl in Hl. unfold ret in Hl. inv Hl.
      exists []. split; [reflexivity | apply entails_refl].
    - monadInv Htr. simpl in Hl.
      eapply sec_bind_inv in Hl as (c' & st1 & Hc' & Hl).
      eapply sec_bind_inv in Hl as (cr' & st2 & Hcr' & Hret).
      unfold ret in Hret. inv Hret.
      destruct (to_equation_entails _ _ _ _ _ _ _ _ _ _ _ EQ Hc')
        as (c & Hc & Hec).
      destruct (IH _ _ _ _ EQ1 Hcr') as (cr & Hcr & Hecr).
      exists (c ++ cr). split.
      + simpl. ssec Hc. ssec Hcr. reflexivity.
      + now apply entails_app.
  Qed.

  (** * Crossing [simplify]

      Both generators eliminate the same locals, so entailment of the raw
      lists becomes preservation of the stored ones.  Both halves already
      exist: [simplify_complete] recovers a valuation of the raw constraints
      from one of the simplified constraints, and [simplify_is_correct]
      pushes a raw valuation forward. *)

  Lemma simplify_correct : forall dlt cns ds,
      listSatisfiable dlt cns -> listSatisfiable dlt (simplify cns ds).
  Proof.
    intros dlt cns ds H.
    eapply simplify_is_correct; [exact H|].
    eapply simplify_simplifyRel. reflexivity.
  Qed.

  (** [wf_constraints] only looks at right-hand sides, so it transfers along
      the right-hand-side equality [entails] records. *)
  Lemma wf_constraints_of_rhs : forall cs' cs,
      map snd cs' = map snd cs -> wf_constraints cs -> wf_constraints cs'.
  Proof.
    intros cs' cs Hr [Hnd Hlen]. split.
    - rewrite Hr. exact Hnd.
    - rewrite Forall_forall in Hlen |- *.
      intros c Hin. destruct c as [lhs rhs].
      assert (Hrhs : In rhs (map snd cs'))
        by (apply in_map_iff; exists (lhs, rhs); split; auto).
      rewrite Hr in Hrhs.
      apply in_map_iff in Hrhs as ((l2, r2) & Hr2 & Hin2).
      simpl in Hr2. subst r2.
      specialize (Hlen _ Hin2). exact Hlen.
  Qed.

  Theorem entails_simplify : forall scope cs' cs ds,
      entails cs' cs ->
      wf_constraints cs ->
      (forall x, In x ds -> ~ In x scope) ->
      preserves_on scope (simplify cs' ds) (simplify cs ds).
  Proof.
    intros scope cs' cs ds He Hwf Hdisj dlt Hsat.
    assert (Hwf' : wf_constraints cs')
      by (eapply wf_constraints_of_rhs; [apply entails_rhs|]; eauto).
    edestruct simplify_complete as (dlt' & Hagree & Hsat'); eauto.
    exists dlt'. split.
    - intros x Hin. now apply Hagree.
    - apply simplify_correct. eapply entails_sat; eauto.
  Qed.

  Lemma l_node_sig_inv : forall G n env aux_names lsig st st',
      generate_lnode_sig G n env aux_names st = OK (lsig, st') ->
      exists clk_id rst_id clk_type rst_type inp out locals cns,
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
        /\ Env.find clk_id env = Some clk_type
        /\ Env.find rst_id env = Some rst_type
        /\ get_mappings_from_node n.(n_in) env = Some inp
        /\ get_mappings_from_node n.(n_out) env = Some out
        /\ get_mappings_from_node n.(n_vars) env = Some locals
        /\ generate_leqns_constraints G env clk_type rst_type
             (lnode_clock_env n) n.(n_eqs) st = OK (cns, st')
        /\ lsig = {| s_name  := n.(n_name);
                     s_in    := inp;
                     s_out   := out;
                     s_reset := rst_type;
                     s_clk   := clk_type;
                     s_constraints := simplify cns (locals ++ minted st st') |}.
  Proof.
    intros G n env aux_names lsig st st' H.
    unfold generate_lnode_sig in H.
    match type of H with
    | match ?X with _ => _ end = _ => destruct X as [[p stz]|er] eqn:E
    end; [|discriminate].
    eapply sec_bind2_inv in E as (clk_id & rst_id & st1 & Haux & E).
    eapply sec_bind_inv in E as (clk_type & st2 & Hclk & E).
    eapply sec_bind_inv in E as (rst_type & st3 & Hrst & E).
    eapply sec_bind_inv in E as (inp & st4 & Hinp & E).
    eapply sec_bind_inv in E as (out & st5 & Hout & E).
    eapply sec_bind_inv in E as (locals & st6 & Hloc & E).
    eapply sec_bind_inv in E as (cns & st7 & Hcns & Hret).
    unfold ret in Hret. inv Hret. inv H.
    sec_peel Haux. sec_peel Hclk. sec_peel Hrst.
    sec_peel Hinp. sec_peel Hout. sec_peel Hloc.
    exists clk_id, rst_id, clk_type, rst_type, inp, out, locals, cns.
    repeat split; auto.
  Qed.

  (** * The NLustre generator is state-pure

      It only ever looks names up, so its result does not depend on the
      fresh-name state it starts from and it does not advance it.  The Lustre
      generator does mint, at nested calls, so the node-level proof needs this
      to move an NLustre run from one start state to another -- and needs it
      to know that on a transcribed node nothing was minted. *)

  Ltac pure_step :=
    apply state_pure_bind;
    [ first [ apply state_pure_option_to_sec
            | apply state_pure_find_env
            | apply state_pure_generate_constraints
            | apply state_pure_ret
            | (apply state_pure_mmap; intros;
               first [ apply state_pure_option_to_sec
                     | apply state_pure_find_env ]) ]
    | intro ].

  Lemma state_pure_generate_eqn_constraint :
    forall G env base_ty rst_ty eq,
      state_pure (generate_eqn_constraint G env base_ty rst_ty eq).
  Proof.
    intros G env base_ty rst_ty eq.
    destruct eq; unfold generate_eqn_constraint;
      repeat match goal with
             | |- state_pure (match ?x with _ => _ end) => destruct x
             end;
      try apply state_pure_ret; try apply state_pure_error;
      repeat pure_step;
      first [ apply state_pure_generate_constraints | apply state_pure_ret ].
  Qed.

  Lemma state_pure_generate_eqns_constraints :
    forall G env base_ty rst_ty eqs,
      state_pure (generate_eqns_constraints G env base_ty rst_ty eqs).
  Proof.
    intros G env base_ty rst_ty eqs.
    induction eqs as [|eq eqs IH]; simpl.
    - apply state_pure_ret.
    - apply state_pure_bind; [apply state_pure_generate_eqn_constraint|intro].
      apply state_pure_bind; [exact IH|intro].
      apply state_pure_ret.
  Qed.

  (** On a transcribed node the Lustre generator mints nothing, because a
      normalized expression holds no nested call.  That shows up here as the
      run leaving the state where it found it. *)
  Lemma minted_refl : forall st, minted st st = [].
  Proof.
    intros st. unfold minted.
    assert (Hz : (Pos.to_nat st - Pos.to_nat st = 0)%nat) by lia.
    rewrite Hz. reflexivity.
  Qed.

  (** * Nodes

      Transcription keeps a node's name and its input, variable and output
      lists definitionally, and by [SecLNameInterface.to_global_lscoped_env]
      both sides read the same naming environment.  So every interface field
      of the two generated signatures is the same computation on the same
      data, and what is left to compare is the constraint list -- which is the
      equation-list theorem, plus the fact that nothing was minted. *)

  Lemma nl_node_sig_inv : forall G n env aux_names nsig,
      generate_node_sig G n env aux_names = OK nsig ->
      exists clk_id rst_id clk_type rst_type inp out locals cns,
        get_node_aux n.(NLSyn.n_name) aux_names = Some (clk_id, rst_id)
        /\ Env.find clk_id env = Some clk_type
        /\ Env.find rst_id env = Some rst_type
        /\ get_mappings_from_node n.(NLSyn.n_in) env = Some inp
        /\ get_mappings_from_node n.(NLSyn.n_out) env = Some out
        /\ get_mappings_from_node n.(NLSyn.n_vars) env = Some locals
        /\ (forall st, generate_eqns_constraints G env clk_type rst_type
                         n.(NLSyn.n_eqs) st = OK (cns, st))
        /\ nsig = {| s_name  := n.(NLSyn.n_name);
                     s_in    := inp;
                     s_out   := out;
                     s_reset := rst_type;
                     s_clk   := clk_type;
                     s_constraints := simplify cns locals |}.
  Proof.
    intros G n env aux_names nsig Hnl.
    unfold generate_node_sig in Hnl.
    match type of Hnl with
    | match ?X with _ => _ end = _ => destruct X as [[p stz]|er] eqn:E
    end; [|discriminate].
    eapply sec_bind2_inv in E as (clk_id & rst_id & st1 & Haux & E).
    eapply sec_bind_inv in E as (clk_type & st2 & Hclk & E).
    eapply sec_bind_inv in E as (rst_type & st3 & Hrst & E).
    eapply sec_bind_inv in E as (inp & st4 & Hinp & E).
    eapply sec_bind_inv in E as (out & st5 & Hout & E).
    eapply sec_bind_inv in E as (locals & st6 & Hloc & E).
    eapply sec_bind_inv in E as (cns & st7 & Hcns & Hret).
    unfold ret in Hret. inv Hret. inv Hnl.
    unfold option_to_sec in Haux, Hclk, Hrst, Hinp, Hout, Hloc.
    destruct (get_node_aux (NLSyn.n_name n) aux_names) as [[ci ri]|] eqn:A1;
      try discriminate.
    unfold ret in Haux. inv Haux.
    destruct (Env.find clk_id env) eqn:A2; try discriminate.
    unfold ret in Hclk. inv Hclk.
    destruct (Env.find rst_id env) eqn:A3; try discriminate.
    unfold ret in Hrst. inv Hrst.
    destruct (get_mappings_from_node (NLSyn.n_in n) env) eqn:A4; try discriminate.
    unfold ret in Hinp. inv Hinp.
    destruct (get_mappings_from_node (NLSyn.n_out n) env) eqn:A5; try discriminate.
    unfold ret in Hout. inv Hout.
    destruct (get_mappings_from_node (NLSyn.n_vars n) env) eqn:A6; try discriminate.
    unfold ret in Hloc. inv Hloc.
    exists clk_id, rst_id, clk_type, rst_type, inp, out, locals, cns.
    repeat split; auto.
    intros st.
    destruct (state_pure_generate_eqns_constraints G env clk_type rst_type
                (NLSyn.n_eqs n) _ st _ _ Hcns) as [_ Hst]. exact Hst.
  Qed.

  (** * Nodes

      Transcription keeps a node's name and its three variable lists
      definitionally, and both sides read one naming environment, so the
      interface fields are the same computation on the same data.  What is
      left is the constraint list, which is the equation-list theorem crossed
      through [simplify].

      The side condition is the Lustre analogue of what
      [SecNLusTypingCorrectness.v] proves for NLustre: the generated raw list
      is well formed, and a node's locals are fresh from its signature scope.
      It is a hypothesis here so the caller supplies it from that file. *)

  Theorem to_node_sig_preserved :
    forall G n n' Hp env aux_names nsig lsig st st',
      to_node n Hp = OK n' ->
      generate_node_sig G n' env aux_names = OK nsig ->
      generate_lnode_sig G n env aux_names st = OK (lsig, st') ->
      (forall clk_type rst_type locals cns,
          get_mappings_from_node n.(n_vars) env = Some locals ->
          generate_eqns_constraints G env clk_type rst_type
            n'.(NLSyn.n_eqs) st = OK (cns, st) ->
          wf_constraints cns
          /\ (forall x, In x locals -> ~ In x (signature_scope lsig))) ->
      SIGPROOFS.signatures_preserved lsig nsig.
  Proof.
    intros G n n' Hp env aux_names nsig lsig st st' Htr Hnl Hl Hside.
    pose proof Htr as Htr'. tonodeInv Htr'.
    eapply nl_node_sig_inv in Hnl
      as (ci & ri & ckt & rstt & inp & out & locs & cns
          & Haux & Hclk & Hrst & Hinp & Hout & Hloc & Hcns & Hnsig).
    eapply l_node_sig_inv in Hl
      as (ci2 & ri2 & ckt2 & rstt2 & inp2 & out2 & locs2 & cns2
          & Haux2 & Hclk2 & Hrst2 & Hinp2 & Hout2 & Hloc2 & Hcns2 & Hlsig).
    simpl in Haux, Hinp, Hout, Hloc, Hcns, Hnsig.
    specialize (Hcns st).
    destruct (Hside ckt rstt locs cns Hloc Hcns) as [Hwf Hfresh].
    rewrite Haux in Haux2. inv Haux2.
    rewrite Hclk in Hclk2. inv Hclk2.
    rewrite Hrst in Hrst2. inv Hrst2.
    rewrite Hinp in Hinp2. inv Hinp2.
    rewrite Hout in Hout2. inv Hout2.
    rewrite Hloc in Hloc2. inv Hloc2.
    destruct (to_equations_entails _ _ _ _ _ _ _ _ _ _ _ Hmmap Hcns2)
      as (cs & Hcs & Hent).
    rewrite Hcns in Hcs. inv Hcs.
    subst. unfold SIGPROOFS.signatures_preserved. split.
    - repeat split; reflexivity.
    - simpl. rewrite minted_refl, app_nil_r.
      apply entails_simplify; auto.
  Qed.

End SECLUSNLUSTRANSLATION.
