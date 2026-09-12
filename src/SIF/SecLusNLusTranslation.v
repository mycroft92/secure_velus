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
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
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
  (Import SIG     : SIGNATURE  Ids SC)
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

  (** A monad law the call case needs: it binds the instantiated block only to
      merge an empty set of carried obligations into it. *)
  Lemma bind_ret_id : forall {A : Type} (m : Sec A) st,
      (do a <- m; ret a) st = m st.
  Proof.
    intros A m st. unfold bind, ret.
    destruct (m st) as [[a st']|e]; reflexivity.
  Qed.

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
      (simpl in H; monadInv H; do 2 eexists;
       repeat split; try eassumption;
       first [ eassumption
             | simpl;
               repeat match goal with
                      | Hl : to_lexp _ = OK _ |- _ => rewrite Hl
                      end;
               reflexivity
             | reflexivity ]).
  Qed.

  Lemma to_equation_fby_inv : forall cenv envo x e0 e an eq',
      to_equation cenv envo ([x], [Efby [e0] [e] [an]]) = OK eq' ->
      exists ck c0 le,
        find_clock cenv x = OK ck
        /\ to_constant e0 = OK c0
        /\ to_lexp e = OK le
        /\ eq' = NLSyn.EqFby x ck c0 le.
  Proof.
    intros cenv envo x e0 e an eq' H.
    simpl in H. monadInv H.
    do 3 eexists. repeat split; eassumption.
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

  Theorem to_equation_constraint_eq_fby :
    forall G env base_ty rst_ty cenv envo x e0 e an eq' cs st st',
      to_equation cenv envo ([x], [Efby [e0] [e] [an]]) = OK eq' ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv ([x], [Efby [e0] [e] [an]]) st
        = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo x e0 e an eq' cs st st' Htr Hnl.
    edestruct to_equation_fby_inv as (ck & c0 & le & Hck & Hc0 & Hle & Heq); eauto.
    subst eq'.
    eapply nl_EqFby_inv in Hnl
      as (cky & sy & by0 & Hcky & Hsy & Hby & Hcs & Hst).
    subst cs st'.
    rewrite gen_leqn_Efby.
    eapply generate_ldef_constraint_eq; try eassumption.
    eapply to_lexp_assign_eq; eassumption.
  Qed.

  (** * What remains: the equation level and above

      The expression-level halves of this leg are proved, in [SecLTyping.v]:
      [to_lexp_assign_eq], [to_cexp_assign_eq] and [to_lexps_assign_eq]. The
      generators have been aligned case for case with [to_equation] -- bind
      order, the monadic output lookup, the join association in merge and ite,
      and the empty-result call case -- so that the remaining steps are
      computations rather than reconciliations.

      The statement to prove is

<<
      Theorem to_equation_constraint_eq :
        forall G env base_ty rst_ty cenv envo eq eq' cs st st',
          to_equation cenv envo eq = OK eq' ->
          generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
          generate_leqn_constraint G env base_ty rst_ty cenv eq st = OK (cs, st').
>>

      running NLustre-to-Lustre, *not* as an equality of the two [Sec]
      computations. Equality is false where generation fails: the two
      generators report different messages, so they agree only on success.
      And this is the direction that is both provable from the expression
      lemmas and sufficient:
      [SecNLusTypingTotality.source_signature_generation_total] says the
      NLustre generator succeeds on any ordered, well-clocked program, and
      transcription supplies both (`TrOrdered.ord_l_nl`,
      `TrClocking.wc_transcription`). So on a program that transcribes the
      NLustre side always succeeds, this theorem hands the Lustre side the
      same constraints, and the two sets are then equal -- which is what
      preservation needs in either direction.

      The proof splits into the four shapes of [to_equation]. The seven forms
      that transcribe to [EqDef] share one script, [Efby] is that script with
      [to_lexp_assign_eq] in place of [to_cexp_assign_eq], and the two call
      shapes use [to_lexps_assign_eq] with [carried_plain], [map_fst_plain]
      and [bind_ret_id].

      One practical warning for whoever writes it. A blanket [simpl] cannot be
      used: it unfolds [SymTypes.merge] into its raw inner [fix] on one side
      of the goal only, after which [reflexivity] cannot close a goal whose
      two sides are otherwise identical. Reduce with [cbn [fst snd]] and the
      per-constant unfolding lemmas instead -- the same discipline
      [norm_cs_cons] and the [assign_lexp_*] equations already impose. *)

End SECLUSNLUSTRANSLATION.
