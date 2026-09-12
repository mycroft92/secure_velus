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
From Velus Require Import SIF.SymTypes.
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
  (Import STEP    : SECMONADSTEP Ids SC)
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
    forall G env base_ty rst_ty cenv envo x e0 e ans eq' cs st st',
      to_equation cenv envo ([x], [Efby [e0] [e] ans]) = OK eq' ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv ([x], [Efby [e0] [e] ans]) st
        = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo x e0 e ans eq' cs st st' Htr Hnl.
    edestruct to_equation_fby_inv as (ck & c0 & le & Hck & Hc0 & Hle & Heq); eauto.
    subst eq'.
    eapply nl_EqFby_inv in Hnl
      as (cky & sy & by0 & Hcky & Hsy & Hby & Hcs & Hst).
    subst cs st'.
    rewrite gen_leqn_Efby.
    eapply generate_ldef_constraint_eq; try eassumption.
    eapply to_lexp_assign_eq; eassumption.
  Qed.

  (** * The call shapes

      Both NLustre call cases special-case an empty result list, and their
      match is flat, so a proof has to split [xs] before either side will
      reduce.  On the empty list both generators return the empty constraint
      list. *)

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

      The dispatcher.  Every equation that transcribes is one of the four
      shapes above; the rest is case analysis. *)

  Ltac def_shape Htr Hnl :=
    eapply to_equation_constraint_eq_def;
    [ exact Htr | intros; discriminate | intros; discriminate | exact Hnl ].

  Theorem to_equation_constraint_eq :
    forall G env base_ty rst_ty cenv envo eq eq' cs st st',
      to_equation cenv envo eq = OK eq' ->
      generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
      generate_leqn_constraint G env base_ty rst_ty cenv eq st = OK (cs, st').
  Proof.
    intros G env base_ty rst_ty cenv envo [xs es] eq' cs st st' Htr Hnl.
    destruct es as [|e [|e' es']];
      [simpl in Htr; discriminate | | simpl in Htr; discriminate].
    destruct e.
    (* the seven shapes that transcribe to EqDef *)
    1-4,6-9: (destruct xs as [|x [|]];
              [simpl in Htr; discriminate | | simpl in Htr; discriminate];
              def_shape Htr Hnl).
    - (* Efby: only the singleton form is a delay; the rest reach EqDef and
         are rejected there by to_cexp *)
      destruct l as [|e0 [|e0' l']]; destruct l0 as [|e1 [|e1' l0']];
        try (destruct xs as [|x [|]];
             [simpl in Htr; discriminate | | simpl in Htr; discriminate];
             solve [ def_shape Htr Hnl
                   | (simpl in Htr; monadInv Htr)
                   | (simpl in Htr; discriminate) ]).
      destruct xs as [|x [|]];
        [simpl in Htr; discriminate | | simpl in Htr; discriminate].
      eapply to_equation_constraint_eq_fby; eassumption.
    - (* Eapp, with and without a reset *)
      destruct o as [er|].
        destruct er;
          try solve [ (simpl in Htr; monadInv Htr)
                    | (simpl in Htr; discriminate) ].
        match goal with an : ann |- _ => destruct an as [ty [ckr nm]] end.
        eapply to_equation_constraint_eq_app_reset; eassumption.
      + eapply to_equation_constraint_eq_app; eassumption.
  Qed.

  (** * Equation lists

      Both generators fold over the list with [++] in the same order, so the
      lift is a plain induction. *)

  Theorem to_equations_constraints_eq :
    forall G env base_ty rst_ty cenv envo eqs neqs cs st st',
      Errors.mmap (to_equation cenv envo) eqs = OK neqs ->
      generate_eqns_constraints G env base_ty rst_ty neqs st = OK (cs, st') ->
      generate_leqns_constraints G env base_ty rst_ty cenv eqs st = OK (cs, st').
  Proof.
    induction eqs as [|eq eqs IH]; intros neqs cs st st' Htr Hnl; simpl in Htr.
    - inv Htr. simpl in Hnl. unfold ret in Hnl. inv Hnl. reflexivity.
    - monadInv Htr. simpl in Hnl.
      eapply sec_bind_inv in Hnl as (c & st1 & Hc & Hnl).
      eapply sec_bind_inv in Hnl as (cr & st2 & Hcr & Hret).
      unfold ret in Hret. inv Hret.
      simpl.
      erewrite bind_OK by (eapply to_equation_constraint_eq; eassumption).
      erewrite bind_OK by (eapply IH; eassumption).
      reflexivity.
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

  Theorem to_node_sig_eq :
    forall G n n' Hp env aux_names nsig st,
      to_node n Hp = OK n' ->
      generate_node_sig G n' env aux_names = OK nsig ->
      generate_lnode_sig G n env aux_names st = OK (nsig, st).
  Proof.
    intros G n n' Hp env aux_names nsig st Htr Hnl.
    (* invert the translation first: the NLustre node then *is* the record
       built from n's own name and variable lists, so the interface fields of
       the two generated signatures are literally the same computations *)
    pose proof Htr as Htr'. tonodeInv Htr'.
    eapply nl_node_sig_inv in Hnl
      as (ci & ri & ckt & rstt & inp & out & locals & cns
          & Haux & Hclk & Hrst & Hinp & Hout & Hloc & Hcns & Hsig).
    simpl in Haux, Hinp, Hout, Hloc, Hcns, Hsig.
    unfold generate_lnode_sig.
    erewrite bind2_OK by (unfold option_to_sec; rewrite Haux; reflexivity).
    erewrite bind_OK by (unfold option_to_sec; rewrite Hclk; reflexivity).
    erewrite bind_OK by (unfold option_to_sec; rewrite Hrst; reflexivity).
    erewrite bind_OK by (unfold option_to_sec; rewrite Hinp; reflexivity).
    erewrite bind_OK by (unfold option_to_sec; rewrite Hout; reflexivity).
    erewrite bind_OK by (unfold option_to_sec; rewrite Hloc; reflexivity).
    erewrite bind_OK by (eapply to_equations_constraints_eq;
                         [ exact Hmmap | apply Hcns ]).
    unfold ret. rewrite minted_refl, app_nil_r.
    now rewrite Hsig.
  Qed.

  Theorem to_node_sig_scoped_env_eq :
    forall G n n' Hp envs aux_names nsig st,
      to_node n Hp = OK n' ->
      generate_node_sig_scoped_env G n' envs aux_names = OK nsig ->
      generate_lnode_sig_scoped_env G n envs aux_names st = OK (nsig, st).
  Proof.
    intros G n n' Hp envs aux_names nsig st Htr Hnl.
    assert (Hname := to_node_name _ _ _ Htr).
    unfold generate_node_sig_scoped_env in Hnl.
    unfold generate_lnode_sig_scoped_env.
    rewrite Hname.
    destruct (find_node_env (NLSyn.n_name n') envs) as [envn|]; [|discriminate].
    eapply to_node_sig_eq; eassumption.
  Qed.

  (** * Programs

      One induction.  Both drivers thread the same accumulator, which is also
      the signature global the node generator reads its callees from, so the
      two stay in step at every prefix. *)

  Theorem to_global_signatures_eq :
    forall LG P Hp acc envs aux_names sigs st,
      to_global LG Hp = OK P ->
      generate_all_signatures_scoped_env' acc P envs aux_names = OK sigs ->
      generate_all_lsignatures' acc LG envs aux_names st = OK (sigs, st).
  Proof.
    induction LG as [|n LG IH]; intros P Hp acc envs aux_names sigs st Htr Hnl.
    - simpl in Htr. inv Htr. simpl in Hnl. inv Hnl. reflexivity.
    - simpl in Htr. monadInv Htr. simpl in Hnl. monadInv Hnl.
      simpl.
      erewrite to_node_sig_scoped_env_eq by eassumption.
      eapply IH; eassumption.
  Qed.

  Corollary to_global_all_signatures_eq :
    forall LG P Hp envs aux_names sigs st,
      to_global LG Hp = OK P ->
      generate_all_signatures_scoped_env P envs aux_names = OK sigs ->
      generate_all_lsignatures_scoped_env LG envs aux_names st = OK sigs.
  Proof.
    intros LG P Hp envs aux_names sigs st Htr Hnl.
    unfold generate_all_signatures_scoped_env in Hnl.
    unfold generate_all_lsignatures_scoped_env.
    erewrite to_global_signatures_eq by eassumption.
    reflexivity.
  Qed.

  (** * Summary

      [to_global_all_signatures_eq] is what this leg exists to prove: on a
      program that transcribes, the Lustre generator produces *the same*
      signature global as the NLustre generator, not merely one whose
      constraints preserve satisfiability.

      Three things make the equality available rather than the [preserves_on]
      the NLustre-to-Stc leg has to settle for.  Transcription introduces no
      variables and keeps a node's name and its input, variable and output
      lists definitionally.  The naming pass runs once, so both sides read the
      same environment ([SecLNameInterface.to_global_lscoped_env] shows a
      Lustre-side allocator would agree with it).  And a normalized expression
      holds no nested call, so the Lustre generator mints nothing here -- which
      is why [minted] contributes nothing to [simplify] and the two signatures
      have identical constraint lists, not merely equivalent ones.

      The statements run NLustre-to-Lustre.  Equality of the two [Sec]
      computations is false where generation fails, since the generators
      report different messages, and this direction is what the expression
      lemmas give.  It loses nothing:
      [SecNLusTypingTotality.source_signature_generation_total] says the
      NLustre generator succeeds on any ordered, well-clocked program, and
      transcription supplies both ([TrOrdered.ord_l_nl],
      [TrClocking.wc_transcription]).  So the NLustre side always succeeds,
      these theorems hand the Lustre side the same result, and the two are
      then equal -- usable in either direction. *)

End SECLUSNLUSTRANSLATION.
