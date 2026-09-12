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
