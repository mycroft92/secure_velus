(** Correctness facts for generated Obc class signatures.

    First slice: satisfaction-equivalence of [collapse] (joining the
    sources of constraints that share a target neither gains nor loses
    satisfying valuations), and the one-target-per-constraint shape of
    the statement-level generator. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecObcTyping.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From compcert Require Import common.Errors.

Module Type SECOBCTYPINGCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG).

  (** * Collapse is satisfaction-neutral *)

  Lemma constraint_satisfiable_merge_split:
    forall dlt a b r,
      SecT.constraintSatisfiable dlt ((a ⊔ b), r) <->
      (SecT.constraintSatisfiable dlt (a, r) /\ SecT.constraintSatisfiable dlt (b, r)).
  Proof.
    intros dlt a b r.
    unfold SecT.constraintSatisfiable, SecT.satisfiable.
    split.
    - intros Hm.
      split.
      + eapply order_trans; [apply SecT.hm_ext_concat_l|exact Hm].
      + eapply order_trans; [apply SecT.hm_ext_concat_r|exact Hm].
    - intros [Ha Hb].
      eapply order_trans; [apply SecT.hm_ext_distributive2|].
      apply join_least_upper_bound; assumption.
  Qed.

  Lemma join_into_satisfaction:
    forall dlt l r acc,
      SecT.listSatisfiable dlt (join_into l r acc) <->
      (SecT.constraintSatisfiable dlt (l, r) /\ SecT.listSatisfiable dlt acc).
  Proof.
    intros dlt l r acc.
    induction acc as [|[l' r'] acc IH]; simpl.
    - split.
      + intros Hs. inversion Hs as [|? ? Hc Hcs]; subst.
        split; [exact Hc|constructor].
      + intros [Hc _]. constructor; [exact Hc|constructor].
    - destruct (st_eq_dec r r') as [Heq|Hneq].
      + subst r'.
        split.
        * intros Hs. inversion Hs as [|? ? Hc Hcs]; subst.
          apply constraint_satisfiable_merge_split in Hc.
          destruct Hc as [Hcl Hcl'].
          split; [exact Hcl|constructor; [exact Hcl'|exact Hcs]].
        * intros [Hc Hs]. inversion Hs as [|? ? Hc' Hcs]; subst.
          constructor; [|exact Hcs].
          apply constraint_satisfiable_merge_split.
          split; assumption.
      + split.
        * intros Hs. inversion Hs as [|? ? Hc' Hcs]; subst.
          apply IH in Hcs. destruct Hcs as [Hc Hacc].
          split; [exact Hc|constructor; [exact Hc'|exact Hacc]].
        * intros [Hc Hs]. inversion Hs as [|? ? Hc' Hacc]; subst.
          constructor; [exact Hc'|].
          apply IH. split; assumption.
  Qed.

  Theorem collapse_satisfaction:
    forall dlt cns,
      SecT.listSatisfiable dlt (collapse cns) <-> SecT.listSatisfiable dlt cns.
  Proof.
    intros dlt cns.
    induction cns as [|[l r] cns IH]; simpl.
    - tauto.
    - rewrite join_into_satisfaction. rewrite IH.
      split.
      + intros [Hc Hs]. constructor; assumption.
      + intros Hs. inversion Hs as [|? ? Hc Hcs]; subst.
        split; assumption.
  Qed.

  (** * Shape of generated constraints: every target list is a singleton *)

  Lemma generate_constraints_rhs_singleton:
    forall sig inp clk rst out cns st st',
      SIG.generate_constraints sig inp clk rst out st = OK (cns, st') ->
      Forall (fun c => length (snd c) = 1%nat) cns.
  Proof.
    intros sig inp clk rst out.
    unfold SIG.generate_constraints.
    intros cns st st' Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & _ & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & _ & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & _ & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & _ & Hgen).
    clear c1 c2 c3 st1 st2 st3.
    revert cns st4 st' Hgen.
    induction out as [|x out IH]; intros cns st4 st' Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst. constructor.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c & st5 & Hhd & Hgen).
      eapply sec_bind_inv in Hgen as (cs & st6 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      eapply sec_bind_inv in Hhd as (sty & st7 & _ & Hhd).
      unfold ret in Hhd. inversion Hhd; subst c st5.
      constructor.
      + simpl. reflexivity.
      + eapply IH; eauto.
  Qed.

  Lemma generate_stmt_constraints_rhs_singleton:
    forall G env state_env s pc cns st st',
      generate_stmt_constraints G env state_env pc s st = OK (cns, st') ->
      Forall (fun c => length (snd c) = 1%nat) cns.
  Proof.
    intros G env state_env s.
    induction s as [x e|x e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o m es|];
      intros pc cns st st' Hgen.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st2 & _ & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      constructor; [simpl; reflexivity|constructor].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st2 & _ & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      constructor; [simpl; reflexivity|constructor].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
      eapply sec_bind_inv in Hgen as (c1 & st2 & Hgen1 & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st3 & Hgen2 & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      apply Forall_app. split; [eapply IH1; eauto|eapply IH2; eauto].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      apply Forall_app. split; [eapply IH1; eauto|eapply IH2; eauto].
    - destruct ys as [|y ys'].
      + simpl in Hgen.
        destruct (ident_eqb m Ids.reset) eqn:Hreset.
        * eapply sec_bind_inv in Hgen as (sty & st1 & _ & Hret).
          unfold ret in Hret. inversion Hret; subst cns st'.
          constructor; [simpl; reflexivity|constructor].
        * unfold ret in Hgen. inversion Hgen; subst. constructor.
      + simpl in Hgen.
        destruct (ident_eqb m Ids.step) eqn:Hstep; try discriminate.
        destruct (SIG.find_signature cls G) as [sig|] eqn:Hfindsig; try discriminate.
        eapply sec_bind_inv in Hgen as (inptyp & st1 & _ & Hgen).
        eapply sec_bind_inv in Hgen as (outtyp & st2 & _ & Hgen).
        eapply sec_bind_inv in Hgen as (sty & st3 & _ & Hgen).
        eapply generate_constraints_rhs_singleton; eauto.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst. constructor.
  Qed.

  Corollary generate_stmt_constraints_collapse_wf:
    forall G env state_env s1 s2 pc1 pc2 c1 c2 st st1 st',
      generate_stmt_constraints G env state_env pc1 s1 st = OK (c1, st1) ->
      generate_stmt_constraints G env state_env pc2 s2 st1 = OK (c2, st') ->
      wf_constraints (collapse (c1 ++ c2)).
  Proof.
    intros G env state_env s1 s2 pc1 pc2 c1 c2 st st1 st' H1 H2.
    apply collapse_wf.
    apply Forall_app.
    split; eapply generate_stmt_constraints_rhs_singleton; eauto.
  Qed.

End SECOBCTYPINGCORRECTNESS.

Module SecObcTypingCorrectness
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG)
  <: SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc SemObc TypObc Lat SecT SIG SIGPROOFS SECOBCTYPING.

Include SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc SemObc TypObc Lat SecT SIG SIGPROOFS SECOBCTYPING.

End SecObcTypingCorrectness.
