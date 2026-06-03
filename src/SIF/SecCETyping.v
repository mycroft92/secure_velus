(** Symbolic security typing judgments for CoreExpr clocks and expressions. *)

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.

From Coq Require Import PArith.
From Velus Require Import SymTypes.
From Velus Require Import SIF.SecTypes.
From Coq Require Import List.
Import ListNotations.

Module Type SECCETYPING
    (Import Ids   : IDS)
    (Import Op    : OPERATORS)
    (Import CESyn : CESYNTAX Op)
    (Import CEIsF : CEISFREE Ids Op CESyn)
    (Import CEClo : CECLOCKING Ids Op CESyn).

  Open Scope option_monad_scope.

  Section SecClkTypingCE.
    Variable ctxt: Env.t ident.
    Variable base_ty: ident.
    Inductive wst_clock : clock -> ST -> Prop :=
      | wst_Base:

        wst_clock Cbase [base_ty]
      | wst_On: forall ck x b ckty xty,
        wst_clock ck ckty ->
        Env.find x ctxt = Some xty ->
        wst_clock (Con ck x b) (ckty ⊔ [xty]).
    Hint Constructors wst_clock.

    Fixpoint assign_clk_type (c: clock): option ST :=
      match c with
      | Cbase       => Some [base_ty]

      | Con ck' x _ =>
          do ckty <- assign_clk_type ck';
          do xty  <- Env.find x ctxt;
          Some (ckty ⊔ [xty])
      end.

    Theorem assign_clk_correct:
      forall ck st, wst_clock ck st -> assign_clk_type ck = Some st.
    Proof.
      induction ck; intros.
      - simpl.  inversion H. now subst.

      - unfold assign_clk_type. fold assign_clk_type.
        inversion H as [| ?????? H_find]. subst.
        assert (assign_clk_type ck = Some ckty) as H'. { now apply IHck. }
        rewrite H',H_find. reflexivity.
    Qed.

    Lemma assign_clk_inv:
      forall ck i b st,  assign_clk_type (Con ck i b) = Some st ->
       exists st' ty, st = st' ⊔ [ty] /\ assign_clk_type ck = Some st' /\ Env.find i ctxt = Some ty.
    Proof.
      intros. simpl in *. destruct (assign_clk_type ck) eqn:E1.
        - exists s. destruct (Env.find i ctxt) eqn: E2.
          + exists i0. simpl in H. now inversion H.
          + simpl in H. discriminate H.
        - simpl in H. discriminate H.
    Qed.

    Theorem assign_clk_correct2:
      forall ck st, assign_clk_type ck = Some st -> wst_clock ck st.
    Proof.
      induction ck; intros.
      - simpl in *. inversion H.  now constructor.

      - apply assign_clk_inv in H as [st' [ty [Hst [Hck Hfind]] ]].
        apply IHck in Hck. rewrite -> Hst. now apply wst_On.
    Qed.
  End SecClkTypingCE.

  Section SecExpTypingCE.
    Variable ctxt: Env.t ident.
    Inductive wst_exp : exp -> ST -> Prop :=
      | wst_Econst : forall c,
          wst_exp (Econst c) []
      | wst_Evar   : forall x t ty,
          Env.find x ctxt = Some ty ->
          wst_exp (Evar x t) [ty]
      | wst_Ewhen  : forall e x b xty ety,
          Env.find x ctxt = Some xty ->
          wst_exp e ety ->
          wst_exp (Ewhen e x b) (ety ⊔ [xty])
      | wst_Eunop  : forall o e ety t,
          wst_exp e ety ->
          wst_exp (Eunop o e t) ety
      | wst_Ebinop : forall b e1 e2 e1ty e2ty t,
          wst_exp e1 e1ty ->
          wst_exp e2 e2ty ->
          wst_exp (Ebinop b e1 e2 t) (e1ty ⊔ e2ty).

    Fixpoint assign_exp_type (e: exp) : option ST :=
      match e with
      | Econst const   => Some []
      | Evar x _       => do xty <- Env.find x ctxt; Some [xty]
      | Ewhen exp x _  =>
          do ety <- assign_exp_type exp;
          do xty <- Env.find x ctxt;
          Some (ety ⊔ [xty])
      | Eunop _ e' _     => assign_exp_type e'
      | Ebinop _ e1 e2 _ =>
          do e1ty <- assign_exp_type e1;
          do e2ty <- assign_exp_type e2;
          Some (e1ty ⊔ e2ty)
      end.

    Fixpoint assign_cexp_type (ce: cexp) : option ST :=
      match ce with
      | Emerge x ce1 ce2 =>
          do xty  <- Env.find x ctxt;
          do c1ty <- assign_cexp_type ce1;
          do c2ty <- assign_cexp_type ce2;
          Some ([xty] ⊔ c1ty ⊔ c2ty)
      | Eite e cet cef  =>
          do ety  <- assign_exp_type e;
          do c1ty <- assign_cexp_type cet;
          do c2ty <- assign_cexp_type cef;
          Some (ety ⊔ c1ty ⊔ c2ty)
      |  Eexp e    => assign_exp_type e
      end.

  End SecExpTypingCE.

  Section SecTypingFreeVars.

    Lemma wc_clock_free_in_vars:
      forall vars x ck,
        wc_clock vars ck ->
        Is_free_in_clock x ck ->
        InMembers x vars.
    Proof.
      intros vars x ck Hwc Hfree.
      induction Hwc.
      - inversion Hfree.
      - inversion Hfree; subst; eauto using In_InMembers.
    Qed.

    Lemma wc_exp_free_in_vars:
      forall vars x e ck,
        wc_exp vars e ck ->
        Is_free_in_exp x e ->
        InMembers x vars.
    Proof.
      intros vars x e ck Hwc.
      induction Hwc; intro Hfree.
      - inversion Hfree.
      - inversion Hfree; subst; eauto using In_InMembers.
      - inversion Hfree; subst; eauto using In_InMembers.
      - inversion Hfree; subst; eauto.
      - inversion Hfree; subst.
        match goal with
        | H : _ \/ _ |- _ => destruct H as [Hfree1|Hfree2]; eauto
        end.
    Qed.

    Lemma wc_cexp_free_in_vars:
      forall vars x ce ck,
        wc_cexp vars ce ck ->
        Is_free_in_cexp x ce ->
        InMembers x vars.
    Proof.
      intros vars x ce ck Hwc.
      induction Hwc; intro Hfree.
      - inversion Hfree; subst; eauto using In_InMembers.
      - inversion Hfree; subst; eauto using wc_exp_free_in_vars.
      - inversion Hfree; subst; eauto using wc_exp_free_in_vars.
    Qed.

  End SecTypingFreeVars.

  Section SecTypingScoped.
    Variable ctxt: Env.t ident.
    Variable base_ty: ident.

    Lemma assign_clk_type_scoped:
      forall scope ck st,
        In base_ty scope ->
        (forall x, Is_free_in_clock x ck -> exists ty, Env.find x ctxt = Some ty /\ In ty scope) ->
        assign_clk_type ctxt base_ty ck = Some st ->
        st_scoped scope st.
    Proof.
      intros scope ck.
      induction ck as [|ck IH x b]; intros st Hbase Hfree Hassign.
      - simpl in Hassign. inversion Hassign; subst.
        apply st_scoped_singleton. exact Hbase.
      - simpl in Hassign.
        destruct (assign_clk_type ctxt base_ty ck) as [ckty|] eqn:Hck; try discriminate.
        destruct (Env.find x ctxt) as [xty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst st.
        apply st_scoped_merge.
        + eapply IH.
          1: exact Hbase.
          intros y Hy.
          apply Hfree. now apply FreeCon2.
          reflexivity.
        + apply st_scoped_singleton.
          destruct (Hfree x) as (? & Hfind' & Hin); [apply FreeCon1|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
    Qed.

    Lemma assign_exp_type_scoped:
      forall scope e st,
        (forall x, Is_free_in_exp x e -> exists ty, Env.find x ctxt = Some ty /\ In ty scope) ->
        assign_exp_type ctxt e = Some st ->
        st_scoped scope st.
    Proof.
      induction e; intros st Hfree Hassign.
      - simpl in Hassign. inversion Hassign; subst. intros x Hin. inversion Hin.
      - simpl in Hassign.
        destruct (Env.find i ctxt) as [xty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst.
        apply st_scoped_singleton.
        destruct (Hfree i) as (? & Hfind' & Hin); [constructor|].
        rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
      - simpl in Hassign.
        destruct (assign_exp_type ctxt e) as [ety|] eqn:He; try discriminate.
        destruct (Env.find i ctxt) as [xty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst.
        apply st_scoped_merge.
        + eapply IHe.
          * intros x Hx. apply Hfree. now apply FreeEwhen1.
          * reflexivity.
        + apply st_scoped_singleton.
          destruct (Hfree i) as (? & Hfind' & Hin); [apply FreeEwhen2|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
      - simpl in Hassign. eauto.
      - simpl in Hassign.
        destruct (assign_exp_type ctxt e1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_exp_type ctxt e2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        apply st_scoped_merge.
        + eapply IHe1.
          * intros x Hx. apply Hfree. now apply FreeEbinop; left.
          * reflexivity.
        + eapply IHe2.
          * intros x Hx. apply Hfree. now apply FreeEbinop; right.
          * reflexivity.
    Qed.

    Lemma assign_cexp_type_scoped:
      forall scope ce st,
        (forall x, Is_free_in_cexp x ce -> exists ty, Env.find x ctxt = Some ty /\ In ty scope) ->
        assign_cexp_type ctxt ce = Some st ->
        st_scoped scope st.
    Proof.
      induction ce; intros st Hfree Hassign.
      - simpl in Hassign.
        destruct (Env.find i ctxt) as [xty|] eqn:Hfind; try discriminate.
        destruct (assign_cexp_type ctxt ce1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_cexp_type ctxt ce2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        change (st_scoped scope ((([xty] ⊔ sty1) ⊔ sty2))).
        apply st_scoped_merge.
        + change (st_scoped scope ([xty] ⊔ sty1)).
          apply st_scoped_merge.
          * apply st_scoped_singleton.
            destruct (Hfree i) as (? & Hfind' & Hin); [apply FreeEmerge_cond|].
            rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
          * eapply IHce1.
            -- intros x Hx. apply Hfree. now apply FreeEmerge_true.
            -- reflexivity.
        + eapply IHce2.
          * intros x Hx. apply Hfree. now apply FreeEmerge_false.
          * reflexivity.
      - simpl in Hassign.
        destruct (assign_exp_type ctxt e) as [ety|] eqn:He; try discriminate.
        destruct (assign_cexp_type ctxt ce1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_cexp_type ctxt ce2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        change (st_scoped scope (((ety ⊔ sty1) ⊔ sty2))).
        apply st_scoped_merge.
        + change (st_scoped scope (ety ⊔ sty1)).
          apply st_scoped_merge.
          * eapply assign_exp_type_scoped.
            -- intros x Hx.
               apply Hfree.
               apply FreeEite_cond.
               exact Hx.
            -- exact He.
          * eapply IHce1.
            -- intros x Hx.
               apply Hfree.
               apply FreeEite_true.
               exact Hx.
            -- reflexivity.
        + eapply IHce2.
          * intros x Hx.
             apply Hfree.
             apply FreeEite_false.
             exact Hx.
          * reflexivity.
      - simpl in Hassign.
        eapply assign_exp_type_scoped.
        + intros x Hx.
          apply Hfree.
          apply FreeEexp.
          exact Hx.
        + exact Hassign.
    Qed.

  End SecTypingScoped.

End SECCETYPING.
