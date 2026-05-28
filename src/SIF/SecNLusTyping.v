(** Symbolic security typing and scoped signature generation for NLustre. *)

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import Clocks.

From Coq Require Import String.
From Coq Require Import Lia.
From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Ord   : NLORDERED Ids Op CESyn SynNL)
  (Import Mem   : MEMORIES Ids Op CESyn SynNL)
  (Import IsD   : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo   : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo).

  Import SECMONADNotations.

  Section SECEQNTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable base_ty: ident.
    Variable rst_ty : ident.

    Definition generate_eqn_constraint (e: equation): Sec (list constraint) :=
      match e with
      | EqDef x ck cexp  =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do xty   <- find_env x env;
          ret [((([rst_ty] ⊔ ckty) ⊔ expty), [xty])]
      | EqFby x  ck _ exp       =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [((([rst_ty] ⊔ ckty) ⊔ expty), [xty])]
      | EqApp [] _ _ _ _ => ret []
      | EqApp xs ck f exps None =>
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | EqApp xs ck f exps (Some (r,ckr)) =>
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do rty    <- find_env r env;
              do rstty  <- option_to_sec (assign_clk_type env rst_ty ckr);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty ([rty] ⊔ rstty) outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      end.

  Fixpoint generate_eqns_constraints (es: list equation) : Sec (list constraint) :=
    match es with
    | []     => ret []
    | e::es' =>
        do c  <- generate_eqn_constraint e;
        do cs <- generate_eqns_constraints es';
        ret (c++cs)
    end.

  Definition env_injective : Prop :=
    forall x y tx ty,
      Env.find x env = Some tx ->
      Env.find y env = Some ty ->
      tx = ty ->
      x = y.

  Definition vars_env_scoped {A: Type} (vars: list (ident * A)) (scope: list ident) : Prop :=
    forall x,
      InMembers x vars ->
      exists ty, Env.find x env = Some ty /\ In ty scope.

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

  Lemma assign_clk_type_scoped:
    forall base scope ck st,
      In base scope ->
      (forall x, Is_free_in_clock x ck -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
      assign_clk_type env base ck = Some st ->
      st_scoped scope st.
  Proof.
    intros base scope ck.
    induction ck as [|ck IH x b]; intros st Hbase Hfree Hassign.
    - simpl in Hassign. inversion Hassign; subst.
      apply st_scoped_singleton. exact Hbase.
    - simpl in Hassign.
      destruct (assign_clk_type env base ck) as [ckty|] eqn:Hck; try discriminate.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      inversion Hassign; subst st.
      apply st_scoped_merge.
      * eapply IH.
        1: exact Hbase.
        intros y Hy.
        apply Hfree. now apply FreeCon2.
        reflexivity.
      * apply st_scoped_singleton.
        destruct (Hfree x) as (? & Hfind' & Hin); [apply FreeCon1|].
        rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
  Qed.

  Lemma assign_exp_type_scoped:
    forall scope e st,
      (forall x, Is_free_in_exp x e -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
      assign_exp_type env e = Some st ->
      st_scoped scope st.
  Proof.
    induction e; intros st Hfree Hassign.
    - simpl in Hassign. inversion Hassign; subst. intros x Hin. inversion Hin.
    - simpl in Hassign.
      destruct (Env.find i env) as [xty|] eqn:Hfind; try discriminate.
      inversion Hassign; subst.
      apply st_scoped_singleton.
      destruct (Hfree i) as (? & Hfind' & Hin); [constructor|].
      rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
    - simpl in Hassign.
      destruct (assign_exp_type env e) as [ety|] eqn:He; try discriminate.
      destruct (Env.find i env) as [xty|] eqn:Hfind; try discriminate.
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
      destruct (assign_exp_type env e1) as [sty1|] eqn:He1; try discriminate.
      destruct (assign_exp_type env e2) as [sty2|] eqn:He2; try discriminate.
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
      (forall x, Is_free_in_cexp x ce -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
      assign_cexp_type env ce = Some st ->
      st_scoped scope st.
  Proof.
    induction ce; intros st Hfree Hassign.
    - simpl in Hassign.
      destruct (Env.find i env) as [xty|] eqn:Hfind; try discriminate.
      destruct (assign_cexp_type env ce1) as [sty1|] eqn:He1; try discriminate.
      destruct (assign_cexp_type env ce2) as [sty2|] eqn:He2; try discriminate.
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
      destruct (assign_exp_type env e) as [ety|] eqn:He; try discriminate.
      destruct (assign_cexp_type env ce1) as [sty1|] eqn:He1; try discriminate.
      destruct (assign_cexp_type env ce2) as [sty2|] eqn:He2; try discriminate.
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

  Lemma mmap_assign_exp_type_scoped:
    forall scope es tys st st',
      Forall
        (fun e =>
           forall x,
             Is_free_in_exp x e ->
             exists ty, Env.find x env = Some ty /\ In ty scope)
        es ->
      mmap (fun x => option_to_sec (assign_exp_type env x)) es st = OK (tys, st') ->
      Forall (st_scoped scope) tys.
  Proof.
    intros scope es.
    induction es as [|e es IH]; intros tys st st' Hfree Hmap.
    - simpl in Hmap. inversion Hmap; subst. constructor.
    - inversion Hfree as [|e0 es0 He Hes]; subst e0 es0.
      simpl in Hmap.
      eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
      unfold option_to_sec in Hhd.
      destruct (assign_exp_type env e) as [ety'|] eqn:Heq; try discriminate.
      inversion Hhd; subst ety st1.
      unfold ret in Hret. inversion Hret; subst tys st'.
      constructor.
      + eapply assign_exp_type_scoped; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma wc_call_clock_free_in_vars:
    forall P vars xs ck f les r x,
      wc_env vars ->
      wc_equation P vars (EqApp xs ck f les r) ->
      Is_free_in_clock x ck ->
      InMembers x vars.
  Proof.
    intros P vars xs ck f les r x Henv Hwc Hfree.
    inversion Hwc as [x' ck' ce' Hx Hce
                     |xs' ck' f' les' r' n sub Hfind Hins Houts Hr
                     |x' ck' v le Hx Hle]; subst.
    destruct n.(n_in) as [|[xin [tin xck]] ins] eqn:Hinps.
    { pose proof n.(n_ingt0) as Hgt0. rewrite Hinps in Hgt0. simpl in Hgt0. lia. }
    inversion Hins as [|? ? ? ? Hhead Htail]; subst.
    destruct Hhead as (_ & lck & Hexp & Hinst).
    assert (Hfree' : Is_free_in_clock x lck).
    { eapply instck_free_bck; eauto. }
    assert (Hwc_lck : wc_clock vars lck).
    { eapply wc_clock_exp; eauto. }
    eapply wc_clock_free_in_vars; eauto.
  Qed.

  Lemma wc_call_args_scoped:
    forall vars scope sub ck (ins : list (ident * (type * clock))) (es : list exp),
      vars_env_scoped vars scope ->
      Forall2
        (fun '(x, (_, xck)) le =>
           SameVar (sub x) le
           /\ exists lck, wc_exp vars le lck /\ instck ck sub xck = Some lck)
        ins es ->
      Forall
        (fun e =>
           forall x,
             Is_free_in_exp x e ->
             exists ty, Env.find x env = Some ty /\ In ty scope)
        es.
  Proof.
    intros vars scope sub ck ins es Hvars Hfor.
    induction Hfor as [|[x [xty xck]] le ins es [Hsame [lck [Hexp Hinst]]] Hfor IH].
    - constructor.
    - constructor.
      + intros z Hz.
        destruct (Hvars z) as (ty & Hfind & Hscope); eauto using wc_exp_free_in_vars.
      + exact IH.
  Qed.

  Lemma wc_call_outs_scoped:
    forall vars scope sub ck (outs : list (ident * (type * clock))) (xs : list ident),
      vars_env_scoped vars scope ->
      Forall2
        (fun '(y, (_, yck)) x =>
           sub y = Some x
           /\ exists xck, In (x, xck) vars /\ instck ck sub yck = Some xck)
        outs xs ->
      forall x,
        In x xs ->
        exists ty, Env.find x env = Some ty /\ In ty scope.
  Proof.
    intros vars scope sub ck outs xs Hvars Hfor x Hin.
    induction Hfor as [|[y [ty yck]] x0 outs xs [Hsub [xck [Hinx Hinst]]] Hfor IH].
    - inversion Hin.
    - simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst x0.
        destruct (Hvars x) as (ty' & Hfind & Hscope); eauto using In_InMembers.
      + eapply IH; eauto.
  Qed.

  Ltac secInv :=
    simpl in *;
    unfold error in *;
    match goal with
    | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
        discriminate
    | H: ret _ _ = _ |- _ =>
        unfold ret in H
    | H: bind ?x ?f ?st = OK (?res, ?st') |- _ =>
        eapply sec_bind_inv in H as [? [? [? ?]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
        eapply sec_bind2_inv in H as [? [? [? [? ?]]]]
    end; simpl in *.

  Lemma generate_eqn_constraint_scoped:
    forall P vars scope eq cns st st',
      secglobal_scoped G ->
      wc_env vars ->
      wc_equation P vars eq ->
      vars_env_scoped vars scope ->
      In base_ty scope ->
      In rst_ty scope ->
      generate_eqn_constraint eq st = OK (cns, st') ->
      constraints_scoped scope cns.
  Proof.
    intros P vars scope eq cns st st'
           Hscoped Henv Hwc Hvars Hbase Hrst Hgen.
    destruct eq as [x ck ce|xs ck f exps r|x ck c0 exp].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst. clear Hgen.
      unfold option_to_sec in Hck.
      destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck'; try discriminate.
      inversion Hck; subst.
      unfold option_to_sec in Hexp.
      destruct (assign_cexp_type env ce) as [expty'|] eqn:Hexp'; try discriminate.
      inversion Hexp; subst.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Hfind'; try discriminate.
      inversion Hfind; subst.
      inversion Hwc as [x' ck' ce' Hx Hce| |]; subst.
      assert (Hsc_rst : st_scoped scope [rst_ty]).
      { apply st_scoped_singleton. exact Hrst. }
      assert (Hsc_ck : st_scoped scope ckty).
      { eapply assign_clk_type_scoped with (base := base_ty) (ck := ck).
          - exact Hbase.
          - intros z Hz.
            assert (Hwc_ck : wc_clock vars ck) by (eapply wc_clock_cexp; eauto).
            pose proof (wc_clock_free_in_vars vars z ck Hwc_ck Hz) as Hmem.
            destruct (Hvars z) as (ty & Henv' & Hscope); [exact Hmem|].
            exists ty; split; assumption.
          - exact Hck'. }
      assert (Hsc_ce : st_scoped scope expty).
      { eapply assign_cexp_type_scoped with (ce := ce).
        - intros z Hz.
          destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_cexp_free_in_vars.
        - exact Hexp'. }
      assert (Hsc_lhs : st_scoped scope ((([rst_ty] ⊔ ckty) ⊔ expty))).
      { apply st_scoped_merge.
        - apply st_scoped_merge; assumption.
        - exact Hsc_ce. }
      constructor.
      + intros y Hin.
        unfold constraint_scope in Hin. simpl in Hin.
        rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        * exact (Hsc_lhs _ Hin).
        * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
          eapply SC.find_env_in_scope with (A := clock) (ann := ck) (st := st') (st' := st'); eauto.
          unfold find_env. rewrite Hfind'. reflexivity.
      + constructor.
    - inversion Hwc as [x' ck' ce' Hx Hce
                       |xs' ck' f' exps' r' n sub Hfindnode Hinputs Houtputs Hreset
                       |x' ck' v le Hx Hle]; subst.
      destruct xs as [|x0 xs0] eqn:Hxs.
      + simpl in Hgen. inversion Hgen; subst. constructor.
      + destruct r as [[rx rck]|].
        * simpl in Hgen.
          unfold find_signature in Hgen.
          destruct (List.find (fun n0 => ident_eqb n0.(s_name) f) G) as [sig|] eqn:Hfindsig; simpl in Hgen; try discriminate.
          assert (Hfindsig' : find_signature f G = Some sig).
          { unfold find_signature. exact Hfindsig. }
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck0 & Hgen).
          eapply sec_bind_inv in Hgen as (rty & st2 & Hr0 & Hgen).
          eapply sec_bind_inv in Hgen as (rstty & st3 & Hrst0 & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st4 & Hinp0 & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st5 & Hout0 & Hgc).
          unfold option_to_sec in Hck0.
          destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck; try discriminate.
          inversion Hck0; subst ckty' st1.
          unfold find_env in Hr0.
          destruct (Env.find rx env) as [rty'|] eqn:Hrfind; try discriminate.
          unfold ret in Hr0. inversion Hr0; subst rty' st2.
          unfold option_to_sec in Hrst0.
          destruct (assign_clk_type env rst_ty rck) as [rstty'|] eqn:Hrstck; try discriminate.
          inversion Hrst0; subst rstty' st3.
          eapply generate_constraints_scoped.
          -- exact (Hscoped f sig Hfindsig').
          -- eapply mmap_assign_exp_type_scoped.
             ++ eapply wc_call_args_scoped; eauto.
             ++ exact Hinp0.
          -- eapply assign_clk_type_scoped with (base := base_ty) (ck := ck).
             ++ exact Hbase.
             ++ intros z Hz.
                destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_call_clock_free_in_vars.
             ++ exact Hck.
          -- apply st_scoped_merge.
             ++ apply st_scoped_singleton.
                destruct (Hvars rx) as (ty & Henv' & Hscope).
                ** eapply In_InMembers. specialize (Hreset (rx, rck) eq_refl). exact Hreset.
                ** rewrite Hrfind in Henv'. inversion Henv'. subst. exact Hscope.
             ++ eapply assign_clk_type_scoped with (base := rst_ty) (ck := rck).
                ** exact Hrst.
                ** intros z Hz.
                   assert (Hinr : In (rx, rck) vars) by (specialize (Hreset (rx, rck) eq_refl); exact Hreset).
                   assert (Hwr : wc_clock vars rck) by (eapply wc_env_var; eauto).
                   destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_clock_free_in_vars, In_InMembers.
                ** exact Hrstck.
          -- eapply SC.mmap_find_env_scoped.
             ++ intros y Hy. eapply wc_call_outs_scoped; eauto.
             ++ exact Hout0.
          -- exact Hgc.
        * simpl in Hgen.
          unfold find_signature in Hgen.
          destruct (List.find (fun n0 => ident_eqb n0.(s_name) f) G) as [sig|] eqn:Hfindsig; simpl in Hgen; try discriminate.
          assert (Hfindsig' : find_signature f G = Some sig).
          { unfold find_signature. exact Hfindsig. }
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck0 & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinp0 & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st3 & Hout0 & Hgc).
          unfold option_to_sec in Hck0.
          destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck; try discriminate.
          inversion Hck0; subst ckty' st1.
          eapply generate_constraints_scoped.
          -- exact (Hscoped f sig Hfindsig').
          -- eapply mmap_assign_exp_type_scoped.
             ++ eapply wc_call_args_scoped; eauto.
             ++ exact Hinp0.
          -- eapply assign_clk_type_scoped with (base := base_ty) (ck := ck).
             ++ exact Hbase.
             ++ intros z Hz.
                destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_call_clock_free_in_vars.
             ++ exact Hck.
          -- apply st_scoped_singleton. exact Hrst.
          -- eapply SC.mmap_find_env_scoped.
             ++ intros y Hy. eapply wc_call_outs_scoped; eauto.
             ++ exact Hout0.
          -- exact Hgc.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst. clear Hgen.
      unfold option_to_sec in Hck.
      destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck'; try discriminate.
      inversion Hck; subst.
      unfold option_to_sec in Hexp.
      destruct (assign_exp_type env exp) as [expty'|] eqn:Hexp'; try discriminate.
      inversion Hexp; subst.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Hfind'; try discriminate.
      inversion Hfind; subst.
      inversion Hwc as [| |x' ck' v exp' Hx Hexpwc]; subst.
      assert (Hsc_rst : st_scoped scope [rst_ty]).
      { apply st_scoped_singleton. exact Hrst. }
      assert (Hsc_ck : st_scoped scope ckty).
      { eapply assign_clk_type_scoped with (base := base_ty) (ck := ck).
          - exact Hbase.
          - intros z Hz.
            assert (Hwc_ck : wc_clock vars ck) by (eapply wc_clock_exp; eauto).
            pose proof (wc_clock_free_in_vars vars z ck Hwc_ck Hz) as Hmem.
            destruct (Hvars z) as (ty & Henv' & Hscope); [exact Hmem|].
            exists ty; split; assumption.
          - exact Hck'. }
      assert (Hsc_exp : st_scoped scope expty).
      { eapply assign_exp_type_scoped with (e := exp).
        - intros z Hz.
          destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_exp_free_in_vars.
        - exact Hexp'. }
      assert (Hsc_lhs : st_scoped scope ((([rst_ty] ⊔ ckty) ⊔ expty))).
      { apply st_scoped_merge.
        - apply st_scoped_merge; assumption.
        - exact Hsc_exp. }
      constructor.
      + intros y Hin.
        unfold constraint_scope in Hin. simpl in Hin.
        rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        * exact (Hsc_lhs _ Hin).
        * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
          eapply SC.find_env_in_scope with (A := clock) (ann := ck) (st := st') (st' := st'); eauto.
          unfold find_env. rewrite Hfind'. reflexivity.
      + constructor.
  Qed.

  (** This shows that raw constraints generated from a node's equations stay inside the chosen security scope.  Signature generation uses it before local variables are eliminated. *)
  Theorem generate_eqns_constraints_scoped:
    forall P vars scope eqs cns st st',
      secglobal_scoped G ->
      wc_env vars ->
      Forall (wc_equation P vars) eqs ->
      vars_env_scoped vars scope ->
      In base_ty scope ->
      In rst_ty scope ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      constraints_scoped scope cns.
  Proof.
    induction eqs as [|eq eqs IH]; intros cns st st'
                                      Hscoped Henv Hwc Hvars Hbase Hrst Hgen.
    - simpl in Hgen. inversion Hgen; subst. constructor.
    - inversion Hwc as [|? ? Hwc_eq Hwc_eqs]; subst.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Heq & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Heqs & Hret).
      unfold ret in Hret. inversion Hret; subst.
      apply Forall_app.
      split.
      + eapply generate_eqn_constraint_scoped; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma get_mappings_app:
    forall xs ys txs tys,
      get_mappings xs env = Some txs ->
      get_mappings ys env = Some tys ->
      get_mappings (xs ++ ys) env = Some (txs ++ tys).
  Proof.
    induction xs as [|x xs IH]; intros ys txs tys Hxs Hys.
    - simpl in Hxs. inversion Hxs; subst. exact Hys.
    - simpl in Hxs.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [txs'|] eqn:Htail; try discriminate.
      inversion Hxs; subst txs.
      simpl. rewrite Hfind.
      rewrite (IH ys txs' tys eq_refl Hys).
      reflexivity.
  Qed.

  Lemma get_mappings_nodup:
    forall xs tys,
      NoDup xs ->
      env_injective ->
      get_mappings xs env = Some tys ->
      NoDup tys.
  Proof.
    induction xs as [|x xs IH]; intros tys Hnd Hinj Hmap.
    - simpl in Hmap. inversion Hmap. constructor.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Htail; try discriminate.
      inversion Hmap; subst tys.
      apply NoDup_cons.
      + intro Hin.
        apply NoDup_cons_iff in Hnd as [Hnin _].
        assert (exists y, In y xs /\ Env.find y env = Some xty).
        {
          clear IH Hmap.
          revert tys' Htail Hin.
          induction xs as [|y ys IHys]; intros tys' Htail Hin.
          - simpl in Htail. inversion Htail; subst tys'. inversion Hin.
          - simpl in Htail.
            destruct (Env.find y env) as [yty|] eqn:Hyfind; try discriminate.
            destruct (get_mappings ys env) as [tys''|] eqn:Hys; try discriminate.
            inversion Htail; subst tys'.
            simpl in Hin.
            destruct Hin as [Heq|Hin'].
            + inversion Heq; subst yty. exists y. split; [left; reflexivity|exact Hyfind].
            + specialize (IHys (fun Hinys => Hnin (or_intror Hinys)) _ eq_refl Hin')
                as (z & Hinz & Hzfind).
              exists z. split; [right; exact Hinz|exact Hzfind].
        }
        destruct H as (y & Hiny & Hyfind).
        assert (x = y) by (eapply Hinj; eauto).
        subst y. contradiction.
        + apply IH.
          * now apply NoDup_cons_iff in Hnd.
          * exact Hinj.
        * exact eq_refl.
  Qed.

  Lemma nodup_singleton_map:
    forall (xs : list ident),
      NoDup xs ->
      NoDup (map (fun ty => [ty]) xs).
  Proof.
    intros xs Hnd.
    induction Hnd as [|x xs Hnin Hnd IH]; simpl.
    - constructor.
    - constructor.
      + intro Hin.
        apply in_map_iff in Hin as (y & Hy & Hiny).
        inversion Hy; subst y. contradiction.
      + exact IH.
  Qed.

  Lemma mmap_find_env_inv:
    forall xs tys st st',
      mmap (fun x => find_env x env) xs st = OK (tys, st') ->
      st' = st /\ get_mappings xs env = Some tys.
  Proof.
    induction xs as [|x xs IH]; intros tys st st' Hmap.
    - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. split; auto.
    - simpl in Hmap.
      eapply sec_bind_inv in Hmap as (xty & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
      unfold find_env in Hhd.
      destruct (Env.find x env) as [xty'|] eqn:Hfind; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst xty st1.
      specialize (IH _ _ _ Htl) as [Hst Hmaps].
      subst st2.
      unfold ret in Hret. inversion Hret; subst tys st'.
      split; auto.
      simpl. rewrite Hfind, Hmaps. reflexivity.
  Qed.

  Lemma generate_eqn_constraint_shape:
    forall eq cns st st',
      env_injective ->
      NoDup (var_defined eq) ->
      generate_eqn_constraint eq st = OK (cns, st') ->
      exists tys,
        get_mappings (var_defined eq) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    intros eq cns st st' Hinj Hnd Hgen.
    destruct eq as [x ck ce|xs ck f exps r|x ck c0 exp].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst cns st'. clear Hgen.
      unfold option_to_sec in Hck.
      destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck'; try discriminate.
      inversion Hck; subst ckty st1.
      unfold option_to_sec in Hexp.
      destruct (assign_cexp_type env ce) as [expty'|] eqn:Hexp'; try discriminate.
      inversion Hexp; subst expty st2.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      exists [xty']. split.
      + simpl. rewrite Hfind'. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - destruct xs as [|x0 xs0] eqn:Hxs.
      + simpl in Hgen. inversion Hgen; subst cns st'. exists []. split; [reflexivity|].
        split; [reflexivity|]. unfold wf_constraints. split; constructor.
      + simpl in Hnd.
        destruct r as [[rx rck]|].
        * simpl in Hgen.
          unfold find_signature in Hgen.
          destruct (List.find (fun n0 => ident_eqb n0.(s_name) f) G) as [sig|] eqn:Hfindsig; simpl in Hgen; try discriminate.
          assert (Hfindsig' : find_signature f G = Some sig).
          { unfold find_signature. exact Hfindsig. }
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck0 & Hgen).
          eapply sec_bind_inv in Hgen as (rty & st2 & Hr0 & Hgen).
          eapply sec_bind_inv in Hgen as (rstty & st3 & Hrst0 & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st4 & Hinp0 & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st5 & Hout0 & Hgc).
          unfold option_to_sec in Hck0.
          destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck; try discriminate.
          inversion Hck0; subst ckty st1.
          unfold find_env in Hr0.
          destruct (Env.find rx env) as [rty'|] eqn:Hrfind; try discriminate.
          unfold ret in Hr0. inversion Hr0; subst rty st2.
          unfold option_to_sec in Hrst0.
          destruct (assign_clk_type env rst_ty rck) as [rstty'|] eqn:Hrstck; try discriminate.
          inversion Hrst0; subst rstty st3.
          assert (Houts : st5 = st4 /\ get_mappings (x0 :: xs0) env = Some outtyp).
          { eapply mmap_find_env_inv; eauto. }
          destruct Houts as [Hstouts Hmapouts]. subst st5.
          assert (Hndout : NoDup outtyp).
          { eapply get_mappings_nodup; eauto. }
          destruct (generate_constraints_shape sig inptyp ckty' ([rty'] ⊔ rstty') outtyp cns st4 st'
                    Hndout Hgc) as [Hwf Hsnd].
          exists outtyp. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
        * simpl in Hgen.
          unfold find_signature in Hgen.
          destruct (List.find (fun n0 => ident_eqb n0.(s_name) f) G) as [sig|] eqn:Hfindsig; simpl in Hgen; try discriminate.
          assert (Hfindsig' : find_signature f G = Some sig).
          { unfold find_signature. exact Hfindsig. }
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck0 & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinp0 & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st3 & Hout0 & Hgc).
          unfold option_to_sec in Hck0.
          destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck; try discriminate.
          inversion Hck0; subst ckty st1.
          assert (Houts : st3 = st2 /\ get_mappings (x0 :: xs0) env = Some outtyp).
          { eapply mmap_find_env_inv; eauto. }
          destruct Houts as [Hstouts Hmapouts]. subst st3.
          assert (Hndout : NoDup outtyp).
          { eapply get_mappings_nodup; eauto. }
          destruct (generate_constraints_shape sig inptyp ckty' [rst_ty] outtyp cns st2 st'
                    Hndout Hgc) as [Hwf Hsnd].
          exists outtyp. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst cns st'. clear Hgen.
      unfold option_to_sec in Hck.
      destruct (assign_clk_type env base_ty ck) as [ckty'|] eqn:Hck'; try discriminate.
      inversion Hck; subst ckty st1.
      unfold option_to_sec in Hexp.
      destruct (assign_exp_type env exp) as [expty'|] eqn:Hexp'; try discriminate.
      inversion Hexp; subst expty st2.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      exists [xty']. split.
      + simpl. rewrite Hfind'. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
  Qed.

  Theorem generate_eqns_constraints_shape:
    forall eqs cns st st',
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      exists tys,
        get_mappings (vars_defined eqs) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    induction eqs as [|eq eqs IH]; intros cns st st' Hinj Hnd Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; [reflexivity|].
      split; [reflexivity|].
      unfold wf_constraints. split; constructor.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Heq & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Heqs & Hret).
      unfold ret in Hret. inversion Hret; subst.
      assert (Hndsplit : NoDup (var_defined eq ++ vars_defined eqs)).
      { simpl in Hnd. exact Hnd. }
      apply NoDup_app'_iff in Hndsplit as [Hnd1 [Hnd2 Hdisj]].
      edestruct generate_eqn_constraint_shape as (tys1 & Hmap1 & Hsnd1 & Hwf1); eauto.
      edestruct IH as (tys2 & Hmap2 & Hsnd2 & Hwf2); eauto.
        exists (tys1 ++ tys2). split.
        + simpl. eapply get_mappings_app; eauto.
        + split.
          * rewrite map_app.
            transitivity (map (fun ty : ident => [ty]) tys1 ++ map snd c2).
            { f_equal. exact Hsnd1. }
            transitivity (map (fun ty : ident => [ty]) tys1 ++ map (fun ty : ident => [ty]) tys2).
            { f_equal. exact Hsnd2. }
            rewrite map_app. reflexivity.
          * unfold wf_constraints in *.
            destruct Hwf1 as [Hndc1 Hfor1].
            destruct Hwf2 as [Hndc2 Hfor2].
            assert (Hsnd :
                      map snd (c1 ++ c2) =
                      map (fun ty : ident => [ty]) (tys1 ++ tys2)).
            { rewrite map_app.
              transitivity (map (fun ty : ident => [ty]) tys1 ++ map snd c2).
              { f_equal. exact Hsnd1. }
              transitivity (map (fun ty : ident => [ty]) tys1 ++ map (fun ty : ident => [ty]) tys2).
              { f_equal. exact Hsnd2. }
              rewrite map_app. reflexivity. }
            split.
            -- rewrite Hsnd.
               eapply nodup_singleton_map.
               eapply get_mappings_nodup with (xs := vars_defined (eq :: eqs)) (tys := tys1 ++ tys2).
               ++ exact Hnd.
               ++ exact Hinj.
               ++ simpl. eapply get_mappings_app; eauto.
            -- rewrite Forall_app. split; auto.
  Qed.

  Corollary generate_eqns_constraints_wf:
    forall eqs cns st st',
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      wf_constraints cns.
  Proof.
    intros eqs cns st st' Hinj Hnd Hgen.
    edestruct generate_eqns_constraints_shape as (? & ? & ? & Hwf); eauto.
  Qed.

  End SECEQNTYPING.

  Section SECNODETYPING.
    Variable G: secglobal.

    Corollary generate_node_eqns_constraints_wf:
      forall n env base_ty rst_ty raw st st',
        env_injective env ->
        generate_eqns_constraints G env base_ty rst_ty n.(n_eqs) st = OK (raw, st') ->
        wf_constraints raw.
    Proof.
      intros n env base_ty rst_ty raw st st' Hinj Hraw.
      eapply generate_eqns_constraints_wf; eauto.
      apply NoDup_var_defined_n_eqs.
    Qed.

    Definition generate_node_signature (n: node): res signature :=
      match  (do (env_in,  inp)  <- insert_vars (List.map fst (n.(n_in))) (Env.empty _);
              do (env_out, out)  <- insert_vars (List.map fst n.(n_out)) env_in;
              do ck_id           <- fresh_ident;
              do rst_id          <- fresh_ident;
              do (env, locals)   <- insert_vars (List.map fst n.(n_vars)) env_out;
              do constraints'    <- generate_eqns_constraints G env ck_id rst_id (n.(n_eqs));
              ret (n_name n, inp, out, rst_id, ck_id, simplify constraints' locals, env_out)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints, _),_) =>
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.

      Definition generate_node_sig (n: node) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match  (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(n_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(n_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(n_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(n_vars)) env);

              do constraints'    <- generate_eqns_constraints G env clk_type rst_type (n.(n_eqs));
              ret (n_name n, inp, out, rst_type, clk_type, simplify constraints' locals, env)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints, _),_) =>
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.

      Definition generate_node_sig_scoped_env
        (n: node) (envs: node_scoped_env) (aux_names: list node_aux_names)
        : res signature :=
        match find_node_env n.(n_name) envs with
        | None =>
            Error (MSG "Missing node-local security environment" :: [CTX n.(n_name)])
        | Some env =>
            generate_node_sig n env aux_names
        end.

      (** This lifts equation-level scopedness to one generated NLustre signature.  Later proofs use it whenever a fresh source signature is added to the global accumulator. *)
      Theorem generate_node_sig_scoped:
        forall P n env aux_names sig,
          secglobal_scoped G ->
          env_injective env ->
          wc_node P n ->
          generate_node_sig n env aux_names = OK sig ->
          signature_scoped sig.
      Proof.
        intros P n env aux_names sig
               Hscoped Hinj Hwc Hsig.
        unfold generate_node_sig in Hsig.
        remember
          ((do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(n_name)) aux_names);
            do clk_type <- option_to_sec (Env.find clk_id env);
            do rst_type <- option_to_sec (Env.find rst_id env);
            do inp <- option_to_sec (get_mappings_from_node (n.(n_in)) env);
            do out <- option_to_sec (get_mappings_from_node (n.(n_out)) env);
            do locals <- option_to_sec (get_mappings_from_node (n.(n_vars)) env);
            do constraints' <- generate_eqns_constraints G env clk_type rst_type (n.(n_eqs));
            ret (n_name n, inp, out, rst_type, clk_type, simplify constraints' locals, env))
             init_state) as gen eqn:Hgen.
        destruct gen as [[packed st0]|]; try discriminate.
        destruct packed as [[[[[[name inp] out] rst_type] clk_type] constraints] env1].
        symmetry in Hgen.
        inversion Hsig; subst sig; clear Hsig.
        eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
        eapply sec_bind_inv in Hgen as (clk_type' & st_clk & Hclk & Hgen).
        eapply sec_bind_inv in Hgen as (rst_type' & st_rst & Hrst & Hgen).
        eapply sec_bind_inv in Hgen as (inp' & st_inp & Hinp & Hgen).
        eapply sec_bind_inv in Hgen as (out' & st_out & Hout & Hgen).
        eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
        eapply sec_bind_inv in Hgen as (raw & st_raw & Hraw & Hret).
        unfold option_to_sec in Haux.
        destruct (get_node_aux (n.(n_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
        inversion Haux; subst clk_id0 rst_id0 st_aux.
        unfold option_to_sec in Hclk.
        destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
        inversion Hclk; subst clk_type0 st_clk.
        unfold option_to_sec in Hrst.
        destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
        inversion Hrst; subst rst_type0 st_rst.
        unfold option_to_sec in Hinp.
        destruct (get_mappings_from_node (n.(n_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
        inversion Hinp; subst inp0 st_inp.
        unfold option_to_sec in Hout.
        destruct (get_mappings_from_node (n.(n_out)) env) as [out0|] eqn:Hout0; try discriminate.
        inversion Hout; subst out0 st_out.
        unfold option_to_sec in Hlocals.
        destruct (get_mappings_from_node (n.(n_vars)) env) as [locals0|] eqn:Hlocals0; try discriminate.
        inversion Hlocals; subst locals0 st_locals.
        unfold ret in Hret. inversion Hret; subst name inp out rst_type clk_type constraints env1 st0.
          unfold signature_scoped, signature_scope.
          eapply simplify_scoped.
          - eapply get_mappings_nodup with (xs := map fst (n.(n_vars))) (tys := locals).
            + apply fst_NoDupMembers.
              pose proof n.(n_nodup) as Hnodup.
              apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
              exact Hnodup.
            + exact Hinj.
            + eapply get_mappings_from_node_eq; eauto.
          - eapply (generate_eqns_constraints_scoped
                      G env clk_type' rst_type' P
                      (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                      ((inp' ++ out' ++ [clk_type'; rst_type']) ++ locals)
                      (n.(n_eqs))).
            + exact Hscoped.
            + inversion Hwc as (_ & _ & Henv & _).
              exact Henv.
            + inversion Hwc as (_ & _ & _ & Heqs).
              exact Heqs.
            + intros x Hmem.
              apply InMembers_idck in Hmem.
              apply InMembers_app in Hmem.
              destruct Hmem as [Hin|Hin].
              * destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp0) as (ty & Hfind & Hin').
                exists ty. split; [exact Hfind|].
                apply in_or_app. left.
                apply in_or_app. left.
                exact Hin'.
              * apply InMembers_app in Hin.
                destruct Hin as [Hin|Hin].
                -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals0) as (ty & Hfind & Hin').
                   exists ty. split; [exact Hfind|].
                   apply in_or_app. right.
                   exact Hin'.
                -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout0) as (ty & Hfind & Hin').
                   exists ty. split; [exact Hfind|].
                   apply in_or_app. left.
                   apply in_or_app. right.
                   apply in_or_app. left.
                   exact Hin'.
            + apply in_or_app. left.
              apply in_or_app. right.
              apply in_or_app. right.
              simpl. now left.
            + apply in_or_app. left.
              apply in_or_app. right.
              apply in_or_app. right.
              simpl. now right; left.
            + exact Hraw.
          - intros d Hd.
            edestruct get_mappings_from_node_In as (x & a & Hinvar & Hfindx); eauto.
            assert (Hdefx : In x (vars_defined n.(n_eqs))).
            { apply IsD.Is_defined_in_vars_defined.
              eapply IsD.node_variable_defined_in_eqs.
              eapply in_map with (f := fst) in Hinvar.
              simpl in Hinvar.
              exact Hinvar. }
            assert (Hexshape :
                      exists tys,
                        get_mappings (vars_defined n.(n_eqs)) env = Some tys /\
                        map snd raw = map (fun ty => [ty]) tys /\
                        wf_constraints raw).
            { eapply (generate_eqns_constraints_shape
                        G env clk_type' rst_type' (n.(n_eqs)) raw init_state st_raw).
              - exact Hinj.
              - apply NoDup_var_defined_n_eqs.
              - exact Hraw. }
            destruct Hexshape as (tys & Hmapdefs & Hsnd & Hwf).
          eapply get_mappings_in in Hmapdefs as (ty & Hfindty & Hintys); eauto.
          rewrite Hfindx in Hfindty. inversion Hfindty; subst ty.
          rewrite Hsnd. apply in_map_iff.
          exists d. split; [reflexivity|exact Hintys].
      Qed.

  End SECNODETYPING.

  Section SECGLOBALTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_signatures' (acc: list signature) (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns =>
        do sig <- generate_node_sig acc n env aux_names;
        generate_all_signatures' (sig::acc) ns env aux_names
      end.
    Definition generate_all_signatures (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names): res (list signature) :=
      generate_all_signatures' [] node_list env aux_names.

    Fixpoint generate_all_signatures_scoped_env'
      (acc: list signature) (node_list: global) (envs: node_scoped_env)
      (aux_names: list node_aux_names) : res (list signature) :=
      match node_list with
      | [] => OK acc
      | n :: ns =>
          do sig <- generate_node_sig_scoped_env acc n envs aux_names;
          generate_all_signatures_scoped_env' (sig :: acc) ns envs aux_names
      end.

    Definition generate_all_signatures_scoped_env
      (node_list: global) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res (list signature) :=
      generate_all_signatures_scoped_env' [] node_list envs aux_names.

    Theorem generate_all_signatures_scoped':
        forall nodes acc env aux_names G,
        wc_global nodes ->
        secglobal_scoped acc ->
        env_injective env ->
        generate_all_signatures' acc nodes env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      induction nodes as [|n nodes IH]; intros acc env aux_names G
                                              Hwc Hacc Hinj Hgen.
      - simpl in Hgen. inversion Hgen; subst. exact Hacc.
      - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        simpl in Hgen.
          destruct (generate_node_sig acc n env aux_names) as [sig|] eqn:Hsig;
            simpl in Hgen;
            try discriminate.
          destruct (generate_all_signatures' (sig :: acc) nodes env aux_names) as [G'|] eqn:Htl;
            simpl in Hgen;
            try discriminate.
          inversion Hgen; subst. clear Hgen.
          eapply IH with (acc := sig :: acc) (env := env) (aux_names := aux_names); eauto.
          eapply secglobal_scoped_cons; eauto.
          eapply generate_node_sig_scoped; eauto.
      Qed.

    (** This is the main global scopedness theorem for generated NLustre signatures.  From a well-clocked global and an injective shared naming environment, it proves that every generated signature only mentions identifiers from its visible interface and local scope.  The source-side correctness, translation, and noninterference files all reuse this global invariant. *)
    Corollary generate_all_signatures_scoped:
      forall nodes env aux_names G,
        wc_global nodes ->
        env_injective env ->
        generate_all_signatures nodes env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros nodes env aux_names G Hwc Hinj Hgen.
      unfold generate_all_signatures in Hgen.
      eapply generate_all_signatures_scoped'; eauto.
      apply secglobal_scoped_nil.
    Qed.

    Fixpoint generate_signatures' (acc: list signature) (node_list: global): res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns =>
        do sig <- generate_node_signature acc n;
        generate_signatures' (sig::acc) ns
      end.

    Definition generate_signatures (node_list: global) := generate_signatures' [] node_list.

  End SECGLOBALTYPING.

End SECNLUSTYPING.

Module SecNLusTyping
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import Ord   : NLORDERED Ids Op CESyn SynNL)
  (Import Mem   : MEMORIES Ids Op CESyn SynNL)
  (Import IsD   : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo   : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  <: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo.

Include SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo.

End SecNLusTyping.
