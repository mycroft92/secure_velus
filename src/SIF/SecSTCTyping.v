
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String. (*Required for Errors *)
From Coq Require Import Lia.
From Coq Require Import Lists.ListSet.
From Coq Require Import Sorting.Permutation.
From compcert Require Import common.Errors.


Import List.ListNotations.

Module Type SECSTCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).
  Module CEIsF := CEIsFreeFun Ids Op CESyn.
  Module CEClo := CEClockingFun Ids Op CESyn.
  Module Last := StcIsLastFun Ids Op CESyn SynStc.
  Module Var := StcIsVariableFun Ids Op CESyn SynStc.
  Module Def := StcIsDefinedFun Ids Op CESyn SynStc Var Last.
  Module Syst := StcIsSystemFun Ids Op CESyn SynStc.
  Module Ord := StcOrderedFun Ids Op CESyn SynStc Syst.
  Module IsF := StcIsFreeFun Ids Op CESyn SynStc CEIsF.
  Module Clo := StcClockingFun Ids Op CESyn SynStc Last Var Def Syst Ord CEClo.
  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x'
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  (* STC signatures hide ordinary locals together with the translated memory
     cells ([s_lasts]) and the STC-only reset-instance auxiliaries.  We remove
     duplicates defensively so the later [simplify_scoped] theorem can be
     applied without having to restate a separate disjointness proof for the
     reset namespace. *)
  Definition hidden_sys_vars (locals lasts rids: list ident) : list ident :=
    nodup ident_eq_dec (locals ++ lasts ++ rids).

  Definition env_injective (env: Env.t ident) : Prop :=
    forall x y tx ty,
      Env.find x env = Some tx ->
      Env.find y env = Some ty ->
      tx = ty ->
      x = y.

  Section RESETHANDLER.
  (** This section collects STC reset statements and assigns one fresh
      reset-instance type variable to each translated reset call. *)
  Fixpoint collect_reset_stmts' (trl: list trconstr) (acc: list trconstr) : list trconstr :=
    match trl with
    | [] => acc
    | tr::trl' => 
      (match tr with
        | TcReset _ _ _ => collect_reset_stmts' trl' (acc ++ [tr])
        | _             => collect_reset_stmts' trl' acc
        end)
    end.

  Definition collect_reset_stmts trl := collect_reset_stmts' trl [].

  (* Reset-instance type variables are STC-specific auxiliaries.
     Keep them in their own namespace so they never clash with the
     shared NLustre/STC interface/local type variables. *)
  Definition fresh_reset_ident : Sec ident :=
    fun n =>
      let id := Ids.gensym Ids.sec_reset n in
      OK (id, Pos.succ n).

  Definition fresh_reset_insert (k: ident) (env: Env.t ident): Sec (Env.t ident * ident) :=
    if Env.mem k env then
      error (MSG "Key declared more than once " :: [CTX k])
    else
      do v <- fresh_reset_ident;
      do e <- insert_env k v env;
      ret (e, v).

  (* Insert one reset-instance type variable for a translated [TcReset]. *)
  Definition assign_reset_type (tr: trconstr) (env: Env.t ident) : Sec (Env.t ident * ident) :=
    match tr with
    | TcReset x ck f => fresh_reset_insert x env
    | _ => error (msg "Not a reset statement! ")
    end. 

  Fixpoint generate_reset_env' (trl: list trconstr) (env: Env.t ident) (acc: list ident): Sec (Env.t ident * list ident) :=
    match trl with
    | [] => ret (env, acc)
    | t :: trl => 
       (match t with
        | TcReset _ _ _ => 
             do (env',i)   <- assign_reset_type  t env; 
             generate_reset_env' trl env' (acc++[i])
        | _  => generate_reset_env' trl env acc
        end)
     end.
  
  Definition generate_reset_env trl : Sec (Env.t ident * list ident) := generate_reset_env' trl (Env.empty _) [].
  End RESETHANDLER.

  (** STC translated-constraint typing in the shared naming environment plus
      the STC-only reset-instance environment. *)
  Section SECTRCONSTRTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable reset_env: Env.t ident.
    Variable base_ty: ident.
    Variable rst_ty : ident.

    Definition vars_env_scoped {A: Type} (vars: list (ident * A)) (scope: list ident) : Prop :=
      forall x,
        InMembers x vars ->
        exists ty, Env.find x env = Some ty /\ In ty scope.

    Lemma wc_clock_free_in_vars:
      forall vars x ck,
        CEClo.wc_clock vars ck ->
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
        CEClo.wc_exp vars e ck ->
        CEIsF.Is_free_in_exp x e ->
        InMembers x vars.
    Proof.
      intros vars x e ck Hwc.
      induction Hwc; intro Hfree; inversion Hfree; subst; eauto using In_InMembers.
    Qed.

    Lemma wc_cexp_free_in_vars:
      forall vars x ce ck,
        CEClo.wc_cexp vars ce ck ->
        CEIsF.Is_free_in_cexp x ce ->
        InMembers x vars.
    Proof.
      intros vars x ce ck Hwc.
      induction Hwc; intro Hfree; inversion Hfree; subst; eauto using In_InMembers, wc_exp_free_in_vars.
    Qed.

    Lemma wc_aexp_free_in_vars:
      forall vars x ck e,
        CEClo.wc_env vars ->
        CEClo.wc_exp vars e ck ->
        CEIsF.Is_free_in_aexp x ck e ->
        InMembers x vars.
    Proof.
      intros vars x ck e Henv Hwc Hfree.
      inversion Hfree; subst.
      - eauto using wc_exp_free_in_vars.
      - eauto using wc_clock_free_in_vars, CEClo.wc_clock_exp.
    Qed.

    Lemma wc_caexp_free_in_vars:
      forall vars x ck ce,
        CEClo.wc_env vars ->
        CEClo.wc_cexp vars ce ck ->
        CEIsF.Is_free_in_caexp x ck ce ->
        InMembers x vars.
    Proof.
      intros vars x ck ce Henv Hwc Hfree.
      inversion Hfree; subst.
      - eauto using wc_cexp_free_in_vars.
      - eauto using wc_clock_free_in_vars, CEClo.wc_clock_cexp.
    Qed.

    Lemma assign_clk_type_scoped:
      forall scope ck st,
        In base_ty scope ->
        (forall x, Is_free_in_clock x ck -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
        assign_clk_type env base_ty ck = Some st ->
        st_scoped scope st.
    Proof.
      intros scope ck.
      induction ck as [|ck IH x b]; intros st Hbase Hfree Hassign.
      - simpl in Hassign. inversion Hassign; subst.
        apply st_scoped_singleton. exact Hbase.
      - simpl in Hassign.
        destruct (assign_clk_type env base_ty ck) as [ckty|] eqn:Hck; try discriminate.
        destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
        inversion Hassign; subst st.
        eapply st_scoped_merge.
        + eapply IH; eauto.
          intros y Hy.
          apply Hfree. now constructor 2.
        + apply st_scoped_singleton.
          destruct (Hfree x) as (? & Hfind' & Hin); [constructor 1|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
    Qed.

    Lemma assign_exp_type_scoped:
      forall scope e st,
        (forall x, CEIsF.Is_free_in_exp x e -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
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
        eapply st_scoped_merge.
        + eapply IHe; eauto.
          intros x Hx. apply Hfree. now constructor 1.
        + apply st_scoped_singleton.
          destruct (Hfree i) as (? & Hfind' & Hin); [constructor 2|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
      - simpl in Hassign. eauto.
      - simpl in Hassign.
        destruct (assign_exp_type env e1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_exp_type env e2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        eapply st_scoped_merge.
        + eapply IHe1; eauto.
          intros x Hx. apply Hfree. now constructor 5; left.
        + eapply IHe2; eauto.
          intros x Hx. apply Hfree. now constructor 5; right.
    Qed.

    Lemma assign_cexp_type_scoped:
      forall scope ce st,
        (forall x, CEIsF.Is_free_in_cexp x ce -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
        assign_cexp_type env ce = Some st ->
        st_scoped scope st.
    Proof.
      induction ce; intros st Hfree Hassign.
      - simpl in Hassign.
        destruct (Env.find i env) as [xty|] eqn:Hfind; try discriminate.
        destruct (assign_cexp_type env ce1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_cexp_type env ce2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        eapply st_scoped_merge.
        + apply st_scoped_singleton.
          destruct (Hfree i) as (? & Hfind' & Hin); [constructor 1|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
        + eapply st_scoped_merge.
          * eapply IHce1; eauto.
            intros x Hx. apply Hfree. now constructor 2.
          * eapply IHce2; eauto.
            intros x Hx. apply Hfree. now constructor 3.
      - simpl in Hassign.
        destruct (assign_exp_type env e) as [ety|] eqn:He; try discriminate.
        destruct (assign_cexp_type env ce1) as [sty1|] eqn:He1; try discriminate.
        destruct (assign_cexp_type env ce2) as [sty2|] eqn:He2; try discriminate.
        inversion Hassign; subst.
        eapply st_scoped_merge.
        + eapply assign_exp_type_scoped; eauto.
          intros x Hx. apply Hfree. now constructor 4.
        + eapply st_scoped_merge.
          * eapply IHce1; eauto.
            intros x Hx. apply Hfree. now constructor 5.
          * eapply IHce2; eauto.
            intros x Hx. apply Hfree. now constructor 6.
      - simpl in Hassign.
        eapply assign_exp_type_scoped; eauto.
        intros x Hx. apply Hfree. now constructor.
    Qed.

    Lemma mmap_assign_exp_type_scoped:
      forall scope es tys st st',
        Forall
          (fun e =>
             forall x,
               CEIsF.Is_free_in_exp x e ->
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

    Lemma mmap_find_env_scoped:
      forall scope xs tys st st',
        (forall x, In x xs -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
        mmap (fun x => find_env x env) xs st = OK (tys, st') ->
        Forall (fun ty => In ty scope) tys.
    Proof.
      intros scope xs.
      induction xs as [|x xs IH]; intros tys st st' Hscope Hmap.
      - simpl in Hmap. inversion Hmap; subst. constructor.
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (xty & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold find_env in Hhd.
        destruct (Env.find x env) as [xty'|] eqn:Hfind; try discriminate.
        inversion Hhd; subst xty st1.
        unfold ret in Hret. inversion Hret; subst tys st'.
        constructor.
        + destruct (Hscope x) as (? & Hfind' & Hin); [left; reflexivity|].
          rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
        + eapply IH; eauto.
          intros y Hy. apply Hscope. now right.
    Qed.

    Lemma find_env_in_scope:
      forall A vars scope x ann ty st st',
        vars_env_scoped vars scope ->
        In (x, ann) vars ->
        find_env x env st = OK (ty, st') ->
        In ty scope.
    Proof.
      intros A vars scope x ann ty st st' Hvars Hin Hfind.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [ty'|] eqn:Henv; try discriminate.
      inversion Hfind; subst ty st'.
      destruct (Hvars x) as (? & Hfind' & Hscope); eauto using In_InMembers.
      rewrite Henv in Hfind'. inversion Hfind'. subst. exact Hscope.
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
          apply in_map_iff in Hin as ([|ty] & Heq & Hin'); inversion Heq; subst ty.
          clear Heq.
          assert (exists y, In y xs /\ Env.find y env = Some xty).
          {
            clear IH.
            induction xs as [|y ys IHys].
            - inversion Hin'.
            - simpl in Htail.
              destruct (Env.find y env) as [yty|] eqn:Hyfind; try discriminate.
              destruct (get_mappings ys env) as [tys''|] eqn:Hys; try discriminate.
              inversion Htail; subst tys'.
              simpl in Hin'.
              destruct Hin' as [Heq|Hin''].
              * inversion Heq; subst yty. exists y. split; [left; reflexivity|exact Hyfind].
              * specialize (IHys Hys Hin'') as (z & Hinz & Hzfind).
                exists z. split; [right; exact Hinz|exact Hzfind].
          }
          destruct H as (y & Hiny & Hyfind).
          assert (x = y) by (eapply Hinj; eauto).
          subst y. contradiction.
        + apply IH.
          * now apply NoDup_cons_iff in Hnd.
          * exact Hinj.
          * exact Htail.
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

    Lemma wc_tc_clock_free_in_vars:
      forall P vars i xs ck rst f es x,
        CEClo.wc_env vars ->
        Clo.wc_trconstr P vars (TcCall i xs ck rst f es) ->
        Is_free_in_clock x ck ->
        InMembers x vars.
    Proof.
      intros P vars i xs ck rst f es x Henv Hwc Hfree.
      inversion Hwc as [| | |i' xs' ck' rst' f' es' s P' sub Hfind Hins Houts]; subst.
      destruct s.(s_in) as [|[xin [tin xck]] ins] eqn:Hinps.
      { simpl in s.(s_ingt0). lia. }
      inversion Hins as [|? ? ? ? Hhead Htail]; subst.
      destruct Hhead as (_ & lck & Hexp & Hinst).
      assert (Hfree' : Is_free_in_clock x lck).
      { eapply instck_free_bck; eauto. }
      assert (Hwc_lck : CEClo.wc_clock vars lck).
      { eapply CEClo.wc_clock_exp; eauto. }
      eapply wc_clock_free_in_vars; eauto.
    Qed.

    Lemma wc_call_args_scoped:
      forall vars scope sub ck ins es,
        vars_env_scoped vars scope ->
        Forall2
          (fun '(x, (_, xck)) le =>
             SameVar (sub x) le
             /\ exists lck, CEClo.wc_exp vars le lck /\ instck ck sub xck = Some lck)
          ins es ->
        Forall
          (fun e =>
             forall x,
               CEIsF.Is_free_in_exp x e ->
               exists ty, Env.find x env = Some ty /\ In ty scope)
          es.
    Proof.
      intros vars scope sub ck ins es Hvars Hfor.
      induction Hfor.
      - constructor.
      - constructor.
        + intros z Hz.
          destruct H as (_ & lck & Hexp & _).
          destruct (Hvars z) as (ty & Hfind & Hscope); eauto using wc_exp_free_in_vars.
        + exact IHHfor.
    Qed.

    Lemma wc_call_outs_scoped:
      forall vars scope sub ck outs xs,
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
      induction Hfor.
      - inversion Hin.
      - simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst y.
          destruct H as (_ & xck & Hinx & _).
          destruct (Hvars x) as (ty & Hfind & Hscope); eauto using In_InMembers.
        + eapply IHHfor; eauto.
    Qed.

    Lemma fresh_reset_insert_find_in_acc:
      forall k acc st env' rst_inst st' x ty,
        fresh_reset_insert k acc st = OK ((env', rst_inst), st') ->
        Env.find x env' = Some ty ->
        ty = rst_inst \/ Env.find x acc = Some ty.
    Proof.
      intros k acc st env' rst_inst st' x ty Hins Hfind.
      unfold fresh_reset_insert in Hins.
      destruct (Env.mem k acc) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_reset_ident in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
      unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
      destruct (Pos.eq_dec x k) as [Heq|Hneq].
      - subst x. rewrite Env.gss in Hfind. inversion Hfind. auto.
      - rewrite Env.gso in Hfind; auto.
    Qed.

    Lemma generate_reset_env'_find_in_acc:
      forall trs acc rids env' st st' x ty,
        generate_reset_env' trs acc rids st = OK ((env', rids), st') ->
        Env.find x env' = Some ty ->
        In ty rids.
    Proof.
      induction trs as [|tr trs IH]; intros acc rids env' st st' x ty Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst env' rids st'. exact Hfind.
      - simpl in Hgen.
        destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
        1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (acc1 & rst_inst & st1 & Hstep & Hrec).
        eapply IH; eauto.
        destruct (fresh_reset_insert_find_in_acc _ _ _ _ _ _ _ _ Hstep Hfind) as [Heq|Hold].
        + subst ty. apply in_or_app. right. simpl. auto.
        + apply in_or_app. left.
          eapply generate_reset_env'_find_in_acc; eauto.
    Qed.

    Lemma generate_reset_env_find_in:
      forall trs reset_env rids st' x ty,
        generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
        Env.find x reset_env = Some ty ->
        In ty rids.
    Proof.
      intros trs reset_env rids st' x ty Hgen Hfind.
      unfold generate_reset_env in Hgen.
      eapply generate_reset_env'_find_in_acc; eauto.
    Qed.

    Lemma fresh_reset_insert_find_self:
      forall k acc st env' rst_inst st',
        fresh_reset_insert k acc st = OK ((env', rst_inst), st') ->
        Env.find k env' = Some rst_inst.
    Proof.
      intros k acc st env' rst_inst st' Hins.
      unfold fresh_reset_insert in Hins.
      destruct (Env.mem k acc) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_reset_ident in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
      unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
      now rewrite Env.gss.
    Qed.

    Lemma fresh_reset_insert_preserves_find:
      forall k acc st env' rst_inst st' x ty,
        fresh_reset_insert k acc st = OK ((env', rst_inst), st') ->
        Env.find x acc = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros k acc st env' rst_inst st' x ty Hins Hfind.
      unfold fresh_reset_insert in Hins.
      destruct (Env.mem k acc) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_reset_ident in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
      unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
      assert (Hxk : x <> k).
      { intro Heq. subst x.
        assert (Env.mem k acc = true).
        { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
        congruence. }
      now rewrite Env.gso.
    Qed.

    Lemma generate_reset_env'_preserves_find:
      forall trs acc rids st env' rids' st' x ty,
        generate_reset_env' trs acc rids st = OK ((env', rids'), st') ->
        Env.find x acc = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      induction trs as [|tr trs IH]; intros acc rids st env' rids' st' x ty Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. exact Hfind.
      - simpl in Hgen.
        destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
        1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (acc1 & rst_inst & st1 & Hstep & Hrec).
        eapply IH; eauto.
        eapply fresh_reset_insert_preserves_find; eauto.
    Qed.

    Definition trconstr_targets (tr: trconstr) : option (list ident) :=
      match tr with
      | TcDef x _ _
      | TcNext x _ _ =>
          match Env.find x env with
          | Some ty => Some [ty]
          | None => None
          end
      | TcCall _ xs _ _ _ _ =>
          get_mappings xs env
      | TcReset x _ _ =>
          match Env.find x reset_env with
          | Some ty => Some [ty]
          | None => None
          end
      end.

    Fixpoint trconstrs_targets (trs: list trconstr) : option (list ident) :=
      match trs with
      | [] => Some []
      | tr :: trs' =>
          do tys1 <- trconstr_targets tr;
          do tys2 <- trconstrs_targets trs';
          Some (tys1 ++ tys2)
      end.

    Theorem generate_trconstr_constraint_scoped:
      forall P vars scope tr cns st st',
        secglobal_scoped G ->
        CEClo.wc_env vars ->
        Clo.wc_trconstr P vars tr ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1, find_env x reset_env st0 = OK (ty, st1) -> In ty scope) ->
        generate_trconstr_constraint tr st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros P vars scope tr cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      destruct tr as [x ck ce|x ck e|x ck f|x0 xs ck b f exps].
      - simpl in Hgen.
        destruct (option_to_sec (assign_clk_type env base_ty ck) st) as [[ckty st1]|] eqn:Hck; try discriminate.
        destruct (option_to_sec (assign_cexp_type env ce) st1) as [[expty st2]|] eqn:Hexp; try discriminate.
        destruct (find_env x env st2) as [[xty st3]|] eqn:Hfind; try discriminate.
        destruct (ret [(ckty ⊔ expty, [xty])] st3) as [[cns' st4]|] eqn:Hret; try discriminate.
        inversion Hgen; subst cns st'.
        inversion Hwc as [x' ck' ce' Hx Hce| | |]; subst.
        constructor.
        intros y Hin.
        unfold constraint_scope in Hin. simpl in Hin.
        rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + eapply assign_clk_type_scoped in Hin.
          2:{ exact Hbase. }
          2:{
            intros z Hz.
            destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_clock_free_in_vars, CEClo.wc_clock_cexp.
          }
          exact Hin.
        + rewrite in_app_iff in Hin.
          destruct Hin as [Hin|Hin].
          * eapply assign_cexp_type_scoped in Hin.
            2:{
              intros z Hz.
              destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_caexp_free_in_vars.
            }
            exact Hin.
          * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
            eapply find_env_in_scope with (A := clock) (ann := ck); eauto.
      - simpl in Hgen.
        destruct (option_to_sec (assign_clk_type env base_ty ck) st) as [[ckty st1]|] eqn:Hck; try discriminate.
        destruct (option_to_sec (assign_exp_type env e) st1) as [[expty st2]|] eqn:Hexp; try discriminate.
        destruct (find_env x env st2) as [[xty st3]|] eqn:Hfind; try discriminate.
        destruct (ret [(ckty ⊔ expty, [xty])] st3) as [[cns' st4]|] eqn:Hret; try discriminate.
        inversion Hgen; subst cns st'.
        inversion Hwc as [|x' ck' e' Hx Hexpwc| |]; subst.
        constructor.
        intros y Hin.
        unfold constraint_scope in Hin. simpl in Hin.
        rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + eapply assign_clk_type_scoped in Hin.
          2:{ exact Hbase. }
          2:{
            intros z Hz.
            destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_clock_free_in_vars, CEClo.wc_clock_exp.
          }
          exact Hin.
        + rewrite in_app_iff in Hin.
          destruct Hin as [Hin|Hin].
          * eapply assign_exp_type_scoped in Hin.
            2:{
              intros z Hz.
              destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_aexp_free_in_vars.
            }
            exact Hin.
          * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
            eapply find_env_in_scope with (A := clock) (ann := ck); eauto.
      - simpl in Hgen.
        destruct (option_to_sec (assign_clk_type env base_ty ck) st) as [[rckty st1]|] eqn:Hck; try discriminate.
        destruct (find_env x reset_env st1) as [[rst_inst st2]|] eqn:Hrstinst; try discriminate.
        destruct (ret [([rst_ty] ⊔ rckty, [rst_inst])] st2) as [[cns' st3]|] eqn:Hret; try discriminate.
        inversion Hgen; subst cns st'.
        inversion Hwc as [| |x' ck' f' Hckwc|]; subst.
        constructor.
        intros y Hin.
        unfold constraint_scope in Hin. simpl in Hin.
        rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + rewrite in_app_iff in Hin.
          destruct Hin as [Hin|Hin].
          * simpl in Hin. destruct Hin as [Heq|[]]. subst y. exact Hrst.
          * eapply assign_clk_type_scoped in Hin.
            2:{ exact Hbase. }
            2:{
              intros z Hz.
              destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_clock_free_in_vars.
            }
            exact Hin.
        + simpl in Hin. destruct Hin as [Heq|[]]. subst y.
          eapply Hreset; eauto.
      - destruct b.
        + simpl in Hgen.
          repeat monadInv.
          inversion Hwc as [| | |i' xs' ck' rst' f' es' s P' sub Hfindnode Hinputs Houtputs]; subst.
          eapply generate_constraints_scoped; eauto.
          * eapply Hscoped; eauto.
          * eapply mmap_assign_exp_type_scoped; eauto.
            eapply wc_call_args_scoped; eauto.
          * eapply assign_clk_type_scoped; eauto.
            intros z Hz.
            destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_tc_clock_free_in_vars.
          * apply st_scoped_singleton. eapply Hreset; eauto.
          * eapply mmap_find_env_scoped; eauto.
            intros y Hy. eapply wc_call_outs_scoped; eauto.
        + simpl in Hgen.
          repeat monadInv.
          inversion Hwc as [| | |i' xs' ck' rst' f' es' s P' sub Hfindnode Hinputs Houtputs]; subst.
          eapply generate_constraints_scoped; eauto.
          * eapply Hscoped; eauto.
          * eapply mmap_assign_exp_type_scoped; eauto.
            eapply wc_call_args_scoped; eauto.
          * eapply assign_clk_type_scoped; eauto.
            intros z Hz.
            destruct (Hvars z) as (ty & Henv' & Hscope); eauto using wc_tc_clock_free_in_vars.
          * apply st_scoped_singleton. exact Hrst.
          * eapply mmap_find_env_scoped; eauto.
            intros y Hy. eapply wc_call_outs_scoped; eauto.
    Qed.

    Theorem generate_trconstrs_constraints_scoped:
      forall P vars scope trs cns st st',
        secglobal_scoped G ->
        CEClo.wc_env vars ->
        Forall (Clo.wc_trconstr P vars) trs ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1, find_env x reset_env st0 = OK (ty, st1) -> In ty scope) ->
        generate_trconstrs_constraints trs st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      induction trs as [|tr trs IH]; intros cns st st'
                                          Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      - simpl in Hgen. inversion Hgen; subst. constructor.
      - inversion Hwc as [|? ? Hwc_tr Hwc_trs]; subst.
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        apply Forall_app.
        split.
        + eapply generate_trconstr_constraint_scoped; eauto.
        + eapply IH; eauto.
    Qed.

    Definition generate_trconstr_constraint (e: trconstr): Sec (list constraint) := 
      match e with
      | TcDef x ck cexp  =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | TcNext x  ck exp       =>         
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | TcCall _ [] _ _ _ _ => ret []
      | TcCall _ xs ck false f exps => 
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)

      | TcCall x0 xs ck true f exps => 
         (match find_signature f G with
          | Some n =>
              do ckty     <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp   <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp   <- mmap (fun x => find_env x env) xs;
              do rst_inst <- find_env x0 reset_env;
            generate_constraints n inptyp ckty [rst_inst] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | TcReset x rck f =>
          do rckty    <- option_to_sec (assign_clk_type env base_ty rck); (* κ''*)
          do rst_inst <- find_env x reset_env; (* κ⁰ in paper*)
          ret [([rst_ty]  ⊔ rckty, [rst_inst])]
      end.

  Fixpoint generate_trconstrs_constraints (es: list trconstr) : Sec (list constraint) :=
    match es with
    | []     => ret []
    | e::es' => 
        do c  <- generate_trconstr_constraint e;
        do cs <- generate_trconstrs_constraints es';
        ret (c++cs)
    end.

  Ltac monadInv :=
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
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.

  
  Lemma generate_tr_constraints_inv: forall (es1 es2: list trconstr)  st sconst st2,
  generate_trconstrs_constraints (es1 ++ es2) st = OK (sconst, st2) -> exists sconst1 st1 sconst2,  generate_trconstrs_constraints es1 st = OK (sconst1, st1) /\ generate_trconstrs_constraints es2 st1 = OK (sconst2, st2) /\ sconst = sconst1++sconst2.
  Proof.
    induction es1.
    - intros. simpl in H.  repeat eexists . eauto.
    - intros. simpl in H. repeat monadInv. eapply IHes1 in Hbind1. destruct Hbind1 as (es1const & es1state & es2const & [indArg1 [indArg2 Hx1]]). exists (x++es1const). exists es1state. exists es2const. split.
    2: split; auto; rewrite <- app_assoc; now subst. 
    unfold bind. destruct (generate_trconstr_constraint a st) as [(x' & x0')|] eqn:Hgen1;  inversion Hbind;
    destruct (generate_trconstrs_constraints es1 x0) eqn:Hgen2; inversion indArg1; subst; unfold ret; try congruence.
  Qed.

  Lemma generate_trconstr_constraint_shape:
    forall tr cns st st',
      call_constraints_shape G ->
      env_injective ->
      NoDup (Def.defined_tc tr) ->
      generate_trconstr_constraint tr st = OK (cns, st') ->
      exists tys,
        trconstr_targets tr = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    intros tr cns st st' Hcall Hinj Hnd Hgen.
    destruct tr as [x ck ce|x ck e|x ck f|x0 xs ck b f exps].
    - simpl in Hgen. repeat monadInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold option_to_sec in H2. destruct (assign_cexp_type env ce); try discriminate.
      unfold find_env in H4. destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      unfold ret in H4. inversion H4; subst.
      unfold ret in H5. inversion H5; subst cns st'.
      exists [xty]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - simpl in Hgen. repeat monadInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold option_to_sec in H2. destruct (assign_exp_type env e); try discriminate.
      unfold find_env in H4. destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      unfold ret in H4. inversion H4; subst.
      unfold ret in H5. inversion H5; subst cns st'.
      exists [xty]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - simpl in Hgen. repeat monadInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold find_env in H2. destruct (Env.find x reset_env) as [rst_inst|] eqn:Hfind; try discriminate.
      unfold ret in H2. inversion H2; subst.
      unfold ret in H3. inversion H3; subst cns st'.
      exists [rst_inst]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - destruct b.
      + simpl in Hgen. repeat monadInv.
        assert (Houts : st6 = st5 /\ get_mappings xs env = Some x3).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st6.
        eapply Hcall in H8; eauto.
        * destruct H8 as [Hwf Hsnd].
          exists x3. split.
          -- simpl. exact Hmapouts.
          -- split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
      + simpl in Hgen. repeat monadInv.
        assert (Houts : st4 = st3 /\ get_mappings xs env = Some x1).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st4.
        eapply Hcall in H6; eauto.
        * destruct H6 as [Hwf Hsnd].
          exists x1. split.
          -- simpl. exact Hmapouts.
          -- split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
  Qed.

  Theorem generate_trconstrs_constraints_targets:
    forall trs cns st st',
      call_constraints_shape G ->
      env_injective ->
      NoDup (Def.defined trs) ->
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      exists tys,
        trconstrs_targets trs = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys.
  Proof.
    induction trs as [|tr trs IH]; intros cns st st' Hcall Hinj Hnd Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; reflexivity.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      rewrite Def.defined_app in Hnd.
      simpl in Hnd.
      apply NoDup_app'_iff in Hnd as [Hnd1 [Hnd2 _]].
      edestruct generate_trconstr_constraint_shape
        as (tys1 & Htys1 & Hsnd1 & Hwf1); eauto.
      edestruct IH as (tys2 & Htys2 & Hsnd2); eauto.
      exists (tys1 ++ tys2). split.
      + simpl. rewrite Htys1, Htys2. reflexivity.
      + rewrite map_app, Hsnd1, Hsnd2. reflexivity.
  Qed.

  Lemma trconstr_targets_contains_defined_tc:
    forall tr x ty tys,
      trconstr_targets tr = Some tys ->
      Def.Is_defined_in_tc x tr ->
      Env.find x env = Some ty ->
      In ty tys.
  Proof.
    intros tr x ty tys Htys Hdef Hfind.
    destruct tr as [y ck ce|y ck e|y ck f|i xs ck rst f es];
      inversion Hdef; subst; simpl in Htys.
    - destruct (Env.find y env) as [yty|] eqn:Hy; try discriminate.
      inversion Htys; subst tys. rewrite Hfind in Hy. inversion Hy; subst. simpl. auto.
    - destruct (Env.find y env) as [yty|] eqn:Hy; try discriminate.
      inversion Htys; subst tys. rewrite Hfind in Hy. inversion Hy; subst. simpl. auto.
    - eapply get_mappings_in; eauto.
    - inversion H.
  Qed.

  Lemma trconstrs_targets_contains_defined:
    forall trs x ty tys,
      trconstrs_targets trs = Some tys ->
      Def.Is_defined_in x trs ->
      Env.find x env = Some ty ->
      In ty tys.
  Proof.
    induction trs as [|tr trs IH]; intros x ty tys Htys Hdef Hfind.
    - inversion Hdef.
    - simpl in Htys.
      destruct (trconstr_targets tr) as [tys1|] eqn:Hty1; try discriminate.
      destruct (trconstrs_targets trs) as [tys2|] eqn:Hty2; try discriminate.
      inversion Htys; subst tys.
      inversion Hdef as [x' tr' Hdefhd|x' tr' trs' Hdeftl]; subst.
      + apply in_or_app. left.
        eapply trconstr_targets_contains_defined_tc; eauto.
      + apply in_or_app. right.
        eapply IH; eauto.
  Qed.

  Lemma trconstrs_targets_contains_reset_ids':
    forall trs acc rids st reset_env rids' st' tys ty,
      generate_reset_env' trs acc rids st = OK ((reset_env, rids'), st') ->
      trconstrs_targets trs = Some tys ->
      In ty rids' ->
      In ty rids \/ In ty tys.
  Proof.
    induction trs as [|tr trs IH]; intros acc rids st reset_env rids' st' tys ty Hgen Htys Hin.
    - simpl in Hgen. inversion Hgen; subst reset_env rids' st'.
      simpl in Htys. inversion Htys; subst tys. auto.
    - simpl in Htys.
      destruct (trconstr_targets tr) as [tys1|] eqn:Hty1; try discriminate.
      destruct (trconstrs_targets trs) as [tys2|] eqn:Hty2; try discriminate.
      inversion Htys; subst tys.
      destruct tr as [x ck ce|x ck e|x ck f|x xs ck b f exps].
      1,2,4: simpl in Hgen; specialize (IH _ _ _ _ _ _ _ _ Hgen Hty2 Hin); tauto.
      simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & rst_inst & st1 & Hstep & Hrec).
      assert (Hself : Env.find x acc1 = Some rst_inst).
      { eapply fresh_reset_insert_find_self; eauto. }
      assert (Hpres : Env.find x reset_env = Some rst_inst).
      { eapply generate_reset_env'_preserves_find; eauto. }
      simpl in Hty1. rewrite Hpres in Hty1. inversion Hty1; subst tys1.
      specialize (IH _ (rids ++ [rst_inst]) _ _ _ _ _ _ Hrec Hty2 Hin).
      destruct IH as [Hin_old|Hin_tail].
      + apply in_app_iff in Hin_old.
        destruct Hin_old as [Hin_old|Hin_old].
        * now left.
        * simpl in Hin_old. destruct Hin_old as [Heq|[]]. subst ty.
          right. apply in_or_app. left. simpl. auto.
      + right. apply in_or_app. right. exact Hin_tail.
  Qed.

  Lemma trconstrs_targets_contains_reset_ids:
    forall trs reset_env rids st' tys ty,
      generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
      trconstrs_targets trs = Some tys ->
      In ty rids ->
      In ty tys.
  Proof.
    intros trs reset_env rids st' tys ty Hgen Htys Hin.
    unfold generate_reset_env in Hgen.
    edestruct trconstrs_targets_contains_reset_ids'
      as [Hin_init|Hin_targets]; eauto.
    - contradiction.
    - exact Hin_targets.
  Qed.
    


  End SECTRCONSTRTYPING.


  Section SECSYSTYPING.
    Variable G: secglobal.

    (* Legacy self-contained system-signature generation. *)
    Definition generate_system_signature (n: system): res signature :=
      match  (do (env_in,  inp)    <- insert_vars (List.map fst (n.(SynStc.s_in))) (Env.empty _);
              do (env_out, out)    <- insert_vars (List.map fst n.(SynStc.s_out)) env_in;
              do (env, locals)     <- insert_vars (List.map fst n.(SynStc.s_vars)) env_out;
              do ck_id             <- fresh_ident;
              do rst_id            <- fresh_ident;
              do (reset_env, rids) <- generate_reset_env n.(SynStc.s_tcs);
              do constraints'      <- generate_trconstrs_constraints G env reset_env ck_id rst_id (n.(SynStc.s_tcs));
              ret (SynStc.s_name n, inp, out, rst_id, ck_id, simplify constraints' (locals ++ rids))) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints),_) => 
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.   

    (* Environment-driven system-signature generation used in the translation
       preservation proofs. The main STC-specific addition is the separate
       reset-instance environment threaded through [generate_reset_env]. *)
    Definition generate_sys_signature (n: system) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(SynStc.s_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(SynStc.s_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(SynStc.s_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(SynStc.s_vars)) env);
              do lasts <- option_to_sec (get_mappings_from_node (n.(SynStc.s_lasts)) env);
              do (reset_env, rids) <- generate_reset_env n.(SynStc.s_tcs);
              do constraints' <- generate_trconstrs_constraints G env reset_env clk_type rst_type (n.(SynStc.s_tcs));
              ret (inp, out, rst_type, clk_type,
                   simplify constraints' (hidden_sys_vars locals lasts rids), env)) init_state with
      | Error e => Error e
      | OK ((inp, out, rst_id, ck_id, constraints, env),_) => 
          OK {| s_name  := SynStc.s_name n;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.  

    Lemma system_var_defined_in_tcs:
      forall s x,
        In x (map fst s.(SynStc.s_vars)) ->
        Def.Is_defined_in x s.(SynStc.s_tcs).
    Proof.
      intros s x Hin.
      assert (Hinvars : In x (map fst s.(SynStc.s_vars) ++ map fst s.(SynStc.s_out))).
      { apply in_or_app. left. exact Hin. }
      apply Def.Is_variable_in_Is_defined_in.
      apply Var.Is_variable_in_variables.
      rewrite <- s.(SynStc.s_vars_out_in_tcs).
      exact Hinvars.
    Qed.

    Lemma system_last_defined_in_tcs:
      forall s x,
        In x (map fst s.(SynStc.s_lasts)) ->
        Def.Is_defined_in x s.(SynStc.s_tcs).
    Proof.
      intros s x Hin.
      apply Def.Is_defined_Is_variable_Is_last_in.
      right.
      apply Last.lasts_of_In.
      rewrite <- s.(SynStc.s_lasts_in_tcs).
      exact Hin.
    Qed.

    Theorem generate_sys_signature_scoped:
      forall P s env aux_names sig,
        secglobal_scoped G ->
        call_constraints_shape G ->
        env_injective env ->
        Clo.wc_system P s ->
        generate_sys_signature s env aux_names = OK sig ->
        signature_scoped sig.
    Proof.
      intros P s env aux_names sig
             Hscoped Hcallshape Hinj Hwc Hsig.
      unfold generate_sys_signature in Hsig.
      remember
        (do (clk_id, rst_id) <- option_to_sec (get_node_aux (s.(SynStc.s_name)) aux_names);
         do clk_type <- option_to_sec (Env.find clk_id env);
         do rst_type <- option_to_sec (Env.find rst_id env);
         do inp <- option_to_sec (get_mappings_from_node (s.(SynStc.s_in)) env);
         do out <- option_to_sec (get_mappings_from_node (s.(SynStc.s_out)) env);
         do locals <- option_to_sec (get_mappings_from_node (s.(SynStc.s_vars)) env);
         do lasts <- option_to_sec (get_mappings_from_node (s.(SynStc.s_lasts)) env);
         do (reset_env, rids) <- generate_reset_env s.(SynStc.s_tcs);
         do constraints' <- generate_trconstrs_constraints G env reset_env clk_type rst_type (s.(SynStc.s_tcs));
         ret (inp, out, rst_type, clk_type,
              simplify constraints' (hidden_sys_vars locals lasts rids), env))
        init_state as gen eqn:Hgen.
      destruct gen as [[[packed env0] st0]|]; try discriminate.
      destruct packed as [packed hidden_constraints].
      destruct packed as [packed packed_clk_type].
      destruct packed as [packed packed_rst_type].
      destruct packed as [packed_out packed_hidden].
      inversion Hsig; subst sig; clear Hsig.
      eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
      eapply sec_bind_inv in Hgen as (clk_type' & st_clk & Hclk & Hgen).
      eapply sec_bind_inv in Hgen as (rst_type' & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
      eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
      eapply sec_bind_inv in Hgen as (lasts & st_lasts & Hlasts & Hgen).
      eapply sec_bind2_inv in Hgen as (reset_env & rids & st_reset & Hresetenv & Hgen).
      eapply sec_bind_inv in Hgen as (raw & st_raw & Hraw & Hret).
      unfold option_to_sec in Haux.
      destruct (get_node_aux (s.(SynStc.s_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
      inversion Haux; subst clk_id0 rst_id0 st_aux.
      unfold option_to_sec in Hclk.
      destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
      inversion Hclk; subst clk_type0 st_clk.
      unfold option_to_sec in Hrst.
      destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
      inversion Hrst; subst rst_type0 st_rst.
      unfold option_to_sec in Hinp.
      destruct (get_mappings_from_node (s.(SynStc.s_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
      inversion Hinp; subst inp0 st_inp.
      unfold option_to_sec in Hout.
      destruct (get_mappings_from_node (s.(SynStc.s_out)) env) as [out0|] eqn:Hout0; try discriminate.
      inversion Hout; subst out0 st_out.
      unfold option_to_sec in Hlocals.
      destruct (get_mappings_from_node (s.(SynStc.s_vars)) env) as [locals0|] eqn:Hlocals0; try discriminate.
      inversion Hlocals; subst locals0 st_locals.
      unfold option_to_sec in Hlasts.
      destruct (get_mappings_from_node (s.(SynStc.s_lasts)) env) as [lasts0|] eqn:Hlasts0; try discriminate.
      inversion Hlasts; subst lasts0 st_lasts.
      unfold ret in Hret.
      inversion Hret; subst packed packed_out packed_hidden packed_rst_type packed_clk_type hidden_constraints env0 st0.
      edestruct generate_trconstrs_constraints_targets
        as (tys & Htys & Hsnd); eauto using Def.s_nodup_defined.
      destruct Hwc as (_ & _ & Henvvars & Hwtcs).
      unfold signature_scoped, signature_scope.
      eapply simplify_scoped with (ds := hidden_sys_vars locals lasts rids).
      - apply NoDup_nodup.
      - eapply generate_trconstrs_constraints_scoped
          with (P := P)
               (vars := idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
                           ++ idck s.(SynStc.s_lasts)); eauto.
        + intros x Hmem.
          apply InMembers_app in Hmem.
          destruct Hmem as [Hin|Hin].
          * apply InMembers_idck in Hin.
            apply InMembers_app in Hin.
            destruct Hin as [Hin|Hin].
            -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp0) as (ty & Hfind & Hscope).
               exists ty. split; [exact Hfind|].
               repeat rewrite in_app_iff. now left.
            -- apply InMembers_app in Hin.
               destruct Hin as [Hin|Hin].
               ++ destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals0) as (ty & Hfind & Hscope).
                  exists ty. split; [exact Hfind|].
                  repeat rewrite in_app_iff. right; right; right; left.
                  rewrite nodup_In. apply in_or_app. left. exact Hscope.
               ++ destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout0) as (ty & Hfind & Hscope).
                  exists ty. split; [exact Hfind|].
                  repeat rewrite in_app_iff. now right.
          * apply InMembers_idck in Hin.
            destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlasts0) as (ty & Hfind & Hscope).
            exists ty. split; [exact Hfind|].
            repeat rewrite in_app_iff. right; right; right; left.
            rewrite nodup_In. apply in_or_app. right. apply in_or_app. left. exact Hscope.
        + repeat rewrite in_app_iff. now right; right; left.
        + repeat rewrite in_app_iff. now right; right; right; left.
        + intros x ty st1 st2 Hfind.
          apply generate_reset_env_find_in with (trs := s.(SynStc.s_tcs)) in Hfind as Hinrid; eauto.
          repeat rewrite in_app_iff. right; right; right; left.
          rewrite nodup_In. apply in_or_app. right. apply in_or_app. right. exact Hinrid.
      - intros d Hd.
        rewrite nodup_In in Hd.
        apply in_app_iff in Hd.
        destruct Hd as [Hd|Hd].
        + apply in_app_iff in Hd.
          destruct Hd as [Hd|Hd].
          * destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals0 Hd)
              as (x & a & Hinx & Hfindx).
            assert (Hdefx : Def.Is_defined_in x s.(SynStc.s_tcs)).
            { eapply system_var_defined_in_tcs.
              now apply in_map with (f := fst) in Hinx. }
            eapply trconstrs_targets_contains_defined in Hdefx; eauto.
            rewrite Hsnd. apply in_map_iff. eexists. split; [reflexivity|exact Hdefx].
          * destruct (get_mappings_from_node_In _ _ _ _ _ Hlasts0 Hd)
              as (x & a & Hinx & Hfindx).
            assert (Hdefx : Def.Is_defined_in x s.(SynStc.s_tcs)).
            { eapply system_last_defined_in_tcs.
              now apply in_map with (f := fst) in Hinx. }
            eapply trconstrs_targets_contains_defined in Hdefx; eauto.
            rewrite Hsnd. apply in_map_iff. eexists. split; [reflexivity|exact Hdefx].
        + eapply trconstrs_targets_contains_reset_ids in Hd; eauto.
          rewrite Hsnd. apply in_map_iff. eexists. split; [reflexivity|exact Hd].
    Qed.
  End SECSYSTYPING.

  Section SECPROGRAMTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_sys_signatures' (acc: list signature) (sys_list: program) (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_sys_signature acc n env aux_names;
        generate_all_sys_signatures' (sig::acc) ns env aux_names
      end.
    Definition generate_all_sys_signatures (sys_list: program) (env: Env.t ident) (aux_names: list node_aux_names): res (list signature) :=
      generate_all_sys_signatures' [] sys_list env aux_names.

    (** Global scopedness for generated STC signatures.

        This is the STC-side analogue of the NLustre theorem in
        [SecNLusTyping.v]. The proof structure is identical:

        1. [wc_program] gives the local [wc_system] fact for the current head
           system.
        2. [generate_sys_signature_scoped] proves that the freshly generated
           head signature only mentions visible interface variables.
        3. [secglobal_scoped_cons] extends the accumulator invariant.
        4. Induction lifts the result to the entire generated STC signature
           list.

        This keeps the STC signature-scopedness argument self-contained in the
        STC typing layer instead of rebuilding it ad hoc in the translation
        development. *)
    Theorem generate_all_sys_signatures_scoped':
      forall systems acc env aux_names G,
        Clo.wc_program systems ->
        secglobal_scoped acc ->
        (forall G1, call_constraints_shape G1) ->
        env_injective env ->
        generate_all_sys_signatures' acc systems env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      induction systems as [|s systems IH]; intros acc env aux_names G
                                                   Hwc Hacc Hcallshape Hinj Hgen.
      - simpl in Hgen. inversion Hgen; subst. exact Hacc.
      - inversion Hwc as [|s' systems' Hwc_tail Hwc_head]; subst s' systems'.
        simpl in Hgen.
        destruct (generate_sys_signature acc s env aux_names) as [sig|] eqn:Hsig;
          try discriminate.
        destruct (generate_all_sys_signatures' (sig :: acc) systems env aux_names) as [G'|] eqn:Htl;
          try discriminate.
        inversion Hgen; subst G'. clear Hgen.
        eapply IH; eauto.
        eapply secglobal_scoped_cons; eauto.
        eapply generate_sys_signature_scoped; eauto.
    Qed.

    Corollary generate_all_sys_signatures_scoped:
      forall systems env aux_names G,
        Clo.wc_program systems ->
        (forall G1, call_constraints_shape G1) ->
        env_injective env ->
        generate_all_sys_signatures systems env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros systems env aux_names G Hwc Hcallshape Hinj Hgen.
      unfold generate_all_sys_signatures in Hgen.
      eapply generate_all_sys_signatures_scoped'; eauto.
      apply secglobal_scoped_nil.
    Qed.


    Fixpoint generate_signatures' (acc: list signature) (sys_list: program): res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_system_signature acc n;
        generate_signatures' (sig::acc) ns
      end.

    Definition generate_signatures (sys_list: program) := generate_signatures' [] sys_list.

  End SECPROGRAMTYPING.
End SECSTCTYPING.

Module SecSTCTyping  
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX Op)
  (SynStc: STCSYNTAX Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING.

Include SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING.


End SecSTCTyping.
