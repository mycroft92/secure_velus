
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

From Coq Require Import String. (*Required for Errors *)
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
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).

  Module CEIsF := CEIsFreeFun Ids Op CESyn.
  Module CEClo := CEClockingFun Ids Op CESyn.
  Module Ord := NLOrderedFun Ids Op CESyn SynNL.
  Module Mem := MemoriesFun Ids Op CESyn SynNL.
  Module IsD := IsDefinedFun Ids Op CESyn SynNL Mem.
  Module IsF := IsFreeFun Ids Op CESyn SynNL CEIsF.
  Module Clo := NLClockingFun Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo.

  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x'
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  (** NLustre equation typing in the shared naming environment. *)
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
          ret [(ckty ⊔ expty, [xty])]
      | EqFby x  ck _ exp       => 
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
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

  (** Structural well-formedness of raw NLustre constraints.

      This is the source-side fact needed later by
      [SecTypes.simplify_complete].  The theorem is stated in two layers:

      - a shape theorem for one equation, saying that its generated
        constraints are indexed exactly by the mapped variables it defines;
      - a list theorem that lifts the result to a whole equation list using
        [NoDup (vars_defined eqs)] from the NLustre syntax layer.

      The [EqApp] case is isolated behind a call-instantiation hypothesis.
      That separation is intentional: the NLustre argument itself only needs
      the standard “variables are defined at most once” property, while the
      call case depends on separate metatheory for [generate_constraints]. *)

  Definition env_injective : Prop :=
    forall x y tx ty,
      Env.find x env = Some tx ->
      Env.find y env = Some ty ->
      tx = ty ->
      x = y.

  (* [vars_env_scoped vars scope] says that every NLustre variable listed in
     [vars] is mapped by the shared environment to a security identifier that
     lies in [scope].  The scopedness proofs below use this to bridge from the
     source-language clocking environment to the symbolic-type scope used by
     the generated constraints. *)
  Definition vars_env_scoped {A: Type} (vars: list (ident * A)) (scope: list ident) : Prop :=
    forall x,
      InMembers x vars ->
      exists ty, Env.find x env = Some ty /\ In ty scope.

  (** Scopedness of the expression/clock type assigners.

      These lemmas are the local “frontend” side of the later signature
      scopedness theorem: whenever all free source variables are mapped inside
      a chosen symbolic scope, the symbolic type computed by [assign_*_type]
      also stays inside that scope. *)

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

  Lemma wc_call_clock_free_in_vars:
    forall P vars xs ck f les r x,
      CEClo.wc_env vars ->
      Clo.wc_equation P vars (EqApp xs ck f les r) ->
      Is_free_in_clock x ck ->
      InMembers x vars.
  Proof.
    intros P vars xs ck f les r x Henv Hwc Hfree.
    inversion Hwc as [|xs' ck' f' les' r' n sub Hfind Hins Houts Hr]; subst.
    destruct n.(n_in) as [|[xin [tin xck]] ins] eqn:Hinps.
    { simpl in n.(n_ingt0). lia. }
    inversion Hins as [|? ? ? ? Hhead Htail]; subst.
    destruct Hhead as (_ & lck & Hexp & Hinst).
    assert (Hfree' : Is_free_in_clock x lck).
    { eapply instck_free_bck; eauto. }
    assert (Hwc_lck : CEClo.wc_clock vars lck).
    { eapply CEClo.wc_clock_exp; eauto. }
    eapply wc_clock_free_in_vars; eauto.
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

  (** Call-site scope transport.

      [EqApp] is the only NLustre case where the generated constraints come
      from an already stored callee signature rather than directly from the
      current equation.  The two lemmas below extract exactly the caller-side
      information needed by [generate_constraints_scoped]:

      - actual input expressions are scoped because their free variables live
        in the current node clocking environment;
      - actual output variables are scoped because the instantiated call-output
        relation points back into that same environment. *)
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

  Lemma generate_eqn_constraint_scoped:
    forall P vars scope eq cns st st',
      secglobal_scoped G ->
      CEClo.wc_env vars ->
      Clo.wc_equation P vars eq ->
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
      destruct (option_to_sec (assign_clk_type env base_ty ck) st) as [[ckty st1]|] eqn:Hck; try discriminate.
      destruct (option_to_sec (assign_cexp_type env ce) st1) as [[expty st2]|] eqn:Hexp; try discriminate.
      destruct (find_env x env st2) as [[xty st3]|] eqn:Hfind; try discriminate.
      destruct (ret [(ckty ⊔ expty, [xty])] st3) as [[cns' st4]|] eqn:Hret; try discriminate.
      inversion Hgen; subst cns st'.
      inversion Hwc as [x' ck' ce' Hx Hce| |]; subst.
      constructor.
      intros y Hin.
      unfold constraint_scope in Hin. simpl in Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + eapply assign_clk_type_scoped in Hin.
        2:{
          exact Hbase.
        }
        2:{
          intros z Hz.
          destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_clock_free_in_vars, CEClo.wc_clock_cexp.
        }
        exact Hin.
      + rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        * eapply assign_cexp_type_scoped in Hin.
          2:{
            intros z Hz.
            destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_cexp_free_in_vars.
          }
          exact Hin.
        * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
          eapply find_env_in_scope with (A := clock) (ann := ck); eauto.
    - inversion Hwc as [|xs' ck' f' exps' r' n sub Hfindnode Hinputs Houtputs Hreset]; subst.
      destruct r as [[rx rck]|].
      + simpl in Hgen. repeat secInv.
        eapply generate_constraints_scoped; eauto.
        * eapply Hscoped; eauto.
        * eapply mmap_assign_exp_type_scoped; eauto.
          eapply wc_call_args_scoped; eauto.
        * eapply assign_clk_type_scoped; eauto.
          intros z Hz.
          destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_call_clock_free_in_vars.
        * apply st_scoped_singleton.
          eapply find_env_in_scope with (A := unit) (ann := (rx, rck)); eauto.
          now apply Hreset.
        * eapply mmap_find_env_scoped; eauto.
          intros y Hy. eapply wc_call_outs_scoped; eauto.
      + simpl in Hgen. repeat secInv.
        eapply generate_constraints_scoped; eauto.
        * eapply Hscoped; eauto.
        * eapply mmap_assign_exp_type_scoped; eauto.
          eapply wc_call_args_scoped; eauto.
        * eapply assign_clk_type_scoped; eauto.
          intros z Hz.
          destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_call_clock_free_in_vars.
        * apply st_scoped_singleton. exact Hrst.
        * eapply mmap_find_env_scoped; eauto.
          intros y Hy. eapply wc_call_outs_scoped; eauto.
    - simpl in Hgen.
      destruct (option_to_sec (assign_clk_type env base_ty ck) st) as [[ckty st1]|] eqn:Hck; try discriminate.
      destruct (option_to_sec (assign_exp_type env exp) st1) as [[expty st2]|] eqn:Hexp; try discriminate.
      destruct (find_env x env st2) as [[xty st3]|] eqn:Hfind; try discriminate.
      destruct (ret [(ckty ⊔ expty, [xty])] st3) as [[cns' st4]|] eqn:Hret; try discriminate.
      inversion Hgen; subst cns st'.
      inversion Hwc as [| |x' ck' v exp' Hx Hexpwc]; subst.
      constructor.
      intros y Hin.
      unfold constraint_scope in Hin. simpl in Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + eapply assign_clk_type_scoped in Hin.
        2:{ exact Hbase. }
        2:{
          intros z Hz.
          destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_clock_free_in_vars, CEClo.wc_clock_exp.
        }
        exact Hin.
      + rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        * eapply assign_exp_type_scoped in Hin.
          2:{
            intros z Hz.
            destruct (Hvars z) as (ty & Henv & Hscope); eauto using wc_exp_free_in_vars.
          }
          exact Hin.
        * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
          eapply find_env_in_scope with (A := clock) (ann := ck); eauto.
  Qed.

  Theorem generate_eqns_constraints_scoped:
    forall P vars scope eqs cns st st',
      secglobal_scoped G ->
      CEClo.wc_env vars ->
      Forall (Clo.wc_equation P vars) eqs ->
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
      unfold ret in Hret. inversion Hret; subst cns st'.
      apply Forall_app.
      split.
      + eapply generate_eqn_constraint_scoped; eauto.
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
      rewrite (IH ys txs' tys Htail Hys).
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
            + inversion Heq; subst yty. exists y. split; [left; reflexivity|exact Hyfind].
            + specialize (IHys Hys Hin'') as (z & Hinz & Hzfind).
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

  Lemma generate_eqn_constraint_shape:
    forall eq cns st st',
      call_constraints_shape G ->
      env_injective ->
      NoDup (var_defined eq) ->
      generate_eqn_constraint eq st = OK (cns, st') ->
      exists tys,
        get_mappings (var_defined eq) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    intros eq cns st st' Hcall Hinj Hnd Hgen.
    destruct eq as [x ck ce|xs ck f exps r|x ck c0 exp].
    - simpl in Hgen. repeat secInv.
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
    - destruct r as [[rx rck]|].
      + simpl in Hgen. repeat secInv.
        unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
        unfold find_env in H2. destruct (Env.find rx env) as [rty|] eqn:Hrfind; try discriminate.
        unfold ret in H2. inversion H2; subst.
        unfold option_to_sec in H4. destruct (assign_clk_type env rst_ty rck); try discriminate.
        assert (Houts : st6 = st5 /\ get_mappings xs env = Some x3).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st6.
        eapply Hcall in H8; eauto.
        * destruct H8 as [Hwf Hsnd].
          exists x3. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
      + simpl in Hgen. repeat secInv.
        unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
        assert (Houts : st4 = st3 /\ get_mappings xs env = Some x1).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st4.
        eapply Hcall in H6; eauto.
        * destruct H6 as [Hwf Hsnd].
          exists x1. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
    - simpl in Hgen. repeat secInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold option_to_sec in H2. destruct (assign_exp_type env exp); try discriminate.
      unfold find_env in H4. destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      unfold ret in H4. inversion H4; subst.
      unfold ret in H5. inversion H5; subst cns st'.
      exists [xty]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
  Qed.

  Theorem generate_eqns_constraints_shape:
    forall eqs cns st st',
      call_constraints_shape G ->
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      exists tys,
        get_mappings (vars_defined eqs) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    induction eqs as [|eq eqs IH]; intros cns st st' Hcall Hinj Hnd Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; [reflexivity|].
      split; [reflexivity|].
      unfold wf_constraints. split; constructor.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Heq & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Heqs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      assert (Hndsplit : NoDup (var_defined eq ++ vars_defined eqs)).
      { simpl in Hnd. exact Hnd. }
      apply NoDup_app'_iff in Hndsplit as [Hnd1 [Hnd2 Hdisj]].
      edestruct generate_eqn_constraint_shape as (tys1 & Hmap1 & Hsnd1 & Hwf1); eauto.
      edestruct IH as (tys2 & Hmap2 & Hsnd2 & Hwf2); eauto.
      exists (tys1 ++ tys2). split.
      + simpl. eapply get_mappings_app; eauto.
      + split.
        * rewrite map_app, Hsnd1, Hsnd2. reflexivity.
        * unfold wf_constraints in *.
          destruct Hwf1 as [Hndc1 Hfor1].
          destruct Hwf2 as [Hndc2 Hfor2].
          split.
          -- rewrite map_app, Hsnd1, Hsnd2.
             eapply get_mappings_nodup; eauto.
             simpl. exact Hnd.
          -- rewrite Forall_app. split; auto.
  Qed.

  Corollary generate_eqns_constraints_wf:
    forall eqs cns st st',
      call_constraints_shape G ->
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      wf_constraints cns.
  Proof.
    intros eqs cns st st' Hcall Hinj Hnd Hgen.
    edestruct generate_eqns_constraints_shape as (? & ? & ? & Hwf); eauto.
  Qed.


  End SECEQNTYPING.
 
  Section SECNODETYPING.
    Variable G: secglobal.

    (** Node-level raw well-formedness.

        This is the NLustre well-formedness fact used later by the translation
        proof.  The crucial source-side premise is not an ad hoc SIF property:
        it is the standard NLustre invariant [NoDup_var_defined_n_eqs], which
        follows from the node record field [n_defd].  In other words, once the
        call-instantiation layer is known to preserve the shape of callee
        constraints, the enclosing node contributes exactly the expected
        “every variable is defined once” argument from the paper. *)
    Corollary generate_node_eqns_constraints_wf:
      forall n env base_ty rst_ty raw st st',
        call_constraints_shape G ->
        env_injective env ->
        generate_eqns_constraints G env base_ty rst_ty n.(n_eqs) st = OK (raw, st') ->
        wf_constraints raw.
    Proof.
      intros n env base_ty rst_ty raw st st' Hcall Hinj Hraw.
      eapply generate_eqns_constraints_wf; eauto.
      apply NoDup_var_defined_n_eqs.
    Qed.

    (* Legacy self-contained signature generation, kept for comparison with the
       newer environment-driven formulation below. *)
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

      (* Environment-driven signature generation used by the translation
         preservation development. The shared [env] and [aux_names] fix the
         interface/local security identifiers ahead of time. *)
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

      (** Signature scopedness for generated NLustre nodes.

          The proof follows the implementation pipeline directly:

          1. [generate_eqns_constraints_scoped] gives raw scopedness of the
             equation-generated constraints, using source [wc_node] plus the
             scopedness invariant on already-generated callee signatures.
          2. [generate_eqns_constraints_shape] supplies the “locals are defined
             by singleton RHS constraints” side-condition required by
             [simplify_scoped].
          3. [simplify_scoped] removes the local variables from the visible
             scope, yielding exactly [signature_scoped].

          This theorem is the node-typing counterpart of the bridge theorem
          later used by the translation-preservation file. *)
      Theorem generate_node_sig_scoped:
        forall P n env aux_names sig,
          secglobal_scoped G ->
          call_constraints_shape G ->
          env_injective env ->
          Clo.wc_node P n ->
          generate_node_sig n env aux_names = OK sig ->
          signature_scoped sig.
      Proof.
        intros P n env aux_names sig
               Hscoped Hcallshape Hinj Hwc Hsig.
        unfold generate_node_sig in Hsig.
        remember
          (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(n_name)) aux_names);
           do clk_type <- option_to_sec (Env.find clk_id env);
           do rst_type <- option_to_sec (Env.find rst_id env);
           do inp <- option_to_sec (get_mappings_from_node (n.(n_in)) env);
           do out <- option_to_sec (get_mappings_from_node (n.(n_out)) env);
           do locals <- option_to_sec (get_mappings_from_node (n.(n_vars)) env);
           do constraints' <- generate_eqns_constraints G env clk_type rst_type (n.(n_eqs));
           ret (n_name n, inp, out, rst_type, clk_type, simplify constraints' locals, env))
          init_state as gen eqn:Hgen.
        destruct gen as [[[packed env0] st0]|]; try discriminate.
        destruct packed as [[[[[[name inp] out] rst_type] clk_type] constraints] env1].
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
        - eapply get_mappings_nodup; eauto.
          + apply fst_NoDupMembers.
            eapply NoDupMembers_app_r, NoDupMembers_app_l.
            exact n.(n_nodup).
          + eapply get_mappings_from_node_eq; eauto.
        - eapply generate_eqns_constraints_scoped; eauto.
          + inversion Hwc as (_ & _ & Henv & Heqs).
            exact Henv.
          + inversion Hwc as (_ & _ & _ & Heqs).
            exact Heqs.
          + intros x Hmem.
            apply InMembers_idck in Hmem.
            apply InMembers_app in Hmem.
            destruct Hmem as [Hin|Hin].
            * destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp0) as (ty & Hfind & Hin').
              exists ty. split; [exact Hfind|].
              repeat rewrite in_app_iff. now left.
            * apply InMembers_app in Hin.
              destruct Hin as [Hin|Hin].
              -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals0) as (ty & Hfind & Hin').
                 exists ty. split; [exact Hfind|].
                 repeat rewrite in_app_iff. now right; left.
              -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout0) as (ty & Hfind & Hin').
                 exists ty. split; [exact Hfind|].
                 repeat rewrite in_app_iff. now right; right; left.
          + repeat rewrite in_app_iff. now right; right; right; left.
          + repeat rewrite in_app_iff. now right; right; right; right; left.
        - intros d Hd.
          apply in_app_iff in Hd.
          destruct Hd as [Hd|[]].
          edestruct get_mappings_from_node_In as (x & a & Hinvar & Hfindx); eauto.
          assert (Hdefx : In x (vars_defined n.(n_eqs))).
          { eapply IsD.node_variable_defined_in_eqs.
            eapply fst_InMembers. exact Hinvar. }
          edestruct generate_eqns_constraints_shape
            as (tys & Hmapdefs & Hsnd & Hwf); eauto.
          2: apply NoDup_var_defined_n_eqs.
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

    (** Global scopedness for generated NLustre signatures.

        The node theorem [generate_node_sig_scoped] is the paper-facing local
        result: one generated NLustre signature only mentions its visible
        interface when its source node is well clocked.  The theorem below is
        the list-level lifting used later by the translation-preservation
        development.

        Proof flow:
        1. [wc_global] supplies the standard [wc_node] fact for the current
           head node.
        2. [generate_node_sig_scoped] gives scopedness of the freshly generated
           head signature from that local clocking fact.
        3. [secglobal_scoped_cons] extends the accumulator invariant.
        4. Induction lifts the result to the full generated signature list.

        This is the NLustre-side modular analogue of the paper's reasoning that
        already-typed callees provide well-scoped assumptions for the next node
        in the list. *)
    Theorem generate_all_signatures_scoped':
      forall nodes acc env aux_names G,
        Clo.wc_global nodes ->
        secglobal_scoped acc ->
        (forall G1, call_constraints_shape G1) ->
        env_injective env ->
        generate_all_signatures' acc nodes env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      induction nodes as [|n nodes IH]; intros acc env aux_names G
                                              Hwc Hacc Hcallshape Hinj Hgen.
      - simpl in Hgen. inversion Hgen; subst. exact Hacc.
      - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        simpl in Hgen.
        destruct (generate_node_sig acc n env aux_names) as [sig|] eqn:Hsig;
          try discriminate.
        destruct (generate_all_signatures' (sig :: acc) nodes env aux_names) as [G'|] eqn:Htl;
          try discriminate.
        inversion Hgen; subst G'. clear Hgen.
        eapply IH; eauto.
        eapply secglobal_scoped_cons; eauto.
        eapply generate_node_sig_scoped; eauto.
    Qed.

    Corollary generate_all_signatures_scoped:
      forall nodes env aux_names G,
        Clo.wc_global nodes ->
        (forall G1, call_constraints_shape G1) ->
        env_injective env ->
        generate_all_signatures nodes env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros nodes env aux_names G Hwc Hcallshape Hinj Hgen.
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
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.

Include SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.


End SecNLusTyping.
