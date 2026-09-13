(** Symbolic security typing for unrestricted Lustre.

    The \nlustre generator of [SecNLusTyping.v] gives an expression a single
    symbolic type.  Lustre needs two things more.  An expression denotes a
    *list* of flows, so a type is a list; and a node call may appear inside an
    expression, where there is no equation on which to hang the callee's
    instantiated constraints, so a type carries them itself.  Both are
    supplied by [LusTypes.v]: the type of one flow is an [LST], a symbolic
    type paired with the obligations it carries.

    The rules are those of ICTAC 2021 Figures 6--8, with three additions that
    the mechanised syntax forces and that neither that paper nor the
    \nlustre/\stc one covers: the ambient reset level is threaded throughout,
    a call may carry a reset expression, and [Earrow] is typed.

    Each case is written against the corresponding case of
    [Transcription/Tr.v], so that on the normalized fragment this generator
    and the \nlustre one emit *equal* constraints rather than merely
    satisfiability-preserving ones. *)

From Coq Require Import List.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLTYPING
  (Import Ids    : IDS)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import LSyn   : LSYNTAX  Ids Op)
  (CESyn         : CESYNTAX     Op)
  (NLSyn         : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE  Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF         : CEISFREE Ids Op CESyn)
  (CEClo         : CECLOCKING Ids Op CESyn)
  (Import SECCET : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR     : TR Ids Op OpAux LSyn CESyn NLSyn).

  Import SECMONADNotations.

  (** Minting one identifier per output flow of a nested call.  These are the
      only identifiers this generator creates.  They live in the ordinary
      [sec] namespace, so the node-level entry point must start the monad at
      the naming pass's final state; see [docs/SecLTyping.md]. *)

  Fixpoint fresh_idents (n : nat) : Sec (list ident) :=
    match n with
    | O => ret []
    | S n' => do x <- SC.fresh_ident;
              do xs <- fresh_idents n';
              ret (x :: xs)
    end.

  Section SECLEXPTYPING.

    Variable G       : secglobal.            (* callee signatures *)
    Variable env     : Env.t ident.          (* program variable -> security name *)
    Variable base_ty : ident.                (* the node's base clock *)
    Variable rst_ty  : ident.                (* the node's ambient reset level *)

    Definition single (ts : list LST) : Sec LST :=
      match ts with
      | [t] => ret t
      | _   => error (msg "security typing: expected a single flow")
      end.

    (** Componentwise join, as every rule of ICTAC Figure 7 is componentwise.
        A length mismatch is a malformed program, not a silent truncation. *)
    Fixpoint ljoin_list (ts us : list LST) : Sec (list LST) :=
      match ts, us with
      | [], [] => ret []
      | t :: ts', u :: us' =>
          do r <- ljoin_list ts' us';
          ret (ljoin t u :: r)
      | _, _ => error (msg "security typing: flow list length mismatch")
      end.

    (** Everything a list of flow types is carrying, collected. *)
    Definition carried (ts : list LST) : list constraint :=
      fold_right (fun t acc => cmerge (snd t) acc) [] ts.

    Fixpoint assign_lexp_type (e : exp) {struct e} : Sec (list LST) :=
      let assign_lexps :=
        fix go (es : list exp) : Sec (list LST) :=
          match es with
          | [] => ret []
          | e' :: es' => do t <- assign_lexp_type e';
                         do r <- go es';
                         ret (t ++ r)
          end in
      match e with
      | Econst _ => ret [lbot]

      | Evar x _ =>
          do a <- find_env x env;
          ret [lvar a]

      | Eunop _ e1 _ =>
          assign_lexp_type e1

      | Ebinop _ e1 e2 _ =>
          do t1 <- assign_lexp_type e1;
          do t2 <- assign_lexp_type e2;
          do a1 <- single t1;
          do a2 <- single t2;
          ret [ljoin a1 a2]

      | Ewhen es x _ _ =>
          do ts <- assign_lexps es;
          do g  <- find_env x env;
          ret (map (fun t => ljoin t (lvar g)) ts)

      (* [xty] (+) t (+) u, associated exactly as the CoreExpr rule
         associates it, so that the two generators agree on the nose *)
      | Emerge x ets efs _ =>
          do g  <- find_env x env;
          do ts <- assign_lexps ets;
          do us <- assign_lexps efs;
          ljoin_list (map (fun t => ljoin (lvar g) t) ts) us

      | Eite e0 ets efs _ =>
          do t0 <- assign_lexp_type e0;
          do th <- single t0;
          do ts <- assign_lexps ets;
          do us <- assign_lexps efs;
          ljoin_list (map (fun t => ljoin th t) ts) us

      | Efby e0s es _ =>
          do ts <- assign_lexps e0s;
          do us <- assign_lexps es;
          ljoin_list ts us

      | Earrow e0s es _ =>
          do ts <- assign_lexps e0s;
          do us <- assign_lexps es;
          ljoin_list ts us

      (** The call case.  The callee's stored signature is instantiated with
          the actual argument types, the call's base clock and the reset level
          reaching it; the outputs are fresh, one per result flow, because a
          nested call has no declared variable whose name it could borrow.
          Each result flow is typed by its own fresh name, refined by the
          instantiated constraints together with everything the arguments and
          the reset expression were themselves carrying.  That is
          [beta{|rho'|}] of rule (LTncall), composed with the join rule of
          Figure 5. *)
      | Eapp f es er anns =>
          do argts <- assign_lexps es;
          do rstty <- (match er with
                       | None => ret (lvar rst_ty)
                       | Some e1 =>
                           do t1 <- assign_lexp_type e1;
                           do a1 <- single t1;
                           ret (ljoin (lvar rst_ty) a1)
                       end);
          do ckty <- option_to_sec
                       (assign_clk_type env base_ty
                          (find_base_clock (LSyn.clocksof es)));
          match find_signature f G with
          | None => error (MSG "Signature not found for: " :: [CTX f])
          | Some sg =>
              do outs <- fresh_idents (List.length anns);
              do cs   <- generate_constraints sg (map fst argts) ckty
                                              (fst rstty) outs;
              let held := cmerge cs (cmerge (carried argts) (snd rstty)) in
              ret (map (fun o => (([o] : ST), held)) outs)
          end
      end.

    Definition assign_lexps (es : list exp) : Sec (list LST) :=
      (fix go (es : list exp) : Sec (list LST) :=
         match es with
         | [] => ret []
         | e' :: es' => do t <- assign_lexp_type e';
                        do r <- go es';
                        ret (t ++ r)
         end) es.


    (** * Unfolding equations

        [assign_lexp_type] recurses over [list exp] through a local [fix], so
        [simpl] cannot expose one layer of it without unfolding the whole
        recursion.  These give a proof exactly one layer, and each holds by
        [reflexivity] because the local [fix] and [assign_lexps] have the same
        body.  Same problem, and same remedy, as [norm_cs_cons]. *)

    Lemma assign_lexp_Econst : forall c,
        assign_lexp_type (Econst c) = ret [lbot].
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Evar : forall x a,
        assign_lexp_type (Evar x a) = (do t <- find_env x env; ret [lvar t]).
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Eunop : forall op e a,
        assign_lexp_type (Eunop op e a) = assign_lexp_type e.
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Ebinop : forall op e1 e2 a,
        assign_lexp_type (Ebinop op e1 e2 a)
        = (do t1 <- assign_lexp_type e1;
           do t2 <- assign_lexp_type e2;
           do a1 <- single t1;
           do a2 <- single t2;
           ret [ljoin a1 a2]).
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Ewhen : forall es x b a,
        assign_lexp_type (Ewhen es x b a)
        = (do ts <- assign_lexps es;
           do g  <- find_env x env;
           ret (map (fun t => ljoin t (lvar g)) ts)).
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Emerge : forall x ets efs a,
        assign_lexp_type (Emerge x ets efs a)
        = (do g  <- find_env x env;
           do ts <- assign_lexps ets;
           do us <- assign_lexps efs;
           ljoin_list (map (fun t => ljoin (lvar g) t) ts) us).
    Proof. reflexivity. Qed.

    Lemma assign_lexp_Eite : forall e0 ets efs a,
        assign_lexp_type (Eite e0 ets efs a)
        = (do t0 <- assign_lexp_type e0;
           do th <- single t0;
           do ts <- assign_lexps ets;
           do us <- assign_lexps efs;
           ljoin_list (map (fun t => ljoin th t) ts) us).
    Proof. reflexivity. Qed.

    Lemma assign_lexps_nil : assign_lexps [] = ret [].
    Proof. reflexivity. Qed.

    Lemma assign_lexps_cons : forall e es,
        assign_lexps (e :: es)
        = (do t <- assign_lexp_type e;
           do r <- assign_lexps es;
           ret (t ++ r)).
    Proof. reflexivity. Qed.

    (** * Leg A, expression level

        On an expression that transcribes, the two generators agree: the
        Lustre one returns the single plain type the CoreExpr one computes,
        and consumes no state -- it mints nothing, because a transcribable
        expression contains no node call. *)

    Lemma to_lexp_assign_eq : forall e le sa st,
        to_lexp e = OK le ->
        assign_exp_type env le = Some sa ->
        assign_lexp_type e st = OK ([(sa, [])], st).
    Proof.
      apply (exp_ind2 (fun e => forall le sa st,
                 to_lexp e = OK le ->
                 assign_exp_type env le = Some sa ->
                 assign_lexp_type e st = OK ([(sa, [])], st))).
      - (* Econst *)
        intros c le sa st Htr Hnl. simpl in Htr. monadInv Htr.
        simpl in Hnl. inv Hnl. reflexivity.
      - (* Evar *)
        intros x a le sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl in Hnl.
        destruct (Env.find x env) eqn:E; try discriminate. inv Hnl.
        rewrite assign_lexp_Evar. unfold find_env. now rewrite E.
      - (* Eunop *)
        intros op e a IH le sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl in Hnl.
        rewrite assign_lexp_Eunop. eauto.
      - (* Ebinop *)
        intros op e1 e2 a IH1 IH2 le sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl in Hnl.
        destruct (assign_exp_type env x) eqn:E1; try discriminate.
        destruct (assign_exp_type env x0) eqn:E2; try discriminate.
        inv Hnl. rewrite assign_lexp_Ebinop. unfold bind, ret.
        erewrite IH1 by eauto. erewrite IH2 by eauto.
        unfold single. reflexivity.
      - (* Efby: never transcribes as an expression *)
        intros e0s es a IH1 IH2 le sa st Htr Hnl. simpl in Htr. discriminate.
      - (* Earrow *)
        intros e0s es a IH1 IH2 le sa st Htr Hnl. simpl in Htr. discriminate.
      - (* Ewhen: only the singleton form transcribes *)
        intros es x b a IH le sa st Htr Hnl.
        destruct es as [|e' [|]]; destruct a as [tys ck]; simpl in Htr;
          try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr. simpl in Hnl.
        destruct (assign_exp_type env x0) eqn:E1; try discriminate.
        destruct (Env.find x env) eqn:E2; try discriminate. inv Hnl.
        rewrite assign_lexp_Ewhen, assign_lexps_cons.
        unfold bind, ret.
        inv IH. erewrite H1 by eauto.
        rewrite assign_lexps_nil. unfold ret.
        unfold find_env. rewrite E2. reflexivity.
      - (* Emerge *)
        intros x ets efs a IH1 IH2 le sa st Htr Hnl. simpl in Htr. discriminate.
      - (* Eite *)
        intros e ets efs a IH IH1 IH2 le sa st Htr Hnl. simpl in Htr.
        discriminate.
      - (* Eapp *)
        intros f es ro a IHr IH le sa st Htr Hnl. simpl in Htr. discriminate.
    Qed.

    (** * Leg A, expression level, Lustre to NLustre

        The converse of [to_lexp_assign_eq].  The preservation proof needs
        this direction: a secure Lustre node is one whose generated
        constraints are satisfied, and the NLustre node's must follow, so the
        hypothesis available is that the *Lustre* generator succeeded.  The
        forward direction no longer suffices on its own, because the Lustre
        fby rule looks up the [when] variables of an initial value that the
        NLustre rule never mentions. *)

    Lemma to_lexp_assign_rev : forall e le ts st st',
        to_lexp e = OK le ->
        assign_lexp_type e st = OK (ts, st') ->
        exists sa, ts = [(sa, [])]
                   /\ assign_exp_type env le = Some sa
                   /\ st' = st.
    Proof.
      apply (exp_ind2 (fun e => forall le ts st st',
                 to_lexp e = OK le ->
                 assign_lexp_type e st = OK (ts, st') ->
                 exists sa, ts = [(sa, [])]
                            /\ assign_exp_type env le = Some sa
                            /\ st' = st)).
      - (* Econst *)
        intros c le ts st st' Htr Hl. simpl in Htr. monadInv Htr.
        rewrite assign_lexp_Econst in Hl. unfold ret in Hl. inv Hl.
        exists []. repeat split; reflexivity.
      - (* Evar *)
        intros x a le ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        rewrite assign_lexp_Evar in Hl.
        eapply sec_bind_inv in Hl as (t & st1 & Ht & Hret).
        unfold ret in Hret. inv Hret.
        unfold find_env in Ht.
        destruct (Env.find x env) eqn:E; try discriminate.
        unfold ret in Ht. inv Ht.
        exists [t]. repeat split; simpl; try reflexivity. now rewrite E.
      - (* Eunop *)
        intros op e a IH le ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        rewrite assign_lexp_Eunop in Hl.
        destruct (IH _ _ _ _ EQ Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - (* Ebinop *)
        intros op e1 e2 a IH1 IH2 le ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        rewrite assign_lexp_Ebinop in Hl.
        eapply sec_bind_inv in Hl as (t1 & st1 & H1 & Hl).
        eapply sec_bind_inv in Hl as (t2 & st2 & H2 & Hl).
        eapply sec_bind_inv in Hl as (a1 & st3 & Ha1 & Hl).
        eapply sec_bind_inv in Hl as (a2 & st4 & Ha2 & Hret).
        unfold ret in Hret. inv Hret.
        destruct (IH1 _ _ _ _ EQ H1) as (s1 & Ht1 & Hnl1 & Hst1). subst t1 st1.
        destruct (IH2 _ _ _ _ EQ1 H2) as (s2 & Ht2 & Hnl2 & Hst2). subst t2 st2.
        unfold single, ret in Ha1. inv Ha1.
        unfold single, ret in Ha2. inv Ha2.
        exists (merge s1 s2). repeat split;
          try reflexivity;
          try (unfold ljoin; cbn [fst snd]; reflexivity);
          try (simpl; now rewrite Hnl1, Hnl2).
      - (* Efby *)
        intros e0s es a IH1 IH2 le ts st st' Htr Hl. simpl in Htr. discriminate.
      - (* Earrow *)
        intros e0s es a IH1 IH2 le ts st st' Htr Hl. simpl in Htr. discriminate.
      - (* Ewhen *)
        intros es x b a IH le ts st st' Htr Hl.
        destruct es as [|e' [|]]; destruct a as [tys ck]; simpl in Htr;
          try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr.
        rewrite assign_lexp_Ewhen in Hl.
        eapply sec_bind_inv in Hl as (ts0 & st1 & Hts0 & Hl).
        eapply sec_bind_inv in Hl as (g & st2 & Hg & Hret).
        unfold ret in Hret. inv Hret.
        rewrite assign_lexps_cons in Hts0.
        eapply sec_bind_inv in Hts0 as (t' & st3 & Ht' & Hts0).
        eapply sec_bind_inv in Hts0 as (r & st4 & Hr & Hret2).
        unfold ret in Hret2. inv Hret2.
        rewrite assign_lexps_nil in Hr. unfold ret in Hr. inv Hr.
        apply Forall_inv in IH.
        destruct (IH _ _ _ _ EQ Ht') as (s' & Hts' & Hnl' & Hst'); subst.
        unfold find_env in Hg.
        destruct (Env.find x env) eqn:E; try discriminate.
        unfold ret in Hg. inv Hg.
        exists (merge s' [g]). repeat split;
          try reflexivity;
          try (unfold ljoin, lvar; cbn [fst snd]; reflexivity);
          try (simpl; now rewrite Hnl', E).
      - (* Emerge *)
        intros x ets efs a IH1 IH2 le ts st st' Htr Hl. simpl in Htr. discriminate.
      - (* Eite *)
        intros e ets efs a IH IH1 IH2 le ts st st' Htr Hl. simpl in Htr.
        discriminate.
      - (* Eapp *)
        intros f es ro a IHr IH le ts st st' Htr Hl. simpl in Htr. discriminate.
    Qed.

    Lemma to_cexp_assign_eq : forall e ce sa st,
        to_cexp e = OK ce ->
        assign_cexp_type env ce = Some sa ->
        assign_lexp_type e st = OK ([(sa, [])], st).
    Proof.
      apply (exp_ind2 (fun e => forall ce sa st,
                 to_cexp e = OK ce ->
                 assign_cexp_type env ce = Some sa ->
                 assign_lexp_type e st = OK ([(sa, [])], st))).
      (* the forms that transcribe through [to_lexp] and sit under [Eexp].
         For the two leaves [simpl] computes [to_lexp] away, so there is no
         hypothesis left to feed the expression lemma and they are discharged
         directly. *)
      - intros c ce sa st Htr Hnl. simpl in Htr. monadInv Htr.
        simpl in Hnl. inv Hnl. reflexivity.
      - intros x a ce sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr. simpl in Hnl.
        destruct (Env.find x env) eqn:E; try discriminate. inv Hnl.
        rewrite assign_lexp_Evar. unfold find_env. now rewrite E.
      - intros op e a IH ce sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        simpl in Hnl. eapply to_lexp_assign_eq; eassumption.
      - intros op e1 e2 a IH1 IH2 ce sa st Htr Hnl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        simpl in Hnl. eapply to_lexp_assign_eq; eassumption.
      - (* Efby *)
        intros e0s es a IH1 IH2 ce sa st Htr Hnl. simpl in Htr. discriminate.
      - (* Earrow *)
        intros e0s es a IH1 IH2 ce sa st Htr Hnl. simpl in Htr. discriminate.
      - (* Ewhen *)
        intros es x b a IH ce sa st Htr Hnl. simpl in Htr. monadInv Htr.
        simpl in Hnl. eapply to_lexp_assign_eq; eassumption.
      - (* Emerge *)
        intros x ets efs a IH1 IH2 ce sa st Htr Hnl.
        destruct ets as [|et [|]]; destruct efs as [|ef [|]];
          destruct a as [tys ck]; simpl in Htr; try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr. simpl in Hnl.
        destruct (Env.find x env) eqn:Eg; try discriminate.
        destruct (assign_cexp_type env x0) eqn:E1; try discriminate.
        destruct (assign_cexp_type env x1) eqn:E2; try discriminate.
        inv Hnl.
        rewrite assign_lexp_Emerge. unfold bind, ret.
        unfold find_env. rewrite Eg.
        rewrite !assign_lexps_cons, assign_lexps_nil. unfold bind, ret.
        inv IH1. inv IH2.
        erewrite H1 by eauto. erewrite H3 by eauto.
        simpl. unfold bind, ret. reflexivity.
      - (* Eite: the scrutinee goes through to_lexp, the branches through to_cexp *)
        intros e ets efs a IH IH1 IH2 ce sa st Htr Hnl.
        destruct ets as [|et [|]]; destruct efs as [|ef [|]];
          destruct a as [tys ck]; simpl in Htr; try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr. simpl in Hnl.
        destruct (assign_exp_type env x) eqn:E0; try discriminate.
        destruct (assign_cexp_type env x0) eqn:E1; try discriminate.
        destruct (assign_cexp_type env x1) eqn:E2; try discriminate.
        inv Hnl.
        rewrite assign_lexp_Eite. unfold bind, ret.
        erewrite to_lexp_assign_eq by eassumption. unfold single.
        rewrite !assign_lexps_cons, assign_lexps_nil. unfold bind, ret.
        inv IH1. inv IH2.
        erewrite H1 by eauto. erewrite H3 by eauto.
        simpl. unfold bind, ret. reflexivity.
      - (* Eapp *)
        intros f es ro a IHr IH ce sa st Htr Hnl. simpl in Htr. discriminate.
    Qed.

    (** * Leg A, expression lists

        The call cases compare a whole argument list, so the expression
        correspondence has to be lifted.  Splitting the NLustre side's
        monadic map into a [Forall2] first keeps the two inductions apart. *)

    Lemma sec_mmap_assign_exp_Forall2 : forall les tys st st',
        SC.mmap (fun e => option_to_sec (assign_exp_type env e)) les st
        = OK (tys, st') ->
        st' = st
        /\ Forall2 (fun le t => assign_exp_type env le = Some t) les tys.
    Proof.
      induction les as [|le les IH]; intros tys st st' Hm; simpl in Hm.
      - unfold ret in Hm. inv Hm. split; [reflexivity|constructor].
      - eapply sec_bind_inv in Hm as (t & st1 & Ht & Hm).
        eapply sec_bind_inv in Hm as (tys' & st2 & Htys & Hret).
        unfold ret in Hret. inv Hret.
        unfold option_to_sec in Ht.
        destruct (assign_exp_type env le) eqn:E; try discriminate.
        unfold ret in Ht. inv Ht.
        destruct (IH _ _ _ Htys) as [Hst Hall]; subst.
        split; [reflexivity|constructor; auto].
    Qed.

    Lemma to_lexps_assign_eq : forall es les tys st,
        Errors.mmap to_lexp es = OK les ->
        Forall2 (fun le t => assign_exp_type env le = Some t) les tys ->
        assign_lexps es st = OK (map (fun t => (t, [])) tys, st).
    Proof.
      induction es as [|e es IH]; intros les tys st Htr Hall;
        simpl in Htr.
      - inv Htr. inv Hall. rewrite assign_lexps_nil. reflexivity.
      - monadInv Htr. inv Hall.
        rewrite assign_lexps_cons. unfold bind, ret.
        erewrite to_lexp_assign_eq by eassumption.
        erewrite IH by eauto. reflexivity.
    Qed.

    Lemma carried_plain : forall tys,
        carried (map (fun t => (t, [])) tys) = [].
    Proof.
      induction tys as [|t tys IH]; simpl; auto.
      unfold carried in *; simpl. now rewrite IH.
    Qed.

    Lemma map_fst_plain : forall tys,
        map fst (map (fun t : ST => (t, ([] : list constraint))) tys) = tys.
    Proof.
      induction tys as [|t tys IH]; simpl; auto. now rewrite IH.
    Qed.

    Lemma ljoin_list_single : forall t u st,
        ljoin_list [t] [u] st = OK ([ljoin t u], st).
    Proof. reflexivity. Qed.

    Lemma to_cexp_assign_rev : forall e ce ts st st',
        to_cexp e = OK ce ->
        assign_lexp_type e st = OK (ts, st') ->
        exists sa, ts = [(sa, [])]
                   /\ assign_cexp_type env ce = Some sa
                   /\ st' = st.
    Proof.
      apply (exp_ind2 (fun e => forall ce ts st st',
                 to_cexp e = OK ce ->
                 assign_lexp_type e st = OK (ts, st') ->
                 exists sa, ts = [(sa, [])]
                            /\ assign_cexp_type env ce = Some sa
                            /\ st' = st)).
      (* the five forms that transcribe through [to_lexp], under [Eexp]:
         build the [to_lexp] fact, then defer to the expression lemma *)
      - intros c ce ts st st' Htr Hl. simpl in Htr. monadInv Htr.
        assert (Hle : to_lexp (Econst c) = OK (CESyn.Econst c)) by reflexivity.
        destruct (to_lexp_assign_rev _ _ _ _ _ Hle Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - intros x a ce ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        assert (Hle : to_lexp (Evar x (ty, ck)) = OK (CESyn.Evar x ty))
          by reflexivity.
        destruct (to_lexp_assign_rev _ _ _ _ _ Hle Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - intros op e a IH ce ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        (* [monadInv] peeled only the outer [Eexp] bind, so [EQ] already *is*
           the [to_lexp] fact, though not syntactically: ascribe it *)
        assert (Hle : to_lexp (Eunop op e (ty, ck)) = OK x) by exact EQ.
        destruct (to_lexp_assign_rev _ _ _ _ _ Hle Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - intros op e1 e2 a IH1 IH2 ce ts st st' Htr Hl.
        destruct a as [ty ck]. simpl in Htr. monadInv Htr.
        assert (Hle : to_lexp (Ebinop op e1 e2 (ty, ck)) = OK x) by exact EQ.
        destruct (to_lexp_assign_rev _ _ _ _ _ Hle Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - (* Efby *)
        intros e0s es a IH1 IH2 ce ts st st' Htr Hl. simpl in Htr. discriminate.
      - (* Earrow *)
        intros e0s es a IH1 IH2 ce ts st st' Htr Hl. simpl in Htr. discriminate.
      - (* Ewhen *)
        intros es x b a IH ce ts st st' Htr Hl.
        destruct es as [|e' [|]]; destruct a as [tys ck]; simpl in Htr;
          try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr.
        assert (Hle : to_lexp (Ewhen [e'] x b ([ty], ck)) = OK x0) by exact EQ.
        destruct (to_lexp_assign_rev _ _ _ _ _ Hle Hl) as (sa & Hts & Hnl & Hst).
        exists sa. repeat split; auto.
      - (* Emerge *)
        intros x ets efs a IH1 IH2 ce ts st st' Htr Hl.
        destruct ets as [|et [|]]; destruct efs as [|ef [|]];
          destruct a as [tys ck]; simpl in Htr; try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr.
        rewrite assign_lexp_Emerge in Hl.
        eapply sec_bind_inv in Hl as (g & st1 & Hg & Hl).
        eapply sec_bind_inv in Hl as (ts1 & st2 & Hts1 & Hl).
        eapply sec_bind_inv in Hl as (us1 & st3 & Hus1 & Hl).
        unfold find_env in Hg.
        destruct (Env.find x env) eqn:Eg; try discriminate.
        unfold ret in Hg. inv Hg.
        rewrite assign_lexps_cons in Hts1.
        eapply sec_bind_inv in Hts1 as (t & sta & Ht & Hts1).
        eapply sec_bind_inv in Hts1 as (r1 & stb & Hr1 & Hr1').
        unfold ret in Hr1'. inv Hr1'.
        rewrite assign_lexps_nil in Hr1. unfold ret in Hr1. inv Hr1.
        rewrite assign_lexps_cons in Hus1.
        eapply sec_bind_inv in Hus1 as (u & stc & Hu & Hus1).
        eapply sec_bind_inv in Hus1 as (r2 & std & Hr2 & Hr2').
        unfold ret in Hr2'. inv Hr2'.
        rewrite assign_lexps_nil in Hr2. unfold ret in Hr2. inv Hr2.
        apply Forall_inv in IH1. apply Forall_inv in IH2.
        destruct (IH1 _ _ _ _ EQ Ht) as (s1 & Ht1 & Hnl1 & Hst1); subst.
        destruct (IH2 _ _ _ _ EQ1 Hu) as (s2 & Ht2 & Hnl2 & Hst2); subst.
        simpl in Hl. try unfold ret in Hl. inv Hl.
        exists (merge (merge [g] s1) s2). repeat split;
          try reflexivity;
          try (unfold ljoin, lvar; cbn [fst snd]; reflexivity);
          try (simpl; now rewrite Eg, Hnl1, Hnl2).
      - (* Eite *)
        intros e ets efs a IH IH1 IH2 ce ts st st' Htr Hl.
        destruct ets as [|et [|]]; destruct efs as [|ef [|]];
          destruct a as [tys ck]; simpl in Htr; try discriminate.
        destruct tys as [|ty [|]]; try discriminate.
        monadInv Htr.
        rewrite assign_lexp_Eite in Hl.
        eapply sec_bind_inv in Hl as (t0 & st1 & Ht0 & Hl).
        eapply sec_bind_inv in Hl as (th & st2 & Hth & Hl).
        eapply sec_bind_inv in Hl as (ts1 & st3 & Hts1 & Hl).
        eapply sec_bind_inv in Hl as (us1 & st4 & Hus1 & Hl).
        destruct (to_lexp_assign_rev _ _ _ _ _ EQ Ht0) as (s0 & Ht0' & Hnl0 & Hst0);
          subst.
        unfold single, ret in Hth. inv Hth.
        rewrite assign_lexps_cons in Hts1.
        eapply sec_bind_inv in Hts1 as (t & sta & Ht & Hts1).
        eapply sec_bind_inv in Hts1 as (r1 & stb & Hr1 & Hr1').
        unfold ret in Hr1'. inv Hr1'.
        rewrite assign_lexps_nil in Hr1. unfold ret in Hr1. inv Hr1.
        rewrite assign_lexps_cons in Hus1.
        eapply sec_bind_inv in Hus1 as (u & stc & Hu & Hus1).
        eapply sec_bind_inv in Hus1 as (r2 & std & Hr2 & Hr2').
        unfold ret in Hr2'. inv Hr2'.
        rewrite assign_lexps_nil in Hr2. unfold ret in Hr2. inv Hr2.
        apply Forall_inv in IH1. apply Forall_inv in IH2.
        destruct (IH1 _ _ _ _ EQ1 Ht) as (s1 & Ht1 & Hnl1 & Hst1); subst.
        destruct (IH2 _ _ _ _ EQ0 Hu) as (s2 & Ht2 & Hnl2 & Hst2); subst.
        simpl in Hl. try unfold ret in Hl. inv Hl.
        exists (merge (merge s0 s1) s2). repeat split;
          try reflexivity;
          try (unfold ljoin; cbn [fst snd]; reflexivity);
          try (simpl; now rewrite Hnl0, Hnl1, Hnl2).
      - (* Eapp *)
        intros f es ro a IHr IH ce ts st st' Htr Hl. simpl in Htr. discriminate.
    Qed.

    Lemma to_lexps_assign_rev : forall es les ts st st',
        Errors.mmap to_lexp es = OK les ->
        assign_lexps es st = OK (ts, st') ->
        exists tys, ts = map (fun t => (t, [])) tys
                    /\ Forall2 (fun le t => assign_exp_type env le = Some t) les tys
                    /\ st' = st.
    Proof.
      induction es as [|e es IH]; intros les ts st st' Htr Hl; simpl in Htr.
      - inv Htr. rewrite assign_lexps_nil in Hl. unfold ret in Hl. inv Hl.
        exists []. repeat split; constructor.
      - monadInv Htr.
        rewrite assign_lexps_cons in Hl.
        eapply sec_bind_inv in Hl as (t & st1 & Ht & Hl).
        eapply sec_bind_inv in Hl as (r & st2 & Hr & Hret).
        unfold ret in Hret. inv Hret.
        destruct (to_lexp_assign_rev _ _ _ _ _ EQ Ht) as (sa & Hts & Hnl & Hst);
          subst.
        destruct (IH _ _ _ _ EQ1 Hr) as (tys & Hr' & Hall & Hst'); subst.
        exists (sa :: tys). repeat split; auto.
    Qed.

    (** * Equations

        One case per shape of [to_equation], so that on the normalized
        fragment each emits exactly the constraint the NLustre generator emits
        for the transcribed equation -- in particular the call cases pass the
        *declared* output variables' security names straight to
        [generate_constraints] rather than routing them through minted names,
        which is what an equality rather than a mere refinement needs.

        The final case is the general rule (LTeq) for equations that are not
        yet normalized; the fby-initialisation and unnesting legs need it. *)

    Variable cenv : Env.t (type * clock).   (* declared clocks, as to_equation reads them *)

    Definition res_to_sec {A : Type} (r : res A) : Sec A :=
      match r with
      | OK a => ret a
      | Error e => error e
      end.

    Definition eqn_clock_type (x : ident) : Sec ST :=
      do ck <- res_to_sec (find_clock cenv x);
      option_to_sec (assign_clk_type env base_ty ck).

    (** The ambient contribution every defined variable carries: the reset
        level joined with the level of the clock it is defined on. *)
    Definition ambient (ckty : ST) : LST :=
      ljoin (lvar rst_ty) (ckty, []).

    (** The body shared by the definition and delayed-definition cases: one
        defined variable, its declared clock, and one expression.  Factoring
        it out is what lets the correspondence be proved once, uniformly in
        the expression, instead of once per syntactic form. *)
    Definition generate_ldef_constraint (x : ident) (e : exp)
      : Sec (list constraint) :=
      do ckty <- eqn_clock_type x;
      do ts   <- assign_lexp_type e;
      do t    <- single ts;
      do b    <- find_env x env;
      ret (lconstrain (ljoin (ambient ckty) t) b).

    Lemma res_to_sec_OK : forall {A : Type} (a : A) st,
        res_to_sec (OK a) st = OK (a, st).
    Proof. reflexivity. Qed.

    (** Step a bind forward given what its left-hand side computes.  Chaining
        these is how the proofs below reduce, rather than by [simpl]: a
        blanket [simpl] unfolds [SymTypes.merge] into its inner [fix] on one
        side of a goal only, and two otherwise identical sides then stop being
        syntactically equal. *)
    Lemma bind_OK : forall {A B : Type} (m : Sec A) (f : A -> Sec B) st a st1,
        m st = OK (a, st1) -> (do x <- m; f x) st = f a st1.
    Proof. intros A B m f st a st1 H. unfold bind. now rewrite H. Qed.

    Lemma eqn_clock_type_OK : forall x ck ckty st,
        find_clock cenv x = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        eqn_clock_type x st = OK (ckty, st).
    Proof.
      intros x ck ckty st Hck Hckty. unfold eqn_clock_type.
      erewrite bind_OK by (rewrite Hck; apply res_to_sec_OK).
      unfold option_to_sec. now rewrite Hckty.
    Qed.

    Lemma find_env_OK : forall x b st,
        Env.find x env = Some b -> find_env x env st = OK (b, st).
    Proof. intros x b st H. unfold find_env. now rewrite H. Qed.

    Lemma generate_ldef_constraint_eq : forall x e ck ckty sa b st,
        find_clock cenv x = OK ck ->
        assign_clk_type env base_ty ck = Some ckty ->
        assign_lexp_type e st = OK ([(sa, [])], st) ->
        Env.find x env = Some b ->
        generate_ldef_constraint x e st
        = OK ([(merge (merge [rst_ty] ckty) sa, [b])], st).
    Proof.
      intros x e ck ckty sa b st Hck Hckty He Hb.
      unfold generate_ldef_constraint.
      erewrite bind_OK by (eapply eqn_clock_type_OK; eassumption).
      erewrite bind_OK by exact He.
      erewrite bind_OK by (unfold single, ret; reflexivity).
      erewrite bind_OK by (apply find_env_OK; exact Hb).
      unfold ret, lconstrain, ljoin, ambient, lvar. cbn [fst snd].
      now rewrite !cmerge_nil.
    Qed.

    Fixpoint generate_lvars_constraints
      (xs : list ident) (bs : list ident) (ts : list LST) : Sec (list constraint) :=
      match xs, bs, ts with
      | [], [], [] => ret []
      | x :: xs', b :: bs', t :: ts' =>
          do ckty <- eqn_clock_type x;
          do rest <- generate_lvars_constraints xs' bs' ts';
          ret (lconstrain (ljoin (ambient ckty) t) b ++ rest)
      | _, _, _ => error (msg "security typing: equation arity mismatch")
      end.

    (* the binds are ordered, and the outputs looked up, exactly as the
       NLustre call case orders and looks them up *)
    Definition generate_lcall_constraint
      (xs : list ident) (f : ident) (es : list exp) (rstty : LST)
      : Sec (list constraint) :=
      match find_signature f G with
      | None => error (MSG "Signature not found for: " :: [CTX f])
      | Some sg =>
          do ckty  <- option_to_sec
                        (assign_clk_type env base_ty
                           (find_base_clock (LSyn.clocksof es)));
          do argts <- assign_lexps es;
          do outs  <- SC.mmap (fun x => find_env x env) xs;
          do cs <- generate_constraints sg (map fst argts) ckty (fst rstty) outs;
          ret (cmerge cs (cmerge (carried argts) (snd rstty)))
      end.

    (** The general rule (LTeq), for equations that are not yet normalized. *)
    Definition generate_lgen_constraint (xs : list ident) (es : list exp)
      : Sec (list constraint) :=
      do ts <- assign_lexps es;
      do bs <- option_to_sec (get_mappings xs env);
      generate_lvars_constraints xs bs ts.

    (** Nested the way [to_equation] nests -- on the expression list first,
        then on the defined variables.  Written as one flat [match] instead,
        the [[x]] patterns force Coq to split the tail of [xs], and the term
        is then stuck on any equation whose variable list is not literal.
        Nesting keeps reduction predictable, which is what the reduction
        lemmas below rely on. *)
    Definition generate_leqn_constraint (eq : equation) : Sec (list constraint) :=
      let (xs, es) := eq in
      match es with
      (** an ordinary call at the head of an equation *)
      | [Eapp f args None _] =>
          match xs with
          | [] => ret []
          | _  => generate_lcall_constraint xs f args (lvar rst_ty)
          end

      (** a reset call; the reset variable's level and the level of the clock
          it is sampled on stack onto the ambient reset, exactly as (NTrc) *)
      | [Eapp f args (Some (Evar r (_, (ckr, _)))) _] =>
          match xs with
          | [] => ret []
          | _  =>
              do rty   <- find_env r env;
              do rstck <- option_to_sec (assign_clk_type env base_ty ckr);
              generate_lcall_constraint xs f args
                (ljoin (lvar rst_ty) (merge [rty] rstck, []))
          end

      (** A delayed definition gets no case of its own.  It falls through to
          the ordinary definition below, whose expression rule joins *both*
          operands of an [Efby].  Typing only the second - which is what the
          NLustre rule (NTfb) does, legitimately, since there the initial
          value is a literal constant - would drop a real dependency here: in
          Lustre the initial value is an arbitrary expression, so [x = h fby 0]
          would be given a constraint that never mentions [h] even though
          [x]'s first value is [h]. *)

      (** an ordinary definition *)
      | [e] =>
          match xs with
          | [x] => generate_ldef_constraint x e
          | _   => generate_lgen_constraint xs es
          end

      | _ => generate_lgen_constraint xs es
      end.

    (** What a successful run of the shared definition body computed.  The
        expression's type may carry refinement obligations, and they come out
        merged alongside the ordering constraint -- that is [lconstrain]. *)
    Lemma generate_ldef_constraint_inv : forall x e cs st st',
        generate_ldef_constraint x e st = OK (cs, st') ->
        exists ck ckty sa rho b,
          find_clock cenv x = OK ck
          /\ assign_clk_type env base_ty ck = Some ckty
          /\ assign_lexp_type e st = OK ([(sa, rho)], st')
          /\ Env.find x env = Some b
          /\ cs = cmerge [(merge (merge [rst_ty] ckty) sa, [b])] rho.
    Proof.
      intros x e cs st st' H.
      unfold generate_ldef_constraint in H.
      eapply sec_bind_inv in H as (ckty & st1 & Hck & H).
      eapply sec_bind_inv in H as (ts & st2 & Hts & H).
      eapply sec_bind_inv in H as (t & st3 & Ht & H).
      eapply sec_bind_inv in H as (b & st4 & Hb & Hret).
      unfold ret in Hret. inv Hret.
      unfold eqn_clock_type in Hck.
      eapply sec_bind_inv in Hck as (ck & sta & Hck0 & Hck).
      unfold res_to_sec in Hck0.
      destruct (find_clock cenv x) eqn:Eck; try discriminate.
      unfold ret in Hck0. inv Hck0.
      unfold option_to_sec in Hck.
      destruct (assign_clk_type env base_ty ck) eqn:Eckty; try discriminate.
      unfold ret in Hck. inv Hck.
      unfold single in Ht. destruct ts as [|t0 [|]]; try discriminate.
      unfold ret in Ht. inv Ht.
      unfold find_env in Hb.
      destruct (Env.find x env) eqn:Eb; try discriminate.
      unfold ret in Hb. inv Hb.
      destruct t as [sa rho].
      exists ck, ckty, sa, rho, b.
      repeat split; auto.
      unfold lconstrain, ljoin, ambient, lvar. cbn [fst snd].
      rewrite ?cmerge_nil, ?cmerge_nil2. reflexivity.
    Qed.

    (** Reduction lemmas for the equation generator, one per shape, each by
        [reflexivity].  A proof uses these instead of reducing the [match]
        itself. *)

    Lemma gen_leqn_Econst : forall x c,
        generate_leqn_constraint ([x], [Econst c]) = generate_ldef_constraint x (Econst c).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Evar : forall x i a,
        generate_leqn_constraint ([x], [Evar i a]) = generate_ldef_constraint x (Evar i a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Eunop : forall x op e a,
        generate_leqn_constraint ([x], [Eunop op e a]) = generate_ldef_constraint x (Eunop op e a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Ebinop : forall x op e1 e2 a,
        generate_leqn_constraint ([x], [Ebinop op e1 e2 a])
        = generate_ldef_constraint x (Ebinop op e1 e2 a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Ewhen : forall x es i b a,
        generate_leqn_constraint ([x], [Ewhen es i b a])
        = generate_ldef_constraint x (Ewhen es i b a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Emerge : forall x i ets efs a,
        generate_leqn_constraint ([x], [Emerge i ets efs a])
        = generate_ldef_constraint x (Emerge i ets efs a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Eite : forall x e ets efs a,
        generate_leqn_constraint ([x], [Eite e ets efs a])
        = generate_ldef_constraint x (Eite e ets efs a).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Efby : forall x e0s es ans,
        generate_leqn_constraint ([x], [Efby e0s es ans])
        = generate_ldef_constraint x (Efby e0s es ans).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Eapp : forall x xs f args a,
        generate_leqn_constraint (x :: xs, [Eapp f args None a])
        = generate_lcall_constraint (x :: xs) f args (lvar rst_ty).
    Proof. reflexivity. Qed.

    Lemma gen_leqn_Eapp_reset : forall x xs f args r ty ckr nm a,
        generate_leqn_constraint
          (x :: xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a])
        = (do rty   <- find_env r env;
           do rstck <- option_to_sec (assign_clk_type env base_ty ckr);
           generate_lcall_constraint (x :: xs) f args
             (ljoin (lvar rst_ty) (merge [rty] rstck, []))).
    Proof. reflexivity. Qed.



    Fixpoint generate_leqns_constraints (eqs : list equation) : Sec (list constraint) :=
      match eqs with
      | [] => ret []
      | eq :: eqs' =>
          do c  <- generate_leqn_constraint eq;
          do cs <- generate_leqns_constraints eqs';
          ret (c ++ cs)
      end.

  End SECLEXPTYPING.




  (** * Nodes and programs

      The naming pass runs once and this reads the environment it produced,
      rather than allocating its own.  That is the discipline the Stc and Obc
      generators already follow, and it is what makes the interface fields of
      a generated Lustre signature and of the corresponding NLustre signature
      equal by computation instead of by hypothesis: each field is a function
      of the node's name, inputs and outputs -- which transcription preserves
      definitionally and normalisation preserves by [node_iface_eq] -- and of
      this one environment.

      Unlike the NLustre generator, which is [state_pure], this one threads the
      state: a nested call mints one name per result flow.  Two consequences
      are handled here.  Starting the run from the naming pass's final state
      keeps those names clear of every program variable's, since both draw
      [gensym] from [Ids.sec].  And [minted] reads them back off the state the
      run consumed, so [simplify] can eliminate them alongside the declared
      locals: a call-output name is local to the node's body exactly as a
      declared local is, and neither may reach the interface. *)

  Fixpoint sec_span (st : sec_state) (k : nat) : list ident :=
    match k with
    | O => []
    | S k' => Ids.gensym Ids.sec st :: sec_span (Pos.succ st) k'
    end.

  Definition minted (st0 st1 : sec_state) : list ident :=
    sec_span st0 (Pos.to_nat st1 - Pos.to_nat st0).

  (** The declared clocks, built the way [to_node] builds them. *)
  Definition lnode_clock_env (n : node) : Env.t (type * clock) :=
    Env.adds' n.(n_vars) (Env.adds' n.(n_in) (Env.from_list n.(n_out))).

  Definition generate_lnode_sig (G : secglobal) (n : node)
    (env : Env.t ident) (aux_names : list node_aux_names) (st0 : sec_state)
    : res (signature * sec_state) :=
    match (do (clk_id, rst_id) <- option_to_sec (get_node_aux n.(n_name) aux_names);
           do clk_type <- option_to_sec (Env.find clk_id env);
           do rst_type <- option_to_sec (Env.find rst_id env);
           do inp      <- option_to_sec (get_mappings_from_node n.(n_in) env);
           do out      <- option_to_sec (get_mappings_from_node n.(n_out) env);
           do locals   <- option_to_sec (get_mappings_from_node n.(n_vars) env);
           do cs       <- generate_leqns_constraints G env clk_type rst_type
                            (lnode_clock_env n) n.(n_eqs);
           ret (inp, out, rst_type, clk_type, locals, cs)) st0 with
    | Error e => Error e
    | OK ((inp, out, rst_type, clk_type, locals, cs), st1) =>
        OK ({| s_name  := n.(n_name);
               s_in    := inp;
               s_out   := out;
               s_reset := rst_type;
               s_clk   := clk_type;
               s_constraints := simplify cs (locals ++ minted st0 st1) |}, st1)
    end.

  Definition generate_lnode_sig_scoped_env (G : secglobal) (n : node)
    (envs : node_scoped_env) (aux_names : list node_aux_names) (st0 : sec_state)
    : res (signature * sec_state) :=
    match find_node_env n.(n_name) envs with
    | None =>
        Error (MSG "Missing node-local security environment " :: [CTX n.(n_name)])
    | Some env => generate_lnode_sig G n env aux_names st0
    end.

  (** As on the NLustre side, the accumulator grows front-to-back while
      [Ordered_nodes] places a callee after its caller, so the drivers
      generate over [rev nodes]: that is what puts a callee's signature in the
      accumulator before its caller needs it. *)

  Fixpoint generate_all_lsignatures' (acc : list signature) (ns : list node)
    (envs : node_scoped_env) (aux_names : list node_aux_names) (st0 : sec_state)
    : res (list signature * sec_state) :=
    match ns with
    | [] => OK (acc, st0)
    | n :: ns' =>
        match generate_lnode_sig_scoped_env acc n envs aux_names st0 with
        | Error e => Error e
        | OK (sig, st1) =>
            generate_all_lsignatures' (sig :: acc) ns' envs aux_names st1
        end
    end.

  Definition generate_all_lsignatures_scoped_env
    (ns : list node) (envs : node_scoped_env) (aux_names : list node_aux_names)
    (st0 : sec_state) : res (list signature) :=
    match generate_all_lsignatures' [] ns envs aux_names st0 with
    | OK (sigs, _) => OK sigs
    | Error e => Error e
    end.

End SECLTYPING.
