(** Symbolic security typing and signature generation for Obc classes
    produced by the Stc-to-Obc translation.

    The generator is a pc-carrying constraint generator over statements:
    clock types of the STC source reappear here as the security types of
    the [Ifte] conditions guarding each statement, so the pc plays the
    role that [assign_clk_type] played at the STC level.

    Note: [Obc.ObcTyping] (wt_exp/wt_stmt) is the ordinary data-type
    system; we use it only to bound the free variables of expressions
    and statements in the scopedness proofs. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String.
From Coq Require Import PArith.
From compcert Require Import common.Errors.

From Coq Require Import List.
Import List.ListNotations.

Module Type SECOBCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import SIG   : SIGNATURE Ids SC).
  Import SECMONADNotations.

  Definition hidden_class_vars (locals lasts stids: list ident) : list ident :=
    nodup ident_eq_dec (locals ++ lasts ++ stids).

  Definition env_injective (env: Env.t ident) : Prop :=
    forall x y tx ty,
      Env.find x env = Some tx ->
      Env.find y env = Some ty ->
      tx = ty ->
      x = y.

  (** * Per-instance state security types

      Every object of a class receives a fresh symbolic state type.  It
      is written by [reset] calls on the instance and read as the reset
      source of [step] calls, mirroring the reset-instance types
      ([rids]) of the STC security typing. *)

  Section STATEHANDLER.

  Definition fresh_state_ident : Sec ident :=
    fun n =>
      let id := Ids.gensym Ids.sec_reset n in
      OK (id, Pos.succ n).

  Definition fresh_state_insert (k: ident) (env: Env.t ident): Sec (Env.t ident * ident) :=
    if Env.mem k env then
      error (MSG "Instance declared more than once " :: [CTX k])
    else
      do v <- fresh_state_ident;
      do e <- insert_env k v env;
      ret (e, v).

  Fixpoint generate_state_env' (objs: list (ident * ident)) (env: Env.t ident) (acc: list ident)
    : Sec (Env.t ident * list ident) :=
    match objs with
    | [] => ret (env, acc)
    | (o, _) :: objs' =>
        do (env', sty) <- fresh_state_insert o env;
        generate_state_env' objs' env' (acc ++ [sty])
    end.

  Definition generate_state_env (objs: list (ident * ident)) : Sec (Env.t ident * list ident) :=
    generate_state_env' objs (Env.empty _) [].

  Lemma fresh_state_insert_find_in_acc:
    forall k acc st env' sty st' x ty,
      fresh_state_insert k acc st = OK ((env', sty), st') ->
      Env.find x env' = Some ty ->
      ty = sty \/ Env.find x acc = Some ty.
  Proof.
    intros k acc st env' sty st' x ty Hins Hfind.
    unfold fresh_state_insert in Hins.
    destruct (Env.mem k acc) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_state_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' sty st'.
    destruct (Pos.eq_dec x k) as [Heq|Hneq].
    - subst x. rewrite Env.gss in Hfind. inversion Hfind. auto.
    - rewrite Env.gso in Hfind; auto.
  Qed.

  Lemma fresh_state_insert_find_self:
    forall k acc st env' sty st',
      fresh_state_insert k acc st = OK ((env', sty), st') ->
      Env.find k env' = Some sty.
  Proof.
    intros k acc st env' sty st' Hins.
    unfold fresh_state_insert in Hins.
    destruct (Env.mem k acc) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_state_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' sty st'.
    now rewrite Env.gss.
  Qed.

  Lemma fresh_state_insert_preserves_find:
    forall k acc st env' sty st' x ty,
      fresh_state_insert k acc st = OK ((env', sty), st') ->
      Env.find x acc = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    intros k acc st env' sty st' x ty Hins Hfind.
    unfold fresh_state_insert in Hins.
    destruct (Env.mem k acc) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_state_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' sty st'.
    assert (Hxk : x <> k).
    { intro Heq. subst x.
      assert (Env.mem k acc = true).
      { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
      congruence. }
    now rewrite Env.gso.
  Qed.

  Lemma generate_state_env'_find_in_acc:
    forall objs env0 acc stids env' st st' x ty,
      (forall y ty', Env.find y env0 = Some ty' -> In ty' acc) ->
      generate_state_env' objs env0 acc st = OK ((env', stids), st') ->
      Env.find x env' = Some ty ->
      In ty stids.
  Proof.
    induction objs as [|[o cls] objs IH]; intros env0 acc stids env' st st' x ty Hacc Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. eauto.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & sty & st1 & Hstep & Hrec).
      eapply (IH acc1 (acc ++ [sty]) stids env' st1 st' x ty).
      + intros y ty' Hyfind.
        destruct (fresh_state_insert_find_in_acc _ _ _ _ _ _ _ _ Hstep Hyfind) as [Heq|Hold].
        * subst ty'. apply in_or_app. right. simpl. auto.
        * apply in_or_app. left.
          eapply Hacc; eauto.
      + exact Hrec.
      + exact Hfind.
  Qed.

  Lemma generate_state_env_find_in:
    forall objs state_env stids st st' x ty,
      generate_state_env objs st = OK ((state_env, stids), st') ->
      Env.find x state_env = Some ty ->
      In ty stids.
  Proof.
    intros objs state_env stids st st' x ty Hgen Hfind.
    unfold generate_state_env in Hgen.
    eapply generate_state_env'_find_in_acc; eauto.
    intros y ty' Hyfind.
    rewrite Env.gempty in Hyfind. discriminate.
  Qed.

  Lemma generate_state_env'_preserves_find:
    forall objs acc stids st env' stids' st' x ty,
      generate_state_env' objs acc stids st = OK ((env', stids'), st') ->
      Env.find x acc = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    induction objs as [|[o cls] objs IH]; intros acc stids st env' stids' st' x ty Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Hfind.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & sty & st1 & Hstep & Hrec).
      eapply IH; eauto.
      eapply fresh_state_insert_preserves_find; eauto.
  Qed.

  End STATEHANDLER.

  (** * Expression security typing *)

  Section SECEXPTYPING.
    Variable ctxt: Env.t ident.

    Fixpoint assign_exp_type (e: exp) : option ST :=
      match e with
      | Var x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | State x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | Valid x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | Const _ => Some []
      | Unop _ e' _ => assign_exp_type e'
      | Binop _ e1 e2 _ =>
          match assign_exp_type e1, assign_exp_type e2 with
          | Some t1, Some t2 => Some (t1 ⊔ t2)
          | _, _ => None
          end
      end.

    Lemma assign_exp_type_scoped:
      forall mems vars scope e st,
        (forall x, InMembers x vars ->
                   exists ty, Env.find x ctxt = Some ty /\ In ty scope) ->
        (forall x, InMembers x mems ->
                   exists ty, Env.find x ctxt = Some ty /\ In ty scope) ->
        TypObc.wt_exp mems vars e ->
        assign_exp_type e = Some st ->
        st_scoped scope st.
    Proof.
      intros mems vars scope e.
      induction e as [x tyx|x tyx|c|op e IHe tye|op e1 IHe1 e2 IHe2 tye|x tyx];
        intros st Hv Hm Hwt Hassign; simpl in Hassign.
      - (* Var *)
        inversion Hwt as [? ? Hin| | | | |]; subst.
        destruct (Hv x) as (ty & Hfind & Hscope); eauto using In_InMembers.
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
      - (* State *)
        inversion Hwt as [|? ? Hin| | | |]; subst.
        destruct (Hm x) as (ty & Hfind & Hscope); eauto using In_InMembers.
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
      - (* Const *)
        inversion Hassign; subst st.
        intros x Hx. inversion Hx.
      - (* Unop *)
        inversion Hwt; subst.
        eapply IHe; eauto.
      - (* Binop *)
        inversion Hwt; subst.
        destruct (assign_exp_type e1) as [t1|] eqn:Ht1; try discriminate.
        destruct (assign_exp_type e2) as [t2|] eqn:Ht2; try discriminate.
        inversion Hassign; subst st.
        apply st_scoped_merge; eauto.
      - (* Valid *)
        inversion Hwt as [| | | | |? ? Hin]; subst.
        destruct (Hv x) as (ty & Hfind & Hscope); eauto using In_InMembers.
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
    Qed.

  End SECEXPTYPING.

  (** * Collapsing constraints with duplicated targets

      Statement-level generation can produce several constraints for the
      same target (e.g. the two branches of a compiled [merge], or a
      state type written both by the reset method and by a translated
      [TcReset]).  [collapse] joins their sources, which is
      satisfaction-equivalent and restores the one-constraint-per-target
      shape assumed by [simplify]. *)

  Definition st_eq_dec : forall (a b: ST), {a = b} + {a <> b} :=
    list_eq_dec ident_eq_dec.

  Fixpoint join_into (lhs rhs: ST) (acc: list constraint) : list constraint :=
    match acc with
    | [] => [(lhs, rhs)]
    | (lhs', rhs') :: acc' =>
        if st_eq_dec rhs rhs'
        then ((lhs ⊔ lhs'), rhs') :: acc'
        else (lhs', rhs') :: join_into lhs rhs acc'
    end.

  Fixpoint collapse (cns: list constraint) : list constraint :=
    match cns with
    | [] => []
    | (lhs, rhs) :: cns' => join_into lhs rhs (collapse cns')
    end.

  Lemma join_into_rhs_in:
    forall lhs rhs acc rhs',
      In rhs' (map snd (join_into lhs rhs acc)) <->
      rhs' = rhs \/ In rhs' (map snd acc).
  Proof.
    intros lhs rhs acc.
    induction acc as [|[l r] acc IH]; intros rhs'; simpl.
    - split.
      + intros [Heq|[]]. auto.
      + intros [Heq|[]]. subst. auto.
    - destruct (st_eq_dec rhs r) as [Heq|Hneq]; simpl.
      + subst r. split.
        * intros [Heq|Hin]; auto.
        * intros [Heq|[Heq|Hin]]; subst; auto.
      + split.
        * intros [Heq|Hin].
          -- subst r. auto.
          -- apply IH in Hin. destruct Hin; auto.
        * intros [Heq|[Heq|Hin]].
          -- right. apply IH. auto.
          -- subst r. auto.
          -- right. apply IH. auto.
  Qed.

  Lemma join_into_rhs_nodup:
    forall lhs rhs acc,
      NoDup (map snd acc) ->
      NoDup (map snd (join_into lhs rhs acc)).
  Proof.
    intros lhs rhs acc.
    induction acc as [|[l r] acc IH]; intros Hnd; simpl.
    - constructor; [intro Hin; inversion Hin|constructor].
    - inversion Hnd as [|? ? Hnin Hnd']; subst.
      destruct (st_eq_dec rhs r) as [Heq|Hneq]; simpl.
      + constructor; assumption.
      + constructor.
        * intro Hin.
          apply join_into_rhs_in in Hin.
          destruct Hin as [Heq|Hin]; [congruence|contradiction].
        * apply IH. exact Hnd'.
  Qed.

  Lemma collapse_rhs_nodup:
    forall cns, NoDup (map snd (collapse cns)).
  Proof.
    induction cns as [|[l r] cns IH]; simpl.
    - constructor.
    - apply join_into_rhs_nodup. exact IH.
  Qed.

  Lemma collapse_rhs_in:
    forall cns rhs,
      In rhs (map snd (collapse cns)) <-> In rhs (map snd cns).
  Proof.
    induction cns as [|[l r] cns IH]; intros rhs; simpl.
    - tauto.
    - rewrite join_into_rhs_in. rewrite IH.
      split.
      + intros [Heq|Hin]; [left; congruence|right; assumption].
      + intros [Heq|Hin]; [left; congruence|right; assumption].
  Qed.

  Lemma join_into_scoped:
    forall scope lhs rhs acc,
      st_scoped scope lhs ->
      st_scoped scope rhs ->
      constraints_scoped scope acc ->
      constraints_scoped scope (join_into lhs rhs acc).
  Proof.
    intros scope lhs rhs acc Hlhs Hrhs.
    induction acc as [|[l r] acc IH]; intros Hsc; simpl.
    - constructor; [|constructor].
      intros x Hx.
      unfold constraint_scope in Hx. simpl in Hx.
      apply in_app_iff in Hx.
      destruct Hx as [Hx|Hx]; [exact (Hlhs _ Hx)|exact (Hrhs _ Hx)].
    - inversion Hsc as [|? ? Hc Hcs]; subst.
      destruct (st_eq_dec rhs r) as [Heq|Hneq].
      + subst r. constructor; [|exact Hcs].
        intros x Hx.
        unfold constraint_scope in Hx. simpl in Hx.
        apply in_app_iff in Hx.
        destruct Hx as [Hx|Hx].
        * apply in_merge_inv in Hx.
          destruct Hx as [Hx|Hx].
          -- exact (Hlhs _ Hx).
          -- apply Hc. unfold constraint_scope. apply in_or_app. now left.
        * apply Hc. unfold constraint_scope. apply in_or_app. now right.
      + constructor; [exact Hc|].
        apply IH. exact Hcs.
  Qed.

  Lemma collapse_scoped:
    forall scope cns,
      constraints_scoped scope cns ->
      constraints_scoped scope (collapse cns).
  Proof.
    intros scope cns.
    induction cns as [|[l r] cns IH]; intros Hsc; simpl.
    - constructor.
    - inversion Hsc as [|? ? Hc Hcs]; subst.
      apply join_into_scoped.
      + intros x Hx. apply Hc.
        unfold constraint_scope. apply in_or_app. now left.
      + intros x Hx. apply Hc.
        unfold constraint_scope. apply in_or_app. now right.
      + apply IH. exact Hcs.
  Qed.

  Lemma join_into_rhs_len:
    forall lhs rhs acc,
      length rhs = 1%nat ->
      Forall (fun c => length (snd c) = 1%nat) acc ->
      Forall (fun c => length (snd c) = 1%nat) (join_into lhs rhs acc).
  Proof.
    intros lhs rhs acc Hlen.
    induction acc as [|[l r] acc IH]; intros Hall; simpl.
    - constructor; [exact Hlen|constructor].
    - inversion Hall as [|? ? Hc Hcs]; subst.
      destruct (st_eq_dec rhs r) as [Heq|Hneq].
      + constructor; [exact Hc|exact Hcs].
      + constructor; [exact Hc|].
        apply IH. exact Hcs.
  Qed.

  Lemma collapse_wf:
    forall cns,
      Forall (fun c => length (snd c) = 1%nat) cns ->
      wf_constraints (collapse cns).
  Proof.
    intros cns Hall.
    split.
    - apply collapse_rhs_nodup.
    - induction cns as [|[l r] cns IH]; simpl.
      + constructor.
      + inversion Hall as [|? ? Hc Hcs]; subst.
        simpl in Hc.
        assert (Hrec : Forall (fun '(_, rhs) => length rhs = 1%nat) (collapse cns)).
        { apply IH. exact Hcs. }
        assert (Hgen : Forall (fun c => length (snd c) = 1%nat) (join_into l r (collapse cns))).
        { apply join_into_rhs_len; [exact Hc|].
          eapply Forall_impl; [|exact Hrec].
          intros [? ?] Hlen. exact Hlen. }
        eapply Forall_impl; [|exact Hgen].
        intros [? ?] Hlen. exact Hlen.
  Qed.

  (** [lhs_join] is the right-nested join of the sources of a
      constraint list; on a list whose constraints all share one target
      it is exactly what [collapse] produces. *)

  Fixpoint lhs_join (cns : list constraint) : ST :=
    match cns with
    | [] => []
    | (l, _) :: rest =>
        match rest with
        | [] => l
        | _ => l ⊔ lhs_join rest
        end
    end.

  Lemma collapse_same_target:
    forall cns r,
      cns <> [] ->
      Forall (fun c => snd c = r) cns ->
      collapse cns = [(lhs_join cns, r)].
  Proof.
    induction cns as [|[l r0] cns IH]; intros r Hne Hall.
    - congruence.
    - assert (Hc : snd (l, r0) = r) by (inversion Hall; auto).
      assert (Hcs : Forall (fun c => snd c = r) cns) by (inversion Hall; auto).
      simpl in Hc. subst r0.
      destruct cns as [|c cns'].
      + simpl. reflexivity.
      + assert (Hne' : c :: cns' <> []) by discriminate.
        specialize (IH r Hne' Hcs).
        simpl. simpl in IH. rewrite IH.
        simpl.
        destruct (st_eq_dec r r) as [_|Habs]; [reflexivity|congruence].
  Qed.

  Lemma lhs_join_app:
    forall a b,
      a <> [] ->
      b <> [] ->
      lhs_join (a ++ b) = lhs_join a ⊔ lhs_join b.
  Proof.
    induction a as [|[l r] a IH]; intros b Hna Hnb.
    - congruence.
    - destruct a as [|c a'].
      + simpl.
        destruct b as [|cb b']; [congruence|reflexivity].
      + assert (Hna' : c :: a' <> []) by discriminate.
        specialize (IH b Hna' Hnb).
        simpl in *.
        rewrite IH.
        rewrite MergeFacts.merge_assoc. reflexivity.
  Qed.

  (** * Statement constraint generation *)

  Section SECSTMTTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    Definition vars_env_scoped {A: Type} (vars: list (ident * A)) (scope: list ident) : Prop :=
      forall x,
        InMembers x vars ->
        exists ty, Env.find x env = Some ty /\ In ty scope.

    (** [pc] is the join of the security types of all conditions
        guarding the statement, seeded at method entry.  For step
        methods of translated classes it starts at
        [[rst_ty] ⊔ [base_ty]], so leaves reproduce the
        [([rst_ty] ⊔ ckty) ⊔ ...] sources of the STC constraints. *)

    Fixpoint generate_stmt_constraints (pc: ST) (s: stmt) : Sec (list constraint) :=
      match s with
      | Skip => ret []
      | Assign x e =>
          do ety <- option_to_sec (assign_exp_type env e);
          do xty <- find_env x env;
          ret [(((([rst_ty] ⊔ pc) ⊔ ety)), [xty])]
      | AssignSt x e =>
          do ety <- option_to_sec (assign_exp_type env e);
          do xty <- find_env x env;
          ret [(((([rst_ty] ⊔ pc) ⊔ ety)), [xty])]
      | Ifte e s1 s2 =>
          do ety <- option_to_sec (assign_exp_type env e);
          do c1 <- generate_stmt_constraints (pc ⊔ ety) s1;
          do c2 <- generate_stmt_constraints (pc ⊔ ety) s2;
          ret (c1 ++ c2)
      | Comp s1 s2 =>
          do c1 <- generate_stmt_constraints pc s1;
          do c2 <- generate_stmt_constraints pc s2;
          ret (c1 ++ c2)
      | Call [] _ o m _ =>
          if ident_eqb m Ids.reset then
            do sty <- find_env o state_env;
            ret [(([rst_ty] ⊔ pc), [sty])]
          else ret []
      | Call ys cls o m es =>
          if ident_eqb m Ids.step then
            match find_signature cls G with
            | Some n =>
                do inptyp <- mmap (fun e => option_to_sec (assign_exp_type env e)) es;
                do outtyp <- mmap (fun y => find_env y env) ys;
                do sty    <- find_env o state_env;
                generate_constraints n inptyp pc [sty] outtyp
            | None => error (MSG "Signature not found for: " :: [CTX cls])
            end
          else error (msg "Unsupported method call")
      end.

    Fixpoint stmt_state_keys (s: stmt) : list ident :=
      match s with
      | Call _ _ o _ _ => [o]
      | Comp s1 s2 => stmt_state_keys s1 ++ stmt_state_keys s2
      | Ifte _ s1 s2 => stmt_state_keys s1 ++ stmt_state_keys s2
      | _ => []
      end.

    Lemma mmap_assign_exp_type_scoped:
      forall mems vars scope es tys st st',
        vars_env_scoped vars scope ->
        vars_env_scoped mems scope ->
        Forall (TypObc.wt_exp mems vars) es ->
        mmap (fun e => option_to_sec (assign_exp_type env e)) es st = OK (tys, st') ->
        Forall (st_scoped scope) tys.
    Proof.
      intros mems vars scope es.
      induction es as [|e es IH]; intros tys st st' Hv Hm Hwt Hmap.
      - simpl in Hmap. inversion Hmap; subst. constructor.
      - inversion Hwt as [|e0 es0 He Hes]; subst e0 es0.
        simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold option_to_sec in Hhd.
        destruct (assign_exp_type env e) as [ety'|] eqn:Heq; try discriminate.
        inversion Hhd; subst ety st1.
        unfold ret in Hret. inversion Hret; subst tys st'.
        constructor.
        + eapply (assign_exp_type_scoped env mems vars scope e ety');
            [exact Hv|exact Hm|exact He|exact Heq].
        + eapply IH; eauto.
    Qed.

    Theorem generate_stmt_constraints_scoped_on_keys:
      forall p insts mems vars scope s pc cns st st',
        secglobal_scoped G ->
        vars_env_scoped vars scope ->
        vars_env_scoped mems scope ->
        TypObc.wt_stmt p insts mems vars s ->
        st_scoped scope pc ->
        In rst_ty scope ->
        (forall o sty st0 st1,
            In o (stmt_state_keys s) ->
            find_env o state_env st0 = OK (sty, st1) ->
            In sty scope) ->
        generate_stmt_constraints pc s st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros p insts mems vars scope s.
      induction s as [x e|x e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o m es|];
        intros pc cns st st' Hglob Hv Hm Hwt Hpc Hrst Hkeys Hgen.
      - (* Assign *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        inversion Hwt as [? ? Hinx Hwte| | | | |]; subst.
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env mems vars scope e ety');
            [exact Hv|exact Hm|exact Hwte|exact Hexp']. }
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        assert (Hxscope : In xty' scope).
        { destruct (Hv x) as (ty & Hfind' & Hscope); eauto using In_InMembers.
          rewrite Hfindx in Hfind'. inversion Hfind'; subst. exact Hscope. }
        assert (Hsrc : st_scoped scope ((([rst_ty] ⊔ pc) ⊔ ety'))).
        { apply st_scoped_merge;
            [apply st_scoped_merge;
              [apply st_scoped_singleton; exact Hrst|exact Hpc]
            |exact Hety]. }
        change (constraints_scoped scope [((([rst_ty] ⊔ pc) ⊔ ety'), [xty'])]).
        constructor; [|constructor].
        intros y Hy.
        unfold constraint_scope in Hy. cbn [fst snd] in Hy.
        apply in_app_iff in Hy.
        destruct Hy as [Hy|Hy].
        + exact (Hsrc _ Hy).
        + simpl in Hy. destruct Hy as [Heq|[]]. subst y. exact Hxscope.
      - (* AssignSt *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        inversion Hwt as [|? ? Hinx Hwte| | | |]; subst.
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env mems vars scope e ety');
            [exact Hv|exact Hm|exact Hwte|exact Hexp']. }
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        assert (Hxscope : In xty' scope).
        { destruct (Hm x) as (ty & Hfind' & Hscope); eauto using In_InMembers.
          rewrite Hfindx in Hfind'. inversion Hfind'; subst. exact Hscope. }
        assert (Hsrc : st_scoped scope ((([rst_ty] ⊔ pc) ⊔ ety'))).
        { apply st_scoped_merge;
            [apply st_scoped_merge;
              [apply st_scoped_singleton; exact Hrst|exact Hpc]
            |exact Hety]. }
        change (constraints_scoped scope [((([rst_ty] ⊔ pc) ⊔ ety'), [xty'])]).
        constructor; [|constructor].
        intros y Hy.
        unfold constraint_scope in Hy. cbn [fst snd] in Hy.
        apply in_app_iff in Hy.
        destruct Hy as [Hy|Hy].
        + exact (Hsrc _ Hy).
        + simpl in Hy. destruct Hy as [Heq|[]]. subst y. exact Hxscope.
      - (* Ifte *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (c1 & st2 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st3 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        inversion Hwt as [| |? ? ? Hwte Hty Hwt1 Hwt2| | |]; subst.
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env mems vars scope e ety');
            [exact Hv|exact Hm|exact Hwte|exact Hexp']. }
        assert (Hpc' : st_scoped scope (pc ⊔ ety')).
        { apply st_scoped_merge; assumption. }
        apply Forall_app. split.
        + eapply IH1; eauto.
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now left.
        + eapply IH2; eauto.
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now right.
      - (* Comp *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        inversion Hwt as [| | |? ? Hwt1 Hwt2| |]; subst.
        apply Forall_app. split.
        + eapply IH1; eauto.
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now left.
        + eapply IH2; eauto.
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now right.
      - (* Call *)
        destruct ys as [|y ys'].
        + simpl in Hgen.
          destruct (ident_eqb m Ids.reset) eqn:Hreset.
          * eapply sec_bind_inv in Hgen as (sty & st1 & Hfind & Hret).
            unfold ret in Hret. inversion Hret; subst cns st'.
            assert (Hsrc : st_scoped scope ([rst_ty] ⊔ pc)).
            { apply st_scoped_merge;
                [apply st_scoped_singleton; exact Hrst|exact Hpc]. }
            change (constraints_scoped scope [(([rst_ty] ⊔ pc), [sty])]).
            constructor; [|constructor].
            intros z Hz.
            unfold constraint_scope in Hz. cbn [fst snd] in Hz.
            apply in_app_iff in Hz.
            destruct Hz as [Hz|Hz].
            -- exact (Hsrc _ Hz).
            -- simpl in Hz. destruct Hz as [Heq|[]]. subst z.
               eapply Hkeys; eauto.
               simpl. now left.
          * unfold ret in Hgen. inversion Hgen; subst. constructor.
        + simpl in Hgen.
          destruct (ident_eqb m Ids.step) eqn:Hstep; try discriminate.
          destruct (find_signature cls G) as [sig|] eqn:Hfindsig; try discriminate.
          eapply sec_bind_inv in Hgen as (inptyp & st1 & Hinp & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st2 & Hout & Hgen).
          eapply sec_bind_inv in Hgen as (sty & st3 & Hsty & Hgen).
          inversion Hwt as
              [| | | |clsid cls0 p' o0 f0 fm ys0 es0 Hino Hfindcls Hfindm Hndys Houts Hins Hwtes|];
            subst.
          assert (HinpScope : Forall (st_scoped scope) inptyp).
          { eapply (mmap_assign_exp_type_scoped mems vars scope es inptyp st st1);
              [exact Hv|exact Hm|exact Hwtes|exact Hinp]. }
          assert (HoutScope : Forall (fun x => In x scope) outtyp).
          { eapply (SC.mmap_find_env_scoped env scope (y :: ys') outtyp st1 st2).
            - intros z Hz.
              assert (Hinz : InMembers z vars).
              { destruct (Forall2_in_left _ _ _ _ Houts Hz) as (xt & Hinxt & Hinvar).
                eapply In_InMembers; eauto. }
              destruct (Hv z Hinz) as (ty & Hfind & Hscope).
              exists ty. split; assumption.
            - exact Hout. }
          assert (Hstyscope : In sty scope).
          { eapply Hkeys; eauto.
            simpl. now left. }
          eapply (generate_constraints_scoped sig scope inptyp pc [sty] outtyp cns st3 st');
            [eapply Hglob; eauto
            |exact HinpScope
            |exact Hpc
            |apply st_scoped_singleton; exact Hstyscope
            |exact HoutScope
            |exact Hgen].
      - (* Skip *)
        simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst. constructor.
    Qed.

    Corollary generate_stmt_constraints_scoped:
      forall p insts mems vars scope s pc cns st st',
        secglobal_scoped G ->
        vars_env_scoped vars scope ->
        vars_env_scoped mems scope ->
        TypObc.wt_stmt p insts mems vars s ->
        st_scoped scope pc ->
        In rst_ty scope ->
        (forall o sty st0 st1,
            find_env o state_env st0 = OK (sty, st1) ->
            In sty scope) ->
        generate_stmt_constraints pc s st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros p insts mems vars scope s pc cns st st'
             Hglob Hv Hm Hwt Hpc Hrst Hkeys Hgen.
      eapply (generate_stmt_constraints_scoped_on_keys p insts mems vars scope s pc cns st st');
        [exact Hglob|exact Hv|exact Hm|exact Hwt|exact Hpc|exact Hrst| |exact Hgen].
      intros o sty st0 st1 Hin Hfind.
      eapply Hkeys; eauto.
    Qed.

  End SECSTMTTYPING.

  (** * Class signature generation *)

  Section SECCLSTYPING.
    Variable G: secglobal.

    Definition generate_class_signature (c: class) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match (do (clk_id, rst_id) <- option_to_sec (get_node_aux (c.(c_name)) aux_names);
             do clk_type <- option_to_sec (Env.find clk_id env);
             do rst_type <- option_to_sec (Env.find rst_id env);
             do stepm  <- option_to_sec (find_method Ids.step c.(c_methods));
             do resetm <- option_to_sec (find_method Ids.reset c.(c_methods));
             do inp    <- option_to_sec (get_mappings_from_node stepm.(m_in) env);
             do out    <- option_to_sec (get_mappings_from_node stepm.(m_out) env);
             do locals <- option_to_sec (get_mappings_from_node stepm.(m_vars) env);
             do lasts  <- option_to_sec (get_mappings_from_node c.(c_mems) env);
             do (state_env, stids) <- generate_state_env c.(c_objs);
             do craw_step <- generate_stmt_constraints G env state_env rst_type
                              [clk_type] stepm.(m_body);
             do craw_reset <- generate_stmt_constraints G env state_env rst_type
                              [] resetm.(m_body);
             ret (inp, out, rst_type, clk_type,
                  simplify (collapse (craw_step ++ craw_reset))
                           (hidden_class_vars locals lasts stids), env)) init_state with
      | Error e => Error e
      | OK ((inp, out, rst_id, ck_id, constraints, env), _) =>
          OK {| s_name  := c.(c_name);
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints |}
      end.

    Definition generate_class_signature_scoped_env
      (c: class) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res signature :=
      match find_node_env c.(c_name) envs with
      | None =>
          Error (MSG "Missing class-local security environment" :: [CTX c.(c_name)])
      | Some env =>
          generate_class_signature c env aux_names
      end.

    Lemma generate_class_signature_inv:
      forall c env aux_names sig,
        generate_class_signature c env aux_names = OK sig ->
        exists clk_id rst_id clk_type rst_type stepm resetm
               inp out locals lasts state_env stids
               craw_step craw_reset st_state st_step st_raw,
          get_node_aux c.(c_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id env = Some clk_type
          /\ Env.find rst_id env = Some rst_type
          /\ find_method Ids.step c.(c_methods) = Some stepm
          /\ find_method Ids.reset c.(c_methods) = Some resetm
          /\ get_mappings_from_node stepm.(m_in) env = Some inp
          /\ get_mappings_from_node stepm.(m_out) env = Some out
          /\ get_mappings_from_node stepm.(m_vars) env = Some locals
          /\ get_mappings_from_node c.(c_mems) env = Some lasts
          /\ generate_state_env c.(c_objs) init_state = OK ((state_env, stids), st_state)
          /\ generate_stmt_constraints G env state_env rst_type [clk_type]
               stepm.(m_body) st_state = OK (craw_step, st_step)
          /\ generate_stmt_constraints G env state_env rst_type []
               resetm.(m_body) st_step = OK (craw_reset, st_raw)
          /\ sig = {| s_name  := c.(c_name);
                      s_in    := inp;
                      s_out   := out;
                      s_reset := rst_type;
                      s_clk   := clk_type;
                      s_constraints :=
                        simplify (collapse (craw_step ++ craw_reset))
                                 (hidden_class_vars locals lasts stids) |}.
    Proof.
      intros c env aux_names sig Hsig.
      unfold generate_class_signature in Hsig.
      lazymatch type of Hsig with
      | context [match ?m with | OK _ => _ | Error _ => _ end = _] =>
          remember m as gen_res eqn:Hgen
      end.
      destruct gen_res as [[packed st_res]|]; try discriminate.
      destruct packed as [packed env0].
      destruct packed as [packed packed_constraints].
      destruct packed as [packed packed_clk_type].
      destruct packed as [packed packed_rst_type].
      destruct packed as [packed_inp packed_out].
      simpl in Hsig.
      inversion Hsig; clear Hsig; subst.
      symmetry in Hgen.
      eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
      eapply sec_bind_inv in Hgen as (clk_type & st_clk & Hclk & Hgen).
      eapply sec_bind_inv in Hgen as (rst_type & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (stepm & st_stepm & Hstepm & Hgen).
      eapply sec_bind_inv in Hgen as (resetm & st_resetm & Hresetm & Hgen).
      eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
      eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
      eapply sec_bind_inv in Hgen as (lasts & st_lasts & Hlasts & Hgen).
      eapply sec_bind2_inv in Hgen as (state_env & stids & st_state & Hstate & Hgen).
      eapply sec_bind_inv in Hgen as (craw_step & st_step & Hstepc & Hgen).
      eapply sec_bind_inv in Hgen as (craw_reset & st_raw & Hresetc & Hret).
      unfold option_to_sec in Haux.
      destruct (get_node_aux (c.(c_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
      inversion Haux; subst clk_id0 rst_id0 st_aux.
      unfold option_to_sec in Hclk.
      destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
      inversion Hclk; subst clk_type0 st_clk.
      unfold option_to_sec in Hrst.
      destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
      inversion Hrst; subst rst_type0 st_rst.
      unfold option_to_sec in Hstepm.
      destruct (find_method Ids.step c.(c_methods)) as [stepm0|] eqn:Hstepm0; try discriminate.
      inversion Hstepm; subst stepm0 st_stepm.
      unfold option_to_sec in Hresetm.
      destruct (find_method Ids.reset c.(c_methods)) as [resetm0|] eqn:Hresetm0; try discriminate.
      inversion Hresetm; subst resetm0 st_resetm.
      unfold option_to_sec in Hinp.
      destruct (get_mappings_from_node (stepm.(m_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
      inversion Hinp; subst inp0 st_inp.
      unfold option_to_sec in Hout.
      destruct (get_mappings_from_node (stepm.(m_out)) env) as [out0|] eqn:Hout0; try discriminate.
      inversion Hout; subst out0 st_out.
      unfold option_to_sec in Hlocals.
      destruct (get_mappings_from_node (stepm.(m_vars)) env) as [locals0|] eqn:Hlocals0; try discriminate.
      inversion Hlocals; subst locals0 st_locals.
      unfold option_to_sec in Hlasts.
      destruct (get_mappings_from_node (c.(c_mems)) env) as [lasts0|] eqn:Hlasts0; try discriminate.
      inversion Hlasts; subst lasts0 st_lasts.
      unfold ret in Hret. inversion Hret; subst.
      exists clk_id, rst_id, packed_clk_type, packed_rst_type, stepm, resetm,
             packed_inp, packed_out, locals, lasts, state_env, stids,
             craw_step, craw_reset, st_state, st_step, st_res.
      repeat split; eauto.
    Qed.

  End SECCLSTYPING.

  (** * Program-level signature generation *)

  Section SECOBCPROGRAMTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_class_signatures' (acc: list signature) (p: program)
             (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match p with
      | [] => OK acc
      | c :: cs =>
          do sig <- generate_class_signature acc c env aux_names;
          generate_all_class_signatures' (sig :: acc) cs env aux_names
      end.

    Definition generate_all_class_signatures (p: program) (env: Env.t ident)
               (aux_names: list node_aux_names) : res (list signature) :=
      generate_all_class_signatures' [] p env aux_names.

    Fixpoint generate_all_class_signatures_scoped_env'
      (acc: list signature) (p: program) (envs: node_scoped_env)
      (aux_names: list node_aux_names) : res (list signature) :=
      match p with
      | [] => OK acc
      | c :: cs =>
          do sig <- generate_class_signature_scoped_env acc c envs aux_names;
          generate_all_class_signatures_scoped_env' (sig :: acc) cs envs aux_names
      end.

    Definition generate_all_class_signatures_scoped_env
      (p: program) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res (list signature) :=
      generate_all_class_signatures_scoped_env' [] p envs aux_names.

  End SECOBCPROGRAMTYPING.

End SECOBCTYPING.

Module SecObcTyping
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS Ids Op OpAux SynObc)
  (Import TypObc: OBCTYPING Ids Op OpAux SynObc SemObc)
  (Import SIG   : SIGNATURE Ids SC)
  <: SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG.

Include SECOBCTYPING Ids Op OpAux SC SynObc SemObc TypObc SIG.

End SecObcTyping.
