(** Symbolic security typing and scoped signature generation for translated STC systems. *)

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
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
From Velus Require Import Clocks.

From Coq Require Import String.
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
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo).
  Import SECMONADNotations.

  Definition hidden_sys_vars (locals lasts rids: list ident) : list ident :=
    nodup ident_eq_dec (locals ++ lasts ++ rids).

  Section RESETHANDLER.

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

  (* fresh_reset_ident / fresh_reset_insert now live in SecContext.v *)

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

  (** A successful [generate_reset_env] witnesses that the reset
      instances are pairwise distinct: [fresh_reset_insert] refuses a key
      that is already bound, so a repeat would have made the whole run
      fail. *)

  Lemma generate_reset_env'_key_unbound:
    forall trs e acc reset_env rids st st' s,
      generate_reset_env' trs e acc st = OK ((reset_env, rids), st') ->
      In s (map fst (resets_of trs)) ->
      Env.find s e = None.
  Proof.
    induction trs as [|tr trs IH]; intros e acc reset_env rids st st' s Hgen Hin.
    - inversion Hin.
    - destruct tr as [x ck ce|x ck ex|s0 ck f|x xs ck b f exps]; simpl in Hin, Hgen.
      1,2,4: eapply IH; eauto.
      eapply sec_bind2_inv in Hgen as (e1 & i & st1 & Hstep & Hrec).
      assert (Hmem : Env.mem s0 e = false).
      { unfold fresh_reset_insert in Hstep.
        destruct (Env.mem s0 e); [discriminate|reflexivity]. }
      assert (Hnone0 : Env.find s0 e = None).
      { destruct (Env.find s0 e) as [v|] eqn:Hf; [|reflexivity].
        assert (Env.mem s0 e = true).
        { apply Env.mem_1. unfold Env.In. eexists; exact Hf. }
        congruence. }
      assert (He1 : e1 = Env.add s0 i e).
      { unfold fresh_reset_insert in Hstep.
        rewrite Hmem in Hstep.
        eapply sec_bind_inv in Hstep as (v & sv & Hfresh & Hstep).
        eapply sec_bind_inv in Hstep as (w & sw & Hins & Hret).
        unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v sv.
        unfold insert_env, ret in Hins. inversion Hins; subst w sw.
        unfold ret in Hret. inversion Hret; subst e1 i st1. reflexivity. }
      destruct Hin as [Heq|Hin].
      + subst s0. exact Hnone0.
      + specialize (IH _ _ _ _ _ _ _ Hrec Hin).
        subst e1.
        destruct (Pos.eq_dec s s0) as [Heq|Hneq].
        * subst s0. rewrite Env.gss in IH. discriminate.
        * rewrite Env.gso in IH by auto. exact IH.
  Qed.

  Lemma generate_reset_env'_keys_nodup:
    forall trs e acc reset_env rids st st',
      generate_reset_env' trs e acc st = OK ((reset_env, rids), st') ->
      NoDup (map fst (resets_of trs)).
  Proof.
    induction trs as [|tr trs IH]; intros e acc reset_env rids st st' Hgen.
    - simpl. constructor.
    - destruct tr as [x ck ce|x ck ex|s0 ck f|x xs ck b f exps]; simpl in Hgen |- *.
      1,2,4: eapply IH; eauto.
      eapply sec_bind2_inv in Hgen as (e1 & i & st1 & Hstep & Hrec).
      constructor.
      + intro Hin.
        pose proof (generate_reset_env'_key_unbound trs e1 _ _ _ _ _ s0 Hrec Hin) as Hnone.
        unfold fresh_reset_insert in Hstep.
        destruct (Env.mem s0 e) eqn:Hmem; [discriminate|].
        eapply sec_bind_inv in Hstep as (v & sv & Hfresh & Hstep).
        eapply sec_bind_inv in Hstep as (w & sw & Hins & Hret).
        unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v sv.
        unfold insert_env, ret in Hins. inversion Hins; subst w sw.
        unfold ret in Hret. inversion Hret; subst e1 i st1.
        rewrite Env.gss in Hnone. discriminate.
      + eapply IH; eauto.
  Qed.

  Lemma generate_reset_env_keys_nodup:
    forall trs reset_env rids st st',
      generate_reset_env trs st = OK ((reset_env, rids), st') ->
      NoDup (map fst (resets_of trs)).
  Proof.
    intros trs reset_env rids st st' Hgen.
    unfold generate_reset_env in Hgen.
    eapply generate_reset_env'_keys_nodup; eauto.
  Qed.

  End RESETHANDLER.

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

      Lemma wc_aexp_free_in_vars:
        forall vars x ck e,
          wc_env vars ->
          wc_exp vars e ck ->
          CEIsF.Is_free_in_aexp x ck e ->
          InMembers x vars.
    Proof.
      intros vars x ck e Henv Hwc Hfree.
      inversion Hfree; subst.
      - eauto using wc_exp_free_in_vars.
        - eauto using wc_clock_free_in_vars, wc_clock_exp.
    Qed.

      Lemma wc_caexp_free_in_vars:
        forall vars x ck ce,
          wc_env vars ->
          wc_cexp vars ce ck ->
          CEIsF.Is_free_in_caexp x ck ce ->
          InMembers x vars.
    Proof.
      intros vars x ck ce Henv Hwc Hfree.
      inversion Hfree; subst.
      - eauto using wc_cexp_free_in_vars.
        - eauto using wc_clock_free_in_vars, wc_clock_cexp.
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

    (** The shared lemma, read at this section's [env]. *)

    Lemma get_mappings_nodup:
      forall xs tys,
        NoDup xs ->
        env_injective env ->
        get_mappings xs env = Some tys ->
        NoDup tys.
    Proof.
      intros xs tys Hnd Hinj Hmap.
      eapply get_mappings_nodup_gen; eauto.
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
        wc_env vars ->
        Clo.wc_trconstr P vars (TcCall i xs ck rst f es) ->
        Is_free_in_clock x ck ->
        InMembers x vars.
    Proof.
      intros P vars i xs ck rst f es x Henv Hwc Hfree.
      inversion Hwc as [| | |i' xs' ck' rst' f' es' s P' sub Hfind Hins Houts]; subst.
        destruct s.(SynStc.s_in) as [|[xin [tin xck]] ins] eqn:Hinps.
        { pose proof s.(SynStc.s_ingt0) as Hgt0.
          rewrite Hinps in Hgt0. simpl in Hgt0. lia. }
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
               CEIsF.Is_free_in_exp x e ->
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
        induction Hfor as [|[y [yty yck]] y0 outs xs [Hsub [xck [Hinx Hinst]]] Hfor IH].
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq|Hin].
          + subst y0.
            destruct (Hvars x) as (ty & Hfind & Hscope); eauto using In_InMembers.
          + eapply IH; eauto.
      Qed.

      Lemma generate_reset_env'_find_in_acc:
        forall trs env0 acc rids env' st st' x ty,
          (forall y ty', Env.find y env0 = Some ty' -> In ty' acc) ->
          generate_reset_env' trs env0 acc st = OK ((env', rids), st') ->
          Env.find x env' = Some ty ->
          In ty rids.
      Proof.
        induction trs as [|tr trs IH]; intros env0 acc rids env' st st' x ty Hacc Hgen Hfind.
        - simpl in Hgen. inversion Hgen; subst. eauto.
        - simpl in Hgen.
          destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
          1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (acc1 & rst_inst & st1 & Hstep & Hrec).
        eapply (IH acc1 (acc ++ [rst_inst]) rids env' st1 st' x ty).
        + intros y ty' Hyfind.
          destruct (fresh_reset_insert_find_in_acc _ _ _ _ _ _ _ _ Hstep Hyfind) as [Heq|Hold].
          * subst ty'. apply in_or_app. right. simpl. auto.
          * apply in_or_app. left.
            eapply Hacc; eauto.
          + exact Hrec.
          + exact Hfind.
      Qed.

    Lemma generate_reset_env_find_in:
      forall trs reset_env0 rids st' x ty,
        generate_reset_env trs init_state = OK ((reset_env0, rids), st') ->
        Env.find x reset_env0 = Some ty ->
        In ty rids.
      Proof.
        intros trs reset_env0 rids st' x ty Hgen Hfind.
        unfold generate_reset_env in Hgen.
        eapply generate_reset_env'_find_in_acc; eauto.
        intros y ty' Hyfind.
        rewrite Env.gempty in Hyfind. discriminate.
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

    (** The accumulated [rids] are exactly the reset instances read back
        through the generated environment, in order. *)

    Lemma generate_reset_env'_rids:
      forall trs e acc renv rids st st',
        generate_reset_env' trs e acc st = OK ((renv, rids), st') ->
        exists rs,
          get_mappings (map fst (resets_of trs)) renv = Some rs
          /\ rids = acc ++ rs.
    Proof.
      induction trs as [|tr trs IH]; intros e acc renv rids st st' Hgen.
      - simpl in Hgen. inversion Hgen; subst.
        exists []. split; [reflexivity|now rewrite app_nil_r].
      - destruct tr as [x ck ce|x ck ex|s0 ck f|x xs ck b f exps]; simpl in Hgen |- *.
        1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (e1 & i & st1 & Hstep & Hrec).
        destruct (IH _ _ _ _ _ _ Hrec) as (rs & Hrs & Hrids).
        assert (Hself : Env.find s0 e1 = Some i).
        { eapply fresh_reset_insert_find_self; eauto. }
        assert (Hfind : Env.find s0 renv = Some i).
        { eapply generate_reset_env'_preserves_find; eauto. }
        exists (i :: rs). split.
        + simpl. rewrite Hfind, Hrs. reflexivity.
        + rewrite Hrids, <- app_assoc. reflexivity.
    Qed.

    Lemma generate_reset_env_rids:
      forall trs renv rids st st',
        generate_reset_env trs st = OK ((renv, rids), st') ->
        get_mappings (map fst (resets_of trs)) renv = Some rids.
    Proof.
      intros trs renv rids st st' Hgen.
      unfold generate_reset_env in Hgen.
      destruct (generate_reset_env'_rids _ _ _ _ _ _ _ Hgen) as (rs & Hrs & Hrids).
      simpl in Hrids. subst rids. exact Hrs.
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
          match trconstr_targets tr, trconstrs_targets trs' with
          | Some tys1, Some tys2 => Some (tys1 ++ tys2)
          | _, _ => None
          end
      end.

    Definition generate_trconstr_constraint (e: trconstr): Sec (list constraint) :=
      match e with
      | TcDef x ck cexp  =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do xty   <- find_env x env;
          ret [((([rst_ty] ⊔ ckty) ⊔ expty), [xty])]
      | TcNext x ck exp =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [((([rst_ty] ⊔ ckty) ⊔ expty), [xty])]
      | TcCall _ [] _ _ _ _ => ret []
      | TcCall _ xs ck false f exps =>
          match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty [rst_ty] outtyp
          | None => error (MSG "Signature not found for: " :: [CTX f])
          end
      | TcCall x0 xs ck true f exps =>
          match find_signature f G with
          | Some n =>
              do ckty     <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp   <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp   <- mmap (fun x => find_env x env) xs;
              do rst_inst <- find_env x0 reset_env;
              generate_constraints n inptyp ckty [rst_inst] outtyp
          | None => error (MSG "Signature not found for: " :: [CTX f])
          end
      | TcReset x (Con ckr r true) f =>
          do rty      <- find_env r env;
          do rstckty  <- option_to_sec (assign_clk_type env base_ty ckr);
          do rst_inst <- find_env x reset_env;
          ret [(([rst_ty] ⊔ ([rty] ⊔ rstckty)), [rst_inst])]
      | TcReset x rck f =>
          do rckty    <- option_to_sec (assign_clk_type env base_ty rck);
          do rst_inst <- find_env x reset_env;
          ret [([rst_ty] ⊔ rckty, [rst_inst])]
      end.

    Fixpoint generate_trconstrs_constraints (es: list trconstr) : Sec (list constraint) :=
      match es with
      | [] => ret []
      | e :: es' =>
          do c  <- generate_trconstr_constraint e;
          do cs <- generate_trconstrs_constraints es';
          ret (c ++ cs)
      end.

    (** ** Generation is state-pure, hence a function of the syntax

        No branch above mints an identifier, so the constraints a
        transition constraint generates depend on the constraint alone
        and not on the state the generator happened to reach.  That is
        what lets a reordering of [s_tcs] permute the generated list
        instead of changing it. *)

    Lemma state_pure_generate_trconstr_constraint:
      forall e, state_pure (generate_trconstr_constraint e).
    Proof.
      intro e.
      assert (Hins : forall xs, state_pure (mmap (fun x => find_env x env) xs))
        by (intro xs; apply state_pure_mmap; intro x; apply state_pure_find_env).
      assert (Hexps : forall es,
                 state_pure (mmap (fun x => option_to_sec (assign_exp_type env x)) es))
        by (intro es; apply state_pure_mmap; intro x;
            apply state_pure_option_to_sec).
      assert (Hbase : forall (m: Sec (list constraint)), state_pure m -> state_pure m)
        by auto.
      clear Hbase.
      (* every branch is a chain of binds over pure steps; [simpl] may
         already have reduced some of them, so accept either form *)
      assert (Hstep : forall (B: Type) (m: Sec B) (g: B -> Sec (list constraint)),
                 state_pure m ->
                 (forall b, state_pure (g b)) ->
                 state_pure (bind m g))
        by (intros; apply state_pure_bind; auto).
      clear Hstep.
      destruct e as [x ck ce|x ck ex|x ck f|i xs ck rst f exps]; simpl;
        [ | |destruct ck as [|ckr r b]; [|destruct b]; simpl
          |destruct xs as [|y ys];
           [destruct rst; apply state_pure_ret
           |destruct rst; destruct (find_signature f G);
            try apply state_pure_error]];
        repeat (apply state_pure_bind;
                [first [apply state_pure_option_to_sec
                       |apply state_pure_find_env
                       |apply Hexps
                       |apply Hins
                       |apply state_pure_ret
                       |apply state_pure_error]
                |intro]);
        first [apply state_pure_ret
              |apply state_pure_generate_constraints].
    Qed.

    (** The total per-constraint form.  Purity makes this a function of
        the transition constraint alone, so a whole body's constraints
        are [concat] of a [map] -- and a reordering of the body permutes
        them. *)

    Definition tc_constraints (e: trconstr) : list constraint :=
      match generate_trconstr_constraint e init_state with
      | OK (c, _) => c
      | Error _ => []
      end.

    Lemma generate_trconstr_constraint_eq:
      forall e st c st',
        generate_trconstr_constraint e st = OK (c, st') ->
        c = tc_constraints e.
    Proof.
      intros e st c st' Hgen.
      unfold tc_constraints.
      destruct (generate_trconstr_constraint e init_state)
        as [[c0 st0]|] eqn:Hgen0.
      - eapply state_pure_det;
          [apply state_pure_generate_trconstr_constraint|exact Hgen|exact Hgen0].
      - destruct (state_pure_generate_trconstr_constraint
                    e st init_state c st' Hgen) as [_ Hgen'].
        rewrite Hgen0 in Hgen'. discriminate.
    Qed.

    Lemma state_pure_generate_trconstrs_constraints:
      forall es, state_pure (generate_trconstrs_constraints es).
    Proof.
      induction es as [|e es IH]; simpl.
      - apply state_pure_ret.
      - apply state_pure_bind;
          [apply state_pure_generate_trconstr_constraint|intro c].
        apply state_pure_bind; [exact IH|intro cs].
        apply state_pure_ret.
    Qed.

    Lemma generate_trconstrs_constraints_eq:
      forall es st c st',
        generate_trconstrs_constraints es st = OK (c, st') ->
        c = List.concat (map tc_constraints es).
    Proof.
      induction es as [|e es IH]; intros st c st' Hgen; simpl in *.
      - unfold ret in Hgen. now inversion Hgen.
      - eapply sec_bind_inv in Hgen as (ce & st1 & Hhd & Hgen).
        eapply sec_bind_inv in Hgen as (cs & st2 & Htl & Hret).
        unfold ret in Hret. inversion Hret; subst c st'.
        rewrite (generate_trconstr_constraint_eq _ _ _ _ Hhd).
        now rewrite (IH _ _ _ Htl).
    Qed.

    (** Reordering a system's transition constraints permutes the raw
        constraints it generates.  This is what the scheduler does. *)

    Lemma Permutation_List_concat:
      forall {A: Type} (l l': list (list A)),
        Permutation l l' ->
        Permutation (List.concat l) (List.concat l').
    Proof.
      intros A l l' Hperm.
      induction Hperm as [|x l l' Hperm IH|x y l|l1 l2 l3 H1 IH1 H2 IH2];
        simpl.
      - constructor.
      - now apply Permutation_app_head.
      - rewrite 2 app_assoc. apply Permutation_app_tail.
        apply Permutation_app_comm.
      - eapply Permutation_trans; eauto.
    Qed.

    Theorem generate_trconstrs_constraints_Permutation:
      forall es es' st c st' st2 c2 st2',
        Permutation es es' ->
        generate_trconstrs_constraints es st = OK (c, st') ->
        generate_trconstrs_constraints es' st2 = OK (c2, st2') ->
        Permutation c c2.
    Proof.
      intros es es' st c st' st2 c2 st2' Hperm Hgen Hgen2.
      rewrite (generate_trconstrs_constraints_eq _ _ _ _ Hgen).
      rewrite (generate_trconstrs_constraints_eq _ _ _ _ Hgen2).
      apply Permutation_List_concat, Permutation_map, Hperm.
    Qed.

    (** Whether generation *succeeds* is a property of the syntax alone
        too, so it also survives a reordering.  That is what lets the
        run on the scheduled body be constructed from the run on the
        original one instead of assumed alongside it. *)

    Definition tc_generates (e: trconstr) : Prop :=
      exists c, generate_trconstr_constraint e init_state = OK (c, init_state).

    Lemma generate_trconstrs_constraints_ok_elems:
      forall es st c st',
        generate_trconstrs_constraints es st = OK (c, st') ->
        Forall tc_generates es.
    Proof.
      induction es as [|e es IH]; intros st c st' Hgen; [constructor|].
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Hhd & Hgen).
      eapply sec_bind_inv in Hgen as (cs & st2 & Htl & _).
      constructor; [|eapply IH; exact Htl].
      exists c1.
      destruct (state_pure_generate_trconstr_constraint e st init_state c1 st1 Hhd)
        as [_ Hok]. exact Hok.
    Qed.

    Lemma generate_trconstrs_constraints_ok_from_elems:
      forall es st,
        Forall tc_generates es ->
        exists c, generate_trconstrs_constraints es st = OK (c, st).
    Proof.
      induction es as [|e es IH]; intros st Hall.
      - exists []. reflexivity.
      - inversion Hall as [|e' es' Hhd0 Htl]; subst.
        destruct Hhd0 as (c1 & Hhd).
        destruct (IH st Htl) as (cs & Hgen).
        destruct (state_pure_generate_trconstr_constraint
                    e init_state st c1 init_state Hhd) as [_ Hhd'].
        exists (c1 ++ cs). simpl. unfold bind at 1.
        rewrite Hhd'. unfold bind. rewrite Hgen. reflexivity.
    Qed.

    Lemma generate_trconstrs_constraints_Permutation_ok:
      forall es es' st c st' st2,
        Permutation es es' ->
        generate_trconstrs_constraints es st = OK (c, st') ->
        exists c', generate_trconstrs_constraints es' st2 = OK (c', st2)
                   /\ Permutation c c'.
    Proof.
      intros es es' st c st' st2 Hperm Hgen.
      assert (Hall : Forall tc_generates es')
        by (eapply Permutation_Forall;
            [exact Hperm|eapply generate_trconstrs_constraints_ok_elems; exact Hgen]).
      destruct (generate_trconstrs_constraints_ok_from_elems es' st2 Hall)
        as (c' & Hgen').
      exists c'. split; [exact Hgen'|].
      eapply generate_trconstrs_constraints_Permutation; eauto.
    Qed.

    Definition trconstr_reset_keys (tr: trconstr) : list ident :=
      match tr with
      | TcReset x _ _ => [x]
      | TcCall x _ _ true _ _ => [x]
      | _ => []
      end.

    Fixpoint trconstrs_reset_keys (trs: list trconstr) : list ident :=
      match trs with
      | [] => []
      | tr :: trs' => trconstr_reset_keys tr ++ trconstrs_reset_keys trs'
      end.

    (** The instances whose reset type the generator looks up are exactly
        the ones the system resets: a step call carrying [rst = true] has
        a matching [TcReset] elsewhere in the list, by
        [reset_consistency]. *)

    Lemma Reset_in_resets_of:
      forall trs x,
        Reset_in x trs ->
        In x (map fst (resets_of trs)).
    Proof.
      induction trs as [|tr trs IH]; intros x Hin.
      - inversion Hin.
      - inversion Hin as [tr' trs' Hhd|tr' trs' Htl]; subst.
        + inversion Hhd; subst. simpl. now left.
        + destruct tr as [y ck ce|y ck e|y ck f|y ys ck b f es]; simpl;
            try (now apply IH).
          right. now apply IH.
    Qed.

    Lemma resets_of_Reset_in:
      forall trs x,
        In x (map fst (resets_of trs)) ->
        Reset_in x trs.
    Proof.
      induction trs as [|tr trs IH]; intros x Hin; [inversion Hin|].
      destruct tr as [y ck ce|y ck e|y ck f|y ys ck b g es]; simpl in Hin;
        try (now right; apply IH).
      destruct Hin as [Heq|Hin].
      - subst y. left. constructor.
      - right. now apply IH.
    Qed.

    Lemma In_trconstrs_reset_keys_call:
      forall trs i xs ck f es,
        In (TcCall i xs ck true f es) trs ->
        In i (trconstrs_reset_keys trs).
    Proof.
      induction trs as [|tr trs IH]; intros i xs ck f es Hin; [inversion Hin|].
      simpl. apply in_or_app.
      destruct Hin as [Heq|Hin].
      - subst tr. left. simpl. now left.
      - right. eapply IH; exact Hin.
    Qed.

    Lemma trconstrs_reset_keys_cases:
      forall trs x,
        In x (trconstrs_reset_keys trs) ->
        Reset_in x trs \/ Step_with_reset_in x true trs.
    Proof.
      induction trs as [|tr trs IH]; intros x Hin; [inversion Hin|].
      simpl in Hin. apply in_app_iff in Hin as [Hhd|Htl].
      - destruct tr as [y ck ce|y ck e|y ck f|y ys ck [|] f es];
          simpl in Hhd; try contradiction.
        + destruct Hhd as [Heq|[]]; subst y.
          left. left. constructor.
        + destruct Hhd as [Heq|[]]; subst y.
          right. left. constructor.
      - destruct (IH x Htl) as [H|H]; [left|right]; now right.
    Qed.

    Lemma trconstrs_reset_keys_in_resets:
      forall trs x,
        reset_consistency trs ->
        In x (trconstrs_reset_keys trs) ->
        In x (map fst (resets_of trs)).
    Proof.
      intros trs x Hcons Hin.
      apply Reset_in_resets_of.
      destruct (trconstrs_reset_keys_cases _ _ Hin) as [H|H]; [exact H|].
      exact (Hcons x true H).
    Qed.

    (** The scoping facts a [TcCall]'s actuals enjoy, read off the
        clocking judgement alone.  Both branches of the case analysis
        below need exactly this, and so does the two-accumulator
        preservation argument, which sees the actuals only through the
        generator's equations.  Stated over those equations for that
        reason rather than over [assign_clk_type] and friends. *)

    Lemma wc_trconstr_call_actuals_scoped:
      forall P vars scope i xs ck rst f es ckty inptyp outtyp
             sa sb sc sd se sf,
        wc_env vars ->
        Clo.wc_trconstr P vars (TcCall i xs ck rst f es) ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        option_to_sec (assign_clk_type env base_ty ck) sa = OK (ckty, sb) ->
        mmap (fun x => option_to_sec (assign_exp_type env x)) es sc
          = OK (inptyp, sd) ->
        mmap (fun x => find_env x env) xs se = OK (outtyp, sf) ->
        call_actuals_scoped scope inptyp ckty outtyp.
    Proof.
      intros P vars scope i xs ck rst f es ckty inptyp outtyp
             sa sb sc sd se sf Henv Hwc Hvars Hbase Hck Hinptyp Houttyp.
      inversion Hwc as [| | |i0 xs0 ck0 rst0 f0 es0 s P0 sub
                             Hfindsys Hinputs Houtputs]; subst.
      assert (Hckopt : assign_clk_type env base_ty ck = Some ckty).
      { unfold option_to_sec in Hck.
        destruct (assign_clk_type env base_ty ck) eqn:Hck'; try discriminate.
        inversion Hck; subst. reflexivity. }
      repeat split.
      - eapply (mmap_assign_exp_type_scoped scope es inptyp sc sd).
        + eapply (wc_call_args_scoped vars scope sub ck (SynStc.s_in s) es); eauto.
        + exact Hinptyp.
      - eapply (assign_clk_type_scoped env base_ty scope ck ckty);
          [exact Hbase| |exact Hckopt].
        intros z Hz.
        assert (Hinm : InMembers z vars) by (eapply wc_tc_clock_free_in_vars; eauto).
        exact (Hvars z Hinm).
      - eapply (SC.mmap_find_env_scoped env scope xs outtyp se sf).
        + intros y Hy.
          eapply (wc_call_outs_scoped vars scope sub ck (SynStc.s_out s) xs); eauto.
        + exact Houttyp.
    Qed.

    Theorem generate_trconstr_constraint_scoped_on_keys:
      forall P vars scope tr cns st st',
        secglobal_scoped G ->
        wc_env vars ->
        Clo.wc_trconstr P vars tr ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1,
            In x (trconstr_reset_keys tr) ->
            find_env x reset_env st0 = OK (ty, st1) ->
            In ty scope) ->
        generate_trconstr_constraint tr st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros P vars scope tr cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      destruct tr as [x ck ce|x ck e|x ck f|x0 xs ck b f exps].
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
        eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
        unfold ret in Hgen.
        inversion Hgen; subst; clear Hgen.
        inversion Hwc as [x' ck' ce' Hx Hce| | |]; subst.
        assert (Hckopt : assign_clk_type env base_ty ck = Some ckty).
        { unfold option_to_sec in Hck.
          destruct (assign_clk_type env base_ty ck) eqn:Hck'; try discriminate.
          inversion Hck; subst. reflexivity. }
        assert (Hexpopt : assign_cexp_type env ce = Some expty).
        { unfold option_to_sec in Hexp.
          destruct (assign_cexp_type env ce) eqn:Hexp'; try discriminate.
          inversion Hexp; subst. reflexivity. }
        assert (Hckscope : st_scoped scope ckty).
        { eapply (assign_clk_type_scoped env base_ty scope ck ckty); [exact Hbase| |exact Hckopt].
          intros z Hz.
          pose proof (wc_clock_cexp _ _ _ Henv Hce) as Hceck.
          assert (Hinm : InMembers z vars) by (eapply wc_clock_free_in_vars; eauto).
          exact (Hvars z Hinm). }
        assert (Hexpscope : st_scoped scope expty).
        { eapply (assign_cexp_type_scoped env scope ce expty); [|exact Hexpopt].
          intros z Hz.
          assert (Hinm : InMembers z vars) by (eapply wc_caexp_free_in_vars; eauto).
          exact (Hvars z Hinm). }
        assert (Hrscope : st_scoped scope [rst_ty]).
        { apply st_scoped_singleton. exact Hrst. }
        assert (Hlhsscope : st_scoped scope (([rst_ty] ⊔ ckty) ⊔ expty)).
        { apply st_scoped_merge.
          - apply st_scoped_merge; eauto.
          - exact Hexpscope. }
        constructor.
        + intros y Hin.
          unfold constraint_scope in Hin. simpl in Hin.
          rewrite in_app_iff in Hin.
          destruct Hin as [Hin|Hin].
          * exact (Hlhsscope _ Hin).
          * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
            eapply SC.find_env_in_scope
              with (A := clock) (vars := vars) (scope := scope)
                   (x := x) (ann := ck) (st := st2) (st' := st'); eauto.
        + constructor.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
        eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
        unfold ret in Hgen.
        inversion Hgen; subst; clear Hgen.
        inversion Hwc as [|x' ck' e' Hx Hexpwc| |]; subst.
        assert (Hckopt : assign_clk_type env base_ty ck = Some ckty).
        { unfold option_to_sec in Hck.
          destruct (assign_clk_type env base_ty ck) eqn:Hck'; try discriminate.
          inversion Hck; subst. reflexivity. }
        assert (Hexpopt : assign_exp_type env e = Some expty).
        { unfold option_to_sec in Hexp.
          destruct (assign_exp_type env e) eqn:Hexp'; try discriminate.
          inversion Hexp; subst. reflexivity. }
        assert (Hckscope : st_scoped scope ckty).
        { eapply (assign_clk_type_scoped env base_ty scope ck ckty); [exact Hbase| |exact Hckopt].
          intros z Hz.
          pose proof (wc_clock_exp _ _ _ Henv Hexpwc) as Hckwc.
          assert (Hinm : InMembers z vars) by (eapply wc_clock_free_in_vars; eauto).
          exact (Hvars z Hinm). }
        assert (Hexpscope : st_scoped scope expty).
        { eapply (assign_exp_type_scoped env scope e expty); [|exact Hexpopt].
          intros z Hz.
          assert (Hinm : InMembers z vars) by (eapply wc_aexp_free_in_vars; eauto).
          exact (Hvars z Hinm). }
        assert (Hrscope : st_scoped scope [rst_ty]).
        { apply st_scoped_singleton. exact Hrst. }
        assert (Hlhsscope : st_scoped scope (([rst_ty] ⊔ ckty) ⊔ expty)).
        { apply st_scoped_merge.
          - apply st_scoped_merge; eauto.
          - exact Hexpscope. }
        constructor.
        + intros y Hin.
          unfold constraint_scope in Hin. simpl in Hin.
          rewrite in_app_iff in Hin.
          destruct Hin as [Hin|Hin].
          * exact (Hlhsscope _ Hin).
          * simpl in Hin. destruct Hin as [Heq|[]]. subst y.
            eapply SC.find_env_in_scope
              with (A := clock) (vars := vars) (scope := scope)
                   (x := x) (ann := ck) (st := st2) (st' := st'); eauto.
        + constructor.
      - simpl in Hgen.
        inversion Hwc as [| |x' ck' f' Hckwc|]; subst.
        destruct ck as [|ck0 r0 b0].
        + simpl in Hgen.
          eapply sec_bind_inv in Hgen as (rckty & st1 & Hck & Hgen).
          eapply sec_bind_inv in Hgen as (rst_inst & st2 & Hrstinst & Hgen).
          unfold ret in Hgen.
          inversion Hgen; subst; clear Hgen.
          assert (Hckopt : assign_clk_type env base_ty Cbase = Some rckty).
          { unfold option_to_sec in Hck.
            simpl in Hck. inversion Hck; subst. reflexivity. }
          assert (Hckscope : st_scoped scope rckty).
          { eapply (assign_clk_type_scoped env base_ty scope Cbase rckty); [exact Hbase| |exact Hckopt].
            intros z Hz. inversion Hz. }
          assert (Hlhsscope : st_scoped scope ([rst_ty] ⊔ rckty)).
          { eapply st_scoped_merge.
            - apply st_scoped_singleton. exact Hrst.
            - exact Hckscope. }
          constructor.
          * intros y Hin.
            unfold constraint_scope in Hin. simpl in Hin.
            rewrite in_app_iff in Hin.
            destruct Hin as [Hin|Hin].
            -- exact (Hlhsscope _ Hin).
            -- simpl in Hin. destruct Hin as [Heq|[]]. subst y.
               eapply Hreset; eauto.
               simpl. now left.
          * constructor.
        + destruct b0.
          * simpl in Hgen.
            eapply sec_bind_inv in Hgen as (rty & st1 & Hr & Hgen).
            eapply sec_bind_inv in Hgen as (rstckty & st2 & Hck & Hgen).
            eapply sec_bind_inv in Hgen as (rst_inst & st3 & Hrstinst & Hgen).
            unfold ret in Hgen.
            inversion Hgen; subst; clear Hgen.
            unfold find_env in Hr.
            destruct (Env.find r0 env) as [rty'|] eqn:Hrfind; try discriminate.
            unfold ret in Hr. inversion Hr; subst rty st1.
            assert (Hrstckopt : assign_clk_type env base_ty ck0 = Some rstckty).
            { unfold option_to_sec in Hck.
              destruct (assign_clk_type env base_ty ck0) eqn:Hck'; try discriminate.
              inversion Hck; subst. reflexivity. }
            assert (Hrscope : st_scoped scope [rty']).
            { apply st_scoped_singleton.
              assert (Hinm : InMembers r0 vars) by (eapply wc_clock_free_in_vars; eauto; constructor 1).
              destruct (Hvars r0 Hinm) as (ty & Hfind & Hinscope).
              rewrite Hrfind in Hfind. inversion Hfind; subst. exact Hinscope. }
            assert (Hrstckscope : st_scoped scope rstckty).
            { eapply (assign_clk_type_scoped env base_ty scope ck0 rstckty); [exact Hbase| |exact Hrstckopt].
              intros z Hz.
              assert (Hinm : InMembers z vars) by (eapply wc_clock_free_in_vars; eauto).
              exact (Hvars z Hinm). }
            assert (Hlhsscope : st_scoped scope ([rst_ty] ⊔ ([rty'] ⊔ rstckty))).
            { eapply st_scoped_merge.
              - apply st_scoped_singleton. exact Hrst.
              - eapply st_scoped_merge; eauto. }
            constructor.
            -- intros y Hin.
               unfold constraint_scope in Hin. simpl in Hin.
               rewrite in_app_iff in Hin.
               destruct Hin as [Hin|Hin].
               ++ exact (Hlhsscope _ Hin).
               ++ simpl in Hin. destruct Hin as [Heq|[]]. subst y.
                  eapply Hreset; eauto.
                  simpl. now left.
            -- constructor.
          * simpl in Hgen.
            eapply sec_bind_inv in Hgen as (rckty & st1 & Hck & Hgen).
            eapply sec_bind_inv in Hgen as (rst_inst & st2 & Hrstinst & Hgen).
            unfold ret in Hgen.
            inversion Hgen; subst; clear Hgen.
            assert (Hckopt : assign_clk_type env base_ty (Con ck0 r0 false) = Some rckty).
            { unfold option_to_sec in Hck.
              simpl in Hck.
              destruct (assign_clk_type env base_ty ck0) as [ckty'|] eqn:Hck0; try discriminate.
              destruct (Env.find r0 env) as [xty'|] eqn:Hr0; try discriminate.
              inversion Hck; subst. simpl. rewrite Hck0, Hr0. reflexivity. }
            assert (Hckscope : st_scoped scope rckty).
            { eapply (assign_clk_type_scoped env base_ty scope (Con ck0 r0 false) rckty); [exact Hbase| |exact Hckopt].
              intros z Hz.
              assert (Hinm : InMembers z vars) by (eapply wc_clock_free_in_vars; eauto).
              exact (Hvars z Hinm). }
            assert (Hlhsscope : st_scoped scope ([rst_ty] ⊔ rckty)).
            { eapply st_scoped_merge.
              - apply st_scoped_singleton. exact Hrst.
              - exact Hckscope. }
            constructor.
            -- intros y Hin.
               unfold constraint_scope in Hin. simpl in Hin.
               rewrite in_app_iff in Hin.
               destruct Hin as [Hin|Hin].
               ++ exact (Hlhsscope _ Hin).
               ++ simpl in Hin. destruct Hin as [Heq|[]]. subst y.
                  eapply Hreset; eauto.
                  simpl. now left.
            -- constructor.
      - destruct b.
        + simpl in Hgen.
          destruct xs as [|x1 xs']; simpl in Hgen.
          * unfold ret in Hgen. inversion Hgen; subst. constructor.
          * destruct (find_signature f G) as [sig|] eqn:Hsig; try discriminate.
            eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
            eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinptyp & Hgen).
            eapply sec_bind_inv in Hgen as (outtyp & st3 & Houttyp & Hgen).
            eapply sec_bind_inv in Hgen as (rst_inst & st4 & Hrstinst & Hgen).
            destruct (wc_trconstr_call_actuals_scoped
                        P vars scope x0 (x1 :: xs') ck true f exps
                        ckty inptyp outtyp _ _ _ _ _ _
                        Henv Hwc Hvars Hbase Hck Hinptyp Houttyp)
              as (HinpScope & Hckscope & HoutScope).
            assert (Hrstscope : In rst_inst scope).
            { eapply Hreset; eauto.
              simpl. now left. }
            eapply (generate_constraints_scoped sig scope inptyp ckty [rst_inst] outtyp cns st4 st');
              [eapply Hscoped; eauto
              |exact HinpScope
              |exact Hckscope
              |apply st_scoped_singleton; exact Hrstscope
              |exact HoutScope
              |exact Hgen].
        + simpl in Hgen.
          destruct xs as [|x1 xs']; simpl in Hgen.
          * unfold ret in Hgen. inversion Hgen; subst. constructor.
          * destruct (find_signature f G) as [sig|] eqn:Hsig; try discriminate.
            eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
            eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinptyp & Hgen).
            eapply sec_bind_inv in Hgen as (outtyp & st3 & Houttyp & Hgen).
            destruct (wc_trconstr_call_actuals_scoped
                        P vars scope x0 (x1 :: xs') ck false f exps
                        ckty inptyp outtyp _ _ _ _ _ _
                        Henv Hwc Hvars Hbase Hck Hinptyp Houttyp)
              as (HinpScope & Hckscope & HoutScope).
            eapply (generate_constraints_scoped sig scope inptyp ckty [rst_ty] outtyp cns st3 st');
              [eapply Hscoped; eauto
              |exact HinpScope
              |exact Hckscope
              |apply st_scoped_singleton; exact Hrst
              |exact HoutScope
              |exact Hgen].
    Qed.

    Theorem generate_trconstrs_constraints_scoped_on_keys:
      forall P vars scope trs cns st st',
        secglobal_scoped G ->
        wc_env vars ->
        Forall (Clo.wc_trconstr P vars) trs ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1,
            In x (trconstrs_reset_keys trs) ->
            find_env x reset_env st0 = OK (ty, st1) ->
            In ty scope) ->
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
        + eapply generate_trconstr_constraint_scoped_on_keys; eauto.
          intros x ty st0 stx Hin Hfind.
          eapply Hreset; eauto.
          apply in_or_app. now left.
        + eapply IH; eauto.
          intros x ty st0 stx Hin Hfind.
          eapply Hreset; eauto.
          apply in_or_app. now right.
    Qed.

    Theorem generate_trconstr_constraint_scoped:
      forall P vars scope tr cns st st',
        secglobal_scoped G ->
        wc_env vars ->
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
      refine (generate_trconstr_constraint_scoped_on_keys
                P vars scope tr cns st st'
                Hscoped Henv Hwc Hvars Hbase Hrst _ Hgen).
      intros x ty st0 st1 _ Hfind.
      eapply Hreset; eauto.
    Qed.

    (** This shows that translated STC constraints stay inside the visible scope plus the reset-instance keys read from the reset environment.  It is the local scopedness fact used to build STC signatures. *)
    Theorem generate_trconstrs_constraints_scoped:
      forall P vars scope trs cns st st',
        secglobal_scoped G ->
        wc_env vars ->
        Forall (Clo.wc_trconstr P vars) trs ->
        vars_env_scoped vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1, find_env x reset_env st0 = OK (ty, st1) -> In ty scope) ->
        generate_trconstrs_constraints trs st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros P vars scope trs cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      refine (generate_trconstrs_constraints_scoped_on_keys
                P vars scope trs cns st st'
                Hscoped Henv Hwc Hvars Hbase Hrst _ Hgen).
      intros x ty st0 st1 _ Hfind.
      eapply Hreset; eauto.
    Qed.

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
      env_injective env ->
      NoDup (Def.defined_tc tr) ->
      generate_trconstr_constraint tr st = OK (cns, st') ->
      exists tys,
        trconstr_targets tr = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    intros tr cns st st' Hinj Hnd Hgen.
    destruct tr as [x ck ce|x ck e|x ck f|x0 xs ck b f exps].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst cns st'; clear Hgen.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Henv; try discriminate.
      inversion Hfind; subst xty st3.
      exists [xty']. split.
      + simpl. rewrite Henv. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (expty & st2 & Hexp & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hgen).
      unfold ret in Hgen. inversion Hgen; subst cns st'; clear Hgen.
      unfold find_env in Hfind.
      destruct (Env.find x env) as [xty'|] eqn:Henv; try discriminate.
      inversion Hfind; subst xty st3.
      exists [xty']. split.
      + simpl. rewrite Henv. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - destruct ck as [|ck0 r0 b0].
      + simpl in Hgen.
        eapply sec_bind_inv in Hgen as (rckty & st1 & Hck & Hgen).
        eapply sec_bind_inv in Hgen as (rst_inst & st2 & Hfind & Hgen).
        unfold ret in Hgen. inversion Hgen; subst cns st'; clear Hgen.
        unfold find_env in Hfind.
        destruct (Env.find x reset_env) as [rst_inst'|] eqn:Henv; try discriminate.
        inversion Hfind; subst rst_inst st2.
        exists [rst_inst']. split.
        * simpl. rewrite Henv. reflexivity.
        * split; [reflexivity|].
          unfold wf_constraints. split.
          -- constructor; [intro Hin; inversion Hin|constructor].
          -- constructor; [simpl; reflexivity|constructor].
      + destruct b0.
        * simpl in Hgen.
          eapply sec_bind_inv in Hgen as (rty & st1 & Hr & Hgen).
          eapply sec_bind_inv in Hgen as (rstckty & st2 & Hck & Hgen).
          eapply sec_bind_inv in Hgen as (rst_inst & st3 & Hfind & Hgen).
          unfold ret in Hgen. inversion Hgen; subst cns st'; clear Hgen.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Henv; try discriminate.
          inversion Hfind; subst rst_inst st3.
          exists [rst_inst']. split.
          -- simpl. rewrite Henv. reflexivity.
          -- split; [reflexivity|].
             unfold wf_constraints. split.
             ++ constructor; [intro Hin; inversion Hin|constructor].
             ++ constructor; [simpl; reflexivity|constructor].
        * simpl in Hgen.
          eapply sec_bind_inv in Hgen as (rckty & st1 & Hck & Hgen).
          eapply sec_bind_inv in Hgen as (rst_inst & st2 & Hfind & Hgen).
          unfold ret in Hgen. inversion Hgen; subst cns st'; clear Hgen.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Henv; try discriminate.
          inversion Hfind; subst rst_inst st2.
          exists [rst_inst']. split.
          -- simpl. rewrite Henv. reflexivity.
          -- split; [reflexivity|].
             unfold wf_constraints. split.
             ++ constructor; [intro Hin; inversion Hin|constructor].
             ++ constructor; [simpl; reflexivity|constructor].
    - destruct b.
      + destruct xs as [|x1 xs'].
        * simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst cns st'.
          exists []. split; [reflexivity|].
          split; [reflexivity|unfold wf_constraints; split; constructor].
        * simpl in Hgen.
          destruct (find_signature f G) as [sig|] eqn:Hsig; try discriminate.
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinptyp & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st3 & Houttyp & Hgen).
          eapply sec_bind_inv in Hgen as (rst_inst & st4 & HgenRst & Hgen).
          pose proof (mmap_find_env_inv (x1 :: xs') outtyp st2 st3 Houttyp) as Houts.
          destruct Houts as [_ Hmapouts].
          assert (Hndout : NoDup outtyp).
          { eapply get_mappings_nodup; eauto. }
          destruct (generate_constraints_shape sig inptyp ckty [rst_inst] outtyp cns st4 st'
                    Hndout Hgen) as [Hwf Hsnd].
          exists outtyp. split.
          -- simpl. exact Hmapouts.
          -- split; [exact Hsnd|exact Hwf].
      + destruct xs as [|x1 xs'].
        * simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst cns st'.
          exists []. split; [reflexivity|].
          split; [reflexivity|unfold wf_constraints; split; constructor].
        * simpl in Hgen.
          destruct (find_signature f G) as [sig|] eqn:Hsig; try discriminate.
          eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
          eapply sec_bind_inv in Hgen as (inptyp & st2 & Hinptyp & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st3 & Houttyp & Hgen).
          pose proof (mmap_find_env_inv (x1 :: xs') outtyp st2 st3 Houttyp) as Houts.
          destruct Houts as [_ Hmapouts].
          assert (Hndout : NoDup outtyp).
          { eapply get_mappings_nodup; eauto. }
          destruct (generate_constraints_shape sig inptyp ckty [rst_ty] outtyp cns st3 st'
                    Hndout Hgen) as [Hwf Hsnd].
          exists outtyp. split.
          -- simpl. exact Hmapouts.
          -- split; [exact Hsnd|exact Hwf].
  Qed.

  Theorem generate_trconstrs_constraints_targets:
    forall trs cns st st',
      env_injective env ->
      NoDup (Def.defined trs) ->
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      exists tys,
        trconstrs_targets trs = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys.
  Proof.
    induction trs as [|tr trs IH]; intros cns st st' Hinj Hnd Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; reflexivity.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      simpl in Hnd.
      apply NoDup_app'_iff in Hnd as [Hnd1 [Hnd2 _]].
      edestruct generate_trconstr_constraint_shape
        as (tys1 & Htys1 & Hsnd1 & Hwf1); eauto.
      edestruct IH as (tys2 & Htys2 & Hsnd2); eauto.
      exists (tys1 ++ tys2). split.
      + simpl. rewrite Htys1, Htys2. reflexivity.
      + replace (map snd (c1 ++ c2)) with (map snd c1 ++ map snd c2).
        * rewrite Hsnd1, Hsnd2, map_app. reflexivity.
        * symmetry. apply map_app.
  Qed.

  (** Every last has a [TcNext] that defines it, and the source of that
      constraint always contains [rst_ty].  The translation bridge uses
      this to discharge the Obc reset method's memory initialisations,
      which are exactly the constraints [rst_ty] |- [last]. *)

  Lemma generate_trconstrs_constraints_last_source:
    forall trs cns st st' x xty,
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      In x (lasts_of trs) ->
      Env.find x env = Some xty ->
      exists src, List.In (src, [xty]) cns /\ List.In rst_ty src.
  Proof.
    induction trs as [|tr trs IH]; intros cns st st' x xty Hgen Hin Hfind.
    - inversion Hin.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      destruct tr as [y ck ce|y ck e|y ck f|y ys ck b f exps]; simpl in Hin.
      2: destruct Hin as [Heq|Hin].
      2:{ (* the defining [TcNext] *)
        subst y. simpl in Htr.
        eapply sec_bind_inv in Htr as (ckty & sa & Hck & Htr).
        eapply sec_bind_inv in Htr as (ety & sb & He & Htr).
        eapply sec_bind_inv in Htr as (yty & sc & Hy & Hret1).
        unfold ret in Hret1. inversion Hret1; subst c1 st1.
        unfold find_env in Hy.
        rewrite Hfind in Hy. unfold ret in Hy. inversion Hy; subst yty sc.
        exists (([rst_ty] ⊔ ckty) ⊔ ety). split.
        - apply in_or_app. left. simpl. now left.
        - apply in_merge_left, in_merge_left. simpl. now left. }
      all: destruct (IH c2 st1 st2 x xty Htrs Hin Hfind) as (src & Hinc & Hrst);
           exists src; split; [apply in_or_app; now right|exact Hrst].
  Qed.

  (** Likewise every reset instance has a [TcReset] whose source
      contains [rst_ty], on either shape of reset clock.  This discharges
      the Obc reset method's instance resets for the instances the system
      actually resets. *)

  Lemma generate_trconstrs_constraints_reset_source:
    forall trs cns st st' o rst_inst,
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      List.In o (map fst (resets_of trs)) ->
      Env.find o reset_env = Some rst_inst ->
      exists src, List.In (src, [rst_inst]) cns /\ List.In rst_ty src.
  Proof.
    induction trs as [|tr trs IH]; intros cns st st' o rst_inst Hgen Hin Hfind.
    - inversion Hin.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      destruct tr as [y ck ce|y ck e|y ck f|y ys ck b f exps]; simpl in Hin.
      3: destruct Hin as [Heq|Hin].
      3:{ (* the defining [TcReset] *)
        subst y.
        destruct ck as [|ck0 r0 [|]]; simpl in Htr.
        - (* Cbase *)
          eapply sec_bind_inv in Htr as (ckty & sa & Hck & Htr).
          eapply sec_bind_inv in Htr as (ri & sb & Hri & Hret1).
          unfold ret in Hret1. inversion Hret1; subst c1 st1.
          unfold find_env in Hri. rewrite Hfind in Hri.
          unfold ret in Hri. inversion Hri; subst ri sb.
          exists ([rst_ty] ⊔ ckty). split.
          + apply in_or_app. left. simpl. now left.
          + apply in_merge_left. simpl. now left.
        - (* Con _ _ true *)
          eapply sec_bind_inv in Htr as (rty & sa & Hr & Htr).
          eapply sec_bind_inv in Htr as (rstckty & sb & Hrck & Htr).
          eapply sec_bind_inv in Htr as (ri & sc & Hri & Hret1).
          unfold ret in Hret1. inversion Hret1; subst c1 st1.
          unfold find_env in Hri. rewrite Hfind in Hri.
          unfold ret in Hri. inversion Hri; subst ri sc.
          exists ([rst_ty] ⊔ ([rty] ⊔ rstckty)). split.
          + apply in_or_app. left. simpl. now left.
          + apply in_merge_left. simpl. now left.
        - (* Con _ _ false *)
          eapply sec_bind_inv in Htr as (ckty & sa & Hck & Htr).
          eapply sec_bind_inv in Htr as (ri & sb & Hri & Hret1).
          unfold ret in Hret1. inversion Hret1; subst c1 st1.
          unfold find_env in Hri. rewrite Hfind in Hri.
          unfold ret in Hri. inversion Hri; subst ri sb.
          exists ([rst_ty] ⊔ ckty). split.
          + apply in_or_app. left. simpl. now left.
          + apply in_merge_left. simpl. now left. }
      all: destruct (IH c2 st1 st2 o rst_inst Htrs Hin Hfind) as (src & Hinc & Hrst);
           exists src; split; [apply in_or_app; now right|exact Hrst].
  Qed.

  (** The list generator is a plain concatenation of the per-trconstr
      blocks, with the fresh-name state threaded left to right.  The
      translation bridge pairs these blocks with the Obc ones. *)

  Lemma generate_trconstrs_constraints_blocks:
    forall trs cns st st',
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      exists blocks,
        cns = List.concat blocks
        /\ Forall2 (fun tr blk =>
                      exists sa sb, generate_trconstr_constraint tr sa = OK (blk, sb))
                   trs blocks.
  Proof.
    induction trs as [|tr trs IH]; intros cns st st' Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; [reflexivity|constructor].
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Htr & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Htrs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      destruct (IH c2 st1 st2 Htrs) as (blocks & Hblocks & Hall).
      exists (c1 :: blocks). split.
      + simpl. f_equal. exact Hblocks.
      + constructor; [|exact Hall].
        exists st, st1. exact Htr.
  Qed.

  (** Well-formedness of the raw constraints reduces to distinctness of
      the targets: the generator already emits exactly one singleton
      target per definition. *)

  Lemma generate_trconstrs_constraints_wf:
    forall trs cns st st' tys,
      env_injective env ->
      NoDup (Def.defined trs) ->
      generate_trconstrs_constraints trs st = OK (cns, st') ->
      trconstrs_targets trs = Some tys ->
      NoDup tys ->
      wf_constraints cns.
  Proof.
    intros trs cns st st' tys Hinj Hnd Hgen Htys Hndtys.
    destruct (generate_trconstrs_constraints_targets trs cns st st' Hinj Hnd Hgen)
      as (tys' & Htys' & Hsnd).
    rewrite Htys in Htys'. inversion Htys'; subst tys'.
    split.
    - rewrite Hsnd. apply nodup_singleton_map. exact Hndtys.
    - clear -Hsnd.
      revert tys Hsnd.
      induction cns as [|[l r] cns IH]; intros tys Hsnd.
      + constructor.
      + destruct tys as [|ty tys]; simpl in Hsnd; try discriminate.
        inversion Hsnd; subst r.
        constructor; [reflexivity|].
        eapply IH; eauto.
  Qed.

  Lemma trconstr_targets_contains_defined_tc:
    forall tr x ty tys,
      trconstr_targets tr = Some tys ->
      Def.Is_defined_in_tc x tr ->
      Env.find x env = Some ty ->
      In ty tys.
  Proof.
    intros tr x ty tys Htys Hdef Hfind.
    destruct tr as [y ck ce|y ck e|x0 rck f|i xs ck rst f es].
    - inversion Hdef; subst; simpl in Htys.
      destruct (Env.find y env) as [yty|] eqn:Hy; try discriminate.
      inversion Htys; subst tys.
      inversion Hfind; subst. simpl. left. reflexivity.
    - inversion Hdef; subst; simpl in Htys.
      destruct (Env.find y env) as [yty|] eqn:Hy; try discriminate.
      inversion Htys; subst tys.
      inversion Hfind; subst. simpl. left. reflexivity.
    - inversion Hdef.
    - inversion Hdef; subst; simpl in Htys.
      edestruct get_mappings_in as (ty' & Hfind' & Hin'); eauto.
      rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin'.
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

  (** The targets of a whole [trconstr] list are exactly the security
      types of its variables, its lasts and its reset instances — in some
      order, since the three groups interleave along the list.  This is
      what makes a generated system signature [signature_good]: after
      [simplify] removes the hidden locals, lasts and reset instances,
      precisely the outputs remain. *)

  Lemma get_mappings_cons_inv:
    forall x xs e tys,
      get_mappings (x :: xs) e = Some tys ->
      exists ty tys',
        Env.find x e = Some ty
        /\ get_mappings xs e = Some tys'
        /\ tys = ty :: tys'.
  Proof.
    intros x xs e tys H.
    simpl in H.
    destruct (Env.find x e) as [ty|] eqn:Hx; simpl in H; try discriminate.
    destruct (get_mappings xs e) as [tys'|] eqn:Hxs; simpl in H; try discriminate.
    inversion H; subst. eauto.
  Qed.

  Lemma get_mappings_app_inv:
    forall xs ys e tys,
      get_mappings (xs ++ ys) e = Some tys ->
      exists txs tys',
        get_mappings xs e = Some txs
        /\ get_mappings ys e = Some tys'
        /\ tys = txs ++ tys'.
  Proof.
    induction xs as [|x xs IH]; intros ys e tys H.
    - simpl in H. exists [], tys. repeat split; auto.
    - rewrite <- app_comm_cons in H.
      apply get_mappings_cons_inv in H as (ty & tys0 & Hx & Hrest & Heq).
      apply IH in Hrest as (txs & tys' & Hxs & Hys & Heq').
      exists (ty :: txs), tys'. repeat split.
      + simpl. rewrite Hx, Hxs. reflexivity.
      + exact Hys.
      + subst. reflexivity.
  Qed.

  Lemma trconstrs_targets_perm:
    forall tcs tys vs ls rs,
      trconstrs_targets tcs = Some tys ->
      get_mappings (variables tcs) env = Some vs ->
      get_mappings (lasts_of tcs) env = Some ls ->
      get_mappings (map fst (resets_of tcs)) reset_env = Some rs ->
      Permutation tys (vs ++ ls ++ rs).
  Proof.
    induction tcs as [|tc tcs IH]; intros tys vs ls rs Htys Hvs Hls Hrs.
    - simpl in *. inversion Htys; inversion Hvs; inversion Hls; inversion Hrs.
      subst. constructor.
    - destruct tc as [x ck ce|x ck e|s ck f|i xs ck rst f es].
      + (* TcDef: contributes one variable *)
        simpl in Htys.
        cbn [variables flat_map variables_tc lasts_of resets_of map fst] in Hvs, Hls, Hrs.
        destruct (Env.find x env) as [tx|] eqn:Hx; try discriminate.
        destruct (trconstrs_targets tcs) as [tys'|] eqn:Htl; try discriminate.
        inversion Htys; subst tys.
        apply get_mappings_cons_inv in Hvs as (tx' & vs' & Hx' & Hvs' & Hvseq).
        rewrite Hx in Hx'. inversion Hx'; subst tx' vs.
        simpl. constructor. eapply IH; eauto.
      + (* TcNext: contributes one last *)
        simpl in Htys.
        cbn [variables flat_map variables_tc lasts_of resets_of map fst] in Hvs, Hls, Hrs.
        destruct (Env.find x env) as [tx|] eqn:Hx; try discriminate.
        destruct (trconstrs_targets tcs) as [tys'|] eqn:Htl; try discriminate.
        inversion Htys; subst tys.
        apply get_mappings_cons_inv in Hls as (tx' & ls' & Hx' & Hls' & Hlseq).
        rewrite Hx in Hx'. inversion Hx'; subst tx' ls.
        change (Permutation (tx :: tys') (vs ++ tx :: (ls' ++ rs))).
        apply Permutation_cons_app.
        eapply IH; eauto.
      + (* TcReset: contributes one reset instance *)
        simpl in Htys.
        cbn [variables flat_map variables_tc lasts_of resets_of map fst] in Hvs, Hls, Hrs.
        destruct (Env.find s reset_env) as [ts|] eqn:Hs; try discriminate.
        destruct (trconstrs_targets tcs) as [tys'|] eqn:Htl; try discriminate.
        inversion Htys; subst tys.
        apply get_mappings_cons_inv in Hrs as (ts' & rs' & Hs' & Hrs' & Hrseq).
        rewrite Hs in Hs'. inversion Hs'; subst ts' rs.
        change (Permutation (ts :: tys') (vs ++ ls ++ ts :: rs')).
        rewrite app_assoc.
        apply Permutation_cons_app.
        rewrite <- app_assoc.
        eapply IH; eauto.
      + (* TcCall: contributes its outputs *)
        simpl in Htys.
        cbn [variables flat_map variables_tc lasts_of resets_of map fst] in Hvs, Hls, Hrs.
        destruct (get_mappings xs env) as [txs|] eqn:Hxs; try discriminate.
        destruct (trconstrs_targets tcs) as [tys'|] eqn:Htl; try discriminate.
        inversion Htys; subst tys.
        apply get_mappings_app_inv in Hvs as (txs' & vs' & Hxs' & Hvs' & Hvseq).
        rewrite Hxs in Hxs'. inversion Hxs'; subst txs' vs.
        rewrite <- app_assoc.
        apply Permutation_app_head.
        eapply IH; eauto.
  Qed.

  Lemma trconstrs_targets_contains_reset_ids':
    forall trs acc rids st rids' st' tys ty,
      generate_reset_env' trs acc rids st = OK ((reset_env, rids'), st') ->
      trconstrs_targets trs = Some tys ->
      In ty rids' ->
      In ty rids \/ In ty tys.
  Proof.
    induction trs as [|tr trs IH]; intros acc rids st rids' st' tys ty Hgen Htys Hin.
    - simpl in Hgen. inversion Hgen; subst rids' st'.
      simpl in Htys. inversion Htys; subst tys. auto.
    - simpl in Htys.
      destruct (trconstr_targets tr) as [tys1|] eqn:Hty1; try discriminate.
      destruct (trconstrs_targets trs) as [tys2|] eqn:Hty2; try discriminate.
      inversion Htys; subst tys.
      destruct tr as [x ck ce|x ck e|x ck f|x xs ck b f exps].
      1,2,4:
        simpl in Hgen;
        specialize (IH _ _ _ _ _ _ _ Hgen eq_refl Hin);
        destruct IH as [Hinr|Hint];
        [left; exact Hinr|right; apply in_or_app; right; exact Hint].
      simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & rst_inst & st1 & Hstep & Hrec).
      assert (Hself : Env.find x acc1 = Some rst_inst).
      { eapply fresh_reset_insert_find_self; eauto. }
      pose proof (generate_reset_env'_preserves_find _ _ _ _ _ _ _ _ _ Hrec Hself) as Hpres.
      simpl in Hty1. rewrite Hpres in Hty1. inversion Hty1; subst tys1.
      specialize (IH _ (rids ++ [rst_inst]) _ _ _ _ _ Hrec eq_refl Hin).
      destruct IH as [Hin_old|Hin_tail].
      + apply in_app_iff in Hin_old.
        destruct Hin_old as [Hin_old|Hin_old].
        * now left.
        * simpl in Hin_old. destruct Hin_old as [Heq|[]]. subst ty.
          right. apply in_or_app. left. simpl. auto.
      + right. apply in_or_app. right. exact Hin_tail.
  Qed.

  Lemma In_resets_of:
    forall trs x ck f,
      List.In (TcReset x ck f) trs ->
      List.In (x, f) (resets_of trs).
  Proof.
    induction trs as [|tr trs IH]; intros x ck f Hin; [inversion Hin|].
    destruct Hin as [Heq|Hin].
    - subst tr. simpl. now left.
    - destruct tr as [y c ce|y c e|y c g|y ys c b g es]; simpl;
        try (now apply (IH x ck f)).
      right. now apply (IH x ck f).
  Qed.

  Lemma In_calls_of:
    forall trs x ys ck b f es,
      List.In (TcCall x ys ck b f es) trs ->
      List.In (x, f) (calls_of trs).
  Proof.
    induction trs as [|tr trs IH]; intros x ys ck b f es Hin; [inversion Hin|].
    destruct Hin as [Heq|Hin].
    - subst tr. simpl. now left.
    - destruct tr as [y c ce|y c e|y c g|y zs c r g es']; simpl;
        try (now apply (IH x ys ck b f es)).
      right. now apply (IH x ys ck b f es).
  Qed.

  (** Mapping-based counterpart, for signatures whose instance
      environment comes from the shared name generator rather than from
      a local [generate_reset_env] run. *)

  Lemma trconstrs_targets_contains_reset_ids_map:
    forall trs rids tys ty,
      get_mappings (map fst (resets_of trs)) reset_env = Some rids ->
      trconstrs_targets trs = Some tys ->
      In ty rids ->
      In ty tys.
  Proof.
    induction trs as [|tr trs IH]; intros rids tys ty Hmap Htys Hin.
    - simpl in Hmap. inversion Hmap; subst rids. inversion Hin.
    - simpl in Htys.
      destruct (trconstr_targets tr) as [tys1|] eqn:Hty1; try discriminate.
      destruct (trconstrs_targets trs) as [tys2|] eqn:Hty2; try discriminate.
      inversion Htys; subst tys.
      destruct tr as [x ck ce|x ck e|x ck f|x xs ck b f exps]; simpl in Hmap.
      1,2,4: apply in_or_app; right; eapply IH; eauto.
      destruct (Env.find x reset_env) as [ri|] eqn:Hri; try discriminate.
      destruct (get_mappings (map fst (resets_of trs)) reset_env) as [rs|] eqn:Hrs;
        try discriminate.
      simpl in Hmap. inversion Hmap; subst rids.
      simpl in Hin. destruct Hin as [Heq|Hin].
      + subst ty. apply in_or_app; left.
        simpl in Hty1. rewrite Hri in Hty1. inversion Hty1; subst tys1.
        simpl. now left.
      + apply in_or_app; right. eapply IH; eauto.
  Qed.

  Lemma trconstrs_targets_contains_reset_ids:
    forall trs rids st' tys ty,
      generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
      trconstrs_targets trs = Some tys ->
      In ty rids ->
      In ty tys.
  Proof.
    intros trs rids st' tys ty Hgen Htys Hin.
    unfold generate_reset_env in Hgen.
    edestruct trconstrs_targets_contains_reset_ids'
      as [Hin_init|Hin_targets]; eauto.
    contradiction.
  Qed.

  End SECTRCONSTRTYPING.

  Section SECSYSTYPING.
    Variable G: secglobal.


    Definition generate_sys_signature (n: system) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(SynStc.s_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(SynStc.s_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(SynStc.s_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(SynStc.s_vars)) env);
              do lasts <- option_to_sec (get_mappings_from_node (n.(SynStc.s_lasts)) env);
              do reset_env <- option_to_sec (get_node_inst (n.(SynStc.s_name)) aux_names);
              do rids <- option_to_sec (get_mappings (map fst (resets_of n.(SynStc.s_tcs))) reset_env);
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

    Definition generate_sys_signature_scoped_env
      (n: system) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res signature :=
      match find_node_env n.(SynStc.s_name) envs with
      | None =>
          Error (MSG "Missing system-local security environment" :: [CTX n.(SynStc.s_name)])
      | Some env =>
          generate_sys_signature n env aux_names
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

    (** The scope the *raw* constraints of a system live in: its
        signature scope together with the names simplification will
        eliminate.  Definitionally [signature_scope sig ++
        hidden_sys_vars locals lasts rids] for the signature the
        generator builds. *)

    Definition sys_raw_scope (inp out: list ident) (clk_type rst_type: ident)
                             (locals lasts rids: list ident) : list ident :=
      (inp ++ out ++ [clk_type; rst_type]) ++ hidden_sys_vars locals lasts rids.

    (** Everything [generate_trconstrs_constraints_scoped_on_keys] asks
        of that scope, read off the system's clocking judgement and the
        mappings the generator looked up.  Both the scopedness theorem
        below and the two-accumulator preservation argument need exactly
        this quadruple, so it is proved once. *)

    Lemma sys_raw_scope_facts:
      forall s env clk_type rst_type inp out locals lasts reset_env rids,
        get_mappings_from_node s.(SynStc.s_in) env = Some inp ->
        get_mappings_from_node s.(SynStc.s_out) env = Some out ->
        get_mappings_from_node s.(SynStc.s_vars) env = Some locals ->
        get_mappings_from_node s.(SynStc.s_lasts) env = Some lasts ->
        get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env = Some rids ->
        let scope := sys_raw_scope inp out clk_type rst_type locals lasts rids in
        vars_env_scoped env
          (idck (s.(SynStc.s_in) ++ s.(SynStc.s_vars) ++ s.(SynStc.s_out))
             ++ idck s.(SynStc.s_lasts)) scope
        /\ In clk_type scope
        /\ In rst_type scope
        /\ (forall x ty st0 st1,
               In x (trconstrs_reset_keys s.(SynStc.s_tcs)) ->
               find_env x reset_env st0 = OK (ty, st1) ->
               In ty scope).
    Proof.
      intros s env clk_type rst_type inp out locals lasts reset_env rids
             Hinp0 Hout0 Hlocals0 Hlasts0 Hrids scope.
      subst scope. unfold sys_raw_scope, hidden_sys_vars.
      repeat split.
      - intros x Hmem.
        apply InMembers_app in Hmem.
        destruct Hmem as [Hin|Hin].
        + apply InMembers_idck in Hin.
          apply InMembers_app in Hin.
          destruct Hin as [Hin|Hin].
          * destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp0)
              as (ty & Hfind & Hscope).
            exists ty. split; [exact Hfind|].
            apply in_or_app. left.
            apply in_or_app. left. exact Hscope.
          * apply InMembers_app in Hin.
            destruct Hin as [Hin|Hin].
            -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals0)
                 as (ty & Hfind & Hscope).
               exists ty. split; [exact Hfind|].
               apply in_or_app. right.
               rewrite nodup_In. apply in_or_app. left. exact Hscope.
            -- destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout0)
                 as (ty & Hfind & Hscope).
               exists ty. split; [exact Hfind|].
               apply in_or_app. left.
               apply in_or_app. right.
               apply in_or_app. left. exact Hscope.
        + apply InMembers_idck in Hin.
          destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlasts0)
            as (ty & Hfind & Hscope).
          exists ty. split; [exact Hfind|].
          apply in_or_app. right.
          rewrite nodup_In. apply in_or_app. right.
          apply in_or_app. left. exact Hscope.
      - apply in_or_app. left.
        apply in_or_app. right.
        apply in_or_app. right.
        simpl. left. reflexivity.
      - apply in_or_app. left.
        apply in_or_app. right.
        apply in_or_app. right.
        simpl. right. left. reflexivity.
      - intros x ty st0 st1 Hkey Hfind.
        unfold find_env in Hfind.
        destruct (Env.find x reset_env) as [ty'|] eqn:Henv; try discriminate.
        inversion Hfind; subst ty st1.
        assert (Hinrid : In ty' rids).
        { destruct (get_mappings_in _ _ _ _
                      (trconstrs_reset_keys_in_resets _ _
                         (s.(SynStc.s_reset_consistency)) Hkey) Hrids)
            as (ty0 & Hfind0 & Hin0).
          rewrite Henv in Hfind0. inversion Hfind0; subst ty0. exact Hin0. }
        apply in_or_app. right.
        rewrite nodup_In. apply in_or_app. right.
        apply in_or_app. right. exact Hinrid.
    Qed.

    (** This lifts translated-constraint scopedness to one generated STC signature.  The global target generator reuses it at each translated system. *)
    Theorem generate_sys_signature_scoped:
      forall P s env aux_names sig,
        secglobal_scoped G ->
        env_injective env ->
        Clo.wc_system P s ->
        generate_sys_signature s env aux_names = OK sig ->
        signature_scoped sig.
    Proof.
      intros P s env aux_names sig
             Hscoped Hinj Hwc Hsig.
      unfold generate_sys_signature in Hsig.
      remember
        ((do (clk_id, rst_id) <- option_to_sec (get_node_aux (s.(SynStc.s_name)) aux_names);
          do clk_type <- option_to_sec (Env.find clk_id env);
          do rst_type <- option_to_sec (Env.find rst_id env);
          do inp <- option_to_sec (get_mappings_from_node (s.(SynStc.s_in)) env);
          do out <- option_to_sec (get_mappings_from_node (s.(SynStc.s_out)) env);
          do locals <- option_to_sec (get_mappings_from_node (s.(SynStc.s_vars)) env);
          do lasts <- option_to_sec (get_mappings_from_node (s.(SynStc.s_lasts)) env);
          do reset_env <- option_to_sec (get_node_inst (s.(SynStc.s_name)) aux_names);
          do rids <- option_to_sec (get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env);
          do constraints' <- generate_trconstrs_constraints G env reset_env clk_type rst_type (s.(SynStc.s_tcs));
          ret (inp, out, rst_type, clk_type,
               simplify constraints' (hidden_sys_vars locals lasts rids), env))
         init_state) as gen eqn:Hgen.
      destruct gen as [[[packed env0] st0]|]; try discriminate.
      destruct packed as [packed hidden_constraints].
      destruct packed as [packed packed_clk_type].
      destruct packed as [packed packed_rst_type].
      destruct packed as [packed_out packed_hidden].
      inversion Hsig; subst sig; clear Hsig.
      symmetry in Hgen.
      eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
      eapply sec_bind_inv in Hgen as (clk_type' & st_clk & Hclk & Hgen).
      eapply sec_bind_inv in Hgen as (rst_type' & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
      eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
      eapply sec_bind_inv in Hgen as (lasts & st_lasts & Hlasts & Hgen).
      eapply sec_bind_inv in Hgen as (reset_env & st_renv & Hresetenv & Hgen).
      eapply sec_bind_inv in Hgen as (rids & st_reset & Hrids & Hgen).
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
      inversion Hret; subst; clear Hret.
      edestruct generate_trconstrs_constraints_targets
        as (tys & Htys & Hsnd); eauto using Def.s_nodup_defined.
      destruct Hwc as (_ & _ & Henvvars & Hwtcs).
      unfold signature_scoped, signature_scope.
      eapply simplify_scoped with (ds := hidden_sys_vars locals lasts rids).
      - apply NoDup_nodup.
      - eapply generate_trconstrs_constraints_scoped_on_keys
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
               unfold signature_scope. simpl.
               apply in_or_app. left.
               apply in_or_app. left. exact Hscope.
            -- apply InMembers_app in Hin.
               destruct Hin as [Hin|Hin].
               ++ destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals0) as (ty & Hfind & Hscope).
                  exists ty. split; [exact Hfind|].
                  unfold signature_scope, hidden_sys_vars. simpl.
                  apply in_or_app. right.
                  rewrite nodup_In. apply in_or_app. left. exact Hscope.
               ++ destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout0) as (ty & Hfind & Hscope).
                  exists ty. split; [exact Hfind|].
                  unfold signature_scope. simpl.
                  apply in_or_app. left.
                  apply in_or_app. right.
                  apply in_or_app. left. exact Hscope.
          * apply InMembers_idck in Hin.
            destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlasts0) as (ty & Hfind & Hscope).
            exists ty. split; [exact Hfind|].
            unfold signature_scope, hidden_sys_vars. simpl.
            apply in_or_app. right.
            rewrite nodup_In. apply in_or_app. right. apply in_or_app. left. exact Hscope.
        + unfold signature_scope, hidden_sys_vars. simpl.
          apply in_or_app. left.
          apply in_or_app. right.
          apply in_or_app. right.
          simpl. left. reflexivity.
        + unfold signature_scope, hidden_sys_vars. simpl.
          apply in_or_app. left.
          apply in_or_app. right.
          apply in_or_app. right.
          simpl. right. left. reflexivity.
        + intros x ty st1 st2 Hkey Hfind.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [ty'|] eqn:Henv; try discriminate.
          inversion Hfind; subst ty st2.
          assert (Hinrid : In ty' rids).
          { unfold option_to_sec in Hrids.
            destruct (get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env)
              as [rs|] eqn:Hmap; try discriminate.
            unfold ret in Hrids. inversion Hrids; subst rs st_reset.
            destruct (get_mappings_in _ _ _ _
                        (trconstrs_reset_keys_in_resets _ _
                           (s.(SynStc.s_reset_consistency)) Hkey) Hmap)
              as (ty0 & Hfind0 & Hin0).
            rewrite Henv in Hfind0. inversion Hfind0; subst ty0. exact Hin0. }
          unfold signature_scope, hidden_sys_vars. simpl.
          apply in_or_app. right.
          rewrite nodup_In. apply in_or_app. right. apply in_or_app. right. exact Hinrid.
        - intros d Hd.
        unfold hidden_sys_vars in Hd.
          rewrite nodup_In in Hd.
          apply in_app_iff in Hd.
        destruct Hd as [Hd|Hd].
        + destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals0 Hd)
            as (x & a & Hinx & Hfindx).
          assert (Hdefx : Def.Is_defined_in x s.(SynStc.s_tcs)).
          { eapply system_var_defined_in_tcs.
            now apply in_map with (f := fst) in Hinx. }
          eapply trconstrs_targets_contains_defined in Hdefx; eauto.
          rewrite Hsnd. apply in_map_iff. eexists. split; [reflexivity|exact Hdefx].
        + apply in_app_iff in Hd.
          destruct Hd as [Hd|Hd].
          * destruct (get_mappings_from_node_In _ _ _ _ _ Hlasts0 Hd)
              as (x & a & Hinx & Hfindx).
            assert (Hdefx : Def.Is_defined_in x s.(SynStc.s_tcs)).
            { eapply system_last_defined_in_tcs.
              now apply in_map with (f := fst) in Hinx. }
            eapply trconstrs_targets_contains_defined in Hdefx; eauto.
            rewrite Hsnd. apply in_map_iff. eexists. split; [reflexivity|exact Hdefx].
          * assert (Hrmap : get_mappings (map fst (resets_of s.(SynStc.s_tcs)))
                              reset_env = Some rids).
            { unfold option_to_sec in Hrids.
              destruct (get_mappings (map fst (resets_of s.(SynStc.s_tcs))) reset_env)
                as [rs|] eqn:Hmap0; try discriminate.
              unfold ret in Hrids. inversion Hrids; subst rs st_reset. reflexivity. }
            eapply trconstrs_targets_contains_reset_ids_map in Hd; eauto.
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

    Fixpoint generate_all_sys_signatures_scoped_env'
      (acc: list signature) (sys_list: program) (envs: node_scoped_env)
      (aux_names: list node_aux_names) : res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n :: ns =>
          do sig <- generate_sys_signature_scoped_env acc n envs aux_names;
          generate_all_sys_signatures_scoped_env' (sig :: acc) ns envs aux_names
      end.

    Definition generate_all_sys_signatures_scoped_env
      (sys_list: program) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res (list signature) :=
      generate_all_sys_signatures_scoped_env' [] sys_list envs aux_names.

    Theorem generate_all_sys_signatures_scoped':
      forall systems acc env aux_names G,
        Clo.wc_program systems ->
        secglobal_scoped acc ->
        env_injective env ->
        generate_all_sys_signatures' acc systems env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      induction systems as [|s systems IH]; intros acc env aux_names G
                                                   Hwc Hacc Hinj Hgen.
      - simpl in Hgen. inversion Hgen; subst. exact Hacc.
      - inversion Hwc as [|s' systems' Hwc_tail Hwc_head]; subst s' systems'.
        simpl in Hgen.
        destruct (generate_sys_signature acc s env aux_names) as [sig|] eqn:Hsig;
          simpl in Hgen; try discriminate.
        destruct (generate_all_sys_signatures' (sig :: acc) systems env aux_names) as [G'|] eqn:Htl;
          simpl in Hgen; try discriminate.
        inversion Hgen; subst; clear Hgen.
        assert (Hsigscoped : signature_scoped sig).
        { eapply generate_sys_signature_scoped; eauto. }
        assert (Hacc' : secglobal_scoped (sig :: acc)).
        { eapply secglobal_scoped_cons; eauto. }
        eapply (IH (sig :: acc) env aux_names G); eauto.
    Qed.

    (** This is the main global scopedness theorem for generated STC signatures.  From a well-clocked translated program and an injective naming environment, it proves that the whole target signature environment remains scoped after processing every system.  The translation-preservation file uses this as its target-side global invariant. *)
    Corollary generate_all_sys_signatures_scoped:
      forall systems env aux_names G,
        Clo.wc_program systems ->
        env_injective env ->
        generate_all_sys_signatures systems env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros systems env aux_names G Hwc Hinj Hgen.
      unfold generate_all_sys_signatures in Hgen.
      eapply generate_all_sys_signatures_scoped'; eauto.
      apply secglobal_scoped_nil.
    Qed.

  End SECPROGRAMTYPING.
End SECSTCTYPING.

Module SecSTCTyping
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Last  : STCISLAST Ids Op CESyn SynStc)
  (Import Var   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def   : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord   : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo   : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  <: SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo.

Include SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo SECCETYPING Last Var Def Syst Ord IsF Clo.

End SecSTCTyping.
