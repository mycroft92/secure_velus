(** Correctness facts for generated Obc class signatures.

    First slice: satisfaction-equivalence of [collapse] (joining the
    sources of constraints that share a target neither gains nor loses
    satisfying valuations), and the one-target-per-constraint shape of
    the statement-level generator. *)

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
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
From Coq Require Import Sorting.Permutation.
From compcert Require Import common.Errors.

Module Type SECOBCTYPINGCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG).

  (** * Collapse is satisfaction-neutral *)

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
    forall G env state_env rst_ty s pc cns st st',
      generate_stmt_constraints G env state_env rst_ty pc s st = OK (cns, st') ->
      Forall (fun c => length (snd c) = 1%nat) cns.
  Proof.
    intros G env state_env rst_ty s.
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
    forall G env state_env rst_ty s1 s2 pc1 pc2 c1 c2 st st1 st',
      generate_stmt_constraints G env state_env rst_ty pc1 s1 st = OK (c1, st1) ->
      generate_stmt_constraints G env state_env rst_ty pc2 s2 st1 = OK (c2, st') ->
      wf_constraints (collapse (c1 ++ c2)).
  Proof.
    intros G env state_env rst_ty s1 s2 pc1 pc2 c1 c2 st st1 st' H1 H2.
    apply collapse_wf.
    apply Forall_app.
    split; eapply generate_stmt_constraints_rhs_singleton; eauto.
  Qed.

  (** * State environment properties

      Ports of the reset-environment lemmas of
      [SecStcTypingCorrectness.v]: generated state types are [sec_reset]
      gensyms below the final counter, pairwise distinct, and the state
      environment is injective; every bound key names an object of the
      class. *)

  Lemma generate_state_env_range':
    forall objs env acc st state_env stids st' x ty,
      (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
      generate_state_env' objs env acc st = OK ((state_env, stids), st') ->
      Env.find x state_env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    induction objs as [|[o cls] objs IH];
      intros env acc st state_env stids st' x ty Henv Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. eauto.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (env1 & sty & st1 & Hstep & Hrec).
      eapply IH; [|eauto|eauto].
      intros y ty' Hy.
      eapply fresh_reset_insert_sec_range; eauto.
  Qed.

  Lemma generate_state_env_range:
    forall objs state_env stids st' x ty,
      generate_state_env objs init_state = OK ((state_env, stids), st') ->
      Env.find x state_env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    intros objs state_env stids st' x ty Hgen Hfind.
    unfold generate_state_env in Hgen.
    eapply generate_state_env_range'; eauto.
    intros y ty' Hy.
    rewrite Env.gempty in Hy. discriminate.
  Qed.




  Lemma generate_state_env_props':
    forall objs env acc st state_env stids st',
      env_reset_bounded st env ->
      NoDupMembers (env_values env) ->
      generate_state_env' objs env acc st = OK ((state_env, stids), st') ->
      env_reset_bounded st' state_env
      /\ NoDupMembers (env_values state_env).
  Proof.
    induction objs as [|[o cls] objs IH];
      intros env acc st state_env stids st' Hbound Hnodup Hgen.
    - simpl in Hgen. inversion Hgen; subst. auto.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (env1 & sty & st1 & Hstep & Hrec).
      destruct (fresh_reset_insert_env_props _ _ _ _ _ _
                  Hbound Hnodup Hstep) as [Hbound1 Hnodup1].
      eapply IH; eauto.
  Qed.

  Lemma generate_state_env_injective:
    forall objs state_env stids st',
      generate_state_env objs init_state = OK ((state_env, stids), st') ->
      forall x y tx ty,
        Env.find x state_env = Some tx ->
        Env.find y state_env = Some ty ->
        tx = ty ->
        x = y.
  Proof.
    intros objs state_env stids st' Hgen.
    unfold generate_state_env in Hgen.
    destruct (generate_state_env' objs (Env.empty _) nil init_state)
      as [[[state_env0 stids0] st0]|] eqn:Hgen'; try discriminate.
    inversion Hgen; subst state_env stids st'.
    intros x y tx ty Hfindx Hfindy Heq.
    destruct (generate_state_env_props' objs (Env.empty _) nil init_state state_env0 stids0 st0)
      as [_ Hnodup];
      eauto.
    - intros z tz Hz. rewrite Env.gempty in Hz. discriminate.
    - constructor.
    - eapply env_values_nodup_injective; eauto.
  Qed.

  (** * Targets of generated constraints

      [stmt_targets] computes the security types written by a statement
      (assigned variables/mems and reset instance states).  The
      generated constraint list has exactly these targets, in order;
      together with [collapse_rhs_in] this discharges the
      defining-constraint premise of [simplify_scoped] once the
      translation supplies "every hidden var is assigned". *)

  Section TARGETS.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    Lemma mmap_find_env_inv:
      forall xs tys st st',
        SC.mmap (fun x => find_env x env) xs st = OK (tys, st') ->
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

    Fixpoint stmt_targets (s: stmt) : option (list ident) :=
      match s with
      | Skip => Some []
      | Assign x _ =>
          match Env.find x env with
          | Some ty => Some [ty]
          | None => None
          end
      | AssignSt x _ =>
          match Env.find x env with
          | Some ty => Some [ty]
          | None => None
          end
      | Comp s1 s2 =>
          match stmt_targets s1, stmt_targets s2 with
          | Some t1, Some t2 => Some (t1 ++ t2)
          | _, _ => None
          end
      | Ifte _ s1 s2 =>
          match stmt_targets s1, stmt_targets s2 with
          | Some t1, Some t2 => Some (t1 ++ t2)
          | _, _ => None
          end
      | Call [] _ o m _ =>
          if ident_eqb m Ids.reset then
            match Env.find o state_env with
            | Some ty => Some [ty]
            | None => None
            end
          else Some []
      | Call ys _ o m _ =>
          if ident_eqb m Ids.step then get_mappings ys env else None
      end.

    Lemma generate_constraints_targets:
      forall sig inp clk rst out cns st st',
        SIG.generate_constraints sig inp clk rst out st = OK (cns, st') ->
        map snd cns = map (fun x => [x]) out.
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
      - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst. reflexivity.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c & st5 & Hhd & Hgen).
        eapply sec_bind_inv in Hgen as (cs & st6 & Htl & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        eapply sec_bind_inv in Hhd as (sty & st7 & _ & Hhd).
        unfold ret in Hhd. inversion Hhd; subst c st5.
        simpl. f_equal.
        eapply IH; eauto.
    Qed.

    Lemma generate_stmt_constraints_targets:
      forall s pc cns st st',
        generate_stmt_constraints G env state_env rst_ty pc s st = OK (cns, st') ->
        exists tys,
          stmt_targets s = Some tys
          /\ map snd cns = map (fun ty => [ty]) tys.
    Proof.
      induction s as [x e|x e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o m es|];
        intros pc cns st st' Hgen.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        exists [xty']. split.
        + simpl. rewrite Hfindx. reflexivity.
        + reflexivity.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        exists [xty']. split.
        + simpl. rewrite Hfindx. reflexivity.
        + reflexivity.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & _ & Hgen).
        eapply sec_bind_inv in Hgen as (c1 & st2 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st3 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        destruct (IH1 _ _ _ _ Hgen1) as (t1 & Ht1 & Hsnd1).
        destruct (IH2 _ _ _ _ Hgen2) as (t2 & Ht2 & Hsnd2).
        exists (t1 ++ t2). split.
        + simpl. rewrite Ht1, Ht2. reflexivity.
        + replace (map snd (c1 ++ c2)) with (map snd c1 ++ map snd c2).
          * rewrite Hsnd1, Hsnd2, map_app. reflexivity.
          * symmetry. apply map_app.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        destruct (IH1 _ _ _ _ Hgen1) as (t1 & Ht1 & Hsnd1).
        destruct (IH2 _ _ _ _ Hgen2) as (t2 & Ht2 & Hsnd2).
        exists (t1 ++ t2). split.
        + simpl. rewrite Ht1, Ht2. reflexivity.
        + replace (map snd (c1 ++ c2)) with (map snd c1 ++ map snd c2).
          * rewrite Hsnd1, Hsnd2, map_app. reflexivity.
          * symmetry. apply map_app.
      - destruct ys as [|y ys'].
        + simpl in Hgen.
          destruct (ident_eqb m Ids.reset) eqn:Hreset.
          * eapply sec_bind_inv in Hgen as (sty & st1 & Hfind & Hret).
            unfold ret in Hret. inversion Hret; subst cns st'.
            unfold find_env in Hfind.
            destruct (Env.find o state_env) as [sty'|] eqn:Hfindo; try discriminate.
            unfold ret in Hfind. inversion Hfind; subst sty st1.
            exists [sty']. split.
            -- simpl. rewrite Hreset, Hfindo. reflexivity.
            -- reflexivity.
          * unfold ret in Hgen. inversion Hgen; subst.
            exists []. split.
            -- simpl. rewrite Hreset. reflexivity.
            -- reflexivity.
        + simpl in Hgen.
          destruct (ident_eqb m Ids.step) eqn:Hstep; try discriminate.
          destruct (SIG.find_signature cls G) as [sig|] eqn:Hfindsig; try discriminate.
          eapply sec_bind_inv in Hgen as (inptyp & st1 & _ & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st2 & Hout & Hgen).
          eapply sec_bind_inv in Hgen as (sty & st3 & _ & Hgen).
          destruct (mmap_find_env_inv (y :: ys') outtyp st1 st2 Hout) as [_ Hmaps].
          exists outtyp. split.
          * simpl. rewrite Hstep. exact Hmaps.
          * eapply generate_constraints_targets; eauto.
      - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
        exists []. split; reflexivity.
    Qed.

    (** The syntactic write sets are covered by the target list: a name a
        statement writes has its security type among the statement's
        targets. *)

    Lemma stmt_writes_targets:
      forall s tys x ty,
        stmt_targets s = Some tys ->
        List.In x (SECOBCTYPING.stmt_writes s) ->
        Env.find x env = Some ty ->
        List.In ty tys.
    Proof.
      induction s as [x0 e|x0 e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o m es|];
        intros tys x ty Htys Hin Hfind; simpl in Hin, Htys.
      - destruct Hin as [Heq|[]]; subst x0.
        rewrite Hfind in Htys. inversion Htys. now left.
      - destruct Hin as [Heq|[]]; subst x0.
        rewrite Hfind in Htys. inversion Htys. now left.
      - destruct (stmt_targets s1) as [t1|] eqn:H1; try discriminate.
        destruct (stmt_targets s2) as [t2|] eqn:H2; try discriminate.
        inversion Htys; subst tys.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app;
          [left; eapply IH1|right; eapply IH2]; eauto.
      - destruct (stmt_targets s1) as [t1|] eqn:H1; try discriminate.
        destruct (stmt_targets s2) as [t2|] eqn:H2; try discriminate.
        inversion Htys; subst tys.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app;
          [left; eapply IH1|right; eapply IH2]; eauto.
      - destruct ys as [|y ys'].
        + destruct (ident_eqb m Ids.step); contradiction.
        + destruct (ident_eqb m Ids.step) eqn:Hm; [|contradiction].
          destruct (get_mappings_in _ _ _ _ Hin Htys) as (ty0 & Hty0 & Hinty).
          rewrite Hfind in Hty0. inversion Hty0; subst ty0. exact Hinty.
      - inversion Hin.
    Qed.

    Lemma stmt_reset_insts_targets:
      forall s tys o ty,
        stmt_targets s = Some tys ->
        List.In o (SECOBCTYPING.stmt_reset_insts s) ->
        Env.find o state_env = Some ty ->
        List.In ty tys.
    Proof.
      induction s as [x0 e|x0 e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o0 m es|];
        intros tys o ty Htys Hin Hfind; simpl in Hin, Htys;
        try (inversion Hin; fail).
      - destruct (stmt_targets s1) as [t1|] eqn:H1; try discriminate.
        destruct (stmt_targets s2) as [t2|] eqn:H2; try discriminate.
        inversion Htys; subst tys.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app;
          [left; eapply IH1|right; eapply IH2]; eauto.
      - destruct (stmt_targets s1) as [t1|] eqn:H1; try discriminate.
        destruct (stmt_targets s2) as [t2|] eqn:H2; try discriminate.
        inversion Htys; subst tys.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app;
          [left; eapply IH1|right; eapply IH2]; eauto.
      - destruct ys as [|y ys']; [|contradiction].
        destruct (ident_eqb m Ids.reset) eqn:Hm; [|contradiction].
        destruct Hin as [Heq|[]]; subst o0.
        rewrite Hfind in Htys. inversion Htys. now left.
    Qed.

    Lemma stmt_targets_defining:
      forall s pc cns st st' tys d,
        generate_stmt_constraints G env state_env rst_ty pc s st = OK (cns, st') ->
        stmt_targets s = Some tys ->
        In d tys ->
        In [d] (map snd cns).
    Proof.
      intros s pc cns st st' tys d Hgen Htys Hin.
      destruct (generate_stmt_constraints_targets _ _ _ _ _ Hgen)
        as (tys' & Htys' & Hsnd).
      rewrite Htys in Htys'. inversion Htys'; subst tys'.
      rewrite Hsnd.
      apply in_map_iff. exists d. split; [reflexivity|exact Hin].
    Qed.

  End TARGETS.

  Lemma generate_state_env'_key_from_objs:
    forall objs env acc st state_env stids st' o ty,
      generate_state_env' objs env acc st = OK ((state_env, stids), st') ->
      Env.find o state_env = Some ty ->
      Env.find o env <> None \/ InMembers o objs.
  Proof.
    induction objs as [|[o0 cls] objs IH];
      intros env acc st state_env stids st' o ty Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst.
      left. rewrite Hfind. discriminate.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (env1 & sty & st1 & Hstep & Hrec).
      destruct (IH _ _ _ _ _ _ _ _ Hrec Hfind) as [Hin1|Hins].
      + destruct (Env.find o env1) as [ty1|] eqn:Hfind1; [|congruence].
        unfold fresh_reset_insert in Hstep.
        destruct (Env.mem o0 env) eqn:Hmem; try discriminate.
        eapply sec_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
        eapply sec_bind_inv in Hstep as (e & ste & Hins0 & Hret).
        unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v stv.
        unfold insert_env, ret in Hins0. inversion Hins0; subst e ste.
        unfold ret in Hret. inversion Hret; subst env1 sty st1.
        destruct (Pos.eq_dec o o0) as [Heq|Hneq].
        * subst o0. right. simpl. now left.
        * rewrite Env.gso in Hfind1 by auto.
          left. rewrite Hfind1. discriminate.
      + right. simpl. now right.
  Qed.

  Lemma generate_state_env_key_from_objs:
    forall objs state_env stids st st' o ty,
      generate_state_env objs st = OK ((state_env, stids), st') ->
      Env.find o state_env = Some ty ->
      InMembers o objs.
  Proof.
    intros objs state_env stids st st' o ty Hgen Hfind.
    unfold generate_state_env in Hgen.
    destruct (generate_state_env'_key_from_objs _ _ _ _ _ _ _ _ _ Hgen Hfind)
      as [Hin|Hins]; [|exact Hins].
    rewrite Env.gempty in Hin. congruence.
  Qed.

  (** * Inversion of class signature generation

      Bridge-facing: decomposes a successful [generate_class_signature]
      into the pieces the translation proof needs. *)

  Section CLSINV.
    Variable G: SIG.secglobal.

    Lemma generate_class_signature_inv:
      forall c env aux_names sig,
        generate_class_signature G c env aux_names = OK sig ->
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
          /\ get_node_inst c.(c_name) aux_names = Some state_env
          /\ get_mappings (map fst c.(c_objs)) state_env = Some stids
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
      eapply sec_bind_inv in Hgen as (state_env & st_senv & Hstate & Hgen).
      eapply sec_bind_inv in Hgen as (stids & st_state & Hstids & Hgen).
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
      unfold option_to_sec in Hstate.
      destruct (get_node_inst (c.(c_name)) aux_names) as [state_env0|] eqn:Hstate0;
        try discriminate.
      unfold ret in Hstate. inversion Hstate; subst state_env0.
      unfold ret in Hstids.
      unfold option_to_sec in Hstids.
      destruct (get_mappings (map fst (c.(c_objs))) state_env) as [stids0|] eqn:Hstids0;
        try discriminate.
      unfold ret in Hstids. inversion Hstids; subst stids0.
      unfold ret in Hret. inversion Hret; subst.
      do 17 eexists.
      repeat split; eauto.
    Qed.

    (** Mirrors [generate_sys_signature_scoped] on the STC side, with
        [class_well_defined] standing in for [wc_system]: an STC system
        record carries its own invariants, an Obc class does not. *)

    Theorem generate_class_signature_scoped:
      forall c envc aux sig,
        SIG.secglobal_scoped G ->
        SECOBCTYPING.class_well_defined c ->
        SECOBCTYPING.generate_class_signature G c envc aux = OK sig ->
        signature_scoped sig.
    Proof.
      intros c envc aux sig Hglob Hwd Hsig.
      edestruct generate_class_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & stepm & resetm
           & inp & out & locals & lasts & senv & stids
           & craw_step & craw_reset & st_state & st_step & st_raw
           & Haux & Hclk & Hrst & Hstepm & Hresetm & Hinp & Hout
           & Hlocals & Hlasts & Hsenv & Hstids & Hstepc & Hresetc & Hsigdef);
        [exact Hsig|].
      destruct (Hwd _ _ Hstepm Hresetm)
        as (Hwstep & Hwmems & Hwobjs & Hfstep & Hfreset & Hkstep & Hkreset).
      subst sig. unfold signature_scoped, signature_scope; simpl.
      (* state types of the class's objects are hidden *)
      assert (Hobjty : forall o sty, InMembers o c.(c_objs) ->
                                     Env.find o senv = Some sty ->
                                     List.In sty stids).
      { intros o sty Hin Hfind.
        destruct (get_mappings_in _ _ _ _ (proj1 (fst_InMembers _ _) Hin) Hstids)
          as (ty & Hty & Hinty).
        rewrite Hfind in Hty. inversion Hty; subst ty. exact Hinty. }
      eapply simplify_scoped.
      - apply NoDup_nodup.
      - apply collapse_scoped.
        unfold constraints_scoped. apply Forall_app. split.
        + eapply (generate_stmt_constraints_scoped_on_keys G envc senv rst_type)
            with (s := m_body stepm) (pc := [clk_type]).
          * exact Hglob.
          * intros x Hx. specialize (Hfstep x Hx).
            unfold SECOBCTYPING.class_interface in Hfstep.
            apply in_app_iff in Hfstep as [Hf|Hfstep].
            { destruct (get_mappings_from_node_inmembers _ _ _ _ _
                          (proj2 (fst_InMembers _ _) Hf) Hinp) as (ty & Hty & Hinty).
              exists ty. split; [exact Hty|].
              apply in_or_app; left. apply in_or_app; now left. }
            apply in_app_iff in Hfstep as [Hf|Hfstep].
            { destruct (get_mappings_from_node_inmembers _ _ _ _ _
                          (proj2 (fst_InMembers _ _) Hf) Hlocals) as (ty & Hty & Hinty).
              exists ty. split; [exact Hty|].
              apply in_or_app; right.
              unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
              apply in_or_app; now left. }
            apply in_app_iff in Hfstep as [Hf|Hf].
            { destruct (get_mappings_from_node_inmembers _ _ _ _ _
                          (proj2 (fst_InMembers _ _) Hf) Hout) as (ty & Hty & Hinty).
              exists ty. split; [exact Hty|].
              apply in_or_app; left. apply in_or_app; right.
              apply in_or_app; now left. }
            { destruct (get_mappings_from_node_inmembers _ _ _ _ _
                          (proj2 (fst_InMembers _ _) Hf) Hlasts) as (ty & Hty & Hinty).
              exists ty. split; [exact Hty|].
              apply in_or_app; right.
              unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
              apply in_or_app; right. apply in_or_app; now left. }
          * apply st_scoped_singleton.
            apply in_or_app; left. apply in_or_app; right.
            apply in_or_app; right. simpl. now left.
          * apply in_or_app; left. apply in_or_app; right.
            apply in_or_app; right. simpl. now right; left.
          * intros o sty st0 st1 Hino Hfind.
            unfold SC.find_env in Hfind.
            destruct (Env.find o senv) as [v|] eqn:Hv; try discriminate.
            unfold ret in Hfind. inversion Hfind; subst v st1.
            apply in_or_app; right.
            unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
            apply in_or_app; right. apply in_or_app; right.
            eapply Hobjty; eauto.
          * exact Hstepc.
        + eapply (generate_stmt_constraints_scoped_on_keys G envc senv rst_type)
            with (s := m_body resetm) (pc := @nil ident).
          * exact Hglob.
          * intros x Hx. specialize (Hfreset x Hx).
            destruct (get_mappings_from_node_inmembers _ _ _ _ _
                        Hfreset Hlasts) as (ty & Hty & Hinty).
            exists ty. split; [exact Hty|].
            apply in_or_app; right.
            unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
            apply in_or_app; right. apply in_or_app; now left.
          * intros z [].
          * apply in_or_app; left. apply in_or_app; right.
            apply in_or_app; right. simpl. now right; left.
          * intros o sty st0 st1 Hino Hfind.
            unfold SC.find_env in Hfind.
            destruct (Env.find o senv) as [v|] eqn:Hv; try discriminate.
            unfold ret in Hfind. inversion Hfind; subst v st1.
            apply in_or_app; right.
            unfold SECOBCTYPING.hidden_class_vars. rewrite nodup_In.
            apply in_or_app; right. apply in_or_app; right.
            eapply Hobjty; eauto.
          * exact Hresetc.
      - (* every hidden name has a defining constraint *)
        destruct (generate_stmt_constraints_targets G envc senv rst_type
                    _ _ _ _ _ Hstepc) as (tstep & Htstep & Hsndstep).
        destruct (generate_stmt_constraints_targets G envc senv rst_type
                    _ _ _ _ _ Hresetc) as (treset & Htreset & Hsndreset).
        intros d Hd.
        rewrite collapse_rhs_in.
        rewrite map_app. apply in_or_app.
        unfold SECOBCTYPING.hidden_class_vars in Hd. rewrite nodup_In in Hd.
        apply in_app_iff in Hd as [Hd|Hd].
        + (* a local: written by the step method *)
          left.
          destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hd)
            as (x & a & Hinx & Hfindx).
          eapply (stmt_targets_defining G envc senv rst_type _ _ _ _ _ _ d
                    Hstepc Htstep).
          eapply stmt_writes_targets; [exact Htstep| |exact Hfindx].
          apply Hwstep. eapply In_InMembers; eauto.
        + apply in_app_iff in Hd as [Hd|Hd]; right.
          * (* a memory: written by the reset method *)
            destruct (get_mappings_from_node_In _ _ _ _ _ Hlasts Hd)
              as (x & a & Hinx & Hfindx).
            eapply (stmt_targets_defining G envc senv rst_type _ _ _ _ _ _ d
                      Hresetc Htreset).
            eapply stmt_writes_targets; [exact Htreset| |exact Hfindx].
            apply Hwmems. eapply In_InMembers; eauto.
          * (* an object: reset by the reset method *)
            destruct (get_mappings_In _ _ _ _ Hstids Hd) as (o & Hino & Hfindo).
            eapply (stmt_targets_defining G envc senv rst_type _ _ _ _ _ _ d
                      Hresetc Htreset).
            eapply stmt_reset_insts_targets; [exact Htreset| |exact Hfindo].
            apply Hwobjs. now apply (proj2 (fst_InMembers _ _)).
    Qed.

  End CLSINV.

End SECOBCTYPINGCORRECTNESS.

Module SecObcTypingCorrectness
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  <: SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS SECOBCTYPING.

Include SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS SECOBCTYPING.

End SecObcTypingCorrectness.
