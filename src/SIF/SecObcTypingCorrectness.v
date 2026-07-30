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
From Coq Require Import Sorting.Permutation.
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

  Definition env_values (env: Env.t ident) : list (ident * ident) :=
    map (fun '(x, ty) => (ty, x)) (Env.elements env).

  Lemma env_values_add:
    forall x ty env,
      ~ Env.In x env ->
      Permutation (env_values (Env.add x ty env))
                  ((ty, x) :: env_values env).
  Proof.
    intros x ty env Hnin.
    unfold env_values.
    replace ((ty, x) :: map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))
      with (map (fun '(x0, ty0) => (ty0, x0)) ((x, ty) :: Env.elements env))
      by reflexivity.
    now apply Permutation_map, Env.elements_add.
  Qed.

  Lemma env_values_nodup_injective:
    forall env,
      NoDupMembers (env_values env) ->
      env_injective env.
  Proof.
    intros env Hnodup x y tx ty Hfindx Hfindy Heq.
    apply Env.elements_correct in Hfindx.
    apply Env.elements_correct in Hfindy.
    unfold env_values in Hnodup.
    assert (Hinx : In (tx, x) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
    { apply in_map_iff. exists (x, tx). split; [reflexivity|exact Hfindx]. }
    assert (Hiny : In (tx, y) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
    { subst ty.
      apply in_map_iff. exists (y, tx). split; [reflexivity|exact Hfindy]. }
    now eapply NoDupMembers_det; eauto.
  Qed.

  Definition state_env_sec_bounded (st: ident) (env: Env.t ident) : Prop :=
    forall x ty,
      Env.find x env = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n /\ (n < st)%positive.

  Lemma fresh_state_insert_sec_range:
    forall env k st env' sty st' x ty,
      (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
      fresh_state_insert k env st = OK ((env', sty), st') ->
      Env.find x env' = Some ty ->
      exists n, ty = Ids.gensym Ids.sec_reset n.
  Proof.
    intros env k st env' sty st' x ty Henv Hins Hfind.
    unfold fresh_state_insert in Hins.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
    eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
    unfold fresh_state_ident in Hfresh.
    inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins0.
    inversion Hins0; subst e st2.
    unfold ret in Hret. inversion Hret. subst env' sty st'.
    destruct (Pos.eq_dec x k) as [Heq|Hneq].
    - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
      eexists; reflexivity.
    - rewrite Env.gso in Hfind; eauto.
  Qed.

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
      eapply fresh_state_insert_sec_range; eauto.
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

  Lemma state_env_sec_bounded_step:
    forall st env,
      state_env_sec_bounded st env ->
      state_env_sec_bounded (Pos.succ st) env.
  Proof.
    intros st env Hbound x ty Hfind.
    specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
    exists n. split; auto.
    eapply Pos.lt_trans; eauto.
    apply Pos.lt_succ_diag_r.
  Qed.

  Lemma state_env_values_fresh_notin:
    forall env st,
      state_env_sec_bounded st env ->
      ~ InMembers (Ids.gensym Ids.sec_reset st) (env_values env).
  Proof.
    intros env st Hbound Hin.
    apply InMembers_In in Hin as (x & Hin).
    unfold env_values in Hin.
    apply in_map_iff in Hin as ((x', ty') & Heq & Hele).
    simpl in Heq. inversion Heq; subst x' ty'. clear Heq.
    apply Env.elements_complete in Hele.
    specialize (Hbound _ _ Hele) as (n & Hgen & Hlt).
    apply gensym_injective in Hgen as [_ Hn]. subst n.
    now apply Pos.lt_irrefl in Hlt.
  Qed.

  Lemma fresh_state_insert_env_props:
    forall env k st env' sty st',
      state_env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      fresh_state_insert k env st = OK ((env', sty), st') ->
      state_env_sec_bounded st' env'
      /\ NoDupMembers (env_values env').
  Proof.
    intros env k st env' sty st' Hbound Hnodup Hgen.
    unfold fresh_state_insert in Hgen.
    destruct (Env.mem k env) eqn:Hmem; try discriminate.
    eapply sec_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
    eapply sec_bind_inv in Hgen as (e & st2 & Hins & Hret).
    unfold fresh_state_ident in Hfresh. inversion Hfresh; subst v st1.
    unfold insert_env, ret in Hins. inversion Hins; subst e st2.
    unfold ret in Hret. inversion Hret; subst env' sty st'.
    split.
    - intros x ty Hfind.
      destruct (ident_eq_dec x k) as [Heq|Hneq].
      + subst x. rewrite Env.gss in Hfind. inversion Hfind; subst ty.
        exists st. split; [reflexivity|apply Pos.lt_succ_diag_r].
      + rewrite Env.gso in Hfind by auto.
        specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
        exists n. split; auto.
        eapply Pos.lt_trans; eauto.
        apply Pos.lt_succ_diag_r.
    - assert (Hnotin : ~ Env.In k env).
      { intro Hin. apply Env.mem_1 in Hin. rewrite Hmem in Hin. discriminate. }
      eapply (NoDupMembers_Permutation_Proper
                (env_values (Env.add k (Ids.gensym Ids.sec_reset st) env))
                ((Ids.gensym Ids.sec_reset st, k) :: env_values env)).
      + apply env_values_add; exact Hnotin.
      + constructor.
        * apply state_env_values_fresh_notin; exact Hbound.
        * exact Hnodup.
  Qed.

  Lemma generate_state_env_props':
    forall objs env acc st state_env stids st',
      state_env_sec_bounded st env ->
      NoDupMembers (env_values env) ->
      generate_state_env' objs env acc st = OK ((state_env, stids), st') ->
      state_env_sec_bounded st' state_env
      /\ NoDupMembers (env_values state_env).
  Proof.
    induction objs as [|[o cls] objs IH];
      intros env acc st state_env stids st' Hbound Hnodup Hgen.
    - simpl in Hgen. inversion Hgen; subst. auto.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (env1 & sty & st1 & Hstep & Hrec).
      destruct (fresh_state_insert_env_props _ _ _ _ _ _
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
        unfold fresh_state_insert in Hstep.
        destruct (Env.mem o0 env) eqn:Hmem; try discriminate.
        eapply sec_bind_inv in Hstep as (v & stv & Hfresh & Hstep).
        eapply sec_bind_inv in Hstep as (e & ste & Hins0 & Hret).
        unfold fresh_state_ident in Hfresh. inversion Hfresh; subst v stv.
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
