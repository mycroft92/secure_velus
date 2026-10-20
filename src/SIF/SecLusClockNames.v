(** Names in the clocks of a well-clocked expression.

    A clock mentions variables.  In a well-clocked expression those are the
    node's declared variables, or streams the expression itself names: the
    named outputs of a call inside it.  This is the statement of
    [LClocking.v] that "the scope of a fresh clock is limited to its
    column", made into a lemma about [ck_vars] and [fresh_in].

    The proof reads three things off the clocking rules:
    - a call's output clocks are instances ([instck]) of the callee's, and
      the callee's output clocks are over its inputs and outputs only
      ([wc_node]: [wc_env (idck (n_in ++ n_out))]);
    - an instance variable is the name of the argument bound to an input, or
      of the output itself ([WellInstantiated]);
    - the base clock of the instantiation is one of the arguments' clocks
      ([WellInstantiated_bck], the callee having an input).

    Nothing here is assumed of the program beyond [wc_global]. *)

From Coq Require Import List.
From Coq Require Import Permutation.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.

Import List.ListNotations.

Module SecLusClockNames
  (Import Ids  : IDS)
  (Import Op   : OPERATORS)
  (Import LSyn : LSYNTAX Ids Op)
  (Import LClo : LCLOCKING Ids Op LSyn).

  Fixpoint ck_vars (ck : clock) : list ident :=
    match ck with
    | Cbase => []
    | Con ck' x _ => x :: ck_vars ck'
    end.

  Lemma Is_free_ck_vars :
    forall x ck, Is_free_in_clock x ck -> In x (ck_vars ck).
  Proof.
    intros x ck. induction ck as [|ck IH y b]; intros H; inversion H; subst.
    - now left.
    - right. apply IH. assumption.
  Qed.

  Lemma ck_vars_Is_free :
    forall x ck, In x (ck_vars ck) -> Is_free_in_clock x ck.
  Proof.
    intros x ck. induction ck as [|ck IH y b]; intros H.
    - destruct H.
    - destruct H as [<-|H]; [constructor|].
      apply FreeCon2. apply IH. exact H.
  Qed.

  Lemma wc_clock_ck_vars :
    forall vars ck,
      wc_clock vars ck -> incl (ck_vars ck) (List.map fst vars).
  Proof.
    intros vars ck. induction 1 as [|ck x b Hck IH Hx]; intros y Hy.
    - destruct Hy.
    - destruct Hy as [<-|Hy].
      + apply in_map_iff. exists (x, ck). split; [reflexivity|exact Hx].
      + exact (IH y Hy).
  Qed.

  Lemma map_fst_idck :
    forall l : list (ident * (type * clock)),
      List.map fst (idck l) = List.map fst l.
  Proof.
    intros l. unfold idck. rewrite map_map.
    apply map_ext. intros [x [t c]]. reflexivity.
  Qed.

  (** What a name of an expression's stream can be. *)
  Definition clock_name_ok (vars : list (ident * clock)) (e : exp)
      (y : ident) : Prop :=
    In y (List.map fst vars) \/ InMembers y (fresh_in e).

  Lemma anon_streams_InMembers :
    forall y (anns : list ann),
      In (Some y) (List.map LSyn.stream_name anns) ->
      InMembers y (LSyn.anon_streams anns).
  Proof.
    intros y anns. induction anns as [|[ty [cl name]] anns IH]; simpl.
    - intros [].
    - intros [H|H].
      + unfold LSyn.stream_name in H. simpl in H. subst name. simpl. now left.
      + specialize (IH H). destruct name as [w|]; [simpl; now right|exact IH].
  Qed.

  Lemma InMembers_fresh_in_Eapp_anns :
    forall y f es ro (anns : list ann),
      InMembers y (LSyn.anon_streams anns) ->
      InMembers y (fresh_in (Eapp f es ro anns)).
  Proof.
    intros y f es ro anns H. destruct ro as [r|]; simpl;
      apply InMembers_app; right; [apply InMembers_app; right|]; exact H.
  Qed.

  Lemma InMembers_fresh_in_Eapp_arg :
    forall y f es ro anns e,
      In e es -> InMembers y (fresh_in e) ->
      InMembers y (fresh_in (Eapp f es ro anns)).
  Proof.
    intros y f es ro anns e He H.
    assert (InMembers y (concat (List.map fresh_in es))) as Hc.
    { apply InMembers_In in H as (a & Ha).
      apply In_InMembers with (b := a). apply in_concat.
      exists (fresh_in e). split; [exact Ha|exact (in_map fresh_in es e He)]. }
    destruct ro as [r|]; simpl; apply InMembers_app; left; exact Hc.
  Qed.

  Lemma InMembers_fresh_in_Eapp_rst :
    forall y f es r anns,
      InMembers y (fresh_in r) ->
      InMembers y (fresh_in (Eapp f es (Some r) anns)).
  Proof.
    intros y f es r anns H. simpl. apply InMembers_app. right.
    apply InMembers_app. left. exact H.
  Qed.

  (** The names a well-clocked expression's streams carry. *)
  Lemma wc_exp_stream_names :
    forall G vars e,
      wc_exp G vars e ->
      forall nc, In nc (nclockof e) ->
      forall y, snd nc = Some y -> clock_name_ok vars e y.
  Proof.
    intros G vars e Hwc nc Hnc y Hy.
    inversion Hwc; subst; simpl in Hnc.
    - destruct Hnc as [<-|[]]. simpl in Hy. discriminate.
    - destruct Hnc as [<-|[]]. simpl in Hy. inversion Hy; subst.
      left. apply in_map_iff. exists (y, ck). split; [reflexivity|assumption].
    - destruct Hnc as [<-|[]]. simpl in Hy. discriminate.
    - destruct Hnc as [<-|[]]. simpl in Hy. discriminate.
    - destruct Hnc as [<-|[]]. simpl in Hy. discriminate.
    - apply in_map_iff in Hnc as (a & <- & Ha).
      rewrite Forall_forall in H3. specialize (H3 a Ha).
      unfold unnamed_stream in H3. rewrite H3 in Hy. discriminate.
    - apply in_map_iff in Hnc as (a & <- & Ha).
      rewrite Forall_forall in H3. specialize (H3 a Ha).
      unfold unnamed_stream in H3. rewrite H3 in Hy. discriminate.
    - apply in_map_iff in Hnc as (a & <- & Ha). simpl in Hy. discriminate.
    - apply in_map_iff in Hnc as (a & <- & Ha). simpl in Hy. discriminate.
    - apply in_map_iff in Hnc as (a & <- & Ha). simpl in Hy. discriminate.
    - right. apply InMembers_fresh_in_Eapp_anns.
      apply anon_streams_InMembers. apply in_map_iff.
      apply in_map_iff in Hnc as (a & Ha1 & Ha2).
      exists a. split; [|exact Ha2].
      unfold LSyn.stream_name. rewrite Ha1. exact Hy.
    - right. apply InMembers_fresh_in_Eapp_anns.
      apply anon_streams_InMembers. apply in_map_iff.
      apply in_map_iff in Hnc as (a & Ha1 & Ha2).
      exists a. split; [|exact Ha2].
      unfold LSyn.stream_name. rewrite Ha1. exact Hy.
  Qed.


  Lemma clock_name_ok_lift :
    forall vars e e' y,
      (InMembers y (fresh_in e) -> InMembers y (fresh_in e')) ->
      (In y (List.map fst vars) -> In y (List.map fst vars)) ->
      clock_name_ok vars e y -> clock_name_ok vars e' y.
  Proof.
    intros vars e e' y H _ [Hv|Hf]; [now left|right; exact (H Hf)].
  Qed.

  Lemma InMembers_concat_fresh :
    forall y (es : list exp) e,
      In e es -> InMembers y (fresh_in e) ->
      InMembers y (concat (List.map fresh_in es)).
  Proof.
    intros y es e He H.
    apply InMembers_In in H as (a & Ha).
    apply In_InMembers with (b := a). apply in_concat.
    exists (fresh_in e). split; [exact Ha|exact (in_map fresh_in es e He)].
  Qed.

  Lemma wc_node_find :
    forall G f n,
      wc_global G -> find_node f G = Some n -> exists G', wc_node G' n.
  Proof. intros. eapply wc_find_node; eauto. Qed.

  Lemma clock_name_ok_arg :
    forall vars f es ro anns e y,
      In e es -> clock_name_ok vars e y ->
      clock_name_ok vars (Eapp f es ro anns) y.
  Proof.
    intros vars f es ro anns e y He [Hv|Hf]; [now left|right].
    exact (InMembers_fresh_in_Eapp_arg y f es ro anns e He Hf).
  Qed.

  Lemma wc_Eapp_clock_names :
    forall G vars f es ro anns n bck sub,
      wc_global G -> wc_env vars ->
      (forall e, In e es ->
         forall ck, In ck (clockof e) ->
         forall y, In y (ck_vars ck) -> clock_name_ok vars e y) ->
      (forall e, In e es -> forall nc, In nc (nclockof e) ->
         forall y, snd nc = Some y -> clock_name_ok vars e y) ->
      find_node f G = Some n ->
      Forall2 (WellInstantiated bck sub) (idck n.(n_in)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (idck n.(n_out)) (List.map snd anns) ->
      forall ck, In ck (clockof (Eapp f es ro anns)) ->
      forall y, In y (ck_vars ck) ->
        clock_name_ok vars (Eapp f es ro anns) y.
  Proof.
    intros G vars f es ro anns n bck sub HG Henv Hck Hnm Hfind Hin Hout ck Hc y Hy.
    destruct (wc_node_find G f n HG Hfind) as (G' & Hwcn).
    destruct Hwcn as (Hwin & Hwio & _).
    simpl in Hc. apply in_map_iff in Hc as (a & <- & Ha).
    assert (In (snd a) (List.map snd anns)) as Hsa
        by (apply in_map_iff; exists a; split; [reflexivity|exact Ha]).
    destruct (Forall2_in_right _ _ _ _ Hout Hsa) as (xc & Hxc & Hwi).
    destruct Hwi as (Hsub & Hinst).
    unfold clock_of_nclock in Hy.
    (** the base clock is a clock of an argument *)
    assert (Hbck : In bck (clocksof es)).
    { rewrite clocksof_nclocksof.
      eapply WellInstantiated_bck; [exact Hwin| |exact Hin].
      unfold idck. rewrite map_length. exact n.(n_ingt0). }
    (** the output's clock is over the callee's inputs and outputs *)
    assert (Hxcw : wc_clock (idck (n.(n_in) ++ n.(n_out))) (snd xc)).
    { assert (Hin' : In xc (idck (n.(n_in) ++ n.(n_out)))).
      { unfold idck in Hxc |- *. apply in_map_iff in Hxc as (q & <- & Hq).
        apply in_map_iff. exists q. split; [reflexivity|].
        apply in_or_app. right. exact Hq. }
      unfold wc_env in Hwio. rewrite Forall_forall in Hwio.
      exact (Hwio xc Hin'). }
    assert (Hfree : Is_free_in_clock y (fst (snd a)))
        by (apply ck_vars_Is_free; exact Hy).
    destruct (instck_inv bck sub (snd xc) (fst (snd a)) y Hinst Hfree)
      as [Hb|(x' & Hx' & Hfx)].
    - apply Is_free_ck_vars in Hb.
      apply In_clocksof in Hbck as (e & He & Hbe).
      exact (clock_name_ok_arg vars f es ro anns e y He (Hck e He bck Hbe y Hb)).
    - apply Is_free_ck_vars in Hfx.
      pose proof (wc_clock_ck_vars _ _ Hxcw x' Hfx) as Hxn.
      rewrite map_fst_idck, map_app in Hxn. apply in_app_or in Hxn as [Hxn|Hxn].
      + apply in_map_iff in Hxn as (q & Hq1 & Hq2).
        assert (In (x', snd (snd q)) (idck n.(n_in))) as Hq
            by (unfold idck; apply in_map_iff; exists q; split;
                [destruct q as (? & ? & ?); simpl in *; subst; reflexivity
                |exact Hq2]).
        destruct (Forall2_in_left _ _ _ _ Hin Hq) as (nc & Hnc & Hwi').
        destruct Hwi' as (Hsub' & _). simpl in Hsub'.
        rewrite Hx' in Hsub'.
        apply In_nclocksof in Hnc as (e & He & Hne).
        exact (clock_name_ok_arg vars f es ro anns e y He
                 (Hnm e He nc Hne y (eq_sym Hsub'))).
      + apply in_map_iff in Hxn as (q & Hq1 & Hq2).
        assert (In (x', snd (snd q)) (idck n.(n_out))) as Hq
            by (unfold idck; apply in_map_iff; exists q; split;
                [destruct q as (? & ? & ?); simpl in *; subst; reflexivity
                |exact Hq2]).
        destruct (Forall2_in_left _ _ _ _ Hout Hq) as (nc & Hnc & Hwi').
        destruct Hwi' as (Hsub' & _). simpl in Hsub'.
        rewrite Hx' in Hsub'.
        apply in_map_iff in Hnc as (a' & <- & Ha').
        right. apply InMembers_fresh_in_Eapp_anns.
        apply anon_streams_InMembers. apply in_map_iff.
        exists a'. split; [|exact Ha'].
        unfold LSyn.stream_name. exact (eq_sym Hsub').
  Qed.

  (** The names in an expression's clocks. *)
  Theorem wc_exp_clock_names :
    forall G vars,
      wc_global G -> wc_env vars ->
      forall e, wc_exp G vars e ->
      forall ck, In ck (clockof e) ->
      forall y, In y (ck_vars ck) -> clock_name_ok vars e y.
  Proof.
    intros G vars HG Henv e.
    induction e using exp_ind2; intros Hwc ck Hck y Hy;
      inversion Hwc; subst; simpl in Hck.
    - (** const *) destruct Hck as [<-|[]]. simpl in Hy. contradiction.
    - (** var *) destruct Hck as [<-|[]]. left.
      eapply wc_clock_ck_vars; [eapply wc_env_var; eauto|exact Hy].
    - (** var, anonymous *) destruct Hck as [<-|[]]. left.
      eapply wc_clock_ck_vars; [eapply wc_env_var; eauto|exact Hy].
    - (** unop *) destruct Hck as [<-|[]].
      refine (IHe H1 ck0 _ y Hy). rewrite H3. now left.
    - (** binop *) destruct Hck as [<-|[]].
      destruct (IHe1 H3 ck0 ltac:(rewrite H5; now left) y Hy) as [Hv|Hf];
        [now left|right; simpl; apply InMembers_app; now left].
    - (** fby *)
      destruct (Forall2_in_left _ _ _ _ H6 Hck) as (ck' & Hck' & Heq). subst ck'.
      apply In_clocksof in Hck' as (e & He & Hce).
      rewrite Forall_forall in H, H4.
      destruct (H e He (H4 e He) ck Hce y Hy) as [Hv|Hf];
        [now left|right; simpl; apply InMembers_app; left;
                  exact (InMembers_concat_fresh y e0s e He Hf)].
    - (** arrow *)
      destruct (Forall2_in_left _ _ _ _ H6 Hck) as (ck' & Hck' & Heq). subst ck'.
      apply In_clocksof in Hck' as (e & He & Hce).
      rewrite Forall_forall in H, H4.
      destruct (H e He (H4 e He) ck Hce y Hy) as [Hv|Hf];
        [now left|right; simpl; apply InMembers_app; left;
                  exact (InMembers_concat_fresh y e0s e He Hf)].
    - (** when *)
      apply in_map_iff in Hck as (t & <- & _). left. simpl in Hy.
      destruct Hy as [<-|Hy].
      + apply in_map_iff. exists (x, ck0). split; [reflexivity|exact H5].
      + exact (wc_clock_ck_vars _ _ (wc_env_var _ _ _ Henv H5) y Hy).
    - (** merge *)
      apply in_map_iff in Hck as (t & <- & _). left. simpl in Hy.
      exact (wc_clock_ck_vars _ _ (wc_env_var _ _ _ Henv H7) y Hy).
    - (** ite *)
      apply in_map_iff in Hck as (t & <- & _). simpl in Hy.
      destruct (IHe H5 ck0 ltac:(rewrite H8; now left) y Hy) as [Hv|Hf];
        [now left|right; simpl; apply InMembers_app; now left].
    - (** call *)
      assert (HPs : forall e, In e es -> forall ck, In ck (clockof e) ->
                forall y, In y (ck_vars ck) -> clock_name_ok vars e y).
      { intros e He. rewrite Forall_forall in H0, H5. exact (H0 e He (H5 e He)). }
      assert (Hnm : forall e, In e es -> forall nc, In nc (nclockof e) ->
                forall y, snd nc = Some y -> clock_name_ok vars e y).
      { intros e He. rewrite Forall_forall in H5.
        exact (wc_exp_stream_names G vars e (H5 e He)). }
      exact (wc_Eapp_clock_names G vars f es None a n bck sub HG Henv HPs Hnm
               H6 H7 H8 ck Hck y Hy).
    - (** call with reset *)
      assert (HPs : forall e, In e es -> forall ck, In ck (clockof e) ->
                forall y, In y (ck_vars ck) -> clock_name_ok vars e y).
      { intros e He. rewrite Forall_forall in H0, H5. exact (H0 e He (H5 e He)). }
      assert (Hnm : forall e, In e es -> forall nc, In nc (nclockof e) ->
                forall y, snd nc = Some y -> clock_name_ok vars e y).
      { intros e He. rewrite Forall_forall in H5.
        exact (wc_exp_stream_names G vars e (H5 e He)). }
      exact (wc_Eapp_clock_names G vars f es (Some r) a n bck sub HG Henv HPs
               Hnm H6 H7 H8 ck Hck y Hy).
  Qed.

End SecLusClockNames.
