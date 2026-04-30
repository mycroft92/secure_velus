From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Coq Require Import Lia.
From Velus Require Import SymTypes.
From Velus Require Export SIF.SecLattice.
Require Import Coq.Program.Equality.
Import List.ListNotations.

(* Syntactic well-formedness of generated constraints.
   This notion does not depend on the lattice semantics, so it is exposed at
   the file level for the typing/signature developments. *)
Definition wf_constraints (cs: list SymTypes.constraint) : Prop :=
  NoDup (map snd cs) /\ Forall (fun '(_, x) => length x = 1) cs.

Definition constraint_scope (c: SymTypes.constraint) : list ident :=
  fst c ++ snd c.

Definition constraint_scoped (scope: list ident) (c: SymTypes.constraint) : Prop :=
  forall x, In x (constraint_scope c) -> In x scope.

Definition constraints_scoped (scope: list ident) (cns: list SymTypes.constraint) : Prop :=
  Forall (constraint_scoped scope) cns.

Definition st_scoped (scope: list ident) (st: SymTypes.ST) : Prop :=
  forall x, In x st -> In x scope.

Lemma st_scoped_weaken:
  forall scope1 scope2 st,
    incl scope1 scope2 ->
    st_scoped scope1 st ->
    st_scoped scope2 st.
Proof.
  intros scope1 scope2 st Hincl Hsc x Hin.
  apply Hincl, Hsc, Hin.
Qed.

Lemma constraints_scoped_weaken:
  forall scope1 scope2 cns,
    incl scope1 scope2 ->
    constraints_scoped scope1 cns ->
    constraints_scoped scope2 cns.
Proof.
  intros scope1 scope2 cns Hincl Hsc.
  unfold constraints_scoped in *.
  rewrite Forall_forall in *.
  intros c Hin.
  specialize (Hsc c Hin).
  intros x Hinx.
  apply Hincl, Hsc, Hinx.
Qed.

Lemma scope_remove_choice:
  forall pre post (x y : ident),
    In y (pre ++ x :: post) ->
    y = x \/ In y (pre ++ post).
Proof.
  intros pre post x y Hin.
  rewrite in_app_iff in Hin.
  destruct Hin as [Hin|Hin].
  - right. now apply in_or_app; left.
  - simpl in Hin. destruct Hin as [Heq|Hin].
    + now left.
    + right. now apply in_or_app; right.
Qed.

Lemma in_merge_inv:
  forall x a b,
    In x (a ⊔ b) ->
    In x a \/ In x b.
Proof.
  intros x a.
  induction a as [|a0 a IHa]; intros b Hin.
  - assert (Hmerge : merge (@nil ident) b = b).
    { induction b as [|b0 b IHb]; simpl; auto. }
    rewrite Hmerge in Hin.
    right. exact Hin.
  - revert a0 a IHa Hin.
    induction b as [|b0 b IHb]; intros a0 a IHa Hin.
    + assert (Hmerge : merge (a0 :: a) (@nil ident) = (a0 :: a)) by reflexivity.
      rewrite Hmerge in Hin.
      left. exact Hin.
    + simpl in Hin.
      destruct (Pos.compare a0 b0) eqn:Hcmp.
      * simpl in Hin. destruct Hin as [Hin|Hin].
        { subst x. now left; left. }
        apply IHa in Hin. destruct Hin as [Hin|Hin].
        { now left; right. }
        { now right; right. }
      * simpl in Hin. destruct Hin as [Hin|Hin].
        { subst x. now left; left. }
        specialize (IHa (b0 :: b) Hin). destruct IHa as [Hin'|Hin'].
        { now left; right. }
        { now right. }
      * simpl in Hin. destruct Hin as [Hin|Hin].
        { subst x. now right; left. }
        specialize (IHb a0 a IHa Hin). destruct IHb as [Hin'|Hin'].
        { now left. }
        { now right; right. }
Qed.

Lemma st_remove_in_inv:
  forall x y st,
    In y (st_remove x st) ->
    In y st /\ y <> x.
Proof.
  intros x y st.
  induction st as [|a st IH]; simpl; intros Hin.
  - contradiction.
  - destruct (ident_eq_dec x a) as [Heq|Hneq].
    + subst a.
      specialize (IH Hin) as [Hin' Hneq'].
      split; [now right|exact Hneq'].
    + simpl in Hin.
      destruct Hin as [Heq|Hin].
      * subst y. split.
        -- now left.
        -- intro Heq'. apply Hneq. symmetry. exact Heq'.
      * specialize (IH Hin) as [Hin' Hneq'].
        split; [now right|exact Hneq'].
Qed.

Lemma st_scoped_remove_app:
  forall pre post x st,
    st_scoped (pre ++ x :: post) st ->
    st_scoped (pre ++ post) (st_remove x st).
Proof.
  intros pre post x st Hsc y Hin.
  destruct (st_remove_in_inv _ _ _ Hin) as [Hin' Hneq].
  specialize (Hsc y Hin').
  destruct (scope_remove_choice pre post x y Hsc) as [Heq|Hin''].
  - contradiction.
  - exact Hin''.
Qed.

Lemma st_scoped_drop_absent_app:
  forall pre post x st,
    ~ In x st ->
    st_scoped (pre ++ x :: post) st ->
    st_scoped (pre ++ post) st.
Proof.
  intros pre post x st Hnin Hsc y Hin.
  destruct (scope_remove_choice pre post x y (Hsc _ Hin)) as [Heq|Hin'].
  - subst y. contradiction.
  - exact Hin'.
Qed.

Lemma st_scoped_merge:
  forall scope st1 st2,
    st_scoped scope st1 ->
    st_scoped scope st2 ->
    st_scoped scope (st1 ⊔ st2).
Proof.
  intros scope st1 st2 H1 H2 x Hin.
  destruct (in_merge_inv _ _ _ Hin) as [Hin'|Hin']; auto.
Qed.

Lemma constraint_scoped_lhs:
  forall scope lhs rhs x,
    constraint_scoped scope (lhs, rhs) ->
    In x lhs ->
    In x scope.
Proof.
  intros scope lhs rhs x Hsc Hin.
  apply Hsc. unfold constraint_scope. now apply in_or_app; left.
Qed.

Lemma constraint_scoped_rhs:
  forall scope lhs rhs x,
    constraint_scoped scope (lhs, rhs) ->
    In x rhs ->
    In x scope.
Proof.
  intros scope lhs rhs x Hsc Hin.
  apply Hsc. unfold constraint_scope. now apply in_or_app; right.
Qed.

Lemma st_scoped_singleton:
  forall scope x,
    In x scope ->
    st_scoped scope [x].
Proof.
  intros scope x Hin y Hy.
  simpl in Hy. destruct Hy as [Heq|[]]. subst. exact Hin.
Qed.

Lemma findST_of_rhs_in:
  forall cns d,
    In [d] (map snd cns) ->
    exists st, findST cns d = Some st.
Proof.
  induction cns as [|[lhs rhs] cns IH]; intros d Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct rhs as [|r rhs'].
    + destruct Hin as [Heq|Hin].
      * discriminate Heq.
      * apply IH. exact Hin.
    + destruct rhs' as [|r' rhs''].
      * simpl in Hin. destruct Hin as [Heq|Hin].
        -- inversion Heq. subst r.
           exists lhs.
           simpl.
           rewrite ident_eqb_refl.
           reflexivity.
        -- destruct (ident_eqb r d) eqn:Hrd.
           ++ apply ident_eqb_eq in Hrd. subst r.
              exists lhs.
              simpl.
              rewrite ident_eqb_refl.
              reflexivity.
           ++ apply IH in Hin as (st & Hfind).
              exists st.
              simpl.
              rewrite Hrd.
              exact Hfind.
      * destruct Hin as [Heq|Hin].
        -- discriminate Heq.
        -- apply IH. exact Hin.
Qed.

Lemma subST_scoped_elim:
  forall scope ds d lhs st,
    st_scoped (scope ++ d :: ds) lhs ->
    st_scoped (scope ++ d :: ds) st ->
    st_scoped (scope ++ ds) (subST lhs d st).
Proof.
  intros scope ds d lhs st Hlhs Hst.
  unfold subST.
  destruct (st_mem d lhs) eqn:Hmem.
  - destruct (st_mem d st) eqn:Hmem'.
    + eapply st_scoped_merge.
      * eapply st_scoped_remove_app; eauto.
      * eapply st_scoped_remove_app; eauto.
    + eapply st_scoped_merge.
      * eapply st_scoped_remove_app; eauto.
      * eapply st_scoped_drop_absent_app with (x := d); eauto.
        intro Hin. apply my_set_mem_correct in Hin. unfold st_mem in Hmem'. rewrite Hin in Hmem'. discriminate.
  - eapply st_scoped_drop_absent_app with (x := d); eauto.
    intro Hin. apply my_set_mem_correct in Hin. unfold st_mem in Hmem. rewrite Hin in Hmem. discriminate.
Qed.

Lemma subAll_scoped_elim:
  forall scope ds cns d st,
    constraints_scoped (scope ++ d :: ds) cns ->
    st_scoped (scope ++ d :: ds) st ->
    constraints_scoped (scope ++ ds) (subAll cns d st).
Proof.
  induction cns as [|[lhs rhs] cns IH]; intros d st Hsc Hst; simpl.
  - constructor.
  - inversion Hsc as [|c0 cs0 Hc Hcs]; subst c0 cs0.
    destruct rhs as [|r rhs'].
    + exact (IH d st Hcs Hst).
    + destruct rhs' as [|r' rhs''].
      * destruct (ident_eqb r d) eqn:Hrd.
        -- exact (IH d st Hcs Hst).
        -- apply Forall_cons.
           ++ unfold constraint_scoped.
              intros y Hin.
              unfold constraint_scope in Hin.
              apply in_app_iff in Hin.
              destruct Hin as [Hin|Hin].
              ** assert (Hlhs : st_scoped (scope ++ d :: ds) lhs).
                 { intros z Hz.
                   eapply constraint_scoped_lhs with (rhs := [r]); eauto. }
                 pose proof (subST_scoped_elim scope ds d lhs st Hlhs Hst) as Hsub.
                 exact (Hsub y Hin).
              ** simpl in Hin.
                 destruct Hin as [Heq|HinFalse].
                 { subst y.
                   assert (HrScope : In r (scope ++ d :: ds)).
                   { eapply constraint_scoped_rhs with (lhs := lhs) (rhs := [r]); eauto.
                     simpl; left; reflexivity. }
                   destruct (scope_remove_choice scope ds d r HrScope) as [Heqd|Hin'].
                   - apply ident_eqb_neq in Hrd. contradiction.
                   - exact Hin'. }
                 { contradiction. }
           ++ exact (IH d st Hcs Hst).
      * exact (IH d st Hcs Hst).
Qed.

Lemma subAll_preserves_other_rhs:
  forall cns d st d',
    d' <> d ->
    In [d'] (map snd cns) ->
    In [d'] (map snd (subAll cns d st)).
Proof.
  induction cns as [|[lhs rhs] cns IH]; intros d st d' Hneq Hin; simpl in *.
  - contradiction.
  - destruct rhs as [|r rhs'].
    + destruct Hin as [Heq|Hin].
      * discriminate Heq.
      * apply IH; auto.
    + destruct rhs' as [|r' rhs''].
      * simpl in Hin.
        destruct Hin as [Heq|Hin].
        -- inversion Heq; subst r.
           destruct (ident_eqb d' d) eqn:Hd.
           ++ apply ident_eqb_eq in Hd. contradiction.
           ++ simpl. left. reflexivity.
        -- destruct (ident_eqb r d) eqn:Hrd.
           ++ apply IH; auto.
           ++ simpl. right. apply IH; auto.
      * destruct Hin as [Heq|Hin].
        -- discriminate Heq.
        -- apply IH; auto.
Qed.

Theorem simplify_scoped:
  forall scope ds cns,
    NoDup ds ->
    constraints_scoped (scope ++ ds) cns ->
    (forall d, In d ds -> In [d] (map snd cns)) ->
    constraints_scoped scope (simplify cns ds).
Proof.
  intros scope ds.
  induction ds as [|d ds IH]; intros cns Hnd Hsc Hdefs.
  - simpl in *. rewrite app_nil_r in Hsc. exact Hsc.
  - simpl.
    assert (Hrhs : In [d] (map snd cns)) by (apply Hdefs; left; reflexivity).
    destruct (findST_of_rhs_in _ _ Hrhs) as [st Hfind].
    rewrite Hfind.
    apply IH.
    + now apply NoDup_cons_iff in Hnd.
    + assert (Hst_scoped : st_scoped (scope ++ d :: ds) st).
      { intros x Hin.
        pose proof Hsc as Hsc_forall.
        unfold constraints_scoped in Hsc_forall.
        rewrite Forall_forall in Hsc_forall.
        eapply constraint_scoped_lhs with (rhs := [d]).
        - apply Hsc_forall. apply find_correct. exact Hfind.
        - exact Hin. }
      eapply subAll_scoped_elim; eauto.
    + intros d' Hin.
      eapply subAll_preserves_other_rhs.
      * intro Heq. subst d'.
        apply NoDup_cons_iff in Hnd as [Hnin _]. contradiction.
      * apply Hdefs. now right.
Qed.

Module Type SECTYPES(Import Lat: Lattice).
    Import ListNotations.

    Inductive nonCanonST : Type :=
    | Bot : nonCanonST
    | Var : ident -> nonCanonST
    | Lub : nonCanonST -> nonCanonST -> nonCanonST.

    Definition ST := list ident.
    Definition constraint  := (ST*ST)%type.

    Fixpoint my_set_mem (a: ident) (st: ST) : bool :=
        match st with
        | [] => false
        | a0 :: st' => if ident_eqb a0 a then true else my_set_mem a st'
        end.

    Section merge.
      Fail Fixpoint merge (c1 c2: ST): ST :=
      match c1, c2 with
      | [], _ => c2
      | _, [] => c1
      | x::xs, y::ys => match Pos.compare x y with
                              | Lt => x:: (merge xs c2)
                              | Eq => x:: (merge xs ys)
                              | Gt => y:: (merge c1 ys)
                              end
      end.
      (*Cool trick on decreasing arguments*)
      Fixpoint merge (c1:ST)  : ST -> ST :=
          fix merge' c2 :=
            match c1,c2 with
            | [], _ => c2
            | _, [] => c1
            | x::xs, y::ys => match Pos.compare x y with
                              | Lt => x:: (merge xs c2)
                              | Eq => x:: (merge xs ys)
                              | Gt => y:: (merge' ys)
                              end
            end.

      Fixpoint intersect (c1: ST): ST -> ST :=
        fix intersect' c2 :=
          match c1, c2 with
          | [], _ => []
          | _, [] => []
          | x::xs, y::ys => match Pos.compare x y with
                            | Lt => intersect xs c2
                            | Eq => x:: (intersect xs ys)
                            | Gt => intersect' ys
                            end
          end.

      Fixpoint canon (x: nonCanonST): ST :=
        match x with
        | Bot => []
        | Var y => [y]
        | Lub y z => let c1 := canon y in
                     let c2 := canon z in
                     merge c1 c2
        end.

      Lemma merge_nil: forall ls, merge ls [] = ls.
      Proof.
        induction ls; auto.
      Qed.

      Lemma merge_nil2: forall ls, merge [] ls = ls.
      Proof.
        induction ls; auto.
      Qed.

      Lemma intersect_nil: forall ls, intersect ls [] = [].
      Proof.
        induction ls; auto.
      Qed.

      Lemma intersect_nil2: forall ls, intersect [] ls = [].
      Proof.
        induction ls; auto.
      Qed.



      Lemma lt_gt_false: forall a b, (a < b)%positive -> (b < a)%positive -> False.
      Proof.
        assert (RelationClasses.Asymmetric Pos.lt). { apply RelationClasses.StrictOrder_Asymmetric. apply Pos.lt_strorder. }
        apply RelationClasses.asymmetry.
      Qed.

      Lemma intersect_correct: forall x y z, intersect x y = z -> forall a, In a z -> In a x.
      Proof.
        induction x as [|a_0 xs IHx]; intros.
        - rewrite intersect_nil2 in H; subst. auto.
        - induction y as [|b_0 ys IHy].
          * rewrite intersect_nil in H. subst. inversion H0.
          * destruct z.
            + inversion H0.
            + simpl in H. destruct (Pos.compare a_0 b_0) eqn:Eab.
               ++ inversion H. destruct H0 as [Hai | Haz].
                  ** subst. simpl. now left.
                  ** apply IHx with (a:=a) in H3; try right; auto.
               ++  apply IHx with (a:=a) in H; auto. now right.
               ++ apply IHy; auto.
      Qed.

      Lemma intersect_comm: forall x y, intersect x y = intersect y x.
      Proof.
        induction x as [| a_0 xs IHx]; intros.
        - now rewrite intersect_nil2, intersect_nil.
        - induction y as [| b_0 ys IHy].
          * now rewrite intersect_nil2, intersect_nil.
          * simpl. destruct (Pos.compare a_0 b_0) eqn:Eab; destruct (Pos.compare b_0 a_0) eqn:Eba.
            + apply Pos.compare_eq_iff in Eab. subst. rewrite IHx. auto.
            (*impossible cases*)
            + apply Pos.compare_eq_iff in Eab. subst. apply Pos.lt_irrefl in Eba. elim Eba.
            + apply Pos.compare_eq_iff in Eab. subst. rewrite Pos.compare_gt_iff in Eba. apply Pos.lt_irrefl in Eba. elim Eba.
            + apply Pos.compare_eq_iff in Eba. subst. apply Pos.lt_irrefl in Eab. elim Eab.
            + rewrite Pos.compare_lt_iff in Eab. rewrite Pos.compare_lt_iff in Eba. elim (lt_gt_false a_0 b_0 Eab Eba).
            (*normal cases*)
            + rewrite IHx. auto.
            (*impossible*)
            + apply Pos.compare_eq_iff in Eba. subst. rewrite Pos.compare_gt_iff in Eab. apply Pos.lt_irrefl in Eab. elim Eab.

            + rewrite <- IHy. auto.
            (*impossible*)
            + rewrite Pos.compare_gt_iff in Eba. rewrite Pos.compare_gt_iff in Eab. elim (lt_gt_false b_0 a_0 Eab Eba).
      Qed.

      Lemma intersect_correct2: forall x y z, intersect y x = z -> forall a, In a z -> In a x.
      Proof.
        intros. rewrite intersect_comm in H. eapply intersect_correct; eauto.
      Qed.

      Lemma merge_comm: forall ls1 ls2, merge ls1 ls2 = merge ls2 ls1.
      Proof.
        induction ls1; intros.
        - rewrite merge_nil, merge_nil2. auto.
        - induction ls2 as [|b bs IHls2].
          * rewrite merge_nil, merge_nil2. auto.
          * simpl. destruct (Pos.compare a b) eqn:Eab.
            + destruct (Pos.compare b a) eqn:Eba.
              ++ rewrite (IHls1 bs). apply Pos.compare_eq_iff in Eab. subst; auto.
              ++ rewrite Pos.compare_eq_iff in Eab. subst.  rewrite Pos.compare_lt_iff in Eba. apply Pos.lt_irrefl in Eba. elim Eba.
              ++ rewrite Pos.compare_eq_iff in Eab. subst.  rewrite Pos.compare_gt_iff in Eba. apply Pos.lt_irrefl in Eba. elim Eba.
            + destruct  (Pos.compare b a) eqn:Eba.
              ++  rewrite Pos.compare_eq_iff in Eba. subst.  rewrite Pos.compare_lt_iff in Eab. apply Pos.lt_irrefl in Eab. elim Eab.
              ++  rewrite Pos.compare_lt_iff in Eab. rewrite Pos.compare_lt_iff in Eba. elim (lt_gt_false a b Eab Eba).
              ++  rewrite (IHls1 (b::bs)). reflexivity.
            + destruct (Pos.compare b a) eqn:Eba.
              ++ rewrite Pos.compare_eq_iff in Eba. subst.  rewrite Pos.compare_gt_iff in Eab. apply Pos.lt_irrefl in Eab. elim Eab.
              ++ rewrite <-IHls2. reflexivity.
              ++ rewrite  Pos.compare_gt_iff in Eab. rewrite Pos.compare_gt_iff in Eba.  elim (lt_gt_false b a Eab Eba).
      Qed.
    End merge.

    Hint Unfold my_set_mem.

    Lemma my_set_mem_correct: forall a st, my_set_mem a st = true <-> In a st.
    Proof.
        intros. generalize dependent a. induction st; split; intros; auto.
        - inversion H.
        - simpl in H. destruct (ident_eqb a a0) eqn:E.
            * apply (ident_eqb_eq) in E. subst. simpl. left. auto.
            * apply (ident_eqb_neq) in E. simpl. right. now apply IHst...
        - simpl.  destruct (ident_eqb a a0) eqn:E.
            * auto.
            * apply (ident_eqb_neq) in E. simpl in H.
              destruct H as [H1|H2]. elim (E H1). (*a0 = a*)
              now apply IHst.
    Qed.

    Fixpoint my_set_union (st_1 st_2: ST): ST :=
    match st_2 with
    | []     => st_1
    | a::st_2' => if my_set_mem a st_1 then my_set_union st_1 st_2'
                else a:: (my_set_union st_1 st_2')
    end.


  Hint Resolve my_set_mem_correct.
  Hint Unfold my_set_union.


  Fixpoint hm_ext (delta: ident -> Lat.t ) (xs: ST): Lat.t :=
    match xs with
    | nil   => Lat.bottom
    | x::xs' => join  (delta x) (hm_ext delta xs')
    end.

  Definition st_remove := List.remove ident_eq_dec.
  Definition st_mem    := my_set_mem.
  (*Local hint data bases from Lattices*)
  Hint Immediate eq_sym.
  Hint Resolve merge_nil merge_nil2 merge_comm intersect_nil intersect_nil2 intersect_comm eq_refl eq_trans eqb_refl
               order_refl order_antisym order_trans
               join_bound1 join_bound2 join_least_upper_bound
               meet_bound1 meet_bound2 meet_greatest_lower_bound
               bottom_is_bottom top_is_top.

  Lemma hm_ext_list_in1 : forall dlt st d,
    In d st -> dlt d ⊑ hm_ext dlt st.
  Proof.
    intros dlt st. induction st as [|a st' IHst];  intros * H; simpl in H.
    - destruct H.
    - destruct H as [Hl| Hr] eqn:E; simpl.
      * subst a; auto.
      * eapply order_trans. eapply IHst. assumption. eapply join_bound2.
  Qed.
  Lemma hm_ext_list_in2 : forall dlt st d,
    hm_ext dlt st ⊑ hm_ext dlt (d::st).
  Proof.
    induction st as [|a st IHst]; simpl; auto.
  Qed.

  Lemma set_rm_lub_l : forall dlt (d:Lat.t) (d_0:ident) (st:ST),
    hm_ext dlt (d_0::st) ⊑ d -> dlt d_0 ⊑ d.
  Proof.
    intros * H. simpl in *.
    eapply order_trans. eapply join_bound1. eapply H.
  Qed.

  Lemma set_rm_lub_r : forall dlt (d:Lat.t) (d_0:ident) (st:ST),
    hm_ext dlt (d_0::st) ⊑ d -> hm_ext dlt st ⊑ d.
  Proof.
    intros * H. simpl in *. apply join_upper_bound_r in H; auto.
  Qed.

  Lemma set_rm_lub_l_d : forall dlt (d d_0:ident) (st:ST),
    hm_ext dlt (d_0::st) ⊑ dlt d -> dlt d_0 ⊑ dlt d.
  Proof.
    intros dlt d d_0 st. apply set_rm_lub_l.
  Qed.

  Lemma set_rm_lub_r_d : forall dlt (d d_0:ident) (st:ST),
    hm_ext dlt (d_0::st) ⊑ dlt d -> hm_ext dlt st ⊑ dlt d.
  Proof.
    intros dlt d d_0 st. apply set_rm_lub_r.
  Qed.

  Lemma set_rm_lub2 : forall dlt  (d:Lat.t) (d_0:ident) (st:ST),
    hm_ext dlt st ⊑ d -> hm_ext dlt (st_remove d_0 st) ⊑ d.
  Proof.
    intros dlt. induction st as [| a st' IHst]; intros * H. simpl in *. auto.
    destruct (ident_eq_dec d_0 a) as [Heq|Hneq] eqn:E;  intros;simpl.
      - subst a. rewrite E.  apply join_upper_bound_r in H; auto.
      - rewrite E. apply set_rm_lub_r in H as H'.
       eapply join_least_upper_bound. eapply set_rm_lub_l in H; eassumption.
       apply IHst. auto.
  Qed.

  Hint Resolve  set_rm_lub_l set_rm_lub_r hm_ext_list_in1 hm_ext_list_in2 set_rm_lub2
                set_rm_lub_r_d set_rm_lub_l_d.

  Lemma set_union_null : forall st1,
      my_set_union  [] st1 = st1.
  Proof.
    intros. induction st1 as [|a st' IHst]; simpl;
    try (rewrite IHst); auto.
  Qed.


  Lemma hm_ext_distributive : forall (dlt:ident -> Lat.t) (st1 st2: ST) d1,
    hm_ext dlt st1 ⊑ d1 ->
    hm_ext dlt st2 ⊑ d1 -> hm_ext dlt (st2 ⊔ st1) ⊑ d1.
  Proof.
    induction st1 as [|a st' IHst]; intros * H1 H2.
    - rewrite merge_nil. auto.
    - rewrite merge_comm. simpl.
      induction st2 as [|b st2 IHst2].
      * auto.
      * destruct (Pos.compare a b) eqn:Hab.
        + apply set_rm_lub_r in H1 as H3. apply set_rm_lub_r in H2 as H4.
          simpl. apply join_least_upper_bound. simpl in *. apply join_upper_bound_l in H1 as H5; auto.
          rewrite merge_comm; auto.
        + simpl. simpl in H1. apply join_upper_bound_l in H1 as H5.  apply join_upper_bound_r in H1 as H6.
          apply join_least_upper_bound; auto. rewrite merge_comm. apply IHst; auto.
        + simpl.  apply join_least_upper_bound. apply join_upper_bound_l in H2 as H5. assumption.
          apply IHst2. apply join_upper_bound_r in H2 as H6. assumption.
    Qed.


  Lemma hm_ext_concat_l : forall dlt a b,
     hm_ext dlt a ⊑ hm_ext dlt (a ⊔ b).
  Proof.
    intros dlt a. induction a as [|a_0 a IHa]; auto.
    intros. apply join_least_upper_bound.
    - induction b as [|b_0 b IHb].
        + simpl. apply join_bound1.
        + simpl. destruct (Pos.compare a_0 b_0) eqn:E.
          * simpl. apply join_bound1.
          * simpl. apply join_bound1.
          * rewrite merge_comm in IHb. apply order_trans with (y:=hm_ext dlt (b ⊔ (a_0::a))). apply IHb.
            rewrite merge_comm. simpl. auto.
    - fold hm_ext. induction b as [|b_0 b IHb]. simpl.
        + auto.
        + simpl. destruct (Pos.compare a_0 b_0) eqn:E.
          * simpl. apply order_trans with (y:= hm_ext dlt (a ⊔ b)); auto.
          * simpl. apply order_trans with (y:= hm_ext dlt (a ⊔ (b_0 :: b))); auto.
          * rewrite merge_comm in IHb. apply order_trans with (y:=hm_ext dlt (b ⊔ (a_0::a))). apply IHb.
            rewrite merge_comm. simpl. auto.
  Qed.


  Lemma hm_ext_concat_r : forall dlt a b,
    hm_ext dlt b ⊑ hm_ext dlt (a ⊔ b).
  Proof.
    intros. rewrite merge_comm. apply hm_ext_concat_l.
  Qed.

  Lemma order_comm1 : forall dlt a b c,
      hm_ext dlt b ⊑ hm_ext dlt (a ⊔ (b ⊔ c)).
  Proof.
    intros.  eapply order_trans. eapply hm_ext_concat_l.
    eapply hm_ext_concat_r.
  Qed.

  Lemma order_comm2 : forall dlt a b c,
    hm_ext dlt c ⊑ hm_ext dlt (a ⊔ b ⊔ c).
  Proof.
    intros. eapply order_trans. eapply hm_ext_concat_r. eauto.
  Qed.
  Import MergeFacts.
  Lemma hm_ext_distributive2: forall st1 st2 dlt,  hm_ext dlt (st1 ⊔ st2) ⊑ join (hm_ext dlt st1) (hm_ext dlt st2).
  Proof.
    intros st1 st2 dlt.
    rewrite merge_comm.
    eapply hm_ext_distributive.
    - apply join_bound1.
    - apply join_bound2.
  Qed.
  Hint Resolve hm_ext_concat_l hm_ext_concat_r  hm_ext_distributive
  hm_ext_distributive2  hm_ext_list_in1.

  (*Constraints and substitutions*)
  (*Under dlt, s_0 ⊑ s_1 *)
  Definition satisfiable (dlt: ident -> Lat.t) (s_0 s_1: ST) :=
    (hm_ext dlt s_0) ⊑ (hm_ext dlt s_1).

  Definition constraintSatisfiable (dlt: ident-> Lat.t) (c: constraint) := let (lhs, rhs) := c in
    satisfiable dlt lhs rhs.

  Definition listSatisfiable (dlt: ident -> Lat.t) (cns: list constraint) := Forall (fun c => constraintSatisfiable dlt c) cns.
    (* Forall (fun '(s,x) => satisfiable dlt s x) cns. *)

  Hint Unfold satisfiable constraintSatisfiable listSatisfiable.

  Fixpoint findST cns d: option ST :=
    match cns with
    | []  => None
    | (st,[d'])::cns'  => if ident_eqb d' d then Some st else findST cns' d
    | _ :: cns'        => findST cns' d
    end.

  Lemma find_correct : forall cs d v,
    findST cs d = Some v -> List.In (v,[d]) cs.
  Proof.
    induction cs as [| (st',d') cs' IHcs]; intros d_0 v H; simpl in H.
    - inversion H.
    - destruct d'  as [|d_1 d''] eqn:E' in H.
      * apply IHcs in H. simpl. right. auto.
      * destruct d''.
        + destruct (ident_eqb d_1 d_0) eqn:E in H.
          ** apply ident_eqb_eq in E. subst. inversion H. simpl. auto.
          ** simpl. right. apply IHcs. auto.
        + apply IHcs in H. simpl. right. auto.
  Qed.

  Example NoDup_1:  (NoDup [[1];[2]]).
  Proof. apply NoDup_cons.
  - unfold not. intros. unfold In in H.
    destruct H as [Hl |Hr]; [congruence | destruct Hr].
  - apply NoDup_cons.
    * unfold not. intros. unfold In in H. destruct H.
    * apply NoDup_nil.
  Qed.

  Lemma NoDup_filter : forall {A:Type} (f: A -> bool) (l: list A), NoDup l -> NoDup (filter f l).
  Proof.
    induction l; simpl; intros Hnd; auto.
    apply NoDup_cons_iff in Hnd.
    destruct (f a); [ | intuition ].
    apply NoDup_cons_iff; split; intuition.
    apply filter_In in H; intuition.
  Qed.



  Definition wf_constraints (cs: list constraint) : Prop :=
    NoDup (map snd cs) /\ Forall (fun '(_,x) => length x = 1 ) cs.

  (*Properties of well formed constraints*)
  Lemma wf_constraints_no_nil: forall x cs,
    wf_constraints (x::cs) -> wf_constraints cs.
  Proof.
    intros * H.  unfold wf_constraints in *. destruct H as [Hl Hr]. split.
    - apply NoDup_cons_iff in Hl as [Hll Hlr]. apply Hlr.
    - inversion Hr. auto.
  Qed.

  Hint Resolve wf_constraints_no_nil.
  Hint Unfold wf_constraints.

  Lemma list_len_1 : forall A (x:list A), length x = 1 <-> exists d, x = [d].
  Proof.
    split.
    - intros. unfold length in H. destruct x eqn:E in H.
      * discriminate H.
      * injection H. intros H_0. assert (l =[]).
        + apply length_zero_iff_nil in H_0. auto.
        + exists a. subst l. auto.
    - intros. destruct H. subst x. reflexivity.
  Qed.

  Lemma wf_constraints_shape : forall cs x y,
    wf_constraints cs -> List.In (y,x) cs -> exists d, x = [d].
  Proof.
    intros * H_0 H_1. unfold wf_constraints in H_0. destruct H_0 as [Hl Hr].
    rewrite Forall_forall in Hr. apply Hr in H_1 as Hres. apply list_len_1. auto.
  Qed.

  Hint Resolve list_len_1 wf_constraints_shape.


  Hint Resolve find_correct.

  (** Extending a valuation with one eliminated variable.

      When [d] is eliminated using its defining symbolic type [st], the
      reconstructed valuation keeps every other identifier unchanged and maps
      [d] to the interpretation of [st] with [d] removed. *)
  Definition complete_subst (dlt: ident -> Lat.t) (d: ident) (st: ST)
    : ident -> Lat.t :=
    fun x => if ident_eqb x d then hm_ext dlt (st_remove d st) else dlt x.

  Lemma complete_subst_neq:
    forall dlt d st x,
      x <> d ->
      complete_subst dlt d st x = dlt x.
  Proof.
    intros dlt d st x Hneq.
    unfold complete_subst.
    rewrite (proj2 (ident_eqb_neq x d) Hneq).
    reflexivity.
  Qed.

  Lemma complete_subst_eq:
    forall dlt d st,
      complete_subst dlt d st d = hm_ext dlt (st_remove d st).
  Proof.
    intros dlt d st.
    unfold complete_subst.
    now rewrite ident_eqb_refl.
  Qed.

  Lemma st_remove_notin:
    forall d st,
      my_set_mem d st = false ->
      st_remove d st = st.
  Proof.
    intros d st.
    induction st as [|a st IH]; intro Hmem; simpl in *; auto.
    destruct (ident_eqb d a) eqn:Hda.
    - apply ident_eqb_eq in Hda. subst a.
      rewrite ident_eqb_refl in Hmem.
      discriminate.
    - apply ident_eqb_neq in Hda.
      unfold st_remove. simpl.
      destruct (ident_eq_dec d a) as [Heq|Hneq].
      + contradiction.
      + assert (Hda' : ident_eqb a d = false).
        { apply (proj2 (ident_eqb_neq a d)). congruence. }
        rewrite Hda' in Hmem.
        f_equal. apply IH. exact Hmem.
  Qed.

  Lemma st_remove_preserves_other_in:
    forall x d st,
      x <> d ->
      In x st ->
      In x (st_remove d st).
  Proof.
    intros x d st Hneq Hin.
    induction st as [|a st IH]; simpl in *.
    - contradiction.
    - destruct Hin as [->|Hin].
      + unfold st_remove. simpl.
        destruct (ident_eq_dec d x) as [Heq|Hneq'].
        * symmetry in Heq. contradiction.
        * left; reflexivity.
      + unfold st_remove. simpl.
        destruct (ident_eq_dec d a) as [Heq|Hneq'].
        * subst a. apply IH. exact Hin.
        * right. apply IH. exact Hin.
  Qed.

  Lemma hm_ext_bound_from_members:
    forall (dlt: ident -> Lat.t) st b,
      (forall x, In x st -> dlt x ⊑ b) ->
      hm_ext dlt st ⊑ b.
  Proof.
    intros dlt st.
    induction st as [|a st IH]; intros b Hbound; simpl.
    - apply bottom_is_bottom.
    - apply join_least_upper_bound.
      + apply Hbound. left; reflexivity.
      + apply IH. intros x Hin.
        apply Hbound. right; exact Hin.
  Qed.

  (* Substitute symbolic type [st'] for identifier [d] in [st].  If [d] does
     not appear in [st], the original symbolic type is unchanged. *)
  Definition subST st d st' : ST :=
  match st_mem d st with
  | false => st
  | true =>
      if st_mem d st'
      then (st_remove d st) ⊔ (st_remove d st')
      else (st_remove d st) ⊔ st'
  end.

  Lemma subST_complete_bound:
    forall dlt st d st',
      hm_ext (complete_subst dlt d st') st ⊑ hm_ext dlt (subST st d st').
  Proof.
    intros dlt st d st'.
    destruct (st_mem d st) eqn:Hmem.
    - apply hm_ext_bound_from_members.
      intros x Hin.
      destruct (ident_eqb x d) eqn:Hxd.
      + apply ident_eqb_eq in Hxd. subst x.
        rewrite complete_subst_eq.
        unfold subST. rewrite Hmem.
        destruct (st_mem d st') eqn:Hmem'.
        * eapply order_trans; [apply hm_ext_concat_r | apply order_refl, eq_refl].
        * rewrite st_remove_notin by exact Hmem'.
          eapply order_trans; [apply hm_ext_concat_r | apply order_refl, eq_refl].
      + apply ident_eqb_neq in Hxd.
        rewrite complete_subst_neq by exact Hxd.
        assert (Hin' : In x (st_remove d st)).
        { eapply st_remove_preserves_other_in; eauto. }
        unfold subST. rewrite Hmem.
        destruct (st_mem d st') eqn:Hmem'.
        * eapply order_trans; [eapply hm_ext_list_in1; exact Hin' | apply hm_ext_concat_l].
        * eapply order_trans; [eapply hm_ext_list_in1; exact Hin' | apply hm_ext_concat_l].
    - apply hm_ext_bound_from_members.
      intros x Hin.
      assert (x <> d).
      { intro Heq. subst x.
        apply my_set_mem_correct in Hin.
        unfold st_mem in Hmem.
        rewrite Hmem in Hin.
        discriminate. }
      rewrite complete_subst_neq by exact H.
      unfold subST. rewrite Hmem.
      eapply hm_ext_list_in1; exact Hin.
  Qed.

  Lemma complete_subst_satisfies_def:
    forall dlt d st,
      satisfiable (complete_subst dlt d st) st [d].
  Proof.
    intros dlt d st.
    unfold satisfiable. simpl.
    rewrite complete_subst_eq.
    rewrite <- join_bottom_eq1.
    eapply order_trans.
    - apply subST_complete_bound.
    - unfold subST.
      destruct (st_mem d st) eqn:Hmem.
      + destruct (st_mem d st) eqn:Hmem'; [|congruence].
        apply hm_ext_distributive.
        * apply order_refl, eq_refl.
        * apply order_refl, eq_refl.
      + rewrite st_remove_notin by exact Hmem.
        apply order_refl, eq_refl.
  Qed.

  (*Substituting st_0 for d in st (results in st_1),             *)
  (*preseves satisfiability of st ⊑ x (meaning st_1 ⊑ x)        *)
  (*provided st_0 ⊑ [d]                                         *)
  Lemma subST_correct : forall dlt st x d st_0 st_1,
    satisfiable dlt st_0 [d] -> satisfiable dlt st x -> subST st d st_0 = st_1 -> satisfiable dlt st_1 x.
  Proof.
    intros * H_0 H_1 H_2. unfold satisfiable in *. simpl in H_0.
    rewrite <- join_bottom_eq1 in H_0. subst st_1.
    unfold subST.
    destruct (st_mem d st) eqn:Edst; auto.
    destruct (st_mem d st_0) eqn:Edst_0.
      * apply hm_ext_distributive.
        + apply set_rm_lub2. apply my_set_mem_correct in Edst.
          apply hm_ext_list_in1 with (dlt:=dlt) in Edst.
          eapply order_trans. eauto. eapply order_trans; eauto.
        + auto.
      * apply hm_ext_distributive.
        + apply my_set_mem_correct in Edst. apply hm_ext_list_in1 with (dlt:=dlt) in Edst.
          eapply order_trans. eauto. eapply order_trans; eauto.
        + auto.
  Qed.

  Hint Resolve subST_correct.

  (*Substituting ident: d with st' in a list of constraints cns  *)
  (*substitution also removes duplicate constraints with the     *)
  (*ident that is being removed(case 2), we only sub valid cns:3 *)
  Fixpoint subAll cns d st' : list constraint :=
    match cns with
    | [] => []
    | (st, [d'])::cns' => if ident_eqb d' d then
                          subAll cns' d st'
                        else ((subST st d st'),[d']):: (subAll cns' d st')
    | _ :: cns'   => subAll cns' d st'
    end.

  (* Check Forall_inv.
  Check Forall_inv_tail.
  Check Forall_cons. *)
  Lemma subAll_is_correct :  forall dlt cns d v cns',
    satisfiable dlt v [d] ->
    subAll cns d v = cns' -> listSatisfiable dlt cns -> listSatisfiable dlt cns'.
  Proof.
    intros dlt cns d v. induction cns as [|(l,r) cns IHcns];
    intros * H_0 H_1 H_2 ; simpl in H_1.
    - subst. assumption.
    - destruct r as [|d_0 r_0] eqn:Er.
      (*r is empty*)
      * inversion H_2. apply IHcns; auto.
      (*r is a list with one or more elems*)
      * destruct r_0 as [|r_1] eqn:El in H_1.
        (*r has exactly one elem: d_0*)
        + subst r_0. destruct (ident_eqb d_0 d) eqn:Edd_0.
          (*d_0 = d*)
          ** inversion H_2. apply IHcns; auto.
          (*d_0 /=d*)
          ** subst cns'. unfold listSatisfiable in *. apply Forall_cons.
            (*Newly generated constraint after subbing d is sat*)
            ++ remember (subST l d v) as st_0 eqn:Hst_0. symmetry in Hst_0.
               apply Forall_inv in H_2 as H_2'. apply (subST_correct dlt l [d_0] d v st_0); auto.
            (*induction case*)
            ++ remember (subAll cns d v) as cns_0 eqn:Hcns_0. inversion  H_2; auto.
        (*r has more than one elem, no substitution happens*)
        + inversion H_2. auto.
  Qed.
  Hint Resolve subAll_is_correct.
  (*Skipping subAll_noDup and subAll_notin, since the main proof doesn't use it*)

  Lemma subAll_rhs_in:
    forall cns d st rhs,
      In rhs (map snd (subAll cns d st)) ->
      In rhs (map snd cns).
  Proof.
    induction cns as [|(lhs, rhs0) cns IH]; intros d st rhs Hin; simpl in *.
    - contradiction.
    - destruct rhs0 as [|d0 rhs0'].
      + right. eapply IH; eauto.
      + destruct rhs0' as [|r rhs0'].
        * destruct (ident_eqb d0 d) eqn:Hd0.
          -- right. eapply IH; eauto.
          -- simpl in Hin. destruct Hin as [Heq|Hin].
             ++ subst rhs. left. reflexivity.
             ++ right. eapply IH; eauto.
        * right. eapply IH; eauto.
  Qed.

  Lemma subAll_wf:
    forall cns d st,
      wf_constraints cns ->
      wf_constraints (subAll cns d st).
  Proof.
    induction cns as [|(lhs, rhs) cns IH]; intros d st Hwf; simpl.
    - split; constructor.
    - destruct Hwf as [Hnd Hfor].
      apply NoDup_cons_iff in Hnd as [Hnotin Hndtail].
      inversion Hfor as [|[lhs' rhs'] cns' Hlen Hfortail]; subst lhs' rhs' cns'; clear Hfor.
      apply list_len_1 in Hlen as [d0 Hr]. subst rhs.
      destruct (ident_eqb d0 d) eqn:Hd0.
      + eapply IH. split; eauto.
      + specialize (IH d st (conj Hndtail Hfortail)) as [Hnd' Hfor'].
        split.
        * apply NoDup_cons.
          -- intro Hin.
             apply Hnotin.
             eapply subAll_rhs_in; eauto.
          -- exact Hnd'.
        * apply Forall_cons.
          -- simpl. reflexivity.
          -- exact Hfor'.
  Qed.

  (** Completeness of one substitution pass when the eliminated identifier no
      longer has a defining constraint in the remaining list.

      This is the tail case needed by [subAll_complete] after removing the
      unique defining constraint guaranteed by [wf_constraints]. *)
  Lemma subAll_complete_none:
    forall dlt cns d v cns',
      wf_constraints cns ->
      findST cns d = None ->
      subAll cns d v = cns' ->
      listSatisfiable dlt cns' ->
      listSatisfiable (complete_subst dlt d v) cns.
  Proof.
    induction cns as [|(lhs, rhs) cns IH]; intros d v cns' Hwf Hfind Hsub Hsat; simpl in *.
    - subst cns'. constructor.
    - destruct Hwf as [Hnd Hfor].
      apply NoDup_cons_iff in Hnd as [Hnotin Hndtail].
      inversion Hfor as [|[lhs' rhs'] cns0 Hlen Hfortail]; subst lhs' rhs' cns0; clear Hfor.
      apply list_len_1 in Hlen as [d0 Hr]. subst rhs.
      destruct (ident_eqb d0 d) eqn:Hd0.
      + discriminate Hfind.
      + apply ident_eqb_neq in Hd0.
        rewrite <- Hsub in Hsat.
        inversion Hsat as [|c cs Hhead Htail]; subst c cs.
        apply Forall_cons.
        * unfold constraintSatisfiable, satisfiable in *.
          simpl in Hhead |- *.
          eapply order_trans.
          -- apply subST_complete_bound.
          -- rewrite complete_subst_neq; eauto.
        * eapply IH with (cns' := subAll cns d v); eauto.
  Qed.

  Theorem subAll_complete:
    forall dlt cns d v cns',
      wf_constraints cns ->
      findST cns d = Some v ->
      subAll cns d v = cns' ->
      listSatisfiable dlt cns' ->
      listSatisfiable (complete_subst dlt d v) cns.
  Proof.
    induction cns as [|(lhs, rhs) cns IH]; intros d v cns' Hwf Hfind Hsub Hsat; simpl in *.
    - discriminate.
    - destruct Hwf as [Hnd Hfor].
      apply NoDup_cons_iff in Hnd as [Hnotin Hndtail].
      inversion Hfor as [|[lhs' rhs'] cns0 Hlen Hfortail]; subst lhs' rhs' cns0; clear Hfor.
      apply list_len_1 in Hlen as [d0 Hr]. subst rhs.
      destruct (ident_eqb d0 d) eqn:Hd0.
      + apply ident_eqb_eq in Hd0. subst d0.
        inversion Hfind; subst v.
        apply Forall_cons.
        * apply complete_subst_satisfies_def.
        * assert (Hfind_tail : findST cns d = None).
          { destruct (findST cns d) eqn:Htail; auto.
            exfalso.
            apply find_correct in Htail.
            apply Hnotin.
            apply in_map with (f := snd) in Htail.
            simpl in Htail.
            exact Htail. }
          eapply subAll_complete_none with (cns' := cns'); eauto.
      + apply ident_eqb_neq in Hd0.
        rewrite <- Hsub in Hsat.
        inversion Hsat as [|c cs Hhead Htail]; subst c cs.
        apply Forall_cons.
        * unfold constraintSatisfiable, satisfiable in *.
          simpl in Hhead |- *.
          eapply order_trans.
            -- apply subST_complete_bound.
            -- rewrite complete_subst_neq; eauto.
        * eapply IH with (cns' := subAll cns d v); eauto.
  Qed.

  (*Substitutes a given ident d by searching in the list of constraints: cns for (v,[d])*)


  (*We currently don't have wellformedness baked into simplify but subST and subALL enforce them*)
  (*We might need a seperate result that the constraints generated from NL are always wellformed*)
  Inductive simplifyRel  : list constraint -> list ident ->  list constraint -> Prop :=
  | baseCase  : forall cns,
    simplifyRel cns [] cns
  | elimCase1 : forall cns d st_0 cns' ds cns'',
    simplifyRel cns' ds cns'' ->
    findST cns d = Some st_0 ->
    subAll cns d st_0 = cns' ->
    simplifyRel cns (d::ds)  cns''
  | elimCase2 : forall cns d cns' ds,
    findST cns d = None ->
    simplifyRel cns ds cns' ->
    simplifyRel cns (d::ds) cns'.

  Hint Constructors simplifyRel.

  Theorem simplify_is_correct : forall (dlt: ident -> Lat.t) cns cns' d,
    listSatisfiable dlt cns -> simplifyRel cns d cns' -> listSatisfiable dlt cns'.
  Proof.
    intros dlt cns cns' d H_0 H_1. induction H_1; auto. (*base cases are trivial*)
    (*induction case*)
    apply find_correct in H. apply subAll_is_correct with (dlt:=dlt) in H0; auto.
    (*We need to show that the constraint that is being substituted was originally satisfiable*)
    (*But this is trivial since it's part of a list of constraints that were ALL satisfiable*)
    rewrite -> (Forall_forall (fun '(s, x) => satisfiable dlt s x) cns) in H_0. apply H_0 in H. auto.
  Qed.

  Theorem simplifyRel_wf:
    forall cns ds cns',
      wf_constraints cns ->
      simplifyRel cns ds cns' ->
      wf_constraints cns'.
  Proof.
    intros cns ds cns' Hwf Hsimp.
    induction Hsimp.
    - exact Hwf.
    - apply IHHsimp.
      rewrite <- H0.
      eapply subAll_wf; eauto.
    - apply IHHsimp. exact Hwf.
  Qed.

  Theorem simplifyRel_complete:
    forall cns ds cns' scope dlt,
      wf_constraints cns ->
      simplifyRel cns ds cns' ->
      (forall x, In x ds -> ~ In x scope) ->
      listSatisfiable dlt cns' ->
      exists dlt',
        (forall x, In x scope -> dlt x = dlt' x)
        /\ listSatisfiable dlt' cns.
  Proof.
    intros cns ds cns' scope dlt Hwf Hsimp.
    revert scope dlt Hwf.
    induction Hsimp; intros scope dlt Hwf Hdisj Hsat.
    - exists dlt. split; auto.
    - assert (Hwf' : wf_constraints cns').
      { rewrite <- H0. eapply subAll_wf; eauto. }
      specialize (IHHsimp scope dlt Hwf').
      assert (Hdisj' : forall x : ident, In x ds -> ~ In x scope).
      { intros x Hin. apply Hdisj. right; exact Hin. }
      specialize (IHHsimp Hdisj' Hsat) as (dlt1 & Hagree1 & Hsat1).
      exists (complete_subst dlt1 d st_0). split.
      + intros x Hin.
        rewrite Hagree1 by exact Hin.
        rewrite complete_subst_neq.
        * reflexivity.
        * intro Heq. subst x.
          apply (Hdisj d).
          -- left; reflexivity.
          -- exact Hin.
      + eapply subAll_complete; eauto.
    - eapply IHHsimp; eauto.
      intros x Hin.
      apply Hdisj.
      right; exact Hin.
  Qed.

  Fixpoint simplify (cns: list constraint) (ds: list ident) : list constraint :=
    match ds with
    | []    => cns
    | d::ds' => match findST cns d with
               | None    => simplify cns ds'
               | Some st => simplify (subAll cns d st) ds'
               end
    end.
  Hint Unfold simplify.

  (* Fixpoint simplify2 (cns: list constraint) (d: ident): list constraints :=
    match cns with
    | []  *)
  Lemma simplify_simplifyRel: forall ds cns  cns', simplify cns ds = cns' -> simplifyRel cns ds cns'.
  Proof.
    induction ds; intros.
    - cbn in H. subst. auto.
    - cbn in H. destruct (findST cns a) eqn:E.
      * remember (subAll cns a s) as cns''. eapply elimCase1; eauto.
      * apply elimCase2; auto.
  Qed.

  Corollary simplify_wf:
    forall cns ds,
      wf_constraints cns ->
      wf_constraints (simplify cns ds).
  Proof.
    intros cns ds Hwf.
    eapply simplifyRel_wf; eauto.
    eapply simplify_simplifyRel. reflexivity.
  Qed.

  Corollary simplify_complete:
    forall cns ds scope dlt,
      wf_constraints cns ->
      (forall x, In x ds -> ~ In x scope) ->
      listSatisfiable dlt (simplify cns ds) ->
      exists dlt',
        (forall x, In x scope -> dlt x = dlt' x)
        /\ listSatisfiable dlt' cns.
  Proof.
    intros cns ds scope dlt Hwf Hdisj Hsat.
    eapply simplifyRel_complete with (cns' := simplify cns ds); eauto.
    eapply simplify_simplifyRel. reflexivity.
  Qed.

  Lemma hm_ext_merge_eq:
    forall dlt st1 st2,
      hm_ext dlt (st1 ⊔ st2) = join (hm_ext dlt st1) (hm_ext dlt st2).
  Proof.
    intros dlt st1 st2.
    apply eq_no_red.
    apply order_antisym.
    - apply hm_ext_distributive2.
    - apply join_least_upper_bound.
      + apply hm_ext_concat_l.
      + apply hm_ext_concat_r.
  Qed.

  (** Generic scope metatheory for constraints and symbolic types.

      These lemmas belong next to [findST], [subST], [subAll], and [simplify]:
      they are independent of any particular source or target language and are
      later reused both by the signature-instantiation layer and by the
      NLustre/STC translation proof. *)

  Definition constraint_scope (c: constraint) : list ident :=
    fst c ++ snd c.

  Definition constraint_scoped (scope: list ident) (c: constraint) : Prop :=
    forall x, In x (constraint_scope c) -> In x scope.

  Definition constraints_scoped (scope: list ident) (cns: list constraint) : Prop :=
    Forall (constraint_scoped scope) cns.

  Definition st_scoped (scope: list ident) (st: ST) : Prop :=
    forall x, In x st -> In x scope.

  (* Agreement of two valuations on a chosen scope.  This is the generic
     semantic relation underlying the later translation-preservation theorems,
     so it belongs with the symbolic-type metatheory rather than any specific
     source/target phase bridge. *)
  Definition agree_on (xs: list ident) (dlt1 dlt2: ident -> Lat.t) : Prop :=
    forall x, In x xs -> dlt1 x = dlt2 x.

  Lemma agree_on_trans:
    forall xs dlt1 dlt2 dlt3,
      agree_on xs dlt1 dlt2 ->
      agree_on xs dlt2 dlt3 ->
      agree_on xs dlt1 dlt3.
  Proof.
    intros xs dlt1 dlt2 dlt3 H12 H23 x Hin.
    rewrite H12 by exact Hin.
    exact (H23 x Hin).
  Qed.

  Lemma agree_on_refl:
    forall xs dlt,
      agree_on xs dlt dlt.
  Proof.
    intros xs dlt x Hin.
    reflexivity.
  Qed.

  (* Weak preservation of one constraint list by another under a chosen shared
     scope.  This is generic symbolic-type metatheory: the only semantic
     ingredients are valuation agreement and constraint satisfiability. *)
  Definition preserves_on (xs: list ident) (cns1 cns2: list constraint) : Prop :=
    forall dlt,
      listSatisfiable dlt cns1 ->
      exists dlt',
        agree_on xs dlt dlt' /\ listSatisfiable dlt' cns2.

  Lemma constraintSatisfiable_ext:
    forall c scope dlt1 dlt2,
      constraint_scoped scope c ->
      agree_on scope dlt1 dlt2 ->
      constraintSatisfiable dlt1 c ->
      constraintSatisfiable dlt2 c.
  Proof.
    intros [lhs rhs] scope dlt1 dlt2 Hsc Hagree Hsat.
    unfold constraintSatisfiable, satisfiable in *.
    assert (Hlhs: hm_ext dlt1 lhs = hm_ext dlt2 lhs).
    {
      clear Hsat.
      induction lhs as [|x xs IH]; simpl; auto.
      rewrite (Hagree x).
      2:{ eapply constraint_scoped_lhs; eauto. now left. }
      rewrite IH; auto.
      intros y Hy.
      eapply Hsc.
      unfold constraint_scope in *. simpl in *. right. exact Hy.
    }
    assert (Hrhs: hm_ext dlt1 rhs = hm_ext dlt2 rhs).
    {
      clear Hsat Hlhs.
      induction rhs as [|x xs IH]; simpl; auto.
      rewrite (Hagree x).
      2:{ eapply constraint_scoped_rhs; eauto. now left. }
      rewrite IH; auto.
      intros y Hy.
      eapply Hsc.
      unfold constraint_scope in *. simpl in *.
      apply in_app_iff in Hy.
      apply in_app_iff.
      destruct Hy as [Hy|Hy].
      + left. exact Hy.
      + right. right. exact Hy.
    }
    rewrite <- Hlhs.
    rewrite <- Hrhs.
    exact Hsat.
  Qed.

  Lemma listSatisfiable_ext:
    forall cns scope dlt1 dlt2,
      constraints_scoped scope cns ->
      agree_on scope dlt1 dlt2 ->
      listSatisfiable dlt1 cns ->
      listSatisfiable dlt2 cns.
  Proof.
    intros cns scope dlt1 dlt2 Hsc Hagree Hsat.
    induction Hsc as [|c cns Hc Hcs IH] in Hsat |- *.
    - constructor.
    - inversion Hsat; subst.
      constructor.
      + eapply constraintSatisfiable_ext; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma constraint_scoped_incl:
    forall scope1 scope2 c,
      incl scope1 scope2 ->
      constraint_scoped scope1 c ->
      constraint_scoped scope2 c.
  Proof.
    intros scope1 scope2 c Hincl Hsc x Hin.
    apply Hincl, Hsc, Hin.
  Qed.

  Lemma constraints_scoped_incl:
    forall scope1 scope2 cns,
      incl scope1 scope2 ->
      constraints_scoped scope1 cns ->
      constraints_scoped scope2 cns.
  Proof.
    intros scope1 scope2 cns Hincl Hsc.
    induction Hsc as [|c cns Hc Hcs IH]; constructor.
    - eapply constraint_scoped_incl; eauto.
    - exact IH.
  Qed.

  Definition agree_on_notin
    (scope extras: list ident)
    (dlt base: ident -> Lat.t) : ident -> Lat.t :=
    fun x =>
      if in_dec ident_eq_dec x extras then dlt x
      else base x.

  Lemma agree_on_notin_scope:
    forall scope extras dlt base,
      (forall x, In x extras -> ~ In x scope) ->
      agree_on scope base (agree_on_notin scope extras dlt base).
  Proof.
    intros scope extras dlt base Hfresh x Hin.
    unfold agree_on_notin.
    destruct (in_dec ident_eq_dec x extras) as [Hinextra|Hnin]; auto.
    exfalso.
    eapply (Hfresh x); eauto.
  Qed.

  Lemma agree_on_notin_extras:
    forall scope extras dlt base,
      NoDup extras ->
      (forall x, In x extras -> ~ In x scope) ->
      agree_on (scope ++ extras) dlt base ->
      agree_on (scope ++ extras) dlt (agree_on_notin scope extras dlt base).
  Proof.
    intros scope extras dlt base Hnd Hfresh Hagree x Hin.
    unfold agree_on_notin.
    destruct (in_dec ident_eq_dec x extras) as [Hinextra|Hnin].
    - reflexivity.
    - apply Hagree.
      apply in_app_iff in Hin.
      apply in_app_iff.
      destruct Hin as [Hin|Hin].
      + now left.
      + right.
        exfalso. apply Hnin. exact Hin.
  Qed.

  Lemma preserves_on_concat_scoped:
    forall scope extras1 extras2 c1 c2 t1 t2,
      NoDup (extras1 ++ extras2) ->
      (forall x, In x (extras1 ++ extras2) -> ~ In x scope) ->
      constraints_scoped (scope ++ extras1) t1 ->
      constraints_scoped (scope ++ extras2) t2 ->
      preserves_on scope c1 t1 ->
      preserves_on scope c2 t2 ->
      preserves_on scope (c1 ++ c2) (t1 ++ t2).
  Proof.
    intros scope extras1 extras2 c1 c2 t1 t2 Hnd Hfresh Hsc1 Hsc2 Hpres1 Hpres2 dlt Hsat.
    unfold listSatisfiable in Hsat.
    rewrite Forall_app in Hsat.
    destruct Hsat as [Hsat1 Hsat2].
    destruct (Hpres1 dlt Hsat1) as (dlt1 & Hagree1 & Ht1).
    destruct (Hpres2 dlt Hsat2) as (dlt2 & Hagree2 & Ht2).
    set (dlt' := agree_on_notin scope extras1 dlt1
                   (agree_on_notin scope extras2 dlt2 dlt)).
    exists dlt'. split.
    - intros x Hin.
      unfold dlt', agree_on_notin.
      destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
      + exfalso.
        eapply (Hfresh x).
        * now apply in_or_app; left.
        * exact Hin.
      + destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
        * exfalso.
          eapply (Hfresh x).
          -- now apply in_or_app; right.
          -- exact Hin.
        * reflexivity.
    - unfold listSatisfiable. rewrite Forall_app. split.
      + eapply listSatisfiable_ext.
        * exact Hsc1.
        * unfold dlt'. intros x Hin.
          unfold agree_on_notin.
          destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
          -- reflexivity.
          -- destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
             ++ exfalso.
                apply in_app_iff in Hin.
                destruct Hin as [Hinscope|Hin1'].
                ** assert (Hin12: In x (extras1 ++ extras2)).
                   { apply in_app_iff. right. exact Hin2. }
                   pose proof (Hfresh x Hin12) as Hninscope.
                   contradiction.
                ** apply Hnin1. exact Hin1'.
             ++ symmetry. apply Hagree1.
                apply in_app_iff in Hin.
                destruct Hin as [Hinscope|Hin1'].
                ** exact Hinscope.
                ** contradiction.
        * exact Ht1.
      + eapply listSatisfiable_ext.
        * exact Hsc2.
        * unfold dlt'. intros x Hin.
          unfold agree_on_notin.
          destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
          -- exfalso.
             apply in_app_iff in Hin.
             destruct Hin as [Hinscope|Hin2].
             ++ assert (Hin12: In x (extras1 ++ extras2)).
                { apply in_app_iff. left. exact Hin1. }
                pose proof (Hfresh x Hin12) as Hninscope.
                contradiction.
             ++ assert (~ In x extras2).
                { intro Hcontra.
                  eapply (NoDup_app_In x) in Hnd; eauto. }
                contradiction.
          -- destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
             ++ reflexivity.
             ++ symmetry. apply Hagree2.
                apply in_app_iff in Hin.
                destruct Hin as [Hinscope|Hin2'].
                ** exact Hinscope.
                ** contradiction.
        * exact Ht2.
  Qed.

  Lemma preserves_on_nil:
    forall scope,
      preserves_on scope nil nil.
  Proof.
    intros scope dlt Hsat.
    exists dlt. split.
    - apply agree_on_refl.
    - exact Hsat.
  Qed.

  Lemma preserves_on_weaken:
    forall scope1 scope2 c1 c2,
      incl scope1 scope2 ->
      preserves_on scope2 c1 c2 ->
      preserves_on scope1 c1 c2.
  Proof.
    intros scope1 scope2 c1 c2 Hincl Hpres dlt Hsat.
    destruct (Hpres dlt Hsat) as (dlt' & Hagree & Htgt).
    exists dlt'. split; [|exact Htgt].
    intros x Hin.
    apply Hagree, Hincl, Hin.
  Qed.

  (* Pointwise valuation updates used by the call-instantiation metatheory.
     They are generic symbolic-type operations, so the reusable definitions and
     their basic agreement lemmas live here. *)
  Definition upd_type (dlt: ident -> Lat.t) (x: ident) (st: ST) : ident -> Lat.t :=
    fun y => if ident_eqb y x then hm_ext dlt st else dlt y.

  Definition upd_ident (dlt: ident -> Lat.t) (x v: ident) : ident -> Lat.t :=
    fun y => if ident_eqb y x then dlt v else dlt y.

  Fixpoint upd_types (dlt: ident -> Lat.t) (xs: list ident) (vs: list ST)
    : ident -> Lat.t :=
    match xs, vs with
    | x :: xs', v :: vs' => upd_types (upd_type dlt x v) xs' vs'
    | _, _ => dlt
    end.

  Fixpoint upd_types_rev (dlt: ident -> Lat.t) (xs: list ident) (vs: list ST)
    : ident -> Lat.t :=
    match xs, vs with
    | x :: xs', v :: vs' => upd_type (upd_types_rev dlt xs' vs') x v
    | _, _ => dlt
    end.

  Fixpoint upd_idents (dlt: ident -> Lat.t) (xs vs: list ident)
    : ident -> Lat.t :=
    match xs, vs with
    | x :: xs', v :: vs' => upd_idents (upd_ident dlt x v) xs' vs'
    | _, _ => dlt
    end.

  Fixpoint upd_idents_rev (dlt: ident -> Lat.t) (xs vs: list ident)
    : ident -> Lat.t :=
    match xs, vs with
    | x :: xs', v :: vs' => upd_ident (upd_idents_rev dlt xs' vs') x v
    | _, _ => dlt
    end.

  Definition overlay_scope
    (scope: list ident) (dlt_scope dlt_base: ident -> Lat.t)
    : ident -> Lat.t :=
    fun x => if in_dec ident_eq_dec x scope then dlt_scope x else dlt_base x.

  Lemma upd_type_outside:
    forall dlt x st y,
      x <> y ->
      upd_type dlt x st y = dlt y.
  Proof.
    intros dlt x st y Hneq.
    unfold upd_type.
    destruct (ident_eqb y x) eqn:Heq.
    - apply ident_eqb_eq in Heq. congruence.
    - reflexivity.
  Qed.

  Lemma upd_ident_outside:
    forall dlt x v y,
      x <> y ->
      upd_ident dlt x v y = dlt y.
  Proof.
    intros dlt x v y Hneq.
    unfold upd_ident.
    destruct (ident_eqb y x) eqn:Heq.
    - apply ident_eqb_eq in Heq. congruence.
    - reflexivity.
  Qed.

  Lemma Forall2_upd_ident_outside_base:
    forall (d0 dlt: ident -> Lat.t) x v xs vs,
      ~ In x xs ->
      Forall2 (fun y vy => d0 y = dlt vy) xs vs ->
      Forall2 (fun y vy => upd_ident d0 x v y = dlt vy) xs vs.
  Proof.
    intros d0 dlt x v xs vs Hnin Hrel.
    induction Hrel.
    - constructor.
    - constructor.
      + unfold upd_ident.
        destruct (ident_eqb x0 x) eqn:Heq.
        * apply ident_eqb_eq in Heq. subst x0.
          exfalso. apply Hnin. now left.
        * exact H.
      + apply IHHrel.
        intro Hin. apply Hnin. now right.
  Qed.

  Lemma Forall2_upd_type_outside_base:
    forall (d0 dlt: ident -> Lat.t) x ty xs tys,
      ~ In x xs ->
      Forall2 (fun y ty' => d0 y = hm_ext dlt ty') xs tys ->
      Forall2 (fun y ty' => upd_type d0 x ty y = hm_ext dlt ty') xs tys.
  Proof.
    intros d0 dlt x ty xs tys Hnin Hrel.
    induction Hrel.
    - constructor.
    - constructor.
      + unfold upd_type.
        destruct (ident_eqb x0 x) eqn:Heq.
        * apply ident_eqb_eq in Heq. subst x0.
          exfalso. apply Hnin. now left.
        * exact H.
      + apply IHHrel.
        intro Hin. apply Hnin. now right.
  Qed.

  Lemma upd_ident_eq_upd_type_singleton:
    forall dlt x v y,
      x <> v ->
      upd_ident dlt x v y = upd_type dlt x ([v]) y.
  Proof.
    intros dlt x v y Hneq.
    unfold upd_ident, upd_type.
    destruct (ident_eqb y x) eqn:Hyx.
    - simpl. rewrite <- join_bottom_eq1. reflexivity.
    - reflexivity.
  Qed.

  Lemma In_nth_error_ex:
    forall (A: Type) (x: A) xs,
      In x xs ->
      exists n, nth_error xs n = Some x.
  Proof.
    intros A x xs Hin.
    induction xs as [|y ys IH]; simpl in Hin.
    - contradiction.
    - destruct Hin as [Heq|Hin].
      + subst y. exists 0%nat. reflexivity.
      + destruct (IH Hin) as [n Hnth].
        exists (S n). exact Hnth.
  Qed.

  Lemma nth_error_In_local:
    forall (A: Type) xs n (x: A),
      nth_error xs n = Some x ->
      In x xs.
  Proof.
    intros A xs.
    induction xs as [|y ys IH]; intros n x Hnth; simpl in Hnth.
    - destruct n; inversion Hnth.
    - destruct n as [|n].
      + inversion Hnth; subst. now left.
      + right. eapply IH. exact Hnth.
  Qed.

  Lemma Forall2_nth_error_inv:
    forall (A B: Type) (P: A -> B -> Prop) xs ys n x,
      Forall2 P xs ys ->
      nth_error xs n = Some x ->
      exists y, nth_error ys n = Some y /\ P x y.
  Proof.
    intros A B P xs ys n x Hrel.
    revert n x.
    induction Hrel as [|x0 y0 xs ys Hxy Hrel IH]; intros n x Hnth.
    - destruct n; simpl in Hnth; discriminate.
    - destruct n; simpl in Hnth.
      + inversion Hnth; subst. exists y0. split; [reflexivity|exact Hxy].
      + eapply IH in Hnth as (y & Hnthy & HP).
        exists y. split; [exact Hnthy|exact HP].
  Qed.

  Lemma upd_types_agree_on:
    forall dlt scope xs vs,
      Forall (fun x => ~ In x scope) xs ->
      agree_on scope dlt (upd_types dlt xs vs).
  Proof.
    intros dlt scope xs.
    revert dlt.
    induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
    - destruct vs; reflexivity.
    - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
      destruct vs as [|v vs].
      + reflexivity.
      + specialize (IH (upd_type dlt x v) vs Hxs y Hy).
        unfold upd_types in IH |- *; simpl in IH |- *.
        destruct (ident_eqb y x) eqn:Heq.
        * apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hx Hy).
        * transitivity ((upd_type dlt x v) y).
          -- symmetry. apply upd_type_outside. intros Heqxy. subst y. exact (Hx Hy).
          -- exact IH.
  Qed.

  Lemma upd_types_rev_agree_on:
    forall dlt scope xs vs,
      Forall (fun x => ~ In x scope) xs ->
      agree_on scope dlt (upd_types_rev dlt xs vs).
  Proof.
    intros dlt scope xs.
    revert dlt.
    induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
    - destruct vs; reflexivity.
    - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
      destruct vs as [|v vs].
      + reflexivity.
      + unfold upd_types_rev; simpl.
        rewrite upd_type_outside.
        * apply IH; auto.
        * intros Heqxy. subst y. exact (Hx Hy).
  Qed.

  Lemma upd_idents_agree_on:
    forall dlt scope xs vs,
      Forall (fun x => ~ In x scope) xs ->
      agree_on scope dlt (upd_idents dlt xs vs).
  Proof.
    intros dlt scope xs.
    revert dlt.
    induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
    - destruct vs; reflexivity.
    - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
      destruct vs as [|v vs].
      + reflexivity.
      + specialize (IH (upd_ident dlt x v) vs Hxs y Hy).
        unfold upd_idents in IH |- *; simpl in IH |- *.
        destruct (ident_eqb y x) eqn:Heq.
        * apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hx Hy).
        * transitivity ((upd_ident dlt x v) y).
          -- symmetry. apply upd_ident_outside. intros Heqxy. subst y. exact (Hx Hy).
          -- exact IH.
  Qed.

  Lemma upd_idents_rev_agree_on:
    forall dlt scope xs vs,
      Forall (fun x => ~ In x scope) xs ->
      agree_on scope dlt (upd_idents_rev dlt xs vs).
  Proof.
    intros dlt scope xs.
    revert dlt.
    induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
    - destruct vs; reflexivity.
    - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
      destruct vs as [|v vs].
      + reflexivity.
      + unfold upd_idents_rev; simpl.
        rewrite upd_ident_outside.
        * apply IH; auto.
        * intros Heqxy. subst y. exact (Hx Hy).
  Qed.

  Lemma upd_type_agree_on:
    forall dlt scope x st,
      ~ In x scope ->
      agree_on scope dlt (upd_type dlt x st).
  Proof.
    intros dlt scope x st Hfresh y Hin.
    unfold upd_type.
    destruct (ident_eqb y x) eqn:Heq.
    - apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hfresh Hin).
    - reflexivity.
  Qed.

  Lemma upd_ident_agree_on:
    forall dlt scope x v,
      ~ In x scope ->
      agree_on scope dlt (upd_ident dlt x v).
  Proof.
    intros dlt scope x v Hfresh y Hin.
    unfold upd_ident.
    destruct (ident_eqb y x) eqn:Heq.
    - apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hfresh Hin).
    - reflexivity.
  Qed.

  Lemma upd_types_rev_outside:
    forall dlt xs vs y,
      ~ In y xs ->
      upd_types_rev dlt xs vs y = dlt y.
  Proof.
    induction xs as [|x xs IH]; intros vs y Hnin.
    - destruct vs; reflexivity.
    - destruct vs as [|v vs]; simpl.
      + reflexivity.
      + rewrite upd_type_outside.
        * eapply IH. intros Hin. apply Hnin. now right.
        * intro Heq. subst y. apply Hnin. now left.
  Qed.

  Lemma upd_idents_rev_outside:
    forall dlt xs vs y,
      ~ In y xs ->
      upd_idents_rev dlt xs vs y = dlt y.
  Proof.
    induction xs as [|x xs IH]; intros vs y Hnin.
    - destruct vs; reflexivity.
    - destruct vs as [|v vs]; simpl.
      + reflexivity.
      + rewrite upd_ident_outside.
        * eapply IH. intros Hin. apply Hnin. now right.
        * intro Heq. subst y. apply Hnin. now left.
  Qed.

  Lemma hm_ext_agree_on_st:
    forall dlt1 dlt2 st,
      agree_on st dlt1 dlt2 ->
      hm_ext dlt1 st = hm_ext dlt2 st.
  Proof.
    intros dlt1 dlt2 st Hagree.
    induction st as [|x st IH]; simpl; auto.
    rewrite (Hagree x).
    2:{ now left. }
    rewrite IH; auto.
    intros y Hy. apply Hagree. now right.
  Qed.

  Lemma overlay_scope_agree_on:
    forall scope dlt_scope dlt_base,
      agree_on scope dlt_scope (overlay_scope scope dlt_scope dlt_base).
  Proof.
    intros scope dlt_scope dlt_base x Hin.
    unfold overlay_scope.
    destruct (in_dec ident_eq_dec x scope) as [Hin'|Hnin].
    - reflexivity.
    - contradiction.
  Qed.

  Lemma overlay_scope_agree_outside:
    forall scope dlt_scope dlt_base x,
      ~ In x scope ->
      overlay_scope scope dlt_scope dlt_base x = dlt_base x.
  Proof.
    intros scope dlt_scope dlt_base x Hfresh.
    unfold overlay_scope.
    destruct (in_dec ident_eq_dec x scope) as [Hin|Hnin].
    - contradiction.
    - reflexivity.
  Qed.

  Lemma hm_ext_agree_on_scoped_type:
    forall scope ty dlt1 dlt2,
      st_scoped scope ty ->
      agree_on scope dlt1 dlt2 ->
      hm_ext dlt1 ty = hm_ext dlt2 ty.
  Proof.
    intros scope ty dlt1 dlt2 Hsc Hagree.
    apply hm_ext_agree_on_st.
    intros x Hin.
    apply Hagree.
    exact (Hsc _ Hin).
  Qed.

  Lemma st_scoped_weaken:
    forall scope1 scope2 st,
      incl scope1 scope2 ->
      st_scoped scope1 st ->
      st_scoped scope2 st.
  Proof.
    intros scope1 scope2 st Hincl Hsc x Hin.
    apply Hincl, Hsc, Hin.
  Qed.

  Lemma scope_remove_choice:
    forall pre post (x y : ident),
      In y (pre ++ x :: post) ->
      y = x \/ In y (pre ++ post).
  Proof.
    intros pre post x y Hin.
    rewrite in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - right. now apply in_or_app; left.
    - simpl in Hin. destruct Hin as [Heq|Hin].
      + now left.
      + right. now apply in_or_app; right.
  Qed.

  Lemma in_merge_inv:
    forall x a b,
      In x (a ⊔ b) ->
      In x a \/ In x b.
  Proof.
    intros x a.
    induction a as [|a0 a IHa]; intros b Hin.
    - rewrite merge_nil2 in Hin. now right.
    - revert a0 a IHa Hin.
      induction b as [|b0 b IHb]; intros a0 a IHa Hin.
      + rewrite merge_nil in Hin. now left.
      + simpl in Hin.
        destruct (Pos.compare a0 b0) eqn:Hcmp.
        * simpl in Hin. destruct Hin as [Hin|Hin].
          { subst x. now left; left. }
          apply IHa in Hin. destruct Hin as [Hin|Hin].
          { now left; right. }
          { now right; right. }
        * simpl in Hin. destruct Hin as [Hin|Hin].
          { subst x. now left; left. }
          specialize (IHa (b0 :: b) Hin). destruct IHa as [Hin'|Hin'].
          { now left; right. }
          { now right. }
        * simpl in Hin. destruct Hin as [Hin|Hin].
          { subst x. now right; left. }
          specialize (IHb a0 a IHa Hin). destruct IHb as [Hin'|Hin'].
          { now left. }
          { now right; right. }
  Qed.

  Lemma st_remove_in_inv:
    forall x y st,
      In y (st_remove x st) ->
      In y st /\ y <> x.
  Proof.
    intros x y st.
    induction st as [|a st IH]; simpl; intros Hin.
    - contradiction.
    - destruct (ident_eq_dec x a) as [Heq|Hneq].
      + subst a.
        specialize (IH Hin) as [Hin' Hneq'].
        split; [now right|exact Hneq'].
      + simpl in Hin.
        destruct Hin as [Heq|Hin].
        * subst y. split.
          -- now left.
          -- intro Heq'. apply Hneq. symmetry. exact Heq'.
        * specialize (IH Hin) as [Hin' Hneq'].
          split; [now right|exact Hneq'].
  Qed.

  Lemma st_scoped_remove_app:
    forall pre post x st,
      st_scoped (pre ++ x :: post) st ->
      st_scoped (pre ++ post) (st_remove x st).
  Proof.
    intros pre post x st Hsc y Hin.
    destruct (st_remove_in_inv _ _ _ Hin) as [Hin' Hneq].
    specialize (Hsc y Hin').
    destruct (scope_remove_choice pre post x y Hsc) as [Heq|Hin''].
    - contradiction.
    - exact Hin''.
  Qed.

  Lemma st_scoped_drop_absent_app:
    forall pre post x st,
      ~ In x st ->
      st_scoped (pre ++ x :: post) st ->
      st_scoped (pre ++ post) st.
  Proof.
    intros pre post x st Hnin Hsc y Hin.
    destruct (scope_remove_choice pre post x y (Hsc _ Hin)) as [Heq|Hin'].
    - subst y. contradiction.
    - exact Hin'.
  Qed.

  Lemma st_scoped_merge:
    forall scope st1 st2,
      st_scoped scope st1 ->
      st_scoped scope st2 ->
      st_scoped scope (st1 ⊔ st2).
  Proof.
    intros scope st1 st2 H1 H2 x Hin.
    destruct (in_merge_inv _ _ _ Hin) as [Hin'|Hin']; auto.
  Qed.

  Lemma constraint_scoped_lhs:
    forall scope lhs rhs x,
      constraint_scoped scope (lhs, rhs) ->
      In x lhs ->
      In x scope.
  Proof.
    intros scope lhs rhs x Hsc Hin.
    apply Hsc. unfold constraint_scope. now apply in_or_app; left.
  Qed.

  Lemma constraint_scoped_rhs:
    forall scope lhs rhs x,
      constraint_scoped scope (lhs, rhs) ->
      In x rhs ->
      In x scope.
  Proof.
    intros scope lhs rhs x Hsc Hin.
    apply Hsc. unfold constraint_scope. now apply in_or_app; right.
  Qed.

  Lemma st_scoped_singleton:
    forall scope x,
      In x scope ->
      st_scoped scope [x].
  Proof.
    intros scope x Hin y Hy.
    simpl in Hy. destruct Hy as [Heq|[]]. subst. exact Hin.
  Qed.

  Lemma findST_of_rhs_in:
    forall cns d,
      In [d] (map snd cns) ->
      exists st, findST cns d = Some st.
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct rhs as [|r rhs'].
      + destruct Hin as [Heq|Hin].
        * discriminate Heq.
        * apply IH. exact Hin.
      + destruct rhs' as [|r' rhs''].
        * simpl in Hin. destruct Hin as [Heq|Hin].
          -- inversion Heq. subst r.
             exists lhs.
             simpl.
             rewrite ident_eqb_refl.
             reflexivity.
          -- destruct (ident_eqb r d) eqn:Hrd.
             ++ apply ident_eqb_eq in Hrd. subst r.
                exists lhs.
                simpl.
                rewrite ident_eqb_refl.
                reflexivity.
             ++ apply IH in Hin as (st & Hfind).
                exists st.
                simpl.
                rewrite Hrd.
                exact Hfind.
        * destruct Hin as [Heq|Hin].
          -- discriminate Heq.
          -- apply IH. exact Hin.
  Qed.

  Lemma subST_scoped_elim:
    forall scope ds d lhs st,
      st_scoped (scope ++ d :: ds) lhs ->
      st_scoped (scope ++ d :: ds) st ->
      st_scoped (scope ++ ds) (subST lhs d st).
  Proof.
    intros scope ds d lhs st Hlhs Hst.
    unfold subST.
    destruct (st_mem d lhs) eqn:Hmem.
    - destruct (st_mem d st) eqn:Hmem'.
      + eapply st_scoped_merge.
        * eapply st_scoped_remove_app; eauto.
        * eapply st_scoped_remove_app; eauto.
      + eapply st_scoped_merge.
        * eapply st_scoped_remove_app; eauto.
        * eapply st_scoped_drop_absent_app with (x := d); eauto.
          intro Hin. apply my_set_mem_correct in Hin. unfold st_mem in Hmem'. rewrite Hin in Hmem'. discriminate.
    - eapply st_scoped_drop_absent_app with (x := d); eauto.
      intro Hin. apply my_set_mem_correct in Hin. unfold st_mem in Hmem. rewrite Hin in Hmem. discriminate.
  Qed.

  Lemma subAll_scoped_elim:
    forall scope ds cns d st,
      constraints_scoped (scope ++ d :: ds) cns ->
      st_scoped (scope ++ d :: ds) st ->
      constraints_scoped (scope ++ ds) (subAll cns d st).
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d st Hsc Hst; simpl.
    - constructor.
    - inversion Hsc as [|c0 cs0 Hc Hcs]; subst c0 cs0.
      destruct rhs as [|r rhs'].
      + exact (IH d st Hcs Hst).
      + destruct rhs' as [|r' rhs''].
        * destruct (ident_eqb r d) eqn:Hrd.
          -- exact (IH d st Hcs Hst).
          -- apply Forall_cons.
             ++ unfold constraint_scoped.
                intros y Hin.
                unfold constraint_scope in Hin.
                apply in_app_iff in Hin.
                destruct Hin as [Hin|Hin].
                ** assert (Hlhs : st_scoped (scope ++ d :: ds) lhs).
                   { intros z Hz.
                     eapply constraint_scoped_lhs with (rhs := [r]); eauto. }
                   pose proof (subST_scoped_elim scope ds d lhs st Hlhs Hst) as Hsub.
                   exact (Hsub y Hin).
                ** simpl in Hin.
                   destruct Hin as [Heq|HinFalse].
                   { subst y.
                     assert (HrScope : In r (scope ++ d :: ds)).
                     { eapply constraint_scoped_rhs with (lhs := lhs) (rhs := [r]); eauto.
                       simpl; left; reflexivity. }
                     destruct (scope_remove_choice scope ds d r HrScope) as [Heqd|Hin'].
                     - apply ident_eqb_neq in Hrd. contradiction.
                     - exact Hin'. }
                   { contradiction. }
             ++ exact (IH d st Hcs Hst).
        * exact (IH d st Hcs Hst).
  Qed.

  Lemma subAll_preserves_other_rhs:
    forall cns d st d',
      d' <> d ->
      In [d'] (map snd cns) ->
      In [d'] (map snd (subAll cns d st)).
  Proof.
    induction cns as [|[lhs rhs] cns IH]; intros d st d' Hneq Hin; simpl in *.
    - contradiction.
    - destruct rhs as [|r rhs'].
      + destruct Hin as [Heq|Hin].
        * discriminate Heq.
        * apply IH; auto.
      + destruct rhs' as [|r' rhs''].
        * simpl in Hin.
          destruct Hin as [Heq|Hin].
          -- inversion Heq; subst r.
             destruct (ident_eqb d' d) eqn:Hd.
             ++ apply ident_eqb_eq in Hd. contradiction.
             ++ simpl. left. reflexivity.
          -- destruct (ident_eqb r d) eqn:Hrd.
             ++ apply IH; auto.
             ++ simpl. right. apply IH; auto.
        * destruct Hin as [Heq|Hin].
          -- discriminate Heq.
          -- apply IH; auto.
  Qed.

  Theorem simplify_scoped:
    forall scope ds cns,
      NoDup ds ->
      constraints_scoped (scope ++ ds) cns ->
      (forall d, In d ds -> In [d] (map snd cns)) ->
      constraints_scoped scope (simplify cns ds).
  Proof.
    intros scope ds.
    induction ds as [|d ds IH]; intros cns Hnd Hsc Hdefs.
    - simpl in *. rewrite app_nil_r in Hsc. exact Hsc.
    - simpl.
      assert (Hrhs : In [d] (map snd cns)) by (apply Hdefs; left; reflexivity).
      destruct (findST_of_rhs_in _ _ Hrhs) as [st Hfind].
      rewrite Hfind.
      apply IH.
      + now apply NoDup_cons_iff in Hnd.
      + assert (Hst_scoped : st_scoped (scope ++ d :: ds) st).
        { intros x Hin.
          pose proof Hsc as Hsc_forall.
          unfold constraints_scoped in Hsc_forall.
          rewrite Forall_forall in Hsc_forall.
          eapply constraint_scoped_lhs with (rhs := [d]).
          - apply Hsc_forall. apply find_correct. exact Hfind.
          - exact Hin. }
        eapply subAll_scoped_elim; eauto.
      + intros d' Hin.
        eapply subAll_preserves_other_rhs.
        * intro Heq. subst d'.
          apply NoDup_cons_iff in Hnd as [Hnin _]. contradiction.
        * apply Hdefs. now right.
  Qed.


End SECTYPES.

Module SecTypes (Lat: Lattice) <: SECTYPES Lat.

  Include SECTYPES Lat.

End SecTypes.
