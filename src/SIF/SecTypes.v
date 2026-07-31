(** Symbolic types, constraints, simplification, and preservation metatheory. *)

From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lists.ListSet.

From Velus Require Import Common.
From Coq Require Import Lia.
From Velus Require Export SIF.SymTypes.
From Velus Require Export SIF.SecLattice.
Require Import Coq.Program.Equality.
Import List.ListNotations.

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

            + apply Pos.compare_eq_iff in Eab. subst. apply Pos.lt_irrefl in Eba. elim Eba.
            + apply Pos.compare_eq_iff in Eab. subst. rewrite Pos.compare_gt_iff in Eba. apply Pos.lt_irrefl in Eba. elim Eba.
            + apply Pos.compare_eq_iff in Eba. subst. apply Pos.lt_irrefl in Eab. elim Eab.
            + rewrite Pos.compare_lt_iff in Eab. rewrite Pos.compare_lt_iff in Eba. elim (lt_gt_false a_0 b_0 Eab Eba).

            + rewrite IHx. auto.

            + apply Pos.compare_eq_iff in Eba. subst. rewrite Pos.compare_gt_iff in Eab. apply Pos.lt_irrefl in Eab. elim Eab.

            + rewrite <- IHy. auto.

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
              destruct H as [H1|H2]. elim (E H1).
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

  Definition st_remove := SymTypes.st_remove.
  Definition st_mem    := SymTypes.st_mem.

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

  Definition satisfiable (dlt: ident -> Lat.t) (s_0 s_1: ST) :=
    (hm_ext dlt s_0) ⊑ (hm_ext dlt s_1).

  Definition constraintSatisfiable (dlt: ident-> Lat.t) (c: constraint) := let (lhs, rhs) := c in
    satisfiable dlt lhs rhs.

  Definition listSatisfiable (dlt: ident -> Lat.t) (cns: list constraint) := Forall (fun c => constraintSatisfiable dlt c) cns.

  Hint Unfold satisfiable constraintSatisfiable listSatisfiable.

  Definition findST := SymTypes.findST.

  Lemma find_correct : forall cs d v,
    findST cs d = Some v -> List.In (v,[d]) cs.
  Proof.
    exact SymTypes.find_correct.
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

  Definition wf_constraints := SymTypes.wf_constraints.

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
    exact SymTypes.st_remove_notin.
  Qed.

  Lemma st_remove_preserves_other_in:
    forall x d st,
      x <> d ->
      In x st ->
      In x (st_remove d st).
  Proof.
    exact SymTypes.st_remove_preserves_other_in.
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

  Lemma hm_ext_incl:
    forall dlt a b,
      (forall z, In z a -> In z b) ->
      hm_ext dlt a ⊑ hm_ext dlt b.
  Proof.
    intros dlt a b Hincl.
    apply hm_ext_bound_from_members.
    intros x Hx.
    apply hm_ext_list_in1, Hincl, Hx.
  Qed.

  Lemma constraint_satisfiable_merge_split:
    forall dlt a b r,
      constraintSatisfiable dlt ((a ⊔ b), r) <->
      (constraintSatisfiable dlt (a, r) /\ constraintSatisfiable dlt (b, r)).
  Proof.
    intros dlt a b r.
    unfold constraintSatisfiable, satisfiable.
    split.
    - intros Hm.
      split.
      + eapply order_trans; [apply hm_ext_concat_l|exact Hm].
      + eapply order_trans; [apply hm_ext_concat_r|exact Hm].
    - intros [Ha Hb].
      eapply order_trans; [apply hm_ext_distributive2|].
      apply join_least_upper_bound; assumption.
  Qed.

  Lemma join_into_satisfaction:
    forall dlt l r acc,
      listSatisfiable dlt (join_into l r acc) <->
      (constraintSatisfiable dlt (l, r) /\ listSatisfiable dlt acc).
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
      listSatisfiable dlt (collapse cns) <-> listSatisfiable dlt cns.
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


  (** Source-inclusion ordering on constraint lists: same targets,
      smaller sources.  A constraint list below another in this ordering
      is weaker, so satisfaction descends. *)

  Definition constraints_src_le (cs1 cs2: list constraint) : Prop :=
    Forall2 (fun c1 c2 =>
               snd c1 = snd c2 /\ (forall z, In z (fst c2) -> In z (fst c1)))
            cs1 cs2.

  Lemma constraints_src_le_satisfaction:
    forall dlt cs1 cs2,
      constraints_src_le cs1 cs2 ->
      listSatisfiable dlt cs1 ->
      listSatisfiable dlt cs2.
  Proof.
    intros dlt cs1 cs2 Hle.
    induction Hle as [|[l1 r1] [l2 r2] cs1 cs2 [Hr Hl] Hle IH]; intros Hsat.
    - constructor.
    - inversion Hsat as [|? ? Hc Hcs]; subst.
      simpl in Hr, Hl. subst r2.
      constructor.
      + unfold constraintSatisfiable, satisfiable in *.
        eapply order_trans; [|exact Hc].
        apply hm_ext_incl. exact Hl.
      + apply IH. exact Hcs.
  Qed.

  Definition subST := SymTypes.subST.

  Lemma subST_complete_bound:
    forall dlt st d st',
      hm_ext (complete_subst dlt d st') st ⊑ hm_ext dlt (subST st d st').
  Proof.
    intros dlt st d st'.
    destruct (SymTypes.st_mem d st) eqn:Hmem.
    - apply hm_ext_bound_from_members.
      intros x Hin.
      destruct (ident_eqb x d) eqn:Hxd.
      + apply ident_eqb_eq in Hxd. subst x.
        rewrite complete_subst_eq.
        unfold subST, SymTypes.subST. rewrite Hmem.
        destruct (SymTypes.st_mem d st') eqn:Hmem'.
        * eapply order_trans; [apply hm_ext_concat_r | apply order_refl, eq_refl].
        * rewrite st_remove_notin by exact Hmem'.
          eapply order_trans; [apply hm_ext_concat_r | apply order_refl, eq_refl].
      + apply ident_eqb_neq in Hxd.
        rewrite complete_subst_neq by exact Hxd.
        assert (Hin' : In x (st_remove d st)).
        { eapply st_remove_preserves_other_in; eauto. }
        unfold subST, SymTypes.subST. rewrite Hmem.
        destruct (SymTypes.st_mem d st') eqn:Hmem'.
        * eapply order_trans; [eapply hm_ext_list_in1; exact Hin' | apply hm_ext_concat_l].
        * eapply order_trans; [eapply hm_ext_list_in1; exact Hin' | apply hm_ext_concat_l].
    - apply hm_ext_bound_from_members.
      intros x Hin.
      assert (x <> d).
      { intro Heq. subst x.
        apply SymTypes.my_set_mem_correct in Hin.
        unfold SymTypes.st_mem in Hmem.
        rewrite Hmem in Hin.
        discriminate. }
      rewrite complete_subst_neq by exact H.
      unfold subST, SymTypes.subST. rewrite Hmem.
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
    - unfold subST, SymTypes.subST.
      destruct (SymTypes.st_mem d st) eqn:Hmem.
      + destruct (SymTypes.st_mem d st) eqn:Hmem'; [|congruence].
        apply hm_ext_distributive.
        * apply order_refl, eq_refl.
        * apply order_refl, eq_refl.
      + rewrite st_remove_notin by exact Hmem.
        apply order_refl, eq_refl.
  Qed.

  Lemma subST_correct : forall dlt st x d st_0 st_1,
    satisfiable dlt st_0 [d] -> satisfiable dlt st x -> subST st d st_0 = st_1 -> satisfiable dlt st_1 x.
  Proof.
    intros * H_0 H_1 H_2. unfold satisfiable in *. simpl in H_0.
    rewrite <- join_bottom_eq1 in H_0. subst st_1.
    unfold subST, SymTypes.subST.
    destruct (SymTypes.st_mem d st) eqn:Edst; auto.
    destruct (SymTypes.st_mem d st_0) eqn:Edst_0.
      * apply hm_ext_distributive.
        + apply set_rm_lub2. apply SymTypes.my_set_mem_correct in Edst.
          apply hm_ext_list_in1 with (dlt:=dlt) in Edst.
          eapply order_trans. eauto. eapply order_trans; eauto.
        + auto.
      * apply hm_ext_distributive.
        + apply SymTypes.my_set_mem_correct in Edst. apply hm_ext_list_in1 with (dlt:=dlt) in Edst.
          eapply order_trans. eauto. eapply order_trans; eauto.
        + auto.
  Qed.

  Lemma satisfiable_remove_self_lhs:
    forall dlt lhs d,
      satisfiable dlt lhs [d] ->
      satisfiable dlt (st_remove d lhs) [d].
  Proof.
    intros dlt lhs d Hsat.
    unfold satisfiable in *.
    eapply set_rm_lub2.
    exact Hsat.
  Qed.

  Lemma satisfiable_restore_self_lhs:
    forall dlt lhs d,
      satisfiable dlt (st_remove d lhs) [d] ->
      satisfiable dlt lhs [d].
  Proof.
    intros dlt lhs d Hsat.
    unfold satisfiable in *.
    apply hm_ext_bound_from_members.
    intros x Hin.
    destruct (ident_eq_dec x d) as [Heq|Hneq].
    - subst x. simpl. apply join_bound1.
    - assert (Hin' : In x (st_remove d lhs)).
      { eapply st_remove_preserves_other_in; eauto. }
      eapply order_trans.
      + apply hm_ext_list_in1. exact Hin'.
      + exact Hsat.
  Qed.

  Hint Resolve subST_correct.

  Definition subAll := SymTypes.subAll.

  Lemma subAll_is_correct :  forall dlt cns d v cns',
    satisfiable dlt v [d] ->
    subAll cns d v = cns' -> listSatisfiable dlt cns -> listSatisfiable dlt cns'.
  Proof.
    intros dlt cns d v. induction cns as [|(l,r) cns IHcns];
    intros * H_0 H_1 H_2 ; simpl in H_1.
    - subst. assumption.
    - destruct r as [|d_0 r_0] eqn:Er.

      * inversion H_2. apply IHcns; auto.

      * destruct r_0 as [|r_1] eqn:El in H_1.

        + subst r_0. destruct (ident_eqb d_0 d) eqn:Edd_0.

          ** inversion H_2. apply IHcns; auto.

          ** subst cns'. unfold listSatisfiable in *. apply Forall_cons.

            ++ apply Forall_inv in H_2 as H_2'.
               eapply satisfiable_remove_self_lhs.
               eapply (subST_correct dlt l [d_0] d v (subST l d v)); eauto.

            ++ remember (subAll cns d v) as cns_0 eqn:Hcns_0. inversion  H_2; auto.

        + inversion H_2. auto.
  Qed.
  Hint Resolve subAll_is_correct.

  Lemma subAll_rhs_in:
    forall cns d st rhs,
      In rhs (map snd (subAll cns d st)) ->
      In rhs (map snd cns).
  Proof.
    exact SymTypes.subAll_rhs_in.
  Qed.

  Lemma subAll_wf:
    forall cns d st,
      wf_constraints cns ->
      wf_constraints (subAll cns d st).
  Proof.
    exact SymTypes.subAll_wf.
  Qed.

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
          rewrite complete_subst_neq; [|exact Hd0].
          eapply order_trans.
          -- apply subST_complete_bound.
          -- eapply satisfiable_restore_self_lhs.
             exact Hhead.
        * eapply IH with (cns' := subAll cns d v).
          -- split; assumption.
          -- exact Hfind.
          -- reflexivity.
          -- exact Htail.
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
          eapply subAll_complete_none with (cns' := cns').
          -- split; assumption.
          -- exact Hfind_tail.
          -- exact Hsub.
          -- exact Hsat.
      + apply ident_eqb_neq in Hd0.
        rewrite <- Hsub in Hsat.
        inversion Hsat as [|c cs Hhead Htail]; subst c cs.
        apply Forall_cons.
        * unfold constraintSatisfiable, satisfiable in *.
          simpl in Hhead |- *.
          rewrite complete_subst_neq; [|exact Hd0].
          eapply order_trans.
            -- apply subST_complete_bound.
            -- eapply satisfiable_restore_self_lhs.
               exact Hhead.
        * eapply IH with (cns' := subAll cns d v).
          -- split; assumption.
          -- exact Hfind.
          -- reflexivity.
          -- exact Htail.
  Qed.

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
    intros dlt cns cns' d H_0 H_1. induction H_1; auto.

    apply find_correct in H. apply subAll_is_correct with (dlt:=dlt) in H0; auto.

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

  Definition simplify := SymTypes.simplify.
  Hint Unfold simplify.

  Lemma simplify_simplifyRel: forall ds cns  cns', simplify cns ds = cns' -> simplifyRel cns ds cns'.
  Proof.
    induction ds as [|d ds IH]; intros cns cns' Hsimp.
    - cbn in Hsimp. subst. constructor.
    - unfold simplify in Hsimp |- *.
      cbn in Hsimp |- *.
      destruct (SymTypes.findST cns d) as [st|] eqn:Hfind.
      + cbn in Hsimp.
        eapply elimCase1 with (st_0 := st) (cns' := SymTypes.subAll cns d st).
        * eapply IH. exact Hsimp.
        * exact Hfind.
        * reflexivity.
      + cbn in Hsimp.
        eapply elimCase2; eauto.
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

  (** This is the public completeness fact for [simplify].  If the raw constraint list is well formed and satisfied under a valuation, then the visible constraint list obtained after eliminating locals is also satisfied.  Signature-generation correctness proofs use this to move from raw local constraints to the public signature constraints. *)
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

  Definition constraint_scope := SymTypes.constraint_scope.

  Definition constraint_scoped := SymTypes.constraint_scoped.

  Definition constraints_scoped := SymTypes.constraints_scoped.

  Definition st_scoped := SymTypes.st_scoped.

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

  Lemma listSatisfiable_Permutation:
    forall dlt cns cns',
      Permutation cns cns' ->
      listSatisfiable dlt cns ->
      listSatisfiable dlt cns'.
  Proof.
    intros dlt cns cns' Hp.
    unfold listSatisfiable.
    now rewrite <- Hp.
  Qed.

  Lemma preserves_on_Permutation:
    forall scope c1 c1' c2 c2',
      Permutation c1 c1' ->
      Permutation c2 c2' ->
      preserves_on scope c1 c2 ->
      preserves_on scope c1' c2'.
  Proof.
    intros scope c1 c1' c2 c2' Hp1 Hp2 Hpres dlt Hsat.
    destruct (Hpres dlt (listSatisfiable_Permutation dlt c1' c1 (Permutation_sym Hp1) Hsat))
      as (dlt' & Hagree & Hsat').
    exists dlt'. split; [exact Hagree|].
    eapply listSatisfiable_Permutation; eauto.
  Qed.

  Lemma preserves_on_from_entailment:
    forall scope c1 c2,
      (forall dlt, listSatisfiable dlt c1 -> listSatisfiable dlt c2) ->
      preserves_on scope c1 c2.
  Proof.
    intros scope c1 c2 Hent dlt Hsat.
    exists dlt. split.
    - apply agree_on_refl.
    - apply Hent, Hsat.
  Qed.

  Lemma preserves_on_refl:
    forall scope cns,
      preserves_on scope cns cns.
  Proof.
    intros scope cns.
    apply preserves_on_from_entailment; auto.
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
    exact SymTypes.st_scoped_weaken.
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
    exact SymTypes.st_scoped_remove_app.
  Qed.

  Lemma st_scoped_drop_absent_app:
    forall pre post x st,
      ~ In x st ->
      st_scoped (pre ++ x :: post) st ->
      st_scoped (pre ++ post) st.
  Proof.
    exact SymTypes.st_scoped_drop_absent_app.
  Qed.

  Lemma st_scoped_merge:
    forall scope st1 st2,
      st_scoped scope st1 ->
      st_scoped scope st2 ->
      st_scoped scope (st1 ⊔ st2).
  Proof.
    exact SymTypes.st_scoped_merge.
  Qed.

  Lemma constraint_scoped_lhs:
    forall scope lhs rhs x,
      constraint_scoped scope (lhs, rhs) ->
      In x lhs ->
      In x scope.
  Proof.
    exact SymTypes.constraint_scoped_lhs.
  Qed.

  Lemma constraint_scoped_rhs:
    forall scope lhs rhs x,
      constraint_scoped scope (lhs, rhs) ->
      In x rhs ->
      In x scope.
  Proof.
    exact SymTypes.constraint_scoped_rhs.
  Qed.

  Lemma st_scoped_singleton:
    forall scope x,
      In x scope ->
      st_scoped scope [x].
  Proof.
    exact SymTypes.st_scoped_singleton.
  Qed.

  Lemma findST_of_rhs_in:
    forall cns d,
      In [d] (map snd cns) ->
      exists st, findST cns d = Some st.
  Proof.
    exact SymTypes.findST_of_rhs_in.
  Qed.

  Lemma subST_scoped_elim:
    forall scope ds d lhs st,
      st_scoped (scope ++ d :: ds) lhs ->
      st_scoped (scope ++ d :: ds) st ->
      st_scoped (scope ++ ds) (subST lhs d st).
  Proof.
    exact SymTypes.subST_scoped_elim.
  Qed.

  Lemma subAll_scoped_elim:
    forall scope ds cns d st,
      constraints_scoped (scope ++ d :: ds) cns ->
      st_scoped (scope ++ d :: ds) st ->
      constraints_scoped (scope ++ ds) (subAll cns d st).
  Proof.
    exact SymTypes.subAll_scoped_elim.
  Qed.

  Lemma subAll_preserves_other_rhs:
    forall cns d st d',
      d' <> d ->
      In [d'] (map snd cns) ->
      In [d'] (map snd (subAll cns d st)).
  Proof.
    exact SymTypes.subAll_preserves_other_rhs.
  Qed.

  Theorem simplify_scoped:
    forall scope ds cns,
      NoDup ds ->
      constraints_scoped (scope ++ ds) cns ->
      (forall d, In d ds -> In [d] (map snd cns)) ->
      constraints_scoped scope (simplify cns ds).
  Proof.
    exact SymTypes.simplify_scoped.
  Qed.

End SECTYPES.

Module SecTypes (Lat: Lattice) <: SECTYPES Lat.

  Include SECTYPES Lat.

End SecTypes.
