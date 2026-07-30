(** Canonical symbolic types and constraint operations. *)

From Coq Require Import List.
From Coq Require Import Lists.ListSet.

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Coq Require Import Lia.
Import ListNotations.
From Coq Require Import Recdef.
Definition ST := list ident.
Definition constraint := (ST*ST)%type.

Fixpoint my_set_mem (a: ident) (st: ST) : bool :=
    match st with
    | [] => false
    | a_0 :: st' => if ident_eqb a_0 a then true else my_set_mem a st'
    end.

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

Fixpoint merge (c1: ST) : ST -> ST :=
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

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1::x2::l' =>
    let (l1,l2) := split l' in
    (x1::l1,x2::l2)
  end.

Definition list_ind2:
  forall (A:Type) (P: list A -> Prop),
    P [] -> (forall (a:A), P [a]) -> (forall (a b: A) (l: list A), P l -> P (a::b::l)) ->
    forall l: list A, P l :=
  fun (A: Type)
      (P: list A -> Prop)
      (H: P [])
      (H0: forall a: A, P [a])
      (H1: forall (a b: A) (l: list A), P l -> P (a::b::l))=>
    fix IH (l: list A): P l:=
      match l with
      | [] => H
      | [x] => H0 x
      | x::y::l' => H1 x y l' (IH l')
    end.

Section SplitFacts.
  Lemma split_len: forall {X} (l: list X) (l1 l2: list X),
    split l = (l1,l2) -> length l1 <= length l /\ length l2 <= length l.
  Proof.
    induction l using list_ind2; intros.
    - inv H. lia.
    - inv H. simpl; lia.
    - inv H. destruct (split l) as [l1' l2']. inv H1.
      simpl. destruct (IHl l1' l2') as [P1 P2]; auto; lia.
  Qed.

End SplitFacts.

Module MergeFacts.
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

    Lemma sortedNoDup_hard: forall l a b, (sortedNoDup (a::l) -> b < a -> sortedNoDup (b:: a:: l))%positive.
    Proof.
      induction l; intros; auto.

    Qed.

    Lemma sortedNoDup_hard2: forall l a b, (sortedNoDup (a::l) -> b <= a -> sortedNoDup (b:: l))%positive.
    Proof.
      induction l; intros; auto.
      inversion H; subst. assert (b < a)%positive. { lia. }
      auto.

    Qed.

    Ltac pos_handler :=
      match goal with
      | [H:  (?x < ?y)%positive,
         H2: (?y < ?x)%positive |- _] =>  lia
      | [H:  (?x < ?x)%positive |- _] =>  elim (Pos.lt_irrefl x H)
      | [H:  (?x ?= ?x)%positive = Lt |- _] => rewrite Pos.compare_lt_iff in H; elim (Pos.lt_irrefl x H)
      | [H:  (?x ?= ?x)%positive = Gt |- _] => rewrite Pos.compare_gt_iff in H; elim (Pos.lt_irrefl x H)
      | [H:  (_ ?= _)%positive = Gt |- _] =>  rewrite Pos.compare_gt_iff in H
      | [H:  (_ ?= _)%positive = Eq |- _] =>  rewrite Pos.compare_eq_iff in H; subst
      | [H:  (_ ?= _)%positive = Lt |- _] =>  rewrite Pos.compare_lt_iff in H
      end.

    Lemma merge1: forall a1 a2 l1 l2, (a1 < a2)%positive -> merge (a1::l1) (a2::l2) = a1 :: merge l1 (a2::l2).
    Proof.
      intros.
      simpl.
      destruct (Pos.compare a1 a2) eqn:E; repeat pos_handler; auto.
    Qed.

    Lemma merge2: forall a1 a2 l1 l2, (a2 < a1) %positive -> merge (a1::l1) (a2::l2) = a2 :: merge (a1::l1) l2.
    Proof.
      intros.
      simpl.
      destruct (Pos.compare a1 a2) eqn:E; repeat pos_handler; auto.
    Qed.

    Lemma merge3: forall a l1 l2, merge (a::l1) (a::l2) = a:: merge l1 l2.
    Proof.
      intros. simpl.
      destruct (Pos.compare a a) eqn:E; pos_handler. auto.
    Qed.

    Lemma sorted_merge1: (forall x x1 l1 x2 l2,
        x < x1 -> x < x2 -> sortedNoDup (merge (x1::l1) (x2::l2)) ->
        sortedNoDup (x :: merge (x1::l1) (x2::l2)) )%positive.
    Proof.
      intros. simpl in *.
      destruct (Pos.compare x1 x2) eqn: E; repeat pos_handler; auto.
    Qed.

    Lemma sortedNoDup_merge: forall l1, sortedNoDup l1 -> forall l2, sortedNoDup l2 -> sortedNoDup (merge l1 l2).
    Proof.
      induction l1.
      - intros. rewrite merge_nil2; auto.
      - induction l2; intros.
        * now rewrite merge_nil.
        * simpl; destruct (Pos.compare a a0) eqn:E; pos_handler.
         + destruct l1; destruct l2; try rewrite merge_nil; try rewrite merge_nil2; auto.
           apply sorted_merge1; inversion H; subst; inversion H0; subst; auto.
         + inversion H; subst; inversion H0; subst.
           ++ rewrite merge_nil2. auto.
           ++ rewrite merge_nil2; auto.
           ++ apply  sorted_merge1; auto.
           ++ apply sorted_merge1; auto.
         + destruct l2; auto.
           apply sorted_merge1; inversion H0; inversion H; subst; auto.
    Qed.

    Lemma merge_refl: forall l, merge l l = l.
    Proof.
      induction l; simpl.
      - easy.
      - destruct (Pos.compare a a) eqn:E; pos_handler. now rewrite IHl.
    Qed.

    Hint Rewrite merge1 merge2.
    Lemma merge_assoc: forall l0 l1 l2, merge (merge l0 l1) l2 = merge l0 (merge l1 l2).
    Proof.
      induction l0 as [| a0 l0 IHl0].
      - induction l1 as [|a1 l1 IHl1].
        * intros. now rewrite merge_nil,merge_nil2,merge_nil2.
        * intros. now repeat rewrite  merge_nil2.
      - induction l1 as [|a1 l1 IHl1].
        * intros. now repeat rewrite merge_nil,merge_nil2.
        * intros.  induction l2 as [|a2 l2 IHl2].
          + simpl ; destruct (Pos.compare a0 a1) eqn:E0; pos_handler; auto.
          + simpl. destruct (Pos.compare a1 a2) eqn:E12.

          ++ destruct (Pos.compare a0 a1) eqn:E01;  repeat pos_handler; auto.
             ** now rewrite merge3,IHl0.
             ** simpl. destruct (Pos.compare a0 a2) eqn:E02; repeat pos_handler. now rewrite IHl0,merge3.
             ** rewrite merge3. rewrite IHl1. auto.
          ++ destruct (Pos.compare a0 a1) eqn:E01;  repeat pos_handler; auto.
             ** simpl. destruct (Pos.compare a1 a2) eqn:E12';  repeat pos_handler. now rewrite IHl0.
             ** simpl. destruct (Pos.compare a0 a2) eqn:E02;  repeat pos_handler.
                -- rewrite IHl0. rewrite merge1; auto.
                -- lia.
             ** now rewrite merge1, IHl1.
          ++ destruct (Pos.compare a0 a2) eqn:E02;  repeat pos_handler; auto.
             ** destruct (Pos.compare a2 a1) eqn:E21; repeat pos_handler. now rewrite merge3,IHl0.
             ** destruct (Pos.compare a0 a1) eqn:E01;  repeat pos_handler.

               -- simpl. destruct  (Pos.compare a0 a2) eqn:E02';  repeat pos_handler. rewrite IHl0.
                  simpl. destruct  (Pos.compare a1 a2) eqn:E12';  repeat pos_handler; auto.
               -- lia.
             ** destruct (Pos.compare a0 a1) eqn:E01;  repeat pos_handler.
                -- rewrite merge2; auto. now rewrite <- (merge3 a1),IHl2.
                -- rewrite merge2; auto. f_equal. rewrite <- merge1; auto.
                -- rewrite merge2; auto. f_equal. simpl in IHl2.
                   destruct (Pos.compare a0 a1) eqn:E01'; repeat pos_handler. auto.
    Qed.

    Lemma merge_singleton_cons_sorted: forall a ls,
      sortedNoDup (a::ls) ->
      merge [a] ls = a::ls.
    Proof.
      intros a ls Hsorted.
      destruct ls as [|b bs].
      - simpl. destruct (Pos.compare a a) eqn:E; pos_handler. auto.
      - simpl. inversion Hsorted; subst.
        destruct (Pos.compare a b) eqn:E; repeat pos_handler; auto.
    Qed.

    Lemma merge_comm2: forall a ls1 ls2,
      sortedNoDup (a::ls1) ->
      merge (a::ls1) ls2 = merge [a] (merge ls1 ls2).
    Proof.
      intros a ls1 ls2 Hsorted.
      rewrite <- (merge_singleton_cons_sorted a ls1 Hsorted).
      apply merge_assoc.
    Qed.

End MergeFacts.

Import MergeFacts.
Function sortST (l: ST) {measure length l} : ST :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => let (l1,l2) := split l in merge (sortST l1) (sortST l2)
  end.
Proof.
  - intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E.  inv teq1. simpl.
    destruct (split_len l1 l1' l2'); auto; lia.
  -  intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. simpl.
    destruct (split_len l1 l1' l2' E); lia.
Defined.

Lemma mergesort_correct: forall l, sortedNoDup (sortST l).
  Proof.
      apply sortST_ind; intros; auto.
      now apply sortedNoDup_merge.
  Qed.

Notation "x ⊔ y" := (merge x y) (at level 40, left associativity).
Definition st_remove := List.remove ident_eq_dec.
Definition st_mem    := my_set_mem.

Lemma sym_st_remove_notin:
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

Lemma sym_st_remove_preserves_other_in:
  forall x d st,
    x <> d ->
    In x st ->
    In x (st_remove d st).
Proof.
  intros x d st Hneq Hin.
  induction st as [|a st IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst a.
      unfold st_remove. simpl.
      destruct (ident_eq_dec d x) as [Hdx|Hdx].
      * exfalso. apply Hneq. symmetry. exact Hdx.
      * left. reflexivity.
    + unfold st_remove. simpl.
      destruct (ident_eq_dec d a) as [Hda|Hda].
      * apply IH. exact Hin.
      * right. apply IH. exact Hin.
Qed.

Fixpoint stEq (c1 c2: ST)  : Prop :=
  let c1 := sortST c1 in
  let c2 := sortST c2 in
  (fix eqst (c1 c2: ST) : Prop :=
  match c1,c2 with
  | [], [] => True
  | [], _  => False
  | _ , [] => False
  | x::c1', y::c2' => if ident_eqb x y then eqst c1' c2'  else False
  end) c1 c2.

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

Definition subST st d st' : ST :=
  match st_mem  d st with
  | false => st
  | true  => if st_mem d st' then (st_remove d st) ⊔ (st_remove d st') else (st_remove d st) ⊔ st'
  end.

Definition wf_constraints (cs: list constraint) : Prop :=
  NoDup (map snd cs) /\ Forall (fun '(_, rhs) => length rhs = 1) cs.

Definition constraint_scope (c: constraint) : list ident :=
  fst c ++ snd c.

Definition constraint_scoped (scope: list ident) (c: constraint) : Prop :=
  forall x, In x (constraint_scope c) -> In x scope.

Definition constraints_scoped (scope: list ident) (cns: list constraint) : Prop :=
  Forall (constraint_scoped scope) cns.

Definition st_scoped (scope: list ident) (st: ST) : Prop :=
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

Lemma in_merge_left:
  forall x a b,
    In x a ->
    In x (a ⊔ b).
Proof.
  intros x a.
  induction a as [|a0 a IHa]; intros b Hin.
  - contradiction.
  - revert Hin.
    induction b as [|b0 b IHb]; intro Hin.
    + simpl. exact Hin.
    + simpl.
      destruct Hin as [Heq|Hin].
      * subst x.
        destruct (Pos.compare a0 b0) eqn:Hcmp; simpl.
        -- left; reflexivity.
        -- left; reflexivity.
        -- right. apply IHb. left; reflexivity.
      * destruct (Pos.compare a0 b0) eqn:Hcmp; simpl.
        -- right. eapply IHa. exact Hin.
        -- right. eapply IHa. exact Hin.
        -- right. apply IHb. right; exact Hin.
Qed.

Lemma in_merge_right:
  forall x a b,
    In x b ->
    In x (a ⊔ b).
Proof.
  intros x a b Hin.
  rewrite MergeFacts.merge_comm.
  now apply in_merge_left.
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

Lemma merge_incl_mono:
  forall a a' b b',
    (forall z, In z a -> In z a') ->
    (forall z, In z b -> In z b') ->
    forall z, In z (a ⊔ b) -> In z (a' ⊔ b').
Proof.
  intros a a' b b' Ha Hb z Hz.
  apply in_merge_inv in Hz.
  destruct Hz as [Hz|Hz].
  - apply in_merge_left. exact (Ha _ Hz).
  - apply in_merge_right. exact (Hb _ Hz).
Qed.


Lemma st_remove_notin:
  forall d st,
    my_set_mem d st = false ->
    st_remove d st = st.
Proof.
  exact sym_st_remove_notin.
Qed.

Lemma st_remove_preserves_other_in:
  forall x d st,
    x <> d ->
    In x st ->
    In x (st_remove d st).
Proof.
  exact sym_st_remove_preserves_other_in.
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

Definition normalize_constraint (lhs: ST) (rhs: ident) : constraint :=
  (st_remove rhs lhs, [rhs]).

Fixpoint subAll cns d st' : list constraint :=
  match cns with
  | [] => []
  | (st, [d'])::cns' => if ident_eqb d' d then
                        subAll cns' d st'
                      else normalize_constraint (subST st d st') d' :: subAll cns' d st'
  | _ :: cns'   => subAll cns' d st'
  end.

Fixpoint simplify (cns: list constraint) (ds: list ident) : list constraint :=
  match ds with
  | []    => cns
  | d::ds' => match findST cns d with
             | None    => simplify cns ds'
             | Some st => simplify (subAll cns d st) ds'
             end
  end.

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
                 destruct (st_remove_in_inv _ _ _ Hin) as [Hin' _].
                 exact (Hsub y Hin').
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

Lemma subAll_nodup:
  forall cns d st,
    NoDup (map snd cns) ->
    NoDup (map snd (subAll cns d st)).
Proof.
  induction cns as [|[lhs rhs] cns IH]; intros d st Hnd; simpl.
  - constructor.
  - apply NoDup_cons_iff in Hnd as [Hnin Hnd].
    destruct rhs as [|r rhs'].
    + exact (IH _ _ Hnd).
    + destruct rhs' as [|r' rhs''].
      * destruct (ident_eqb r d) eqn:Hr.
        -- exact (IH _ _ Hnd).
        -- apply NoDup_cons_iff. split.
           ++ intro Hin.
              apply Hnin.
              eapply subAll_rhs_in; eauto.
           ++ exact (IH _ _ Hnd).
      * exact (IH _ _ Hnd).
Qed.

Lemma subAll_singleton_rhs:
  forall cns d st,
    Forall (fun '(_, rhs) => length rhs = 1) cns ->
    Forall (fun '(_, rhs) => length rhs = 1) (subAll cns d st).
Proof.
  induction cns as [|[lhs rhs] cns IH]; intros d st Hlen; simpl.
  - constructor.
  - inversion Hlen as [|[lhs0 rhs0] cns0 Hhd Htl]; subst lhs0 rhs0 cns0.
    destruct rhs as [|r rhs'].
    + discriminate Hhd.
    + destruct rhs' as [|r' rhs''].
      * destruct (ident_eqb r d) eqn:Hr.
        -- exact (IH _ _ Htl).
        -- constructor.
           ++ simpl. reflexivity.
           ++ exact (IH _ _ Htl).
      * discriminate Hhd.
Qed.

Corollary subAll_wf:
  forall cns d st,
    wf_constraints cns ->
    wf_constraints (subAll cns d st).
Proof.
  intros cns d st [Hnd Hlen].
  split.
  - eapply subAll_nodup; eauto.
  - eapply subAll_singleton_rhs; eauto.
Qed.

Lemma simplify_rhs_in:
  forall cns ds rhs,
    In rhs (map snd (simplify cns ds)) ->
    In rhs (map snd cns).
Proof.
  intros cns ds.
  revert cns.
  induction ds as [|d ds IH]; intros cs rhs Hin; simpl in *.
  - exact Hin.
  - destruct (findST cs d) as [st|] eqn:Hfind.
    + specialize (IH (subAll cs d st) rhs Hin).
      eapply subAll_rhs_in. exact IH.
    + eapply (IH cs rhs). exact Hin.
Qed.

Lemma simplify_preserves_other_rhs:
  forall cns ds d0,
    (forall d, In d ds -> d0 <> d) ->
    In [d0] (map snd cns) ->
    In [d0] (map snd (simplify cns ds)).
Proof.
  intros cns ds.
  revert cns.
  induction ds as [|d ds IH]; intros cs d0 Hneq Hin; simpl.
  - exact Hin.
  - destruct (findST cs d) as [st|] eqn:Hfind.
    + eapply (IH (subAll cs d st) d0).
      * intros d' Hin'. apply Hneq. now right.
      * eapply subAll_preserves_other_rhs; eauto.
        apply Hneq. now left.
    + eapply (IH cs d0); eauto.
      intros d' Hin'. apply Hneq. now right.
Qed.

Lemma simplify_nodup:
  forall cns ds,
    NoDup (map snd cns) ->
    NoDup (map snd (simplify cns ds)).
Proof.
  intros cns ds.
  revert cns.
  induction ds as [|d ds IH]; intros cns Hnd; simpl.
  - exact Hnd.
  - destruct (findST cns d) as [st|] eqn:Hfind.
    + apply IH. eapply subAll_nodup. exact Hnd.
    + apply IH. exact Hnd.
Qed.

Lemma simplify_singleton_rhs:
  forall cns ds,
    Forall (fun '(_, rhs) => length rhs = 1) cns ->
    Forall (fun '(_, rhs) => length rhs = 1) (simplify cns ds).
Proof.
  intros cns ds.
  revert cns.
  induction ds as [|d ds IH]; intros cns Hlen; simpl.
  - exact Hlen.
  - destruct (findST cns d) as [st|] eqn:Hfind.
    + apply IH. eapply subAll_singleton_rhs. exact Hlen.
    + apply IH. exact Hlen.
Qed.

Corollary simplify_wf:
  forall cns ds,
    wf_constraints cns ->
    wf_constraints (simplify cns ds).
Proof.
  intros cns ds [Hnd Hlen].
  split.
  - eapply simplify_nodup; eauto.
  - eapply simplify_singleton_rhs; eauto.
Qed.

Section ConstraintOrdering.

  Definition ident_list_compare (l1 l2: list ident): comparison :=
    let l1' := sortST l1 in
    let l2' := sortST l2 in
    (fix compare' (l1 l2: list ident): comparison :=
    match l1,l2 with
    | [], [] => Eq
    | [], _  => Lt
    | _, []  => Gt
    | a1::l1'', a2::l2'' =>
        match Pos.compare a1 a2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => compare' l1'' l2''
        end
    end) l1' l2'.

  Definition ident_sorted_list_compare (l1 l2: list ident): comparison :=
    (fix compare' (l1 l2: list ident): comparison :=
    match l1,l2 with
    | [], [] => Eq
    | [], _  => Lt
    | _, []  => Gt
    | a1::l1'', a2::l2'' =>
        match Pos.compare a1 a2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => compare' l1'' l2''
        end
    end) l1 l2.

  Definition constraint_compare (c1 c2: constraint) : comparison :=
    let (c1x, c1y) := (sortST (fst c1), snd c1) in
    let (c2x, c2y) := (sortST (fst c2), snd c2) in
    match (ident_sorted_list_compare c1y c2y) with
    | Eq => ident_sorted_list_compare c1x c2x
    | Lt => Lt
    | Gt => Gt
    end.

  Fixpoint constraint_merge (c1s : list constraint) : list constraint -> list constraint :=
  fix merge' c2s :=
    match c1s,c2s with
    | [], _ => c2s
    | _, [] => c1s
    | x::xs, y::ys => match constraint_compare x y with
                      | Lt => x:: (constraint_merge xs c2s)
                      | Eq => x:: (constraint_merge xs ys)
                      | Gt => y:: (merge' ys)
                      end
    end.

End ConstraintOrdering.
