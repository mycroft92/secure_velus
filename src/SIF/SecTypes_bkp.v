From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Coq Require Import Lia.

From Velus Require Export SIF.SecLattice.
(** Outdated file, not used currently*)

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
        | a_0 :: st' => if ident_eqb a_0 a then true else my_set_mem a st'
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

      Lemma merge_comm: forall ls1 ls2, merge ls1 ls2 = merge ls2 ls1.
      Proof.
        induction ls1; intros.
        - rewrite merge_nil, merge_nil2. auto.
        - induction ls2 as [|b bs IHls2].
          * rewrite merge_nil, merge_nil2. auto.
          * simpl. destruct (Pos.compare a b) eqn:E.
      Admitted.
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

  Notation "x ⊔ y" := (my_set_union x y) (at level 40, left associativity).
  (* Notation "x ⊔ y" := (merge x y) (at level 40, left associativity). *)


  Fixpoint hm_ext (delta: ident -> Lat.t ) (xs: ST): Lat.t :=
    match xs with
    | nil   => Lat.bottom
    | x::xs' => join  (delta x) (hm_ext delta xs')
    end.

  Definition st_remove := List.remove ident_eq_dec.
  Definition st_mem    := my_set_mem.
  (*Local hint data bases from Lattices*)
  Hint Immediate eq_sym.
  Hint Resolve merge_nil merge_nil2 merge_comm eq_refl eq_trans eqb_refl
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
    induction st1 as [|a st' IHst]; intros * H1 H2. auto.
    (* - rewrite merge_nil. auto.
    - rewrite merge_comm. simpl. destruct st2 eqn:E.
      * auto.
      * destruct (Pos.compare a i) eqn:Hai.
        +  *)
    simpl. apply set_rm_lub_r with (d_0:=a) in H1 as H3.
    apply set_rm_lub_l with (d_0:=a) in H1 as H4.
    destruct (my_set_mem a st2) eqn:E1.
    - apply IHst; auto.
    - simpl. apply join_least_upper_bound; auto.
  Qed.

  Lemma hm_ext_concat_l : forall dlt a b,
     hm_ext dlt a ⊑ hm_ext dlt (a ⊔ b).
  Proof.
    intros dlt a. induction a as [|a_0 a IHa]; auto.
    intros. apply join_least_upper_bound.
    - induction b as [|b_0 b IHb].
        + simpl. apply join_bound1.
        + simpl. destruct (ident_eqb a_0 b_0) eqn:E.
          * apply IHb.
          * destruct (my_set_mem b_0 a) eqn:E2.
            ++ apply IHb.
            ++ simpl. apply order_trans with (y:= (hm_ext dlt ((a_0 :: a) ⊔ b))); auto.
      - fold hm_ext. induction b as [|b_0 b IHb].
        + simpl. auto.
        + simpl. destruct (ident_eqb a_0 b_0) eqn:E.
          * auto.
          * destruct (my_set_mem b_0 a) eqn:E2.
            ++ auto.
            ++ simpl. apply order_trans with (y:= (hm_ext dlt ((a_0 :: a) ⊔ b))); auto.
  Qed.

  Lemma hm_ext_concat_r : forall dlt a b,
    hm_ext dlt b ⊑ hm_ext dlt (a ⊔ b).
  Proof.
    intros dlt a b. generalize dependent a. induction b as [|b_0 b IHb].
    - auto.
    - intros a. apply join_least_upper_bound; auto.
      * simpl. destruct (my_set_mem b_0 a) eqn:E.
        + apply my_set_mem_correct in E. eapply hm_ext_list_in1 in E.
          eapply order_trans. eauto. apply hm_ext_concat_l.
        + simpl. apply join_bound1.
      * fold hm_ext. simpl. destruct (my_set_mem b_0 a) eqn:E; auto.
        eapply order_trans. eapply IHb. eauto.
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

  Hint Resolve hm_ext_concat_l hm_ext_concat_r  hm_ext_distributive
  hm_ext_list_in1.

  (*Constraints and substitutions*)
  (*Under dlt, s_0 ⊑ s_1 *)
  Definition satisfiable (dlt: ident -> Lat.t) (s_0 s_1: ST) :=
    (hm_ext dlt s_0) ⊑ (hm_ext dlt s_1).

  Definition listSatisfiable (dlt: ident -> Lat.t) (cns: list constraint) :=
    Forall (fun '(s,x) => satisfiable dlt s x) cns.

  Hint Unfold satisfiable listSatisfiable.

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

  Print NoDup.
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

  Print Forall.

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

  (*Substitute an ident d in st wtih st'*)
  Definition subST st d st' : ST :=
  match st_mem  d st with
  | false => st
  | true  => if st_mem d st' then (st_remove d st) ⊔ (st_remove d st') else (st_remove d st) ⊔ st'
  end.

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

  Theorem simplify_is_correct : forall dlt cns cns' d,
    listSatisfiable dlt cns -> simplifyRel cns d cns' -> listSatisfiable dlt cns'.
  Proof.
    intros dlt cns cns' d H_0 H_1. induction H_1; auto. (*base cases are trivial*)
    (*induction case*)
    apply find_correct in H. apply subAll_is_correct with (dlt:=dlt) in H0; auto.
    (*We need to show that the constraint that is being substituted was originally satisfiable*)
    (*But this is trivial since it's part of a list of constraints that were ALL satisfiable*)
    rewrite -> (Forall_forall (fun '(s, x) => satisfiable dlt s x) cns) in H_0. apply H_0 in H. auto.
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

  Lemma simplify_simplifyRel: forall ds cns  cns', simplify cns ds = cns' -> simplifyRel cns ds cns'.
  Proof.
    induction ds; intros.
    - cbn in H. subst. auto.
    - cbn in H. destruct (findST cns a) eqn:E.
      * remember (subAll cns a s) as cns''. eapply elimCase1; eauto.
      * apply elimCase2; auto.
  Qed.


End SECTYPES.

(*
- Syntactic subset checks might make most of the effort easier.
- make types Canonical (order the identifiers within the list)
    - make sure the LUB properties hold
- Confluence
- Soundness for the extended form (of the type equalities)
- Add constraint simplification (refer to the notes on15th Oct)

- New fresh monad representation, on "st ident"
- Abstract on the fresh name, don't push the generated names into record
*)
Print SECTYPES.

Module SecTypes (Lat: Lattice) <: SECTYPES Lat.

  Include SECTYPES Lat.

End SecTypes.

Print SecTypes.
