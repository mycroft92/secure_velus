From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Coq Require Import Lia.

From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes.
(* Require Import Coq.Program.Equality. *)


Module Type SECTYPESEXTENDED(Import Lat: Lattice).
    Import ListNotations.
    Import MergeFacts.
  
  Hint Resolve my_set_mem_correct.
  (* Hint Unfold my_set_union. *)

  (* Notation "x ⊔ y" := (my_set_union x y) (at level 40, left associativity). *)
  Notation "x ⊔ y" := (merge x y) (at level 40, left associativity).


  Fixpoint hm_ext (delta: ident -> Lat.t ) (xs: ST): Lat.t := 
    match xs with
    | nil    => Lat.bottom
    | x::xs' => join  (delta x) (hm_ext delta xs')
    end.
  
  (* Definition st_remove := List.remove ident_eq_dec.
  Definition st_mem    := my_set_mem. *)
  (*Local hint data bases from Lattices*)
  Hint Immediate eq_sym.

  Hint Resolve merge_nil merge_nil2 merge_comm intersect_nil intersect_nil2 intersect_comm eq_refl eq_trans   
    eqb_refl order_refl order_antisym order_trans join_bound1 join_bound2 join_least_upper_bound
    meet_bound1 meet_bound2 meet_greatest_lower_bound bottom_is_bottom top_is_top.

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

  Hint Resolve hm_ext_concat_l hm_ext_concat_r  hm_ext_distributive 
  hm_ext_list_in1.
  
  (*Constraints and substitutions*)
  (*Under dlt, s_0 ⊑ s_1 *)
  Definition satisfiable (dlt: ident -> Lat.t) (s_0 s_1: ST) := 
    (hm_ext dlt s_0) ⊑ (hm_ext dlt s_1).
  
  Definition listSatisfiable (dlt: ident -> Lat.t) (cns: list constraint) :=
    Forall (fun '(s,x) => satisfiable dlt s x) cns.

  Hint Unfold satisfiable listSatisfiable.
  
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


  
  Lemma wf_constraints_shape : forall cs x y,
    wf_constraints cs -> List.In (y,x) cs -> exists d, x = [d].
  Proof.
    intros * H_0 H_1. unfold wf_constraints in H_0. destruct H_0 as [Hl Hr].
    rewrite Forall_forall in Hr. apply Hr in H_1 as Hres. apply list_len_1. auto.
  Qed.

  Hint Resolve list_len_1 wf_constraints_shape.


  Hint Resolve find_correct.
  

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
  
  

  (* Check Forall_inv.
  Check Forall_inv_tail. 
  Check Forall_cons. *)
  Lemma subAll_is_correct :  forall Δ cns δ v cns',
    satisfiable Δ v [δ] ->
    subAll cns δ v = cns' -> listSatisfiable Δ cns -> listSatisfiable Δ cns'.
  Proof.
    intros Δ cns d v. induction cns as [|(l,r) cns IHcns];
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
                apply Forall_inv in H_2 as H_2'. apply (subST_correct Δ l [d_0] d v st_0); auto.
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

  Theorem simplifyRel_is_correct : forall (Δ: ident -> Lat.t) cns cns' δs,
    listSatisfiable Δ cns -> simplifyRel cns δs cns' -> listSatisfiable Δ cns'.
  Proof.
    intros Δ cns cns' δs H_0 H_1. induction H_1; auto. (*base cases are trivial*)
    (*induction case*)
    apply find_correct in H. apply subAll_is_correct with (Δ:=Δ) in H0; auto.
    (*We need to show that the constraint that is being substituted was originally satisfiable*)
    (*But this is trivial since it's part of a list of constraints that were ALL satisfiable*)
    rewrite -> (Forall_forall (fun '(s, x) => satisfiable Δ s x) cns) in H_0. apply H_0 in H. auto.
  Qed.


  Lemma simplify_simplifyRel: forall δs cns  cns', simplify cns δs = cns' -> simplifyRel cns δs cns'.
  Proof.
    induction δs; intros.
    - cbn in H. subst. auto.
    - cbn in H. destruct (findST cns a) eqn:E.
      * remember (subAll cns a s) as cns''. eapply elimCase1; eauto.
      * apply elimCase2; auto.
  Qed.

  Theorem simplify_is_correct : forall (Δ: ident -> Lat.t) cns cns' δs,
    listSatisfiable Δ cns -> simplify cns δs = cns' -> listSatisfiable Δ cns'.
  Proof.
    intros. apply simplify_simplifyRel in H0. eapply simplifyRel_is_correct; eauto.
  Qed.


End SECTYPESEXTENDED.

(*
- Syntactic subset checks might make most of the effort easier.
- make types Canonical (order the identifiers within the list) 
    - make sure the LUB properties hold
- Confluence (* would need an inductive predicate along the lines of sorted*)
- Soundness for the extended form (of the type equalities)
- Add constraint simplification (refer to the notes on15th Oct)
    a <= b, c <= b => a ⊔ c <= b 
(*subset properties on lists required for this*)
- New fresh monad representation, on "st ident"
- Abstract on the fresh name, don't push the generated names into record
*)
(*
- Refinement types, soundness of simplify
- Lustre typing
  - NLustre constraints to be ordered.
  - Constraints equisatisfiability on the same DLT (ident -> sec ident)
  - Use a helper function that changes 
- Confluence
- Subject reduction
*)
Print SECTYPES.

Module SecTypes (Lat: Lattice) <: SECTYPES Lat.

  Include SECTYPES Lat.

End SecTypes.

Print SecTypes.
