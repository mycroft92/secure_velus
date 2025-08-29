(*Describes security signature related properties.*)
(* Change this implementation to work with res and Sec Monad*)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 
From Velus Require Import SIF.SecTypes. 
From Velus Require Export SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Coq   Require Import List Sorting.Permutation.
From Coq Require Import String. (*for errors*)
From compcert Require Import common.Errors.
Import List.ListNotations.

(*
    Given a node with input variables: x,y and output: z in the node signature
    Say n_in: [α_1,α_2], n_out:= [β], 
    we always asssume x has type α_1, y has type α_2 and z has type β
    Constraints can be in any order!
*)


Module Type SIGNATURE 
  (Import Ids : IDS)
  (Import SC  : SECMONAD Ids).
(* 1. How do I carry the constraints?
   2. How do I replace the vars in constraints with newly generated names? *)
Import SECMONADNotations.
(* Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list (ident*ident); (*ordered list of input security types*)
    n_out  : list (ident*ident); (*ordered list of output security types*)

    n_reset: ident*ident; (* We generate the name for the reset type and its corresponding value*)
    n_clk  : ident*ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    constraints : list constraint; (*constraints*)
}. *)
(*simpler record*)
Record signature := mkSig {
    s_name : ident; (*node name*)
    s_in   : list ident; (*ordered list of input security types*)
    s_out  : list ident; (*ordered list of output security types*)

    s_reset: ident; (* We generate the name for the reset type and its corresponding value*)
    s_clk  : ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    s_constraints : list constraint; (*constraints*)
}.
Definition secglobal := list signature.


Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).


Section Type_Substitutions.
    (* ty[v/x] substitution*)
  Local Definition subst_ident_in_type (ty: ST) (x: ident) (v: ST): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ (st_remove x v)
    end.
  (* THIS is ST substitution, need to rethink. substituting preserves type maybe required here. *)
  
  Definition subst_inp_ident_in_constraint (c: constraint) (x: ident) (v: ST): Sec constraint :=
    match c with
    | (ty, [x']) => 
      if ident_eqb x x' then
        error (MSG "Something wrong with fresh_gen, ident is regenerated in an inner node. " :: [CTX x])
      else ret (subst_ident_in_type ty x v, [x'])
    | _ => error (msg "malformed constraint")
    end.
  (* THIS is ST substitution, need to rethink. substitution preserves satisfiability required here*)
  (* if c is satisfied before substitution, then c is satistfied after substituting x in c.*)
   (* forall c ∈ cs, c[v/x]*)
  Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v: ST)
   : Sec (list constraint) :=
   mmap (fun c => subst_inp_ident_in_constraint c x v) cs.
   (* induction obviously for multiple cs*)

   (*input types are to substituted by this function, in the FINAL call constraint set. *)
  Fixpoint subst_constraints_inp_map (cs: list constraint) (xs: list ident) (vs: list ST): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs => 
    (*Do we need additional help like x is not present in ANY vs?*)
      do cs' <- subst_ident_in_constraints cs x v;
      subst_constraints_inp_map cs' xs vs
    | _, _ => error (msg "Malformed replace map")
    end.

  Local Definition subst_ident (ty: ST) (x v: ident): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ [v]
    end.

  Definition subst_ident_constraint (c: constraint) (x v: ident): Sec constraint :=
    if ident_eqb x v then error (msg "Illegal same ident substitution") else
    (match c with
    | (ty, [x']) => 
       if ident_eqb x x' then
        ret (subst_ident_in_type ty x [v], [v])
       else ret (subst_ident_in_type ty x [v], [x'])
    | _  => error (msg "Malformed constraint")
    end).

  Definition subst_ident_constraints (cs: list constraint) (x v: ident): Sec (list constraint) :=
    mmap (fun c => subst_ident_constraint c x v) cs.

  Fixpoint subst_constraints_out_map (cs: list constraint) (xs: list ident) (vs: list ident): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs => 
    (*Do we need additional help like x is not present in ANY vs?*)
      do cs' <- subst_ident_constraints cs x v;
      subst_constraints_out_map cs' xs vs
    | _, _ => error (msg "Malformed replace map")
    end.
  
  (* We need lemmas that the substitution is happening correctly *)
  Definition generate_constraints (node: signature) 
    (inp: list ST) 
    (clk: ST) 
    (res: ST) 
    (out: list ident): Sec (list constraint) :=
    do inp_subst_constraints <- subst_constraints_inp_map node.(s_constraints) node.(s_in) inp;
    do clk_subst_constraints <- subst_ident_in_constraints inp_subst_constraints node.(s_clk) clk;
    do res_subst_constraints <- subst_ident_in_constraints clk_subst_constraints node.(s_reset) res;
    subst_constraints_out_map res_subst_constraints node.(s_out) out.
    
  (* Substitution lemma *)
   
End Type_Substitutions.

End SIGNATURE.
(* What correctness criterion would be needed? *)
(**)
(*Need to write a bunch of axioms that the number of list node == number of signature, for every node there is a signature etc..*)

Module Signature 
    (Ids : IDS)
    (SC : SECMONAD Ids) <: SIGNATURE Ids SC.
Include SIGNATURE Ids SC.
End Signature.

Module Type SIGNATURE_PROOFS (Import Ids: IDS)
  (Import SC: SECMONAD Ids)
  (Import SIG: SIGNATURE Ids SC)
  (Import Lat: Lattice)
  (Import SecTypes: SECTYPES Lat).
Import MergeFacts.
  Lemma st_remove_correct: forall dlt ty x, hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty.
  Proof.
    induction ty; intros.
    - now unfold SymTypes.st_remove.
    - unfold  SymTypes.st_remove. simpl.
      destruct (ident_eq_dec x a) eqn:Hxa.
      + subst x. assert (hm_ext dlt (remove ident_eq_dec a ty) ⊑ hm_ext dlt ty) as H1. { auto. }
      assert (hm_ext dlt ty ⊑ join (dlt a) (hm_ext dlt ty)) as H2. { apply join_bound2. }
      now eapply order_trans.
      + simpl. auto.
  Qed. 

  Lemma subst_ident_in_type_correct1: 
      forall dlt x st ty, hm_ext dlt st ⊑ dlt x 
      -> hm_ext dlt (SIG.subst_ident_in_type ty x st) ⊑ hm_ext dlt ty.
  Proof.
    induction ty; intros; unfold SIG.subst_ident_in_type; unfold SymTypes.my_set_mem; auto.
    destruct (ident_eqb a x) eqn:Hax.
    - unfold SymTypes.st_remove.  
      apply ident_eqb_eq in Hax; subst. simpl.
      destruct (ident_eq_dec x x) eqn:Hxx; auto.
      * fold SymTypes.st_remove. apply (hm_ext_distributive dlt (SymTypes.st_remove x st) (SymTypes.st_remove x ty) (join (dlt x) (hm_ext dlt ty))).
        + assert (hm_ext dlt (SymTypes.st_remove x st) ⊑ hm_ext dlt st) as Hez. {  apply st_remove_correct. }
       apply Lat.order_trans with (y:=hm_ext dlt st); auto. 
       apply Lat.order_trans with (y:=dlt x); auto.
        + assert (hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty) as Hez. {  apply st_remove_correct. }
      apply Lat.order_trans with (y:=hm_ext dlt ty); auto.
      * congruence.
    - fold SymTypes.my_set_mem. apply ident_eqb_neq in Hax. simpl. destruct (ident_eq_dec x a) eqn:Hxa; try congruence.
    unfold SIG.subst_ident_in_type in IHty. apply IHty in H as Hih.
    destruct (SymTypes.my_set_mem x ty) eqn:Hmem; auto.
    rewrite merge_comm2. assert (hm_ext dlt ([a] ⊔ (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st)) ⊑ join (hm_ext dlt [a]) (hm_ext dlt (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st))) as Htrans. { apply hm_ext_distributive2. }
    apply order_trans with (y:=join (hm_ext dlt [a])
               (hm_ext dlt (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st))); auto.
    simpl. rewrite <- join_bottom_eq1.  apply join_least_upper_bound; auto. eapply order_trans; eauto.
  Qed.

  
  Lemma subst_inp_ident_in_constraint_correct:
    forall (c: constraint) (x: ident) (v: ST) c' st st', subst_inp_ident_in_constraint c x v st = OK (c' , st') ->
    forall dlt, constraintSatisfiable dlt c -> 
    hm_ext dlt v ⊑ dlt x ->constraintSatisfiable dlt c'.
  Proof.
    intros. unfold subst_inp_ident_in_constraint in H. destruct c eqn:Hc. destruct s0 eqn:Hs0; try (now inversion H). destruct s1 eqn:Hs1; try (now inversion H). destruct (ident_eqb x i) eqn:Hxi; try (now inversion H). unfold ret in H; inversion H.
    unfold constraintSatisfiable in *. unfold satisfiable in *.
    apply order_trans with (y:=hm_ext dlt s). eapply subst_ident_in_type_correct1; eauto. easy.
  Qed.

  Ltac monadInv :=
    simpl in *;
    unfold error in *;
    match goal with
    | H: ident_eqb _ _ = true |- _ => rewrite ident_eqb_eq in H; subst
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

  Lemma subst_ident_in_constraints_correct:
    forall (cs: list constraint) (x: ident) (v: ST) cs' st st', subst_ident_in_constraints cs x v st = OK (cs' , st') ->
      forall dlt, listSatisfiable dlt cs -> hm_ext dlt v ⊑ dlt x -> listSatisfiable dlt cs'.
  Proof. 
    induction cs; intros.
    - simpl in H. unfold ret in H. inversion H; now subst.
    - repeat monadInv. unfold listSatisfiable in *. inversion H0. apply Forall_cons.
      + apply (subst_inp_ident_in_constraint_correct a x v x0 st x1); auto.
      + now apply (IHcs x v x2 x1 st').
  Qed.

  Definition inp_replace_cond dlt (x: ident) (v: ST): Prop := hm_ext dlt v ⊑ dlt x.
  Check Forall2.
  Locate Forall2.
  Print Forall2_cons.

  (* Lemma subst_constraints_inp_map_helper: 
    forall (cs: list constraint) (xs: list ident) (vs: list ST) cs' st st' ->  *)
  (* Find the right statement here*)
  Lemma  subst_constraints_inp_map_correct:
    forall  (xs: list ident) (cs: list constraint) (vs: list ST) cs' st st', 
      subst_constraints_inp_map cs xs vs st = OK (cs',st') -> 
        forall dlt, listSatisfiable dlt cs -> Forall2 (inp_replace_cond dlt) xs vs
        -> listSatisfiable dlt cs'.
  Proof.
    induction xs as [| x xs]; intros.
    - simpl in H; destruct vs eqn:E; inversion H; now subst.
    - simpl in H. destruct vs eqn:E; inversion H.
      *  monadInv. inversion  H1. unfold inp_replace_cond in H5.
        apply (IHxs x0 l cs' x1 st'); auto. 
        eapply subst_ident_in_constraints_correct; eauto.
  Qed. 

  Lemma subst_ident_constraint_correct: forall (c: constraint) (x v: ident) (c': constraint) st st', 
      subst_ident_constraint c x v st = OK (c', st') -> forall dlt, constraintSatisfiable dlt c -> dlt x ⊑ dlt v -> constraintSatisfiable dlt c'.
  Proof.
    intros. unfold subst_ident_constraint in H. destruct (ident_eqb x v) eqn:Hxv; try inversion H.
    destruct c as [lhs x'] eqn:Hc. destruct x' as [|x'' l] eqn:Hx'; try inversion H. destruct l eqn:Hl; inversion H; clear H3 H4 H5.
    destruct (ident_eqb x x'') eqn:Hxx''; repeat monadInv; unfold satisfiable in *;
    unfold hm_ext in H0; fold hm_ext in H0; rewrite <- join_bottom_eq1 in H0.
    Admitted. 
    

  Lemma subst_constraints_out_map_correct: 
    

End SIGNATURE_PROOFS.