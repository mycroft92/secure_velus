From Coq Require Import List.
From Coq Require Import Lists.ListSet.
(*From Coq Require Import Logic.Classical_Prop.*)
From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Coq Require Import Lia.

Import ListNotations.
From Coq Require Import Recdef.
(* Require Import Coq.Program.Equality. *)
(*Decoupling the symbolic types from the lattice in this module*)

Inductive nonCanonST : Type :=
| Bot  : nonCanonST
| Var  : ident -> nonCanonST
| Lub  : nonCanonST -> nonCanonST  -> nonCanonST
| Ref  : nonCanonST -> uConstraint -> nonCanonST
with uConstraint: Type := 
| CNil : uConstraint
| Cns  : (nonCanonST * nonCanonST) -> uConstraint -> uConstraint.

Definition ST := list ident.
Definition constraint := (ST*ST)%type.

Definition wf_constraint (c: constraint): Prop :=  
  match c with
  | (s1,s2) => (List.length s2 = 1) /\ sortedNoDup s1
  end.


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
          destruct H as [H1|H2]. elim (E H1). (*a0 = a*)
          now apply IHst.
Qed.
  (*for now this is just a plain append*)
Fixpoint gatherCns (c1 c2:uConstraint): uConstraint:=
  match c1 with
  | CNil => c2
  | Cns x c1' => Cns x (gatherCns c1' c2)
  end.

Inductive EqNL : nonCanonST -> nonCanonST -> Prop :=
| refl_case: forall α, EqNL  α α
| lub_assoc: forall α β θ, EqNL (Lub (Lub α β) θ) (Lub α (Lub β θ))
| lub_var_refl : forall α, EqNL (Lub (Var α) (Var α)) (Var α)
| ref_base : forall α, EqNL (Ref α CNil) α
| ref_lub  : forall α_1 α_2 ρ_1 ρ_2, 
   EqNL (Lub (Ref α_1 ρ_1) (Ref α_2 ρ_2)) (Ref (Lub α_1 α_2) (gatherCns ρ_1 ρ_2))
| ref_ref  : forall α ρ_1 ρ_2, EqNL (Ref (Ref α ρ_1) ρ_2) (Ref α (gatherCns ρ_1 ρ_2))
(* | ref_lub_assocl: forall α_1 α_2 ρ, 
            EqNL (Lub (Ref α_1 ρ) (Var α_2)) (Ref (Lub α_1 α_2) ρ)
| ref_lub_assocr: forall α_1 α_2 ρ, 
            EqNL (Lub (Var α_1) (Ref α_2 ρ) ) (Ref (Lub α_1 α_2) ρ) *)
| ref_lub_assocl: forall α_1 α_2 ρ, 
            EqNL (Lub α_1 (Ref α_2 ρ) ) (Ref (Lub α_1 α_2) ρ)
| ref_lub_assocr: forall α_1 α_2 ρ, 
            EqNL (Lub (Ref α_1 ρ) α_2) (Ref (Lub α_1 α_2) ρ).

    
(*Cool trick on decreasing arguments*)
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

    (* The proofs are horrible, need to tidy them up*)
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
          
   


    Hint Constructors EqNL.
    (* Lemma StrongConfluence: forall α_1 α_2, EqNL α_1 α_2 -> canon α_1 = canon α_2.
    Proof.
      induction 1; auto.
      - simpl. destruct (canon α) eqn:E1. destruct (canon β) eqn:E2. destruct (canon θ) eqn:E3.
        now rewrite merge_assoc, app_assoc.
      (*set the append correctly*)
      - simpl. destruct (canon α) eqn:E1. rewrite merge_refl. *)
          
        
        
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
Qed.


(*needs a precondition that c1 and c2 are sorted*)
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
  
(*canonical type specification and correctness to be proved*)

(*Need to write a new append for flat constraints like merge*)
Fixpoint canon (x:nonCanonST): (ST*(list constraint)) :=
  match x with
  | Bot   => ([],[])
  | Var i => ([i],[])
  | Lub α_1 α_2 => 
      let (st1,ρ_1):= canon α_1 in
      let (st2,ρ_2):= canon α_2 in
      (merge st1 st2, ρ_1 ++ ρ_2)
  | Ref i ρ => 
      let (st, ρ') := canon i in
      let ρ'' := unfurl ρ in 
      (st, ρ''++ρ') (* I need to change this to ordering append but this works for now*)
  end 
with unfurl (ρ: uConstraint): list constraint :=
  match ρ with
  | CNil => []
  | Cns (α_1,α_2) ρ' => 
      let (α_1', ρ_1) := canon α_1 in
      let (α_2', ρ_2) := canon α_2 in
      let ρ'' := unfurl ρ' in
      (α_1',α_2') :: ρ_1 ++ ρ_2 ++ ρ'' (* I need to change this to ordering append but this works for now*)
  end.
  

Lemma cannon_sortedNoDup: forall x, 
              match canon x with
              | (α,_) => sortedNoDup α
              end .
Proof.
  induction x as [|? | α_1 IH1 α_2 IH2| α ρ IH]; simpl; auto.
    - destruct (canon α_1). destruct (canon α_2). apply sortedNoDup_merge; auto.
    - destruct (canon α). auto.
Qed.


Notation "x ⊔ y" := (merge x y) (at level 40, left associativity).
Definition st_remove := List.remove ident_eq_dec.
Definition st_mem    := my_set_mem.


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

(*Substitute an ident d in st wtih st'*)
Definition subST st d st' : ST := 
  match st_mem  d st with
  | false => st
  | true  => if st_mem d st' then (st_remove d st) ⊔ (st_remove d st') else (st_remove d st) ⊔ st'
  end. 


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

Fixpoint simplify (cns: list constraint) (ds: list ident) : list constraint :=
  match ds with 
  | []    => cns
  | d::ds' => match findST cns d with
             | None    => simplify cns ds'
             | Some st => simplify (subAll cns d st) ds'
             end
  end.

(*
Items that I don't know how to do or have issues with:
1. Constraint sorting is needlessly convoluted and is harder to get right
2. Setting up correspondence between signatures of Lustre and Lustre via Fresh Monad
3. Why is this complicated for such simple math on paper
*)


(*Plan of action
1. Implement the full typing for Lustre and NLustre to dump constraints?? without the correctness
2.  

*)
