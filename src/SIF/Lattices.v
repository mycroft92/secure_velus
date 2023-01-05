(*******************************************************************)
(* Lattices properties only                                        *)
(* Idea is to have an actual lattice inherit from this module type *)
(* Proofs only need the results from here                          *)
(*******************************************************************)


(*Adapted from David Picharde's work*)

Require Export List.
Require Inclusion.
Require Inverse_Image.


Module Type Lattice.


Parameter t : Set.
(*Probably I can replace these with the Eq typeclass, will be much simpler*)
Parameter eq : t -> t -> Prop.
Parameter eqb : t -> t -> bool.
Parameter eq_refl : forall x : t, eq x x.
Parameter eqb_refl : forall x y, eqb x y = true <-> eq x y.
Parameter eq_no_red: forall x y, eq x y <-> x = y.
(*This is needed for proof in cexp.*)
Parameter eq_sym : forall x y : t, eq x y -> eq y x.  
Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Parameter eq_dec : forall x y : t, {eq x y}+{~ eq x y}.

Parameter order : t -> t -> Prop.
Parameter order_refl : forall x y : t, eq x y -> order x y.
Parameter order_antisym : forall x y : t, order x y -> order y x -> eq x y.
Parameter order_trans : forall x y z : t, order x y -> order y z -> order x z.
Parameter order_dec : forall x y : t, {order x y}+{~ order x y}.

Parameter join : t -> t -> t.
Parameter join_bound1 : forall x y : t, order x (join x y).
Parameter join_bound2 : forall x y : t, order y (join x y).
Parameter join_least_upper_bound : forall x y z : t, order x z -> order y z -> order (join x y) z.

Parameter meet : t -> t -> t.
Parameter meet_bound1 : forall x y : t, order (meet x y) x.
Parameter meet_bound2 : forall x y : t, order (meet x y) y.
Parameter meet_greatest_lower_bound : forall x y z : t, order z x -> order z y -> order z (meet x y).

Parameter bottom : t.
Parameter bottom_is_bottom : forall x : t, order bottom x.
Parameter top : t.
Parameter top_is_top : forall x : t, order x top.

Notation "x ⊑ y" := (order x y) (at level 40, left associativity).

 Hint Immediate eq_sym.
 Hint Resolve eq_refl eq_trans eqb_refl
             order_refl order_antisym order_trans
             join_bound1 join_bound2 join_least_upper_bound
             meet_bound1 meet_bound2 meet_greatest_lower_bound
             bottom_is_bottom top_is_top.


  Lemma join_upper_bound_l : forall x y z, order (join x y) z -> order x z.
  Proof.
    intros. apply order_trans with (y:=(join x y)). auto. assumption.
  Qed.

  Lemma join_upper_bound_r : forall x y z, order (join x y) z -> order y z.
  Proof.
    intros. apply order_trans with (y:=(join x y)). auto. assumption.
  Qed.

  Lemma eq_leibiniz : forall x y, x = y -> eq x y.
  Proof.
    intros. rewrite H. apply eq_refl.
  Qed.

  Lemma meet_monotone : forall x1 x2 y1 y2,
    order x1 x2 -> order y1 y2 -> order (meet x1 y1) (meet x2 y2).
  Proof.
    eauto.
  Qed.

  Lemma join_monotone : forall x1 x2 y1 y2,
    order x1 x2 -> order y1 y2 -> order (join x1 y1) (join x2 y2).
  Proof.
    eauto.
  Qed.

  Lemma order_eq_order :
   forall x y z : t, order x y -> eq y z -> order x z.
  Proof.
    eauto.
  Qed.

  Lemma eq_order_order :
   forall x y z : t, eq x y -> order y z -> order x z.
  Proof.
    intros x y z H H1; apply order_trans with y; auto.
  Qed.

  Lemma meet_sym : forall x y :t, eq (meet x y) (meet y x).
    auto.
  Qed.

  Lemma join_sym : forall x y :t, eq (join x y) (join y x).
    auto.
  Qed.

  Lemma meet_assoc : forall x y z, eq (meet x (meet y z)) (meet (meet x y) z).
  Proof.
    intros; apply order_antisym; apply meet_greatest_lower_bound.
    apply meet_greatest_lower_bound; auto.
    apply order_trans with (meet y z); auto.
    apply order_trans with (meet y z); auto.
    apply order_trans with (meet x y); auto.
    apply meet_greatest_lower_bound; auto.
    apply order_trans with (meet x y); auto.
  Qed.

  Lemma join_assoc : forall x y z, eq (join x (join y z)) (join (join x y) z).
  Proof.
    intros; apply order_antisym; apply join_least_upper_bound.
    apply order_trans with (join x y); auto.
    apply join_least_upper_bound; auto.
    apply order_trans with (join x y); auto.
    apply join_least_upper_bound; auto.
    apply order_trans with (join y z); auto.
    apply order_trans with (join y z); auto.
  Qed.

  Lemma meet_eq1 :
    forall x y z, eq x y -> eq (meet x z) (meet y z).
  Proof.
    intros; apply order_antisym.
    apply meet_greatest_lower_bound; auto.
    apply order_eq_order with x; auto.
    apply meet_greatest_lower_bound; auto.
    apply order_eq_order with y; auto.
  Qed.

  Lemma join_eq1 :
    forall x y z, eq x y -> eq (join x z) (join y z).
  Proof.
    intros; apply order_antisym.
    apply join_least_upper_bound; auto.
    apply eq_order_order with y; auto.
    apply join_least_upper_bound; auto.
    apply eq_order_order with x; auto.
  Qed.

  Lemma meet_eq2 :
    forall x y z, eq y z -> eq (meet x z) (meet x y).
  Proof.
    intros; apply order_antisym.
    apply meet_greatest_lower_bound; auto.
    apply order_eq_order with z; auto.
    apply meet_greatest_lower_bound; auto.
    apply order_eq_order with y; auto.
  Qed.

  Lemma join_eq2 :
    forall x y z : t, eq y z -> eq (join x z) (join x y).
  Proof.
    intros; apply order_antisym.
    apply join_least_upper_bound; auto.
    apply eq_order_order with y; auto.
    apply join_least_upper_bound; auto.
    apply eq_order_order with z; auto.
  Qed.

  Lemma meet_bottom1 : forall x : t, eq bottom (meet bottom x).
  Proof.
    intros; apply order_antisym ;auto.
  Qed.

  Lemma join_bottom1 : forall x : t, eq x (join bottom x).
  Proof.
    intros; apply order_antisym; auto.
  Qed.

  Lemma join_bottom1b : forall x : t, eqb x (join bottom x) = true.
  Proof.
    intros; apply eqb_refl; apply order_antisym; auto.
  Qed.

  Lemma meet_bottom2 : forall x : t, eq bottom (meet x bottom).
  Proof.
    intros; apply order_antisym; auto.
  Qed.

  Lemma join_bottom2 : forall x : t, eq x (join x bottom).
  Proof.
    intros; apply order_antisym; auto.
  Qed.

  Lemma join_bottom_eq1 : forall x : t,  x = (join x bottom).
  Proof.
    intros; apply eq_no_red; apply order_antisym; auto.
  Qed.

  Lemma join_bottom_eq2 : forall x : t,  x = (join bottom x).
  Proof.
    intros; apply eq_no_red; apply order_antisym; auto.
  Qed.

  Fixpoint join_list (l : list t) : t :=
    match l with
    | nil => bottom
    | a :: q => join a (join_list q)
    end.

  Lemma join_list_greater :
   forall (l : list t) (x : t), In x l -> order x (join_list l).
  Proof.
    induction l; simpl in |- *; intuition.
    subst; auto.
    apply order_trans with (join_list l); auto.
  Qed.

  Lemma join_list_least_greater :
   forall (l : list t) (z : t),
   (forall x : t, In x l -> order x z) -> order (join_list l) z.
  Proof.
    induction l; simpl in |- *; intuition.
  Qed.

  Inductive list_order : list t -> list t -> Prop :=
    | list_order_nil : list_order nil nil
    | list_order_cons :
        forall (x1 x2 : t) (l1 l2 : list t),
        order x1 x2 -> list_order l1 l2 -> list_order (x1 :: l1) (x2 :: l2).

  Lemma list_order_join_list :
   forall l1 l2 : list t,
   list_order l1 l2 -> order (join_list l1) (join_list l2).
  Proof.
    induction 1; simpl in |- *; auto.
    apply join_least_upper_bound.
    apply order_trans with x2; auto.
    apply order_trans with (join_list l2); auto.
  Qed.

  Hint Resolve join_bottom1 join_bottom2 join_list_greater join_bottom_eq1 join_bottom_eq2
    join_list_least_greater.


End Lattice.
