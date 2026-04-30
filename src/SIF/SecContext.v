From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Environment.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.
From Coq Require Import List.


Import List.ListNotations.

Module Type SECMONAD (Import Ids   : IDS).

Section MySecMonad.
  Context {A : Type}.
  (* The state only tracks the next fresh index. The shared typing context is
     threaded explicitly through the generators that use this monad. *)
  Definition sec_state : Type := ident.
  Definition Sec A := sec_state -> res (A * sec_state).
  Definition init_state : sec_state := xH.
  Definition initialize : ident -> sec_state := fun xi  => xi.
  
  Definition ret (x : A) : Sec A := fun st => OK (x, st).
  
  Definition bind {B : Type} (x : Sec A) (f : A -> Sec B) : Sec B :=
    fun st => match (x st) with
          | OK (a, st') => f a st'
          | Error err => Error err
          end.
  
  Definition bind2 {A1 A2 B : Type} (x : Sec (A1 * A2)) (f : A1 -> A2 -> Sec B) : Sec B :=
    fun st => match (x st) with
          | OK ((a1, a2), st') => f a1 a2 st'
          | Error err => Error err
          end.
  
  Definition error (msg : errmsg) : Sec A :=
    fun st => Error msg.
  
  Definition fresh_ident : Sec ident :=
    fun n =>
      let id := Ids.gensym Ids.sec n in
      OK (id, Pos.succ n).
  
  Definition gets : Sec sec_state :=
    fun st => OK (st, st).

  Lemma sec_bind_inv {B} : forall (x : Sec A) (f : A -> Sec B) res st,
      (bind x f) st = OK res ->
      exists y st'',
        x st = OK (y, st'') /\ f y st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind in Hbind.
    destruct (x st) as [[y st'']|]; eauto. inv Hbind.
  Qed.

  Lemma sec_bind2_inv {A1 A2 B} : forall (x : Sec (A1 * A2)) (f : A1 -> A2 -> Sec B) res st,
      (bind2 x f) st = OK res ->
      exists y1 y2 st'',
        x st = OK ((y1, y2), st'') /\ f y1 y2 st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind2 in Hbind.
    destruct (x st) as [[[y1 y2] st'']|]; eauto. inv Hbind.
  Qed.

End MySecMonad.

Module SECMONADNotations.
    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X ident, A at level 100, B at level 200).
        
    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200).
        
End SECMONADNotations.
Import SECMONADNotations.


(* Extend the context with one fresh security variable. *)
Definition insert_env (k v: ident) (env: Env.t ident): Sec (Env.t ident) :=
  let st:= Env.add k v env in
    ret st.

Definition fresh_insert (k: ident) (env: Env.t ident): Sec (Env.t ident*ident) :=
  if Env.mem k env then
   error (MSG "Key declared more than once ":: [CTX k])
  else
    do v <- fresh_ident; 
    do e <- insert_env k v env;
    ret (e, v).

Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Sec B).
  
  Fixpoint mmap (l: list A) {struct l} : Sec (list B) :=
    match l with
    | nil => ret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; ret (hd' :: tl')
    end.
End mmap.

Fixpoint insert_vars' (xs: list ident) (acc: list ident) (env: Env.t ident): Sec (Env.t ident * list ident) :=
    (match xs with
    | nil    => ret (env, acc)
    | x::xs => 
        do (env', v) <- fresh_insert x env;
        insert_vars' xs (acc++[v]) env'
    end).
(** Inserts mappings for xs into env, returns newly generated mappings in order and the env*)
Definition insert_vars xs env := insert_vars' xs [] env.
Section mmap2.
  Context {A B1 B2 : Type}.
  Variable (f : A -> Sec (B1 * B2)).

  
  
  Fixpoint mmap2 (l: list A) {struct l} : Sec (list B1 * list B2) :=
    match l with
    | nil => ret (nil, nil)
    | hd :: tl => do (hd1, hd2) <- f hd;
                 do (tl1, tl2) <- mmap2 tl;
                 ret ((hd1::tl1), (hd2::tl2))
    end.
End mmap2.

Section zipper.
  Context  {A1 A2 B: Type}.
  (* Variable (f: A1 -> A2 -> B). *)
  Import List.ListNotations.
  Fixpoint zip (l1: list A1) (l2: list A2) : Sec (list (A1*A2)) :=
    match l1,l2 with
    | [], [] => ret []
    | _ , [] => error (msg "too many elements in l1")
    | [], _  => error (msg "too many elements in l2")
    | x1::l1', x2::l2' =>
        do ls <- zip l1' l2';
        ret ((x1,x2)::ls )
    end.
End zipper.

Section option_to_sec.

  Definition option_to_sec {A: Type} (x: option A) : Sec A :=
    match x with
    | Some x' => ret x'
    | None    => error (msg "Nothing to convert")
    end.
End option_to_sec.

(* Generic monadic determinism facts used throughout the SIF development.
   They do not depend on any specific source/target language, only on the
   state/error structure of the security monad. *)
Lemma option_to_sec_consistent:
  forall (A: Type) (x: option A) st1 st2 y1 y2 st1' st2',
    @option_to_sec A x st1 = OK (y1, st1') ->
    @option_to_sec A x st2 = OK (y2, st2') ->
    y1 = y2.
Proof.
  intros A [a|] st1 st2 y1 y2 st1' st2' H1 H2;
    unfold option_to_sec in *; inversion H1; inversion H2; now subst.
Qed.

Lemma mmap_consistent:
  forall (A B: Type) (f g: A -> Sec B) xs st1 st2 ys1 ys2 st1' st2',
    (forall x s1 s2 y1 y2 s1'' s2'',
        f x s1 = OK (y1, s1'') ->
        g x s2 = OK (y2, s2'') ->
        y1 = y2) ->
    mmap f xs st1 = OK (ys1, st1') ->
    mmap g xs st2 = OK (ys2, st2') ->
    ys1 = ys2.
Proof.
  intros A B f g xs.
  induction xs as [|x xs IH]; intros st1 st2 ys1 ys2 st1' st2' Hfg Hm1 Hm2.
  - simpl in Hm1, Hm2. inversion Hm1; inversion Hm2. reflexivity.
  - simpl in Hm1, Hm2.
    eapply sec_bind_inv in Hm1 as [hd1 [st_mid1 [Hhd1 Hm1]]].
    eapply sec_bind_inv in Hm1 as [tl1 [st_fin1 [Htl1 Hret1]]].
    unfold ret in Hret1. inversion Hret1. subst ys1 st1'.
    eapply sec_bind_inv in Hm2 as [hd2 [st_mid2 [Hhd2 Hm2]]].
    eapply sec_bind_inv in Hm2 as [tl2 [st_fin2 [Htl2 Hret2]]].
    unfold ret in Hret2. inversion Hret2. subst ys2 st2'.
    f_equal.
    + eapply Hfg; eauto.
    + eapply IH; eauto.
Qed.

Lemma mmap_option_to_sec_consistent:
  forall (A B: Type) (f: A -> option B) xs st1 st2 ys1 ys2 st1' st2',
    mmap (fun x => option_to_sec (f x)) xs st1 = OK (ys1, st1') ->
    mmap (fun x => option_to_sec (f x)) xs st2 = OK (ys2, st2') ->
    ys1 = ys2.
Proof.
  intros.
  eapply (@mmap_consistent A B (fun x => option_to_sec (f x)) (fun x => option_to_sec (f x)) xs).
  - intros. eapply option_to_sec_consistent; eauto.
  - exact H.
  - exact H0.
Qed.

End SECMONAD.



Module SecMonad (Ids   : IDS) <: SECMONAD Ids.
Include SECMONAD Ids.

End SecMonad.


Module MonadLaws (Ids  : IDS)
  (SC: SECMONAD Ids).
  Import SC.

  
  Section laws.
    Variable A B C: Type.
    Lemma ret_helper: forall (x:A) st, ret x st = OK (x,st).
    Proof.
      easy.
    Qed.

    (* return a >>= k                  =  k a *)
    Theorem left_unital_law: forall (x: A) (f: A -> Sec B) st, bind (ret x) f st = f x st.  
    Proof.
      intros. unfold bind. 
      destruct (ret x st) as [(a,st')|] eqn:E; rewrite ret_helper in E; now inversion E.
    Qed.

    (*m        >>= return             =  m*)
    Theorem right_unital_law: forall (m: Sec A) st, bind m ret st = m st.
    Proof.
      intros. unfold bind. now destruct (m st) as [(a & st')|] eqn:E . 
    Qed.

    (* m        >>= (\x -> k x >>= h)  =  (m >>= k) >>= h *)
    Theorem composition_law: forall (m: Sec A) (k: A -> Sec B) (h: B -> Sec C) st,
      bind m (fun x => bind (k x) h) st = bind (bind m k) h st.
    Proof.
      intros. unfold bind. now destruct (m st) as [(a,st')|] eqn:E.
    Qed.
  End laws.
 End MonadLaws.
