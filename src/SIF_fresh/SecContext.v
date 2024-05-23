From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.SimpleListTypes.


From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Open Scope list_scope.

Module Type SECMONAD (Import Ids   : IDS).

Section MySecMonad.
  Context {A : Type}.
  (* The state is current fresh number to use to generate the name 
   * and the map of currently generated type for each program var *)
  Definition sec_state : Type := (ident * Env.t ident).
  
  Definition Sec A := sec_state -> res (A * sec_state).
  Definition init_state : sec_state := (xH, Env.empty _).
  Definition initialize : ident -> Env.t ident -> sec_state := fun xi ev => (xi, ev). 
  
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
    fun '(n, sub1) =>
      let id := Ids.gensym Ids.sec n in
      OK (id, (Pos.succ n, sub1)).
  
  Definition gets : Sec sec_state :=
    fun st => OK (st, st).

  (* (*Just ignore st'. We instead have st coming *)
  Definition puts : sec_state -> Sec unit :=
    fun st => fun st' => OK (tt, st).  *)
  
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

(* To insert into the map*)
Definition insert_ctxt : ident -> ident -> Sec unit :=
  fun k v => (* Take key value*)
    fun '(n, sub1) => (* insert into the map*)
      let st:= Env.add k v sub1 in
        OK (tt, (n, st)).

Definition fresh_insert : ident -> Sec ident :=
  fun k =>
    do v <- fresh_ident; 
    do _ <- insert_ctxt k v;
    ret v.


Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Sec B).
  
  Fixpoint mmap (l: list A) {struct l} : Sec (list B) :=
    match l with
    | nil => ret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; ret (hd' :: tl')
    end.
End mmap.

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

Section option_to_sec.

  Definition option_to_sec {A: Type} (x: option A) : Sec A :=
    match x with
    | Some x' => ret x'
    | None    => error (msg "Nothing to convert")
    end.
End option_to_sec.
End SECMONAD.






Module SecMonad (Ids   : IDS) <: SECMONAD Ids.
Include SECMONAD Ids.

End SecMonad.