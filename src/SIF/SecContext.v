(** Security monad and environment operations used by the SIF generators. *)

From Velus Require Import Common.
From Velus Require Import SIF.Helpers.
From Velus Require Import Environment.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Environment.

From Coq Require Import String.
From compcert Require Import common.Errors.
From Coq Require Import List.
From Coq Require Import Sorting.Permutation.

Import List.ListNotations.

Module Type SECMONAD (Import Ids   : IDS).

Section MySecMonad.
  Context {A : Type}.

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

Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
  match Env.find x env with
  | Some x' => ret x'
  | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
  end.

Lemma find_env_consistent:
  forall x env st1 st2 st3 st4 xty xty2,
    find_env x env st1 = OK (xty, st2) ->
    find_env x env st3 = OK (xty2, st4) ->
    xty = xty2.
Proof.
  intros x env st1 st2 st3 st4 xty xty2 H1 H2.
  unfold find_env in *.
  destruct (Env.find x env) eqn:Hfind; inversion H1; inversion H2; now subst.
Qed.

Lemma find_env_of_Env_find:
  forall env x ty st,
    Env.find x env = Some ty ->
    find_env x env st = OK (ty, st).
Proof.
  intros env x ty st Hfind.
  unfold find_env. rewrite Hfind. reflexivity.
Qed.

Lemma find_env_in_scope:
  forall (A : Type) env (vars : list (ident * A)) scope x ann ty st st',
    (forall y, InMembers y vars -> exists ty, Env.find y env = Some ty /\ In ty scope) ->
    In (x, ann) vars ->
    find_env x env st = OK (ty, st') ->
    In ty scope.
Proof.
  intros A env vars scope x ann ty st st' Hvars Hin Hfind.
  unfold find_env in Hfind.
  destruct (Env.find x env) as [ty'|] eqn:Henv; try discriminate.
  inversion Hfind; subst ty st'.
  destruct (Hvars x) as (? & Hfind' & Hscope); eauto using In_InMembers.
  rewrite Henv in Hfind'. inversion Hfind'. subst. exact Hscope.
Qed.

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

(** Introduction rule for [mmap]: the counterpart of [sec_bind_inv],
    used when a successful run has to be *constructed* rather than
    inverted. *)
Lemma mmap_cons_ok:
  forall {A B: Type} (f: A -> Sec B) a l st y st' ys st'',
    f a st = OK (y, st') ->
    mmap f l st' = OK (ys, st'') ->
    mmap f (a :: l) st = OK (y :: ys, st'').
Proof.
  intros A B f a l st y st' ys st'' Hh Ht.
  simpl. unfold bind. rewrite Hh, Ht. reflexivity.
Qed.

Lemma mmap_nil_ok:
  forall {A B: Type} (f: A -> Sec B) st,
    mmap f nil st = OK (nil, st).
Proof. intros. reflexivity. Qed.

(** * Injectivity and scopedness of naming environments *)


Definition names_scoped (env: Env.t ident) (scope: list ident) (xs: list ident) : Prop :=
  forall x, In x xs -> exists ty, Env.find x env = Some ty /\ In ty scope.

Lemma names_scoped_app:
  forall env scope xs ys,
    names_scoped env scope (xs ++ ys) ->
    names_scoped env scope xs /\ names_scoped env scope ys.
Proof.
  intros env scope xs ys H.
  split; intros z Hz; apply H, in_or_app; auto.
Qed.


(** * Fresh per-key security names

    A key (an STC sub-instance, an Obc object) is given a fresh
    [sec_reset] name recorded in an environment.  Shared by the STC and
    Obc security typings, which differ only in how they walk the
    program to collect the keys. *)

Definition fresh_reset_ident : Sec ident :=
  fun n =>
    let id := Ids.gensym Ids.sec_reset n in
    OK (id, Pos.succ n).

Definition fresh_reset_insert (k: ident) (env: Env.t ident): Sec (Env.t ident * ident) :=
  if Env.mem k env then
    error (MSG "Instance declared more than once " :: [CTX k])
  else
    do v <- fresh_reset_ident;
    do e <- insert_env k v env;
    ret (e, v).


Lemma fresh_reset_insert_find_in_acc:
  forall k acc st env' sty st' x ty,
    fresh_reset_insert k acc st = OK ((env', sty), st') ->
    Env.find x env' = Some ty ->
    ty = sty \/ Env.find x acc = Some ty.
Proof.
  intros k acc st env' sty st' x ty Hins Hfind.
  unfold fresh_reset_insert in Hins.
  destruct (Env.mem k acc) eqn:Hmem; try discriminate.
  eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
  eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
  unfold fresh_reset_ident in Hfresh.
  inversion Hfresh; subst v st1.
  unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
  unfold ret in Hret. inversion Hret; subst env' sty st'.
  destruct (Pos.eq_dec x k) as [Heq|Hneq].
  - subst x. rewrite Env.gss in Hfind. inversion Hfind. auto.
  - rewrite Env.gso in Hfind; auto.
Qed.

Lemma fresh_reset_insert_find_self:
  forall k acc st env' sty st',
    fresh_reset_insert k acc st = OK ((env', sty), st') ->
    Env.find k env' = Some sty.
Proof.
  intros k acc st env' sty st' Hins.
  unfold fresh_reset_insert in Hins.
  destruct (Env.mem k acc) eqn:Hmem; try discriminate.
  eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
  eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
  unfold fresh_reset_ident in Hfresh.
  inversion Hfresh; subst v st1.
  unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
  unfold ret in Hret. inversion Hret; subst env' sty st'.
  now rewrite Env.gss.
Qed.

Lemma fresh_reset_insert_preserves_find:
  forall k acc st env' sty st' x ty,
    fresh_reset_insert k acc st = OK ((env', sty), st') ->
    Env.find x acc = Some ty ->
    Env.find x env' = Some ty.
Proof.
  intros k acc st env' sty st' x ty Hins Hfind.
  unfold fresh_reset_insert in Hins.
  destruct (Env.mem k acc) eqn:Hmem; try discriminate.
  eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
  eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
  unfold fresh_reset_ident in Hfresh.
  inversion Hfresh; subst v st1.
  unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
  unfold ret in Hret. inversion Hret; subst env' sty st'.
  assert (Hxk : x <> k).
  { intro Heq. subst x.
    assert (Env.mem k acc = true).
    { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
    congruence. }
  now rewrite Env.gso.
Qed.


(** * Ranges and injectivity of generated name environments

    Shared by the STC and Obc security typings; both allocate their
    per-instance names with the [sec_reset] prefix through
    [fresh_reset_insert]. *)



Definition env_reset_bounded (st: ident) (env: Env.t ident) : Prop :=
  forall x ty,
    Env.find x env = Some ty ->
    exists n, ty = Ids.gensym Ids.sec_reset n /\ (n < st)%positive.

Lemma fresh_reset_insert_sec_range:
  forall env k st env' sty st' x ty,
    (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
    fresh_reset_insert k env st = OK ((env', sty), st') ->
    Env.find x env' = Some ty ->
    exists n, ty = Ids.gensym Ids.sec_reset n.
Proof.
  intros env k st env' sty st' x ty Henv Hins Hfind.
  unfold fresh_reset_insert in Hins.
  destruct (Env.mem k env) eqn:Hmem; try discriminate.
  eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
  eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
  unfold fresh_reset_ident in Hfresh.
  inversion Hfresh; subst v st1.
  unfold insert_env, ret in Hins0.
  inversion Hins0; subst e st2.
  unfold ret in Hret. inversion Hret. subst env' sty st'.
  destruct (Pos.eq_dec x k) as [Heq|Hneq].
  - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
    eexists; reflexivity.
  - rewrite Env.gso in Hfind; eauto.
Qed.


Lemma env_reset_bounded_step:
  forall st env,
    env_reset_bounded st env ->
    env_reset_bounded (Pos.succ st) env.
Proof.
  intros st env Hbound x ty Hfind.
  specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
  exists n. split; auto.
  eapply Pos.lt_trans; eauto.
  apply Pos.lt_succ_diag_r.
Qed.

Lemma env_values_reset_fresh_notin:
  forall env st,
    env_reset_bounded st env ->
    ~ InMembers (Ids.gensym Ids.sec_reset st) (env_values env).
Proof.
  intros env st Hbound Hin.
  apply InMembers_In in Hin as (x & Hin).
  unfold env_values in Hin.
  apply in_map_iff in Hin as ((x', ty') & Heq & Hele).
  simpl in Heq. inversion Heq; subst x' ty'. clear Heq.
  apply Env.elements_complete in Hele.
  specialize (Hbound _ _ Hele) as (n & Hgen & Hlt).
  apply gensym_injective in Hgen as [_ Hn]. subst n.
  now apply Pos.lt_irrefl in Hlt.
Qed.

Lemma fresh_reset_insert_env_props:
  forall env k st env' sty st',
    env_reset_bounded st env ->
    NoDupMembers (env_values env) ->
    fresh_reset_insert k env st = OK ((env', sty), st') ->
    env_reset_bounded st' env'
    /\ NoDupMembers (env_values env').
Proof.
  intros env k st env' sty st' Hbound Hnodup Hgen.
  unfold fresh_reset_insert in Hgen.
  destruct (Env.mem k env) eqn:Hmem; try discriminate.
  eapply sec_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
  eapply sec_bind_inv in Hgen as (e & st2 & Hins & Hret).
  unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v st1.
  unfold insert_env, ret in Hins. inversion Hins; subst e st2.
  unfold ret in Hret. inversion Hret; subst env' sty st'.
  split.
  - intros x ty Hfind.
    destruct (ident_eq_dec x k) as [Heq|Hneq].
    + subst x. rewrite Env.gss in Hfind. inversion Hfind; subst ty.
      exists st. split; [reflexivity|apply Pos.lt_succ_diag_r].
    + rewrite Env.gso in Hfind by auto.
      specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
      exists n. split; auto.
      eapply Pos.lt_trans; eauto.
      apply Pos.lt_succ_diag_r.
  - assert (Hnotin : ~ Env.In k env).
    { intro Hin. apply Env.mem_1 in Hin. rewrite Hmem in Hin. discriminate. }
    eapply (NoDupMembers_Permutation_Proper
              (env_values (Env.add k (Ids.gensym Ids.sec_reset st) env))
              ((Ids.gensym Ids.sec_reset st, k) :: env_values env)).
    + apply env_values_add; exact Hnotin.
    + constructor.
      * apply env_values_reset_fresh_notin; exact Hbound.
      * exact Hnodup.
Qed.


Lemma mmap_find_env_scoped:
  forall env scope xs tys st st',
    (forall x, In x xs -> exists ty, Env.find x env = Some ty /\ In ty scope) ->
    mmap (fun x => find_env x env) xs st = OK (tys, st') ->
    Forall (fun ty => In ty scope) tys.
Proof.
  intros env scope xs.
  induction xs as [|x xs IH]; intros tys st st' Hscope Hmap.
  - simpl in Hmap. inversion Hmap; subst. constructor.
  - simpl in Hmap.
    eapply sec_bind_inv in Hmap as (xty & st1 & Hhd & Hmap).
    eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
    unfold find_env in Hhd.
    destruct (Env.find x env) as [xty'|] eqn:Hfind; try discriminate.
    inversion Hhd; subst xty st1.
    unfold ret in Hret. inversion Hret; subst tys st'.
    constructor.
    + destruct (Hscope x) as (? & Hfind' & Hin); [left; reflexivity|].
      rewrite Hfind in Hfind'. inversion Hfind'. subst. exact Hin.
    + eapply IH; eauto.
      intros y Hy. apply Hscope. now right.
Qed.

Fixpoint insert_vars' (xs: list ident) (acc: list ident) (env: Env.t ident): Sec (Env.t ident * list ident) :=
    (match xs with
    | nil    => ret (env, acc)
    | x::xs =>
        do (env', v) <- fresh_insert x env;
        insert_vars' xs (acc++[v]) env'
    end).

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

    Theorem left_unital_law: forall (x: A) (f: A -> Sec B) st, bind (ret x) f st = f x st.
    Proof.
      intros. unfold bind.
      destruct (ret x st) as [(a,st')|] eqn:E; rewrite ret_helper in E; now inversion E.
    Qed.

    Theorem right_unital_law: forall (m: Sec A) st, bind m ret st = m st.
    Proof.
      intros. unfold bind. now destruct (m st) as [(a & st')|] eqn:E .
    Qed.

    Theorem composition_law: forall (m: Sec A) (k: A -> Sec B) (h: B -> Sec C) st,
      bind m (fun x => bind (k x) h) st = bind (bind m k) h st.
    Proof.
      intros. unfold bind. now destruct (m st) as [(a,st')|] eqn:E.
    Qed.
  End laws.
 End MonadLaws.
