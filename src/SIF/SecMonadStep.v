(** Stepping and inverting computations in the [Sec] monad.

    Three mechanical difficulties recur in every cross-phase proof about the
    constraint generators, and this file removes two of them.  (The third is a
    design rule, not a lemma: write a generator's [match] nested -- on an
    expression list before the defined variables -- or the singleton patterns
    leave the term stuck on any equation whose variable list is not literal.)

    - *Reduction.*  A goal comparing two generators is a bind chain applied to
      a state.  [simpl] must not be used on it: it unfolds [SymTypes.merge]
      into its inner [fix] on one side only, after which two otherwise
      identical sides are no longer syntactically equal.  [bind_OK] steps one
      bind forward given what its left-hand side computes, and the tactics
      below are the common instances of that.

    - *Inversion.*  Reading back what a successful run computed means peeling
      the chain with [sec_bind_inv] and then, at each step, unfolding
      [option_to_sec] or [find_env], destructing, discriminating and
      inverting.  [option_to_sec_inv] and [find_env_inv] do that once and for
      all. *)

From Coq Require Import List.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.SecContext.

From compcert Require Import common.Errors.

Module Type SECMONADSTEP (Import Ids : IDS) (Import SC : SECMONAD Ids).

  Import SECMONADNotations.

  (** * Stepping forward *)

  Lemma bind_OK : forall {A B : Type} (m : Sec A) (f : A -> Sec B) st a st1,
      m st = OK (a, st1) -> (do x <- m; f x) st = f a st1.
  Proof. intros A B m f st a st1 H. unfold bind. now rewrite H. Qed.

  Lemma bind2_OK : forall {A1 A2 B : Type} (m : Sec (A1 * A2))
                          (f : A1 -> A2 -> Sec B) st a1 a2 st1,
      m st = OK ((a1, a2), st1) -> (do (x, y) <- m; f x y) st = f a1 a2 st1.
  Proof. intros. unfold bind2. now rewrite H. Qed.

  Lemma option_to_sec_OK : forall {A : Type} (o : option A) (a : A) st,
      o = Some a -> option_to_sec o st = OK (a, st).
  Proof. intros A o a st H. unfold option_to_sec. now rewrite H. Qed.

  Lemma find_env_OK : forall x env a st,
      Env.find x env = Some a -> find_env x env st = OK (a, st).
  Proof. intros x env a st H. unfold find_env. now rewrite H. Qed.

  (** * Inverting *)

  Lemma option_to_sec_inv : forall {A : Type} (o : option A) st a st',
      option_to_sec o st = OK (a, st') -> o = Some a /\ st' = st.
  Proof.
    intros A o st a st' H. unfold option_to_sec in H.
    destruct o; [|discriminate]. unfold ret in H. inv H. split; reflexivity.
  Qed.

  Lemma find_env_inv : forall x env st a st',
      find_env x env st = OK (a, st') -> Env.find x env = Some a /\ st' = st.
  Proof.
    intros x env st a st' H. unfold find_env in H.
    destruct (Env.find x env); [|discriminate].
    unfold ret in H. inv H. split; reflexivity.
  Qed.

  Lemma ret_inv : forall {A : Type} (a b : A) st st',
      (ret a : Sec A) st = OK (b, st') -> b = a /\ st' = st.
  Proof.
    intros A a b st st' H. unfold ret in H. inv H. split; reflexivity.
  Qed.

  (** * Tactics

      [ssec] steps a bind whose left-hand side is given by a hypothesis;
      [osec] and [fsec] step the two common lookups; [osec2] is [osec] for the
      pair-destructuring bind.  [sec_peel] inverts one step of a chain in a
      hypothesis, discharging a lookup or a [ret] and substituting the state
      it leaves unchanged. *)

  Ltac ssec H := erewrite bind_OK by exact H.
  Ltac osec H := erewrite bind_OK by (apply option_to_sec_OK; exact H).
  Ltac fsec H := erewrite bind_OK by (apply find_env_OK; exact H).
  Ltac osec2 H := erewrite bind2_OK by (apply option_to_sec_OK; exact H).

  Ltac sec_peel H :=
    first [ apply option_to_sec_inv in H as [H ?]; subst
          | apply find_env_inv in H as [H ?]; subst
          | apply ret_inv in H as [H ?]; subst ].

End SECMONADSTEP.

Module SecMonadStep (Ids : IDS) (SC : SECMONAD Ids) <: SECMONADSTEP Ids SC.
  Include SECMONADSTEP Ids SC.
End SecMonadStep.
