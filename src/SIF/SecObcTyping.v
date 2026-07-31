(** Symbolic security typing and signature generation for Obc classes
    produced by the Stc-to-Obc translation.

    The generator is a pc-carrying constraint generator over statements:
    clock types of the STC source reappear here as the security types of
    the [Ifte] conditions guarding each statement, so the pc plays the
    role that [assign_clk_type] played at the STC level.

    This file is purely syntactic: it depends on [Obc.ObcSyntax] only,
    never on the Obc semantics or on the ordinary Obc data-type system,
    mirroring how [SecSTCTyping.v] depends on clocking rather than
    semantics.  Scopedness is stated over the syntactic free names
    ([exp_free] / [stmt_free]). *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String.
From Coq Require Import PArith.
From compcert Require Import common.Errors.

From Coq Require Import List.
Import List.ListNotations.

Module Type SECOBCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SIG   : SIGNATURE Ids SC).
  Import SECMONADNotations.

  Definition hidden_class_vars (locals lasts stids: list ident) : list ident :=
    nodup ident_eq_dec (locals ++ lasts ++ stids).

  (** * Per-instance state security types

      Every object of a class receives a fresh symbolic state type.  It
      is written by [reset] calls on the instance and read as the reset
      source of [step] calls, mirroring the reset-instance types
      ([rids]) of the STC security typing. *)

  Section STATEHANDLER.

  Fixpoint generate_state_env' (objs: list (ident * ident)) (env: Env.t ident) (acc: list ident)
    : Sec (Env.t ident * list ident) :=
    match objs with
    | [] => ret (env, acc)
    | (o, _) :: objs' =>
        do (env', sty) <- fresh_reset_insert o env;
        generate_state_env' objs' env' (acc ++ [sty])
    end.

  Definition generate_state_env (objs: list (ident * ident)) : Sec (Env.t ident * list ident) :=
    generate_state_env' objs (Env.empty _) [].

  Lemma generate_state_env'_find_in_acc:
    forall objs env0 acc stids env' st st' x ty,
      (forall y ty', Env.find y env0 = Some ty' -> In ty' acc) ->
      generate_state_env' objs env0 acc st = OK ((env', stids), st') ->
      Env.find x env' = Some ty ->
      In ty stids.
  Proof.
    induction objs as [|[o cls] objs IH]; intros env0 acc stids env' st st' x ty Hacc Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. eauto.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & sty & st1 & Hstep & Hrec).
      eapply (IH acc1 (acc ++ [sty]) stids env' st1 st' x ty).
      + intros y ty' Hyfind.
        destruct (fresh_reset_insert_find_in_acc _ _ _ _ _ _ _ _ Hstep Hyfind) as [Heq|Hold].
        * subst ty'. apply in_or_app. right. simpl. auto.
        * apply in_or_app. left.
          eapply Hacc; eauto.
      + exact Hrec.
      + exact Hfind.
  Qed.

  Lemma generate_state_env_find_in:
    forall objs state_env stids st st' x ty,
      generate_state_env objs st = OK ((state_env, stids), st') ->
      Env.find x state_env = Some ty ->
      In ty stids.
  Proof.
    intros objs state_env stids st st' x ty Hgen Hfind.
    unfold generate_state_env in Hgen.
    eapply generate_state_env'_find_in_acc; eauto.
    intros y ty' Hyfind.
    rewrite Env.gempty in Hyfind. discriminate.
  Qed.

  Lemma generate_state_env'_preserves_find:
    forall objs acc stids st env' stids' st' x ty,
      generate_state_env' objs acc stids st = OK ((env', stids'), st') ->
      Env.find x acc = Some ty ->
      Env.find x env' = Some ty.
  Proof.
    induction objs as [|[o cls] objs IH]; intros acc stids st env' stids' st' x ty Hgen Hfind.
    - simpl in Hgen. inversion Hgen; subst. exact Hfind.
    - simpl in Hgen.
      eapply sec_bind2_inv in Hgen as (acc1 & sty & st1 & Hstep & Hrec).
      eapply IH; eauto.
      eapply fresh_reset_insert_preserves_find; eauto.
  Qed.

  End STATEHANDLER.

  (** * Free names of Obc expressions and statements

      Purely syntactic.  The security scopedness proofs need only that
      every name a construct reads or writes has a scoped type in the
      security environment.  We deliberately do NOT use the ordinary Obc
      data-type system ([Obc.ObcTyping]) for this: it is parameterised by
      the Obc semantics, and this file is syntax-level, mirroring
      [SecSTCTyping.v] (which uses clocking, not semantics). *)

  Fixpoint exp_free (e: exp) : list ident :=
    match e with
    | Var x _ | State x _ | Valid x _ => [x]
    | Const _ => []
    | Unop _ e' _ => exp_free e'
    | Binop _ e1 e2 _ => exp_free e1 ++ exp_free e2
    end.

  Fixpoint stmt_free (s: stmt) : list ident :=
    match s with
    | Assign x e | AssignSt x e => x :: exp_free e
    | Ifte e s1 s2 => exp_free e ++ (stmt_free s1 ++ stmt_free s2)
    | Comp s1 s2 => stmt_free s1 ++ stmt_free s2
    | Call ys _ _ _ es => ys ++ flat_map exp_free es
    | Skip => []
    end.

  (** * Expression security typing *)

  Section SECEXPTYPING.
    Variable ctxt: Env.t ident.

    Fixpoint assign_exp_type (e: exp) : option ST :=
      match e with
      | Var x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | State x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | Valid x _ =>
          match Env.find x ctxt with
          | Some ty => Some [ty]
          | None => None
          end
      | Const _ => Some []
      | Unop _ e' _ => assign_exp_type e'
      | Binop _ e1 e2 _ =>
          match assign_exp_type e1, assign_exp_type e2 with
          | Some t1, Some t2 => Some (t1 ⊔ t2)
          | _, _ => None
          end
      end.

    Lemma assign_exp_type_scoped:
      forall scope e st,
        names_scoped ctxt scope (exp_free e) ->
        assign_exp_type e = Some st ->
        st_scoped scope st.
    Proof.
      intros scope e.
      induction e as [x tyx|x tyx|c|op e IHe tye|op e1 IHe1 e2 IHe2 tye|x tyx];
        intros st Hfree Hassign; simpl in Hassign.
      - (* Var *)
        destruct (Hfree x) as (ty & Hfind & Hscope); [simpl; now left|].
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
      - (* State *)
        destruct (Hfree x) as (ty & Hfind & Hscope); [simpl; now left|].
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
      - (* Const *)
        inversion Hassign; subst st.
        intros z Hz. inversion Hz.
      - (* Unop *)
        eapply IHe; eauto.
      - (* Binop *)
        simpl in Hfree.
        destruct (names_scoped_app _ _ _ _ Hfree) as [Hf1 Hf2].
        destruct (assign_exp_type e1) as [t1|] eqn:Ht1; try discriminate.
        destruct (assign_exp_type e2) as [t2|] eqn:Ht2; try discriminate.
        inversion Hassign; subst st.
        apply st_scoped_merge; eauto.
      - (* Valid *)
        destruct (Hfree x) as (ty & Hfind & Hscope); [simpl; now left|].
        rewrite Hfind in Hassign. inversion Hassign; subst st.
        apply st_scoped_singleton. exact Hscope.
    Qed.

  End SECEXPTYPING.

  (** * Collapsing constraints with duplicated targets

      Statement-level generation can produce several constraints for the
      same target (e.g. the two branches of a compiled [merge], or a
      state type written both by the reset method and by a translated
      [TcReset]).  [collapse] joins their sources, which is
      satisfaction-equivalent and restores the one-constraint-per-target
      shape assumed by [simplify]. *)

  (** * Statement constraint generation *)

  Section SECSTMTTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident.
    Variable state_env: Env.t ident.
    Variable rst_ty: ident.

    Definition vars_env_scoped {A: Type} (vars: list (ident * A)) (scope: list ident) : Prop :=
      forall x,
        InMembers x vars ->
        exists ty, Env.find x env = Some ty /\ In ty scope.

    (** [pc] is the join of the security types of all conditions
        guarding the statement, seeded at method entry.  For step
        methods of translated classes it starts at
        [[rst_ty] ⊔ [base_ty]], so leaves reproduce the
        [([rst_ty] ⊔ ckty) ⊔ ...] sources of the STC constraints. *)

    Fixpoint generate_stmt_constraints (pc: ST) (s: stmt) : Sec (list constraint) :=
      match s with
      | Skip => ret []
      | Assign x e =>
          do ety <- option_to_sec (assign_exp_type env e);
          do xty <- find_env x env;
          ret [(((([rst_ty] ⊔ pc) ⊔ ety)), [xty])]
      | AssignSt x e =>
          do ety <- option_to_sec (assign_exp_type env e);
          do xty <- find_env x env;
          ret [(((([rst_ty] ⊔ pc) ⊔ ety)), [xty])]
      | Ifte e s1 s2 =>
          do ety <- option_to_sec (assign_exp_type env e);
          do c1 <- generate_stmt_constraints (pc ⊔ ety) s1;
          do c2 <- generate_stmt_constraints (pc ⊔ ety) s2;
          ret (c1 ++ c2)
      | Comp s1 s2 =>
          do c1 <- generate_stmt_constraints pc s1;
          do c2 <- generate_stmt_constraints pc s2;
          ret (c1 ++ c2)
      | Call [] _ o m _ =>
          if ident_eqb m Ids.reset then
            do sty <- find_env o state_env;
            ret [(([rst_ty] ⊔ pc), [sty])]
          else ret []
      | Call ys cls o m es =>
          if ident_eqb m Ids.step then
            match find_signature cls G with
            | Some n =>
                do inptyp <- mmap (fun e => option_to_sec (assign_exp_type env e)) es;
                do outtyp <- mmap (fun y => find_env y env) ys;
                do sty    <- find_env o state_env;
                generate_constraints n inptyp pc [sty] outtyp
            | None => error (MSG "Signature not found for: " :: [CTX cls])
            end
          else error (msg "Unsupported method call")
      end.

    Fixpoint stmt_state_keys (s: stmt) : list ident :=
      match s with
      | Call _ _ o _ _ => [o]
      | Comp s1 s2 => stmt_state_keys s1 ++ stmt_state_keys s2
      | Ifte _ s1 s2 => stmt_state_keys s1 ++ stmt_state_keys s2
      | _ => []
      end.

    (** The translation builds several statements as a left fold of
        [Comp acc new] (the reset method's memory initialisation and its
        instance resets).  Constraint generation for [Comp] is a plain
        concatenation, so such a fold yields the accumulator's
        constraints followed by the per-element blocks, in order. *)

    Lemma generate_fold_left_Comp:
      forall {A} (f: A -> stmt) (l: list A) acc pc cns st st',
        generate_stmt_constraints pc
          (fold_left (fun s a => Comp s (f a)) l acc) st = OK (cns, st') ->
        exists cacc blocks sa,
          generate_stmt_constraints pc acc st = OK (cacc, sa)
          /\ cns = cacc ++ List.concat blocks
          /\ Forall2 (fun a blk =>
                        exists s1 s2, generate_stmt_constraints pc (f a) s1 = OK (blk, s2))
                     l blocks.
    Proof.
      intros A f l.
      induction l as [|a l IH]; intros acc pc cns st st' Hgen.
      - simpl in Hgen.
        exists cns, [], st'. repeat split.
        + exact Hgen.
        + simpl. now rewrite app_nil_r.
        + constructor.
      - simpl in Hgen.
        destruct (IH (Comp acc (f a)) pc cns st st' Hgen)
          as (cacc & blocks & sa & Hacc & Hcns & Hall).
        simpl in Hacc.
        eapply sec_bind_inv in Hacc as (c1 & s1 & Hc1 & Hacc).
        eapply sec_bind_inv in Hacc as (c2 & s2 & Hc2 & Hret).
        unfold ret in Hret. inversion Hret; subst cacc sa.
        exists c1, (c2 :: blocks), s1. repeat split.
        + exact Hc1.
        + subst cns. simpl. now rewrite <- app_assoc.
        + constructor; [|exact Hall].
          exists s1, s2. exact Hc2.
    Qed.

    Lemma mmap_assign_exp_type_scoped:
      forall scope es tys st st',
        names_scoped env scope (flat_map exp_free es) ->
        mmap (fun e => option_to_sec (assign_exp_type env e)) es st = OK (tys, st') ->
        Forall (st_scoped scope) tys.
    Proof.
      intros scope es.
      induction es as [|e es IH]; intros tys st st' Hfree Hmap.
      - simpl in Hmap. inversion Hmap; subst. constructor.
      - simpl in Hfree.
        destruct (names_scoped_app _ _ _ _ Hfree) as [Hfe Hfes].
        simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold option_to_sec in Hhd.
        destruct (assign_exp_type env e) as [ety'|] eqn:Heq; try discriminate.
        inversion Hhd; subst ety st1.
        unfold ret in Hret. inversion Hret; subst tys st'.
        constructor.
        + eapply (assign_exp_type_scoped env scope e ety'); [exact Hfe|exact Heq].
        + eapply IH; eauto.
    Qed.

    Theorem generate_stmt_constraints_scoped_on_keys:
      forall scope s pc cns st st',
        secglobal_scoped G ->
        names_scoped env scope (stmt_free s) ->
        st_scoped scope pc ->
        In rst_ty scope ->
        (forall o sty st0 st1,
            In o (stmt_state_keys s) ->
            find_env o state_env st0 = OK (sty, st1) ->
            In sty scope) ->
        generate_stmt_constraints pc s st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros scope s.
      induction s as [x e|x e|e s1 IH1 s2 IH2|s1 IH1 s2 IH2|ys cls o m es|];
        intros pc cns st st' Hglob Hfree Hpc Hrst Hkeys Hgen.
      - (* Assign *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        simpl in Hfree.
        assert (Hfx : exists ty, Env.find x env = Some ty /\ In ty scope)
          by (apply Hfree; now left).
        assert (Hfe : names_scoped env scope (exp_free e))
          by (intros z Hz; apply Hfree; now right).
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env scope e ety'); [exact Hfe|exact Hexp']. }
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        assert (Hxscope : In xty' scope).
        { destruct Hfx as (ty & Hf & Hs).
          assert (Hteq : ty = xty') by congruence.
          subst ty. exact Hs. }
        assert (Hsrc : st_scoped scope ((([rst_ty] ⊔ pc) ⊔ ety'))).
        { apply st_scoped_merge;
            [apply st_scoped_merge;
              [apply st_scoped_singleton; exact Hrst|exact Hpc]
            |exact Hety]. }
        change (constraints_scoped scope [((([rst_ty] ⊔ pc) ⊔ ety'), [xty'])]).
        constructor; [|constructor].
        intros y Hy.
        unfold constraint_scope in Hy. cbn [fst snd] in Hy.
        apply in_app_iff in Hy.
        destruct Hy as [Hy|Hy].
        + exact (Hsrc _ Hy).
        + simpl in Hy. destruct Hy as [Heq|[]]. subst y. exact Hxscope.
      - (* AssignSt *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (xty & st2 & Hfind & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        simpl in Hfree.
        assert (Hfx : exists ty, Env.find x env = Some ty /\ In ty scope)
          by (apply Hfree; now left).
        assert (Hfe : names_scoped env scope (exp_free e))
          by (intros z Hz; apply Hfree; now right).
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env scope e ety'); [exact Hfe|exact Hexp']. }
        unfold find_env in Hfind.
        destruct (Env.find x env) as [xty'|] eqn:Hfindx; try discriminate.
        unfold ret in Hfind. inversion Hfind; subst xty st2.
        assert (Hxscope : In xty' scope).
        { destruct Hfx as (ty & Hf & Hs).
          assert (Hteq : ty = xty') by congruence.
          subst ty. exact Hs. }
        assert (Hsrc : st_scoped scope ((([rst_ty] ⊔ pc) ⊔ ety'))).
        { apply st_scoped_merge;
            [apply st_scoped_merge;
              [apply st_scoped_singleton; exact Hrst|exact Hpc]
            |exact Hety]. }
        change (constraints_scoped scope [((([rst_ty] ⊔ pc) ⊔ ety'), [xty'])]).
        constructor; [|constructor].
        intros y Hy.
        unfold constraint_scope in Hy. cbn [fst snd] in Hy.
        apply in_app_iff in Hy.
        destruct Hy as [Hy|Hy].
        + exact (Hsrc _ Hy).
        + simpl in Hy. destruct Hy as [Heq|[]]. subst y. exact Hxscope.
      - (* Ifte *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (ety & st1 & Hexp & Hgen).
        eapply sec_bind_inv in Hgen as (c1 & st2 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st3 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        simpl in Hfree.
        destruct (names_scoped_app _ _ _ _ Hfree) as [Hfe Hfs].
        destruct (names_scoped_app _ _ _ _ Hfs) as [Hf1 Hf2].
        unfold option_to_sec in Hexp.
        destruct (assign_exp_type env e) as [ety'|] eqn:Hexp'; try discriminate.
        inversion Hexp; subst ety st1.
        assert (Hety : st_scoped scope ety').
        { eapply (assign_exp_type_scoped env scope e ety'); [exact Hfe|exact Hexp']. }
        assert (Hpc' : st_scoped scope (pc ⊔ ety')).
        { apply st_scoped_merge; assumption. }
        apply Forall_app. split.
        + eapply (IH1 (pc ⊔ ety') c1 st st2);
            [exact Hglob|exact Hf1|exact Hpc'|exact Hrst| |exact Hgen1].
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now left.
        + eapply (IH2 (pc ⊔ ety') c2 st2 st3);
            [exact Hglob|exact Hf2|exact Hpc'|exact Hrst| |exact Hgen2].
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now right.
      - (* Comp *)
        simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c1 & st1 & Hgen1 & Hgen).
        eapply sec_bind_inv in Hgen as (c2 & st2 & Hgen2 & Hret).
        unfold ret in Hret. inversion Hret; subst cns st'.
        simpl in Hfree.
        destruct (names_scoped_app _ _ _ _ Hfree) as [Hf1 Hf2].
        apply Forall_app. split.
        + eapply (IH1 pc c1 st st1);
            [exact Hglob|exact Hf1|exact Hpc|exact Hrst| |exact Hgen1].
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now left.
        + eapply (IH2 pc c2 st1 st2);
            [exact Hglob|exact Hf2|exact Hpc|exact Hrst| |exact Hgen2].
          intros o' sty st0 st1' Hin Hfind.
          eapply Hkeys; eauto.
          simpl. apply in_or_app. now right.
      - (* Call *)
        simpl in Hfree.
        destruct (names_scoped_app _ _ _ _ Hfree) as [Hfys Hfes].
        destruct ys as [|y ys'].
        + simpl in Hgen.
          destruct (ident_eqb m Ids.reset) eqn:Hreset.
          * eapply sec_bind_inv in Hgen as (sty & st1 & Hfind & Hret).
            unfold ret in Hret. inversion Hret; subst cns st'.
            assert (Hsrc : st_scoped scope ([rst_ty] ⊔ pc)).
            { apply st_scoped_merge;
                [apply st_scoped_singleton; exact Hrst|exact Hpc]. }
            change (constraints_scoped scope [(([rst_ty] ⊔ pc), [sty])]).
            constructor; [|constructor].
            intros z Hz.
            unfold constraint_scope in Hz. cbn [fst snd] in Hz.
            apply in_app_iff in Hz.
            destruct Hz as [Hz|Hz].
            -- exact (Hsrc _ Hz).
            -- simpl in Hz. destruct Hz as [Heq|[]]. subst z.
               eapply Hkeys; eauto.
               simpl. now left.
          * unfold ret in Hgen. inversion Hgen; subst. constructor.
        + simpl in Hgen.
          destruct (ident_eqb m Ids.step) eqn:Hstep; try discriminate.
          destruct (find_signature cls G) as [sig|] eqn:Hfindsig; try discriminate.
          eapply sec_bind_inv in Hgen as (inptyp & st1 & Hinp & Hgen).
          eapply sec_bind_inv in Hgen as (outtyp & st2 & Hout & Hgen).
          eapply sec_bind_inv in Hgen as (sty & st3 & Hsty & Hgen).
          assert (HinpScope : Forall (st_scoped scope) inptyp).
          { eapply (mmap_assign_exp_type_scoped scope es inptyp st st1);
              [exact Hfes|exact Hinp]. }
          assert (HoutScope : Forall (fun x => In x scope) outtyp).
          { eapply (SC.mmap_find_env_scoped env scope (y :: ys') outtyp st1 st2);
              [exact Hfys|exact Hout]. }
          assert (Hstyscope : In sty scope).
          { eapply Hkeys; eauto.
            simpl. now left. }
          eapply (generate_constraints_scoped sig scope inptyp pc [sty] outtyp cns st3 st');
            [eapply Hglob; eauto
            |exact HinpScope
            |exact Hpc
            |apply st_scoped_singleton; exact Hstyscope
            |exact HoutScope
            |exact Hgen].
      - (* Skip *)
        simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst. constructor.
    Qed.

    Corollary generate_stmt_constraints_scoped:
      forall scope s pc cns st st',
        secglobal_scoped G ->
        names_scoped env scope (stmt_free s) ->
        st_scoped scope pc ->
        In rst_ty scope ->
        (forall o sty st0 st1,
            find_env o state_env st0 = OK (sty, st1) ->
            In sty scope) ->
        generate_stmt_constraints pc s st = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros scope s pc cns st st' Hglob Hfree Hpc Hrst Hkeys Hgen.
      eapply (generate_stmt_constraints_scoped_on_keys scope s pc cns st st');
        [exact Hglob|exact Hfree|exact Hpc|exact Hrst| |exact Hgen].
      intros o sty st0 st1 Hin Hfind.
      eapply Hkeys; eauto.
    Qed.

  End SECSTMTTYPING.

  (** * Class signature generation *)

  Section SECCLSTYPING.
    Variable G: secglobal.

    Definition generate_class_signature (c: class) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match (do (clk_id, rst_id) <- option_to_sec (get_node_aux (c.(c_name)) aux_names);
             do clk_type <- option_to_sec (Env.find clk_id env);
             do rst_type <- option_to_sec (Env.find rst_id env);
             do stepm  <- option_to_sec (find_method Ids.step c.(c_methods));
             do resetm <- option_to_sec (find_method Ids.reset c.(c_methods));
             do inp    <- option_to_sec (get_mappings_from_node stepm.(m_in) env);
             do out    <- option_to_sec (get_mappings_from_node stepm.(m_out) env);
             do locals <- option_to_sec (get_mappings_from_node stepm.(m_vars) env);
             do lasts  <- option_to_sec (get_mappings_from_node c.(c_mems) env);
             do (state_env, stids) <- generate_state_env c.(c_objs);
             do craw_step <- generate_stmt_constraints G env state_env rst_type
                              [clk_type] stepm.(m_body);
             do craw_reset <- generate_stmt_constraints G env state_env rst_type
                              [] resetm.(m_body);
             ret (inp, out, rst_type, clk_type,
                  simplify (collapse (craw_step ++ craw_reset))
                           (hidden_class_vars locals lasts stids), env)) init_state with
      | Error e => Error e
      | OK ((inp, out, rst_id, ck_id, constraints, env), _) =>
          OK {| s_name  := c.(c_name);
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints |}
      end.

    Definition generate_class_signature_scoped_env
      (c: class) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res signature :=
      match find_node_env c.(c_name) envs with
      | None =>
          Error (MSG "Missing class-local security environment" :: [CTX c.(c_name)])
      | Some env =>
          generate_class_signature c env aux_names
      end.

  End SECCLSTYPING.

  (** * Program-level signature generation *)

  Section SECOBCPROGRAMTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_class_signatures' (acc: list signature) (p: program)
             (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match p with
      | [] => OK acc
      | c :: cs =>
          do sig <- generate_class_signature acc c env aux_names;
          generate_all_class_signatures' (sig :: acc) cs env aux_names
      end.

    Definition generate_all_class_signatures (p: program) (env: Env.t ident)
               (aux_names: list node_aux_names) : res (list signature) :=
      generate_all_class_signatures' [] p env aux_names.

    Fixpoint generate_all_class_signatures_scoped_env'
      (acc: list signature) (p: program) (envs: node_scoped_env)
      (aux_names: list node_aux_names) : res (list signature) :=
      match p with
      | [] => OK acc
      | c :: cs =>
          do sig <- generate_class_signature_scoped_env acc c envs aux_names;
          generate_all_class_signatures_scoped_env' (sig :: acc) cs envs aux_names
      end.

    Definition generate_all_class_signatures_scoped_env
      (p: program) (envs: node_scoped_env) (aux_names: list node_aux_names)
      : res (list signature) :=
      generate_all_class_signatures_scoped_env' [] p envs aux_names.

  End SECOBCPROGRAMTYPING.

End SECOBCTYPING.

Module SecObcTyping
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import SIG   : SIGNATURE Ids SC)
  <: SECOBCTYPING Ids Op OpAux SC SynObc SIG.

Include SECOBCTYPING Ids Op OpAux SC SynObc SIG.

End SecObcTyping.
