(*** Translation preservation from NLustre typing constraints to STC typing constraints.

     This file proves a deliberately weak preservation statement.

     - We do not require the NLustre and STC valuations to coincide everywhere.
     - We only require agreement on a chosen list of shared variables.
     - STC is allowed to introduce additional auxiliary variables, in particular
       reset-instance variables created during the STC translation.

     The proof is organised in three layers:

     1. [eqn_preserv]: one NLustre equation versus the STC constraints produced
        by [translate_eqn].
     2. [eqns_preserv]: extension to a list of equations, using the fact that
        both typing functions concatenate constraint lists.
     3. [node_preserv]: instantiation of the list-level theorem for a translated
        node/system pair, with the scope chosen to be the interface variables,
        locals, clock type, and reset type. *)
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.

Module Type SECNLUSSTCTRANSLATION 
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import SecTypes : SECTYPES Lat)
  (Import CESyn    : CESYNTAX      Op)
  (Import SynNL    : NLSYNTAX  Ids Op CESyn)
  (Import SynStc   : STCSYNTAX Ids Op CESyn)
  (Import Mem      : MEMORIES  Ids Op CESyn SynNL)
  (Import Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (Import SIG          : SIGNATURE   Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING  : SECCETYPING Ids Op CESyn)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING).
  (** In this section we relate the constraint generator for one NLustre
      equation with the constraint generator for the STC constraints obtained
      by translation. *)
  Section SECEQNPRES.

    (** The monadic state only threads a fresh-name counter. The helper lemmas
        below record that environment lookups and option lifts return the same
        semantic result independently of that state. They are used to align the
        intermediate values computed on the NLustre and STC sides before
        applying the abstract call-preservation hypothesis. *)
    Lemma find_env_consistent: forall x env st1 st2 st3 st4 xty xty2, 
      find_env x env st1 = OK (xty, st2) ->
      find_env x env st3 = OK (xty2, st4) -> xty = xty2.
    Proof.
      intros. unfold find_env in *.
      destruct (Env.find x env) eqn:findx1; inversion H; inversion H0.
      now subst.
    Qed.

    Lemma find_env_consistent_nl_stc:
      forall x env st1 st2 st3 st4 xty xty2,
        SECNLUSTYPING.find_env x env st1 = OK (xty, st2) ->
        SECSTCTYPING.find_env x env st3 = OK (xty2, st4) ->
        xty = xty2.
    Proof.
      intros. unfold SECNLUSTYPING.find_env, SECSTCTYPING.find_env in *.
      destruct (Env.find x env) eqn:Hfind; inversion H; inversion H0.
      now subst.
    Qed.

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

    Lemma mmap_find_env_consistent_nl_stc:
      forall xs env st1 st2 ys1 ys2 st1' st2',
        mmap (fun x => SECNLUSTYPING.find_env x env) xs st1 = OK (ys1, st1') ->
        mmap (fun x => find_env x env) xs st2 = OK (ys2, st2') ->
        ys1 = ys2.
    Proof.
      intros.
      eapply (@mmap_consistent ident ident (fun x => SECNLUSTYPING.find_env x env) (fun x => find_env x env) xs).
      - intros. eapply find_env_consistent_nl_stc; eauto.
      - exact H.
      - exact H0.
    Qed.

    (** [agree_on xs dlt1 dlt2] means that two valuations coincide on the
        variables we care about. The STC side may assign arbitrary values to
        variables outside [xs]. *)
    Definition agree_on (xs: list ident) (dlt1 dlt2: ident -> Lat.t) : Prop :=
      forall x, In x xs -> dlt1 x = dlt2 x.

    (** [preserves_on xs cns1 cns2] states the weak preservation property used
        throughout the file: every valuation satisfying the source constraints
        can be extended to some valuation satisfying the target constraints,
        while preserving agreement on the shared scope [xs]. *)
    Definition preserves_on (xs: list ident) (cns1 cns2: list constraint) : Prop :=
      forall dlt,
        listSatisfiable dlt cns1 ->
        exists dlt',
          agree_on xs dlt dlt' /\ listSatisfiable dlt' cns2.

    (** These definitions capture the stronger signature-level reading of the
        same idea. They are convenient summaries, although the main theorem we
        prove in this development is the raw-constraint theorem [node_preserv]
        below. *)
    Definition sig_scope (sig: signature) : list ident :=
      sig.(s_in) ++ sig.(s_out) ++ (sig.(s_clk) :: sig.(s_reset) :: nil).

    Definition signature_fields_agree (n1 n2: signature) : Prop :=
      n1.(s_in) = n2.(s_in)
      /\ n1.(s_out) = n2.(s_out)
      /\ n1.(s_reset) = n2.(s_reset)
      /\ n1.(s_clk) = n2.(s_clk).

    Definition signatures_preserved (n1 n2: signature) : Prop :=
      signature_fields_agree n1 n2
      /\ preserves_on (sig_scope n1) n1.(s_constraints) n2.(s_constraints).

    (** [Signature_call_preserves n1 n2] packages the two call-specific
        obligations used by [eqn_preserv]:

        - ordinary calls instantiate the callee signatures with the caller's
          argument/output types;
        - resettable calls do the same, while allowing STC to prepend one fresh
          reset-instance constraint outside the shared scope. *)
    Definition Signature_call_preserves (n1 n2: signature) : Prop :=
      (forall scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2,
          generate_constraints n1 inptyp ckty rstty outtyp st_init1 = OK (nconst, st1) ->
          generate_constraints n2 inptyp ckty rstty outtyp st_init2 = OK (sconst, st2) ->
          preserves_on scope nconst sconst)
      /\ (forall scope inptyp ckty srcrst outtyp reset_lhs rst_inst nconst sconst st_init1 st_init2 st1 st2,
            ~ In rst_inst scope ->
            generate_constraints n1 inptyp ckty srcrst outtyp st_init1 = OK (nconst, st1) ->
            generate_constraints n2 inptyp ckty (rst_inst :: nil) outtyp st_init2 = OK (sconst, st2) ->
            preserves_on scope nconst ((reset_lhs, (rst_inst :: nil)) :: sconst)).

    (** [Signature_head_consistent n1 n2] is the local compatibility predicate
        for one NLustre/STC signature pair. [Signature_consistent] below is just
        the pointwise lifting of this predicate over global signature lists. *)
    Definition Signature_head_consistent (n1 n2: signature) : Prop :=
      n1.(s_name) = n2.(s_name)
      /\ signature_fields_agree n1 n2
      /\ Signature_call_preserves n1 n2.

    (** [Signature_consistent G1 G2] is the abstract compatibility assumption
        relating a source global signature environment and a target one.

        For each callee signature found on the NLustre side, it provides:

        - a matching STC signature with the same interface fields;
        - preservation for ordinary calls;
        - preservation for resettable calls, where STC is allowed to prepend one
          extra reset-instance constraint using a fresh identifier outside the
          chosen shared scope.

        This is the point where the present mechanisation intentionally differs
        from a literal "same signature" theorem from the paper: the statement
        explicitly tolerates STC-only auxiliaries. *)
    Definition Signature_consistent (G1 G2: secglobal) : Prop :=
      forall f n1,
        SECNLUSTYPING.find_signature f G1 = Some n1 ->
        exists n2,
          SECSTCTYPING.find_signature f G2 = Some n2
          /\ Signature_head_consistent n1 n2.
    Hint Unfold Signature_call_preserves Signature_head_consistent Signature_consistent.

    (** Closure of the weak preservation relation under concatenation of
        constraint lists. This is assumed rather than reproved here, so that the
        list-level theorem isolates the translation argument from the generic
        constraint semantics. *)
    Definition preserves_on_app_closed (scope: list ident) : Prop :=
      forall c1 c2 t1 t2,
        preserves_on scope c1 t1 ->
        preserves_on scope c2 t2 ->
        preserves_on scope (c1 ++ c2) (t1 ++ t2).

    (** Satisfaction is extensional on the variables a constraint actually
        mentions. This is the semantic replacement for the older ad hoc
        concatenation premise: to compose independently constructed witnesses,
        it is enough to know that each target block only depends on its shared
        scope plus its own private auxiliary variables. *)
    Lemma constraintSatisfiable_ext:
      forall c scope dlt1 dlt2,
        constraint_scoped scope c ->
        agree_on scope dlt1 dlt2 ->
        constraintSatisfiable dlt1 c ->
        constraintSatisfiable dlt2 c.
    Proof.
      intros [lhs rhs] scope dlt1 dlt2 Hsc Hagree Hsat.
      unfold constraintSatisfiable, satisfiable in *.
      assert (Hlhs: hm_ext dlt1 lhs = hm_ext dlt2 lhs).
      {
        clear Hsat.
        induction lhs as [|x xs IH]; simpl; auto.
        rewrite (Hagree x).
        2:{ eapply constraint_scoped_lhs; eauto. now left. }
        rewrite IH; auto.
        intros y Hy. apply Hagree.
        eapply constraint_scoped_lhs; eauto. now right.
      }
      destruct rhs as [|x rhs']; simpl in *.
      - exact Hsat.
      - rewrite <- Hlhs.
        rewrite (Hagree x).
        + exact Hsat.
        + eapply constraint_scoped_rhs; eauto. now left.
    Qed.

    Lemma listSatisfiable_ext:
      forall cns scope dlt1 dlt2,
        constraints_scoped scope cns ->
        agree_on scope dlt1 dlt2 ->
        listSatisfiable dlt1 cns ->
        listSatisfiable dlt2 cns.
    Proof.
      intros cns scope dlt1 dlt2 Hsc Hagree Hsat.
      induction Hsc as [|c cns Hc Hcs IH] in Hsat |- *.
      - constructor.
      - inversion Hsat; subst.
        constructor.
        + eapply constraintSatisfiable_ext; eauto.
        + eapply IH; eauto.
    Qed.

    Definition agree_on_notin
      (scope extras: list ident)
      (dlt base: ident -> Lat.t) : ident -> Lat.t :=
      fun x =>
        if in_dec ident_eq_dec x extras then dlt x
        else base x.

    Lemma agree_on_notin_scope:
      forall scope extras dlt base,
        (forall x, In x extras -> ~ In x scope) ->
        agree_on scope base (agree_on_notin scope extras dlt base).
    Proof.
      intros scope extras dlt base Hfresh x Hin.
      unfold agree_on_notin.
      destruct (in_dec ident_eq_dec x extras) as [Hinextra|Hnin]; auto.
      exfalso. eauto.
    Qed.

    Lemma agree_on_notin_extras:
      forall scope extras dlt base,
        NoDup extras ->
        (forall x, In x extras -> ~ In x scope) ->
        agree_on (scope ++ extras) dlt base ->
        agree_on (scope ++ extras) dlt (agree_on_notin scope extras dlt base).
    Proof.
      intros scope extras dlt base Hnd Hfresh Hagree x Hin.
      unfold agree_on_notin.
      destruct (in_dec ident_eq_dec x extras) as [Hinextra|Hnin].
      - reflexivity.
      - apply Hagree.
        apply in_app_iff in Hin.
        apply in_app_iff.
        destruct Hin as [Hin|Hin].
        + now left.
        + right.
          exfalso. apply Hnin. exact Hin.
    Qed.

    Lemma preserves_on_concat_scoped:
      forall scope extras1 extras2 c1 c2 t1 t2,
        NoDup (extras1 ++ extras2) ->
        (forall x, In x (extras1 ++ extras2) -> ~ In x scope) ->
        constraints_scoped (scope ++ extras1) t1 ->
        constraints_scoped (scope ++ extras2) t2 ->
        preserves_on scope c1 t1 ->
        preserves_on scope c2 t2 ->
        preserves_on scope (c1 ++ c2) (t1 ++ t2).
    Proof.
      intros scope extras1 extras2 c1 c2 t1 t2 Hnd Hfresh Hsc1 Hsc2 Hpres1 Hpres2 dlt Hsat.
      rewrite Forall_app in Hsat.
      destruct Hsat as [Hsat1 Hsat2].
      destruct (Hpres1 dlt Hsat1) as (dlt1 & Hagree1 & Ht1).
      destruct (Hpres2 dlt Hsat2) as (dlt2 & Hagree2 & Ht2).
      set (dlt' := agree_on_notin scope extras1 dlt1
                     (agree_on_notin scope extras2 dlt2 dlt)).
      exists dlt'. split.
      - unfold dlt'. eapply agree_on_notin_scope.
        intros x Hin.
        apply Hfresh. now apply in_or_app; left.
      - rewrite Forall_app. split.
        + eapply listSatisfiable_ext.
          * exact Hsc1.
          * unfold dlt'. eapply agree_on_notin_extras.
            -- eapply NoDup_app_l. exact Hnd.
            -- intros x Hin.
               apply Hfresh. now apply in_or_app; left.
            -- intros x Hin.
               unfold agree_on_notin.
               destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
               ++ reflexivity.
               ++ destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
                  ** exfalso.
                     apply in_app_iff in Hin.
                     destruct Hin as [Hinscope|Hin1'].
                     --- eapply Hfresh in Hin2. contradiction.
                         now apply in_or_app; right.
                     --- apply Hnin1. exact Hin1'.
                  ** apply Hagree1.
                     apply in_app_iff in Hin.
                     destruct Hin as [Hinscope|Hin1'].
                     --- exact Hinscope.
                     --- contradiction.
          * exact Ht1.
        + eapply listSatisfiable_ext.
          * exact Hsc2.
          * unfold dlt'. intros x Hin.
            unfold agree_on_notin.
            destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
            -- exfalso.
               apply in_app_iff in Hin.
               destruct Hin as [Hinscope|Hin2].
               ++ eapply Hfresh in Hin1. contradiction.
                  now apply in_or_app; left.
               ++ assert (~ In x extras2).
                  { intro Hcontra.
                    eapply NoDup_app_In with (x := x) in Hnd; eauto. }
                  contradiction.
            -- destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
               ++ reflexivity.
               ++ apply Hagree2.
                  apply in_app_iff in Hin.
                  destruct Hin as [Hinscope|Hin2'].
                  ** exact Hinscope.
                  ** contradiction.
          * exact Ht2.
    Qed.

    Lemma agree_on_refl: forall xs dlt, agree_on xs dlt dlt.
    Proof.
      intros * x Hin. reflexivity.
    Qed.

    Lemma preserves_on_nil: forall scope, preserves_on scope nil nil.
    Proof.
      intros scope dlt Hsat.
      exists dlt. split.
      - apply agree_on_refl.
      - exact Hsat.
    Qed.

    (** Reset-call keys in source equations.

        These helpers isolate the only source-defined variables that create
        private STC auxiliaries during translation: the leading output of a
        resettable [EqApp].  They are used later to relate source equation-list
        structure to the reset-instance environment generated on the STC side. *)
    Definition reset_call_var (e: equation) : option ident :=
      match e with
      | EqApp (x :: _) _ _ _ (Some _) => Some x
      | _ => None
      end.

    Fixpoint reset_call_vars (eqs: list equation) : list ident :=
      match eqs with
      | [] => []
      | eq :: eqs' =>
          match reset_call_var eq with
          | Some x => x :: reset_call_vars eqs'
          | None => reset_call_vars eqs'
          end
      end.

    Lemma reset_call_vars_in_vars_defined:
      forall eqs x,
        In x (reset_call_vars eqs) ->
        In x (vars_defined eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      - inversion Hin.
      - destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp];
          simpl in *; try now right; eauto.
        destruct xs as [|x0 xs]; simpl in *.
        + eauto.
        + destruct orst as [[r ckr]|]; simpl in *.
          * destruct Hin as [Heq|Hin].
            -- subst x.
               rewrite IsD.vars_defined_cons. simpl. now left.
            -- rewrite IsD.vars_defined_cons. simpl. right. eauto.
          * eauto.
    Qed.

    Lemma reset_call_vars_nodup:
      forall eqs,
        NoDup (vars_defined eqs) ->
        NoDup (reset_call_vars eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros Hnd.
      - constructor.
      - destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp];
          simpl in *; eauto.
        destruct xs as [|x0 xs]; simpl in *; eauto.
        destruct orst as [[r ckr]|]; simpl in *; eauto.
        apply NoDup_cons.
        + intro Hin.
          apply (reset_call_vars_in_vars_defined eqs) in Hin.
          rewrite IsD.vars_defined_cons in Hnd.
          apply NoDup_cons_iff in Hnd as [Hnin _].
          simpl in Hnin.
          apply Hnin. now right.
        + rewrite IsD.vars_defined_cons in Hnd.
          apply NoDup_cons_iff in Hnd as [_ Htail].
          eauto.
    Qed.

    Lemma reset_call_var_translate_eqn:
      forall eq x,
        reset_call_var eq = Some x ->
        exists ck f,
          In (TcReset x ck f) (translate_eqn eq).
    Proof.
      intros [y ck ce|xs ck f exps orst|y ck c0 exp] x Hreset;
        simpl in Hreset; try discriminate.
      destruct xs as [|x0 xs]; try discriminate.
      destruct orst as [[r ckr]|]; try discriminate.
      inversion Hreset; subst x.
      exists (Con ckr r true), f.
      simpl. now left.
    Qed.

    Lemma reset_call_vars_translate_eqns:
      forall eqs x,
        In x (reset_call_vars eqs) ->
        exists ck f,
          In (TcReset x ck f) (translate_eqns eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      - inversion Hin.
      - simpl in Hin.
        destruct (reset_call_var eq) as [x0|] eqn:Hreset.
        + destruct Hin as [Heq|Hin].
          * subst x.
            destruct (reset_call_var_translate_eqn _ _ Hreset) as (ck & f & Hin').
            exists ck, f.
            unfold translate_eqns. simpl. now apply in_or_app; left.
          * destruct (IH _ Hin) as (ck & f & Hin').
            exists ck, f.
            unfold translate_eqns. simpl. now apply in_or_app; right.
        + destruct (IH _ Hin) as (ck & f & Hin').
          exists ck, f.
          unfold translate_eqns. simpl. now apply in_or_app; right.
    Qed.
    
    (** Small inversion tactic for the state/error monad used by the typing
        functions. *)
    Ltac myMonadInv :=
      simpl in *;
      try (unfold error in *);
      match goal with
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
   

    (** Single-equation preservation.

        The interesting cases are calls:

        - an ordinary call is discharged by the ordinary-call component of
          [Signature_consistent];
        - a resettable call is discharged by the reset-call component of
          [Signature_consistent], after aligning the fresh reset-instance name
          introduced on the STC side and recording that it lies outside the
          shared scope. *)
    Theorem eqn_preserv:
    forall scope (G1 G2: secglobal), Signature_consistent G1 G2 ->
    forall (e: equation) (trs: list trconstr), translate_eqn e = trs ->
    forall (env rst_env: Env.t ident)
           (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
           (forall x rst_inst st1' st2',
               find_env x rst_env st1' = OK (rst_inst, st2') ->
               ~ In rst_inst scope) ->
           (generate_eqn_constraint G1 env base_ty rst_ty e init_state1) = OK (nconst, st1) ->
           (generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2) = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope G1 G2 Hsig e trs Htr env rst_env base_ty rst_ty nconst sconst
             init_state1 init_state2 st1 st2 Hfresh Hnl Hstc.
      destruct e as [x ck cexp|xs ck f exps orst|x ck c0 exp].
      - simpl in Htr. subst trs. simpl in Hnl, Hstc.
        repeat myMonadInv.
        assert (Hck: x0 = x1).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hexp: x7 = x3).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hxty: x9 = x5).
        { eapply find_env_consistent_nl_stc; eauto. }
        subst.
        unfold preserves_on. intros dlt Hsat.
        exists dlt. split.
        + apply agree_on_refl.
        + exact Hsat.
      - destruct xs as [|x xs].
        + simpl in Htr. subst trs. simpl in Hnl, Hstc.
          repeat myMonadInv.
          apply preserves_on_nil.
        + destruct orst as [[r ckr]|].
          * simpl in Htr. subst trs. simpl in Hnl, Hstc.
            destruct (SECNLUSTYPING.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [_ Hresetcall]]]]].
            rewrite Hfindstc in Hstc.
            repeat myMonadInv.
            assert (Hck: x0 = x2).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp: x21 = x5).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthead: x25 = x11).
            { eapply find_env_consistent_nl_stc; eauto. }
            assert (Houttail: x27 = x13).
            { eapply mmap_find_env_consistent_nl_stc; eauto. }
            assert (Hrstinst: x15 = x9).
            { eapply find_env_consistent; eauto. }
            subst x2 x5 x11 x13 x15.
            assert (Hnin: ~ In x9 scope).
            { eapply (Hfresh x x9 x14 x1). exact Hbind. }
            rewrite app_nil_r.
            eexact (Hresetcall scope x21 x0 _ (x25 :: x27) ((rst_ty :: nil) ⊔ x7)
                                x9 nconst x3 x24 x10 st1 st2 Hnin Hbind13 Hbind5).
          * simpl in Htr. subst trs. simpl in Hnl, Hstc.
            destruct (SECNLUSTYPING.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [Hsimplecall _]]]]].
            rewrite Hfindstc in Hstc.
            repeat myMonadInv.
            assert (Hck: x5 = x1).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp: x11 = x3).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthead: x15 = x7).
            { eapply find_env_consistent_nl_stc; eauto. }
            assert (Houttail: x17 = x9).
            { eapply mmap_find_env_consistent_nl_stc; eauto. }
            subst x1 x3 x7 x9.
            rewrite app_nil_r.
            eexact (Hsimplecall scope x11 x5 (rst_ty :: nil) (x15 :: x17)
                                 nconst x0 x14 x6 st1 st2 Hbind8 Hbind3).
      - simpl in Htr. subst trs. simpl in Hnl, Hstc.
        repeat myMonadInv.
        assert (Hck: x0 = x1).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hexp: x7 = x3).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hxty: x9 = x5).
        { eapply find_env_consistent_nl_stc; eauto. }
        subst.
        unfold preserves_on. intros dlt Hsat.
        exists dlt. split.
        + apply agree_on_refl.
        + exact Hsat.
    Qed.

    (** List-level preservation follows by induction over equations and the fact
        that [translate_eqns], [generate_eqns_constraints], and
        [generate_trconstrs_constraints] all compose by concatenation. *)
    Lemma eqns_preserv: forall scope (G1 G2: secglobal), Signature_consistent G1 G2 ->
    preserves_on_app_closed scope ->
    forall (es: list equation) (trs: list trconstr), translate_eqns es = trs ->
    forall (env rst_env: Env.t ident)
           (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
           (forall x rst_inst st1' st2',
               find_env x rst_env st1' = OK (rst_inst, st2') ->
               ~ In rst_inst scope) ->
           (generate_eqns_constraints G1 env base_ty rst_ty es init_state1) = OK (nconst, st1) ->
           (generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2) = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope G1 G2 Hsig Happ es.
      induction es as [|e es IH]; intros trs env rst_env base_ty rst_ty nconst sconst
                                      Htr init_state1 init_state2 st1 st2 Hfresh Hnl Hstc.
      - simpl in Htr. subst trs. simpl in Hnl, Hstc.
        repeat myMonadInv.
        apply preserves_on_nil.
      - unfold translate_eqns in Htr. simpl in Htr.
        simpl in Hnl.
        repeat myMonadInv.
        eapply generate_tr_constraints_inv in Hstc.
        destruct Hstc as (sconst1 & st_mid & sconst2 & [Hstc1 [Hstc2 Hsconst]]).
        rewrite Hsconst.
        eapply Happ.
        + eapply eqn_preserv; eauto with nocore.
          reflexivity.
        + eapply IH; eauto.
    Qed.

  End SECEQNPRES. 

  (** The node/system part of the development is organised in five layers:

      1. [node_preserv] is the core theorem. It works for one already-aligned
         node/system pair and assumes the relevant environment lookups plus the
         freshness of STC reset-instance variables.
      2. The freshness and inversion lemmas below are used only to discharge
         those assumptions when the environments and signatures come from the
         generators in [NameInterface], [SecNLusTyping], and [SecSTCTyping].
      3. [generated_node_preserv] packages that discharge for generated
         signatures, and [found_system_preserv] is the lookup-based corollary
         obtained from [find_system_translate].
      4. The bridge layer reconstructs per-node
         [Signature_head_consistent] from two explicit semantic ingredients:
         simplification completeness for generated signatures, and call-time
         preservation derived from [signatures_preserved].
      5. [Signature_consistent_cons] and the generated-signature induction then
         lift that local compatibility relation to entire generated signature
         lists.
      6. [generated_node_preserv_global] and
         [generated_program_preserv_global] use that global consistency result
         to remove the explicit [Signature_consistent] premise from the final
         node/system theorems. *)
  Section NODESYSPRES.

    (** Core node theorem.

        This is the direct analogue of the list-level theorem [eqns_preserv]
        for a translated node/system pair. All bookkeeping facts are explicit
        in the premises:

        - shared NLustre/STC interface lookups in the common environment;
        - the chosen shared scope;
        - the reset-instance environment produced on the STC side;
        - freshness of reset-instance variables with respect to the shared
          scope.

        The more user-facing theorem [generated_node_preserv] below is obtained
        by reconstructing these premises from the generated environments and
        signatures. *)
    Theorem node_preserv:
      forall (n : node) (s: system) scope
             (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             clk_id rst_id clk_type rst_type
             inp out locals
             reset_env rids
             nconst sconst
             st_reset st_n st_s,
        translate_node n = s ->
        Signature_consistent G1 G2 ->
        preserves_on_app_closed scope ->
        get_node_aux (n.(n_name)) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node (n.(n_in)) env = Some inp ->
        get_mappings_from_node (n.(n_out)) env = Some out ->
        get_mappings_from_node (n.(n_vars)) env = Some locals ->
        scope = inp ++ out ++ locals ++ (clk_type :: rst_type :: nil) ->
        generate_reset_env s.(SynStc.s_tcs) init_state = OK ((reset_env, rids), st_reset) ->
        (forall x rst_inst st1 st2,
            find_env x reset_env st1 = OK (rst_inst, st2) ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (nconst, st_n) ->
        generate_trconstrs_constraints G2 env reset_env clk_type rst_type s.(SynStc.s_tcs) st_reset = OK (sconst, st_s) ->
        preserves_on scope nconst sconst.
    Proof.
      intros n s scope G1 G2 env aux_names clk_id rst_id clk_type rst_type
             inp out locals reset_env rids nconst sconst st_reset st_n st_s
             Htr Hsig Happ Haux Hclk Hrst Hinp Hout Hlocals Hscope
             Hresetenv Hfresh Hnl Hstc.
      subst scope.
      subst s. simpl in Hresetenv, Hstc.
      eapply eqns_preserv; eauto.
    Qed.

    (** The lemmas in this block are only used to discharge the freshness side
        conditions of [generated_node_preserv]. They establish that ordinary
        security variables come from the [sec] namespace, while reset-instance
        variables come from the disjoint [sec_reset] namespace. *)
    Ltac myNameInv :=
      simpl in *;
      match goal with
      | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
      | H: Error _ = OK _ |- _ =>
        discriminate
      | H: NMret _ _ = _ |- _ =>
        unfold NMret in H
      | H: NMbind ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply name_bind_inv in H as [? [? [H1 H2]]]
      | H: NMbind2 ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply name_bind2_inv in H as [? [? [? [H1 H2]]]]
      end; simpl in *.

    Ltac mySecInv :=
      simpl in *;
      match goal with
      | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
      | H: Error _ = OK _ |- _ =>
        discriminate
      | H: ret _ _ = _ |- _ =>
        unfold ret in H
      | H: bind ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply sec_bind_inv in H as [? [? [H1 H2]]]
      | H: bind2 ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
      end; simpl in *.

    Lemma get_mappings_In:
      forall xs env tys ty,
        get_mappings xs env = Some tys ->
        In ty tys ->
        exists x, In x xs /\ Env.find x env = Some ty.
    Proof.
      induction xs as [|x xs IH]; intros env tys ty Hmap Hin.
      - simpl in Hmap. inversion Hmap; subst. inversion Hin.
      - simpl in Hmap.
        destruct (Env.find x env) as [xty|] eqn:Hfind.
        2: discriminate.
        destruct (get_mappings xs env) as [tys'|] eqn:Hmaps.
        2: discriminate.
        inversion Hmap; subst tys.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst ty. exists x. split; [left; reflexivity|exact Hfind].
        + specialize (IH env tys' ty Hmaps Hin) as (x' & Hin' & Hfind').
          exists x'. split; [right; exact Hin'|exact Hfind'].
    Qed.

    Lemma fresh_map_list_preserves_find:
      forall ks env st env' st' x ty,
        fresh_map_list ks env st = OK (env', st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      induction ks as [|k ks IH]; intros env st env' st' x ty Hmap Hfind.
      - simpl in Hmap. inversion Hmap; subst. exact Hfind.
      - simpl in Hmap.
        unfold fresh_insert in Hmap.
        destruct (Env.mem k env) eqn:Hmem; try discriminate.
        eapply name_bind_inv in Hmap as (v & st1 & Hfresh & Hmap).
        eapply name_bind_inv in Hmap as (env1 & st2 & Hins & Hmap).
        unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v st1.
        unfold insert_env, NMret in Hins. inversion Hins; subst env1 st2.
        assert (Hxk : x <> k).
        { intro Heq; subst x.
          assert (Env.mem k env = true).
          { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
          congruence. }
        apply IH with (st := Pos.succ st); auto.
        rewrite Env.gso; auto.
    Qed.

    Lemma generate_new_names_for_node_preserves_find:
      forall n env st env' aux st' x ty,
        generate_new_names_for_node n env st = OK ((env', aux), st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros n env st env' aux st' x ty Hgen Hfind.
      unfold generate_new_names_for_node in Hgen.
      eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
      eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
      eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hret).
      unfold NMret in Hret. inversion Hret; subst env' aux st'.
      eapply fresh_map_list_preserves_find; eauto.
    Qed.

    Lemma generate_node_env'_preserves_find:
      forall ns env acc st env' aux st' x ty,
        generate_node_env' ns env acc st = OK ((env', aux), st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      induction ns as [|n ns IH]; intros env acc st env' aux st' x ty Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. exact Hfind.
      - simpl in Hgen.
        eapply name_bind2_inv in Hgen as (env1 & r & st1 & Hstep & Hgen).
        eapply IH; eauto.
        eapply generate_new_names_for_node_preserves_find; eauto.
    Qed.

    Lemma fresh_insert_sec_range:
      forall env k st env' st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec n) ->
        fresh_insert env k st = OK (env', st') ->
        Env.find x env' = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n.
    Proof.
      intros env k st env' st' x ty Henv Hins Hfind.
      unfold fresh_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply name_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_ident_gen in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, NMret in Hins0.
      inversion Hins0; subst e st2.
      unfold NMret in Hret. inversion Hret. subst env' st'.
      destruct (Pos.eq_dec x k) as [Heq|Hneq].
      - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
        eexists; reflexivity.
      - rewrite Env.gso in Hfind; eauto.
    Qed.

    Lemma fresh_map_list_sec_range:
      forall ks env st env' st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec n) ->
        fresh_map_list ks env st = OK (env', st') ->
        Env.find x env' = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n.
    Proof.
      induction ks as [|k ks IH]; intros env st env' st' x ty Henv Hmap Hfind.
      - simpl in Hmap. inversion Hmap; subst. eauto.
      - simpl in Hmap.
        repeat myNameInv.
        eapply IH; [|eauto|eauto].
        intros y ty' Hy.
        eapply fresh_insert_sec_range; eauto.
    Qed.

    Lemma generate_new_names_for_node_sec_range:
      forall n env st env' aux st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists m, ty' = Ids.gensym Ids.sec m) ->
        generate_new_names_for_node n env st = OK ((env', aux), st') ->
        Env.find x env' = Some ty ->
        exists m, ty = Ids.gensym Ids.sec m.
    Proof.
      intros n env st env' aux st' x ty Henv Hgen Hfind.
      unfold generate_new_names_for_node in Hgen.
      eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
      eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
      eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hret).
      unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
      unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
      unfold NMret in Hret. inversion Hret. subst env' aux st'.
      eapply fresh_map_list_sec_range; eauto.
    Qed.

    Lemma generate_node_env_sec_range':
      forall ns env acc st env' aux st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists m, ty' = Ids.gensym Ids.sec m) ->
        generate_node_env' ns env acc st = OK ((env', aux), st') ->
        Env.find x env' = Some ty ->
        exists m, ty = Ids.gensym Ids.sec m.
    Proof.
      induction ns as [|n ns IH]; intros env acc st env' aux st' x ty Henv Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. eauto.
      - simpl in Hgen.
        repeat myNameInv.
        eapply IH; [|eauto|eauto].
        intros y ty' Hy.
        eapply generate_new_names_for_node_sec_range; eauto.
    Qed.

    Lemma generate_node_env_sec_range:
      forall ns env aux x ty,
        generate_node_env ns = OK (env, aux) ->
        Env.find x env = Some ty ->
        exists m, ty = Ids.gensym Ids.sec m.
    Proof.
      intros ns env aux x ty Hgen Hfind.
      unfold generate_node_env in Hgen.
      destruct (generate_node_env' ns (Env.empty _) nil init_state) as [[[env' aux'] st']|] eqn:Hgen'; try discriminate.
      inversion Hgen; subst env aux.
      eapply generate_node_env_sec_range'; eauto.
      intros y ty' Hy.
      rewrite Env.gempty in Hy. discriminate.
    Qed.

    Definition env_values (env: Env.t ident) : list (ident * ident) :=
      map (fun '(x, ty) => (ty, x)) (Env.elements env).

    Definition env_sec_bounded (st: ident) (env: Env.t ident) : Prop :=
      forall x ty,
        Env.find x env = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive.

    Definition aux_sec_names (aux: list node_aux_names) : Prop :=
      forall rec,
        In rec aux ->
        exists i j,
          rec.(nclk) = Ids.gensym Ids.sec i
          /\ rec.(nrst) = Ids.gensym Ids.sec j.

    Lemma env_sec_bounded_step:
      forall st env,
        env_sec_bounded st env ->
        env_sec_bounded (Pos.succ st) env.
    Proof.
      intros st env Hbound x ty Hfind.
      specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
      exists n. split; auto.
      eapply Pos.lt_trans; eauto.
      apply Pos.lt_succ_diag_r.
    Qed.

    Lemma env_values_add:
      forall x ty env,
        ~ Env.In x env ->
        Permutation.Permutation (env_values (Env.add x ty env))
                                ((ty, x) :: env_values env).
    Proof.
      intros x ty env Hnin.
      unfold env_values.
      replace ((ty, x) :: map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))
        with (map (fun '(x0, ty0) => (ty0, x0)) ((x, ty) :: Env.elements env))
        by reflexivity.
      now apply Permutation.Permutation_map, Env.elements_add.
    Qed.

    Lemma env_values_nodup_injective:
      forall env,
        NoDupMembers (env_values env) ->
        SECNLUSTYPING.env_injective env.
    Proof.
      intros env Hnodup x y tx ty Hfindx Hfindy Heq.
      apply Env.elements_correct in Hfindx.
      apply Env.elements_correct in Hfindy.
      unfold env_values in Hnodup.
      assert (Hinx : In (tx, x) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
      { apply in_map_iff. exists (x, tx). split; [reflexivity|exact Hfindx]. }
      assert (Hiny : In (tx, y) (map (fun '(x0, ty0) => (ty0, x0)) (Env.elements env))).
      { subst ty.
        apply in_map_iff. exists (y, tx). split; [reflexivity|exact Hfindy]. }
      now eapply NoDupMembers_det; eauto.
    Qed.

    Lemma env_values_fresh_notin:
      forall env st,
        env_sec_bounded st env ->
        ~ InMembers (Ids.gensym Ids.sec st) (env_values env).
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

    Lemma fresh_insert_env_props:
      forall env k st env' st',
        env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        fresh_insert env k st = OK (env', st') ->
        env_sec_bounded st' env'
        /\ NoDupMembers (env_values env').
    Proof.
      intros env k st env' st' Hbound Hnodup Hgen.
      unfold fresh_insert in Hgen.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
      eapply name_bind_inv in Hgen as (e & st2 & Hins & Hret).
      unfold fresh_ident_gen in Hfresh. inversion Hfresh; subst v st1.
      unfold insert_env, NMret in Hins. inversion Hins; subst e st2.
      unfold NMret in Hret. inversion Hret; subst env' st'.
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
                  (env_values (Env.add k (Ids.gensym Ids.sec st) env))
                  ((Ids.gensym Ids.sec st, k) :: env_values env)).
        + apply env_values_add; exact Hnotin.
        + constructor.
          * apply env_values_fresh_notin; exact Hbound.
          * exact Hnodup.
    Qed.

    Lemma fresh_map_list_env_props:
      forall ks env st env' st',
        env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        fresh_map_list ks env st = OK (env', st') ->
        env_sec_bounded st' env'
        /\ NoDupMembers (env_values env').
    Proof.
      induction ks as [|k ks IH]; intros env st env' st' Hbound Hnodup Hgen.
      - simpl in Hgen. inversion Hgen; subst. auto.
      - simpl in Hgen.
        eapply name_bind_inv in Hgen as (env1 & st1 & Hstep & Hgen).
        eapply name_bind_inv in Hgen as (env2 & st2 & Hrec & Hret).
        unfold NMret in Hret. inversion Hret; subst env' st'.
        destruct (fresh_insert_env_props _ _ _ _ _ Hbound Hnodup Hstep) as [Hbound1 Hnodup1].
        eapply IH; eauto.
    Qed.

    Lemma generate_new_names_for_node_env_props:
      forall n env st env' aux st',
        env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        generate_new_names_for_node n env st = OK ((env', aux), st') ->
        env_sec_bounded st' env'
        /\ NoDupMembers (env_values env')
        /\ exists i j,
            aux.(nclk) = Ids.gensym Ids.sec i
            /\ aux.(nrst) = Ids.gensym Ids.sec j.
    Proof.
      intros n env st env' aux st' Hbound Hnodup Hgen.
      unfold generate_new_names_for_node in Hgen.
      eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
      eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
      eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hret).
      unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
      unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
      unfold NMret in Hret. inversion Hret; subst env' aux st'.
      destruct (fresh_map_list_env_props _ _ _ _ _
                  (env_sec_bounded_step _ _ (env_sec_bounded_step _ _ Hbound))
                  Hnodup Hmap) as [Hbound' Hnodup'].
      split; [exact Hbound'|].
      split; [exact Hnodup'|].
      exists st, (Pos.succ st). auto.
    Qed.

    Lemma generate_node_env_props':
      forall ns env acc st env' aux st',
        env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        aux_sec_names acc ->
        generate_node_env' ns env acc st = OK ((env', aux), st') ->
        env_sec_bounded st' env'
        /\ NoDupMembers (env_values env')
        /\ aux_sec_names aux.
    Proof.
      induction ns as [|n ns IH]; intros env acc st env' aux st'
                                          Hbound Hnodup Hacc Hgen.
      - simpl in Hgen. inversion Hgen; subst. repeat split; auto.
      - simpl in Hgen.
        eapply name_bind2_inv in Hgen as (env1 & rec & st1 & Hstep & Hgen).
        eapply name_bind2_inv in Hgen as (env2 & rs & st2 & Hrec & Hret).
        unfold NMret in Hret. inversion Hret; subst env' aux st'.
        destruct (generate_new_names_for_node_env_props _ _ _ _ _ _
                    Hbound Hnodup Hstep)
          as [Hbound1 [Hnodup1 Haux1]].
        eapply IH; eauto.
        intros rec' Hin.
        destruct Hin as [Heq|Hin].
        + subst rec'. exact Haux1.
        + eapply Hacc; eauto.
    Qed.

    Lemma generate_node_env_injective:
      forall all_nodes env aux_names,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.env_injective env.
    Proof.
      intros all_nodes env aux_names Hgen.
      unfold generate_node_env in Hgen.
      destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
        as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
      inversion Hgen; subst env aux_names.
      destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
        as [_ [Hnodup _]];
        eauto.
      - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
      - constructor.
      - intros rec Hin. contradiction.
      - eapply env_values_nodup_injective; eauto.
    Qed.

    Lemma get_node_aux_In:
      forall name aux clk_id rst_id,
        get_node_aux name aux = Some (clk_id, rst_id) ->
        exists rec,
          In rec aux
          /\ rec.(nname) = name
          /\ rec.(nclk) = clk_id
          /\ rec.(nrst) = rst_id.
    Proof.
      induction aux as [|rec aux IH]; intros clk_id rst_id Haux.
      - unfold get_node_aux in Haux. simpl in Haux. discriminate.
      - unfold get_node_aux in Haux. simpl in Haux.
        destruct (ident_eqb name rec.(nname)) eqn:Hname.
        + inversion Haux; subst clk_id rst_id.
          apply ident_eqb_eq in Hname.
          exists rec. repeat split; auto.
        + eapply IH in Haux as (rec' & Hin & Hn & Hc & Hr).
          exists rec'. repeat split; auto.
    Qed.

    Lemma generate_node_aux_sec_names:
      forall all_nodes env aux_names name clk_id rst_id,
        generate_node_env all_nodes = OK (env, aux_names) ->
        get_node_aux name aux_names = Some (clk_id, rst_id) ->
        exists i j,
          clk_id = Ids.gensym Ids.sec i
          /\ rst_id = Ids.gensym Ids.sec j.
    Proof.
      intros all_nodes env aux_names name clk_id rst_id Hgen Haux.
      unfold generate_node_env in Hgen.
      destruct (generate_node_env' all_nodes (Env.empty _) nil init_state)
        as [[[env0 aux0] st0]|] eqn:Hgen'; try discriminate.
      inversion Hgen; subst env aux_names.
      destruct (generate_node_env_props' all_nodes (Env.empty _) nil init_state env0 aux0 st0)
        as [_ [_ Hauxsec]];
        eauto.
      - intros x ty Hfind. rewrite Env.gempty in Hfind. discriminate.
      - constructor.
      - intros rec Hin. contradiction.
      - eapply get_node_aux_In in Haux as (rec & Hin & _ & Hclk & Hrst).
        specialize (Hauxsec rec Hin) as (i & j & Hi & Hj).
        rewrite Hclk, Hrst in *. eauto.
    Qed.

    Lemma fresh_reset_insert_sec_range:
      forall env k st env' rst_inst st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
        fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
        Env.find x env' = Some ty ->
        exists n, ty = Ids.gensym Ids.sec_reset n.
    Proof.
      intros env k st env' rst_inst st' x ty Henv Hins Hfind.
      unfold fresh_reset_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_reset_ident in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins0.
      inversion Hins0; subst e st2.
      unfold ret in Hret. inversion Hret. subst env' rst_inst st'.
      destruct (Pos.eq_dec x k) as [Heq|Hneq].
      - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
        eexists; reflexivity.
      - rewrite Env.gso in Hfind; eauto.
    Qed.

    Lemma generate_reset_env_range':
      forall trs env acc st reset_env rids st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec_reset n) ->
        generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
        Env.find x reset_env = Some ty ->
        exists n, ty = Ids.gensym Ids.sec_reset n.
    Proof.
      induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ty Henv Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. eauto.
      - simpl in Hgen.
        destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
        1,2,4: eapply IH; eauto.
        repeat mySecInv.
        eapply IH; [|eauto|eauto].
        intros y ty' Hy.
        eapply fresh_reset_insert_sec_range; eauto.
    Qed.

    Lemma generate_reset_env_range:
      forall trs reset_env rids st' x ty,
        generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
        Env.find x reset_env = Some ty ->
        exists n, ty = Ids.gensym Ids.sec_reset n.
    Proof.
      intros trs reset_env rids st' x ty Hgen Hfind.
      unfold generate_reset_env in Hgen.
      eapply generate_reset_env_range'; eauto.
      intros y ty' Hy.
      rewrite Env.gempty in Hy. discriminate.
    Qed.

    Lemma fresh_reset_insert_preserves_find:
      forall env k st env' rst_inst st' x ty,
        fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros env k st env' rst_inst st' x ty Hins Hfind.
      unfold fresh_reset_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply sec_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_reset_ident in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins0. inversion Hins0; subst e st2.
      unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
      assert (Hxk : x <> k).
      { intro Heq. subst x.
        assert (Env.mem k env = true).
        { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
        congruence. }
      now rewrite Env.gso.
    Qed.

    Lemma generate_reset_env'_preserves_find:
      forall trs env acc st reset_env rids st' x ty,
        generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
        Env.find x env = Some ty ->
        Env.find x reset_env = Some ty.
    Proof.
      induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ty Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. exact Hfind.
      - simpl in Hgen.
        destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
        1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
        eapply IH; eauto.
        eapply fresh_reset_insert_preserves_find; eauto.
    Qed.

    Definition reset_env_sec_bounded (st: ident) (env: Env.t ident) : Prop :=
      forall x ty,
        Env.find x env = Some ty ->
        exists n, ty = Ids.gensym Ids.sec_reset n /\ (n < st)%positive.

    Lemma reset_env_sec_bounded_step:
      forall st env,
        reset_env_sec_bounded st env ->
        reset_env_sec_bounded (Pos.succ st) env.
    Proof.
      intros st env Hbound x ty Hfind.
      specialize (Hbound _ _ Hfind) as (n & Hn & Hlt).
      exists n. split; auto.
      eapply Pos.lt_trans; eauto.
      apply Pos.lt_succ_diag_r.
    Qed.

    Lemma reset_env_values_fresh_notin:
      forall env st,
        reset_env_sec_bounded st env ->
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
      forall env k st env' rst_inst st',
        reset_env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        fresh_reset_insert k env st = OK ((env', rst_inst), st') ->
        reset_env_sec_bounded st' env'
        /\ NoDupMembers (env_values env').
    Proof.
      intros env k st env' rst_inst st' Hbound Hnodup Hgen.
      unfold fresh_reset_insert in Hgen.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply sec_bind_inv in Hgen as (v & st1 & Hfresh & Hgen).
      eapply sec_bind_inv in Hgen as (e & st2 & Hins & Hret).
      unfold fresh_reset_ident in Hfresh. inversion Hfresh; subst v st1.
      unfold insert_env, ret in Hins. inversion Hins; subst e st2.
      unfold ret in Hret. inversion Hret; subst env' rst_inst st'.
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
          * apply reset_env_values_fresh_notin; exact Hbound.
          * exact Hnodup.
    Qed.

    Lemma generate_reset_env_props':
      forall trs env acc st reset_env rids st',
        reset_env_sec_bounded st env ->
        NoDupMembers (env_values env) ->
        generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
        reset_env_sec_bounded st' reset_env
        /\ NoDupMembers (env_values reset_env).
    Proof.
      induction trs as [|tr trs IH]; intros env acc st reset_env rids st'
                                            Hbound Hnodup Hgen.
      - simpl in Hgen. inversion Hgen; subst. auto.
      - simpl in Hgen.
        destruct tr as [x0 ck ce|x0 ck e|x0 rck f|x0 xs ck b f exps].
        1,2,4: eapply IH; eauto.
        eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
        destruct (fresh_reset_insert_env_props _ _ _ _ _ _
                    Hbound Hnodup Hstep) as [Hbound1 Hnodup1].
        eapply IH; eauto.
    Qed.

    Lemma generate_reset_env_injective:
      forall trs reset_env rids st',
        generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
        forall x y tx ty,
          Env.find x reset_env = Some tx ->
          Env.find y reset_env = Some ty ->
          tx = ty ->
          x = y.
    Proof.
      intros trs reset_env rids st' Hgen.
      unfold generate_reset_env in Hgen.
      destruct (generate_reset_env' trs (Env.empty _) [] init_state)
        as [[[reset_env0 rids0] st0]|] eqn:Hgen'; try discriminate.
      inversion Hgen; subst reset_env rids st'.
      intros x y tx ty Hfindx Hfindy Heq.
      destruct (generate_reset_env_props' trs (Env.empty _) [] init_state reset_env0 rids0 st0)
        as [_ Hnodup];
        eauto.
      - intros z tz Hz. rewrite Env.gempty in Hz. discriminate.
      - constructor.
      - eapply env_values_nodup_injective; eauto.
    Qed.

    Lemma generate_reset_env'_has_reset_stmt:
      forall trs env acc st reset_env rids st' x ck f,
        generate_reset_env' trs env acc st = OK ((reset_env, rids), st') ->
        In (TcReset x ck f) trs ->
        exists ty, Env.find x reset_env = Some ty.
    Proof.
      induction trs as [|tr trs IH]; intros env acc st reset_env rids st' x ck f Hgen Hin.
      - inversion Hin.
      - simpl in Hgen.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst tr.
          eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
          exists i.
          eapply generate_reset_env'_preserves_find; eauto.
          unfold assign_reset_type in Hstep.
          eapply sec_bind2_inv in Hstep as (env0 & rst_inst & st0 & Hfresh & Hret).
          inversion Hret; subst env0 rst_inst st0.
          unfold fresh_reset_insert in Hfresh.
          destruct (Env.mem x env) eqn:Hmem; try discriminate.
          eapply sec_bind_inv in Hfresh as (v & stv & Hfreshid & Hins).
          eapply sec_bind_inv in Hins as (e & ste & Hins & Hdone).
          unfold fresh_reset_ident in Hfreshid. inversion Hfreshid; subst v stv.
          unfold insert_env, ret in Hins. inversion Hins; subst e ste.
          rewrite Env.gss. reflexivity.
        + destruct tr as [x0 ck0 ce|x0 ck0 e|x0 rck0 f0|x0 xs ck0 b f0 exps].
          1,2,4: eauto.
          eapply sec_bind2_inv in Hgen as (env1 & i & st1 & Hstep & Hrec).
          eauto.
    Qed.

    Lemma generate_reset_env_has_reset_stmt:
      forall trs reset_env rids st' x ck f,
        generate_reset_env trs init_state = OK ((reset_env, rids), st') ->
        In (TcReset x ck f) trs ->
        exists ty, Env.find x reset_env = Some ty.
    Proof.
      intros trs reset_env rids st' x ck f Hgen Hin.
      unfold generate_reset_env in Hgen.
      eapply generate_reset_env'_has_reset_stmt; eauto.
    Qed.

    Lemma node_scope_sec_range:
      forall all_nodes env aux_names n
             clk_id rst_id clk_type rst_type inp out locals ty,
        generate_node_env all_nodes = OK (env, aux_names) ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
        exists m, ty = Ids.gensym Ids.sec m.
    Proof.
      intros all_nodes env aux_names n clk_id rst_id clk_type rst_type inp out locals ty
             Henvgen Haux Hclk Hrst Hinp Hout Hlocals Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin) as (x & a & _ & Hfind).
        eapply generate_node_env_sec_range; eauto.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin) as (x & a & _ & Hfind).
        eapply generate_node_env_sec_range; eauto.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin) as (x & a & _ & Hfind).
        eapply generate_node_env_sec_range; eauto.
      - subst. eapply generate_node_env_sec_range; eauto.
      - subst. eapply generate_node_env_sec_range; eauto.
    Qed.

    Ltac prove_str_to_pos_neq :=
      intros Heq; apply str_to_pos_injective in Heq; discriminate.

    Lemma sec_not_in_gensym_prefs :
      ~In Ids.sec gensym_prefs.
    Proof.
      unfold gensym_prefs.
      repeat rewrite not_in_cons.
      repeat split; auto; prove_str_to_pos_neq.
    Qed.

    Lemma node_var_not_sec_gensym:
      forall n x i,
        In x (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
        x <> Ids.gensym Ids.sec i.
    Proof.
      intros n x i Hin Heq.
      destruct n.(n_good) as [Hgood _].
      rewrite Forall_forall in Hgood.
      specialize (Hgood _ Hin).
      destruct Hgood as [Hat|Hex].
      - rewrite Heq in Hat.
        eapply gensym_not_atom; eauto.
      - unfold PS.Exists in Hex.
        destruct Hex as (pre & Hinpre & m & Hm).
        rewrite Heq in Hm.
        symmetry in Hm.
        apply gensym_injective in Hm as [Hpre _]. subst pre.
        apply PSP.of_list_1 in Hinpre.
        exact (sec_not_in_gensym_prefs Hinpre).
    Qed.

    (** The next two inversion lemmas package the operational content of the
        generated NLustre/STC signatures. They let the node/system theorem talk
        directly in terms of the underlying constraint generators, rather than
        repeatedly unfolding the large monadic definitions. *)

    Lemma generate_node_sig_inv:
      forall G n env aux_names sig,
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
        exists clk_id rst_id clk_type rst_type inp out locals nconst st_n,
          get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id env = Some clk_type
          /\ Env.find rst_id env = Some rst_type
          /\ get_mappings_from_node n.(n_in) env = Some inp
          /\ get_mappings_from_node n.(n_out) env = Some out
          /\ get_mappings_from_node n.(n_vars) env = Some locals
          /\ generate_eqns_constraints G env clk_type rst_type n.(n_eqs) init_state = OK (nconst, st_n)
          /\ sig = {| s_name := n.(n_name);
                      s_in := inp;
                      s_out := out;
                      s_reset := rst_type;
                      s_clk := clk_type;
                      s_constraints := SymTypes.simplify nconst locals |}.
    Proof.
      intros G n env aux_names sig Hsig.
      unfold SECNLUSTYPING.generate_node_sig in Hsig.
      lazymatch type of Hsig with
      | context [match ?m with | OK _ => _ | Error _ => _ end = _] =>
          remember m as gen_res eqn:Hgen
      end.
      destruct gen_res as [[packed st_res]|]; try discriminate.
      destruct packed as [packed env0].
      destruct packed as [packed packed_constraints].
      destruct packed as [packed packed_clk_type].
      destruct packed as [packed packed_rst_type].
      destruct packed as [packed packed_out].
      destruct packed as [name packed_inp].
      simpl in Hsig.
      inversion Hsig; clear Hsig; subst.
      symmetry in Hgen.
      eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
      eapply sec_bind_inv in Hgen as (clk_type & st_clk & Hclk & Hgen).
      eapply sec_bind_inv in Hgen as (rst_type & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
      eapply sec_bind_inv in Hgen as (locals & st_locals & Hlocals & Hgen).
      eapply sec_bind_inv in Hgen as (nconst & st_n & Hnconst & Hret).
      unfold option_to_sec in Haux.
      destruct (get_node_aux (n.(n_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
      inversion Haux; subst clk_id0 rst_id0 st_aux.
      unfold option_to_sec in Hclk.
      destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
      inversion Hclk; subst clk_type0 st_clk.
      unfold option_to_sec in Hrst.
      destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
      inversion Hrst; subst rst_type0 st_rst.
      unfold option_to_sec in Hinp.
      destruct (get_mappings_from_node (n.(n_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
      inversion Hinp; subst inp0 st_inp.
      unfold option_to_sec in Hout.
      destruct (get_mappings_from_node (n.(n_out)) env) as [out0|] eqn:Hout0; try discriminate.
      inversion Hout; subst out0 st_out.
      unfold option_to_sec in Hlocals.
      destruct (get_mappings_from_node (n.(n_vars)) env) as [locals0|] eqn:Hlocals0; try discriminate.
      inversion Hlocals; subst locals0 st_locals.
      unfold ret in Hret. inversion Hret; subst.
      exists clk_id, rst_id, packed_clk_type, packed_rst_type, packed_inp, packed_out, locals, nconst, st_res.
      repeat split; eauto.
    Qed.

    Lemma generate_sys_signature_inv:
      forall G s env aux_names sig,
        SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
        exists clk_id rst_id clk_type rst_type inp out slocals slasts
               reset_env rids st_reset sconst st_s,
          get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id env = Some clk_type
          /\ Env.find rst_id env = Some rst_type
          /\ get_mappings_from_node s.(SynStc.s_in) env = Some inp
          /\ get_mappings_from_node s.(SynStc.s_out) env = Some out
          /\ get_mappings_from_node s.(SynStc.s_vars) env = Some slocals
          /\ get_mappings_from_node s.(SynStc.s_lasts) env = Some slasts
          /\ generate_reset_env s.(SynStc.s_tcs) init_state = OK ((reset_env, rids), st_reset)
          /\ generate_trconstrs_constraints G env reset_env clk_type rst_type s.(SynStc.s_tcs) st_reset = OK (sconst, st_s)
          /\ sig = {| s_name := s.(SynStc.s_name);
                      s_in := inp;
                      s_out := out;
                      s_reset := rst_type;
                      s_clk := clk_type;
                      s_constraints := SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids) |}.
    Proof.
      intros G s env aux_names sig Hsig.
      unfold SECSTCTYPING.generate_sys_signature in Hsig.
      lazymatch type of Hsig with
      | context [match ?m with | OK _ => _ | Error _ => _ end = _] =>
          remember m as gen_res eqn:Hgen
      end.
      destruct gen_res as [[packed st_res]|]; try discriminate.
      destruct packed as [packed env0].
      destruct packed as [packed packed_constraints].
      destruct packed as [packed packed_clk_type].
      destruct packed as [packed packed_rst_type].
      destruct packed as [packed_inp packed_out].
      simpl in Hsig.
      inversion Hsig; clear Hsig; subst.
      symmetry in Hgen.
      eapply sec_bind2_inv in Hgen as (clk_id & rst_id & st_aux & Haux & Hgen).
      eapply sec_bind_inv in Hgen as (clk_type & st_clk & Hclk & Hgen).
      eapply sec_bind_inv in Hgen as (rst_type & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (out & st_out & Hout & Hgen).
      eapply sec_bind_inv in Hgen as (slocals & st_locals & Hslocals & Hgen).
      eapply sec_bind_inv in Hgen as (slasts & st_lasts & Hslasts & Hgen).
      eapply sec_bind2_inv in Hgen as (reset_env & rids & st_reset & Hresetenv & Hgen).
      eapply sec_bind_inv in Hgen as (sconst & st_s & Hsconst & Hret).
      unfold option_to_sec in Haux.
      destruct (get_node_aux (s.(SynStc.s_name)) aux_names) as [[clk_id0 rst_id0]|] eqn:Haux0; try discriminate.
      inversion Haux; subst clk_id0 rst_id0 st_aux.
      unfold option_to_sec in Hclk.
      destruct (Env.find clk_id env) as [clk_type0|] eqn:Hclk0; try discriminate.
      inversion Hclk; subst clk_type0 st_clk.
      unfold option_to_sec in Hrst.
      destruct (Env.find rst_id env) as [rst_type0|] eqn:Hrst0; try discriminate.
      inversion Hrst; subst rst_type0 st_rst.
      unfold option_to_sec in Hinp.
      destruct (get_mappings_from_node (s.(SynStc.s_in)) env) as [inp0|] eqn:Hinp0; try discriminate.
      inversion Hinp; subst inp0 st_inp.
      unfold option_to_sec in Hout.
      destruct (get_mappings_from_node (s.(SynStc.s_out)) env) as [out0|] eqn:Hout0; try discriminate.
      inversion Hout; subst out0 st_out.
      unfold option_to_sec in Hslocals.
      destruct (get_mappings_from_node (s.(SynStc.s_vars)) env) as [slocals0|] eqn:Hslocals0; try discriminate.
      inversion Hslocals; subst slocals0 st_locals.
      unfold option_to_sec in Hslasts.
      destruct (get_mappings_from_node (s.(SynStc.s_lasts)) env) as [slasts0|] eqn:Hslasts0; try discriminate.
      inversion Hslasts; subst slasts0 st_lasts.
      unfold ret in Hret. inversion Hret; subst.
      exists clk_id, rst_id, packed_clk_type, packed_rst_type, packed_inp, packed_out,
             slocals, slasts, reset_env, rids, st_reset, sconst, st_res.
      repeat split; eauto.
    Qed.

    (** Generated-node theorem.

        This theorem reconstructs the explicit premises of [node_preserv] from
        the generated environment and the two generated signatures. Its proof
        proceeds as follows:

        - [generate_node_sig_inv] and [generate_sys_signature_inv] recover the
          raw lookup equalities and raw constraint generators hidden inside the
          signature constructors;
        - the freshness lemmas above show that reset-instance variables created
          on the STC side cannot belong to the shared NLustre scope;
        - the result is then discharged by a single application of
          [node_preserv]. *)
    Theorem generated_node_preserv:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes n G1 G2 env aux_names nsig ssig Hsec Hsig Happ Henvgen Hnsig Hssig.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & nlocals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hnlocals & Hnconst & Hnsigdef); eauto.
      edestruct generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Haux in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      rewrite Hnsigdef in *.
      rewrite Hssigdef in *.
      exists nlocals, slocals, slasts, rids, nconst, sconst.
      split.
      - repeat split; reflexivity.
      - split; [reflexivity|].
        split; [reflexivity|].
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfind Hin.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfind; clear Hfind; subst.
          edestruct generate_reset_env_range as (nrst & Hrsteq); eauto.
          edestruct node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref. contradiction.
        }
        eapply node_preserv
          with (scope := inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)
               (G1 := G1) (G2 := G2)
               (s := translate_node n)
               (env := env) (reset_env := reset_env)
               (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (clk_type := clk_type) (rst_type := rst_type)
               (inp := inp) (out := out) (locals := nlocals)
               (rids := rids) (nconst := nconst) (sconst := sconst)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s); eauto.
    Qed.

    (** System-lookup corollary.

        Once [generated_node_preserv] is available, the only remaining work is
        to rewrite a [find_system] hypothesis on the translated program back to
        the corresponding source node using [find_system_translate]. *)
    Corollary found_system_preserv:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        find_node f all_nodes = Some n ->
        SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes f n s prog' G1 G2 env aux_names nsig ssig
             Hsec Hsig Happ Henvgen Hfind Hsys Hnsig Hssig.
      eapply find_system_translate in Hsys as (n' & Hfind' & Htr).
      rewrite Hfind in Hfind'. inversion Hfind'. subst n'. subst s.
      eapply generated_node_preserv; eauto.
    Qed.

    (** Structural side conditions for the simplify-completeness bridge.

        The generic theorem [SecTypes.simplify_complete] no longer needs a
        signature-specific semantic axiom. Instead, the generated-node bridge
        only requires the exact concrete facts that theorem consumes:

        - the raw generated NLustre constraints are well formed;
        - the variables eliminated by [simplify] are disjoint from the visible
          signature scope.

        This predicate packages those facts at the level of generated node
        signatures. *)
    Definition generated_node_simplify_ready
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G1 n nsig
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n) ->
        nsig = {| s_name := n.(n_name);
                  s_in := inp;
                  s_out := out;
                  s_reset := rst_type;
                  s_clk := clk_type;
                  s_constraints := SymTypes.simplify raw locals |} ->
        wf_constraints raw
        /\ (forall x, In x locals -> ~ In x (sig_scope nsig)).

    (** Generated-node structural readiness for [simplify_complete].

        This theorem discharges the two source-side obligations in
        [generated_node_simplify_ready] from:

        - the shared generated naming environment, which gives injective
          security names and ensures clock/reset helper names are disjoint from
          user variables;
        - the NLustre node invariant [NoDup_var_defined_n_eqs];
        - the remaining call-instantiation shape assumption on
          [generate_constraints]. *)
    Theorem generated_node_simplify_ready_from_generated_env:
      forall all_nodes env aux_names,
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_simplify_ready env aux_names.
    Proof.
      intros all_nodes env aux_names Henvgen Hcall.
      intros G1 n nsig
             clk_id rst_id clk_type rst_type inp out locals raw st_n
             Hnsig Haux Hclk Hrst Hinp Hout Hlocals Hraw Hnsigdef.
      split.
      - eapply SECNLUSTYPING.generate_node_eqns_constraints_wf; eauto.
        + apply Hcall.
        + eapply generate_node_env_injective; eauto.
      - intros ty Hinlocal Hinsig.
        subst nsig.
        unfold sig_scope in Hinsig.
        repeat rewrite in_app_iff in Hinsig.
        destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hinlocal)
          as (xlocal & alocal & Hxlocal & Hfindlocal).
        pose proof (generate_node_env_injective _ _ _ Henvgen) as Hinj.
        pose proof (generate_node_aux_sec_names _ _ _ _ _ _ Henvgen Haux)
          as (iclk & irst & Hclkid & Hrstid).
        assert (Hndvars : NoDup (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
        { apply fst_NoDupMembers. exact n.(n_nodup). }
        destruct Hinsig as [Hininput|[Hinoutput|[Hinclk|[Hinrst|[]]]]].
        + destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hininput)
            as (xinp & ainp & Hxinp & Hfindinp).
          assert (xlocal = xinp) by (eapply Hinj; eauto).
          subst xinp.
          repeat rewrite map_app in Hndvars.
          eapply (NoDup_app_In xlocal) in Hndvars; eauto.
          apply Hndvars.
          apply in_or_app. left. now apply in_map with (f := fst) in Hxlocal.
        + destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hinoutput)
            as (xout & aout & Hxout & Hfindout).
          assert (xlocal = xout) by (eapply Hinj; eauto).
          subst xout.
          repeat rewrite map_app in Hndvars.
          eapply (NoDup_app_In xlocal) in Hndvars.
          2:{ apply in_or_app. right. now apply in_map with (f := fst) in Hxout. }
          apply Hndvars.
          apply in_or_app. right. now apply in_map with (f := fst) in Hxlocal.
        + destruct Hinclk as [Heq|[]]. subst ty.
          assert (xlocal = clk_id) by (eapply Hinj; eauto).
          subst xlocal.
          eapply node_var_not_sec_gensym.
          * apply in_or_app. right. apply in_or_app. left.
            now apply in_map with (f := fst) in Hxlocal.
          * now rewrite Hclkid.
        + destruct Hinrst as [Heq|[]]. subst ty.
          assert (xlocal = rst_id) by (eapply Hinj; eauto).
          subst xlocal.
          eapply node_var_not_sec_gensym.
          * apply in_or_app. right. apply in_or_app. left.
            now apply in_map with (f := fst) in Hxlocal.
          * now rewrite Hrstid.
    Qed.

    Lemma sig_scope_in_raw_scope:
      forall sig locals x,
        In x (sig_scope sig) ->
        In x (sig.(s_in) ++ sig.(s_out) ++ locals ++ sig.(s_clk) :: sig.(s_reset) :: nil).
    Proof.
      intros sig locals x Hin.
      unfold sig_scope in Hin.
      repeat rewrite in_app_iff in *.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]];
        try (now left);
        try (now right; right; right; left);
        try (now right; right; right; right; left).
    Qed.

    (** This theorem is the concrete connection point between the generic
        [SecTypes.simplify_complete] metatheory and the NLustre/STC
        translation proof.

        Flow:
        - [generated_node_preserv] gives preservation for the raw NLustre/STC
          constraints before signature simplification;
        - [generated_node_simplify_ready] supplies the two structural facts
          needed to invert the NLustre-side [simplify];
        - [SecTypes.simplify_complete] reconstructs a satisfying valuation for
          the raw NLustre constraints while preserving the visible signature
          scope;
        - [simplify_is_correct] pushes the resulting STC valuation back down
          to the stored simplified STC signature. *)
    Theorem generated_signatures_preserved_from_simplify_bridge:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        generated_node_simplify_ready env aux_names ->
        signatures_preserved nsig ssig.
    Proof.
      intros all_nodes n G1 G2 env aux_names nsig ssig
             Hsec Hcons Happ Henvgen Hnsig Hssig Hready.
      edestruct generated_node_preserv as
          (nlocals & slocals & slasts & rids & nconst & sconst
           & Hfields & Hnsigcstr & Hssigcstr & Hrawpres); eauto.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hnsigdef); eauto.
      destruct (Hready G1 n nsig
                  clk_id rst_id clk_type rst_type inp out locals raw st_n
                  Hnsig Haux Hclk Hrst Hinp Hout Hlocals Hraw Hnsigdef)
        as [Hwf Hdisj].
      rewrite Hnsigdef in Hnsigcstr.
      inversion Hnsigcstr; subst nlocals nconst.
      split; [exact Hfields|].
      unfold preserves_on.
      intros dlt Hsat.
      edestruct simplify_complete
        as (dlt1 & Hagree1 & Hrawsat1); eauto.
      edestruct Hrawpres as (dlt2 & Hagree2 & Hrawsat2); eauto.
      exists dlt2. split.
      - intros x Hin.
        rewrite <- (Hagree1 x Hin).
        apply Hagree2.
        eapply sig_scope_in_raw_scope; eauto.
      - rewrite Hssigcstr.
        eapply simplify_is_correct; eauto.
        eapply simplify_simplifyRel.
        reflexivity.
    Qed.

    (** Call-instantiation metatheory.

        The remaining step from [signatures_preserved] to
        [Signature_call_preserves] is semantic rather than translation-specific:
        the stored signature constraints must behave well under call-time
        substitution. The definitions in this block make the exact remaining
        requirements explicit.

        - [signature_scoped] says that the stored signature constraints mention
          only the interface variables plus clock/reset.
        - [call_subst_fresh] says that the actual caller-side names/types used
          to instantiate a callee signature are fresh with respect to that
          formal signature scope.

        When both properties hold, the source and target signatures can be
        instantiated against the same caller valuation without accidentally
        capturing callee-local names. *)

    (** Scope/substitution metatheory lives in [SIFSignature].

        The translation proof only keeps the [simplify]-specific lemmas local.
        Everything about how call-time signature instantiation transforms
        scoped constraints is proved once in the signature layer and imported
        here through [SIG]. *)

    (** Generic scope metatheory for [findST], [subST], [subAll], and
        [simplify] now lives in [SecTypes].  The translation proof only uses
        the imported lemmas, rather than carrying local copies here. *)

    Definition type_fresh (scope: list ident) (st: ST) : Prop :=
      Forall (fun x => ~ In x scope) st.

    Definition types_fresh (scope: list ident) (sts: list ST) : Prop :=
      Forall (type_fresh scope) sts.

    Definition outputs_fresh (scope: list ident) (outs: list ident) : Prop :=
      Forall (fun x => ~ In x scope) outs.

    Definition call_subst_fresh
      (sig: signature) (inptyp: list ST) (ckty rstty: ST) (outtyp: list ident) : Prop :=
      types_fresh (sig_scope sig) inptyp
      /\ type_fresh (sig_scope sig) ckty
      /\ type_fresh (sig_scope sig) rstty
      /\ outputs_fresh (sig_scope sig) outtyp.

    (** Global freshness assumption for successful call instantiations.

        This is lower-level than the previous [signature_calls_from_preservation]
        placeholder: it talks only about the substitution interface exported by
        [generate_constraints]. In the intended finished development, this
        should be discharged from the shared name-generation environment in
        [NameInterface] together with the fact that generated signatures are
        scoped to their visible interface. *)
    Definition successful_call_substitutions_fresh : Prop :=
      forall sig inptyp ckty rstty outtyp cns st_init st',
        generate_constraints sig inptyp ckty rstty outtyp st_init = OK (cns, st') ->
        call_subst_fresh sig inptyp ckty rstty outtyp.

    Definition upd_type (dlt: ident -> Lat.t) (x: ident) (st: ST) : ident -> Lat.t :=
      fun y => if ident_eqb y x then hm_ext dlt st else dlt y.

    Definition upd_ident (dlt: ident -> Lat.t) (x v: ident) : ident -> Lat.t :=
      fun y => if ident_eqb y x then dlt v else dlt y.

    (** The remaining gap to a fully proved signature-step theorem is not in
        the global induction; it is in the semantic bridge from generated raw
        node/system constraints to the simplified modular signatures used at
        call sites.

        The two obligations below isolate that gap exactly:

        - [signatures_preserved] must be derivable for generated signatures,
          typically from [generated_node_preserv] plus a completeness result
          for [SymTypes.simplify];
        - [Signature_call_preserves] must follow from
          [signatures_preserved], via a semantic correctness theorem for
          [generate_constraints] under consistent fresh-name instantiations.

        Once these two bridge lemmas are available, the abstract
        [generated_signature_step_consistent] hypothesis used by the global
        theorems is no longer needed. *)

    Lemma generated_signature_name_agree:
      forall G1 G2 n env aux_names nsig ssig,
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        nsig.(s_name) = ssig.(s_name).
    Proof.
      intros G1 G2 n env aux_names nsig ssig Hnsig Hssig.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts & Hresetenv & Hsconst & Hssigdef); eauto.
      rewrite Hnsigdef, Hssigdef. reflexivity.
    Qed.

    Theorem generated_signature_step_consistent_from_bridges:
      forall all_nodes env aux_names,
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1 G2 n nsig ssig,
            Signature_consistent G1 G2 ->
            SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
            SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
            signatures_preserved nsig ssig) ->
        (forall nsig ssig,
            signatures_preserved nsig ssig ->
            Signature_call_preserves nsig ssig) ->
        generated_signature_step_consistent env aux_names.
    Proof.
      intros all_nodes env aux_names Henvgen Hsigpres Hcall.
      unfold generated_signature_step_consistent.
      intros G1 G2 n nsig ssig Hcons Hnsig Hssig.
      split.
      - eapply generated_signature_name_agree; eauto.
      - destruct (Hsigpres G1 G2 n nsig ssig Hcons Hnsig Hssig) as [Hfields Hpres].
        split; [exact Hfields|].
        eapply Hcall. split; eauto.
    Qed.

    (** Concrete bridge premises.

        The abstract step theorem above only needs two semantic ingredients:

        - structural side conditions that let [SecTypes.simplify_complete]
          reconstruct raw generated NLustre constraints from the stored
          simplified signature;
        - call-level preservation derived from [signatures_preserved], which is
          where the later fresh-name instantiation metatheory belongs.

        The definitions below package those requirements explicitly so the
        public node/system/program theorems do not need to mention the opaque
        predicate [generated_signature_step_consistent]. *)
    Definition generated_node_simplify_ready_global
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      generated_node_simplify_ready env aux_names.

    Corollary generated_node_simplify_ready_global_from_call_shape:
      forall all_nodes env aux_names,
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_simplify_ready_global env aux_names.
    Proof.
      intros all_nodes env aux_names Henvgen Hcall.
      exact (generated_node_simplify_ready_from_generated_env _ _ _ Henvgen Hcall).
    Qed.

    Definition generated_signatures_preserved
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G1 G2 n nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        signatures_preserved nsig ssig.

    Definition generated_node_signatures_scoped
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G n nsig,
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK nsig ->
        signature_scoped nsig.

    (** The node-side scopedness theorem now lives in [SecNLusTyping.v]:
        [SECNLUSTYPING.generate_node_sig_scoped] proves the local one-node
        result, and [SECNLUSTYPING.generate_all_signatures_scoped] lifts it to
        a fully generated NLustre signature environment under the standard
        source [wc_global] premise.

        The pointwise predicate kept here is therefore stronger than what the
        final theorem should expose.  It remains only because the current
        translation-layer step theorem is still phrased for arbitrary
        accumulators; once that step is refactored to consume generated globals
        directly, this premise should disappear.  On the STC side, the base
        scopedness theorems now live in [SecSTCTyping.v]
        ([generate_sys_signature_scoped] and
        [generate_all_sys_signatures_scoped]); this stronger pointwise wrapper
        remains here only because the translation-layer step theorem is still
        phrased over arbitrary accumulator globals. *)
    Definition generated_system_signatures_scoped
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G s ssig,
        SECSTCTYPING.generate_sys_signature G s env aux_names = OK ssig ->
        signature_scoped ssig.

    (** This is the semantic call bridge that still has to come from the
        signature-instantiation layer.

        Unlike the older placeholder [signature_calls_from_preservation], this
        formulation exposes the actual low-level requirements:

        - stored signatures must be scoped to their visible interface;
        - successful instantiations produced by [generate_constraints] must use
          caller-side names that are fresh with respect to that scope.

        Once the corresponding metatheory is proved in the signature layer,
        this premise should disappear entirely. *)
    Definition signatures_preserved_calls : Prop :=
      successful_call_substitutions_fresh ->
      forall nsig ssig,
        signature_scoped nsig ->
        signature_scoped ssig ->
        signatures_preserved nsig ssig ->
        Signature_call_preserves nsig ssig.

    (** Generated signatures satisfy the weak signature theorem as soon as the
        remaining concrete call-shape premise reconstructs the derived
        generated-node readiness predicate used by [simplify_complete]. *)
    Corollary generated_signatures_preserved_from_simplify_complete:
      forall all_nodes env aux_names,
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_signatures_preserved env aux_names.
    Proof.
      intros all_nodes env aux_names Hsec Happ Henvgen Hcallshape.
      pose proof (generated_node_simplify_ready_global_from_call_shape
                    all_nodes env aux_names Henvgen Hcallshape) as Hready.
      unfold generated_signatures_preserved.
      intros G1 G2 n nsig ssig Hcons Hnsig Hssig.
      eapply generated_signatures_preserved_from_simplify_bridge; eauto.
    Qed.

    Corollary generated_signature_step_consistent_concrete:
      forall all_nodes env aux_names,
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_signatures_scoped env aux_names ->
        generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        generated_signature_step_consistent env aux_names.
    Proof.
      intros all_nodes env aux_names Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall.
      eapply generated_signature_step_consistent_from_bridges; eauto.
      eapply generated_signatures_preserved_from_simplify_complete; eauto.
      intros nsig ssig Hpres.
      eapply Hcall; eauto.
    Qed.

    (** Global-signature extension.

        Once the new NLustre/STC signatures for one processed node are known to
        satisfy [Signature_head_consistent], adding them to already-consistent
        accumulators preserves global [Signature_consistent]. This is the basic
        step needed for the induction over [generate_all_signatures'] and
        [generate_all_sys_signatures']. *)
    Lemma Signature_consistent_nil:
      Signature_consistent nil nil.
    Proof.
      intros f n1 Hfind.
      simpl in Hfind. discriminate.
    Qed.

    Theorem Signature_consistent_cons:
      forall G1 G2 nsig ssig,
        Signature_consistent G1 G2 ->
        Signature_head_consistent nsig ssig ->
        Signature_consistent (nsig :: G1) (ssig :: G2).
    Proof.
      intros G1 G2 nsig ssig Hcons Hhead f n1 Hfind.
      simpl in Hfind.
      destruct (ident_eqb nsig.(s_name) f) eqn:Hname.
      - destruct Hhead as [Hsgname Hhead].
        apply ident_eqb_eq in Hname. inversion Hfind; subst n1.
        exists ssig. simpl. rewrite <- Hsgname, Hname, ident_eqb_refl.
        split; [reflexivity|].
        split; [exact Hsgname|exact Hhead].
      - apply ident_eqb_neq in Hname.
        destruct Hhead as [Hsgname Hhead].
        specialize (Hcons f n1 Hfind) as (n2 & Hfind2 & Hhead2).
        assert (Hssigname : ssig.(s_name) <> f).
        { rewrite <- Hsgname. exact Hname. }
        assert (Hneqb : ident_eqb ssig.(s_name) f = false).
        { apply ident_eqb_neq. exact Hssigname. }
        exists n2. simpl. rewrite Hneqb. auto.
    Qed.

    (** The source-side generated-global scopedness theorem now belongs to the
        NLustre typing layer.  This corollary is just the translation-facing
        bridge from [generate_node_env] to the typing theorem's injective-env
        premise. *)
    Corollary generate_all_source_signatures_scoped:
      forall all_nodes env aux_names G,
        SECNLUSTYPING.Clo.wc_global all_nodes ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros all_nodes env aux_names G Hwc Henvgen Hcallshape Hgen.
      eapply SECNLUSTYPING.generate_all_signatures_scoped; eauto.
      eapply generate_node_env_injective; eauto.
    Qed.

    Corollary generate_all_translated_system_signatures_scoped:
      forall all_nodes env aux_names G,
        SECSTCTYPING.Clo.wc_program (translate all_nodes) ->
        (forall G1, call_constraints_shape G1) ->
        SECSTCTYPING.env_injective env ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros all_nodes env aux_names G Hwc Hcallshape Hinj Hgen.
      eapply SECSTCTYPING.generate_all_sys_signatures_scoped; eauto.
    Qed.

    (** This is the generated-signature form of [Signature_consistent_cons].
        The generation equalities do not contribute to the proof directly, but
        they make the statement line up with the accumulator step of the global
        generators and with the intended later use: once a theorem establishes
        [Signature_head_consistent] for the newly generated pair, the global
        invariant extends immediately. *)
    Theorem generated_signature_consistent_step:
      forall G1 G2 n env aux_names nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        Signature_head_consistent nsig ssig ->
        Signature_consistent (nsig :: G1) (ssig :: G2).
    Proof.
      intros. eapply Signature_consistent_cons; eauto.
    Qed.

    (** Per-step compatibility hypothesis used by the global generators.

        The present development does not yet prove this property directly from
        [generated_node_preserv], because that would require a completeness
        argument for [SymTypes.simplify] with respect to call-time signature
        instantiation. Instead, the global theorems below isolate that missing
        bridge into this single hypothesis. *)
    Definition generated_signature_step_consistent
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall acc1 acc2 n nsig ssig,
        Signature_consistent acc1 acc2 ->
        SECNLUSTYPING.generate_node_sig acc1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names = OK ssig ->
        Signature_head_consistent nsig ssig.

    (** Abstract list induction over generated signatures.

        The theorem isolates the accumulator argument from the still-separate
        theorem that one freshly generated node/system signature pair satisfies
        [Signature_head_consistent]. Once such a per-step theorem is available,
        this induction lifts it to the entire generated global/program
        signature lists. *)
    Theorem generate_all_signatures_consistent'_abstract:
      forall nodes acc1 acc2 env aux_names G1 G2,
        Signature_consistent acc1 acc2 ->
        generated_signature_step_consistent env aux_names ->
        SECNLUSTYPING.generate_all_signatures' acc1 nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures' acc2 (translate nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      induction nodes as [|n nodes IH]; intros acc1 acc2 env aux_names G1 G2
                                            Hcons Hstep Hnl Hstc.
      - simpl in Hnl, Hstc. inversion Hnl; inversion Hstc; subst. exact Hcons.
      - simpl in Hnl, Hstc.
        destruct (SECNLUSTYPING.generate_node_sig acc1 n env aux_names) as [nsig|] eqn:Hnsig;
          try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures' (nsig :: acc1) nodes env aux_names) as [G1'|] eqn:Hnl';
          try discriminate.
        inversion Hnl; subst; clear Hnl.
        destruct (SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names) as [ssig|] eqn:Hssig;
          try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures' (ssig :: acc2) (translate nodes) env aux_names) as [G2'|] eqn:Hstc';
          try discriminate.
        inversion Hstc; subst; clear Hstc.
        eapply IH with (acc1 := nsig :: acc1) (acc2 := ssig :: acc2); eauto.
        eapply Signature_consistent_cons; eauto.
    Qed.

    Corollary generate_all_signatures_consistent_abstract:
      forall nodes env aux_names G1 G2,
        generated_signature_step_consistent env aux_names ->
        SECNLUSTYPING.generate_all_signatures nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros nodes env aux_names G1 G2 Hstep Hnl Hstc.
      unfold SECNLUSTYPING.generate_all_signatures in Hnl.
      unfold SECSTCTYPING.generate_all_sys_signatures in Hstc.
      eapply generate_all_signatures_consistent'_abstract with (acc1 := []) (acc2 := []); eauto.
      apply Signature_consistent_nil.
    Qed.

    (** Concrete global-signature theorem.

        This is the version intended for later use in the development: the
        caller provides the concrete bridge premises, and the abstract
        accumulator invariant is rebuilt internally.  The older derived
        assumption [generated_node_simplify_ready_global] is no longer exposed:
        it is reconstructed from [generate_node_env] and the remaining
        call-shape premise. *)
    Corollary generate_all_signatures_consistent:
      forall all_nodes env aux_names G1 G2,
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_signatures_scoped env aux_names ->
        generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros all_nodes env aux_names G1 G2
             Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc.
      eapply generate_all_signatures_consistent_abstract; eauto.
      eapply generated_signature_step_consistent_concrete; eauto.
    Qed.

    (** Closed node theorem for globally generated signatures under the
        concrete bridge premises.

        This is the first point where the explicit [Signature_consistent]
        premise disappears from the node-level statement. The theorem rebuilds
        that premise from the full generated signature lists by combining:

        1. generated signature simplification completeness;
        2. call preservation derived from [signatures_preserved];
        3. the abstract list induction [generate_all_signatures_consistent_abstract];
        4. the pointwise generated-node theorem [generated_node_preserv]. *)
    Theorem generated_node_preserv_global:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_signatures_scoped env aux_names ->
        generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes n G1 G2 env aux_names nsig ssig
             Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc Hnsig Hssig.
      pose proof (generate_all_signatures_consistent
                    all_nodes env aux_names G1 G2 Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc) as Hcons.
      eapply generated_node_preserv; eauto.
    Qed.

    (** Lookup-based closed node theorem.

        Compared with [found_system_preserv], the signature-consistency premise
        is now discharged internally from the global generation equalities. *)
    Corollary found_system_preserv_global:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_signatures_scoped env aux_names ->
        generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        find_node f all_nodes = Some n ->
        SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes f n s prog' G1 G2 env aux_names nsig ssig
             Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc Hfind Hsys Hnsig Hssig.
      pose proof (generate_all_signatures_consistent
                    all_nodes env aux_names G1 G2 Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc) as Hcons.
      eapply found_system_preserv; eauto.
    Qed.

    (** Program-level preservation property.

        This packages the lookup corollary so that the final theorem can state
        directly that every translated system found in the target program
        satisfies the same raw preservation relation as its source node. *)
    Definition generated_program_preserves
      (all_nodes: global)
      (env: Env.t ident)
      (aux_names: list node_aux_names)
      (G1 G2: secglobal) : Prop :=
      forall f n s prog' nsig ssig,
        find_node f all_nodes = Some n ->
        SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.

    (** Final program theorem.

        The final program theorem no longer exposes the derived readiness
        predicate [generated_node_simplify_ready_global].  Instead it keeps the
        remaining lower-level premise that still has to be discharged above
        this layer:

        - [call_constraints_shape] for the shared generated env;
        - generated NLustre/STC signatures are scoped to their visible
          interfaces;
        - weak signature preservation is stable under call-time instantiation.

        From those ingredients, the abstract per-step compatibility invariant
        is rebuilt internally, and every translated system in the program
        satisfies the node-level raw preservation theorem without an explicit
        [Signature_consistent] premise. *)
    Theorem generated_program_preserv_global:
      forall all_nodes (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names),
        Ids.sec <> Ids.sec_reset ->
        (forall scope, preserves_on_app_closed scope) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1, call_constraints_shape G1) ->
        generated_node_signatures_scoped env aux_names ->
        generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        generated_program_preserves all_nodes env aux_names G1 G2.
    Proof.
      intros all_nodes G1 G2 env aux_names
             Hsec Happ Henvgen Hcallshape Hnscoped Hsscoped Hfreshcalls Hcall Hallnl Hallstc.
      intros f n s prog' nsig ssig Hfind Hsys Hnsig Hssig.
      eapply found_system_preserv_global; eauto.
    Qed.
  End NODESYSPRES.



End SECNLUSSTCTRANSLATION.


Module SecNLusStcTranslation 
  (Ids   : IDS)
  (Lat   : Lattice)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (SecTypes : SECTYPES Lat)
  (CESyn : CESYNTAX Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SynStc: STCSYNTAX Ids Op CESyn)
  (Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (SIG          : SIGNATURE   Ids SC)
  (NAMEGEN      : NAMEGEN Ids Op CESyn SynNL)
  (SECCETYPING  : SECCETYPING Ids Op CESyn)
  (SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING)
  (SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING) <: SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG NAMEGEN SECCETYPING SECNLUSTYPING SECSTCTYPING.

  Include SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG NAMEGEN SECCETYPING SECNLUSTYPING SECSTCTYPING.
End SecNLusStcTranslation.
