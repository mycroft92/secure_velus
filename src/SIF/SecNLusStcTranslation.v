(*** Translation preservation from NLustre typing constraints to STC typing constraints.

     This file proves a deliberately weak preservation statement.

     - We do not require the NLustre and STC valuations to coincide everywhere.
     - We only require agreement on a chosen list of shared variables.
     - STC is allowed to introduce additional auxiliary variables, in particular
       reset-instance variables created during the STC translation.

     The proof is organised in three layers:

     1. [eqn_preserv]: one NLustre equation versus the STC constraints produced
        by [translate_eqn].
     2. [eqns_preserv_scoped]: extension to a list of equations through the
        scoped concatenation argument.
     3. [node_preserv_scoped]: instantiation of the list-level theorem for a
        translated
        node/system pair, with the scope chosen to be the interface variables,
        locals, clock type, and reset type. *)
From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import NLustre.Memories.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.
From Velus Require Import Clocks.

From Coq Require Import String. (*Required for Errors *)
From Coq Require Import Program.Equality.
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
  (Import CEIsF        : CEISFREE Ids Op CESyn)
  (Import CEClo        : CECLOCKING Ids Op CESyn)
  (Import OrdNL        : NLORDERED Ids Op CESyn SynNL)
  (Import IsD          : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsFNL        : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import CloNL        : NLCLOCKING Ids Op CESyn SynNL OrdNL Mem IsD CEIsF IsFNL CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
  (Import SECNLUSTYPINGCORRECTNESS
      : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL SECNLUSTYPING)
  (Import Last         : STCISLAST Ids Op CESyn SynStc)
  (Import Var          : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def          : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst         : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc       : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsFStc       : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc       : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc)
  (Import SECSTCTYPINGCORRECTNESS
      : SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING).
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
        prove in this development is the raw-constraint theorem
        [node_preserv_scoped] below. *)
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

    (** Satisfaction is extensional on the variables a constraint actually
        mentions.  This is the semantic principle behind scoped composition:
        independently constructed witnesses compose once each target block is
        known to depend only on the shared scope together with its own private
        auxiliary variables. *)
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
        intros y Hy.
        eapply Hsc.
        unfold constraint_scope in *. simpl in *. right. exact Hy.
      }
      assert (Hrhs: hm_ext dlt1 rhs = hm_ext dlt2 rhs).
      {
        clear Hsat Hlhs.
        induction rhs as [|x xs IH]; simpl; auto.
        rewrite (Hagree x).
        2:{ eapply constraint_scoped_rhs; eauto. now left. }
        rewrite IH; auto.
        intros y Hy.
        eapply Hsc.
        unfold constraint_scope in *. simpl in *.
        apply in_app_iff in Hy.
        apply in_app_iff.
        destruct Hy as [Hy|Hy].
        + left. exact Hy.
        + right. right. exact Hy.
      }
      rewrite <- Hlhs.
      rewrite <- Hrhs.
      exact Hsat.
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

    Lemma constraint_scoped_incl:
      forall scope1 scope2 c,
        incl scope1 scope2 ->
        constraint_scoped scope1 c ->
        constraint_scoped scope2 c.
    Proof.
      intros scope1 scope2 c Hincl Hsc x Hin.
      apply Hincl, Hsc, Hin.
    Qed.

    Lemma constraints_scoped_incl:
      forall scope1 scope2 cns,
        incl scope1 scope2 ->
        constraints_scoped scope1 cns ->
        constraints_scoped scope2 cns.
    Proof.
      intros scope1 scope2 cns Hincl Hsc.
      induction Hsc as [|c cns Hc Hcs IH]; constructor.
      - eapply constraint_scoped_incl; eauto.
      - exact IH.
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
      exfalso.
      eapply (Hfresh x); eauto.
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

    (** Scoped concatenation of weak-preservation witnesses.

        Two independently proved preservation facts can be composed provided
        the target-side
        auxiliary variables are:

        - scoped to [scope ++ extras_i] for each block;
        - pairwise fresh across the two blocks;
        - outside the shared scope [scope].

        In the NLustre-to-STC development, the intended instantiation is:

        - [scope] = node interface/local variables shared across phases;
        - [extras_i] = the STC-only reset-instance variables introduced by the
          translation of one equation.

        The later equation-list theorem should therefore combine:

        - one-step preservation for the head equation;
        - the induction hypothesis for the tail;
        - per-equation scopedness/freshness facts for translated reset calls. *)
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
      unfold listSatisfiable in Hsat.
      rewrite Forall_app in Hsat.
      destruct Hsat as [Hsat1 Hsat2].
      destruct (Hpres1 dlt Hsat1) as (dlt1 & Hagree1 & Ht1).
      destruct (Hpres2 dlt Hsat2) as (dlt2 & Hagree2 & Ht2).
      set (dlt' := agree_on_notin scope extras1 dlt1
                     (agree_on_notin scope extras2 dlt2 dlt)).
      exists dlt'. split.
      - intros x Hin.
        unfold dlt', agree_on_notin.
        destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
        + exfalso.
          eapply (Hfresh x).
          * now apply in_or_app; left.
          * exact Hin.
        + destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
          * exfalso.
            eapply (Hfresh x).
            -- now apply in_or_app; right.
            -- exact Hin.
          * reflexivity.
      - unfold listSatisfiable. rewrite Forall_app. split.
        + eapply listSatisfiable_ext.
          * exact Hsc1.
          * unfold dlt'. intros x Hin.
            unfold agree_on_notin.
            destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
            -- reflexivity.
            -- destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
               ++ exfalso.
                  apply in_app_iff in Hin.
                  destruct Hin as [Hinscope|Hin1'].
                  ** assert (Hin12: In x (extras1 ++ extras2)).
                     { apply in_app_iff. right. exact Hin2. }
                     pose proof (Hfresh x Hin12) as Hninscope.
                     contradiction.
                  ** apply Hnin1. exact Hin1'.
               ++ symmetry. apply Hagree1.
                  apply in_app_iff in Hin.
                  destruct Hin as [Hinscope|Hin1'].
                  ** exact Hinscope.
                  ** contradiction.
          * exact Ht1.
        + eapply listSatisfiable_ext.
          * exact Hsc2.
          * unfold dlt'. intros x Hin.
            unfold agree_on_notin.
            destruct (in_dec ident_eq_dec x extras1) as [Hin1|Hnin1].
            -- exfalso.
               apply in_app_iff in Hin.
               destruct Hin as [Hinscope|Hin2].
               ++ assert (Hin12: In x (extras1 ++ extras2)).
                  { apply in_app_iff. left. exact Hin1. }
                  pose proof (Hfresh x Hin12) as Hninscope.
                  contradiction.
               ++ assert (~ In x extras2).
                  { intro Hcontra.
                    eapply (NoDup_app_In x) in Hnd; eauto. }
                  contradiction.
            -- destruct (in_dec ident_eq_dec x extras2) as [Hin2|Hnin2].
               ++ reflexivity.
               ++ symmetry. apply Hagree2.
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

    Lemma preserves_on_weaken:
      forall scope1 scope2 c1 c2,
        incl scope1 scope2 ->
        preserves_on scope2 c1 c2 ->
        preserves_on scope1 c1 c2.
    Proof.
      intros scope1 scope2 c1 c2 Hincl Hpres dlt Hsat.
      destruct (Hpres dlt Hsat) as (dlt' & Hagree & Htgt).
      exists dlt'. split; [|exact Htgt].
      intros x Hin.
      apply Hagree, Hincl, Hin.
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
      | nil => nil
      | e :: eqs' =>
          match reset_call_var e with
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
      { inversion Hin. }
      destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp]; simpl in *.
      { right. exact (IH _ Hin). }
      {
        destruct xs as [|x0 xs']; simpl in *.
        { exact (IH _ Hin). }
        destruct orst as [[r ckr]|]; simpl in *.
        { destruct Hin as [Heq|Hin].
          - subst x. simpl. now left.
          - simpl. right. apply in_app_iff. right. exact (IH _ Hin). }
        { right. apply in_app_iff. right. exact (IH _ Hin). }
      }
      { right. exact (IH _ Hin). }
    Qed.

    Lemma reset_call_vars_nodup:
      forall eqs,
        NoDup (vars_defined eqs) ->
        NoDup (reset_call_vars eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros Hnd.
      - constructor.
      - destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp]; simpl in *.
        + apply NoDup_cons_iff in Hnd as [_ Htail].
          exact (IH Htail).
        + destruct xs as [|x0 xs']; simpl in *.
          * exact (IH Hnd).
          * destruct orst as [[r ckr]|]; simpl in *.
            -- apply NoDup_cons.
               ++ intro Hin.
                  apply (reset_call_vars_in_vars_defined eqs) in Hin.
                  apply NoDup_cons_iff in Hnd as [Hnin _].
                  apply Hnin.
                  apply in_app_iff. right. exact Hin.
               ++ apply IH.
                  apply NoDup_cons_iff in Hnd as [_ Htail].
                  eapply NoDup_app_r. exact Htail.
            -- apply IH.
               apply NoDup_cons_iff in Hnd as [_ Htail].
               eapply NoDup_app_r. exact Htail.
        + apply NoDup_cons_iff in Hnd as [_ Htail].
          exact (IH Htail).
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

    (** Concrete reset-instance extras used by translated equation blocks.

        A resettable NLustre call introduces exactly one STC-only auxiliary
        identifier, obtained by looking up the call's leading output in the
        reset-instance environment built for the translated system.  The list
        version mirrors [reset_call_vars] and will later be used to track the
        private variables threaded through the scoped concatenation proof. *)
    Definition eqn_reset_extras (rst_env: Env.t ident) (eq: equation)
      : option (list ident) :=
      match reset_call_var eq with
      | Some x =>
          match Env.find x rst_env with
          | Some ty => Some (ty :: nil)
          | None => None
          end
      | None => Some nil
      end.

    Fixpoint eqns_reset_extras (rst_env: Env.t ident) (eqs: list equation)
      : option (list ident) :=
      match eqs with
      | nil => Some nil
      | eq :: eqs' =>
          match eqn_reset_extras rst_env eq, eqns_reset_extras rst_env eqs' with
          | Some tys1, Some tys2 => Some (tys1 ++ tys2)
          | _, _ => None
          end
      end.

    Lemma find_env_of_Env_find:
      forall env x ty st,
        Env.find x env = Some ty ->
        find_env x env st = OK (ty, st).
    Proof.
      intros env x ty st Hfind.
      unfold find_env. rewrite Hfind. reflexivity.
    Qed.

    Lemma get_mappings_In_here:
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

    Lemma eqns_reset_extras_eq_get_mappings:
      forall eqs rst_env,
        eqns_reset_extras rst_env eqs = get_mappings (reset_call_vars eqs) rst_env.
    Proof.
      induction eqs as [|eq eqs IH]; intros rst_env; simpl.
      - reflexivity.
      - destruct (reset_call_var eq) as [x|] eqn:Hreset.
        + unfold eqn_reset_extras. rewrite Hreset. simpl.
          destruct (Env.find x rst_env) as [ty|] eqn:Hfind; simpl.
          * rewrite IH.
            destruct (get_mappings (reset_call_vars eqs) rst_env) as [tys|] eqn:Htail;
              reflexivity.
          * reflexivity.
        + unfold eqn_reset_extras. rewrite Hreset. simpl.
          rewrite IH.
          destruct (get_mappings (reset_call_vars eqs) rst_env) as [tys|] eqn:Htail;
            reflexivity.
    Qed.

    Lemma eqns_reset_extras_complete:
      forall rst_env eqs tys x ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In x (reset_call_vars eqs) ->
        Env.find x rst_env = Some ty ->
        In ty tys.
    Proof.
      intros rst_env eqs tys x ty Hextras Hin Hfind.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      destruct (get_mappings_in _ _ _ _ Hin Hextras) as (ty' & Hfind' & Hin').
      rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. exact Hin'.
    Qed.

    Lemma eqns_reset_extras_In:
      forall rst_env eqs tys ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In ty tys ->
        exists x,
          In x (reset_call_vars eqs)
          /\ Env.find x rst_env = Some ty.
    Proof.
      intros rst_env eqs tys ty Hextras Hin.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      eapply get_mappings_In_here; eauto.
    Qed.

    Lemma eqns_reset_extras_nodup:
      forall rst_env eqs tys,
        NoDup (reset_call_vars eqs) ->
        SECSTCTYPING.env_injective rst_env ->
        eqns_reset_extras rst_env eqs = Some tys ->
        NoDup tys.
    Proof.
      intros rst_env eqs tys Hnd Hinj Hextras.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      eapply SECSTCTYPING.get_mappings_nodup; eauto.
    Qed.

    Lemma eqns_reset_extras_fresh:
      forall rst_env eqs tys scope,
        eqns_reset_extras rst_env eqs = Some tys ->
        (forall x rst_inst st1 st2,
            find_env x rst_env st1 = OK (rst_inst, st2) ->
            ~ In rst_inst scope) ->
        forall ty, In ty tys -> ~ In ty scope.
    Proof.
      intros rst_env eqs tys scope Hextras Hfresh ty Hin HinScope.
      destruct (eqns_reset_extras_In _ _ _ _ Hextras Hin) as (x & Hinx & Hfind).
      eapply (Hfresh x ty init_state init_state).
      - eapply find_env_of_Env_find; eauto.
      - exact HinScope.
    Qed.

    Lemma get_mappings_exists:
      forall xs env,
        (forall x, In x xs -> exists ty, Env.find x env = Some ty) ->
        exists tys, get_mappings xs env = Some tys.
    Proof.
      induction xs as [|x xs IH]; intros env Hfind.
      - exists nil. reflexivity.
      - destruct (Hfind x) as [ty Hxty]; [left; reflexivity|].
        destruct (IH env) as [tys Htys].
        + intros y Hy. apply Hfind. right. exact Hy.
        + exists (ty :: tys). simpl. rewrite Hxty, Htys. reflexivity.
    Qed.

    Lemma eqns_reset_extras_exists:
      forall rst_env eqs,
        (forall x, In x (reset_call_vars eqs) -> exists ty, Env.find x rst_env = Some ty) ->
        exists tys, eqns_reset_extras rst_env eqs = Some tys.
    Proof.
      intros rst_env eqs Hfind.
      rewrite eqns_reset_extras_eq_get_mappings.
      eapply get_mappings_exists; eauto.
    Qed.

    Lemma trconstrs_reset_keys_translate_eqn:
      forall eq x,
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqn eq)) ->
        reset_call_var eq = Some x.
    Proof.
      intros [y ck ce|xs ck f exps orst|y ck c0 exp] x Hin;
        simpl in *; try contradiction.
      destruct xs as [|x0 xs']; simpl in *; try contradiction.
      destruct orst as [[r ckr]|]; simpl in *; try contradiction.
      intuition congruence.
    Qed.

    Lemma trconstrs_reset_keys_app:
      forall trs1 trs2,
        SECSTCTYPING.trconstrs_reset_keys (trs1 ++ trs2)
        = SECSTCTYPING.trconstrs_reset_keys trs1
            ++ SECSTCTYPING.trconstrs_reset_keys trs2.
    Proof.
      induction trs1 as [|tr trs1 IH]; intros trs2; simpl.
      - reflexivity.
      - rewrite IH, app_assoc. reflexivity.
    Qed.

    Lemma trconstrs_reset_keys_translate_eqns:
      forall eqs x,
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        In x (reset_call_vars eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      - inversion Hin.
      - unfold translate_eqns in Hin. simpl in Hin.
        change
          (In x
             (SECSTCTYPING.trconstrs_reset_keys
                (translate_eqn eq ++ translate_eqns eqs))) in Hin.
        rewrite trconstrs_reset_keys_app in Hin.
        apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + destruct (reset_call_var eq) as [x0|] eqn:Hreset; simpl.
          * pose proof (trconstrs_reset_keys_translate_eqn _ _ Hin) as Heq.
            rewrite Heq. simpl. auto.
          * pose proof (trconstrs_reset_keys_translate_eqn _ _ Hin) as Heq.
            congruence.
        + destruct (reset_call_var eq) as [x0|] eqn:Hreset; simpl.
          * rewrite Hreset. simpl. exact (or_intror (IH _ Hin)).
          * rewrite Hreset. simpl. exact (IH _ Hin).
    Qed.

    (** Bridging translated reset keys to the concrete mapped extras.

        The scoped concatenation proof later needs exactly this fact: whenever
        the STC constraints generated from [translate_eqns eqs] consult the
        reset-instance environment on some source identifier [x], the returned
        security variable belongs to the private-extra list reconstructed by
        [eqns_reset_extras rst_env eqs]. *)
    Lemma translated_reset_key_in_extras:
      forall rst_env eqs tys x ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        Env.find x rst_env = Some ty ->
        In ty tys.
    Proof.
      intros rst_env eqs tys x ty Hextras Hin Hfind.
      eapply eqns_reset_extras_complete; eauto.
      eapply trconstrs_reset_keys_translate_eqns; eauto.
    Qed.

    Lemma translated_reset_key_fresh:
      forall rst_env eqs tys scope x ty st1 st2,
        eqns_reset_extras rst_env eqs = Some tys ->
        (forall y rst_inst st3 st4,
            find_env y rst_env st3 = OK (rst_inst, st4) ->
            ~ In rst_inst scope) ->
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        find_env x rst_env st1 = OK (ty, st2) ->
        In ty tys /\ ~ In ty scope.
    Proof.
      intros rst_env eqs tys scope x ty st1 st2 Hextras Hfresh Hin Hfind.
      split.
      - unfold find_env in Hfind.
        destruct (Env.find x rst_env) as [ty'|] eqn:Henv; try discriminate.
        inversion Hfind; subst ty' st2.
        eapply translated_reset_key_in_extras; eauto.
      - eapply Hfresh; eauto.
    Qed.

    Lemma node_vars_env_scoped_from_mappings:
      forall n env inp out locals clk_type rst_type,
        get_mappings_from_node (n.(n_in)) env = Some inp ->
        get_mappings_from_node (n.(n_out)) env = Some out ->
        get_mappings_from_node (n.(n_vars)) env = Some locals ->
        SECSTCTYPING.vars_env_scoped env
          (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
          (inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
    Proof.
      intros n env inp out locals clk_type rst_type Hinp Hout Hlocals x Hmem.
      apply InMembers_idck in Hmem.
      apply InMembers_app in Hmem.
      destruct Hmem as [Hin|Hin].
      - destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hinp)
          as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app. left.
        exact Hscope.
      - apply InMembers_app in Hin.
        destruct Hin as [Hin|Hin].
        + destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hlocals)
            as (ty & Hfind & Hscope).
          exists ty. split; [exact Hfind|].
          apply in_or_app. right.
          apply in_or_app. right.
          apply in_or_app. left.
          exact Hscope.
        + destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin Hout)
            as (ty & Hfind & Hscope).
          exists ty. split; [exact Hfind|].
          apply in_or_app. right.
          apply in_or_app. left.
          exact Hscope.
    Qed.

    (** Local clocking preservation for translated equations.

        These are the lightweight translation-clocking lemmas needed by the
        scoped concatenation proof.  They deliberately avoid pulling the full
        [NL2StcClocking] functor into the SIF proof: all we need here is that a
        well-clocked NLustre equation list translates to an STC trconstr list
        that is accepted by the STC clocking judgement under the same local
        variable environment. *)
    Lemma translate_eqn_wc_local:
      forall P vars eq,
        wc_env vars ->
        wc_equation P vars eq ->
        Forall (wc_trconstr (translate P) vars) (translate_eqn eq).
    Proof.
      intros P vars eq Henv Hwc.
      destruct eq as [x ck ce|xs ck f les orst|x ck c0 e].
      - inversion_clear Hwc. simpl.
        constructor.
        + constructor; auto.
        + constructor.
      - inversion_clear Hwc. simpl.
        destruct xs as [|x0 xs']; simpl; auto.
        apply find_node_translate in H as (? & ? & ? & ?); subst.
        destruct orst as [[r ckr]|].
        + constructor.
          * econstructor.
            { constructor.
              - apply wc_env_var with (x := r).
                + exact Henv.
                + eapply H2; reflexivity.
              - eapply H2; reflexivity. }
          * constructor.
            { econstructor; eauto. }
            { constructor. }
        + constructor.
          * econstructor; eauto.
          * constructor.
      - inversion_clear Hwc. simpl.
        constructor.
        + constructor; auto.
        + constructor.
    Qed.

    Lemma translate_eqns_wc_local:
      forall P vars eqs,
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        Forall (wc_trconstr (translate P) vars) (translate_eqns eqs).
    Proof.
      intros P vars eqs Henv Hwc.
      induction Hwc as [|eq eqs Hwc_eq Hwc_eqs IH]; simpl.
      - constructor.
      - apply Forall_app; split.
        + eapply translate_eqn_wc_local; eauto.
        + exact IH.
    Qed.

    (** Scopedness of translated STC constraints from key lookups.

        This is the direct translation-layer wrapper around
        [SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys].  It keeps
        the NLustre-side hypotheses close by: well-clocked source equations
        produce well-clocked translated trconstrs under the same local variable
        environment. *)
    Lemma translated_eqns_constraints_scoped_on_keys:
      forall P (G2 : secglobal) vars scope eqs (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1,
            In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
            find_env x rst_env st0 = OK (ty, st1) ->
            In ty scope) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns eqs) st
          = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros P G2 vars scope eqs env rst_env base_ty rst_ty cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      eapply (SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys
                G2 env rst_env base_ty rst_ty
                (translate P) vars scope (translate_eqns eqs) cns st st').
      - exact Hscoped.
      - exact Henv.
      - eapply translate_eqns_wc_local; eauto.
      - exact Hvars.
      - exact Hbase.
      - exact Hrst.
      - exact Hreset.
      - exact Hgen.
    Qed.

    (** Concrete scopedness corollary using [eqns_reset_extras].

        Once the private reset-instance names for an equation list have been
        reconstructed as [extras], every translated reset lookup lands inside
        that list.  The generated STC constraints are therefore scoped to the
        shared scope extended with exactly those extras. *)
    Lemma translated_eqns_constraints_scoped:
      forall P (G2 : secglobal) vars scope eqs (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) extras cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env eqs = Some extras ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns eqs) st
          = OK (cns, st') ->
        constraints_scoped (scope ++ extras) cns.
    Proof.
      intros P G2 vars scope eqs env rst_env base_ty rst_ty extras cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hextras Hgen.
      eapply (translated_eqns_constraints_scoped_on_keys
                P G2 vars (scope ++ extras) eqs env rst_env base_ty rst_ty cns st st').
      - exact Hscoped.
      - exact Henv.
      - exact Hwc.
      - intros x Hx.
        destruct (Hvars x Hx) as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app. left. exact Hscope.
      - apply in_or_app. left. exact Hbase.
      - apply in_or_app. left. exact Hrst.
      - intros x ty st0 st1 Hin Hfind.
        apply in_app_iff. right.
        unfold find_env in Hfind.
        destruct (Env.find x rst_env) as [ty'|] eqn:Henvfind; try discriminate.
        inversion Hfind; subst ty' st1.
        eapply translated_reset_key_in_extras; eauto.
      - exact Hgen.
    Qed.

    (** Single-equation scopedness corollary.

        This is the one-step target scopedness fact used in the new scoped
        equation-list preservation proof: the translated STC block for one
        NLustre equation only mentions the shared scope plus the equation's own
        reset-instance extra (if any). *)
    Lemma translated_eqn_constraints_scoped:
      forall P (G2 : secglobal) vars scope e (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) extras cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        wc_equation P vars e ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqn_reset_extras rst_env e = Some extras ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqn e) st
          = OK (cns, st') ->
        constraints_scoped (scope ++ extras) cns.
    Proof.
      intros P G2 vars scope e env rst_env base_ty rst_ty extras cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hextra Hgen.
      destruct e; simpl in Hextra |- *; try discriminate.
      - eapply (translated_eqns_constraints_scoped
                  P G2 vars scope (EqDef i c c0 :: nil) env rst_env
                  base_ty rst_ty extras cns st st').
        + exact Hscoped.
        + exact Henv.
        + constructor; [exact Hwc|constructor].
        + exact Hvars.
        + exact Hbase.
        + exact Hrst.
        + simpl in Hextra. inversion Hextra; subst extras. reflexivity.
        + simpl. exact Hgen.
      - destruct l as [|x xs]; simpl in Hextra |- *.
        + inversion Hextra; subst extras.
          simpl in Hgen. inversion Hgen; subst cns st'.
          constructor.
        + eapply (translated_eqns_constraints_scoped
                    P G2 vars scope (EqApp (x :: xs) c i l0 o :: nil) env rst_env
                    base_ty rst_ty extras cns st st').
          * exact Hscoped.
          * exact Henv.
          * constructor; [exact Hwc|constructor].
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * simpl. rewrite Hextra, app_nil_r. reflexivity.
          * simpl. rewrite app_nil_r. exact Hgen.
      - eapply (translated_eqns_constraints_scoped
                  P G2 vars scope (EqFby i c c0 e :: nil) env rst_env
                  base_ty rst_ty extras cns st st').
        + exact Hscoped.
        + exact Henv.
        + constructor; [exact Hwc|constructor].
        + exact Hvars.
        + exact Hbase.
        + exact Hrst.
        + simpl in Hextra. inversion Hextra; subst extras. reflexivity.
        + simpl. exact Hgen.
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

    Lemma eqns_preserv_scoped_nil:
      forall scope P vars (G1 G2: secglobal)
             extras (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
             (nconst sconst: list constraint)
             (init_state1 init_state2 st1 st2: sec_state),
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) nil ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env nil = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1' st2',
            find_env x rst_env st1' = OK (rst_inst, st2') ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env base_ty rst_ty nil init_state1 = OK (nconst, st1) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns nil) init_state2
          = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 extras env rst_env base_ty rst_ty nconst sconst
             init_state1 init_state2 st1 st2
             Hsig Hscoped Henv Hwc Hvars Hbase Hrst Hextras Hnd Hfresh Hnl Hstc.
      dependent destruction Hwc.
      simpl in Hextras, Hnl, Hstc.
      inversion Hextras; subst.
      unfold ret in Hnl, Hstc.
      destruct nconst as [|cn nconst']; try discriminate.
      destruct sconst as [|cs sconst']; try discriminate.
      inversion Hnl; inversion Hstc; subst.
      exact (preserves_on_nil scope).
    Qed.

    (** Scoped equation-list preservation.

        In addition to one-step preservation, this theorem tracks the concrete
        STC-only reset-instance extras produced by the translation and
        composes head/tail blocks with [preserves_on_concat_scoped]. *)
    Lemma eqns_preserv_scoped:
      forall scope P vars (G1 G2: secglobal) (es: list equation) extras
             (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
             (nconst sconst: list constraint)
             (init_state1 init_state2 st1 st2: sec_state),
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) es ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env es = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1' st2',
            find_env x rst_env st1' = OK (rst_inst, st2') ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env base_ty rst_ty es init_state1 = OK (nconst, st1) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns es) init_state2
          = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 es.
      induction es as [|e es IH]; intros extras env rst_env base_ty rst_ty nconst sconst
                                      init_state1 init_state2 st1 st2
                                      Hsig Hscoped Henv Hwc Hvars Hbase Hrst
                                      Hextras Hnd Hfresh Hnl Hstc.
      - eapply (eqns_preserv_scoped_nil
                  scope P vars G1 G2 extras env rst_env base_ty rst_ty
                  nconst sconst init_state1 init_state2 st1 st2).
        + exact Hsig.
        + exact Hscoped.
        + exact Henv.
        + exact Hwc.
        + exact Hvars.
        + exact Hbase.
        + exact Hrst.
        + exact Hextras.
        + exact Hnd.
        + exact Hfresh.
        + exact Hnl.
        + exact Hstc.
      - inversion Hwc as [|eq eqs Hwc_e Hwc_es]; subst eq eqs.
        simpl in Hextras.
        destruct (eqn_reset_extras rst_env e) as [extras1|] eqn:Hextra1;
          try discriminate.
        destruct (eqns_reset_extras rst_env es) as [extras2|] eqn:Hextra2;
          try discriminate.
        inversion Hextras; subst extras.
        simpl in Hnl.
        repeat myMonadInv.
        eapply generate_tr_constraints_inv in Hstc.
        destruct Hstc as (sconst1 & st_mid & sconst2 & [Hstc1 [Hstc2 Hsconst]]).
        rewrite Hsconst.
        eapply preserves_on_concat_scoped with (extras1 := extras1) (extras2 := extras2).
        + exact Hnd.
        + intros ty0 Hin.
          eapply (eqns_reset_extras_fresh
                    rst_env (e :: es) (extras1 ++ extras2) scope).
          * simpl. rewrite Hextra1, Hextra2. reflexivity.
          * exact Hfresh.
          * exact Hin.
        + eapply (translated_eqn_constraints_scoped
                    P G2 vars scope e env rst_env base_ty rst_ty
                    extras1 sconst1 init_state2 st_mid).
          * exact Hscoped.
          * exact Henv.
          * exact Hwc_e.
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * exact Hextra1.
          * exact Hstc1.
        + eapply (translated_eqns_constraints_scoped
                    P G2 vars scope es env rst_env base_ty rst_ty
                    extras2 sconst2 st_mid st2).
          * exact Hscoped.
          * exact Henv.
          * exact Hwc_es.
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * exact Hextra2.
          * exact Hstc2.
        + eapply eqn_preserv; eauto with nocore.
          reflexivity.
        + eapply (IH extras2 env rst_env base_ty rst_ty x1 sconst2
                     x0 st_mid st1 st2).
          * exact Hsig.
          * exact Hscoped.
          * exact Henv.
          * exact Hwc_es.
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * exact Hextra2.
          * eapply NoDup_app_r; eauto.
          * exact Hfresh.
          * exact Hbind1.
          * exact Hstc2.
    Qed.

  End SECEQNPRES. 

  (** The node/system part of the development is organised in five layers:

      1. [node_preserv_scoped] is the core theorem. It works for one
         already-aligned
         node/system pair and assumes the relevant environment lookups plus the
         freshness of STC reset-instance variables.
      2. The freshness and inversion lemmas below are used only to discharge
         those assumptions when the environments and signatures come from the
         generators in [NameInterface], [SecNLusTyping], and [SecSTCTyping].
      3. [generated_node_preserv_scoped] packages that discharge for generated
         signatures, and [found_system_preserv_scoped_global] is the
         lookup-based global corollary obtained from [find_system_translate].
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

    (** The lemmas in this block are only used to discharge the freshness side
        conditions of the generated-node theorems. They establish that ordinary
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

    Lemma fresh_insert_preserves_find:
      forall env k st env' st' x ty,
        fresh_insert env k st = OK (env', st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros env k st env' st' x ty Hins Hfind.
      unfold fresh_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply name_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_ident_gen in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, NMret in Hins0. inversion Hins0; subst e st2.
      unfold NMret in Hret. inversion Hret; subst env' st'.
      assert (Hxk : x <> k).
      { intro Heq. subst x.
        assert (Env.mem k env = true).
        { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
        congruence. }
      now rewrite Env.gso.
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
        eapply name_bind_inv in Hmap as (env1 & st1 & Hstep & Hrec).
        eapply name_bind_inv in Hrec as (env2 & st2 & Hrec & Hret).
        unfold NMret in Hret. inversion Hret; subst env' st'.
        eapply IH; eauto.
        eapply fresh_insert_preserves_find; eauto.
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
        eapply name_bind2_inv in Hgen as (env2 & rs & st2 & Hrec & Hret).
        unfold NMret in Hret. inversion Hret; subst env' aux st'.
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

    Lemma generated_reset_env_maps_reset_calls:
      forall eqs reset_env rids st' x,
        generate_reset_env (translate_eqns eqs) init_state = OK ((reset_env, rids), st') ->
        In x (reset_call_vars eqs) ->
        exists ty, Env.find x reset_env = Some ty.
    Proof.
      intros eqs reset_env rids st' x Hgen Hin.
      destruct (reset_call_vars_translate_eqns _ _ Hin) as (ck & f & Hinreset).
      eapply SECSTCTYPINGCORRECTNESS.generate_reset_env_has_reset_stmt; eauto.
    Qed.

    Lemma generated_eqns_reset_extras:
      forall eqs reset_env rids st',
        NoDup (vars_defined eqs) ->
        generate_reset_env (translate_eqns eqs) init_state = OK ((reset_env, rids), st') ->
        exists tys,
          eqns_reset_extras reset_env eqs = Some tys
          /\ NoDup tys.
    Proof.
      intros eqs reset_env rids st' Hnodup Hgen.
      destruct (eqns_reset_extras_exists reset_env eqs) as [tys Hextras].
      {
        intros x Hin.
        eapply generated_reset_env_maps_reset_calls; eauto.
      }
      exists tys. split; [exact Hextras|].
      eapply eqns_reset_extras_nodup; eauto.
      - eapply reset_call_vars_nodup; eauto.
      - intros x y tx ty Hfindx Hfindy Heq.
        eapply SECSTCTYPINGCORRECTNESS.generate_reset_env_injective; eauto.
    Qed.

    (** Scoped node theorem.

        This theorem packages [eqns_preserv_scoped] at node level, so it keeps
        the concrete structural side conditions that justify scoped
        concatenation:

        - local NLustre clocking for the node equations;
        - scoped target signatures in [G2];
        - the exact reset-instance extras produced by the translated STC side.
     *)
    Theorem node_preserv_scoped:
      forall P (n : node) (s: system) scope
             (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             clk_id rst_id clk_type rst_type
             inp out locals
             reset_env rids extras
             nconst sconst
             st_reset st_n st_s,
        translate_node n = s ->
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        get_node_aux (n.(n_name)) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node (n.(n_in)) env = Some inp ->
        get_mappings_from_node (n.(n_out)) env = Some out ->
        get_mappings_from_node (n.(n_vars)) env = Some locals ->
        scope = inp ++ out ++ locals ++ (clk_type :: rst_type :: nil) ->
        generate_reset_env s.(SynStc.s_tcs) init_state = OK ((reset_env, rids), st_reset) ->
        eqns_reset_extras reset_env n.(n_eqs) = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1 st2,
            find_env x reset_env st1 = OK (rst_inst, st2) ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (nconst, st_n) ->
        generate_trconstrs_constraints G2 env reset_env clk_type rst_type s.(SynStc.s_tcs) st_reset = OK (sconst, st_s) ->
        preserves_on scope nconst sconst.
    Proof.
      intros P n s scope G1 G2 env aux_names clk_id rst_id clk_type rst_type
             inp out locals reset_env rids extras nconst sconst st_reset st_n st_s
             Htr Hsig Hscoped Hwc Haux Hclk Hrst Hinp Hout Hlocals Hscope
             Hresetenv Hextras Hnd Hfresh Hnl Hstc.
      subst scope.
      subst s. simpl in Hresetenv, Hstc.
      destruct Hwc as [_ [_ [Hwcenv Hwc]]].
      eapply (eqns_preserv_scoped
                (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                G1 G2 n.(n_eqs) extras env reset_env clk_type rst_type
                nconst sconst init_state st_reset st_n st_s); eauto.
      - eapply node_vars_env_scoped_from_mappings; eauto.
      - repeat rewrite in_app_iff. right. right. right. left. reflexivity.
      - repeat rewrite in_app_iff. right. right. right. right. left. reflexivity.
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

    (** Scoped generated-node theorem.

        This is the generated counterpart of [node_preserv_scoped].  It
        exposes the concrete local prerequisites used by the scoped
        concatenation proof:

        - local source clocking for [n];
        - scoped target signatures in [G2].

        This theorem is the generated bridge from node-level scoped
        preservation to the later global corollaries. *)
    Theorem generated_node_preserv_scoped:
      forall P all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
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
      intros P all_nodes n G1 G2 env aux_names nsig ssig
             Hsec Hsig Hscoped Hwc Henvgen Hnsig Hssig.
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
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
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
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref. contradiction.
        }
        eapply node_preserv_scoped
          with (P := P)
               (scope := inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)
               (G1 := G1) (G2 := G2)
               (s := translate_node n)
               (env := env) (reset_env := reset_env)
               (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (clk_type := clk_type) (rst_type := rst_type)
               (inp := inp) (out := out) (locals := nlocals)
               (rids := rids) (extras := extras)
               (nconst := nconst) (sconst := sconst)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s); eauto.
    Qed.

    (** Generated-node corollary under standard source-side well-formedness.

        This packages [generated_node_preserv_scoped] with the standard
        NLustre ordering/clocking facts needed to recover the local [wc_node]
        hypothesis. *)
    Corollary generated_node_preserv_scoped_global:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        CloNL.wc_global all_nodes ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
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
             Hsec Hsig Hwcg Hscoped Henvgen Hfind Hnsig Hssig.
      edestruct (CloNL.wc_find_node all_nodes n.(n_name) n Hwcg Hfind)
        as (G'' & G' & _ & Hwc).
      eapply generated_node_preserv_scoped with (P := G'); eauto.
    Qed.

    (** Lookup corollary.

        This is the lookup-based version of
        [generated_node_preserv_scoped_global]. *)
    Corollary found_system_preserv_scoped_global:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        CloNL.wc_global all_nodes ->
        secglobal_scoped G2 ->
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
             Hsec Hsig Hwcg Hscoped Henvgen Hfind Hsys Hnsig Hssig.
      eapply find_system_translate in Hsys as (n' & Hfind' & Htr).
      rewrite Hfind in Hfind'. inversion Hfind'. subst n'. subst s.
      pose proof (find_node_name _ _ _ Hfind) as Hname.
      subst f.
      eapply generated_node_preserv_scoped_global; eauto.
    Qed.

    Lemma sig_scope_in_raw_scope:
      forall sig locals x,
        In x (sig_scope sig) ->
        In x (sig.(s_in) ++ sig.(s_out) ++ locals ++ sig.(s_clk) :: sig.(s_reset) :: nil).
    Proof.
      intros sig locals x Hin.
      unfold sig_scope in Hin.
      repeat rewrite in_app_iff in *.
      destruct Hin as [Hin|[Hin|Hin]].
      - now left.
      - right. left. exact Hin.
      - destruct Hin as [Hinclk|[Hinrst|[]]].
        + right. right. right. left. exact Hinclk.
        + right. right. right. right. left. exact Hinrst.
    Qed.

    (** Simplify bridge for generated signatures.

        This theorem combines the generated node preservation result with the
        source-side simplify completeness theorem and the target-side simplify
        soundness theorem. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_scoped:
      forall all_nodes P (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        CloNL.wc_node P n ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready env aux_names ->
        signatures_preserved nsig ssig.
    Proof.
      intros all_nodes P n G1 G2 env aux_names nsig ssig
             Hsec Hcons Hscoped Henvgen Hwc Hnsig Hssig Hready.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Haux in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      destruct (Hready G1 n nsig
                  clk_id rst_id clk_type rst_type inp out locals nconst st_n
                  Hnsig Haux Hclk Hrst Hinp Hout Hlocals Hnconst Hnsigdef)
        as [Hwf Hdisj].
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
      assert (Hrawpres :
                preserves_on
                  (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                  nconst sconst).
      {
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfindrst Hin.
          unfold find_env in Hfindrst.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfindrst; clear Hfindrst; subst.
          edestruct generate_reset_env_range as (nrst & Hrsteq); eauto.
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref. contradiction.
        }
        eapply node_preserv_scoped
          with (P := P)
               (s := translate_node n)
               (G1 := G1) (G2 := G2)
               (env := env) (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (inp := inp) (out := out) (locals := locals)
               (reset_env := reset_env) (rids := rids) (extras := extras)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s); eauto.
      }
      subst nsig ssig.
      unfold signatures_preserved.
      split.
      - repeat split; reflexivity.
      - unfold preserves_on.
        intros dlt Hsat.
        destruct (SecTypes.simplify_complete
                    nconst locals
                    (inp ++ out ++ clk_type :: rst_type :: nil)
                    dlt
                    Hwf
                    Hdisj
                    Hsat)
          as (dlt_raw & Hagree & Hsat_raw).
        destruct (Hrawpres dlt_raw Hsat_raw) as (dlt_stc & Hagree_stc & Hsat_stc).
        exists dlt_stc. split.
        + intros x Hin.
          pose proof (sig_scope_in_raw_scope
                        {| s_name := n.(n_name);
                           s_in := inp;
                           s_out := out;
                           s_reset := rst_type;
                           s_clk := clk_type;
                           s_constraints := SymTypes.simplify nconst locals |}
                        locals x Hin) as Hinraw.
          transitivity (dlt_raw x).
          * apply Hagree. exact Hin.
          * apply Hagree_stc.
            exact Hinraw.
        + eapply simplify_is_correct.
          * exact Hsat_stc.
          * eapply simplify_simplifyRel. reflexivity.
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

        It talks only about the substitution interface exported by
        [generate_constraints].  The intended discharge point is the shared
        name-generation discipline in [NameInterface] together with generated
        signature scopedness. *)
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
          typically from [generated_node_preserv_scoped] plus a completeness result
          for [SymTypes.simplify];
        - [Signature_call_preserves] must follow from
          [signatures_preserved], via a semantic correctness theorem for
          [generate_constraints] under consistent fresh-name instantiations.

        Once these two bridge lemmas are available, the abstract
        [generated_signature_step_consistent] hypothesis used by the global
        theorems is no longer needed. *)

    (** Abstract per-generated-node bridge.

        This packages the one-step compatibility obligation needed by the later
        list-of-signatures induction: if a node and its translated system are
        generated from already consistent accumulators, then the fresh source
        and target signatures are themselves [Signature_head_consistent]. *)
    Definition generated_signature_step_consistent
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall acc1 acc2 n nsig ssig,
        Signature_consistent acc1 acc2 ->
        SECNLUSTYPING.generate_node_sig acc1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names = OK ssig ->
        Signature_head_consistent nsig ssig.

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
        (forall G1 G2 n nsig ssig,
            SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
            SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
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
        eapply Hcall; eauto.
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
    Definition generated_signatures_preserved
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G1 G2 n nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        signatures_preserved nsig ssig.

    (** This is the semantic call bridge that still has to come from the
        signature-instantiation layer.

        The formulation exposes the exact low-level requirements:

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

    Corollary generate_all_translated_system_signatures_scoped:
      forall all_nodes env aux_names G,
        CloStc.wc_program (translate all_nodes) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros all_nodes env aux_names G Hwc Henvgen Hgen.
      eapply SECSTCTYPING.generate_all_sys_signatures_scoped; eauto.
      eapply NAMEGEN.generate_node_env_injective; eauto.
    Qed.

    (** This is the generated-signature form of [Signature_consistent_cons].
        The generation equalities make the statement line up with the
        accumulator step of the global generators: once one generated
        source/target pair satisfies [Signature_head_consistent], the global
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

        This isolates the one-node bridge from the accumulator induction:
        if one freshly generated node/system signature pair satisfies
        [Signature_head_consistent], then the list induction lifts that fact to
        the whole generated global signature lists. *)
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
        destruct (SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names) as [ssig|] eqn:Hssig;
          simpl in Hnl, Hstc; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures' (nsig :: acc1) nodes env aux_names) as [G1'|] eqn:Hnl';
          simpl in Hnl; try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures' (ssig :: acc2) (translate nodes) env aux_names) as [G2'|] eqn:Hstc';
          simpl in Hstc; try discriminate.
        inversion Hnl; subst; clear Hnl.
        inversion Hstc; subst; clear Hstc.
        eapply IH with (acc1 := nsig :: acc1) (acc2 := ssig :: acc2); eauto.
        + eapply generated_signature_consistent_step; eauto.
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
      eapply generate_all_signatures_consistent'_abstract
        with (acc1 := @nil signature) (acc2 := @nil signature); eauto.
      apply Signature_consistent_nil.
    Qed.

    (** Concrete global-signature theorem.

        This proof performs the accumulator induction directly and uses the
        scoped simplify bridge for the current head node, together with the
        current scopedness and call-preservation hypotheses. *)
    Theorem generate_all_signatures_consistent_scoped':
      forall all_nodes nodes acc1 acc2 env aux_names G1 G2,
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready env aux_names ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global nodes ->
        Signature_consistent acc1 acc2 ->
        secglobal_scoped acc2 ->
        SECNLUSTYPING.generate_all_signatures' acc1 nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures' acc2 (translate nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2 /\ secglobal_scoped G2.
    Proof.
      induction nodes as [|n nodes IH]; intros acc1 acc2 env aux_names G1 G2
                                             Hsec Henvgen Hready Hnscoped Hsscoped
                                             Hfreshcalls Hcall Hwc Hcons Haccscoped Hnl Hstc.
      - simpl in Hnl, Hstc. inversion Hnl; inversion Hstc; subst.
        split; assumption.
      - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        simpl in Hnl, Hstc.
        destruct (SECNLUSTYPING.generate_node_sig acc1 n env aux_names) as [nsig|] eqn:Hnsig;
          try discriminate.
        destruct (SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names) as [ssig|] eqn:Hssig;
          simpl in Hnl, Hstc; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures' (nsig :: acc1) nodes env aux_names) as [G1'|] eqn:Hnl';
          simpl in Hnl; try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures' (ssig :: acc2) (translate nodes) env aux_names) as [G2'|] eqn:Hstc';
          simpl in Hstc; try discriminate.
        inversion Hnl; subst G1'. clear Hnl.
        inversion Hstc; subst G2'. clear Hstc.
        assert (Hpres : signatures_preserved nsig ssig).
        {
          eapply generated_signatures_preserved_from_simplify_bridge_scoped
            with (all_nodes := all_nodes) (P := nodes) (G1 := acc1) (G2 := acc2); eauto.
        }
        assert (Hhead : Signature_head_consistent nsig ssig).
        {
          split.
          - eapply generated_signature_name_agree; eauto.
          - destruct Hpres as [Hfields Hprescall].
            split; [exact Hfields|].
            eapply (Hcall Hfreshcalls nsig ssig).
            + eapply Hnscoped; eauto.
            + eapply Hsscoped; eauto.
            + split; [exact Hfields|exact Hprescall].
        }
        assert (Hcons' : Signature_consistent (nsig :: acc1) (ssig :: acc2)).
        { eapply Signature_consistent_cons; eauto. }
        assert (Hscoped' : secglobal_scoped (ssig :: acc2)).
        { eapply secglobal_scoped_cons; eauto. }
        eapply IH; eauto.
    Qed.

    Corollary generate_all_signatures_consistent_scoped:
      forall all_nodes env aux_names G1 G2,
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros all_nodes env aux_names G1 G2
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc.
      pose proof (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_global_from_env
                    all_nodes env aux_names Henvgen)
        as Hready.
      unfold SECNLUSTYPING.generate_all_signatures in Hallnl.
      unfold SECSTCTYPING.generate_all_sys_signatures in Hallstc.
      destruct (generate_all_signatures_consistent_scoped'
                  all_nodes all_nodes nil nil env aux_names G1 G2
                  Hsec Henvgen Hready Hnscoped Hsscoped Hfreshcalls Hcall
                  Hwc Signature_consistent_nil secglobal_scoped_nil Hallnl Hallstc)
        as [Hcons _].
      exact Hcons.
    Qed.

    (** Concrete global-signature theorem.

        The caller provides the remaining bridge premises, and the accumulator
        invariant is rebuilt internally.  Source-side simplify readiness is
        derived from
        [SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_global_from_env]. *)
    Corollary generate_all_signatures_consistent:
      forall all_nodes env aux_names G1 G2,
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros all_nodes env aux_names G1 G2
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc.
      eapply generate_all_signatures_consistent_scoped; eauto.
    Qed.

    (** Closed node theorem for globally generated signatures.

        This theorem rebuilds [Signature_consistent] from the full generated
        source/target globals and then reuses the node-level raw preservation
        theorem. *)
    Theorem generated_node_preserv_global:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        find_node n.(n_name) all_nodes = Some n ->
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
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hfind Hallnl Hallstc Hnsig Hssig.
      pose proof (generate_all_signatures_consistent
                    all_nodes env aux_names G1 G2 Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc) as Hcons.
      pose proof (SECSTCTYPINGCORRECTNESS.generate_all_sys_signatures_scoped_from_pointwise
                    (translate all_nodes) env aux_names G2 Hsscoped Hallstc) as HscopedG2.
      eapply generated_node_preserv_scoped_global; eauto.
    Qed.

    (** Lookup-based closed node theorem.

        The signature-consistency premise is discharged internally from the
        global generation equalities. *)
    Corollary found_system_preserv_global:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
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
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc Hfind Hsys Hnsig Hssig.
      pose proof (generate_all_signatures_consistent
                    all_nodes env aux_names G1 G2 Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc) as Hcons.
      pose proof (SECSTCTYPINGCORRECTNESS.generate_all_sys_signatures_scoped_from_pointwise
                    (translate all_nodes) env aux_names G2 Hsscoped Hallstc) as HscopedG2.
      eapply found_system_preserv_scoped_global; eauto.
    Qed.

    (** Lookup-based signature theorem.

        This is the public signature-level consequence of the global bridge:
        once the source and target signatures are generated for matching source
        and translated systems, the simplified signatures satisfy
        [signatures_preserved] directly.  Internal NLustre/STC locals stay in
        the bridge lemmas and do not appear in this exported statement. *)
    Corollary found_system_signatures_preserved_global:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        find_node f all_nodes = Some n ->
        SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
        signatures_preserved nsig ssig.
    Proof.
      intros all_nodes f n s prog' G1 G2 env aux_names nsig ssig
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc
             Hfind Hsys Hnsig Hssig.
      pose proof (generate_all_signatures_consistent
                    all_nodes env aux_names G1 G2
                    Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall
                    Hwc Hallnl Hallstc) as Hcons.
      pose proof (SECSTCTYPINGCORRECTNESS.generate_all_sys_signatures_scoped_from_pointwise
                    (translate all_nodes) env aux_names G2 Hsscoped Hallstc) as HscopedG2.
      edestruct (CloNL.wc_find_node all_nodes f n Hwc Hfind)
        as (P'' & P' & _ & Hwcnode).
      eapply find_system_translate in Hsys as (n' & Hfind' & Htr).
      rewrite Hfind in Hfind'. inversion Hfind'. subst n'. subst s.
      pose proof (find_node_name _ _ _ Hfind) as Hfname. subst f.
      eapply generated_signatures_preserved_from_simplify_bridge_scoped
        with (all_nodes := all_nodes) (P := P') (G1 := G1) (G2 := G2); eauto.
      eapply SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_global_from_env; eauto.
    Qed.

    (** Program-level preservation property.

        This packages the lookup corollary so that the final theorem can state
        directly that every translated system found in the target program
        satisfies the underlying raw preservation relation. *)
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

        The theorem keeps the remaining lower-level premises that still have to
        be discharged above this layer:

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
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        generated_program_preserves all_nodes env aux_names G1 G2.
    Proof.
      intros all_nodes G1 G2 env aux_names
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc.
      intros f n s prog' nsig ssig Hfind Hsys Hnsig Hssig.
      eapply found_system_preserv_global; eauto.
    Qed.

    (** Program-level signature corollary.

        This is the simplified reading of the final theorem: once both source
        and target signatures are generated for matching source and translated
        systems, those signatures satisfy [signatures_preserved].  Internal
        NLustre locals remain hidden inside the raw bridge theorems. *)
    Corollary generated_program_signatures_preserved_global:
      forall all_nodes (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names),
        Ids.sec <> Ids.sec_reset ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPINGCORRECTNESS.generated_node_signatures_scoped env aux_names ->
        SECSTCTYPINGCORRECTNESS.generated_system_signatures_scoped env aux_names ->
        successful_call_substitutions_fresh ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G2 ->
        forall f n s prog' nsig ssig,
          find_node f all_nodes = Some n ->
          SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
          SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
          SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
          signatures_preserved nsig ssig.
    Proof.
      intros all_nodes G1 G2 env aux_names
             Hsec Henvgen Hnscoped Hsscoped Hfreshcalls Hcall Hwc Hallnl Hallstc
             f n s prog' nsig ssig Hfind Hsys Hnsig Hssig.
      eapply found_system_signatures_preserved_global; eauto.
    Qed.
  End NODESYSPRES.



End SECNLUSSTCTRANSLATION.


Module SecNLusStcTranslation
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import SecTypes : SECTYPES Lat)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Import Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (Import SIG          : SIGNATURE   Ids SC)
  (Import NAMEGEN      : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING  : SECCETYPING Ids Op CESyn)
  (Import CEIsF        : CEISFREE Ids Op CESyn)
  (Import CEClo        : CECLOCKING Ids Op CESyn)
  (Import OrdNL        : NLORDERED Ids Op CESyn SynNL)
  (Import IsD          : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsFNL        : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import CloNL        : NLCLOCKING Ids Op CESyn SynNL OrdNL Mem IsD CEIsF IsFNL CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
  (Import SECNLUSTYPINGCORRECTNESS
      : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL SECNLUSTYPING)
  (Import Last         : STCISLAST Ids Op CESyn SynStc)
  (Import Var          : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def          : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst         : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc       : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsFStc       : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc       : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc)
  (Import SECSTCTYPINGCORRECTNESS
      : SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING)
  <: SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL IsD IsFNL CloNL SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING SECSTCTYPINGCORRECTNESS.

  Include SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL IsD IsFNL CloNL SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING SECSTCTYPINGCORRECTNESS.
End SecNLusStcTranslation.
