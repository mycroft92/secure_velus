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
          /\ signature_fields_agree n1 n2
          /\ (forall scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2,
                generate_constraints n1 inptyp ckty rstty outtyp st_init1 = OK (nconst, st1) ->
                generate_constraints n2 inptyp ckty rstty outtyp st_init2 = OK (sconst, st2) ->
                preserves_on scope nconst sconst)
          /\ (forall scope inptyp ckty srcrst outtyp reset_lhs rst_inst nconst sconst st_init1 st_init2 st1 st2,
                ~ In rst_inst scope ->
                generate_constraints n1 inptyp ckty srcrst outtyp st_init1 = OK (nconst, st1) ->
                generate_constraints n2 inptyp ckty (rst_inst :: nil) outtyp st_init2 = OK (sconst, st2) ->
                preserves_on scope nconst ((reset_lhs, (rst_inst :: nil)) :: sconst)).
    Hint Unfold Signature_consistent.

    (** Closure of the weak preservation relation under concatenation of
        constraint lists. This is assumed rather than reproved here, so that the
        list-level theorem isolates the translation argument from the generic
        constraint semantics. *)
    Definition preserves_on_app_closed (scope: list ident) : Prop :=
      forall c1 c2 t1 t2,
        preserves_on scope c1 t1 ->
        preserves_on scope c2 t2 ->
        preserves_on scope (c1 ++ c2) (t1 ++ t2).

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
            unfold Signature_consistent in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [Hfields [_ Hresetcall]]]].
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
            unfold Signature_consistent in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [Hfields [Hsimplecall _]]]].
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

  (** The node-level theorem simply instantiates the list-level result with the
      scope that matters for the current development:

      - inputs
      - outputs
      - locals
      - the node clock type
      - the node reset type

      Any STC-only reset-instance variables live outside this scope. *)
  Section NODESYSPRES.

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
        generate_trconstrs_constraints G2 env reset_env clk_type rst_type s.(SynStc.s_tcs) init_state = OK (sconst, st_s) ->
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
