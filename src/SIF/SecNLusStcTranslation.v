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
From Coq Require Import List.
Import List.ListNotations.
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
From Coq Require Import Permutation.
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
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
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

	    Lemma agree_on_trans:
	      forall xs dlt1 dlt2 dlt3,
	        agree_on xs dlt1 dlt2 ->
	        agree_on xs dlt2 dlt3 ->
	        agree_on xs dlt1 dlt3.
	    Proof.
	      intros xs dlt1 dlt2 dlt3 H12 H23 x Hin.
	      rewrite H12 by exact Hin.
	      exact (H23 x Hin).
	    Qed.

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

    Definition call_actuals_scoped
      (scope: list ident) (inptyp: list ST) (ckty: ST) (outtyp: list ident) : Prop :=
      Forall (st_scoped scope) inptyp
      /\ st_scoped scope ckty
      /\ Forall (fun x => In x scope) outtyp.

    Definition call_subst_scoped
      (scope: list ident) (inptyp: list ST) (ckty rstty: ST) (outtyp: list ident) : Prop :=
      call_actuals_scoped scope inptyp ckty outtyp
      /\ st_scoped scope rstty.

    (** [scope_fresh scope sig] says that every identifier visible in the caller
        scope is disjoint from the callee signature scope.  This is the precise
        freshness condition the call cases actually need: once the actual
        arguments, clock/reset types, and outputs are known to stay inside the
        caller scope, [scope_fresh] turns that scopedness information into the
        local [call_subst_fresh] premises consumed by
        [Signature_call_preserves]. *)
    Definition scope_fresh (scope: list ident) (sig: signature) : Prop :=
      forall x, In x scope -> ~ In x (sig_scope sig).

    (** Generated-accumulator freshness is best expressed structurally:
        every callee signature currently stored in a source accumulator must be
        disjoint from the current caller scope.  This is the eventual
        replacement for the older global assumption
        [successful_call_substitutions_fresh], which was phrased directly over
        arbitrary successful [generate_constraints] calls and was therefore much
        stronger than what the translation proof actually uses. *)
    Definition secglobal_scope_fresh (scope: list ident) (G: secglobal) : Prop :=
      forall f sig,
        find_signature f G = Some sig ->
        scope_fresh scope sig.

    (** Resettable calls additionally need the target-local namespace fact that
        visible signature identifiers stay in the ordinary [sec] namespace.
        The generic notion [signature_scope_sec] lives in [SIFSignature.v];
        here we only add the accumulator-level wrapper consumed by the
        translation proof. *)
    Definition secglobal_scope_sec (G: secglobal) : Prop :=
      forall f sig,
        find_signature f G = Some sig ->
        signature_scope_sec sig.

    (** Structural caller-scope freshness for one generated node environment.

        This is the local shape the generated call proofs actually need.  Once
        the current node's clock/reset ids and interface/local mappings are
        recovered from the naming environment, every signature already present
        in the source accumulator must be fresh with respect to that caller
        scope.  Later proofs will derive this from node-scoped naming
        provenance; it is strictly narrower than the old global assumption
        [successful_call_substitutions_fresh]. *)
    Definition node_scope_fresh_in_env
      (n: node) (env: Env.t ident) (aux_names: list node_aux_names) (G: secglobal) : Prop :=
      forall clk_id rst_id clk_type rst_type inp out locals,
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        secglobal_scope_fresh
          (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) G.

    (** Generated-program wrapper for [node_scope_fresh_in_env].

        This is the replacement interface that the generated/global theorem
        stack should eventually consume instead of
        [successful_call_substitutions_fresh]: every source node found in the
        program induces a fresh caller scope against the current source
        accumulator. *)
    Definition generated_callers_scope_fresh
      (all_nodes: global) (env: Env.t ident) (aux_names: list node_aux_names)
      (G: secglobal) : Prop :=
      forall n,
        find_node n.(n_name) all_nodes = Some n ->
        node_scope_fresh_in_env n env aux_names G.

    Definition scope_lower_bounded (scope: list ident) (st: ident) : Prop :=
      forall ty,
        In ty scope ->
        exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive.

    Definition signature_scope_bounded_above (sig: signature) (st: ident) : Prop :=
      forall ty,
        In ty (sig_scope sig) ->
        exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive.

    Definition secglobal_scope_bounded_above (G: secglobal) (st: ident) : Prop :=
      forall f sig,
        find_signature f G = Some sig ->
        signature_scope_bounded_above sig st.

    Lemma secglobal_scope_bounded_above_nil:
      forall st, secglobal_scope_bounded_above nil st.
    Proof.
      intros st f sig Hfind.
      simpl in Hfind. discriminate.
    Qed.

    Lemma secglobal_scope_bounded_above_cons:
      forall st sig G,
        signature_scope_bounded_above sig st ->
        secglobal_scope_bounded_above G st ->
        secglobal_scope_bounded_above (sig :: G) st.
    Proof.
      intros st sig G Hsig HG f sig' Hfind.
      simpl in Hfind.
      destruct (ident_eqb sig.(s_name) f) eqn:Hname.
      - inversion Hfind; subst. exact Hsig.
      - eapply HG; eauto.
    Qed.

    Lemma scope_fresh_from_bounds:
      forall scope sig st,
        scope_lower_bounded scope st ->
        signature_scope_bounded_above sig st ->
        scope_fresh scope sig.
    Proof.
      intros scope sig st Hlo Hhi ty Hinscope Hinsig.
      destruct (Hlo ty Hinscope) as (nlo & Hloeq & Hlole).
      destruct (Hhi ty Hinsig) as (nhi & Hhieq & Hhilt).
      rewrite Hloeq in Hhieq.
      apply gensym_injective in Hhieq as [_ Hidx].
      subst nhi.
      assert (Hcontra : (nlo < nlo)%positive)
        by (eapply Pos.lt_le_trans; [exact Hhilt | exact Hlole]).
      exfalso.
      exact (Pos.lt_irrefl _ Hcontra).
    Qed.

    Lemma signature_scope_bounded_above_monotone:
      forall sig st st',
        signature_scope_bounded_above sig st ->
        (st <= st')%positive ->
        signature_scope_bounded_above sig st'.
    Proof.
      intros sig st st' Hbound Hle ty Hin.
      destruct (Hbound ty Hin) as (n & Hn & Hlt).
      exists n. split; auto.
      eapply Pos.lt_le_trans; eauto.
    Qed.

    Lemma secglobal_scope_bounded_above_monotone:
      forall G st st',
        secglobal_scope_bounded_above G st ->
        (st <= st')%positive ->
        secglobal_scope_bounded_above G st'.
    Proof.
      intros G st st' Hbound Hle f sig Hfind.
      eapply signature_scope_bounded_above_monotone; eauto.
    Qed.

    Lemma signature_fields_agree_scope_eq:
      forall n1 n2,
        signature_fields_agree n1 n2 ->
        sig_scope n1 = sig_scope n2.
    Proof.
      intros n1 n2 [Hin [Hout [Hrst Hclk]]].
      unfold sig_scope.
      now rewrite Hin, Hout, Hclk, Hrst.
    Qed.

    Lemma scope_fresh_fields_agree:
      forall scope n1 n2,
        signature_fields_agree n1 n2 ->
        scope_fresh scope n1 ->
        scope_fresh scope n2.
    Proof.
      intros scope n1 n2 Hagree Hfresh x Hin.
      rewrite <- (signature_fields_agree_scope_eq _ _ Hagree).
      eauto.
    Qed.

    Lemma signature_scope_sec_fields_agree:
      forall n1 n2,
        signature_fields_agree n1 n2 ->
        signature_scope_sec n1 ->
        signature_scope_sec n2.
    Proof.
      intros n1 n2 Hagree Hsec ty Hin.
      destruct Hagree as [Hin' [Hout' [Hrst' Hclk']]].
      unfold signature_scope in *.
      rewrite <- Hin', <- Hout', <- Hclk', <- Hrst' in Hin.
      eauto.
    Qed.

    Lemma type_fresh_from_scope_fresh:
      forall scope sig ty,
        scope_fresh scope sig ->
        st_scoped scope ty ->
        type_fresh (sig_scope sig) ty.
    Proof.
      intros scope sig ty Hfresh Hsc.
      unfold type_fresh.
      rewrite Forall_forall.
      intros x Hin Hsig.
      eapply Hfresh; eauto.
    Qed.

    Lemma types_fresh_from_scope_fresh:
      forall scope sig tys,
        scope_fresh scope sig ->
        Forall (st_scoped scope) tys ->
        types_fresh (sig_scope sig) tys.
    Proof.
      intros scope sig tys Hfresh Htys.
      induction Htys as [|ty tys Hty Htys IH]; constructor; auto.
      eapply type_fresh_from_scope_fresh; eauto.
    Qed.

    Lemma outputs_fresh_from_scope_fresh:
      forall scope sig outs,
        scope_fresh scope sig ->
        Forall (fun x => In x scope) outs ->
        outputs_fresh (sig_scope sig) outs.
    Proof.
      intros scope sig outs Hfresh Houts.
      induction Houts as [|x outs Hin Houts IH]; constructor; auto.
    Qed.

    Lemma call_subst_fresh_from_scope_fresh:
      forall scope sig inptyp ckty rstty outtyp,
        scope_fresh scope sig ->
        Forall (st_scoped scope) inptyp ->
        st_scoped scope ckty ->
        st_scoped scope rstty ->
        Forall (fun x => In x scope) outtyp ->
        call_subst_fresh sig inptyp ckty rstty outtyp.
    Proof.
      intros scope sig inptyp ckty rstty outtyp
             Hfresh Hinp Hclk Hrst Hout.
      repeat split.
      - eapply types_fresh_from_scope_fresh; eauto.
      - eapply type_fresh_from_scope_fresh; eauto.
      - eapply type_fresh_from_scope_fresh; eauto.
      - eapply outputs_fresh_from_scope_fresh; eauto.
    Qed.

    Lemma call_subst_fresh_reset_from_scope_fresh:
      forall scope sig inptyp ckty rst_inst outtyp,
        scope_fresh scope sig ->
        signature_scope_sec sig ->
        Forall (st_scoped scope) inptyp ->
        st_scoped scope ckty ->
        (exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
        Forall (fun x => In x scope) outtyp ->
        call_subst_fresh sig inptyp ckty (rst_inst :: nil) outtyp.
    Proof.
      intros scope sig inptyp ckty rst_inst outtyp
             Hfresh Hsigsec Hinp Hclk Hrstinst Hout.
      repeat split.
      - eapply types_fresh_from_scope_fresh; eauto.
      - eapply type_fresh_from_scope_fresh; eauto.
      - unfold type_fresh. rewrite Forall_forall.
        intros x Hin Hsig.
        simpl in Hin. destruct Hin as [Heq|[]]. subst x.
        eapply sec_reset_not_in_signature_scope; eauto.
      - eapply outputs_fresh_from_scope_fresh; eauto.
    Qed.

    Definition successful_call_substitutions_fresh : Prop :=
      forall sig inptyp ckty rstty outtyp cns st_init st',
        generate_constraints sig inptyp ckty rstty outtyp st_init = OK (cns, st') ->
        call_subst_fresh sig inptyp ckty rstty outtyp.

    (** [Signature_call_preserves n1 n2] packages the two call-specific
        obligations used by [eqn_preserv]:

        - ordinary calls instantiate the callee signatures with the caller's
          argument/output types;
        - resettable calls do the same, while allowing STC to prepend one fresh
          reset-instance constraint outside the shared scope. *)
    Definition Signature_call_preserves (n1 n2: signature) : Prop :=
      (forall scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2,
          call_subst_scoped scope inptyp ckty rstty outtyp ->
          call_subst_fresh n1 inptyp ckty rstty outtyp ->
          call_subst_fresh n2 inptyp ckty rstty outtyp ->
          generate_constraints n1 inptyp ckty rstty outtyp st_init1 = OK (nconst, st1) ->
          generate_constraints n2 inptyp ckty rstty outtyp st_init2 = OK (sconst, st2) ->
          preserves_on scope nconst sconst)
      /\ (forall scope inptyp ckty srcrst outtyp reset_lhs rst_inst nconst sconst st_init1 st_init2 st1 st2,
            call_subst_scoped scope inptyp ckty srcrst outtyp ->
            ~ In rst_inst scope ->
            call_subst_fresh n1 inptyp ckty srcrst outtyp ->
            call_subst_fresh n2 inptyp ckty (rst_inst :: nil) outtyp ->
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
        rewrite SECSTCTYPINGCORRECTNESS.trconstrs_reset_keys_app in Hin.
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

    (** Local clocking preservation for translated equations and nodes.

        These are the lightweight translation-clocking lemmas needed by the
        scoped concatenation proof.  They deliberately avoid pulling the full
        [NL2StcClocking] functor into the SIF proof: all we need here is that a
        well-clocked NLustre fragment translates to STC constraints and systems
        that are accepted by the STC clocking judgement under the corresponding
        translated environments. *)
    Lemma gather_eqs_n_vars_wc_local:
      forall n G,
        Forall (wc_equation G (idck (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
        Permutation (idck (fst (gather_eqs (n_eqs n))))
                    (idck
                       (fst
                          (partition
                             (fun x : ident * (type * clock) =>
                                PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                             (n_vars n)))).
    Proof.
      intros * WC.
      rewrite fst_partition_filter.
      apply NoDup_Permutation.
      - apply NoDupMembers_NoDup, NoDupMembers_idck, fst_NoDupMembers.
        rewrite fst_fst_gather_eqs_var_defined.
        pose proof (NoDup_var_defined_n_eqs n) as Hnodup;
          rewrite <-is_filtered_vars_defined in Hnodup.
        rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
        rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
        auto.
      - apply NoDupMembers_NoDup, fst_NoDupMembers.
        rewrite map_fst_idck, filter_mem_fst.
        apply nodup_filter.
        pose proof (n.(n_nodup)) as Hnodup.
        apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
        now apply fst_NoDupMembers.
      - intros (x, ck).
        setoid_rewrite ps_from_list_gather_eqs_memories.
        assert (forall x, In x (vars_defined (filter is_fby (n_eqs n))) ->
                     InMembers x (n_vars n)) as Spec
            by (intro; rewrite <-fst_partition_memories_var_defined, fst_partition_filter,
                       filter_mem_fst, filter_In, fst_InMembers; intuition).
        pose proof (filter_fst_idck (n_vars n)
                                    (fun x => PS.mem x (Mem.memories (n_eqs n)))) as E;
          setoid_rewrite E; clear E.
        setoid_rewrite filter_In.
        setoid_rewrite <-PSE.MP.Dec.F.mem_iff.
        unfold Mem.memories, gather_eqs in *.
        generalize (@nil (ident * ident)).
        induction (n_eqs n) as [|[]]; inversion_clear WC as [|?? WCeq]; simpl; intros; auto.
        + split; try contradiction.
          setoid_rewrite PSE.MP.Dec.F.empty_iff; intuition.
        + cases.
        + inversion_clear WCeq as [| |???? Hinc].
          rewrite In_fold_left_memory_eq, PSE.MP.Dec.F.add_iff, PSE.MP.Dec.F.empty_iff.
          split.
          * intros * Hin.
            unfold idck in Hin.
            apply in_map_iff in Hin as ((x', (c', ck')) & E & Hin); simpl in *; inv E.
            apply In_fst_fold_left_gather_eq in Hin as [Hin|Hin].
            -- inversion_clear Hin as [E|]; try contradiction; inv E.
               intuition.
               assert (InMembers x (n_vars n)) by auto.
               pose proof (n_nodup n) as Hnodup.
               rewrite fst_NoDupMembers, 2 map_app, NoDup_swap, <- 2 map_app, <-fst_NoDupMembers in Hnodup.
               eapply NoDupMembers_app_InMembers, NotInMembers_app in Hnodup as (? & ?); eauto.
               rewrite 2 idck_app, 2 in_app in Hinc; destruct Hinc as [Hinc|[|Hinc]]; auto;
                 apply In_InMembers in Hinc; rewrite InMembers_idck in Hinc; contradiction.
            -- assert (In (x, ck) (idck (fst (fold_left gather_eq l ((@nil (ident * (const * clock))), l0)))))
                 as Hin' by (apply in_map_iff; eexists; intuition; eauto; simpl; auto).
               apply IHl in Hin'; intuition.
          * intros * (Hin & [MemIn|MemIn]).
            -- assert (In (x, ck) (idck (fst (fold_left gather_eq l ((@nil (ident * (const * clock))), l0))))) as Hin'
                   by (apply IHl; auto; intros * Hin';
                       apply Spec; simpl; auto).
               unfold idck in Hin'; apply in_map_iff in Hin' as ((x', (c', ck')) & E & Hin'); simpl in *; inv E.
               apply in_map_iff; exists (x, (c', ck)); simpl.
               rewrite In_fst_fold_left_gather_eq; intuition.
            -- destruct MemIn as [E|]; try contradiction; inv E.
               apply in_map_iff; exists (x, (c0, c)); simpl.
               rewrite In_fst_fold_left_gather_eq; intuition.
               f_equal.
               assert (In (x, ck) (idck (n_in n ++ n_vars n ++ n_out n)))
                 by (rewrite 2 idck_app, 2 in_app; auto).
               eapply NoDupMembers_det; eauto.
               apply NoDupMembers_idck, n_nodup.
    Qed.

    Lemma wc_trconstrs_permutation_local:
      forall P vars vars' trs,
        Permutation vars vars' ->
        Forall (wc_trconstr P vars) trs ->
        Forall (wc_trconstr P vars') trs.
    Proof.
      intros * E WC.
      eapply Forall_impl with (2 := WC); eauto.
      setoid_rewrite E; auto.
    Qed.

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

    Lemma translate_node_wc_local:
      forall G n,
        wc_node G n ->
        wc_system (translate G) (translate_node n).
    Proof.
      intros G n Hwc.
      destruct Hwc as (Henv_in & Henv_out & Henv_vars & Heqs).
      assert (E :
                Permutation
                  (idck (n_in n ++
                         snd
                           (partition
                              (fun x : ident * (type * clock) =>
                                 PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                              (n_vars n)) ++
                         n_out n) ++ idck (fst (gather_eqs (n_eqs n))))
                  (idck (n_in n ++ n_vars n ++ n_out n))).
      {
        repeat rewrite idck_app.
        rewrite Permutation_app_comm, Permutation_swap, gather_eqs_n_vars_wc_local,
          <-2 idck_app, app_assoc, <-permutation_partition, idck_app; eauto.
      }
      repeat split; simpl; auto.
      - now rewrite E.
      - apply Permutation_sym in E.
        eapply wc_trconstrs_permutation_local with (vars := idck (n_in n ++ n_vars n ++ n_out n)); eauto.
        clear - Heqs Henv_vars.
        induction Heqs as [|eq eqs Hwc_eq Hwc_eqs IH]; simpl.
        + constructor.
        + apply Forall_app; split.
          * eapply translate_eqn_wc_local; eauto.
          * exact IH.
    Qed.

    Lemma translate_wc_local:
      forall G,
        wc_global G ->
        wc_program (translate G).
    Proof.
      intros G Hwc.
      induction Hwc; simpl; auto.
      constructor; auto.
      eapply translate_node_wc_local; eauto.
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
      forall scope P vars (G1 G2: secglobal)
             (e: equation) (trs: list trconstr)
             (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
      Signature_consistent G1 G2 ->
      secglobal_scope_fresh scope G1 ->
      secglobal_scope_sec G2 ->
      wc_env vars ->
      wc_equation P vars e ->
      SECNLUSTYPING.vars_env_scoped env vars scope ->
      In base_ty scope ->
      In rst_ty scope ->
      translate_eqn e = trs ->
      (forall x rst_inst st1' st2',
          find_env x rst_env st1' = OK (rst_inst, st2') ->
          exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
      (forall x rst_inst st1' st2',
          find_env x rst_env st1' = OK (rst_inst, st2') ->
          ~ In rst_inst scope) ->
      generate_eqn_constraint G1 env base_ty rst_ty e init_state1 = OK (nconst, st1) ->
      generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2 = OK (sconst, st2) ->
      preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 e trs env rst_env base_ty rst_ty nconst sconst
             init_state1 init_state2 st1 st2
             Hsig Hscopefresh Hglobsec Henv Hwc Hvars Hbase Hrst Htr Hrstgen Hfresh Hnl Hstc.
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
            inversion Hwc as [x' ck' ce' Hx Hce
                             |xs' ck' f' exps' r' n' sub Hfindnode Hinputs Houtputs Hreset
                             |x' ck' v le Hx Hle]; subst.
            destruct (SECNLUSTYPING.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [_ Hresetcall]]]]].
            pose proof (Hscopefresh f snl Hfindnl) as Hsnlfresh.
            pose proof (scope_fresh_fields_agree scope snl sstc Hfields Hsnlfresh) as Hsstcfresh.
            pose proof (Hglobsec f sstc Hfindstc) as Hsstcsec.
            rewrite Hfindstc in Hstc.
            eapply sec_bind_inv in Hnl as (ckty_nl & st_ck_nl & Hck_nl & Hnl).
            eapply sec_bind_inv in Hnl as (rty_nl & st_r_nl & Hr_nl & Hnl).
            eapply sec_bind_inv in Hnl as (rstty_nl & st_rst_nl & Hrst_nl & Hnl).
            eapply sec_bind_inv in Hnl as (inptyp_nl & st_inp_nl & Hinp_nl & Hnl).
            eapply sec_bind_inv in Hnl as (outtyp_nl & st_out_nl & Hout_nl & Hcall_nl).
            eapply sec_bind_inv in Hstc as (reset_cns & st_mid & Hreset_blk & Hstc).
            eapply sec_bind_inv in Hstc as (call_cns & st_call2 & Hcall_blk & Hret_concat).
            unfold ret in Hret_concat. inversion Hret_concat; subst sconst st2.
            simpl in Hreset_blk.
            eapply sec_bind_inv in Hreset_blk as (rckty_stc & st_rck_stc & Hck_reset_stc & Hreset_blk).
            eapply sec_bind_inv in Hreset_blk as (rst_inst_reset & st_rstinst_reset & Hrstinst_reset & Hret_reset).
            unfold ret in Hret_reset. inversion Hret_reset; subst reset_cns st_mid.
            simpl in Hcall_blk.
            eapply sec_bind_inv in Hcall_blk as (c_call & st_call1 & Hc_call & Hcall_blk).
            eapply sec_bind_inv in Hcall_blk as (c_nil_call & st_call3 & Hnil_call & Hret_call_blk).
            unfold ret in Hret_call_blk. inversion Hret_call_blk; subst call_cns st_call2.
            unfold ret in Hnil_call. inversion Hnil_call; subst c_nil_call st_call3.
            simpl in Hc_call.
            eapply sec_bind_inv in Hc_call as (ckty_stc & st_ck_stc & Hck_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (inptyp_stc & st_inp_stc & Hinp_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (outtyp_stc & st_out_stc & Hout_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (rst_inst_call & st_rstinst_call & Hrstinst_call & Hcall_stc).
            eapply sec_bind_inv in Hout_nl as (outhd_nl & st_outhd_nl & Houthd_nl & Hout_nl).
            eapply sec_bind_inv in Hout_nl as (outtl_nl & st_outtl_nl & Houttl_nl & Hret_out_nl).
            unfold ret in Hret_out_nl. inversion Hret_out_nl; subst outtyp_nl st_out_nl.
            eapply sec_bind_inv in Hout_stc as (outhd_stc & st_outhd_stc & Houthd_stc & Hout_stc).
            eapply sec_bind_inv in Hout_stc as (outtl_stc & st_outtl_stc & Houttl_stc & Hret_out_stc).
            unfold ret in Hret_out_stc. inversion Hret_out_stc; subst outtyp_stc st_out_stc.
            assert (Hck : ckty_nl = ckty_stc).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp : inptyp_nl = inptyp_stc).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthd : outhd_nl = outhd_stc).
            { eapply find_env_consistent_nl_stc; eauto. }
            assert (Houttl : outtl_nl = outtl_stc).
            { eapply mmap_find_env_consistent_nl_stc; eauto. }
            assert (Hrstinst : rst_inst_call = rst_inst_reset).
            { eapply find_env_consistent; eauto. }
            assert (Hckopt : assign_clk_type env base_ty ck = Some ckty_nl).
            { unfold option_to_sec in Hck_nl.
              destruct (assign_clk_type env base_ty ck) eqn:Hckopt; try discriminate.
              inversion Hck_nl; subst. reflexivity. }
            assert (Hrstopt : assign_clk_type env rst_ty ckr = Some rstty_nl).
            { unfold option_to_sec in Hrst_nl.
              destruct (assign_clk_type env rst_ty ckr) eqn:Hrstopt; try discriminate.
              inversion Hrst_nl; subst. reflexivity. }
            assert (Hckscope : st_scoped scope ckty_nl).
            { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := base_ty) (ck := ck); eauto.
              intros z Hz.
              destruct (Hvars z) as (ty & Hfind & Hscopez); eauto using SECNLUSTYPING.wc_call_clock_free_in_vars. }
            assert (Hrstscope : st_scoped scope ((rty_nl :: nil) ⊔ rstty_nl)).
            { assert (Hinr : In (r, ckr) vars).
              { eapply Hreset. reflexivity. }
              assert (Hwc_ckr : wc_clock vars ckr).
              { eapply wc_env_var; eauto. }
              eapply st_scoped_merge.
              { apply st_scoped_singleton.
                destruct (Hvars r (In_InMembers r ckr vars Hinr)) as (ty & Hfind & Hscope_r).
                unfold SECNLUSTYPING.find_env in Hr_nl.
                rewrite Hfind in Hr_nl. inversion Hr_nl; subst. exact Hscope_r. }
              { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_ty) (ck := ckr); eauto.
                intros z Hz.
                destruct (Hvars z) as (ty & Hfind & Hscopez).
                { eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto. }
                exists ty. split; assumption. } }
            assert (HinpScope : Forall (st_scoped scope) inptyp_nl).
            { eapply SECNLUSTYPING.mmap_assign_exp_type_scoped.
              - eapply SECNLUSTYPING.wc_call_args_scoped; eauto.
              - exact Hinp_nl. }
            assert (HoutScope : Forall (fun x => In x scope) (outhd_nl :: outtl_nl)).
            { constructor.
              - assert (HxIn : In x (x :: xs)) by (left; reflexivity).
                destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                            Hvars Houtputs x HxIn)
                  as [ty [Hfind Hinscope]].
                unfold SECNLUSTYPING.find_env in Houthd_nl.
                rewrite Hfind in Houthd_nl. inversion Houthd_nl; subst. exact Hinscope.
              - eapply SECNLUSTYPING.mmap_find_env_scoped.
                + intros y Hy.
                  destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                              Hvars Houtputs y (or_intror Hy)) as [ty [Hfind Hscopey]].
                  exists ty. split.
                  * exact Hfind.
                  * exact Hscopey.
                + exact Houttl_nl. }
            assert (Hfresh_nl :
                      call_subst_fresh snl inptyp_nl ckty_nl ((rty_nl :: nil) ⊔ rstty_nl) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
            subst ckty_stc inptyp_stc outhd_stc outtl_stc rst_inst_call.
            assert (Hrstinst_gensym : exists n, rst_inst_reset = Ids.gensym Ids.sec_reset n).
            { exact (Hrstgen x rst_inst_reset st_rck_stc st_rstinst_reset Hrstinst_reset). }
            assert (Hfresh_stc :
                      call_subst_fresh sstc inptyp_nl ckty_nl (rst_inst_reset :: nil) (outhd_nl :: outtl_nl)).
	            { exact (call_subst_fresh_reset_from_scope_fresh
	                       scope sstc inptyp_nl ckty_nl rst_inst_reset (outhd_nl :: outtl_nl)
	                       Hsstcfresh Hsstcsec HinpScope Hckscope Hrstinst_gensym HoutScope). }
	            assert (Hnin : ~ In rst_inst_reset scope).
	            { exact (Hfresh x rst_inst_reset st_rck_stc st_rstinst_reset Hrstinst_reset). }
	            set (srcrst_call :=
	                                ((fix merge' (c2 : SymTypes.ST) : SymTypes.ST :=
	                                    match c2 with
	                       | nil => rty_nl :: nil
	                       | y :: ys =>
	                           match (rty_nl ?= y)%positive with
	                           | Eq =>
	                               rty_nl
	                               :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) ys
	                           | Lt =>
	                               rty_nl
	                               :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) c2
	                           | Gt => y :: merge' ys
	                           end
	                       end) rstty_nl)).
	            assert (Hsrcrstscope_call : st_scoped scope srcrst_call).
	            { unfold srcrst_call. change (st_scoped scope ((rty_nl :: nil) ⊔ rstty_nl)). exact Hrstscope. }
	            change
	              (generate_constraints snl inptyp_nl ckty_nl srcrst_call
	                 (outhd_nl :: outtl_nl) st_outtl_nl = OK (nconst, st1))
	              in Hcall_nl.
	            repeat rewrite app_nil_r.
	            cbn [app].
	            eexact (Hresetcall scope inptyp_nl ckty_nl srcrst_call
	                                (outhd_nl :: outtl_nl)
	                                ((fix merge' (c2 : SymTypes.ST) : SymTypes.ST :=
                                    match c2 with
                                    | nil => rst_ty :: nil
                                    | y :: ys =>
                                        match (rst_ty ?= y)%positive with
                                        | Eq =>
                                            rst_ty
                                            :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) ys
                                        | Lt =>
                                            rst_ty
                                            :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) c2
                                        | Gt => y :: merge' ys
                                        end
                                    end) rckty_stc)
	                                rst_inst_reset
	                                nconst c_call st_outtl_nl st_rstinst_call st1 st_call1
	                                (conj (conj HinpScope (conj Hckscope HoutScope)) Hsrcrstscope_call)
	                                Hnin Hfresh_nl Hfresh_stc Hcall_nl Hcall_stc).
          * simpl in Htr. subst trs. simpl in Hnl, Hstc.
            inversion Hwc as [x' ck' ce' Hx Hce
                             |xs' ck' f' exps' r' n' sub Hfindnode Hinputs Houtputs Hreset
                             |x' ck' v le Hx Hle]; subst.
            destruct (SECNLUSTYPING.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [Hsimplecall _]]]]].
            pose proof (Hscopefresh f snl Hfindnl) as Hsnlfresh.
            pose proof (scope_fresh_fields_agree scope snl sstc Hfields Hsnlfresh) as Hsstcfresh.
            rewrite Hfindstc in Hstc.
            eapply sec_bind_inv in Hnl as (ckty_nl & st_ck_nl & Hck_nl & Hnl).
            eapply sec_bind_inv in Hnl as (inptyp_nl & st_inp_nl & Hinp_nl & Hnl).
            eapply sec_bind_inv in Hnl as (outtyp_nl & st_out_nl & Hout_nl & Hcall_nl).
            simpl in Hstc.
            eapply sec_bind_inv in Hstc as (c_call & st_call1 & Hc_call & Hstc).
            eapply sec_bind_inv in Hstc as (c_nil_call & st_call2 & Hnil_call & Hret_call_blk).
            unfold ret in Hret_call_blk. inversion Hret_call_blk; subst sconst st2.
            unfold ret in Hnil_call. inversion Hnil_call; subst c_nil_call st_call2.
            simpl in Hc_call.
            eapply sec_bind_inv in Hc_call as (ckty_stc & st_ck_stc & Hck_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (inptyp_stc & st_inp_stc & Hinp_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (outtyp_stc & st_out_stc & Hout_stc & Hcall_stc).
            eapply sec_bind_inv in Hout_nl as (outhd_nl & st_outhd_nl & Houthd_nl & Hout_nl).
            eapply sec_bind_inv in Hout_nl as (outtl_nl & st_outtl_nl & Houttl_nl & Hret_out_nl).
            unfold ret in Hret_out_nl. inversion Hret_out_nl; subst outtyp_nl st_out_nl.
            eapply sec_bind_inv in Hout_stc as (outhd_stc & st_outhd_stc & Houthd_stc & Hout_stc).
            eapply sec_bind_inv in Hout_stc as (outtl_stc & st_outtl_stc & Houttl_stc & Hret_out_stc).
            unfold ret in Hret_out_stc. inversion Hret_out_stc; subst outtyp_stc st_out_stc.
            assert (Hck : ckty_nl = ckty_stc).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp : inptyp_nl = inptyp_stc).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthd : outhd_nl = outhd_stc).
            { eapply find_env_consistent_nl_stc; eauto. }
            assert (Houttl : outtl_nl = outtl_stc).
            { eapply mmap_find_env_consistent_nl_stc; eauto. }
            assert (Hckopt : assign_clk_type env base_ty ck = Some ckty_nl).
            { unfold option_to_sec in Hck_nl.
              destruct (assign_clk_type env base_ty ck) eqn:Hckopt; try discriminate.
              inversion Hck_nl; subst. reflexivity. }
            assert (Hckscope : st_scoped scope ckty_nl).
            { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := base_ty) (ck := ck); eauto.
              intros z Hz.
              destruct (Hvars z) as (ty & Hfind & Hscopez); eauto using SECNLUSTYPING.wc_call_clock_free_in_vars. }
            assert (Hrstsingle : st_scoped scope (rst_ty :: nil)).
            { apply st_scoped_singleton; exact Hrst. }
            assert (HinpScope : Forall (st_scoped scope) inptyp_nl).
            { eapply SECNLUSTYPING.mmap_assign_exp_type_scoped.
              - eapply SECNLUSTYPING.wc_call_args_scoped; eauto.
              - exact Hinp_nl. }
            assert (HoutScope : Forall (fun x => In x scope) (outhd_nl :: outtl_nl)).
            { constructor.
              - assert (HxIn : In x (x :: xs)) by (left; reflexivity).
                destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                            Hvars Houtputs x HxIn)
                  as [ty [Hfind Hinscope]].
                unfold SECNLUSTYPING.find_env in Houthd_nl.
                rewrite Hfind in Houthd_nl. inversion Houthd_nl; subst. exact Hinscope.
              - eapply SECNLUSTYPING.mmap_find_env_scoped.
                + intros y Hy.
                  destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                              Hvars Houtputs y (or_intror Hy)) as [ty [Hfind Hscopey]].
                  exists ty. split.
                  * exact Hfind.
                  * exact Hscopey.
                + exact Houttl_nl. }
            assert (Hfresh_nl :
                      call_subst_fresh snl inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
            subst ckty_stc inptyp_stc outhd_stc outtl_stc.
            assert (Hfresh_stc :
                      call_subst_fresh sstc inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
	            repeat rewrite app_nil_r.
	            cbn [app].
	            eexact (Hsimplecall scope inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)
	                                 nconst c_call st_outtl_nl st_outtl_stc st1 st_call1
	                                 (conj (conj HinpScope (conj Hckscope HoutScope)) Hrstsingle)
	                                 Hfresh_nl Hfresh_stc Hcall_nl Hcall_stc).
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
        secglobal_scope_fresh scope G1 ->
        secglobal_scope_sec G2 ->
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
            exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
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
                                      Hsig Hscopefresh Hglobsec Hscoped Henv Hwc Hvars Hbase Hrst
                                      Hextras Hnd Hrstgen Hfresh Hnl Hstc.
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
        + match goal with
          | Hnl1 : generate_eqn_constraint G1 env base_ty rst_ty e init_state1 = OK (_, _),
            Hstc1' : generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqn e) init_state2 = OK (_, _) |- _ =>
              eapply (eqn_preserv scope P vars G1 G2 e (translate_eqn e) env rst_env base_ty rst_ty
                                  _ _ init_state1 init_state2 _ _)
          end;
          [ exact Hsig
          | exact Hscopefresh
          | exact Hglobsec
          | exact Henv
          | exact Hwc_e
          | exact Hvars
          | exact Hbase
          | exact Hrst
          | reflexivity
          | exact Hrstgen
          | exact Hfresh
          | eassumption
          | eassumption ].
        + eapply (IH extras2 env rst_env base_ty rst_ty x1 sconst2
                     x0 st_mid st1 st2).
          * exact Hsig.
          * exact Hscopefresh.
          * exact Hglobsec.
          * exact Hscoped.
          * exact Henv.
          * exact Hwc_es.
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * exact Hextra2.
          * eapply NoDup_app_r; eauto.
          * exact Hrstgen.
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
        secglobal_scope_fresh scope G1 ->
        secglobal_scope_sec G2 ->
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
             Htr Hsig Hscopefresh Hglobsec Hscoped Hwc Haux Hclk Hrst Hinp Hout Hlocals Hscope
             Hresetenv Hextras Hnd Hfresh Hnl Hstc.
      subst scope.
      subst s. simpl in Hresetenv, Hstc.
      destruct Hwc as [_ [_ [Hwcenv Hwc]]].
      eapply (eqns_preserv_scoped
                (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                G1 G2 n.(n_eqs) extras env reset_env clk_type rst_type
                nconst sconst init_state st_reset st_n st_s).
      - exact Hsig.
      - exact Hscopefresh.
      - exact Hglobsec.
      - exact Hscoped.
      - exact Hwcenv.
      - exact Hwc.
      - eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings; eauto.
      - repeat rewrite in_app_iff. right. right. right. left. reflexivity.
      - repeat rewrite in_app_iff. right. right. right. right. left. reflexivity.
      - exact Hextras.
      - exact Hnd.
      - intros x0 rst_inst st1 st2 Hfind.
        unfold find_env in Hfind.
        destruct (Env.find x0 reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
        inversion Hfind; subst rst_inst st2.
        eapply generate_reset_env_range; eauto.
      - exact Hfresh.
      - exact Hnl.
      - exact Hstc.
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

    (** Visible-field provenance for generated NLustre signatures.

        Any identifier that appears in the visible scope of a generated source
        signature comes from a concrete key of the generating node: either one
        of its inputs/outputs or one of the node-specific clock/reset keys
        stored in [aux_names].  This is the source-side ingredient needed later
        to derive generated call freshness from the naming discipline. *)
    Lemma generated_node_sig_scope_key:
      forall G n env aux_names sig ty,
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
        In ty (sig_scope sig) ->
        exists clk_id rst_id x,
          get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
          /\ (In x (map fst n.(n_in))
              \/ In x (map fst n.(n_out))
              \/ x = clk_id
              \/ x = rst_id)
          /\ Env.find x env = Some ty.
    Proof.
      intros G n env aux_names sig ty Hsig Hin.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hsigdef); eauto.
      subst sig.
      unfold sig_scope in Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|Hin]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
          as (x & a & Hinx & Hfindx).
        exists clk_id, rst_id, x.
        split; [exact Haux|].
        split.
        + left. now apply in_map with (f := fst) in Hinx.
        + exact Hfindx.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
          as (x & a & Hinx & Hfindx).
        exists clk_id, rst_id, x.
        split; [exact Haux|].
        split.
        + right; left. now apply in_map with (f := fst) in Hinx.
        + exact Hfindx.
      - destruct Hin as [Hinclk|[Hinrst|[]]].
        + subst ty.
          exists clk_id, rst_id, clk_id.
          split; [exact Haux|].
          split.
          * right; right; left; reflexivity.
          * exact Hclk.
        + subst ty.
          exists clk_id, rst_id, rst_id.
          split; [exact Haux|].
          split.
          * right; right; right; reflexivity.
          * exact Hrst.
    Qed.

    (** Visible-field provenance for generated STC signatures.

        This is the target-local counterpart of
        [generated_node_sig_scope_key].  Visible identifiers of a generated STC
        signature come from the shared environment image of the system's
        inputs/outputs and the per-node clock/reset keys, never from STC-only
        hidden state. *)
    Lemma generated_sys_signature_scope_key:
      forall G s env aux_names sig ty,
        SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
        In ty (sig_scope sig) ->
        exists clk_id rst_id x,
          get_node_aux s.(SynStc.s_name) aux_names = Some (clk_id, rst_id)
          /\ (In x (map fst s.(SynStc.s_in))
              \/ In x (map fst s.(SynStc.s_out))
              \/ x = clk_id
              \/ x = rst_id)
          /\ Env.find x env = Some ty.
    Proof.
      intros G s env aux_names sig ty Hsig Hin.
      edestruct generate_sys_signature_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux & Hclk & Hrst & Hinp & Hout & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hsigdef); eauto.
      subst sig.
      unfold sig_scope in Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|Hin]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
          as (x & a & Hinx & Hfindx).
        exists clk_id, rst_id, x.
        split; [exact Haux|].
        split.
        + left. now apply in_map with (f := fst) in Hinx.
        + exact Hfindx.
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
          as (x & a & Hinx & Hfindx).
        exists clk_id, rst_id, x.
        split; [exact Haux|].
        split.
        + right; left. now apply in_map with (f := fst) in Hinx.
        + exact Hfindx.
      - destruct Hin as [Hinclk|[Hinrst|[]]].
        + subst ty.
          exists clk_id, rst_id, clk_id.
          split; [exact Haux|].
          split.
          * right; right; left; reflexivity.
          * exact Hclk.
        + subst ty.
          exists clk_id, rst_id, rst_id.
          split; [exact Haux|].
          split.
          * right; right; right; reflexivity.
          * exact Hrst.
    Qed.

    (** Namespace corollaries for generated visible signatures.

        Together with the naming-layer fact that every shared-environment value
        produced by [generate_node_env] lies in the [sec] namespace, the two
        provenance lemmas above imply that every visible identifier stored in a
        generated source/target signature also lies in that same namespace. *)
    Lemma generated_node_sig_scope_sec:
      forall all_nodes G n env aux_names sig,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
        signature_scope_sec sig.
    Proof.
      intros all_nodes G n env aux_names sig Henvgen Hsig ty Hin.
      destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
        as (clk_id & rst_id & x & _ & _ & Hfind).
      eapply SECNLUSTYPINGCORRECTNESS.generate_node_env_sec_range in Hfind; eauto.
    Qed.

    Lemma generated_sys_signature_scope_sec:
      forall all_nodes G s env aux_names sig,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECSTCTYPING.generate_sys_signature G s env aux_names = OK sig ->
        signature_scope_sec sig.
    Proof.
      intros all_nodes G s env aux_names sig Henvgen Hsig ty Hin.
      destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
        as (clk_id & rst_id & x & _ & _ & Hfind).
      eapply SECNLUSTYPINGCORRECTNESS.generate_node_env_sec_range in Hfind; eauto.
    Qed.

    (** Target-local namespace fact under one node-local env generation.

        This is the node-scoped counterpart of
        [generated_sys_signature_scope_sec]: once the current node's local
        security env has been generated, every visible identifier in the
        resulting STC signature lies in the [sec] namespace. *)
    Lemma generated_sys_signature_scope_sec_from_local_env:
      forall G n env aux_names rec st st' sig,
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        SECSTCTYPING.generate_sys_signature G (translate_node n) env aux_names = OK sig ->
        signature_scope_sec sig.
    Proof.
      intros G n env aux_names rec st st' sig Hlocal Hsig ty Hin.
      destruct (generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
        as (clk_id & rst_id & x & _ & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_sec_range in Hfind; eauto.
    Qed.

    (** Local lower bound for visible source signature identifiers.

        When a source signature is generated from one node-local env allocated
        starting at state [st], every visible identifier in that signature
        comes from the fresh [sec] interval allocated for that node, hence is
        at least [Pos.succ (Pos.succ st)] (the first two fresh names are the
        clock/reset helper keys). *)
    Lemma generated_node_sig_scope_lower_bound_from_local_env:
      forall G n env aux_names sig st rec st' ty,
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
        In ty (sig_scope sig) ->
        exists m, ty = Ids.gensym Ids.sec m /\ (Pos.succ (Pos.succ st) <= m)%positive.
    Proof.
      intros G n env aux_names sig st rec st' ty Hlocal Hsig Hin.
      destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
        as (clk_id & rst_id & x & _ & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_lower_bound in Hfind; eauto.
    Qed.

    (** Local upper bound for visible source signature identifiers.

        Dually, the same visible identifiers stay below the final state [st']
        returned by the node-local name generator.  This is the source-side
        “earlier than the current caller node” half of the eventual
        prefix-accumulator freshness proof. *)
    Lemma generated_node_sig_scope_upper_bound_from_local_env:
      forall G n env aux_names sig st rec st' ty,
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig ->
        In ty (sig_scope sig) ->
        exists m, ty = Ids.gensym Ids.sec m /\ (m < st')%positive.
    Proof.
      intros G n env aux_names sig st rec st' ty Hlocal Hsig Hin.
      destruct (generated_node_sig_scope_key _ _ _ _ _ _ Hsig Hin)
        as (clk_id & rst_id & x & _ & _ & Hfind).
      edestruct (NAMEGEN.generate_local_env_for_node_bounded
                   n st env rec st' Hlocal x ty Hfind)
        as (m & Hm & Hlt).
      exists m. split; assumption.
    Qed.

    Lemma node_scope_lower_bounded_from_local_env:
      forall n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals,
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        scope_lower_bounded (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) st.
    Proof.
      intros n st env rec st'
             clk_id rst_id clk_type rst_type inp out locals
             Hlocal Hclk Hrst Hinp Hout Hlocals ty Hin.
      repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
          as (xinp & ainp & _ & Hfindinp).
        edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                     n st env rec st' xinp ty Hlocal Hfindinp)
          as (m & Hm & Hlo).
        exists m. split; auto.
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
          as (xout & aout & _ & Hfindout).
        edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                     n st env rec st' xout ty Hlocal Hfindout)
          as (m & Hm & Hlo).
        exists m. split; auto.
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
      - destruct (get_mappings_from_node_In _ _ _ _ _ Hlocals Hin)
          as (xlocal & alocal & _ & Hfindlocal).
        edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                     n st env rec st' xlocal ty Hlocal Hfindlocal)
          as (m & Hm & Hlo).
        exists m. split; auto.
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
      - subst ty.
        edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                     n st env rec st' clk_id clk_type Hlocal Hclk)
          as (m & Hm & Hlo).
        exists m. split; auto.
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
      - subst ty.
        edestruct (NAMEGEN.generate_local_env_for_node_lower_bound
                     n st env rec st' rst_id rst_type Hlocal Hrst)
          as (m & Hm & Hlo).
        exists m. split; auto.
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
        eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
    Qed.

    Lemma node_scope_fresh_in_env_from_bounds:
      forall n st env aux_names G rec st',
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        secglobal_scope_bounded_above G st ->
        node_scope_fresh_in_env n env aux_names G.
    Proof.
      intros n st env aux_names G rec st' Hlocal Hbound
             clk_id rst_id clk_type rst_type inp out locals
             Haux Hclk Hrst Hinp Hout Hlocals.
      intros f sig Hfindsig.
      eapply scope_fresh_from_bounds.
      - eapply node_scope_lower_bounded_from_local_env; eauto.
      - eapply Hbound; eauto.
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
        Signature_consistent G1 G2 ->
        node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
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
             Hsig Hscopefreshenv Hglobsec Hscoped Hwc Henvgen Hnsig Hssig.
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
      pose proof (Hscopefreshenv
                    clk_id rst_id clk_type rst_type inp out nlocals
                    Haux Hclk Hrst Hinp Hout Hnlocals)
        as Hscopefresh.
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
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
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
               (nconst := nconst) (sconst := sconst);
          eauto.
    Qed.

    (** Node-scoped generated-node theorem.

        This is the same local generated bridge as
        [generated_node_preserv_scoped], but phrased over the new
        node-scoped naming layer.  The proof projects the current node's local
        env from the outer node-indexed table and reuses the raw node theorem
        on that recovered local env. *)
    Theorem generated_node_preserv_scoped_scoped_env:
      forall P all_nodes (n : node) (G1 G2: secglobal)
             (envs: node_scoped_env) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        (forall env,
            find_node_env n.(n_name) envs = Some env ->
            node_scope_fresh_in_env n env aux_names G1) ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        SECNLUSTYPING.generate_node_sig_scoped_env G1 n envs aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature_scoped_env G2 (translate_node n) envs aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros P all_nodes n G1 G2 envs aux_names nsig ssig
             Hsig Hfreshenv Hglobsec Hscoped Hwc Henvsgen Hfindnode Hnsig Hssig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
      destruct (find_node_env n.(n_name) envs) as [env|] eqn:Hfindenv; try discriminate.
      simpl in Hssig.
      rewrite Hfindenv in Hssig.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & nlocals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hnlocals & Hnconst & Hnsigdef); eauto.
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
      rewrite Hnsigdef in *.
      rewrite Hssigdef in *.
      assert (Hsameenv : Some env = Some env) by reflexivity.
      specialize (Hfreshenv env Hsameenv).
      pose proof (find_node_In _ _ _ Hfindnode) as [_ Hinall].
      apply in_split in Hinall as (prefix & suffix & Hall).
      subst all_nodes.
      edestruct NAMEGEN.generate_node_scoped_env_find_current
        as (local_env & rec & st_pref & st_local & Hlocalgen & Hlocalfind);
        eauto.
      rewrite Hfindenv in Hlocalfind. inversion Hlocalfind. subst local_env.
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
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          repeat rewrite in_app_iff in Hin.
          destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
              as (xinp & ainp & _ & Hfindinp).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xinp rst_inst
                         Hlocalgen Hfindinp) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
              as (xout & aout & _ & Hfindout).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xout rst_inst
                         Hlocalgen Hfindout) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hnlocals Hin)
              as (xlocal & alocal & _ & Hfindlocal).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xlocal rst_inst
                         Hlocalgen Hfindlocal) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - subst rst_inst.
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local clk_id clk_type
                         Hlocalgen Hclk) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - subst rst_inst.
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local rst_id rst_type
                         Hlocalgen Hrst) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
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
               (nconst := nconst) (sconst := sconst);
          eauto.
    Qed.

    (** Generated-node corollary under standard source-side well-formedness.

        This packages [generated_node_preserv_scoped] with the standard
        NLustre ordering/clocking facts needed to recover the local [wc_node]
        hypothesis. *)
    Corollary generated_node_preserv_scoped_global:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        generated_callers_scope_fresh all_nodes env aux_names G1 ->
        CloNL.wc_global all_nodes ->
        secglobal_scope_sec G2 ->
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
             Hsig Hfreshgen Hwcg Hglobsec Hscoped Henvgen Hfind Hnsig Hssig.
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
        Signature_consistent G1 G2 ->
        generated_callers_scope_fresh all_nodes env aux_names G1 ->
        CloNL.wc_global all_nodes ->
        secglobal_scope_sec G2 ->
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
             Hsig Hfreshgen Hwcg Hglobsec Hscoped Henvgen Hfind Hsys Hnsig Hssig.
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
        Signature_consistent G1 G2 ->
        node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        CloNL.wc_node P n ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready env aux_names ->
        signatures_preserved nsig ssig.
    Proof.
      intros all_nodes P n G1 G2 env aux_names nsig ssig
             Hcons Hscopefreshenv Hglobsec Hscoped Henvgen Hwc Hnsig Hssig Hready.
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
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (s := translate_node n)
               (G1 := G1) (G2 := G2)
               (env := env) (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (inp := inp) (out := out) (locals := locals)
               (reset_env := reset_env) (rids := rids) (extras := extras)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s).
        - reflexivity.
        - exact Hcons.
        - eapply Hscopefreshenv; eauto.
        - exact Hglobsec.
        - exact Hscoped.
        - exact Hwc.
        - exact Haux.
        - exact Hclk.
        - exact Hrst.
        - exact Hinp.
        - exact Hout.
        - exact Hlocals.
        - reflexivity.
        - exact Hresetenv.
        - exact Hextras.
        - exact Hnd.
        - exact Hfresh.
        - exact Hnconst.
        - exact Hsconst.
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

    (** Local simplify bridge under one node-scoped env generation.

        This is the node-scoped counterpart of
        [generated_signatures_preserved_from_simplify_bridge_scoped].  It
        avoids the old flat generated-env prerequisite and instead reasons from
        the one caller node's locally generated security env. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_local_env:
      forall P G1 G2 n env aux_names rec st st' nsig ssig,
        Signature_consistent G1 G2 ->
        node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst)) ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        signatures_preserved nsig ssig.
    Proof.
      intros P G1 G2 n env aux_names rec st st' nsig ssig
             Hcons Hscopefreshenv Hglobsec Hscoped Hwc Hlocal Hauxrec Hnsig Hssig.
      edestruct generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Hauxrec in Haux. inversion Haux. subst clk_id rst_id.
      rewrite Hauxrec in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      pose proof (Hscopefreshenv
                    rec.(nclk) rec.(nrst) clk_type rst_type inp out locals
                    Hauxrec Hclk Hrst Hinp Hout Hlocals)
        as Hscopefresh.
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
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          destruct
            (SECNLUSTYPINGCORRECTNESS.local_node_scope_sec_range
               n st env rec st'
               rec.(nclk) rec.(nrst) clk_type rst_type inp out locals rst_inst
               Hlocal Hclk Hrst Hinp Hout Hlocals Hin)
            as (nsec & Hscopeeq).
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (s := translate_node n)
               (G1 := G1) (G2 := G2)
               (env := env) (aux_names := aux_names)
               (clk_id := rec.(nclk)) (rst_id := rec.(nrst))
               (inp := inp) (out := out) (locals := locals)
               (reset_env := reset_env) (rids := rids)
               (nconst := nconst) (sconst := sconst)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s).
        - reflexivity.
        - exact Hcons.
        - exact Hscopefresh.
        - exact Hglobsec.
        - exact Hscoped.
        - exact Hwc.
        - exact Hauxrec.
        - exact Hclk.
        - exact Hrst.
        - exact Hinp.
        - exact Hout.
        - exact Hlocals.
        - reflexivity.
        - exact Hresetenv.
        - exact Hextras.
        - exact Hnd.
        - exact Hfresh.
        - exact Hnconst.
        - exact Hsconst.
      }
      rewrite Hnsigdef, Hssigdef.
      unfold signatures_preserved.
      split.
      - repeat split; reflexivity.
      - assert (Hnsig_local :
                  SECNLUSTYPING.generate_node_sig G1 n env aux_names =
                  OK
                    {| s_name := n.(n_name);
                       s_in := inp;
                       s_out := out;
                       s_reset := rst_type;
                       s_clk := clk_type;
                       s_constraints := SymTypes.simplify nconst locals |}).
        {
          rewrite <- Hnsigdef.
          exact Hnsig.
        }
        assert (Hclk_local : Env.find rec.(nclk) env = Some clk_type) by exact Hclk.
        assert (Hrst_local : Env.find rec.(nrst) env = Some rst_type) by exact Hrst.
        destruct (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_from_local_env
                    G1 n
                    {| s_name := n.(n_name);
                       s_in := inp;
                       s_out := out;
                       s_reset := rst_type;
                       s_clk := clk_type;
                       s_constraints := SymTypes.simplify nconst locals |}
                    env rec aux_names st st' clk_type rst_type inp out locals nconst st_n
                    Hlocal Hnsig_local Hclk_local Hrst_local Hinp Hout Hlocals Hnconst
                    ltac:(reflexivity))
          as [Hwf Hdisj].
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
          * apply Hagree_stc. exact Hinraw.
        + eapply simplify_is_correct.
          * exact Hsat_stc.
          * eapply simplify_simplifyRel. reflexivity.
    Qed.

    (** Scoped-env head-step simplify bridge.

        This is the generated-prefix counterpart of
        [generated_signatures_preserved_from_simplify_bridge_local_env].  The
        source accumulator carries only the structural bound that all already
        generated visible identifiers lie below the current naming state [st].
        The current caller node is then recovered from the node-scoped env run,
        and [node_scope_fresh_in_env_from_bounds] turns that bound into the
        exact local call-freshness fact consumed by the bridge. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_scoped_env:
      forall prefix P G1 G2 n envs aux_names
             envs_pref aux_pref st nsig ssig,
        NAMEGEN.generate_node_scoped_env' prefix (Env.empty _) nil NAMEGEN.init_state
          = OK ((envs_pref, aux_pref), st) ->
        generate_node_scoped_env (prefix ++ n :: P) = OK (envs, aux_names) ->
        Signature_consistent G1 G2 ->
        secglobal_scope_bounded_above G1 st ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        SECNLUSTYPING.generate_node_sig_scoped_env G1 n envs aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature_scoped_env G2 (translate_node n) envs aux_names = OK ssig ->
        signatures_preserved nsig ssig.
    Proof.
      intros prefix P G1 G2 n envs aux_names
             envs_pref aux_pref st nsig ssig
             Hprefgen Henvsgen Hcons Hbound Hglobsec Hscoped Hwc Hnsig Hssig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
      destruct (find_node_env n.(n_name) envs) as [env|] eqn:Hfindenv; try discriminate.
      assert (Hfindenv_sys : find_node_env (translate_node n).(SynStc.s_name) envs = Some env).
      { simpl. exact Hfindenv. }
      rewrite Hfindenv_sys in Hssig.
      unfold generate_node_scoped_env in Henvsgen.
      destruct (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: P) (Env.empty _) nil NAMEGEN.init_state)
        as [[[envs' aux'] st']|] eqn:Hrun; try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
            & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
        eauto.
      rewrite Hprefgen in Hpref. inversion Hpref; subst envs_pref' aux_pref' st_pref.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
        eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
        - pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
          unfold get_node_aux. simpl. rewrite <- Hrecname, ident_eqb_refl. reflexivity.
        - eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      rewrite Hfindenv in Hfindlocal. inversion Hfindlocal. subst local_env.
      eapply generated_signatures_preserved_from_simplify_bridge_local_env
        with (P := P) (rec := rec) (st := st) (st' := st_local); eauto.
      eapply node_scope_fresh_in_env_from_bounds; eauto.
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

	    Definition upd_type (dlt: ident -> Lat.t) (x: ident) (st: ST) : ident -> Lat.t :=
	      fun y => if ident_eqb y x then hm_ext dlt st else dlt y.

	    Definition upd_ident (dlt: ident -> Lat.t) (x v: ident) : ident -> Lat.t :=
	      fun y => if ident_eqb y x then dlt v else dlt y.

	    Fixpoint upd_types (dlt: ident -> Lat.t) (xs: list ident) (vs: list ST)
	      : ident -> Lat.t :=
	      match xs, vs with
	      | x :: xs', v :: vs' => upd_types (upd_type dlt x v) xs' vs'
	      | _, _ => dlt
	      end.

	    Fixpoint upd_types_rev (dlt: ident -> Lat.t) (xs: list ident) (vs: list ST)
	      : ident -> Lat.t :=
	      match xs, vs with
	      | x :: xs', v :: vs' => upd_type (upd_types_rev dlt xs' vs') x v
	      | _, _ => dlt
	      end.

	    Fixpoint upd_idents (dlt: ident -> Lat.t) (xs vs: list ident)
	      : ident -> Lat.t :=
	      match xs, vs with
	      | x :: xs', v :: vs' => upd_idents (upd_ident dlt x v) xs' vs'
	      | _, _ => dlt
	      end.

	    Fixpoint upd_idents_rev (dlt: ident -> Lat.t) (xs vs: list ident)
	      : ident -> Lat.t :=
	      match xs, vs with
	      | x :: xs', v :: vs' => upd_ident (upd_idents_rev dlt xs' vs') x v
	      | _, _ => dlt
	      end.

	    Definition inst_valuation
	      (dlt: ident -> Lat.t) (sig: signature)
	      (inp: list ST) (clk rst: ST) (out: list ident)
	      : ident -> Lat.t :=
	      upd_idents
	        (upd_type
	           (upd_type
	              (upd_types dlt sig.(s_in) inp)
	              sig.(s_clk) clk)
	           sig.(s_reset) rst)
	        sig.(s_out) out.

	    Definition overlay_scope
	      (scope: list ident) (dlt_scope dlt_base: ident -> Lat.t)
	      : ident -> Lat.t :=
	      fun x => if in_dec ident_eq_dec x scope then dlt_scope x else dlt_base x.

	    Lemma upd_type_outside:
	      forall dlt x st y,
	        x <> y ->
	        upd_type dlt x st y = dlt y.
	    Proof.
	      intros dlt x st y Hneq.
	      unfold upd_type.
	      destruct (ident_eqb y x) eqn:Heq.
	      - apply ident_eqb_eq in Heq. congruence.
	      - reflexivity.
	    Qed.

	    Lemma upd_ident_outside:
	      forall dlt x v y,
	        x <> y ->
	        upd_ident dlt x v y = dlt y.
	    Proof.
	      intros dlt x v y Hneq.
	      unfold upd_ident.
	      destruct (ident_eqb y x) eqn:Heq.
	      - apply ident_eqb_eq in Heq. congruence.
	      - reflexivity.
	    Qed.

	    Lemma upd_types_agree_on:
	      forall dlt scope xs vs,
	        Forall (fun x => ~ In x scope) xs ->
	        agree_on scope dlt (upd_types dlt xs vs).
	    Proof.
	      intros dlt scope xs.
	      revert dlt.
	      induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
	      - destruct vs; reflexivity.
	      - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
	        destruct vs as [|v vs].
	        + reflexivity.
	        + specialize (IH (upd_type dlt x v) vs Hxs y Hy).
	          unfold upd_types in IH |- *; simpl in IH |- *.
	          destruct (ident_eqb y x) eqn:Heq.
	          * apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hx Hy).
	          * transitivity ((upd_type dlt x v) y).
	            -- symmetry. apply upd_type_outside. intros Heqxy. subst y. exact (Hx Hy).
	            -- exact IH.
	    Qed.

	    Lemma upd_idents_agree_on:
	      forall dlt scope xs vs,
	        Forall (fun x => ~ In x scope) xs ->
	        agree_on scope dlt (upd_idents dlt xs vs).
	    Proof.
	      intros dlt scope xs.
	      revert dlt.
	      induction xs as [|x xs IH]; intros dlt vs Hfresh y Hy.
	      - destruct vs; reflexivity.
	      - inversion Hfresh as [|x' xs' Hx Hxs]; subst x' xs'.
	        destruct vs as [|v vs].
	        + reflexivity.
	        + specialize (IH (upd_ident dlt x v) vs Hxs y Hy).
	          unfold upd_idents in IH |- *; simpl in IH |- *.
	          destruct (ident_eqb y x) eqn:Heq.
	          * apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hx Hy).
	          * transitivity ((upd_ident dlt x v) y).
	            -- symmetry. apply upd_ident_outside. intros Heqxy. subst y. exact (Hx Hy).
	            -- exact IH.
	    Qed.

	    Lemma upd_type_agree_on:
	      forall dlt scope x st,
	        ~ In x scope ->
	        agree_on scope dlt (upd_type dlt x st).
	    Proof.
	      intros dlt scope x st Hfresh y Hin.
	      unfold upd_type.
	      destruct (ident_eqb y x) eqn:Heq.
	      - apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hfresh Hin).
	      - reflexivity.
	    Qed.

	    Lemma upd_ident_agree_on:
	      forall dlt scope x v,
	        ~ In x scope ->
	        agree_on scope dlt (upd_ident dlt x v).
	    Proof.
	      intros dlt scope x v Hfresh y Hin.
	      unfold upd_ident.
	      destruct (ident_eqb y x) eqn:Heq.
	      - apply ident_eqb_eq in Heq. subst y. exfalso. exact (Hfresh Hin).
	      - reflexivity.
	    Qed.

	    Lemma scope_fresh_notin_sig_scope:
	      forall scope sig x,
	        scope_fresh scope sig ->
	        In x (sig_scope sig) ->
	        ~ In x scope.
	    Proof.
	      intros scope sig x Hfresh Hsig Hscope.
	      exact (Hfresh x Hscope Hsig).
	    Qed.

	    Lemma scope_fresh_notin_inputs:
	      forall scope sig,
	        scope_fresh scope sig ->
	        Forall (fun x => ~ In x scope) sig.(s_in).
	    Proof.
	      intros scope sig Hfresh.
	      rewrite Forall_forall.
	      intros x Hin.
	      eapply scope_fresh_notin_sig_scope; eauto.
	      unfold sig_scope. apply in_or_app. now left.
	    Qed.

	    Lemma scope_fresh_notin_outputs:
	      forall scope sig,
	        scope_fresh scope sig ->
	        Forall (fun x => ~ In x scope) sig.(s_out).
	    Proof.
	      intros scope sig Hfresh.
	      rewrite Forall_forall.
	      intros x Hin.
	      eapply scope_fresh_notin_sig_scope; eauto.
	      unfold sig_scope. apply in_or_app. right. apply in_or_app. left. exact Hin.
	    Qed.

	    Lemma scope_fresh_notin_clk:
	      forall scope sig,
	        scope_fresh scope sig ->
	        ~ In sig.(s_clk) scope.
	    Proof.
	      intros scope sig Hfresh.
	      eapply scope_fresh_notin_sig_scope; eauto.
	      unfold sig_scope. apply in_or_app. right. apply in_or_app. right. simpl. left. reflexivity.
	    Qed.

	    Lemma scope_fresh_notin_reset:
	      forall scope sig,
	        scope_fresh scope sig ->
	        ~ In sig.(s_reset) scope.
	    Proof.
	      intros scope sig Hfresh.
	      eapply scope_fresh_notin_sig_scope; eauto.
	      unfold sig_scope. apply in_or_app. right. apply in_or_app. right. simpl. right. left. reflexivity.
	    Qed.

	    Lemma inst_valuation_agree_on_scope:
	      forall dlt sig scope inp clk rst out,
	        scope_fresh scope sig ->
	        agree_on scope dlt (inst_valuation dlt sig inp clk rst out).
	    Proof.
	      intros dlt sig scope inp clk rst out Hfresh.
	      unfold inst_valuation.
	      eapply agree_on_trans.
	      - eapply upd_types_agree_on.
	        eapply scope_fresh_notin_inputs; eauto.
	      - eapply agree_on_trans.
	        + eapply upd_type_agree_on.
	          eapply scope_fresh_notin_clk; eauto.
	        + eapply agree_on_trans.
	          * eapply upd_type_agree_on.
	            eapply scope_fresh_notin_reset; eauto.
	          * eapply upd_idents_agree_on.
	            eapply scope_fresh_notin_outputs; eauto.
	    Qed.

	    Lemma hm_ext_agree_on_st:
	      forall dlt1 dlt2 st,
	        agree_on st dlt1 dlt2 ->
	        hm_ext dlt1 st = hm_ext dlt2 st.
	    Proof.
	      intros dlt1 dlt2 st Hagree.
	      induction st as [|x st IH]; simpl; auto.
	      rewrite (Hagree x).
	      2:{ now left. }
	      rewrite IH; auto.
	      intros y Hy. apply Hagree. now right.
	    Qed.

	    Lemma overlay_scope_agree_on:
	      forall scope dlt_scope dlt_base,
	        agree_on scope dlt_scope (overlay_scope scope dlt_scope dlt_base).
	    Proof.
	      intros scope dlt_scope dlt_base x Hin.
	      unfold overlay_scope.
	      destruct (in_dec ident_eq_dec x scope) as [Hin'|Hnin].
	      - reflexivity.
	      - contradiction.
	    Qed.

	    Lemma overlay_scope_agree_outside:
	      forall scope dlt_scope dlt_base x,
	        ~ In x scope ->
	        overlay_scope scope dlt_scope dlt_base x = dlt_base x.
	    Proof.
	      intros scope dlt_scope dlt_base x Hfresh.
	      unfold overlay_scope.
	      destruct (in_dec ident_eq_dec x scope) as [Hin|Hnin].
	      - contradiction.
	      - reflexivity.
	    Qed.

	    Lemma overlay_scope_agree_on_sig_scope:
	      forall scope sig dlt_scope dlt_base,
	        scope_fresh scope sig ->
	        agree_on (sig_scope sig) dlt_base (overlay_scope scope dlt_scope dlt_base).
	    Proof.
	      intros scope sig dlt_scope dlt_base Hfresh x Hin.
	      symmetry.
	      apply overlay_scope_agree_outside.
	      intro Hscope.
	      exact (Hfresh x Hscope Hin).
	    Qed.

	    Lemma hm_ext_agree_on_scoped_type:
	      forall scope ty dlt1 dlt2,
	        st_scoped scope ty ->
	        agree_on scope dlt1 dlt2 ->
	        hm_ext dlt1 ty = hm_ext dlt2 ty.
	    Proof.
	      intros scope ty dlt1 dlt2 Hsc Hagree.
	      apply hm_ext_agree_on_st.
	      intros x Hin.
	      apply Hagree.
	      exact (Hsc _ Hin).
	    Qed.

	    Lemma upd_ident_eq_upd_type_singleton:
	      forall dlt x v y,
	        x <> v ->
	        upd_ident dlt x v y = upd_type dlt x ([v]) y.
	    Proof.
	      intros dlt x v y Hneq.
	      unfold upd_ident, upd_type.
	      destruct (ident_eqb y x) eqn:Hyx.
	      - simpl. rewrite <- join_bottom_eq1. reflexivity.
	      - reflexivity.
	    Qed.

	    Lemma sym_st_remove_notin:
	      forall d st,
	        SymTypes.my_set_mem d st = false ->
	        SymTypes.st_remove d st = st.
	    Proof.
	      intros d st.
	      induction st as [|a st IH]; intro Hmem; simpl in *; auto.
	      destruct (ident_eqb d a) eqn:Hda.
	      - apply ident_eqb_eq in Hda. subst a.
	        rewrite ident_eqb_refl in Hmem.
	        discriminate.
	      - apply ident_eqb_neq in Hda.
	        unfold SymTypes.st_remove. simpl.
	        destruct (ident_eq_dec d a) as [Heq|Hneq].
	        + contradiction.
	        + assert (Hda' : ident_eqb a d = false).
	          { apply (proj2 (ident_eqb_neq a d)). congruence. }
	          rewrite Hda' in Hmem.
	          f_equal. apply IH. exact Hmem.
	    Qed.

	    Lemma sym_st_remove_preserves_other_in:
	      forall x d st,
	        x <> d ->
	        In x st ->
	        In x (SymTypes.st_remove d st).
	    Proof.
	      intros x d st Hneq Hin.
	      induction st as [|a st IH]; simpl in *.
	      - contradiction.
	      - destruct Hin as [Heq|Hin].
	        + subst a.
	          unfold SymTypes.st_remove. simpl.
	          destruct (ident_eq_dec d x) as [Hdx|Hdx].
	          * exfalso. apply Hneq. symmetry. exact Hdx.
	          * left. reflexivity.
	        + unfold SymTypes.st_remove. simpl.
	          destruct (ident_eq_dec d a) as [Hda|Hda].
	          * apply IH. exact Hin.
	          * right. apply IH. exact Hin.
	    Qed.

	    Lemma hm_ext_upd_type_subst_le_l:
	      forall dlt x st ty,
	        ~ In x st ->
	        hm_ext (upd_type dlt x st) ty ⊑ hm_ext dlt (SIG.subst_ident_in_type ty x st).
	    Proof.
	      intros dlt x st ty Hfresh.
	      apply hm_ext_bound_from_members.
	      intros y Hy.
	      destruct (ident_eq_dec y x) as [Heq|Hneq].
		      - subst y.
		        unfold upd_type. rewrite ident_eqb_refl.
		        unfold SIG.subst_ident_in_type.
		        destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
		        + assert (Hmemst : SymTypes.my_set_mem x st = false).
		          {
		            destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
		            exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
		          }
		          assert (Heqst : SymTypes.st_remove x st = st).
		          { apply sym_st_remove_notin. exact Hmemst. }
		          rewrite Heqst.
		          change (hm_ext dlt st ⊑
		                  hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st)).
		          eapply order_trans.
		          * apply hm_ext_concat_r.
		          * apply order_refl, eq_refl.
	        + exfalso.
	          apply (proj2 (SymTypes.my_set_mem_correct x ty)) in Hy.
	          rewrite Hmem in Hy. discriminate.
		      - rewrite upd_type_outside by (intro Heq; apply Hneq; symmetry; exact Heq).
		        unfold SIG.subst_ident_in_type.
		        destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
		        + assert (Hmemst : SymTypes.my_set_mem x st = false).
		          {
		            destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
		            exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
		          }
		          assert (Heqst : SymTypes.st_remove x st = st).
		          { apply sym_st_remove_notin. exact Hmemst. }
		          rewrite Heqst.
		          change (dlt y ⊑ hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st)).
		          assert (Hinrm : In y (SymTypes.st_remove x ty)).
		          { eapply sym_st_remove_preserves_other_in; eauto. }
		          eapply order_trans.
	          * eapply hm_ext_list_in1. exact Hinrm.
	          * apply hm_ext_concat_l.
	        + eapply hm_ext_list_in1. exact Hy.
	    Qed.

	    Lemma hm_ext_upd_type_subst_le_r:
	      forall dlt x st ty,
	        ~ In x st ->
	        hm_ext dlt (SIG.subst_ident_in_type ty x st) ⊑ hm_ext (upd_type dlt x st) ty.
	    Proof.
		      intros dlt x st ty Hfresh.
		      unfold SIG.subst_ident_in_type.
		      destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
		      - assert (Hmemst : SymTypes.my_set_mem x st = false).
		        {
		          destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
		          exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
		        }
		        assert (Heqst : SymTypes.st_remove x st = st).
		        { apply sym_st_remove_notin. exact Hmemst. }
		        rewrite Heqst.
		        change (hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st) ⊑
		                hm_ext (upd_type dlt x st) ty).
		        apply hm_ext_bound_from_members.
	        intros y Hin.
	        destruct (in_merge_inv _ _ _ Hin) as [Hinrm|Hinst].
	        + destruct (st_remove_in_inv _ _ _ Hinrm) as [Hinty Hneq].
	          assert (Hxny : x <> y).
	          { intro Heq. apply Hneq. symmetry. exact Heq. }
	          assert (Heqout : eq (dlt y) (upd_type dlt x st y)).
	          {
	            apply (proj2 (eq_no_red _ _)).
	            symmetry. apply upd_type_outside. exact Hxny.
	          }
	          eapply order_trans.
	          * apply order_refl.
	            exact Heqout.
	          * eapply hm_ext_list_in1. exact Hinty.
	        + assert (Hinty : In x ty).
	          { apply SymTypes.my_set_mem_correct. exact Hmem. }
	          assert (Heqx : eq (hm_ext dlt st) (upd_type dlt x st x)).
	          {
	            apply (proj2 (eq_no_red _ _)).
	            unfold upd_type. rewrite ident_eqb_refl. reflexivity.
	          }
	          eapply order_trans.
	          * eapply hm_ext_list_in1. exact Hinst.
	          * eapply order_trans.
	            -- apply order_refl. exact Heqx.
	            -- eapply hm_ext_list_in1. exact Hinty.
	      - apply hm_ext_bound_from_members.
	        intros y Hin.
	        assert (Hneq : y <> x).
	        { intro Heq. subst y.
	          apply SymTypes.my_set_mem_correct in Hin.
	          rewrite Hin in Hmem. discriminate.
	        }
	        assert (Hxny : x <> y).
	        { intro Heq. apply Hneq. symmetry. exact Heq. }
	        assert (Heqout : eq (dlt y) (upd_type dlt x st y)).
	        {
	          apply (proj2 (eq_no_red _ _)).
	          symmetry. apply upd_type_outside. exact Hxny.
	        }
	        eapply order_trans.
	        + apply order_refl.
	          exact Heqout.
	        + eapply hm_ext_list_in1. exact Hin.
	    Qed.

	    Lemma hm_ext_upd_type_subst:
	      forall dlt x st ty,
	        ~ In x st ->
	        hm_ext (upd_type dlt x st) ty = hm_ext dlt (SIG.subst_ident_in_type ty x st).
	    Proof.
	      intros dlt x st ty Hfresh.
	      apply eq_no_red.
	      apply order_antisym.
	      - apply hm_ext_upd_type_subst_le_l; exact Hfresh.
	      - apply hm_ext_upd_type_subst_le_r; exact Hfresh.
	    Qed.

	    Lemma hm_ext_upd_ident_subst:
	      forall dlt x v ty,
	        x <> v ->
	        hm_ext (upd_ident dlt x v) ty = hm_ext dlt (SIG.subst_ident_in_type ty x [v]).
	    Proof.
	      intros dlt x v ty Hneq.
	      rewrite (hm_ext_agree_on_st (upd_ident dlt x v) (upd_type dlt x [v]) ty).
	      - apply hm_ext_upd_type_subst.
	        simpl. intros [Heq|[]]. subst v. contradiction.
	      - intros y Hin.
	        apply upd_ident_eq_upd_type_singleton; exact Hneq.
	    Qed.

	    Lemma subst_ident_constraint_complete_out:
	      forall c x v c' st st',
	        SIG.subst_ident_constraint c x v st = OK (c', st') ->
	        forall dlt,
	          constraintSatisfiable dlt c' ->
	          constraintSatisfiable (upd_ident dlt x v) c.
	    Proof.
	      intros [lhs rhs] x v c' st st' Hsub dlt Hsat.
	      unfold SIG.subst_ident_constraint in Hsub.
	      destruct (ident_eqb x v) eqn:Hxv; try discriminate.
	      apply ident_eqb_neq in Hxv as Hneq.
	      destruct rhs as [|r rhs']; try discriminate.
	      destruct rhs' as [|r' rhs'']; try discriminate.
	      unfold ret in Hsub.
	      destruct (ident_eqb x r) eqn:Hxr; inversion Hsub; subst c' st'; clear Hsub.
	      - apply ident_eqb_eq in Hxr. subst r.
	        unfold constraintSatisfiable, satisfiable in *.
	        simpl in Hsat.
	        rewrite <- hm_ext_upd_ident_subst in Hsat by exact Hneq.
	        simpl.
	        unfold upd_ident.
	        rewrite ident_eqb_refl.
	        exact Hsat.
	      - apply ident_eqb_neq in Hxr.
	        unfold constraintSatisfiable, satisfiable in *.
	        simpl in Hsat.
	        rewrite <- hm_ext_upd_ident_subst in Hsat by exact Hneq.
	        simpl.
	        rewrite upd_ident_outside by exact Hxr.
	        exact Hsat.
	    Qed.

	    Lemma subst_ident_constraints_complete_out:
	      forall cs x v cs' st st',
	        SIG.subst_ident_constraints cs x v st = OK (cs', st') ->
	        forall dlt,
	          listSatisfiable dlt cs' ->
	          listSatisfiable (upd_ident dlt x v) cs.
	    Proof.
	      induction cs as [|c cs IH]; intros x v cs' st st' Hsub dlt Hsat.
	      - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
	      - simpl in Hsub.
	        eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
	        eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
	        unfold ret in Hret. inversion Hret; subst cs' st'.
	        inversion Hsat; subst.
	        constructor.
	        + eapply subst_ident_constraint_complete_out; eauto.
	        + eapply IH; eauto.
	    Qed.

	    Lemma subst_inp_ident_in_constraint_complete:
	      forall c x ty c' st st',
	        ~ In x ty ->
	        SIG.subst_inp_ident_in_constraint c x ty st = OK (c', st') ->
	        forall dlt,
	          constraintSatisfiable dlt c' ->
	          constraintSatisfiable (upd_type dlt x ty) c.
	    Proof.
	      intros [lhs rhs] x ty c' st st' Hfresh Hsub dlt Hsat.
	      unfold SIG.subst_inp_ident_in_constraint in Hsub.
	      destruct rhs as [|r rhs']; try discriminate.
	      destruct rhs' as [|r' rhs'']; try discriminate.
	      destruct (ident_eqb x r) eqn:Hxr; try discriminate.
	      unfold ret in Hsub. inversion Hsub; subst c' st'; clear Hsub.
	      apply ident_eqb_neq in Hxr.
	      unfold constraintSatisfiable, satisfiable in *.
	      simpl in Hsat.
	      rewrite <- hm_ext_upd_type_subst in Hsat by exact Hfresh.
	      simpl.
	      rewrite upd_type_outside by exact Hxr.
	      exact Hsat.
	    Qed.

	    Lemma subst_ident_in_constraints_complete:
	      forall cs x ty cs' st st',
	        ~ In x ty ->
	        SIG.subst_ident_in_constraints cs x ty st = OK (cs', st') ->
	        forall dlt,
	          listSatisfiable dlt cs' ->
	          listSatisfiable (upd_type dlt x ty) cs.
	    Proof.
	      induction cs as [|c cs IH]; intros x ty cs' st st' Hfresh Hsub dlt Hsat.
	      - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
	      - simpl in Hsub.
	        eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
	        eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
	        unfold ret in Hret. inversion Hret; subst cs' st'.
	        inversion Hsat; subst.
	        constructor.
	        + eapply subst_inp_ident_in_constraint_complete; eauto.
	        + eapply IH; eauto.
	    Qed.

	    Lemma wf_constraints_rhs_unique:
	      forall cs lhs1 lhs2 x,
	        wf_constraints cs ->
	        In (lhs1, [x]) cs ->
	        In (lhs2, [x]) cs ->
	        lhs1 = lhs2.
	    Proof.
	      induction cs as [|[lhs rhs] cs IH]; intros lhs1 lhs2 x Hwf Hin1 Hin2.
	      - contradiction.
	      - unfold wf_constraints in Hwf.
	        destruct Hwf as [Hnd Hall].
	        simpl in Hin1, Hin2.
	        destruct Hin1 as [Hin1|Hin1]; destruct Hin2 as [Hin2|Hin2].
	        + inversion Hin1; inversion Hin2; subst; congruence.
	        + inversion Hin1; subst lhs rhs.
	          inversion Hnd as [|? ? Hnotin _]; subst.
	          exfalso. apply Hnotin.
	          apply in_map_iff.
	          exists (lhs2, [x]). split; [reflexivity|exact Hin2].
	        + inversion Hin2; subst lhs rhs.
	          inversion Hnd as [|? ? Hnotin _]; subst.
	          exfalso. apply Hnotin.
	          apply in_map_iff.
	          exists (lhs1, [x]). split; [reflexivity|exact Hin1].
	        + eapply IH.
	          * eapply wf_constraints_no_nil.
	            exact (conj Hnd Hall).
	          * exact Hin1.
	          * exact Hin2.
	    Qed.

	    Lemma findST_wf_exact:
	      forall cs lhs x,
	        wf_constraints cs ->
	        In (lhs, [x]) cs ->
	        findST cs x = Some lhs.
	    Proof.
	      intros cs lhs x Hwf Hin.
	      assert (Hinrhs : In [x] (map snd cs)).
	      { apply in_map_iff. exists (lhs, [x]). split; [reflexivity|exact Hin]. }
	      destruct (findST_of_rhs_in _ _ Hinrhs) as [lhs' Hfind].
	      pose proof (find_correct _ _ _ Hfind) as Hinfind.
	      assert (lhs' = lhs).
	      { eapply wf_constraints_rhs_unique; eauto. }
	      subst lhs'. exact Hfind.
	    Qed.

	    Lemma reorder_constraints_member:
	      forall src outs cns st st' x lhs,
	        SC.mmap
	          (fun y : ident =>
	             SC.bind (option_to_sec (findST src y))
	                     (fun st0 => SC.ret (st0, [y]))) outs st = OK (cns, st') ->
	        In x outs ->
	        findST src x = Some lhs ->
	        In (lhs, [x]) cns.
	    Proof.
	      induction outs as [|y outs IH]; intros cns st st' x lhs Hmap Hin Hfind.
	      - contradiction.
	      - simpl in Hmap.
	        eapply sec_bind_inv in Hmap as (cy & st1 & Hhd & Hmap).
	        eapply sec_bind_inv in Hmap as (cys & st2 & Htl & Hret).
	        unfold option_to_sec in Hhd.
	        destruct (findST src y) as [lhsy|] eqn:Hfindy; try discriminate.
	        unfold ret in Hhd. inversion Hhd; subst cy st1.
	        unfold ret in Hret. inversion Hret; subst cns st'.
	        simpl in Hin.
	        destruct Hin as [Heq|Hin].
	        + subst x.
	          rewrite Hfind in Hfindy. inversion Hfindy; subst lhsy.
	          simpl. now left.
	        + simpl. right. eapply IH; eauto.
	    Qed.

	    Lemma reorder_constraints_correct:
	      forall src outs cns st st' dlt,
	        SC.mmap
	          (fun x : ident =>
	             SC.bind (option_to_sec (findST src x))
	                     (fun st0 => SC.ret (st0, [x]))) outs st = OK (cns, st') ->
	        listSatisfiable dlt src ->
	        listSatisfiable dlt cns.
	    Proof.
	      induction outs as [|x outs IH]; intros cns st st' dlt Hmap Hsat.
	      - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. constructor.
	      - simpl in Hmap.
	        eapply sec_bind_inv in Hmap as (cx & st1 & Hhd & Hmap).
	        eapply sec_bind_inv in Hmap as (cxs & st2 & Htl & Hret).
	        unfold option_to_sec in Hhd.
	        destruct (findST src x) as [lhs|] eqn:Hfind; try discriminate.
	        unfold ret in Hhd. inversion Hhd; subst cx st1.
	        unfold ret in Hret. inversion Hret; subst cns st'.
	        constructor.
	        + unfold listSatisfiable in Hsat.
	          rewrite Forall_forall in Hsat.
	          specialize (Hsat _ (find_correct _ _ _ Hfind)).
	          exact Hsat.
	        + eapply IH; eauto.
	    Qed.

	    Lemma reorder_constraints_complete:
	      forall src outs cns st st' dlt,
	        wf_constraints src ->
	        Permutation (map snd src) (map (fun x => [x]) outs) ->
	        SC.mmap
	          (fun x : ident =>
	             SC.bind (option_to_sec (findST src x))
	                     (fun st0 => SC.ret (st0, [x]))) outs st = OK (cns, st') ->
	        listSatisfiable dlt cns ->
	        listSatisfiable dlt src.
	    Proof.
	      intros src outs cns st st' dlt Hwf Hperm Hmap Hsat.
	      unfold listSatisfiable.
	      rewrite Forall_forall.
	      intros [lhs rhs] Hin.
	      destruct (wf_constraints_shape _ _ _ Hwf Hin) as [x Hrhs].
	      subst rhs.
	      assert (Hinrhs : In [x] (map snd src)).
	      { apply in_map_iff. exists (lhs, [x]). split; [reflexivity|exact Hin]. }
	      assert (Hinouts : In x outs).
	      {
	        assert (Hinouts' : In [x] (map (fun y => [y]) outs)).
	        { eapply Permutation_in; [exact Hperm|exact Hinrhs]. }
	        apply in_map_iff in Hinouts' as (y & Hy & Hiny).
	        inversion Hy; subst y. exact Hiny.
	      }
	      assert (Hfind : findST src x = Some lhs).
	      { eapply findST_wf_exact; eauto. }
	      unfold listSatisfiable in Hsat.
	      rewrite Forall_forall in Hsat.
	      specialize (Hsat _ (reorder_constraints_member _ _ _ _ _ _ _ Hmap Hinouts Hfind)).
	      exact Hsat.
	    Qed.

	    Lemma subst_ident_constraint_correct_out:
	      forall c x v c' st st',
	        SIG.subst_ident_constraint c x v st = OK (c', st') ->
	        forall dlt,
	          dlt v = dlt x ->
	          constraintSatisfiable dlt c ->
	          constraintSatisfiable dlt c'.
	    Proof.
	      intros [lhs rhs] x v c' st st' Hsub dlt Hveq Hsat.
	      unfold SIG.subst_ident_constraint in Hsub.
	      destruct (ident_eqb x v) eqn:Hxv; try discriminate.
	      apply ident_eqb_neq in Hxv as Hneq.
	      destruct rhs as [|r rhs']; try discriminate.
	      destruct rhs' as [|r' rhs'']; try discriminate.
	      unfold ret in Hsub.
	      destruct (ident_eqb x r) eqn:Hxr; inversion Hsub; subst c' st'; clear Hsub.
	      - apply ident_eqb_eq in Hxr. subst r.
	        unfold constraintSatisfiable, satisfiable in *.
	        simpl in Hsat |- *.
	        rewrite <- (hm_ext_upd_ident_subst dlt x v lhs Hneq).
	        rewrite (hm_ext_agree_on_st (upd_ident dlt x v) dlt lhs).
	        + rewrite Hveq. exact Hsat.
	        + intros y Hy.
	          unfold upd_ident.
	          destruct (ident_eqb y x) eqn:Hyx; auto.
	          apply ident_eqb_eq in Hyx. subst y.
	          exact Hveq.
	      - unfold constraintSatisfiable, satisfiable in *.
	        simpl in Hsat |- *.
	        rewrite <- (hm_ext_upd_ident_subst dlt x v lhs Hneq).
	        rewrite (hm_ext_agree_on_st (upd_ident dlt x v) dlt lhs).
	        + exact Hsat.
	        + intros y Hy.
	          unfold upd_ident.
	          destruct (ident_eqb y x) eqn:Hyx; auto.
	          apply ident_eqb_eq in Hyx. subst y.
	          exact Hveq.
	    Qed.

	    Lemma subst_ident_constraints_correct_out:
	      forall cs x v cs' st st',
	        SIG.subst_ident_constraints cs x v st = OK (cs', st') ->
	        forall dlt,
	          dlt v = dlt x ->
	          listSatisfiable dlt cs ->
	          listSatisfiable dlt cs'.
	    Proof.
	      induction cs as [|c cs IH]; intros x v cs' st st' Hsub dlt Hveq Hsat.
	      - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
	      - simpl in Hsub.
	        eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
	        eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
	        unfold ret in Hret. inversion Hret; subst cs' st'.
	        inversion Hsat; subst.
	        constructor.
	        + eapply subst_ident_constraint_correct_out; eauto.
	        + eapply IH; eauto.
	    Qed.

	    Lemma subst_constraints_out_map_correct:
	      forall cs xs vs cs' st st',
	        SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
	        forall dlt,
	          listSatisfiable dlt cs ->
	          Forall2 (fun x v => dlt v = dlt x) xs vs ->
	          listSatisfiable dlt cs'.
	    Proof.
	      intros cs xs.
	      revert cs.
	      induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub dlt Hsat Hrel.
	      - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
	        unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
	      - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
	        inversion Hrel as [|x' v' xs' vs' Heq Hrel']; subst x' v' xs' vs'.
	        simpl in Hsub.
	        revert Hsub.
	        destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; simpl in Hsub.
	        + discriminate.
	        + eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
	          eapply IH with (cs := cs1) (dlt := dlt) in Htl; eauto.
	          eapply subst_ident_constraints_correct_out; eauto.
	    Qed.

	    Lemma subst_constraints_out_map_complete:
	      forall cs xs vs cs' st st',
	        SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
	        forall dlt,
	          listSatisfiable dlt cs' ->
	          listSatisfiable (upd_idents_rev dlt xs vs) cs.
	    Proof.
	      intros cs xs.
	      revert cs.
	      induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub dlt Hsat.
	      - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
	        unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
	      - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
	        simpl in Hsub.
	        revert Hsub.
	        destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; simpl in Hsub.
	        + discriminate.
	        + eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
	          pose proof (IH cs1 vs cs' st1 st' Htl dlt Hsat) as Hmid.
	          change (listSatisfiable (upd_ident (upd_idents_rev dlt xs vs) x v) cs).
	          eapply subst_ident_constraints_complete_out; eauto.
	    Qed.

	    Lemma subst_constraints_inp_map_complete:
	      forall cs xs tys cs' st st',
	        Forall2 (fun x ty => ~ In x ty) xs tys ->
	        SIG.subst_constraints_inp_map cs xs tys st = OK (cs', st') ->
	        forall dlt,
	          listSatisfiable dlt cs' ->
	          listSatisfiable (upd_types_rev dlt xs tys) cs.
	    Proof.
	      intros cs xs.
	      revert cs.
	      induction xs as [|x xs IH]; intros cs tys cs' st st' Hfresh Hsub dlt Hsat.
	      - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
	        unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
	      - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
	        inversion Hfresh as [|x' ty' xs' tys' Hxy Hfresh']; subst x' ty' xs' tys'.
	        eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
	        pose proof (IH cs1 tys cs' st1 st' Hfresh' Htl dlt Hsat) as Hmid.
	        change (listSatisfiable (upd_type (upd_types_rev dlt xs tys) x ty) cs).
	        eapply subst_ident_in_constraints_complete; eauto.
	    Qed.

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
        - each concrete call instantiation must satisfy the local freshness
          premises now required by [Signature_call_preserves].

        Once the corresponding metatheory is proved in the signature layer,
        this premise should disappear entirely. *)
    Definition signatures_preserved_calls : Prop :=
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

    Lemma generate_all_source_signatures_scope_sec':
      forall all_nodes nodes acc env aux_names G,
        generate_node_env all_nodes = OK (env, aux_names) ->
        secglobal_scope_sec acc ->
        SECNLUSTYPING.generate_all_signatures' acc nodes env aux_names = OK G ->
        secglobal_scope_sec G.
    Proof.
      intros all_nodes nodes.
      induction nodes as [|n nodes IH]; intros acc env aux_names G Henvgen Hacc Hgen.
      - simpl in Hgen. inversion Hgen; subst. exact Hacc.
      - simpl in Hgen.
        destruct (SECNLUSTYPING.generate_node_sig acc n env aux_names) as [sig|e] eqn:Hsig;
          simpl in Hgen; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures' (sig :: acc) nodes env aux_names) as [G'|e] eqn:Htl;
          simpl in Hgen; try discriminate.
        inversion Hgen; subst.
        eapply IH with (acc := sig :: acc) (env := env) (aux_names := aux_names).
        + exact Henvgen.
        + eapply secglobal_scope_sec_cons; eauto.
          eapply generated_node_sig_scope_sec; eauto.
        + exact Htl.
    Qed.

    Corollary generate_all_source_signatures_scope_sec:
      forall all_nodes env aux_names G,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.generate_all_signatures all_nodes env aux_names = OK G ->
        secglobal_scope_sec G.
    Proof.
      intros all_nodes env aux_names G Henvgen Hgen.
      unfold SECNLUSTYPING.generate_all_signatures in Hgen.
      eapply generate_all_source_signatures_scope_sec'; eauto.
      apply secglobal_scope_sec_nil.
    Qed.

    Corollary generate_all_translated_system_signatures_scope_sec:
      forall all_nodes env aux_names G,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G ->
        secglobal_scope_sec G.
    Proof.
      intros all_nodes env aux_names G Henvgen.
      unfold SECSTCTYPING.generate_all_sys_signatures.
      assert (Haccsec:
                forall todo acc G',
                  secglobal_scope_sec acc ->
                  SECSTCTYPING.generate_all_sys_signatures' acc (translate todo) env aux_names = OK G' ->
                  secglobal_scope_sec G').
      {
        intros todo.
        induction todo as [|n todo IHtodo]; intros acc G' Haccsec Hgen'.
        - simpl in Hgen'. inversion Hgen'; subst. exact Haccsec.
        - simpl in Hgen'.
          destruct (SECSTCTYPING.generate_sys_signature acc (translate_node n) env aux_names) as [sig'|e] eqn:Hsig';
            simpl in Hgen'; try discriminate.
          destruct (SECSTCTYPING.generate_all_sys_signatures' (sig' :: acc) (translate todo) env aux_names) as [G''|e] eqn:Htl';
            simpl in Hgen'; try discriminate.
          inversion Hgen'; subst. eapply IHtodo.
          + eapply secglobal_scope_sec_cons; eauto.
            eapply generated_sys_signature_scope_sec; eauto.
          + exact Htl'.
      }
      intro Hgen.
      eapply Haccsec; eauto.
      apply secglobal_scope_sec_nil.
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
      forall prefix nodes acc1 acc2 envs aux_names
             envs_pref aux_pref st G1 G2,
        NAMEGEN.generate_node_scoped_env' prefix (Env.empty _) nil NAMEGEN.init_state
          = OK ((envs_pref, aux_pref), st) ->
        generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
        signatures_preserved_calls ->
        CloNL.wc_global nodes ->
        Signature_consistent acc1 acc2 ->
        secglobal_scoped acc1 ->
        secglobal_scoped acc2 ->
        secglobal_scope_sec acc2 ->
        secglobal_scope_bounded_above acc1 st ->
        SECNLUSTYPING.generate_all_signatures_scoped_env' acc1 nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env' acc2 (translate nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2 /\ secglobal_scoped G2 /\ secglobal_scope_sec G2.
    Proof.
      intros prefix nodes.
      revert prefix.
      induction nodes as [|n nodes IH];
        intros prefix acc1 acc2 envs aux_names envs_pref aux_pref st G1 G2
               Hprefgen Henvsgen Hcall Hwc Hcons Hacc1scoped Hacc2scoped
               Hacc2sec Hbound Hnl Hstc.
      - simpl in Hnl, Hstc. inversion Hnl; inversion Hstc; subst.
        repeat split; assumption.
      - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        simpl in Hnl, Hstc.
        destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc1 n envs aux_names)
          as [nsig|] eqn:Hnsig; try discriminate.
        destruct (SECSTCTYPING.generate_sys_signature_scoped_env acc2 (translate_node n) envs aux_names)
          as [ssig|] eqn:Hssig; simpl in Hnl, Hstc; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures_scoped_env' (nsig :: acc1) nodes envs aux_names)
          as [G1'|] eqn:Hnl'; simpl in Hnl; try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures_scoped_env' (ssig :: acc2) (translate nodes) envs aux_names)
          as [G2'|] eqn:Hstc'; simpl in Hstc; try discriminate.
        inversion Hnl; subst G1'. clear Hnl.
        inversion Hstc; subst G2'. clear Hstc.
        pose proof Henvsgen as Henvsgen_full.
        unfold generate_node_scoped_env in Henvsgen_full.
        destruct (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nodes) (Env.empty _) nil NAMEGEN.init_state)
          as [[[envs_full aux_full] st_full]|] eqn:Hrun; try discriminate.
        inversion Henvsgen_full; subst envs_full aux_full; clear Henvsgen_full.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
              & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
          eauto.
        rewrite Hprefgen in Hpref. inversion Hpref; subst envs_pref' aux_pref' st_pref.
        assert (Hcur : st_cur = st_local).
        {
          unfold NAMEGEN.fresh_insert_node_env in Hins.
          destruct (Env.mem n.(n_name) envs_pref) eqn:Hmem; try discriminate.
          unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
          inversion Hins. reflexivity.
        }
        subst st_cur.
        assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
        {
          eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
          eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
        }
        assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
        {
          eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
          - pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
            unfold get_node_aux. simpl. rewrite <- Hrecname, ident_eqb_refl. reflexivity.
          - eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
        }
        unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
        rewrite Hfindlocal in Hnsig.
        unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
        assert (Hfindlocal_sys :
                  find_node_env (translate_node n).(SynStc.s_name) envs = Some local_env).
        { simpl. exact Hfindlocal. }
        rewrite Hfindlocal_sys in Hssig.
        assert (Henvinj : SECNLUSTYPING.env_injective local_env).
        { eapply NAMEGEN.generate_local_env_for_node_injective; eauto. }
        assert (Hnsigscoped : signature_scoped nsig).
        {
          eapply SECNLUSTYPING.generate_node_sig_scoped with (P := nodes).
          - exact Hacc1scoped.
          - exact Henvinj.
          - exact Hwc_head.
          - exact Hnsig.
        }
        assert (Hssigscoped : signature_scoped ssig).
        {
          eapply SECSTCTYPING.generate_sys_signature_scoped with (P := translate nodes).
          - exact Hacc2scoped.
          - exact Henvinj.
          - eapply translate_node_wc_local; eauto.
          - exact Hssig.
        }
        assert (Hscopefresh : node_scope_fresh_in_env n local_env aux_names acc1).
        {
          eapply node_scope_fresh_in_env_from_bounds; eauto.
        }
        assert (Hpres : signatures_preserved nsig ssig).
        {
          eapply generated_signatures_preserved_from_simplify_bridge_local_env
            with (P := nodes) (env := local_env) (aux_names := aux_names)
                 (rec := rec) (st := st) (st' := st_local); eauto.
        }
        assert (Hhead : Signature_head_consistent nsig ssig).
        {
          split.
          - eapply generated_signature_name_agree; eauto.
          - destruct Hpres as [Hfields Hprescall].
            split; [exact Hfields|].
            eapply (Hcall nsig ssig); eauto.
            exact (conj Hfields Hprescall).
        }
        assert (Hcons' : Signature_consistent (nsig :: acc1) (ssig :: acc2)).
        { eapply Signature_consistent_cons; eauto. }
        assert (Hacc1scoped' : secglobal_scoped (nsig :: acc1)).
        { eapply secglobal_scoped_cons; eauto. }
        assert (Hacc2scoped' : secglobal_scoped (ssig :: acc2)).
        { eapply secglobal_scoped_cons; eauto. }
        assert (Hacc2sec' : secglobal_scope_sec (ssig :: acc2)).
        {
          eapply secglobal_scope_sec_cons; eauto.
          eapply generated_sys_signature_scope_sec_from_local_env
            with (rec := rec) (st := st) (st' := st_local) (aux_names := aux_names); eauto.
        }
        assert (Hnsigbound : signature_scope_bounded_above nsig st_local).
        {
          intros ty Hin.
          eapply generated_node_sig_scope_upper_bound_from_local_env
            with (rec := rec) (st := st) (st' := st_local) (aux_names := aux_names); eauto.
        }
        assert (Hle : (st <= st_local)%positive).
        { eapply NAMEGEN.generate_local_env_for_node_state_monotone; eauto. }
        assert (Hbound' : secglobal_scope_bounded_above (nsig :: acc1) st_local).
        {
          eapply secglobal_scope_bounded_above_cons; eauto.
          eapply secglobal_scope_bounded_above_monotone; eauto.
        }
        assert (Hstep :
                  NAMEGEN.generate_node_scoped_env' (n :: nil) envs_pref aux_pref st =
                  OK ((envs_cur, rec :: aux_pref), st_local)).
        {
          simpl.
          unfold NMbind2.
          rewrite Hlocal.
          simpl.
          unfold NMbind.
          rewrite Hins.
          simpl.
          reflexivity.
        }
        assert (Hprefgen' :
                  NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nil) (Env.empty _) nil NAMEGEN.init_state =
                  OK ((envs_cur, rec :: aux_pref), st_local)).
        {
          eapply NAMEGEN.generate_node_scoped_env'_app; eauto.
        }
	        assert (Henvsgen' : generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes) = OK (envs, aux_names)).
	        {
	          assert (Heqlist : (prefix ++ n :: nil) ++ nodes = prefix ++ n :: nodes).
	          {
	            clear - prefix n nodes.
	            induction prefix as [|a prefix IHprefix]; simpl.
	            - reflexivity.
	            - now f_equal.
	          }
	          assert (Heqprefix :
	                    generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes) =
	                    generate_node_scoped_env (prefix ++ n :: nodes)).
	          {
	            now rewrite Heqlist.
	          }
	          rewrite Heqprefix.
	          simpl.
	          exact Henvsgen.
	        }
        eapply IH with (prefix := prefix ++ n :: nil)
                        (acc1 := nsig :: acc1) (acc2 := ssig :: acc2)
                        (envs := envs) (aux_names := aux_names)
                        (envs_pref := envs_cur) (aux_pref := rec :: aux_pref)
                        (st := st_local); eauto.
    Qed.

    Corollary generate_all_signatures_consistent_scoped:
      forall all_nodes envs aux_names G1 G2,
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2 /\ secglobal_scoped G2 /\ secglobal_scope_sec G2.
	    Proof.
	      intros all_nodes envs aux_names G1 G2
	             Henvsgen Hcall Hwc Hallnl Hallstc.
	      unfold SECNLUSTYPING.generate_all_signatures_scoped_env in Hallnl.
	      unfold SECSTCTYPING.generate_all_sys_signatures_scoped_env in Hallstc.
	      eapply generate_all_signatures_consistent_scoped'
	        with (prefix := nil) (acc1 := nil) (acc2 := nil)
	             (envs := envs) (aux_names := aux_names)
	             (envs_pref := Env.empty _) (aux_pref := nil)
	             (st := NAMEGEN.init_state) (G1 := G1) (G2 := G2).
	      - reflexivity.
	      - exact Henvsgen.
	      - exact Hcall.
	      - exact Hwc.
	      - apply Signature_consistent_nil.
	      - apply secglobal_scoped_nil.
	      - apply secglobal_scoped_nil.
	      - apply secglobal_scope_sec_nil.
	      - apply secglobal_scope_bounded_above_nil.
	      - exact Hallnl.
	      - exact Hallstc.
	    Qed.

    Corollary generate_all_signatures_consistent:
      forall all_nodes envs aux_names G1 G2,
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        signatures_preserved_calls ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros all_nodes envs aux_names G1 G2
             Henvsgen Hcall Hwc Hallnl Hallstc.
      destruct (generate_all_signatures_consistent_scoped
                  all_nodes envs aux_names G1 G2 Henvsgen Hcall Hwc Hallnl Hallstc)
        as [Hcons _].
      exact Hcons.
    Qed.

	    (** Lookup-based program signature theorem.

	        This is the public signature-level form of the final result.  It does
	        not rerun per-node signature generation.  Instead, it states directly
	        that any source signature found in the generated global source
        signature environment has a matching target signature in the generated
        STC global environment, and that the pair is
        [Signature_head_consistent].  All raw/local constraint details remain
        internal to the bridge lemmas above. *)
	    Corollary generated_program_signatures_preserved_global:
	      forall all_nodes (G1 G2: secglobal)
	             (envs: node_scoped_env) (aux_names: list node_aux_names),
	        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
	        signatures_preserved_calls ->
	        CloNL.wc_global all_nodes ->
	        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
	        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
	        forall f nsig,
	          SECNLUSTYPING.find_signature f G1 = Some nsig ->
	          exists ssig,
	            SECSTCTYPING.find_signature f G2 = Some ssig
	            /\ Signature_head_consistent nsig ssig.
	    Proof.
	      intros all_nodes G1 G2 envs aux_names
	             Henvsgen Hcall Hwc Hallnl Hallstc
	             f nsig Hfindsig.
	      pose proof (generate_all_signatures_consistent
	                    all_nodes envs aux_names G1 G2
	                    Henvsgen Hcall
	                    Hwc Hallnl Hallstc) as Hcons.
	      destruct (Hcons f nsig Hfindsig) as (ssig & Hfindstc & Hhead).
	      exists ssig. split; assumption.
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
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
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
