(** Leg U: unnesting preserves generated constraints.

    This is the pass the refinement types were built for.  [unnest_exp] on a
    nested call mints one variable per result with [idents_for_anns'], returns
    an [Evar] for each, and emits the call as its own equation.
    [assign_lexp_type] on the same expression mints one security name per
    result with [fresh_idents], returns a variable-shaped type for each, and
    *carries* that equation's constraints.

    So the theorem is that the carried constraints are the constraints of the
    equations unnesting emits, and the minted security names are the variables
    unnesting adds.  Nothing in the transcription leg states this, and nothing
    in it can: [to_lexp] rejects [Eapp], so by then there are no nested calls
    left and the carried component is empty everywhere.

    The two allocators cannot produce the same names -- unnesting mints
    [gensym norm1 _] and the security monad [gensym sec _] -- so the two sides
    are related by a bijection rather than by equality.  Both mint one name per
    annotation in the same order, so within a node the bijection is positional,
    and [preserves_on] absorbs it: the witness valuation is free to differ off
    the visible scope, which is exactly where the renamed names live. *)

From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Lia.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.
From Velus Require Import SIF.SecLusUnnestingEquations.

Module SecLusUnnestingNodes
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import Lat     : Lattice)
  (Import SecT    : SECTYPES Lat)
  (Import SLT     : SECLUSTYPES Lat SecT)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX Ids Op)
  (Import LClo    : LCLOCKING Ids Op LSyn)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import UNN     : UNNESTING Ids Op OpAux LSyn)
.

Module EQ := SecLusUnnestingEquations Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include EQ.

Import SECMONADNotations.
Import UNN.Fresh.Tactics.

  Section Preservation.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable vars    : list (ident * clock).
    Variable cenv    : Env.t (type * clock).
    Variable scope   : list ident.
    Variable stF     : sec_state.
    Variable amb     : ST.

    Hypothesis env_inj : env_injective env.
    Hypothesis amb_scoped : st_scoped scope amb.
    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.
    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).
    Hypothesis source_types_scoped :
      source_types_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis source_lexps_scoped :
      source_lexps_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis rst_ty_scoped : In rst_ty scope.
    Hypothesis clk_types_scoped :
      forall ck ckty,
        assign_clk_type env base_ty ck = Some ckty -> st_scoped scope ckty.
    Hypothesis env_range_scoped :
      forall x b, Env.find x env = Some b -> In b scope.
    Hypothesis source_lexps_carried_scoped :
      source_lexps_carried_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis sig_scoped :
      forall f sg, find_signature f GL = Some sg -> signature_scoped sg.
    Hypothesis sig_actuals_fresh :
      forall f sg inp ck rst os cns sa sb,
        find_signature f GL = Some sg ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    Local Notation moved_by := (EQ.moved_by env).

    (** * The equations of a node

        [unnest_equations] is a [map_bind], and the composition is the one
        the expression and right-hand side lists already used: the head's
        witness is extended by the tail's, and each side's obligations
        survive the other's because they move over disjoint stretches of the
        fresh state. *)

    Lemma unnest_equations_inv :
      forall P eqs eqs' st st',
        unnest_equations P eqs st = (eqs', st') ->
        exists eqss,
          map_bind (unnest_equation P) eqs st = (eqss, st')
          /\ eqs' = List.concat eqss.
    Proof.
      intros P eqs eqs' st st' H.
      unfold unnest_equations in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma map_bind_unnest_equation_cons :
      forall P eq eqs eqss st st',
        map_bind (unnest_equation P) (eq :: eqs) st = (eqss, st') ->
        exists eq1 st1 eqsr,
          unnest_equation P eq st = (eq1, st1)
          /\ map_bind (unnest_equation P) eqs st1 = (eqsr, st')
          /\ eqss = eq1 :: eqsr.
    Proof.
      intros P eq eqs eqss st st' H.
      simpl in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma map_bind_unnest_equation_nil :
      forall P eqss st st',
        map_bind (unnest_equation P) [] st = (eqss, st') ->
        eqss = [] /\ st' = st.
    Proof.
      intros P eqss st st' H. simpl in H.
      rewrite ret_spec in H. inv H. auto.
    Qed.

    Lemma eqns_carries :
      forall P eqs eqss st st' ce xst xst' cet yst yst' dlt,
        Forall (wl_equation P) eqs ->
        Forall (wc_equation P vars) eqs ->
        NoDup (vars_defined (List.concat eqss) ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined (List.concat eqss)) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of env (vars_defined eqs)) ->
                   satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        map_bind (unnest_equation P) eqs st = (eqss, st') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.concat eqss) yst = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le xst' stF ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.
    Proof.
      induction eqs as [|eq eqs IH];
        intros eqss st st' ce xst xst' cet yst yst' dlt
        Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat Hbnd.
      - apply map_bind_unnest_equation_nil in Hun as (? & ?); subst.
        simpl in Hgent.
        destruct
          (generate_leqns_constraints_nil GL env base_ty rst_ty cenv
             cet yst yst' Hgent) as (? & ?); subst.
        exists dlt. split.
        + intros x _. reflexivity.
        + split; constructor.
      - inversion Hwl as [|eqa eqsa Hwl1 Hwlr]; subst.
        inversion Hwc as [|eqb eqsb Hwc1 Hwcr]; subst.
        apply map_bind_unnest_equation_cons in Hun
          as (eq1 & st1 & eqsr & Hun1 & Hunr & ?); subst.
        assert (st_follows st st1) as Hf1
            by exact (unnest_equation_st_follows P eq eq1 st st1 Hun1).
        assert (st_follows st1 st') as Hf2
            by (apply (@map_bind_st_follows equation (list equation)
                         (type * clock) (unnest_equation P)
                         eqs eqsr st1 st' Hunr);
                rewrite Forall_forall; intros eq0 _ eqs0 s s' Heq;
                exact (unnest_equation_st_follows P eq0 eqs0 s s' Heq)).
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & xst1 & Hgen1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & xst2 & Hgen2 & Hret).
        unfold SC.ret in Hret. inv Hret.
        simpl List.concat in Hgent, Hnd, Hamb.
        apply generate_leqns_constraints_app in Hgent
          as (ct1 & ct2 & ystm & Hgt1 & Hgt2 & ?); subst.
        rewrite vars_defined_app in Hnd, Hamb.
        apply listSatisfiable_app in Hsat as (Hsat1 & Hsat2).
        apply Forall_app in Hcesc as (Hcesc1 & Hcesc2).
        assert (Permutation (vars_defined eq1 ++ st_ids st)
                  (fst eq ++ st_ids st1)) as Hp1'.
        { assert
            (Permutation (vars_defined eq1 ++ st_ids st)
               (vars_defined [eq] ++ st_ids st1)) as Hunnestperm
              by exact
                (unnest_equation_vars_perm P eq eq1 st st1 Hwl1 Hun1).
          assert
            (Permutation (vars_defined [eq] ++ st_ids st1)
               (fst eq ++ st_ids st1)) as Hsourceperm.
          { rewrite vars_defined_cons_eq. simpl. rewrite app_nil_r.
            reflexivity. }
          exact
            (@Permutation_trans ident _ _ _ Hunnestperm Hsourceperm). }
        rewrite <- app_assoc in Hnd.
        assert (NoDup (vars_defined eq1 ++ st_ids st)) as Hndh
            by exact
              (NoDup_drop_middle (vars_defined eq1)
                 (vars_defined (List.concat eqsr)) (st_ids st) Hnd).
        assert (NoDup (vars_defined (List.concat eqsr) ++ st_ids st1))
          as Hndt.
        { assert
            (NoDup
               (vars_defined (List.concat eqsr) ++ vars_defined eq1 ++
                st_ids st)) as Hndswap
              by exact
                (@Permutation_NoDup ident _ _
                   (Permutation_swap3 (vars_defined eq1)
                      (vars_defined (List.concat eqsr)) (st_ids st)) Hnd).
          assert
            (NoDup
               (vars_defined (List.concat eqsr) ++ fst eq ++ st_ids st1))
            as Hndmapped
              by exact
                (@Permutation_NoDup ident _ _
                   (Permutation_app_head (vars_defined (List.concat eqsr))
                      Hp1') Hndswap).
          exact
            (NoDup_drop_middle (vars_defined (List.concat eqsr))
               (fst eq) (st_ids st1) Hndmapped). }

        (** the first equation's run ends before the rest's, so the
            checkmark bound reaches it too *)
        assert (sec_le xst1 stF) as Hbh.
        { eapply sec_le_trans; [|exact Hbnd].
          eapply generate_leqns_constraints_sec_le; exact Hgen2. }

        edestruct
          (eqn_carries_all GL env base_ty rst_ty vars cenv scope stF amb
             env_inj amb_scoped sig_good sig_nodup source_types_scoped
             source_lexps_scoped rst_ty_scoped clk_types_scoped
             env_range_scoped source_lexps_carried_scoped sig_scoped
             sig_actuals_fresh P eq eq1 st st1 c1 xst xst1
             ct1 yst ystm dlt)
          as (dlt1 & Hoff1 & Hce1 & Hscope1).
        { exact Hwl1. }
        { exact Hwc1. }
        { exact Hndh. }
        { intros y Hy.
          exact (Hmv y (eq_moved_by_prefix env st st1 st' Hf2 y Hy)). }
        { intros y cky ckty Hy. apply Hamb. apply in_or_app. now left. }
        { intros b Hb. apply Hbs0.
          unfold sec_of in *. apply in_flat_map in Hb as (x & Hx & Hb).
          apply in_flat_map. exists x. split; [|exact Hb].
          rewrite vars_defined_cons_eq. apply in_or_app. now left. }
        { exact Hcesc1. }
        { exact Hun1. }
        { exact Hgen1. }
        { exact Hgt1. }
        { exact Hsat1. }
        { exact Hbh. }

        edestruct (IH eqsr st1 st' c2 xst1 xst' ct2 ystm yst' dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2).
        { exact Hwlr. }
        { exact Hwcr. }
        { exact Hndt. }
        { intros y Hy.
          exact (Hmv y (eq_moved_by_suffix env st st1 st' Hf1 y Hy)). }
        { intros y cky ckty Hy. apply Hamb. apply in_or_app. now right. }
        { intros b Hb.
          assert (In b (sec_of env (vars_defined (eq :: eqs)))) as Hb0.
          { unfold sec_of in *. apply in_flat_map in Hb as (x & Hx & Hbx).
            apply in_flat_map. exists x. split; [|exact Hbx].
            rewrite vars_defined_cons_eq. apply in_or_app. now right. }
          assert (forall y, In y amb -> ~ In y (moved_by st st1)) as Hamboff.
          { intros y Hy Hin.
            exact
              (Hmv y (eq_moved_by_prefix env st st1 st' Hf2 y Hin)
                 (amb_scoped y Hy)). }
          assert (forall y, In y [b] -> ~ In y (moved_by st st1)) as Hboff.
          { intros y Hy Hin. destruct Hy as [Hy|[]]. subst y.
            exact
              (Hmv b (eq_moved_by_prefix env st st1 st' Hf2 b Hin)
                 (sec_of_scoped env scope env_range_scoped
                    (vars_defined (eq :: eqs)) b Hb0)). }
          exact
            (satisfiable_off amb [b] (moved_by st st1) dlt dlt1
               Hoff1 Hamboff Hboff (Hbs0 b Hb0)). }
        { exact Hcesc2. }
        { exact Hunr. }
        { exact Hgen2. }
        { exact Hgt2. }
        { assert (forall y, In y (moved_by st st1) -> ~ In y scope)
            as Hprefixfresh.
          { intros y Hy.
            exact (Hmv y (eq_moved_by_prefix env st st1 st' Hf2 y Hy)). }
          exact
            (listSatisfiable_off scope c2 (moved_by st st1) dlt dlt1
               Hcesc2 Hprefixfresh Hoff1 Hsat2). }
        { exact Hbnd. }

        assert (forall y, In y (moved_by st1 st') ->
                          ~ In y (scope ++ moved_by st st1)) as Hsep.
        { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
          - apply (Hmv y); [|exact Hy].
            apply (eq_moved_by_suffix env st st1 st' Hf1). exact Hin.
          - exact (eq_moved_by_disjoint env env_inj st st1 st' y Hy Hin). }
        assert (incl (scope ++ moved_by st st1)
                     (scope ++ moved_by st st')) as Hinc1.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_prefix env st st1 st' Hf2). }
        assert (incl (scope ++ moved_by st1 st')
                     (scope ++ moved_by st st')) as Hinc2.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_suffix env st st1 st' Hf1). }

        exists dlt2. split; [|split].
        + exact
            (agree_off_trans (moved_by st st') dlt dlt1 dlt2
               (agree_off_incl (moved_by st st1) (moved_by st st') dlt dlt1
                  (eq_moved_by_prefix env st st1 st' Hf2) Hoff1)
               (agree_off_incl (moved_by st1 st') (moved_by st st') dlt1 dlt2
                  (eq_moved_by_suffix env st st1 st' Hf1) Hoff2)).
        + apply listSatisfiable_app. split; [|exact Hce2].
          exact
            (listSatisfiable_off_scope ct1 (scope ++ moved_by st st1)
               (moved_by st1 st') dlt1 dlt2 Hscope1 Hsep Hoff2 Hce1).
        + apply Forall_app. split.
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st st1))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st st1) (scope ++ moved_by st st')
                        c Hinc1 Hc) ct1 Hscope1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st1 st'))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st1 st') (scope ++ moved_by st st')
                        c Hinc2 Hc) ct2 Hscope2).
    Qed.

  End Preservation.

  (** * Equation lists at their own ambients

      [eqns_carries] runs at one fixed ambient, because the section fixes
      one.  A node cannot: the ambient of an equation is the ambient of
      *its* clock, and a node-wide ambient would have to lie below every
      variable in the node, which is false as soon as two equations are on
      unrelated clocks.

      So the composition is redone here, outside the section, where the
      section's lemmas are universally quantified over the ambient and each
      equation can be given its own. *)

  Section NodeEquations.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable vars    : list (ident * clock).
    Variable cenv    : Env.t (type * clock).
    Variable scope   : list ident.
    Variable stF     : sec_state.

    Hypothesis env_inj : env_injective env.
    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.
    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).
    Hypothesis source_types_scoped :
      source_types_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis source_lexps_scoped :
      source_lexps_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis rst_ty_scoped : In rst_ty scope.
    Hypothesis clk_types_scoped :
      forall ck ckty,
        assign_clk_type env base_ty ck = Some ckty -> st_scoped scope ckty.
    Hypothesis env_range_scoped :
      forall x b, Env.find x env = Some b -> In b scope.
    Hypothesis source_lexps_carried_scoped :
      source_lexps_carried_scoped_upto GL env base_ty rst_ty scope stF.
    Hypothesis sig_scoped :
      forall f sg, find_signature f GL = Some sg -> signature_scoped sg.
    Hypothesis sig_actuals_fresh :
      forall f sg inp ck rst os cns sa sb,
        find_signature f GL = Some sg ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    (** The ambient of an equation, as a function of the equation.  Its two
        properties are the ones a single ambient had: it names only program
        variables, and it covers the ambient of every variable the
        equation's unnesting defines. *)

    Variable A : equation -> ST.
    Hypothesis A_scoped : forall eq, st_scoped scope (A eq).

    Lemma eqns_carries_amb :
      forall P eqs eqss st st' ce xst xst' cet yst yst' dlt,
        Forall (wl_equation P) eqs ->
        Forall (wc_equation P vars) eqs ->
        NoDup (vars_defined (List.concat eqss) ++ st_ids st) ->
        (forall x, In x (moved_by env st st') -> ~ In x scope) ->
        (forall eq eqs1 s s',
            In eq eqs -> unnest_equation P eq s = (eqs1, s') ->
            forall x ck ckty,
              In x (vars_defined eqs1) -> find_clock cenv x = OK ck ->
              assign_clk_type env base_ty ck = Some ckty ->
              incl (merge [rst_ty] ckty) (A eq)) ->
        (forall eq b, In eq eqs -> In b (sec_of env (fst eq)) ->
                      satisfiable dlt (A eq) [b]) ->
        constraints_scoped scope ce ->
        map_bind (unnest_equation P) eqs st = (eqss, st') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.concat eqss) yst = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le xst' stF ->
        exists dlt',
          agree_off (moved_by env st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by env st st') cet.
    Proof.
      induction eqs as [|eq eqs IH];
        intros eqss st st' ce xst xst' cet yst yst' dlt
          Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat Hbnd.
      - apply map_bind_unnest_equation_nil in Hun as (Hq1 & Hq2); subst.
        simpl List.concat in Hgent.
        apply generate_leqns_constraints_nil in Hgent as (Hq3 & Hq4); subst.
        exists dlt. split; [apply agree_off_refl|].
        split; constructor.
      - inversion Hwl as [|eqa eqsa Hwl1 Hwlr]; subst.
        inversion Hwc as [|eqb eqsb Hwc1 Hwcr]; subst.
        apply map_bind_unnest_equation_cons in Hun
          as (eq1 & st1 & eqsr & Hun1 & Hunr & ?); subst.
        assert (st_follows st st1) as Hf1
            by exact (unnest_equation_st_follows P eq eq1 st st1 Hun1).
        assert (st_follows st1 st') as Hf2
            by (apply (@map_bind_st_follows equation (list equation)
                         (type * clock) (unnest_equation P)
                         eqs eqsr st1 st' Hunr);
                rewrite Forall_forall; intros eq0 _ eqs0 s s' Heq;
                exact (unnest_equation_st_follows P eq0 eqs0 s s' Heq)).
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & xst1 & Hgen1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & xst2 & Hgen2 & Hret).
        unfold SC.ret in Hret. inv Hret.
        simpl List.concat in Hgent, Hnd.
        apply generate_leqns_constraints_app in Hgent
          as (ct1 & ct2 & ystm & Hgt1 & Hgt2 & ?); subst.
        rewrite vars_defined_app in Hnd.
        apply listSatisfiable_app in Hsat as (Hsat1 & Hsat2).
        apply Forall_app in Hcesc as (Hcesc1 & Hcesc2).
        assert (Permutation (vars_defined eq1 ++ st_ids st)
                  (fst eq ++ st_ids st1)) as Hp1'.
        { assert
            (Permutation (vars_defined eq1 ++ st_ids st)
               (vars_defined [eq] ++ st_ids st1)) as Hunnestperm
              by exact
                (unnest_equation_vars_perm P eq eq1 st st1 Hwl1 Hun1).
          assert
            (Permutation (vars_defined [eq] ++ st_ids st1)
               (fst eq ++ st_ids st1)) as Hsourceperm.
          { rewrite vars_defined_cons_eq. simpl. rewrite app_nil_r.
            reflexivity. }
          exact
            (@Permutation_trans ident _ _ _ Hunnestperm Hsourceperm). }
        rewrite <- app_assoc in Hnd.
        assert (NoDup (vars_defined eq1 ++ st_ids st)) as Hndh
            by exact
              (NoDup_drop_middle (vars_defined eq1)
                 (vars_defined (List.concat eqsr)) (st_ids st) Hnd).
        assert (NoDup (vars_defined (List.concat eqsr) ++ st_ids st1))
          as Hndt.
        { assert
            (NoDup
               (vars_defined (List.concat eqsr) ++ vars_defined eq1 ++
                st_ids st)) as Hndswap
              by exact
                (@Permutation_NoDup ident _ _
                   (Permutation_swap3 (vars_defined eq1)
                      (vars_defined (List.concat eqsr)) (st_ids st)) Hnd).
          assert
            (NoDup
               (vars_defined (List.concat eqsr) ++ fst eq ++ st_ids st1))
            as Hndmapped
              by exact
                (@Permutation_NoDup ident _ _
                   (Permutation_app_head (vars_defined (List.concat eqsr))
                      Hp1') Hndswap).
          exact
            (NoDup_drop_middle (vars_defined (List.concat eqsr))
               (fst eq) (st_ids st1) Hndmapped). }

        (** the first equation's run ends before the rest's, so the
            checkmark bound reaches it too *)
        assert (sec_le xst1 stF) as Hbh.
        { eapply sec_le_trans; [|exact Hbnd].
          eapply generate_leqns_constraints_sec_le; exact Hgen2. }

        edestruct
          (eqn_carries_all GL env base_ty rst_ty vars cenv scope stF (A eq)
             env_inj (A_scoped eq) sig_good sig_nodup source_types_scoped
             source_lexps_scoped rst_ty_scoped clk_types_scoped
             env_range_scoped source_lexps_carried_scoped sig_scoped
             sig_actuals_fresh P eq eq1 st st1 c1 xst xst1
             ct1 yst ystm dlt)
          as (dlt1 & Hoff1 & Hce1 & Hscope1).
        { exact Hwl1. }
        { exact Hwc1. }
        { exact Hndh. }
        { intros y Hy.
          exact (Hmv y (moved_by_prefix env st st1 st' Hf2 y Hy)). }
        { intros x ck ckty Hx.
          exact
            (Hamb eq eq1 st st1 (or_introl Logic.eq_refl) Hun1
               x ck ckty Hx). }
        { intros b Hb. exact (Hbs0 eq b (or_introl Logic.eq_refl) Hb). }
        { exact Hcesc1. }
        { exact Hun1. }
        { exact Hgen1. }
        { exact Hgt1. }
        { exact Hsat1. }
        { exact Hbh. }

        edestruct (IH eqsr st1 st' c2 xst1 xst' ct2 ystm yst' dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2).
        { exact Hwlr. }
        { exact Hwcr. }
        { exact Hndt. }
        { intros y Hy.
          exact (Hmv y (moved_by_suffix env st st1 st' Hf1 y Hy)). }
        { intros eq' eqs1 s s' Hin.
          exact (Hamb eq' eqs1 s s' (or_intror Hin)). }
        { intros eq' b Hin Hb.
          assert (In b (sec_of env (fst eq'))) as Hb0 by exact Hb.
          assert (In b scope) as Hbsc.
          { unfold sec_of in Hb. apply in_flat_map in Hb as (x & _ & Hbx).
            destruct (Env.find x env) as [b0|] eqn:Hf; [|contradiction].
            destruct Hbx as [Hbx|[]]; subst b0.
            exact (env_range_scoped x b Hf). }
          assert (forall y, In y (A eq') -> ~ In y (moved_by env st st1))
            as Hamboff.
          { intros y Hy Hin'.
            exact
              (Hmv y (moved_by_prefix env st st1 st' Hf2 y Hin')
                 (A_scoped eq' y Hy)). }
          assert (forall y, In y [b] -> ~ In y (moved_by env st st1))
            as Hboff.
          { intros y Hy Hin'. destruct Hy as [Hy|[]]. subst y.
            exact
              (Hmv b (moved_by_prefix env st st1 st' Hf2 b Hin') Hbsc). }
          exact
            (satisfiable_off (A eq') [b] (moved_by env st st1) dlt dlt1
               Hoff1 Hamboff Hboff (Hbs0 eq' b (or_intror Hin) Hb0)). }
        { exact Hcesc2. }
        { exact Hunr. }
        { exact Hgen2. }
        { exact Hgt2. }
        { assert (forall y, In y (moved_by env st st1) -> ~ In y scope)
            as Hprefixfresh.
          { intros y Hy.
            exact (Hmv y (moved_by_prefix env st st1 st' Hf2 y Hy)). }
          exact
            (listSatisfiable_off scope c2 (moved_by env st st1) dlt dlt1
               Hcesc2 Hprefixfresh Hoff1 Hsat2). }
        { exact Hbnd. }

        assert (forall y, In y (moved_by env st1 st') ->
                          ~ In y (scope ++ moved_by env st st1)) as Hsep.
        { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
          - apply (Hmv y); [|exact Hy].
            apply (moved_by_suffix env st st1 st' Hf1). exact Hin.
          - exact (moved_by_disjoint env env_inj st st1 st' y Hy Hin). }
        assert (incl (scope ++ moved_by env st st1)
                     (scope ++ moved_by env st st')) as Hinc1.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (moved_by_prefix env st st1 st' Hf2). }
        assert (incl (scope ++ moved_by env st1 st')
                     (scope ++ moved_by env st st')) as Hinc2.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (moved_by_suffix env st st1 st' Hf1). }

        exists dlt2. split; [|split].
        + exact
            (agree_off_trans (moved_by env st st') dlt dlt1 dlt2
               (agree_off_incl (moved_by env st st1) (moved_by env st st')
                  dlt dlt1 (moved_by_prefix env st st1 st' Hf2) Hoff1)
               (agree_off_incl (moved_by env st1 st') (moved_by env st st')
                  dlt1 dlt2 (moved_by_suffix env st st1 st' Hf1) Hoff2)).
        + apply listSatisfiable_app. split; [|exact Hce2].
          exact
            (listSatisfiable_off_scope ct1 (scope ++ moved_by env st st1)
               (moved_by env st1 st') dlt1 dlt2
               Hscope1 Hsep Hoff2 Hce1).
        + apply Forall_app. split.
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by env st st1))
                     (constraint_scoped (scope ++ moved_by env st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by env st st1)
                        (scope ++ moved_by env st st') c Hinc1 Hc)
                     ct1 Hscope1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by env st1 st'))
                     (constraint_scoped (scope ++ moved_by env st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by env st1 st')
                        (scope ++ moved_by env st st') c Hinc2 Hc)
                     ct2 Hscope2).
    Qed.


    (** * The node level

        A node's equations are unnested from the empty fresh state, so the
        [NoDup] premise collapses to the node's own well-formedness -- the
        unnested equations define each variable once -- and everything else
        is [eqns_carries_amb] at [init_st].

        What is left for the caller is the interface to the two passes this
        file does not perform: the naming pass, which fixes [env] and hence
        [scope] and the separation between a node's own names and the ones a
        run moves; and the ambient, which is a fact about the clocks the
        unnesting emits. *)

    Theorem node_carries :
      forall P (eqs : list equation) eqs' st' ce xst xst' cet yst yst' dlt,
        Forall (wl_equation P) eqs ->
        Forall (wc_equation P vars) eqs ->
        NoDup (vars_defined eqs') ->
        (forall x, In x (moved_by env init_st st') -> ~ In x scope) ->
        (forall eq eqs1 s s',
            In eq eqs -> unnest_equation P eq s = (eqs1, s') ->
            forall x ck ckty,
              In x (vars_defined eqs1) -> find_clock cenv x = OK ck ->
              assign_clk_type env base_ty ck = Some ckty ->
              incl (merge [rst_ty] ckty) (A eq)) ->
        (forall eq b, In eq eqs -> In b (sec_of env (fst eq)) ->
                      satisfiable dlt (A eq) [b]) ->
        constraints_scoped scope ce ->
        unnest_equations P eqs init_st = (eqs', st') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le xst' stF ->
        exists dlt',
          agree_off (moved_by env init_st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by env init_st st') cet.
    Proof.
      intros P eqs eqs' st' ce xst xst' cet yst yst' dlt
        Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat Hbnd.
      apply unnest_equations_inv in Hun as (eqss & Hmap & ?); subst.
      assert (NoDup
                (vars_defined (List.concat eqss) ++
                 st_ids (init_st : fresh_st (type * clock))))
        as Hnd0.
      { unfold st_ids. rewrite init_st_anns. simpl. rewrite app_nil_r.
        exact Hnd. }
      exact
        (eqns_carries_amb P eqs eqss (init_st : fresh_st (type * clock))
           st' ce xst xst' cet yst yst'
           dlt Hwl Hwc Hnd0 Hmv Hamb Hbs0 Hcesc Hmap Hgen Hgent Hsat Hbnd).
    Qed.

    (** The valuation produced by [node_carries] changes only the security
        names paired with variables introduced by unnesting.  Freshness of
        those names therefore turns the stronger [agree_off] conclusion into
        the visible-interface agreement required by [preserves_on]. *)
    Theorem node_carries_preserves :
      forall P (eqs : list equation) eqs' st' ce xst xst' cet yst yst',
        Forall (wl_equation P) eqs ->
        Forall (wc_equation P vars) eqs ->
        NoDup (vars_defined eqs') ->
        (forall x, In x (moved_by env init_st st') -> ~ In x scope) ->
        (forall eq eqs1 s s',
            In eq eqs -> unnest_equation P eq s = (eqs1, s') ->
            forall x ck ckty,
              In x (vars_defined eqs1) -> find_clock cenv x = OK ck ->
              assign_clk_type env base_ty ck = Some ckty ->
              incl (merge [rst_ty] ckty) (A eq)) ->
        (forall dlt,
            listSatisfiable dlt ce ->
            forall eq b,
              In eq eqs -> In b (sec_of env (fst eq)) ->
              satisfiable dlt (A eq) [b]) ->
        constraints_scoped scope ce ->
        unnest_equations P eqs init_st = (eqs', st') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        (** The checkmark bound: this run of the source generator, and
            every sub-run of it, finishes before [stF]. *)
        sec_le xst' stF ->
        preserves_on scope ce cet.
    Proof.
      intros P eqs eqs' st' ce xst xst' cet yst yst'
        Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hbnd dlt Hsat.
      destruct
        (node_carries P eqs eqs' st' ce xst xst' cet yst yst' dlt
           Hwl Hwc Hnd Hmv Hamb (Hbs0 dlt Hsat) Hcesc Hun Hgen Hgent Hsat
           Hbnd)
        as (dlt' & Hoff & Hsat' & Hscoped).
      exists dlt'. split.
      - exact
          (agree_off_agree_on scope (moved_by env init_st st') dlt dlt'
             Hmv Hoff).
      - exact Hsat'.
    Qed.

    (** [unnest_node] hides the equation run in a dependent pair.  This
        projection lemma exposes the concrete result used in its equation and
        local-variable fields, so subsequent preservation statements do not
        have to unfold the program definition. *)
    Lemma unnest_node_fields :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs),
        (unnest_node P n Hwl Hpref).(n_eqs)
          = fst (unnest_equations P n.(n_eqs) init_st)
        /\ (unnest_node P n Hwl Hpref).(n_vars)
             = n.(n_vars) ++
                 st_anns (snd (unnest_equations P n.(n_eqs) init_st)).
    Proof.
      intros P n Hwl Hpref.
      unfold unnest_node, unnest_equations'.
      split; reflexivity.
    Qed.

    Corollary unnest_node_equations_nodup :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st',
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        NoDup (vars_defined eqs').
    Proof.
      intros P n Hwl Hpref eqs' st' Hrun.
      destruct (unnest_node_fields P n Hwl Hpref) as (Heqs & Hvars).
      rewrite Hrun in Heqs. simpl in Heqs.
      rewrite <- Heqs.
      exact (NoDup_vars_defined_n_eqs (unnest_node P n Hwl Hpref)).
    Qed.

    Lemma new_ids_from_init :
      forall st, new_ids init_st st = st_ids st.
    Proof.
      intros st. unfold new_ids.
      assert (st_ids (init_st : fresh_st (type * clock)) = []) as Hinit.
      { unfold st_ids. rewrite init_st_anns. reflexivity. }
      rewrite Hinit.
      induction (st_ids st) as [|x xs IH].
      - reflexivity.
      - change
          (x :: filter
                  (fun y => if in_dec ident_eq_dec y [] then false else true)
                  xs = x :: xs).
        f_equal. exact IH.
    Qed.

    (** The fresh-state identifiers appended to the target node are disjoint
        from every identifier declared by the source node.  This is obtained
        from the target node's own [n_nodup] invariant, rather than assumed
        separately by the security proof. *)
    Lemma unnest_node_new_ids_fresh :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st' x,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        In x (new_ids init_st st') ->
        ~ InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)).
    Proof.
      intros P n Hwl Hpref eqs' st' x Hrun Hnew Hold.
      destruct (unnest_node_fields P n Hwl Hpref) as (Heqs & Hvars).
      rewrite Hrun in Hvars. simpl in Hvars.
      assert (InMembers x (st_anns st')) as Hnewmem.
      { rewrite new_ids_from_init in Hnew.
        unfold st_ids in Hnew.
        apply in_map_iff in Hnew as (xa & Hxa & Hin).
        destruct xa as [y a]. simpl in Hxa. subst y.
        exact (In_InMembers x a (st_anns st') Hin). }
      exact
        (unnested_locals_fresh n (unnest_node P n Hwl Hpref) (st_anns st')
           Logic.eq_refl Logic.eq_refl Hvars x Hold Hnewmem).
    Qed.

    (** Injectivity transports the preceding program-name disjointness to
        security names.  This is the non-auxiliary part of the moved-name
        freshness premise of [node_carries]. *)
    Lemma unnest_node_moved_fresh_from_vars :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st',
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        forall b,
          In b (moved_by env init_st st') ->
          ~ In b
              (sec_of env
                 (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    Proof.
      intros P n Hwl Hpref eqs' st' Hrun b Hmoved Hold.
      unfold moved_by, sec_of in Hmoved, Hold.
      apply in_flat_map in Hmoved as (x & Hxnew & Hxb).
      apply in_flat_map in Hold as (y & Hyold & Hyb).
      destruct (Env.find x env) as [bx|] eqn:Hfx; [|contradiction].
      destruct Hxb as [Hxb|[]]. subst bx.
      destruct (Env.find y env) as [by0|] eqn:Hfy; [|contradiction].
      destruct Hyb as [Hyb|[]]. subst by0.
      assert (x = y) as Hxy
          by exact (env_inj x y b b Hfx Hfy Logic.eq_refl).
      subst y.
      apply
        (unnest_node_new_ids_fresh P n Hwl Hpref eqs' st' x Hrun Hxnew).
      apply in_map_iff in Hyold as (xa & Hxa & Hin).
      destruct xa as [z a]. simpl in Hxa. subst z.
      exact (In_InMembers x a _ Hin).
    Qed.

    Lemma unnest_node_new_id_not_sec_gensym :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st' x,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        In x (new_ids init_st st') ->
        forall i, x <> Ids.gensym Ids.sec i.
    Proof.
      intros P n Hwl Hpref eqs' st' x Hrun Hnew i Heq.
      destruct (unnest_node_fields P n Hwl Hpref) as (Heqs & Hvars).
      rewrite Hrun in Hvars. simpl in Hvars.
      assert
        (In x
           (List.map fst
              ((unnest_node P n Hwl Hpref).(n_in)
                 ++ (unnest_node P n Hwl Hpref).(n_vars)
                 ++ (unnest_node P n Hwl Hpref).(n_out)))) as Hindecls.
      { simpl. rewrite Hvars, map_app, map_app.
        apply in_or_app. right. apply in_or_app. left.
        rewrite map_app. apply in_or_app. right.
        rewrite new_ids_from_init in Hnew.
        exact Hnew. }
      destruct (n_good (unnest_node P n Hwl Hpref)) as (Hgood & Hname).
      rewrite Forall_forall in Hgood.
      specialize (Hgood x).
      assert
        (In x
           (List.map fst
              ((unnest_node P n Hwl Hpref).(n_in)
                 ++ (unnest_node P n Hwl Hpref).(n_vars)
                 ++ (unnest_node P n Hwl Hpref).(n_out)
                 ++ anon_in_eqs
                      (unnest_node P n Hwl Hpref).(n_eqs)))) as Hinall.
      { apply in_map_iff in Hindecls as (xa & Hxa & Hindecls).
        apply in_map_iff. exists xa. split; [exact Hxa|].
        apply in_app_or in Hindecls as [Hin|Hindecls].
        - apply in_or_app. now left.
        - apply in_app_or in Hindecls as [Hin|Hin].
          + apply in_or_app. right. apply in_or_app. now left.
          + apply in_or_app. right. apply in_or_app. right.
            apply in_or_app. now left. }
      specialize (Hgood Hinall).
      rewrite Heq in Hgood.
      assert
        (PS.In Ids.sec
           (n_prefixes (unnest_node P n Hwl Hpref))) as Hsecpref.
      { destruct Hgood as [Hat|Hex].
        - exfalso. exact (gensym_not_atom Ids.sec i Hat).
        - unfold PS.Exists in Hex.
          destruct Hex as (pref & Hinpref & k & Hgen).
          apply gensym_injective in Hgen as (Hprefs & Hindices).
          subst pref. exact Hinpref. }
      simpl in Hsecpref. rewrite Hpref in Hsecpref.
      apply Ids.sec_not_in_gensym_prefs.
      unfold gensym_prefs.
      unfold elab_prefs in Hsecpref.
      rewrite PSF.add_iff, PSF.singleton_iff in Hsecpref.
      destruct Hsecpref as [Hsec|Hsec]; subst; simpl; auto.
    Qed.

    Corollary unnest_node_moved_fresh_from_scope :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st'
             clk_id rst_id,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        Env.find clk_id env = Some base_ty ->
        Env.find rst_id env = Some rst_ty ->
        (forall x, In x (new_ids init_st st') -> x <> clk_id) ->
        (forall x, In x (new_ids init_st st') -> x <> rst_id) ->
        forall b,
          In b (moved_by env init_st st') ->
          ~ In b
              (sec_of env
                 (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
               ++ [base_ty; rst_ty]).
    Proof.
      intros P n Hwl Hpref eqs' st' clk_id rst_id
        Hrun Hclk Hrst Hclkfresh Hrstfresh b Hmoved Hscope.
      apply in_app_or in Hscope as [Hvars|Haux].
      - exact
          (unnest_node_moved_fresh_from_vars P n Hwl Hpref eqs' st'
             Hrun b Hmoved Hvars).
      - unfold moved_by, sec_of in Hmoved.
        apply in_flat_map in Hmoved as (x & Hxnew & Hxb).
        destruct (Env.find x env) as [bx|] eqn:Hfx; [|contradiction].
        destruct Hxb as [Hxb|[]]. subst bx.
        destruct Haux as [Hbase|[Hreset|[]]].
        + subst b. apply (Hclkfresh x Hxnew).
          exact (env_inj x clk_id base_ty base_ty Hfx Hclk Logic.eq_refl).
        + subst b. apply (Hrstfresh x Hxnew).
          exact (env_inj x rst_id rst_ty rst_ty Hfx Hrst Logic.eq_refl).
    Qed.

    Corollary unnest_node_moved_fresh_generated_aux :
      forall P (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st'
             clk_id rst_id i j,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        Env.find clk_id env = Some base_ty ->
        Env.find rst_id env = Some rst_ty ->
        clk_id = Ids.gensym Ids.sec i ->
        rst_id = Ids.gensym Ids.sec j ->
        forall b,
          In b (moved_by env init_st st') ->
          ~ In b
              (sec_of env
                 (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
               ++ [base_ty; rst_ty]).
    Proof.
      intros P n Hwl Hpref eqs' st' clk_id rst_id i j
        Hrun Hclk Hrst Hclkid Hrstid.
      exact
        (unnest_node_moved_fresh_from_scope P n Hwl Hpref eqs' st'
           clk_id rst_id Hrun Hclk Hrst
           (fun x Hx =>
              eq_ind_r (fun id => x <> id)
                (unnest_node_new_id_not_sec_gensym
                   P n Hwl Hpref eqs' st' x Hrun Hx i) Hclkid)
           (fun x Hx =>
              eq_ind_r (fun id => x <> id)
                (unnest_node_new_id_not_sec_gensym
                   P n Hwl Hpref eqs' st' x Hrun Hx j) Hrstid)).
    Qed.

    (** * The interface a node publishes does not move

        [unnest_node] copies [n_name], [n_in] and [n_out] and only *extends*
        [n_vars].  So of the six fields a signature has, five are computed from
        data the pass leaves alone, and are equal on the nose -- not merely
        related.  Only [s_constraints] can differ, which is exactly what
        [preserves_on] speaks about.  Proving it is what makes the signature
        comparison meaningful at all.

        The projection lemma is reproved here rather than reused: the Leg A copy
        (`l_node_sig_inv`) sits later in the build order. *)

    Lemma lnode_sig_inv :
      forall (G : secglobal) (n : node) (aux : list node_aux_names) sg st st',
        generate_lnode_sig G n env aux st = OK (sg, st') ->
        exists clk_id rst_id clk_type rst_type inp out locals cns,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id)
          /\ Env.find clk_id env = Some clk_type
          /\ Env.find rst_id env = Some rst_type
          /\ get_mappings_from_node n.(n_in) env = Some inp
          /\ get_mappings_from_node n.(n_out) env = Some out
          /\ get_mappings_from_node n.(n_vars) env = Some locals
          /\ generate_leqns_constraints G env clk_type rst_type
               (lnode_clock_env n) n.(n_eqs) st = OK (cns, st')
          /\ sg = {| s_name  := n.(n_name);
                     s_in    := inp;
                     s_out   := out;
                     s_reset := rst_type;
                     s_clk   := clk_type;
                     s_constraints := simplify cns (locals ++ minted st st') |}.
    Proof.
      intros G n aux sg st st' H.
      unfold generate_lnode_sig in H.
      match type of H with
      | match ?X with _ => _ end = _ => destruct X as [[q stz]|er] eqn:E
      end; [|discriminate H].
      eapply sec_bind2_inv in E as (clk_id & rst_id & s1 & Haux & E).
      eapply sec_bind_inv in E as (clk_type & s2 & Hclk & E).
      eapply sec_bind_inv in E as (rst_type & s3 & Hrst & E).
      eapply sec_bind_inv in E as (inp & s4 & Hinp & E).
      eapply sec_bind_inv in E as (out & s5 & Hout & E).
      eapply sec_bind_inv in E as (locals & s6 & Hloc & E).
      eapply sec_bind_inv in E as (cns & s7 & Hcns & Eret).
      apply option_to_sec_inv in Hclk as (Hclk & ?); subst s2.
      apply option_to_sec_inv in Hrst as (Hrst & ?); subst s3.
      apply option_to_sec_inv in Hinp as (Hinp & ?); subst s4.
      apply option_to_sec_inv in Hout as (Hout & ?); subst s5.
      apply option_to_sec_inv in Hloc as (Hloc & ?); subst s6.
      apply option_to_sec_inv in Haux as (Haux & ?); subst s1.
      unfold SC.ret in Eret.
      assert (q = (inp, out, rst_type, clk_type, locals, cns) /\ stz = s7)
        as (? & ?) by (inversion Eret; auto); subst q stz.
      assert (sg = {| s_name := n.(n_name); s_in := inp; s_out := out;
                      s_reset := rst_type; s_clk := clk_type;
                      s_constraints :=
                        simplify cns (locals ++ minted st s7) |}
              /\ st' = s7) as (? & ?)
          by (inversion H; auto); subst sg; subst st'.
      exists clk_id, rst_id, clk_type, rst_type, inp, out, locals, cns.
      repeat split; try assumption; reflexivity.
    Qed.

    Corollary unnest_node_sig_interface :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs)
             (G : secglobal) (aux : list node_aux_names)
             st0 sg st1 sg' st1',
        generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
        generate_lnode_sig G (unnest_node P n Hwl Hpref) env aux st0
          = OK (sg', st1') ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg.
    Proof.
      intros P n Hwl Hpref G aux st0 sg st1 sg' st1' H H'.
      apply lnode_sig_inv in H
        as (c1 & r1 & ct1 & rt1 & i1 & o1 & l1 & cs1
            & Ha1 & Hc1 & Hr1 & Hi1 & Ho1 & _ & _ & ?); subst sg.
      apply lnode_sig_inv in H'
        as (c2 & r2 & ct2 & rt2 & i2 & o2 & l2 & cs2
            & Ha2 & Hc2 & Hr2 & Hi2 & Ho2 & _ & _ & ?); subst sg'.
      (** the pass copies the three fields the interface is read from *)
      cbn [n_name n_in n_out unnest_node] in Ha2, Hi2, Ho2.
      rewrite Ha1 in Ha2. inversion Ha2; subst c2 r2.
      rewrite Hc1 in Hc2. inversion Hc2; subst ct2.
      rewrite Hr1 in Hr2. inversion Hr2; subst rt2.
      rewrite Hi1 in Hi2. inversion Hi2; subst i2.
      rewrite Ho1 in Ho2. inversion Ho2; subst o2.
      cbn [s_name s_in s_out s_clk s_reset].
      repeat split; reflexivity.
    Qed.

    (** * Extending a node's variables does not move its clock environment

        [lnode_clock_env] is [Env.adds'] over [n_vars] on top of the inputs and
        outputs, and [Env.adds'] is a left fold of [add], so extending [n_vars]
        on the right only adds keys.  On a key the extension does not mention,
        the two environments therefore agree -- which is what lets the source
        equations be run against the unnested node's clock environment, and so
        lets the equation-level theorem be applied with one [cenv]. *)
    Lemma lnode_clock_env_vars_ext :
      forall (n m : node) (extra : list (ident * (type * clock))) x,
        m.(n_in) = n.(n_in) ->
        m.(n_out) = n.(n_out) ->
        m.(n_vars) = n.(n_vars) ++ extra ->
        ~ InMembers x extra ->
        Env.find x (lnode_clock_env m) = Env.find x (lnode_clock_env n).
    Proof.
      intros n m extra x Hin Hout Hvars Hx.
      unfold lnode_clock_env. rewrite Hin, Hout, Hvars.
      rewrite <- Env.adds'_app.
      exact (Env.gsso' x extra _ Hx).
    Qed.

    Corollary find_clock_vars_ext :
      forall (n m : node) (extra : list (ident * (type * clock))) x,
        m.(n_in) = n.(n_in) ->
        m.(n_out) = n.(n_out) ->
        m.(n_vars) = n.(n_vars) ++ extra ->
        ~ InMembers x extra ->
        find_clock (lnode_clock_env m) x = find_clock (lnode_clock_env n) x.
    Proof.
      intros n m extra x Hin Hout Hvars Hx.
      unfold find_clock.
      now rewrite (lnode_clock_env_vars_ext n m extra x Hin Hout Hvars Hx).
    Qed.

    (** And for the unnested node specifically: its extra variables are the
        ones the run created, so the two environments agree on every key the
        run did not create. *)
    Corollary find_clock_unnest_node_ext :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) x,
        ~ InMembers x (st_anns (snd (unnest_equations P n.(n_eqs) init_st))) ->
        find_clock (lnode_clock_env (unnest_node P n Hwl Hpref)) x
        = find_clock (lnode_clock_env n) x.
    Proof.
      intros P n Hwl Hpref x Hx.
      eapply find_clock_vars_ext; [reflexivity|reflexivity| |exact Hx].
      exact (proj2 (unnest_node_fields P n Hwl Hpref)).
    Qed.

    (** And the premise discharged: a variable the source equations *define* is
        never one the run created, so the two clock environments agree
        everywhere [generate_leqns_constraints] looks.

        [n_defd] puts a defined variable among the declared ones, and
        [unnest_node_new_ids_fresh] keeps the created ones out of those.  Since
        the run starts at [init_st], which has no annotations, every key of
        [st_anns] is a created id. *)
    Corollary find_clock_unnest_node_defd :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) eqs' st' x,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        In x (vars_defined n.(n_eqs)) ->
        find_clock (lnode_clock_env (unnest_node P n Hwl Hpref)) x
        = find_clock (lnode_clock_env n) x.
    Proof.
      intros P n Hwl Hpref eqs' st' x Hrun Hx.
      (** the variable is declared *)
      assert (InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) as Hdecl.
      { pose proof (n_defd n) as Hperm.
        assert (In x (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hm
            by (rewrite <- Hperm; exact Hx).
        apply fst_InMembers in Hm.
        apply InMembers_app. right.
        apply InMembers_app in Hm as [Hm|Hm];
          [apply InMembers_app; now left|apply InMembers_app; now right]. }
      (** so it is not one the run created *)
      assert (~ InMembers x (st_anns st')) as Hnew.
      { intro Hc.
        apply (unnest_node_new_ids_fresh P n Hwl Hpref eqs' st' x Hrun);
          [|exact Hdecl].
        unfold new_ids. apply filter_In. split.
        - unfold st_ids. apply fst_InMembers. exact Hc.
        - destruct (in_dec ident_eq_dec x
                     (st_ids (init_st : fresh_st (type * clock))))
            as [Hin|_]; [|reflexivity].
          exfalso. unfold st_ids in Hin. rewrite init_st_anns in Hin.
          contradiction. }
      (** and the two environments agree on it *)
      apply (find_clock_unnest_node_ext P n Hwl Hpref x).
      rewrite Hrun in *. exact Hnew.
    Qed.

    (** The bridge, assembled: the source equations generate the same
        constraints against either clock environment. *)
    Corollary generate_leqns_unnest_node_cenv :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs) (G : secglobal) eqs' st' s,
        unnest_equations P n.(n_eqs) init_st = (eqs', st') ->
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env (unnest_node P n Hwl Hpref)) n.(n_eqs) s
        = generate_leqns_constraints G env base_ty rst_ty
            (lnode_clock_env n) n.(n_eqs) s.
    Proof.
      intros P n Hwl Hpref G eqs' st' s Hrun.
      apply EQ.generate_leqns_constraints_cenv_ext.
      intros x Hx.
      exact (find_clock_unnest_node_defd P n Hwl Hpref eqs' st' x Hrun Hx).
    Qed.

    (** * The equation-level entailment, for a node

        [node_carries_preserves] with everything a node supplies: its equation
        list from [unnest_node_fields], its [NoDup] from
        [unnest_node_equations_nodup], and the two clock environments reconciled
        by [generate_leqns_unnest_node_cenv].

        The section's [cenv] has to be the *unnested* node's, since that is the
        one the target run uses and the theorem fixes a single environment; at
        the program level the section is instantiated with exactly that, so the
        hypothesis is discharged by [reflexivity].  What is left as hypotheses
        are the ambient premises -- the [A eq] family -- which is precisely what
        the pointwise contract exists to remove. *)
    Corollary unnest_node_entailment :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs)
             ce cet st0 ct1 ct1',
        cenv = lnode_clock_env (unnest_node P n Hwl Hpref) ->
        Forall (wl_equation P) n.(n_eqs) ->
        Forall (wc_equation P vars) n.(n_eqs) ->
        (forall x,
            In x (moved_by env init_st
                    (snd (unnest_equations P n.(n_eqs) init_st))) ->
            ~ In x scope) ->
        (forall eq eqs1 s s',
            In eq n.(n_eqs) -> unnest_equation P eq s = (eqs1, s') ->
            forall x ck ckty,
              In x (vars_defined eqs1) -> find_clock cenv x = OK ck ->
              assign_clk_type env base_ty ck = Some ckty ->
              incl (merge [rst_ty] ckty) (A eq)) ->
        (forall dlt,
            listSatisfiable dlt ce ->
            forall eq b, In eq n.(n_eqs) -> In b (sec_of env (fst eq)) ->
              satisfiable dlt (A eq) [b]) ->
        constraints_scoped scope ce ->
        sec_le ct1 stF ->
        generate_leqns_constraints GL env base_ty rst_ty
          (lnode_clock_env n) n.(n_eqs) st0 = OK (ce, ct1) ->
        generate_leqns_constraints GL env base_ty rst_ty
          (lnode_clock_env (unnest_node P n Hwl Hpref))
          (unnest_node P n Hwl Hpref).(n_eqs) st0 = OK (cet, ct1') ->
        preserves_on scope ce cet.
    Proof.
      intros P n Hwl Hpref ce cet st0 ct1 ct1' Hcenv Hwle Hwce Hmv Hamb Hbs
        Hcesc Hbnd Hsrc Htgt.
      (** the run, and the equation list it produced *)
      remember (unnest_equations P n.(n_eqs) init_st) as r eqn:Hr.
      destruct r as (eqs' & st').
      assert ((unnest_node P n Hwl Hpref).(n_eqs) = eqs') as Heqs'.
      { destruct (unnest_node_fields P n Hwl Hpref) as (He & _).
        rewrite He, <- Hr. reflexivity. }
      (** the source run, read against the section's clock environment *)
      assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                n.(n_eqs) st0 = OK (ce, ct1)) as Hsrc'.
      { rewrite Hcenv.
        rewrite (generate_leqns_unnest_node_cenv P n Hwl Hpref GL eqs' st' st0
                   (@Coq.Init.Logic.eq_sym _ _ _ Hr)).
        exact Hsrc. }
      (** and the target run, which already is *)
      assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                eqs' st0 = OK (cet, ct1')) as Htgt'
          by (rewrite Hcenv, <- Heqs'; exact Htgt).
      eapply node_carries_preserves;
        [exact Hwle|exact Hwce
        |exact (unnest_node_equations_nodup P n Hwl Hpref eqs' st'
                  (@Coq.Init.Logic.eq_sym _ _ _ Hr))
        | |exact Hamb|exact Hbs|exact Hcesc
        |exact (@Coq.Init.Logic.eq_sym _ _ _ Hr)
        |exact Hsrc'|exact Htgt'|exact Hbnd].
      intros x Hx. apply Hmv. cbn [snd]. exact Hx.
    Qed.

    (** * A node's locals are not its interface

        Half of [unnest_node_signatures_preserved]'s disjointness side
        condition, and the half that is provable here: what [generate_lnode_sig]
        eliminates includes the locals' security names, and those are outside
        the interface because [env] is injective and a local is not an input or
        an output -- which is [n_nodup], a field of the node record.

        The other half, that the minted names are outside it too, is a fact
        about where the run *starts*: the naming pass allocates below [st0].
        That belongs at the program level, where [st0] is chosen. *)
    Lemma locals_not_interface :
      forall (n : node) locals,
        NoDupMembers (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        forall x, In x locals ->
          ~ In x (sec_of env (List.map fst (n.(n_in) ++ n.(n_out)))).
    Proof.
      intros n locals Hnd Hloc x Hx Hc.
      (** the name comes from a local *)
      apply get_mappings_from_node_eq in Hloc.
      destruct (get_mappings_In _ env locals x Hloc Hx) as (v & Hv & Hfv).
      (** and, supposedly, from an input or an output *)
      unfold sec_of in Hc. apply in_flat_map in Hc as (w & Hw & Hxw).
      destruct (Env.find w env) as [b|] eqn:Hfw; [|contradiction].
      destruct Hxw as [Hxw|[]]; subst b.
      (** injectivity makes them the same variable *)
      assert (v = w) as ?
          by (exact (env_inj v w x x Hfv Hfw
                       (@Coq.Init.Logic.eq_refl ident x))); subst w.
      (** which [n_nodup] forbids: a local is neither an input nor an output *)
      assert (InMembers v n.(n_vars)) as Hvm by (apply fst_InMembers; exact Hv).
      apply in_map_iff in Hw as (q & Hq & Hqin).
      apply in_app_or in Hqin.
      assert (InMembers v n.(n_in) \/ InMembers v n.(n_out)) as Hqm.
      { destruct Hqin as [Hqin|Hqin];
          [left|right]; apply fst_InMembers; apply in_map_iff;
          exists q; split; [exact Hq|exact Hqin|exact Hq|exact Hqin]. }
      destruct Hqm as [Hqm|Hqm].
      - (** an input: [n_in] comes before [n_vars] *)
        apply (NoDupMembers_app_InMembers v n.(n_in)
                 (n.(n_vars) ++ n.(n_out)) Hnd Hqm).
        apply InMembers_app. now left.
      - (** an output: [n_vars] comes before [n_out] *)
        apply (NoDupMembers_app_InMembers v (n.(n_in) ++ n.(n_vars))
                 n.(n_out));
          [rewrite <- app_assoc; exact Hnd
          |apply InMembers_app; now right
          |exact Hqm].
    Qed.

    (** * Signature preservation for one unnested node

        The statement the phase is for: the signature [unnest_node] publishes
        has the *same* interface as the one [n] publishes, and its constraints
        are entailed by [n]'s on that interface.  Interface equality is
        [unnest_node_sig_interface]; the entailment is the equation-level
        theorem carried through both eliminations by [preserves_on_simplify].

        The side condition is the one that makes the backward step through the
        source's elimination sound: what it eliminates -- its locals and the
        names its run minted -- lies outside the interface.  That is what
        [unnest_node_moved_fresh_generated_aux] and the scope's definition
        arrange. *)
    Theorem unnest_node_signatures_preserved :
      forall (P : global) (n : node) (Hwl : wl_node P n)
             (Hpref : n_prefixes n = elab_prefs)
             (G : secglobal) (aux : list node_aux_names)
             st0 sg st1 sg' st1',
        (** the two aux levels are the ones this section speaks about *)
        (forall clk_id rst_id,
            get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
            Env.find clk_id env = Some base_ty
            /\ Env.find rst_id env = Some rst_ty) ->
        (** the equation-level entailment, for this node's two runs *)
        (forall ce cet ct1 ct1',
            generate_leqns_constraints G env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) st0 = OK (ce, ct1) ->
            generate_leqns_constraints G env base_ty rst_ty
              (lnode_clock_env (unnest_node P n Hwl Hpref))
              (unnest_node P n Hwl Hpref).(n_eqs) st0 = OK (cet, ct1') ->
            preserves_on scope ce cet) ->
        (** the source's raw constraints are well formed *)
        (forall ce ct1,
            generate_leqns_constraints G env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) st0 = OK (ce, ct1) ->
            wf_constraints ce) ->
        (** and what it eliminates lies outside the interface *)
        (forall locals cns ct1,
            get_mappings_from_node n.(n_vars) env = Some locals ->
            generate_leqns_constraints G env base_ty rst_ty
              (lnode_clock_env n) n.(n_eqs) st0 = OK (cns, ct1) ->
            forall x, In x (locals ++ minted st0 ct1) -> ~ In x scope) ->
        generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
        generate_lnode_sig G (unnest_node P n Hwl Hpref) env aux st0
          = OK (sg', st1') ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg
        /\ preserves_on scope sg.(s_constraints) sg'.(s_constraints).
    Proof.
      intros P n Hwl Hpref G aux st0 sg st1 sg' st1' Haux Hpres Hwf Hdisj H H'.
      assert (s_name sg' = s_name sg
              /\ s_in sg' = s_in sg
              /\ s_out sg' = s_out sg
              /\ s_clk sg' = s_clk sg
              /\ s_reset sg' = s_reset sg) as Hiface
          by exact (unnest_node_sig_interface P n Hwl Hpref G aux st0 sg st1
                      sg' st1' H H').
      destruct Hiface as (Hn & Hi & Ho & Hc & Hr).
      repeat split; try assumption.
      apply lnode_sig_inv in H
        as (c1 & r1 & ct1 & rt1 & i1 & o1 & l1 & cs1
            & Ha1 & Hc1 & Hr1 & _ & _ & Hl1 & Hcs1 & ?); subst sg.
      apply lnode_sig_inv in H'
        as (c2 & r2 & ct2 & rt2 & i2 & o2 & l2 & cs2
            & Ha2 & Hc2 & Hr2 & _ & _ & Hl2 & Hcs2 & ?); subst sg'.
      (** the aux lookups pin the two levels to the section's *)
      destruct (Haux c1 r1 Ha1) as (Hb1 & Hbr1).
      rewrite Hc1 in Hb1. apply option_Some_inj in Hb1; subst ct1.
      rewrite Hr1 in Hbr1. apply option_Some_inj in Hbr1; subst rt1.
      cbn [n_name unnest_node] in Ha2.
      destruct (Haux c2 r2 Ha2) as (Hb2 & Hbr2).
      rewrite Hc2 in Hb2. apply option_Some_inj in Hb2; subst ct2.
      rewrite Hr2 in Hbr2. apply option_Some_inj in Hbr2; subst rt2.
      cbn [s_constraints].
      (** and the entailment goes through both eliminations *)
      eapply preserves_on_simplify;
        [exact (Hwf cs1 st1 Hcs1)
        |exact (Hdisj l1 cs1 st1 Hl1 Hcs1)
        |exact (Hpres cs1 cs2 st1 st1' Hcs1 Hcs2)].
    Qed.

  End NodeEquations.

End SecLusUnnestingNodes.
