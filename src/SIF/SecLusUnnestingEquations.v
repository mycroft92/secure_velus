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
From Velus Require Import SIF.SecLusUnnestingStreams.

Module SecLusUnnestingEquations
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

Module STREAMS := SecLusUnnestingStreams Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include STREAMS.

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
    Variable amb     : ST.

    Hypothesis env_inj : env_injective env.
    Hypothesis amb_scoped : st_scoped scope amb.
    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.
    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).
    Hypothesis source_types_scoped :
      forall e ts s s',
        assign_lexp_type GL env base_ty rst_ty e s = OK (ts, s') ->
        Forall (fun t => st_scoped scope (fst t)) ts.
    Hypothesis source_lexps_scoped :
      forall es ts s s',
        assign_lexps GL env base_ty rst_ty es s = OK (ts, s') ->
        Forall (fun t => st_scoped scope (fst t)) ts.
    Hypothesis rst_ty_scoped : In rst_ty scope.
    Hypothesis clk_types_scoped :
      forall ck ckty,
        assign_clk_type env base_ty ck = Some ckty -> st_scoped scope ckty.
    Hypothesis env_range_scoped :
      forall x b, Env.find x env = Some b -> In b scope.
    Hypothesis source_lexps_carried_scoped :
      forall es ts s s',
        assign_lexps GL env base_ty rst_ty es s = OK (ts, s') ->
        constraints_scoped scope (carried ts).
    Hypothesis sig_scoped :
      forall f sg, find_signature f GL = Some sg -> signature_scoped sg.
    Hypothesis sig_actuals_fresh :
      forall f sg inp ck rst os cns sa sb,
        find_signature f GL = Some sg ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    Local Notation sec_of := (CALLS.sec_of env).
    Local Notation moved_by := (CALLS.moved_by env).
    Local Notation carries_at :=
      (CALLS.carries_at GL env base_ty rst_ty vars cenv scope amb).
    Local Notation carries :=
      (CALLS.carries GL env base_ty rst_ty vars cenv scope amb).
    Local Notation carries_list :=
      (CALLS.carries_list GL env base_ty rst_ty vars cenv scope amb).
    Local Notation lifted_defs_local :=
      (CALLS.lifted_defs GL env base_ty rst_ty cenv amb env_inj).
    Local Notation carries_list_intro_local :=
      (CALLS.carries_list_intro GL env base_ty rst_ty vars cenv scope amb
         env_inj amb_scoped).
    Local Notation sig_nodup_pipeline_local :=
      (CALLS.sig_nodup_pipeline GL sig_nodup).
    Local Notation assign_lexps_elementwise_local :=
      (CALLS.assign_lexps_elementwise GL env base_ty rst_ty).
    Local Notation unnest_fby_types_local :=
      (CALLS.unnest_fby_types GL env base_ty rst_ty).
    Local Notation unnest_arrow_types_local :=
      (CALLS.unnest_arrow_types GL env base_ty rst_ty).
    Local Notation carries_Eapp_local :=
      (CALLS.carries_Eapp GL env base_ty rst_ty vars cenv scope amb
         env_inj amb_scoped sig_good sig_nodup source_types_scoped
         source_lexps_scoped rst_ty_scoped clk_types_scoped sig_scoped
         sig_actuals_fresh).
    Local Notation noops_operand_types_local :=
      (CALLS.noops_operand_types GL env base_ty rst_ty cenv).
    Local Notation noops_step_local :=
      (CALLS.noops_step GL env base_ty rst_ty cenv amb env_inj).
    Local Notation reset_step_local :=
      (CALLS.reset_step GL env base_ty rst_ty vars cenv scope amb env_inj
         amb_scoped).
    Local Notation amb_pair_local := (CALLS.amb_pair amb).

    Local Lemma eq_moved_by_prefix :
      forall st st1 st', st_follows st1 st' ->
        incl (moved_by st st1) (moved_by st st').
    Proof. apply (CALLS.moved_by_prefix_local env). Qed.

    Local Lemma eq_moved_by_suffix :
      forall st st1 st', st_follows st st1 ->
        incl (moved_by st1 st') (moved_by st st').
    Proof. apply (CALLS.moved_by_suffix_local env). Qed.

    Local Lemma eq_moved_by_disjoint :
      forall sta stb stc x,
        In x (moved_by sta stb) -> ~ In x (moved_by stb stc).
    Proof.
      intros sta stb stc x Hin1 Hin2.
      exact (CALLS.moved_by_disjoint_local env env_inj sta stb stc x Hin1 Hin2).
    Qed.

    (** * The expression level, closed

        Every Lustre expression carries no more than what the equations its
        unnesting emits generate.  The merge and the conditional are the only
        constructors whose two [is_control] flags behave differently -- under
        [true] they are pushed inward and nothing is lifted, under [false]
        every resulting stream is bound -- so they are the only cases that
        split on the flag. *)

    Theorem carries_exp : forall P e, carries P e.
    Proof.
      intros P e. induction e using exp_ind2; intros ic.
      - apply carries_Econst.
      - apply carries_Evar.
      - apply carries_Eunop; assumption.
      - apply carries_Ebinop; assumption.
      - apply carries_Efby; assumption.
      - apply carries_Earrow; assumption.
      - apply carries_Ewhen; assumption.
      - destruct a as (tys & cl). destruct ic;
          [apply carries_Emerge_control|apply carries_Emerge_lift];
          assumption.
      - destruct a as (tys & cl). destruct ic;
          [apply carries_Eite_control|apply carries_Eite_lift]; assumption.
      - apply carries_Eapp_local; [assumption|].
        intros e1 Her. subst ro. assumption.
    Qed.

    Corollary carries_exps : forall P es, carries_list P es.
    Proof.
      intros P es. apply carries_list_intro_local.
      apply Forall_forall. intros e _. apply carries_exp.
    Qed.

    (** * The right-hand side of an equation

        [unnest_rhs] is [unnest_exp true] everywhere except at the three
        constructors an equation's variables can bind directly: a call, a
        delay and an initialised delay are left where they are, because the
        equation already has variables for their results.  So unlike
        [unnest_exp], what comes back is not always a variable, and what it
        carries is not always nothing -- a call left in place is typed again,
        with its own fresh result names and its own instantiated block.

        That is the one conclusion this level adds: what the returned
        expressions carry has to be satisfied too, because the equation's own
        rule joins it in. *)

    Definition rhs_carries (P : global) (e : exp) : Prop :=
      forall es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt,
        wl_exp P e -> wc_exp P vars e ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        (forall x ck ckty,
            In x (vars_defined eqs) -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        unnest_rhs P e st = ((es', eqs), st') ->
        assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty es' yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ listSatisfiable dlt' (carried ts'')
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ constraints_scoped (scope ++ moved_by st st') (carried ts'')
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    Lemma unnest_rhs_other :
      forall P e,
        (match e with
         | Eapp _ _ _ _ | Efby _ _ _ | Earrow _ _ _ => False
         | _ => True
         end) ->
        unnest_rhs P e = unnest_exp P true e.
    Proof. intros P e H. destruct e; try reflexivity; contradiction. Qed.

    (** The constructors an equation cannot bind directly are unnested exactly
        as they are inside an expression, and what comes back is normalized,
        so it carries nothing and the extra conclusions are vacuous. *)

    Lemma rhs_carries_other :
      forall P e,
        (match e with
         | Eapp _ _ _ _ | Efby _ _ _ | Earrow _ _ _ => False
         | _ => True
         end) ->
        rhs_carries P e.
    Proof.
      intros P e He
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      rewrite unnest_rhs_other in Hun by exact He.
      assert (Forall normalized_cexp es') as Hne
          by exact (unnest_exp_normalized_cexp P e es' eqs st st' Hun).
      destruct (assign_lexps_normalized_pure GL env base_ty rst_ty es' Hne
                  ts'' yst yst' Has') as (_ & _ & Hct & _).
      edestruct (carries_exp P e true es' eqs st st' ts sst sst'
                   ce xst xst' ts'' yst yst' dlt)
        as (dlt' & Hoff & Hce & Hrel & Hscope & Hscts);
        try assumption.
      exists dlt'. split; [exact Hoff|]. split; [exact Hce|].
      rewrite Hct. split; [constructor|]. split; [exact Hrel|].
      split; [exact Hscope|]. split; [constructor|exact Hscts].
    Qed.

    Lemma unnest_rhs_Efby_inv :
      forall P e0s es anns es' eqs st st',
        unnest_rhs P (Efby e0s es anns) st = ((es', eqs), st') ->
        exists f0 eqs1 st1 f1 eqs2,
          unnest_exps P e0s st = ((f0, eqs1), st1)
          /\ unnest_exps P es st1 = ((f1, eqs2), st')
          /\ es' = unnest_fby f0 f1 anns
          /\ eqs = eqs1 ++ eqs2.
    Proof.
      intros P e0s es anns es' eqs st st' H.
      simpl in H. repeat inv_bind.
      repeat esplit; eauto.
      all: unfold unnest_exps; apply bind2_spec;
           repeat esplit; eauto using ret_spec.
    Qed.

    Lemma unnest_rhs_Earrow_inv :
      forall P e0s es anns es' eqs st st',
        unnest_rhs P (Earrow e0s es anns) st = ((es', eqs), st') ->
        exists f0 eqs1 st1 f1 eqs2,
          unnest_exps P e0s st = ((f0, eqs1), st1)
          /\ unnest_exps P es st1 = ((f1, eqs2), st')
          /\ es' = unnest_arrow f0 f1 anns
          /\ eqs = eqs1 ++ eqs2.
    Proof.
      intros P e0s es anns es' eqs st st' H.
      simpl in H. repeat inv_bind.
      repeat esplit; eauto.
      all: unfold unnest_exps; apply bind2_spec;
           repeat esplit; eauto using ret_spec.
    Qed.

    (** The operands of the delays a right-hand side came back as are typed,
        because the delays themselves are.  Their types are what the
        induction hypothesis on the two operand lists needs, and at the top of
        an equation nothing else computes them: no defining equation is
        emitted to read them back off. *)

    Lemma unnest_fby_operands_typed :
      forall (e0s es : list exp) anns ts'' s s',
        Forall normalized_cexp e0s -> Forall normalized_cexp es ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        assign_lexps GL env base_ty rst_ty (unnest_fby e0s es anns) s
          = OK (ts'', s') ->
        exists ts0 us,
          (forall q, assign_lexps GL env base_ty rst_ty e0s q = OK (ts0, q))
          /\ (forall q, assign_lexps GL env base_ty rst_ty es q = OK (us, q)).
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts'' s s' Hn0 Hn1 Hl0 Hl1 H.
      - destruct anns; simpl in Hl0; [|discriminate Hl0].
        destruct es; simpl in Hl1; [|discriminate Hl1].
        exists [], []. split; intros q; now rewrite assign_lexps_nil.
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_fby_cons in H.
        apply assign_lexps_carried_cons in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        rewrite assign_lexp_Efby in Ht.
        apply sec_bind_inv in Ht as (t0 & s1 & Ht0 & Ht).
        apply sec_bind_inv in Ht as (u0 & s2 & Hu0 & _).
        assert (Forall normalized_cexp [e0]) as Hne0
            by (constructor; [exact H2|constructor]).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty [e0]
                    Hne0 t0 s s1 Ht0) as (_ & _ & _ & Ht0').
        assert (Forall normalized_cexp [e]) as Hne
            by (constructor; [exact H4|constructor]).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty [e]
                    Hne u0 s1 s2 Hu0) as (_ & _ & _ & Hu0').
        edestruct (IH es anns r sta s') as (ts0 & us & Hts0 & Hus);
          [assumption|assumption|lia|lia|exact Hr|].
        exists (t0 ++ ts0), (u0 ++ us). split.
        + intros q. rewrite assign_lexps_cons.
          unfold SC.bind.
          rewrite (assign_lexps_single GL env base_ty rst_ty e0 t0 q q
                     (Ht0' q)), (Hts0 q).
          reflexivity.
        + intros q. rewrite assign_lexps_cons.
          unfold SC.bind.
          rewrite (assign_lexps_single GL env base_ty rst_ty e u0 q q
                     (Hu0' q)), (Hus q).
          reflexivity.
    Qed.

    Lemma unnest_arrow_operands_typed :
      forall (e0s es : list exp) anns ts'' s s',
        Forall normalized_cexp e0s -> Forall normalized_cexp es ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        assign_lexps GL env base_ty rst_ty (unnest_arrow e0s es anns) s
          = OK (ts'', s') ->
        exists ts0 us,
          (forall q, assign_lexps GL env base_ty rst_ty e0s q = OK (ts0, q))
          /\ (forall q, assign_lexps GL env base_ty rst_ty es q = OK (us, q)).
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts'' s s' Hn0 Hn1 Hl0 Hl1 H.
      - destruct anns; simpl in Hl0; [|discriminate Hl0].
        destruct es; simpl in Hl1; [|discriminate Hl1].
        exists [], []. split; intros q; now rewrite assign_lexps_nil.
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_arrow_cons in H.
        apply assign_lexps_carried_cons in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        rewrite assign_lexp_Earrow in Ht.
        apply sec_bind_inv in Ht as (t0 & s1 & Ht0 & Ht).
        apply sec_bind_inv in Ht as (u0 & s2 & Hu0 & _).
        assert (Forall normalized_cexp [e0]) as Hne0
            by (constructor; [exact H2|constructor]).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty [e0]
                    Hne0 t0 s s1 Ht0) as (_ & _ & _ & Ht0').
        assert (Forall normalized_cexp [e]) as Hne
            by (constructor; [exact H4|constructor]).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty [e]
                    Hne u0 s1 s2 Hu0) as (_ & _ & _ & Hu0').
        edestruct (IH es anns r sta s') as (ts0 & us & Hts0 & Hus);
          [assumption|assumption|lia|lia|exact Hr|].
        exists (t0 ++ ts0), (u0 ++ us). split.
        + intros q. rewrite assign_lexps_cons.
          unfold SC.bind.
          rewrite (assign_lexps_single GL env base_ty rst_ty e0 t0 q q
                     (Ht0' q)), (Hts0 q).
          reflexivity.
        + intros q. rewrite assign_lexps_cons.
          unfold SC.bind.
          rewrite (assign_lexps_single GL env base_ty rst_ty e u0 q q
                     (Hu0' q)), (Hus q).
          reflexivity.
    Qed.

    (** A list of expressions whose types are pinned elementwise has exactly
        those types, whatever state it is typed from. *)

    Lemma assign_lexps_determined :
      forall (es : list exp) (rs : list LST) q ts s',
        Forall2 (fun e r =>
          (match e with Eapp _ _ _ _ => False | _ => True end)
          /\ (forall tss s0 s0',
                assign_lexp_type GL env base_ty rst_ty e s0 = OK (tss, s0') ->
                s0' = s0 /\ List.length tss = 1 /\ carried tss = [])
          /\ (forall tf s0 s0',
                assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                tf = r)) es rs ->
        assign_lexps GL env base_ty rst_ty es q = OK (ts, s') ->
        ts = rs /\ s' = q.
    Proof.
      intros es rs q ts s' Hall. revert q ts s'.
      induction Hall as [|e r es0 rs0 (_ & Hp & Hr) Hrest IH];
        intros q ts s' H.
      - apply (assign_lexps_carried_nil GL env base_ty rst_ty) in H
          as (? & _ & ?); subst. auto.
      - apply assign_lexps_carried_cons in H
          as (t & rest & sta & Ht & Hrest' & ? & _); subst.
        destruct (Hp _ _ _ Ht) as (? & Hlt & _); subst sta.
        destruct t as [|t0 [|]]; simpl in Hlt; try discriminate.
        assert (t0 = r) as ? by exact (Hr t0 q q Ht); subst t0.
        edestruct IH as (? & ?); [exact Hrest'|]; subst. auto.
    Qed.

    (** * The delay at the top of a right-hand side

        [Efby] inside an expression lifts: one variable per result, one
        emitted equation each.  At the top of an equation it does not -- the
        equation's own variables bind the delays, and what [unnest_rhs]
        returns is the delays themselves.  So this is [carries_Efby] without
        its [lifted_defs] step, and with one thing to do instead: read the
        operands' types back off the delays, since no emitted equation
        computes them here. *)

    Lemma rhs_carries_Efby :
      forall P e0s es anns, rhs_carries P (Efby e0s es anns).
    Proof.
      intros P e0s es anns
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      pose proof Hwl as Hwlfby.
      inv Hwl. inv Hwc.
      apply unnest_rhs_Efby_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & Hun0 & Hun1 & ? & ?); subst.
      apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
      apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by exact (map_bind2_unnest_st_follows P false e0s ess0 eqss0
                      st st1 Hmap0).
      assert (st_follows st1 st') as Hf1
          by exact (map_bind2_unnest_st_follows P false es ess1 eqss1
                      st1 st' Hmap1).

      rewrite assign_lexp_Efby in Has.
      apply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      apply sec_bind_inv in Has as (us & sb & Hus & Hj).

      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      assert (Forall normalized_lexp (List.concat ess0)) as Hn0
          by exact (map_bind2_unnest_normalized_lexp P e0s ess0 eqss0
                      st st1 Hmap0).
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1
          by exact (map_bind2_unnest_normalized_lexp P es ess1 eqss1
                      st1 st' Hmap1).
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (rewrite Forall_forall in Hn0 |- *;
              intros e' He'; constructor; exact (Hn0 e' He')).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (rewrite Forall_forall in Hn1 |- *;
              intros e' He'; constructor; exact (Hn1 e' He')).
      assert (List.length (List.concat ess0) = List.length anns) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := e0s); eauto).
      assert (List.length (List.concat ess1) = List.length anns) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es); eauto).

      edestruct (unnest_fby_operands_typed (List.concat ess0)
                   (List.concat ess1) anns ts'' yst yst')
        as (ts0x & usx & Ht0x & Hux);
        [exact Hc0|exact Hc1|exact Hle0|exact Hle1|exact Has'|].

      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct
          by exact (ljoin_list_carried ts0 us ts sb sst' Hj).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc0 & Hsc1).
      apply listSatisfiable_cmerge in Hcar as (Hcar0 & Hcar1).
      pose proof Hsts as Hstsall.
      destruct (ljoin_list_scoped_plain_inv scope ts0 us ts sb sst' Hj Hsts)
        as (Hsts0 & Hsts1).

      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st)
                (st_ids st1)) as Hp0.
      { exact (map_bind2_unnest_vars_perm P false e0s ess0 eqss0 st st1
                 H2 Hmap0). }

      edestruct (carries_exps P e0s false ess0 eqss0 st st1 ts0
                   sst sa ce1 xst xstm ts0x yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { exact (NoDup_vd_app_l (List.concat eqss0) (List.concat eqss1)
                 (st_ids st) Hnd). }
      { intros y Hy. apply Hmv.
        apply (eq_moved_by_prefix st st1 st' Hf1). exact Hy. }
      { exact Hsc0. }
      { exact Hsts0. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hts0. }
      { exact Hgen1. }
      { apply (Ht0x yst). }
      { exact Hcar0. }

      edestruct (carries_exps P es false ess1 eqss1 st1 st' us
                   sa sb ce2 xstm xst' usx yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { exact (NoDup_vd_app_r (List.concat eqss0) (List.concat eqss1)
                 (st_ids st) (st_ids st1) Hp0 Hnd). }
      { intros y Hy. apply Hmv.
        apply (eq_moved_by_suffix st st1 st' Hf0). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hus. }
      { exact Hgen2. }
      { apply (Hux yst). }
      { assert (forall y, In y (moved_by st st1) -> ~ In y scope) as Hfresh.
        { intros y Hy. apply Hmv.
          apply (eq_moved_by_prefix st st1 st' Hf1). exact Hy. }
        exact (listSatisfiable_off scope (carried us) (moved_by st st1)
                 dlt dlt1 Hsc1 Hfresh Hoff1 Hcar1). }

      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts0x) as Hew0
          by exact (assign_lexps_elementwise_local (List.concat ess0) ts0x
                      yst yst Hc0 (Ht0x yst)).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) usx) as Hew1
          by exact (assign_lexps_elementwise_local (List.concat ess1) usx
                      yst yst Hc1 (Hux yst)).
      destruct (unnest_fby_types_local (List.concat ess0) (List.concat ess1)
                  anns ts0x usx yst Hew0 Hew1 Hle0 Hle1)
        as (rs & Hjr & Hallr).
      assert (ts'' = rs /\ yst' = yst) as (? & ?)
          by exact (assign_lexps_determined
                      (unnest_fby (List.concat ess0) (List.concat ess1) anns)
                      rs yst ts'' yst' Hallr Has');
        subst.

      assert (carried rs = []) as Hcrs.
      { erewrite ljoin_list_carried by exact Hjr.
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty
                    (List.concat ess0) Hc0 ts0x yst yst (Ht0x yst))
          as (_ & _ & Hz0 & _).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty
                    (List.concat ess1) Hc1 usx yst yst (Hux yst))
          as (_ & _ & Hz1 & _).
        rewrite Hz0, Hz1. reflexivity. }

      assert (forall y, In y (moved_by st1 st') ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - apply (Hmv y); [|exact Hy].
          apply (eq_moved_by_suffix st st1 st' Hf0). exact Hin.
        - exact (eq_moved_by_disjoint st st1 st' y Hy Hin). }
      assert (Forall2 (fun t t' =>
                satisfiable dlt2 (fst t') (merge amb (fst t))) ts0 ts0x)
        as Hrel1'.
      { assert (incl scope (scope ++ moved_by st st1)) as Hscopeincl.
        { intros x Hx. apply in_or_app. left. exact Hx. }
        assert (st_scoped (scope ++ moved_by st st1) amb) as Hamb'.
        { exact (st_scoped_weaken scope (scope ++ moved_by st st1) amb
                   Hscopeincl amb_scoped). }
        assert (Forall (fun t => st_scoped (scope ++ moved_by st st1) (fst t))
                  ts0) as Hsts0'.
        { rewrite Forall_forall in Hsts0 |- *.
          intros q Hq.
          exact (st_scoped_weaken scope (scope ++ moved_by st st1) (fst q)
                   Hscopeincl (Hsts0 q Hq)). }
        exact (Forall2_rel_off amb dlt1 dlt2 (moved_by st1 st') ts0 ts0x
                 (scope ++ moved_by st st1) Hoff2 Hsep12 Hamb' Hsts0'
                 Hts1 Hrel1). }

      assert (incl (scope ++ moved_by st st1) (scope ++ moved_by st st'))
        as Hinc1.
      { intros x Hx. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app.
        - left. exact Hx.
        - right. exact (eq_moved_by_prefix st st1 st' Hf1 x Hx). }
      assert (incl (scope ++ moved_by st1 st') (scope ++ moved_by st st'))
        as Hinc2.
      { intros x Hx. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app.
        - left. exact Hx.
        - right. exact (eq_moved_by_suffix st st1 st' Hf0 x Hx). }

      exists dlt2. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - assert (agree_off (moved_by st st') dlt dlt1) as Hoff1'.
        { exact (agree_off_incl (moved_by st st1) (moved_by st st') dlt dlt1
                   (eq_moved_by_prefix st st1 st' Hf1) Hoff1). }
        assert (agree_off (moved_by st st') dlt1 dlt2) as Hoff2'.
        { exact (agree_off_incl (moved_by st1 st') (moved_by st st') dlt1 dlt2
                   (eq_moved_by_suffix st st1 st' Hf0) Hoff2). }
        exact (agree_off_trans (moved_by st st') dlt dlt1 dlt2
                 Hoff1' Hoff2').
      - apply listSatisfiable_app. split; [|exact Hce2].
        exact (listSatisfiable_off_scope ce1 (scope ++ moved_by st st1)
                 (moved_by st1 st') dlt1 dlt2 Hscope1 Hsep12 Hoff2 Hce1).
      - rewrite Hcrs. constructor.
      - exact (ljoin_list_rel_plain amb dlt2 ts0 us ts ts0x usx rs
                 sb sst' yst yst Hj Hjr Hrel1' Hrel2).
      - apply Forall_app. split.
        + unfold constraints_scoped, SymTypes.constraints_scoped in Hscope1 |- *.
          rewrite Forall_forall in Hscope1 |- *.
          intros cc Hcc.
          exact (constraint_scoped_incl (scope ++ moved_by st st1)
                   (scope ++ moved_by st st') cc Hinc1 (Hscope1 cc Hcc)).
        + unfold constraints_scoped, SymTypes.constraints_scoped in Hscope2 |- *.
          rewrite Forall_forall in Hscope2 |- *.
          intros cc Hcc.
          exact (constraint_scoped_incl (scope ++ moved_by st1 st')
                   (scope ++ moved_by st st') cc Hinc2 (Hscope2 cc Hcc)).
      - rewrite Hcrs. constructor.
      - assert (Forall (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                  ts0x) as Hts1'.
        { rewrite Forall_forall in Hts1 |- *.
          intros q Hq.
          exact (st_scoped_weaken (scope ++ moved_by st st1)
                   (scope ++ moved_by st st') (fst q) Hinc1 (Hts1 q Hq)). }
        assert (Forall (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                  usx) as Hts2'.
        { rewrite Forall_forall in Hts2 |- *.
          intros q Hq.
          exact (st_scoped_weaken (scope ++ moved_by st1 st')
                   (scope ++ moved_by st st') (fst q) Hinc2 (Hts2 q Hq)). }
        exact (ljoin_list_scoped_plain (scope ++ moved_by st st') ts0x usx
                 rs yst yst Hjr Hts1' Hts2').
    Qed.

    (** The initialised delay, which behaves exactly as the delay does

        at the top of a right-hand side. *)

    Lemma rhs_carries_Earrow :
      forall P e0s es anns, rhs_carries P (Earrow e0s es anns).
    Proof.
      intros P e0s es anns
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      pose proof Hwl as Hwlarrow.
      inv Hwl. inv Hwc.
      apply unnest_rhs_Earrow_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & Hun0 & Hun1 & ? & ?); subst.
      apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
      apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by exact (map_bind2_unnest_st_follows P false e0s ess0 eqss0
                      st st1 Hmap0).
      assert (st_follows st1 st') as Hf1
          by exact (map_bind2_unnest_st_follows P false es ess1 eqss1
                      st1 st' Hmap1).

      rewrite assign_lexp_Earrow in Has.
      apply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      apply sec_bind_inv in Has as (us & sb & Hus & Hj).

      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & ?); subst.

      assert (Forall normalized_lexp (List.concat ess0)) as Hn0
          by exact (map_bind2_unnest_normalized_lexp P e0s ess0 eqss0
                      st st1 Hmap0).
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1
          by exact (map_bind2_unnest_normalized_lexp P es ess1 eqss1
                      st1 st' Hmap1).
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0
          by (rewrite Forall_forall in Hn0 |- *;
              intros e' He'; constructor; exact (Hn0 e' He')).
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1
          by (rewrite Forall_forall in Hn1 |- *;
              intros e' He'; constructor; exact (Hn1 e' He')).
      assert (List.length (List.concat ess0) = List.length anns) as Hle0
          by (erewrite map_bind2_unnest_exp_length with (es := e0s); eauto).
      assert (List.length (List.concat ess1) = List.length anns) as Hle1
          by (erewrite map_bind2_unnest_exp_length with (es := es); eauto).

      edestruct (unnest_arrow_operands_typed (List.concat ess0)
                   (List.concat ess1) anns ts'' yst yst')
        as (ts0x & usx & Ht0x & Hux);
        [exact Hc0|exact Hc1|exact Hle0|exact Hle1|exact Has'|].

      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct
          by exact (ljoin_list_carried ts0 us ts sb sst' Hj).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc0 & Hsc1).
      apply listSatisfiable_cmerge in Hcar as (Hcar0 & Hcar1).
      pose proof Hsts as Hstsall.
      destruct (ljoin_list_scoped_plain_inv scope ts0 us ts sb sst' Hj Hsts)
        as (Hsts0 & Hsts1).

      assert (Permutation (vars_defined (List.concat eqss0) ++ st_ids st)
                (st_ids st1)) as Hp0.
      { exact (map_bind2_unnest_vars_perm P false e0s ess0 eqss0 st st1
                 H2 Hmap0). }

      edestruct (carries_exps P e0s false ess0 eqss0 st st1 ts0
                   sst sa ce1 xst xstm ts0x yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { exact (NoDup_vd_app_l (List.concat eqss0) (List.concat eqss1)
                 (st_ids st) Hnd). }
      { intros y Hy. apply Hmv.
        apply (eq_moved_by_prefix st st1 st' Hf1). exact Hy. }
      { exact Hsc0. }
      { exact Hsts0. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. now left. }
      { exact Hmap0. }
      { exact Hts0. }
      { exact Hgen1. }
      { apply (Ht0x yst). }
      { exact Hcar0. }

      edestruct (carries_exps P es false ess1 eqss1 st1 st' us
                   sa sb ce2 xstm xst' usx yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { exact (NoDup_vd_app_r (List.concat eqss0) (List.concat eqss1)
                 (st_ids st) (st_ids st1) Hp0 Hnd). }
      { intros y Hy. apply Hmv.
        apply (eq_moved_by_suffix st st1 st' Hf0). exact Hy. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        rewrite vars_defined_app. apply in_or_app. now right. }
      { exact Hmap1. }
      { exact Hus. }
      { exact Hgen2. }
      { apply (Hux yst). }
      { assert (forall y, In y (moved_by st st1) -> ~ In y scope) as Hfresh.
        { intros y Hy. apply Hmv.
          apply (eq_moved_by_prefix st st1 st' Hf1). exact Hy. }
        exact (listSatisfiable_off scope (carried us) (moved_by st st1)
                 dlt dlt1 Hsc1 Hfresh Hoff1 Hcar1). }

      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess0) ts0x) as Hew0
          by exact (assign_lexps_elementwise_local (List.concat ess0) ts0x
                      yst yst Hc0 (Ht0x yst)).
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = [])
                (List.concat ess1) usx) as Hew1
          by exact (assign_lexps_elementwise_local (List.concat ess1) usx
                      yst yst Hc1 (Hux yst)).
      destruct (unnest_arrow_types_local (List.concat ess0) (List.concat ess1)
                  anns ts0x usx yst Hew0 Hew1 Hle0 Hle1)
        as (rs & Hjr & Hallr).
      assert (ts'' = rs /\ yst' = yst) as (? & ?)
          by exact (assign_lexps_determined
                      (unnest_arrow (List.concat ess0) (List.concat ess1) anns)
                      rs yst ts'' yst' Hallr Has');
        subst.

      assert (carried rs = []) as Hcrs.
      { erewrite ljoin_list_carried by exact Hjr.
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty
                    (List.concat ess0) Hc0 ts0x yst yst (Ht0x yst))
          as (_ & _ & Hz0 & _).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty
                    (List.concat ess1) Hc1 usx yst yst (Hux yst))
          as (_ & _ & Hz1 & _).
        rewrite Hz0, Hz1. reflexivity. }

      assert (forall y, In y (moved_by st1 st') ->
                        ~ In y (scope ++ moved_by st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - apply (Hmv y); [|exact Hy].
          apply (eq_moved_by_suffix st st1 st' Hf0). exact Hin.
        - exact (eq_moved_by_disjoint st st1 st' y Hy Hin). }
      assert (Forall2 (fun t t' =>
                satisfiable dlt2 (fst t') (merge amb (fst t))) ts0 ts0x)
        as Hrel1'.
      { assert (incl scope (scope ++ moved_by st st1)) as Hscopeincl.
        { intros x Hx. apply in_or_app. left. exact Hx. }
        assert (st_scoped (scope ++ moved_by st st1) amb) as Hamb'.
        { exact (st_scoped_weaken scope (scope ++ moved_by st st1) amb
                   Hscopeincl amb_scoped). }
        assert (Forall (fun t => st_scoped (scope ++ moved_by st st1) (fst t))
                  ts0) as Hsts0'.
        { rewrite Forall_forall in Hsts0 |- *.
          intros q Hq.
          exact (st_scoped_weaken scope (scope ++ moved_by st st1) (fst q)
                   Hscopeincl (Hsts0 q Hq)). }
        exact (Forall2_rel_off amb dlt1 dlt2 (moved_by st1 st') ts0 ts0x
                 (scope ++ moved_by st st1) Hoff2 Hsep12 Hamb' Hsts0'
                 Hts1 Hrel1). }

      assert (incl (scope ++ moved_by st st1) (scope ++ moved_by st st'))
        as Hinc1.
      { intros x Hx. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app.
        - left. exact Hx.
        - right. exact (eq_moved_by_prefix st st1 st' Hf1 x Hx). }
      assert (incl (scope ++ moved_by st1 st') (scope ++ moved_by st st'))
        as Hinc2.
      { intros x Hx. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app.
        - left. exact Hx.
        - right. exact (eq_moved_by_suffix st st1 st' Hf0 x Hx). }

      exists dlt2. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - assert (agree_off (moved_by st st') dlt dlt1) as Hoff1'.
        { exact (agree_off_incl (moved_by st st1) (moved_by st st') dlt dlt1
                   (eq_moved_by_prefix st st1 st' Hf1) Hoff1). }
        assert (agree_off (moved_by st st') dlt1 dlt2) as Hoff2'.
        { exact (agree_off_incl (moved_by st1 st') (moved_by st st') dlt1 dlt2
                   (eq_moved_by_suffix st st1 st' Hf0) Hoff2). }
        exact (agree_off_trans (moved_by st st') dlt dlt1 dlt2
                 Hoff1' Hoff2').
      - apply listSatisfiable_app. split; [|exact Hce2].
        exact (listSatisfiable_off_scope ce1 (scope ++ moved_by st st1)
                 (moved_by st1 st') dlt1 dlt2 Hscope1 Hsep12 Hoff2 Hce1).
      - rewrite Hcrs. constructor.
      - exact (ljoin_list_rel_plain amb dlt2 ts0 us ts ts0x usx rs
                 sb sst' yst yst Hj Hjr Hrel1' Hrel2).
      - apply Forall_app. split.
        + unfold constraints_scoped, SymTypes.constraints_scoped in Hscope1 |- *.
          rewrite Forall_forall in Hscope1 |- *.
          intros cc Hcc.
          exact (constraint_scoped_incl (scope ++ moved_by st st1)
                   (scope ++ moved_by st st') cc Hinc1 (Hscope1 cc Hcc)).
        + unfold constraints_scoped, SymTypes.constraints_scoped in Hscope2 |- *.
          rewrite Forall_forall in Hscope2 |- *.
          intros cc Hcc.
          exact (constraint_scoped_incl (scope ++ moved_by st1 st')
                   (scope ++ moved_by st st') cc Hinc2 (Hscope2 cc Hcc)).
      - rewrite Hcrs. constructor.
      - assert (Forall (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                  ts0x) as Hts1'.
        { rewrite Forall_forall in Hts1 |- *.
          intros q Hq.
          exact (st_scoped_weaken (scope ++ moved_by st st1)
                   (scope ++ moved_by st st') (fst q) Hinc1 (Hts1 q Hq)). }
        assert (Forall (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                  usx) as Hts2'.
        { rewrite Forall_forall in Hts2 |- *.
          intros q Hq.
          exact (st_scoped_weaken (scope ++ moved_by st1 st')
                   (scope ++ moved_by st st') (fst q) Hinc2 (Hts2 q Hq)). }
        exact (ljoin_list_scoped_plain (scope ++ moved_by st st') ts0x usx
                 rs yst yst Hjr Hts1' Hts2').
    Qed.

    (** * The right-hand side level, closed away from calls

        Every right-hand side but a call.  The call is left out deliberately,
        and not because it is hard: at the top of an equation a call is never
        *typed* as an expression at all.  The equation generator's call rule
        instantiates the callee directly, with the equation's own variables
        as the outputs, so the type [assign_lexp_type] would give the
        returned [Eapp] -- with its own freshly minted result names -- is
        never looked at.  Which is just as well, because those names are the
        security monad's and not the run's, so no witness this statement is
        allowed to build could say anything about them.

        The equation level therefore branches on whether its right-hand side
        is a call, and this covers the branch that is not. *)

    Theorem rhs_carries_exp :
      forall P e,
        (match e with Eapp _ _ _ _ => False | _ => True end) ->
        rhs_carries P e.
    Proof.
      intros P e He. destruct e; try (apply rhs_carries_other; exact I).
      - apply rhs_carries_Efby.
      - apply rhs_carries_Earrow.
      - contradiction.
    Qed.

    (** * The general rule, monotone in the right-hand side's types

        The rule for an equation that is not a call constrains each defined
        variable above the ambient of its own clock joined with the type of
        the stream that defines it, and releases whatever that type carried.
        Weakening the stream types -- modulo the ambient, which is what
        unnesting does to them -- weakens the obligations with them, provided
        the ambient lies below each defined variable.

        For this rule that proviso is free: the *source* equation's own
        constraint already puts [ambient (clock x)] below [x], and at the top
        of an equation the ambient is exactly that.  It is the call rule,
        whose constraint is an instantiated block rather than an ordering,
        that has to be given it. *)

    Lemma order_iff_satisfiable :
      forall dlt s b, Lat.order (hm_ext dlt s) (dlt b) <-> satisfiable dlt s [b].
    Proof.
      intros dlt s b. unfold satisfiable.
      rewrite hm_ext_single, <- join_bottom_eq1. reflexivity.
    Qed.

    Lemma eqn_clock_type_pure :
      forall x, state_pure (eqn_clock_type env base_ty cenv x).
    Proof.
      intros x. unfold eqn_clock_type.
      apply state_pure_bind.
      - unfold res_to_sec. destruct (find_clock cenv x);
          [apply state_pure_ret|apply state_pure_error].
      - intro ck. apply state_pure_option_to_sec.
    Qed.

    (** * What an emitted equation generates does not depend on the state

        Every equation unnesting emits is [unnested_equation]: one expression
        on the right-hand side, and no call anywhere below its top.  Nothing
        there mints a result name -- which is the only thing the security
        state carries -- so the constraints an emitted equation generates are
        a function of the equation alone.

        That is what lets a run over a list of emitted equations be cut and
        put back together in another order, which is what the chunked
        equation rule needs: unnesting emits every split equation before
        every auxiliary one, while the typing rule interleaves them chunk by
        chunk. *)

    Lemma state_pure_single :
      forall (ts : list LST), state_pure (single ts).
    Proof.
      intros ts. unfold single.
      destruct ts as [|t [|]];
        (apply state_pure_ret || apply state_pure_error).
    Qed.

    Lemma state_pure_assign_lexp_cexp :
      forall e, normalized_cexp e ->
        state_pure (assign_lexp_type GL env base_ty rst_ty e).
    Proof.
      intros e Hn st1 st2 ts st1' H.
      apply assign_lexp_normalized_cexp_pure in H as (? & _ & _ & Hs);
        [|exact Hn].
      split; [assumption|apply Hs].
    Qed.

    Lemma state_pure_assign_lexps_lexp :
      forall es, Forall normalized_lexp es ->
        state_pure (assign_lexps GL env base_ty rst_ty es).
    Proof.
      intros es Hn st1 st2 ts st1' H.
      assert (Forall normalized_cexp es) as Hnc.
      { rewrite Forall_forall in Hn |- *.
        intros e He. exact (normalized_lexp_cexp e (Hn e He)). }
      destruct (assign_lexps_normalized_pure GL env base_ty rst_ty es Hnc
                  ts st1 st1' H) as (Heq & _ & _ & Hs).
      split; [exact Heq|exact (Hs st2)].
    Qed.

    Lemma state_pure_ljoin_list :
      forall (ts us : list LST), state_pure (ljoin_list ts us).
    Proof.
      induction ts as [|t ts IH]; intros us; destruct us as [|u us]; simpl;
        try apply state_pure_error; try apply state_pure_ret.
      apply state_pure_bind; [apply IH|intro rs]. apply state_pure_ret.
    Qed.

    Lemma state_pure_assign_lexp_fby :
      forall e0s es ans,
        Forall normalized_lexp e0s -> Forall normalized_lexp es ->
        state_pure (assign_lexp_type GL env base_ty rst_ty (Efby e0s es ans)).
    Proof.
      intros e0s es ans H0 H1. rewrite assign_lexp_Efby.
      apply state_pure_bind; [now apply state_pure_assign_lexps_lexp|intro ts].
      apply state_pure_bind; [now apply state_pure_assign_lexps_lexp|intro us].
      apply state_pure_ljoin_list.
    Qed.

    Lemma state_pure_assign_lexp_arrow :
      forall e0s es ans,
        Forall normalized_lexp e0s -> Forall normalized_lexp es ->
        state_pure (assign_lexp_type GL env base_ty rst_ty (Earrow e0s es ans)).
    Proof.
      intros e0s es ans H0 H1. rewrite assign_lexp_Earrow.
      apply state_pure_bind; [now apply state_pure_assign_lexps_lexp|intro ts].
      apply state_pure_bind; [now apply state_pure_assign_lexps_lexp|intro us].
      apply state_pure_ljoin_list.
    Qed.

    Lemma state_pure_generate_lvars :
      forall xs bs ts,
        state_pure
          (generate_lvars_constraints env base_ty rst_ty cenv xs bs ts).
    Proof.
      induction xs as [|x xs IH]; intros bs ts;
        destruct bs as [|b bs]; destruct ts as [|t ts]; simpl;
        try apply state_pure_error; try apply state_pure_ret.
      apply state_pure_bind; [apply eqn_clock_type_pure|intro ckty].
      apply state_pure_bind; [apply IH|intro rest].
      apply state_pure_ret.
    Qed.

    Lemma state_pure_generate_ldef :
      forall x e,
        state_pure (assign_lexp_type GL env base_ty rst_ty e) ->
        state_pure (generate_ldef_constraint GL env base_ty rst_ty cenv x e).
    Proof.
      intros x e He. unfold generate_ldef_constraint.
      apply state_pure_bind; [apply eqn_clock_type_pure|intro ckty].
      apply state_pure_bind; [exact He|intro ts].
      apply state_pure_bind; [apply state_pure_single|intro t].
      apply state_pure_bind; [apply state_pure_find_env|intro b].
      apply state_pure_ret.
    Qed.

    Lemma state_pure_generate_lcall :
      forall xs f es rstty,
        Forall normalized_lexp es ->
        state_pure
          (generate_lcall_constraint GL env base_ty rst_ty xs f es rstty).
    Proof.
      intros xs f es rstty Hn. unfold generate_lcall_constraint.
      destruct (find_signature f GL) as [sg|]; [|apply state_pure_error].
      apply state_pure_bind; [apply state_pure_option_to_sec|intro ckty].
      apply state_pure_bind;
        [now apply state_pure_assign_lexps_lexp|intro argts].
      apply state_pure_bind;
        [apply state_pure_mmap; intro; apply state_pure_find_env|intro outs].
      apply state_pure_bind;
        [apply state_pure_generate_constraints|intro cs].
      apply state_pure_ret.
    Qed.

    Lemma state_pure_generate_leqn :
      forall (P : global) eq,
        unnested_equation P eq ->
        state_pure (generate_leqn_constraint GL env base_ty rst_ty cenv eq).
    Proof.
      intros P eq Hu. inv Hu.
      - (** a call with no reset *)
        match goal with
        | |- state_pure (generate_leqn_constraint _ _ _ _ _ (?l, _)) =>
            destruct l as [|z zs]
        end; [apply state_pure_ret|].
        rewrite gen_leqn_Eapp. now apply state_pure_generate_lcall.
      - (** a call reset by a variable *)
        match goal with
        | |- state_pure (generate_leqn_constraint _ _ _ _ _ (?l, _)) =>
            destruct l as [|z zs]
        end; [apply state_pure_ret|].
        rewrite gen_leqn_Eapp_someresetel.
        apply state_pure_bind;
          [apply state_pure_assign_lexp_cexp;
           apply normalized_lexp_cexp; constructor|intro t1].
        apply state_pure_bind; [apply state_pure_single|intro a1].
        apply state_pure_bind; [apply state_pure_option_to_sec|intro rck].
        now apply state_pure_generate_lcall.
      - (** a delayed definition *)
        rewrite generate_leqn_constraint_def by exact I.
        apply state_pure_generate_ldef.
        apply state_pure_assign_lexp_fby; now constructor.
      - (** an arrow *)
        rewrite generate_leqn_constraint_def by exact I.
        apply state_pure_generate_ldef.
        apply state_pure_assign_lexp_arrow; now constructor.
      - (** an ordinary definition *)
        match goal with H : normalized_cexp ?e |- _ =>
          assert (match e with Eapp _ _ _ _ => False | _ => True end) as Hne
            by (inv H; try exact I;
                match goal with Hl : normalized_lexp _ |- _ => inv Hl end;
                exact I)
        end.
        rewrite generate_leqn_constraint_def by exact Hne.
        apply state_pure_generate_ldef.
        now apply state_pure_assign_lexp_cexp.
    Qed.

    Lemma state_pure_generate_leqns :
      forall (P : global) eqs,
        Forall (unnested_equation P) eqs ->
        state_pure (generate_leqns_constraints GL env base_ty rst_ty cenv eqs).
    Proof.
      intros P eqs Hu. induction Hu as [|eq eqs He Hes IH];
        [apply state_pure_ret|].
      rewrite generate_leqns_constraints_cons.
      apply state_pure_bind;
        [exact (state_pure_generate_leqn P eq He)|intro c].
      apply state_pure_bind; [exact IH|intro cs].
      apply state_pure_ret.
    Qed.

    Lemma generate_lvars_constraints_mono :
      forall dlt xs bs ts ts'' c c' s s' q q',
        Forall2 (fun t t'' => satisfiable dlt (fst t'') (merge amb (fst t)))
          ts ts'' ->
        Forall (fun b => satisfiable dlt amb [b]) bs ->
        listSatisfiable dlt (carried ts'') ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
          = OK (c, s') ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts'' q
          = OK (c', q') ->
        listSatisfiable dlt c ->
        listSatisfiable dlt c'.
    Proof.
      intros dlt xs. induction xs as [|x xs IH];
        intros bs ts ts'' c c' s s' q q' Hrel Hbs Hct H1 H2 Hsat.
      - simpl in H2. destruct bs; [|discriminate H2].
        destruct ts''; [|discriminate H2].
        unfold SC.ret in H2. inv H2. constructor.
      - destruct bs as [|b bs]; [simpl in H2; discriminate H2|].
        destruct ts as [|t ts];
          [inversion Hrel; subst; simpl in H2; discriminate H2|].
        inversion Hrel as [|t0 t0'' ts0 ts0'' Hr Hrelr]; subst.
        inversion Hbs as [|b0 bs0 Hb Hbsr]; subst.
        simpl in Hct. apply listSatisfiable_cmerge in Hct as (Hcth & Hctr).
        simpl in H1, H2.
        apply sec_bind_inv in H1 as (ckty1 & s1 & Hck1 & H1).
        apply sec_bind_inv in H1 as (rest1 & s2 & Hr1 & Hret1).
        unfold SC.ret in Hret1. inv Hret1.
        apply sec_bind_inv in H2 as (ckty2 & q1 & Hck2 & H2).
        apply sec_bind_inv in H2 as (rest2 & q2 & Hr2 & Hret2).
        unfold SC.ret in Hret2. inv Hret2.
        destruct (eqn_clock_type_pure x _ q _ _ Hck1) as (? & Hck1'); subst s1.
        rewrite Hck1' in Hck2. inv Hck2.
        apply listSatisfiable_app in Hsat as (Hsath & Hsatr).
        apply listSatisfiable_app. split.
        2: { exact (IH bs ts ts0'' rest1 rest2 s s' q1 q'
                      Hrelr Hbsr Hctr Hr1 Hr2 Hsatr). }
        apply lconstrain_sound in Hsath as (_ & Hle).
        apply lconstrain_sound. split.
        + unfold lst_defined. rewrite snd_ljoin.
          unfold ambient. rewrite snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hcth.
        + apply order_iff_satisfiable.
          apply order_iff_satisfiable in Hle.
          unfold lst_interp in *. rewrite fst_ljoin in *.
          assert (satisfiable dlt (fst t) [b]) as Htb
              by exact
                (satisfiable_through_merge_r dlt
                   (fst (ambient rst_ty ckty2)) (fst t) [b] Hle).
          exact (satisfiable_merge_intro dlt
                   (fst (ambient rst_ty ckty2)) (fst t0'') [b]
                   (satisfiable_through_merge_l dlt
                      (fst (ambient rst_ty ckty2)) (fst t) [b] Hle)
                   (satisfiable_trans dlt (fst t0'')
                      (merge amb (fst t)) [b] Hr
                      (satisfiable_merge_intro dlt amb (fst t) [b] Hb Htb))).
    Qed.

    (** The output-wise form needed by multi-stream expressions.  Each source
        and target type pair has its own ambient, and that same ambient is
        bounded by the corresponding equation output.  The scalar lemma
        above is the special case where [ambs] is a constant list. *)
    Lemma generate_lvars_constraints_mono_streams :
      forall dlt xs bs ambs ts ts'' c c' s s' q q',
        stream_rel dlt ambs ts ts'' ->
        stream_bounds dlt ambs bs ->
        listSatisfiable dlt (carried ts'') ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
          = OK (c, s') ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts'' q
          = OK (c', q') ->
        listSatisfiable dlt c ->
        listSatisfiable dlt c'.
    Proof.
      intros dlt xs. induction xs as [|x xs IH];
        intros bs ambs ts ts'' c c' s s' q q'
          Hrel Hbs Hct H1 H2 Hsat.
      all: unfold stream_rel in Hrel; unfold stream_bounds in Hbs.
      - simpl in H2. destruct bs; [|discriminate H2].
        destruct ts''; [|discriminate H2].
        unfold SC.ret in H2. inversion H2. constructor.
      - destruct bs as [|b bs]; [simpl in H2; discriminate H2|].
        destruct ambs as [|a ambs]; [inversion Hbs|].
        destruct ts as [|t ts]; [inversion Hrel|].
        inversion Hrel as
          [|a0 t0 t0'' ambs0 ts0 ts0'' Hr Hrelr]; subst.
        inversion Hbs as [|a0 b0 ambs0 bs0 Hb Hbsr]; subst.
        simpl in Hct.
        apply listSatisfiable_cmerge in Hct as (Hcth & Hctr).
        simpl in H1, H2.
        apply sec_bind_inv in H1 as (ckty1 & s1 & Hck1 & H1).
        apply sec_bind_inv in H1 as (rest1 & s2 & Hr1 & Hret1).
        unfold SC.ret in Hret1. inversion Hret1; subst.
        apply sec_bind_inv in H2 as (ckty2 & q1 & Hck2 & H2).
        apply sec_bind_inv in H2 as (rest2 & q2 & Hr2 & Hret2).
        unfold SC.ret in Hret2. inversion Hret2; subst.
        destruct (eqn_clock_type_pure x _ q _ _ Hck1)
          as (Hs1 & Hck1').
        subst s1. rewrite Hck1' in Hck2. inversion Hck2; subst.
        apply listSatisfiable_app in Hsat as (Hsath & Hsatr).
        apply listSatisfiable_app. split.
        + apply lconstrain_sound in Hsath as (Hdefined & Hle).
          apply lconstrain_sound. split.
          * unfold lst_defined. rewrite snd_ljoin.
            unfold ambient. rewrite snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2. exact Hcth.
          * apply order_iff_satisfiable.
            apply order_iff_satisfiable in Hle.
            unfold lst_interp in *. rewrite fst_ljoin in *.
            assert (satisfiable dlt (fst t) [b]) as Htb.
            { exact
                (satisfiable_through_merge_r dlt
                   (fst (ambient rst_ty ckty2)) (fst t) [b] Hle). }
            exact
              (satisfiable_merge_intro dlt
                 (fst (ambient rst_ty ckty2)) (fst t0'') [b]
                 (satisfiable_through_merge_l dlt
                    (fst (ambient rst_ty ckty2)) (fst t) [b] Hle)
                 (satisfiable_trans dlt (fst t0'')
                    (merge a (fst t)) [b] Hr
                    (satisfiable_merge_intro dlt a (fst t) [b]
                       Hb Htb))).
        + exact
            (IH bs ambs ts ts0'' rest1 rest2 s s' q1 q'
               Hrelr Hbsr Hctr Hr1 Hr2 Hsatr).
    Qed.

    (** The property the split needs of what a right-hand side comes back
        as: single-stream, not a call, and one type whatever state it is
        typed from.  The split cuts the right-hand side into one equation per
        stream, and each of those equations types its own expression at its
        own state. *)

    Definition rhs_pinned (e' : exp) (t : LST) : Prop :=
      (match e' with Eapp _ _ _ _ => False | _ => True end)
      /\ (forall tss s0 s0',
             assign_lexp_type GL env base_ty rst_ty e' s0 = OK (tss, s0') ->
             s0' = s0 /\ List.length tss = 1 /\ carried tss = [])
      /\ (forall tf s0 s0',
             assign_lexp_type GL env base_ty rst_ty e' s0 = OK ([tf], s0') ->
             tf = t).

    (** * The split, on the security side

        [split_equation] cuts an unnested right-hand side into one equation
        per group of streams.  Away from calls every returned expression is
        single-stream, so every group is one variable and every piece is a
        definition -- and the constraint the definition rule emits for it is,
        term for term, the one the general rule would have put at that
        position.  So the whole split generates exactly what
        [generate_lvars_constraints] does, and the previous lemma applies to
        it unchanged. *)

    Lemma split_equation_nil : split_equation ([], []) = [].
    Proof. reflexivity. Qed.

    Lemma split_equation_cons :
      forall x xs e es,
        numstreams e = 1 ->
        split_equation (x :: xs, e :: es)
        = ([x], [e]) :: split_equation (xs, es).
    Proof.
      intros x xs e es Hn. unfold split_equation.
      cbn [combine_for_numstreams]. rewrite Hn.
      cbn [firstn skipn List.map]. reflexivity.
    Qed.

    Lemma split_equation_is_lvars :
      forall (xs : list ident) (es' : list exp) bs ts'' c s s' q,
        Forall (fun e => numstreams e = 1) es' ->
        Forall2 (fun x b => Env.find x env = Some b) xs bs ->
        Forall2 rhs_pinned es' ts'' ->
        List.length xs = List.length es' ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (split_equation (xs, es')) s = OK (c, s') ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts'' q
          = OK (c, q).
    Proof.
      induction xs as [|x xs IH];
        intros es' bs ts'' c s s' q Hns Hbs Hts Hlen Hgen.
      - destruct es'; simpl in Hlen; [|discriminate Hlen].
        inv Hbs. inv Hts.
        rewrite split_equation_nil in Hgen.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        reflexivity.
      - destruct es' as [|e es']; simpl in Hlen; [discriminate Hlen|].
        inversion Hns as [|e0 es0 Hn1 Hnsr]; subst.
        inversion Hbs as [|x0 b xs0 bs0 Hxb Hbsr]; subst.
        inversion Hts as [|e2 t es2 ts2 (He1 & Hpur & Hpin) Htsr]; subst.
        rewrite split_equation_cons in Hgen by exact Hn1.
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (ch & sh & Hch & Hgen).
        apply sec_bind_inv in Hgen as (ct & stt & Hct & Hret).
        unfold SC.ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hch by exact He1.
        unfold generate_ldef_constraint in Hch.
        apply sec_bind_inv in Hch as (ckty & s1 & Hck & Hch).
        apply sec_bind_inv in Hch as (tss & s2 & Htss & Hch).
        apply sec_bind_inv in Hch as (tt & s3 & Htt & Hch).
        apply sec_bind_inv in Hch as (b' & s4 & Hb' & Hretc).
        unfold SC.ret in Hretc. inv Hretc.
        destruct (Hpur _ _ _ Htss) as (? & Hlt & _); subst s2.
        destruct tss as [|t0 [|]]; simpl in Hlt; try discriminate.
        assert (t0 = t) as ? by exact (Hpin t0 s1 s1 Htss); subst t0.
        apply single_inv in Htt as (Htt & ?); subst.
        inv Htt.
        apply find_env_inv in Hb' as (Hb'' & ?); subst.
        rewrite Hxb in Hb''. inv Hb''.
        simpl.
        assert (List.length xs = List.length es') as Hlenr
          by now injection Hlen.
        destruct (eqn_clock_type_pure x s q ckty s1 Hck)
          as (Hs1 & Hckq). subst s1.
        assert (generate_lvars_constraints env base_ty rst_ty cenv
                  xs bs0 ts2 q = OK (ct, q)) as Htail'
          by exact (IH es' bs0 ts2 ct s s' q
                      Hnsr Hbsr Htsr Hlenr Hct).
        erewrite bind_OK by exact Hckq.
        erewrite bind_OK by exact Htail'.
        reflexivity.
    Qed.

    (** * Right-hand side lists

        The list level of [rhs_carries], for the [map_bind2] inside
        [unnest_rhss].  The same composition as [carries_list_intro], with
        the two extra conclusions riding along: what the head and the tail
        return carry is the merge of the two, so both the satisfaction and
        the scoping split with the list. *)

    Lemma map_bind2_unnest_rhs_cons :
      forall P e es es' eqs st st',
        map_bind2 (unnest_rhs P) (e :: es) st = ((es', eqs), st') ->
        exists e' eq1 st1 es'r eqsr,
          unnest_rhs P e st = ((e', eq1), st1)
          /\ map_bind2 (unnest_rhs P) es st1 = ((es'r, eqsr), st')
          /\ es' = e' :: es'r
          /\ eqs = eq1 :: eqsr.
    Proof.
      intros P e es es' eqs st st' H.
      simpl in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma map_bind2_unnest_rhs_nil :
      forall P es' eqs st st',
        map_bind2 (unnest_rhs P) [] st = ((es', eqs), st') ->
        es' = [] /\ eqs = [] /\ st' = st.
    Proof.
      intros P es' eqs st st' H. simpl in H.
      rewrite ret_spec in H. inv H. repeat split.
    Qed.

    Lemma map_bind2_unnest_rhs_st_follows :
      forall P es es' eqs st st',
        map_bind2 (unnest_rhs P) es st = ((es', eqs), st') ->
        st_follows st st'.
    Proof.
      intros P es es' eqs st st' H.
      assert (Forall
                (fun e => forall e' eqs0 st0 st1,
                   unnest_rhs P e st0 = ((e', eqs0), st1) ->
                   st_follows st0 st1) es) as Hfollows.
      { rewrite Forall_forall.
        intros e Hin e' eqs0 st0 st1 He.
        exact (unnest_rhs_st_follows P e (e', eqs0) st0 st1 He). }
      exact (@map_bind2_st_follows exp (list exp) (list equation) (type * clock)
               (unnest_rhs P) es es' eqs st st' H Hfollows).
    Qed.

    Definition rhs_carries_list (P : global) (es : list exp) : Prop :=
      forall es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        Forall (wl_exp P) es ->
        Forall (wc_exp P vars) es ->
        NoDup (vars_defined (List.concat eqs) ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        (forall x ck ckty,
            In x (vars_defined (List.concat eqs)) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        map_bind2 (unnest_rhs P) es st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.concat eqs) xst = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty (List.concat es') yst
          = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ listSatisfiable dlt' (carried ts'')
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ constraints_scoped (scope ++ moved_by st st') (carried ts'')
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    Lemma rhs_carries_list_intro :
      forall P es, Forall (rhs_carries P) es -> rhs_carries_list P es.
    Proof.
      intros P es Hall.
      induction Hall as [|e es IHe IHes IH];
        intros es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
          Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.

      - apply map_bind2_unnest_rhs_nil in Hun as (? & ? & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has'
          as (? & Hc0 & ?); subst.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. rewrite Hc0.
        split; [|split; [|split; [|split; [|split; [|split]]]]];
          solve [apply agree_off_refl | constructor].

      - inversion Hwl as [|e0 es0 Hwle Hwlrest]; subst.
        inversion Hwc as [|e0 es0 Hwce Hwcrest]; subst.
        apply map_bind2_unnest_rhs_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        assert (st_follows st st1) as Hf1
            by exact (unnest_rhs_st_follows P e (f1, eq1) st st1 Hun1).
        assert (st_follows st1 st') as Hf2
            by exact
              (map_bind2_unnest_rhs_st_follows P es fr eqsr st1 st' Hunr).

        apply assign_lexps_carried_cons in Has
          as (t & r & sa & Ht & Hr & ? & Hcts); subst.
        simpl in Has'.
        apply assign_lexps_app_inv in Has'
          as (u & v & ya & Hu & Hv & ?); subst.
        simpl in Hgen.
        apply generate_leqns_constraints_app in Hgen
          as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

        rewrite Hcts in Hsc, Hcar.
        apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
        apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
        apply Forall_app in Hsts as (Hsts1 & Hsts2).

        assert (Permutation (vars_defined eq1 ++ st_ids st) (st_ids st1)) as Hp1
            by exact
              (unnest_rhs_vars_perm P e f1 eq1 st st1 Hwle Hun1).
        edestruct (IHe f1 eq1 st st1 t sst sa ce1 xst xst1 u yst ya dlt)
          as (dlt1 & Hoff1 & Hce1 & Hcy1 & Hrel1 & Hscope1 & Hcs1 & Hts1).
        { exact Hwle. }
        { exact Hwce. }
        { exact (NoDup_vd_app_l eq1 (List.concat eqsr) (st_ids st) Hnd). }
        { intros x Hx.
          exact (Hmv x (eq_moved_by_prefix st st1 st' Hf2 x Hx)). }
        { exact Hsc1. }
        { exact Hsts1. }
        { intros y cky ckty Hy.
          exact (Hamb y cky ckty
                   (vars_defined_incl_l eq1 (List.concat eqsr) y Hy)). }
        { exact Hun1. }
        { exact Ht. }
        { exact Hgen1. }
        { exact Hu. }
        { exact Hcar1. }

        edestruct (IH fr eqsr st1 st' r sa sst' ce2 xst1 xst' v ya yst' dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hcy2 & Hrel2 & Hscope2 & Hcs2 & Hts2).
        { exact Hwlrest. }
        { exact Hwcrest. }
        { exact (NoDup_vd_app_r eq1 (List.concat eqsr)
                   (st_ids st) (st_ids st1) Hp1 Hnd). }
        { intros x Hx.
          exact (Hmv x (eq_moved_by_suffix st st1 st' Hf1 x Hx)). }
        { exact Hsc2. }
        { exact Hsts2. }
        { intros y cky ckty Hy.
          exact (Hamb y cky ckty
                   (vars_defined_incl_r eq1 (List.concat eqsr) y Hy)). }
        { exact Hunr. }
        { exact Hr. }
        { exact Hgen2. }
        { exact Hv. }
        { exact (listSatisfiable_off scope (carried r) (moved_by st st1)
                   dlt dlt1 Hsc2
                   (fun x Hx =>
                      Hmv x (eq_moved_by_prefix st st1 st' Hf2 x Hx))
                   Hoff1 Hcar2). }

        assert (forall x, In x (moved_by st1 st') ->
                          ~ In x (scope ++ moved_by st st1)) as Hsep.
        { intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
          - apply (Hmv x); [|exact Hx].
            apply (eq_moved_by_suffix st st1 st' Hf1). exact Hin.
          - exact (eq_moved_by_disjoint st st1 st' x Hx Hin). }
        assert (incl (scope ++ moved_by st st1)
                     (scope ++ moved_by st st')) as Hinc1.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_prefix st st1 st' Hf2). }
        assert (incl (scope ++ moved_by st1 st')
                     (scope ++ moved_by st st')) as Hinc2.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_suffix st st1 st' Hf1). }

        exists dlt2.
        split; [|split; [|split; [|split; [|split; [|split]]]]].
        + exact (agree_off_trans (moved_by st st') dlt dlt1 dlt2
                   (agree_off_incl (moved_by st st1) (moved_by st st')
                      dlt dlt1 (eq_moved_by_prefix st st1 st' Hf2) Hoff1)
                   (agree_off_incl (moved_by st1 st') (moved_by st st')
                      dlt1 dlt2 (eq_moved_by_suffix st st1 st' Hf1) Hoff2)).
        + apply listSatisfiable_app. split; [|exact Hce2].
          exact (listSatisfiable_off_scope ce1
                   (scope ++ moved_by st st1) (moved_by st1 st') dlt1 dlt2
                   Hscope1 Hsep Hoff2 Hce1).
        + rewrite carried_app. apply listSatisfiable_cmerge. split; [|exact Hcy2].
          exact (listSatisfiable_off_scope (carried u)
                   (scope ++ moved_by st st1) (moved_by st1 st') dlt1 dlt2
                   Hcs1 Hsep Hoff2 Hcy1).
        + apply Forall2_app; [|exact Hrel2].
          assert (forall p q, In p t -> In q u ->
                    satisfiable dlt1 (fst q) (merge amb (fst p)) ->
                    satisfiable dlt2 (fst q) (merge amb (fst p)))
            as Hrel12.
          { intros p q Hp Hq Hpq.
            assert (forall x, In x (fst q) -> ~ In x (moved_by st1 st'))
              as Hqoff.
            { intros x Hx Hin.
              rewrite Forall_forall in Hts1.
              exact (Hsep x Hin (Hts1 q Hq x Hx)). }
            assert (forall x, In x (merge amb (fst p)) ->
                       ~ In x (moved_by st1 st')) as Hpoff.
            { intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
              - exact (Hsep x Hin (in_or_app _ _ x (or_introl (amb_scoped x Hx)))).
              - rewrite Forall_forall in Hsts1.
                exact (Hsep x Hin
                         (in_or_app _ _ x (or_introl (Hsts1 p Hp x Hx)))). }
            exact (satisfiable_off (fst q) (merge amb (fst p))
                     (moved_by st1 st') dlt1 dlt2 Hoff2 Hqoff Hpoff Hpq). }
          exact (@Forall2_impl_In LST LST
                   (fun p q => satisfiable dlt1 (fst q) (merge amb (fst p)))
                   (fun p q => satisfiable dlt2 (fst q) (merge amb (fst p)))
                   t u Hrel12 Hrel1).
        + apply Forall_app. split.
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st st1))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st st1) (scope ++ moved_by st st')
                        c Hinc1 Hc) ce1 Hscope1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st1 st'))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st1 st') (scope ++ moved_by st st')
                        c Hinc2 Hc) ce2 Hscope2).
        + rewrite carried_app. apply constraints_scoped_cmerge. split.
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st st1))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st st1) (scope ++ moved_by st st')
                        c Hinc1 Hc) (carried u) Hcs1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st1 st'))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st1 st') (scope ++ moved_by st st')
                        c Hinc2 Hc) (carried v) Hcs2).
        + apply Forall_app. split.
          * exact (@Forall_impl LST
                     (fun q => st_scoped (scope ++ moved_by st st1) (fst q))
                     (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                     (fun q Hq => st_scoped_weaken
                        (scope ++ moved_by st st1) (scope ++ moved_by st st')
                        (fst q) Hinc1 Hq) u Hts1).
          * exact (@Forall_impl LST
                     (fun q => st_scoped (scope ++ moved_by st1 st') (fst q))
                     (fun q => st_scoped (scope ++ moved_by st st') (fst q))
                     (fun q Hq => st_scoped_weaken
                        (scope ++ moved_by st1 st') (scope ++ moved_by st st')
                        (fst q) Hinc2 Hq) v Hts2).
    Qed.

    (** * Both source rules, in one shape

        Away from calls the equation generator has two rules -- the
        definition rule for a single variable defined by a single expression,
        and the general rule for everything else -- and they differ only in
        that the first is the second's one-element case with the empty tail
        already appended.  Reducing both to [generate_lvars_constraints] is
        what lets the split and the source be compared by one lemma. *)

    Lemma generate_leqn_constraint_gen :
      forall xs es,
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False
                         | _ => True
                         end) es ->
        (match es with
         | [_] => match xs with [_] => False | _ => True end
         | _ => True
         end) ->
        generate_leqn_constraint GL env base_ty rst_ty cenv (xs, es)
        = generate_lgen_constraint GL env base_ty rst_ty cenv xs es.
    Proof.
      intros xs es Hne Hsh.
      destruct es as [|e [|e2 es2]].
      - reflexivity.
      - inv Hne. destruct e; try contradiction;
          (destruct xs as [|x [|x2 xs2]];
           [reflexivity|contradiction|reflexivity]).
      - rewrite gen_leqn_cons2, (has_lcall_false _ Hne). reflexivity.
    Qed.

    Lemma generate_lgen_constraint_inv :
      forall xs es c s s',
        generate_lgen_constraint GL env base_ty rst_ty cenv xs es s
          = OK (c, s') ->
        exists ts bs si,
          assign_lexps GL env base_ty rst_ty es s = OK (ts, si)
          /\ get_mappings xs env = Some bs
          /\ generate_lvars_constraints env base_ty rst_ty cenv xs bs ts si
             = OK (c, s').
    Proof.
      intros xs es c s s' H. unfold generate_lgen_constraint in H.
      apply sec_bind_inv in H as (ts & si & Hts & H).
      apply sec_bind_inv in H as (bs & sj & Hbs & H).
      apply option_to_sec_inv in Hbs as (Hbs & ?); subst sj.
      exists ts, bs, si. auto.
    Qed.

    Lemma generate_ldef_is_lvars :
      forall x e b t c s s' si,
        Env.find x env = Some b ->
        assign_lexp_type GL env base_ty rst_ty e s = OK ([t], si) ->
        generate_ldef_constraint GL env base_ty rst_ty cenv x e s
          = OK (c, s') ->
        generate_lvars_constraints env base_ty rst_ty cenv [x] [b] [t] si
          = OK (c, s').
    Proof.
      intros x e b t c s s' si Hb Hte H.
      unfold generate_ldef_constraint in H.
      apply sec_bind_inv in H as (ckty & s1 & Hck & H).
      apply sec_bind_inv in H as (tss & s2 & Htss & H).
      apply sec_bind_inv in H as (tt & s3 & Htt & H).
      apply sec_bind_inv in H as (b' & s4 & Hb' & Hret).
      unfold SC.ret in Hret. inv Hret.
      destruct (eqn_clock_type_pure x _ si _ _ Hck) as (? & Hck'); subst s1.
      rewrite Hte in Htss. inv Htss.
      apply single_inv in Htt as (Htt & ?); subst. inv Htt.
      apply find_env_inv in Hb' as (Hb'' & ?); subst.
      rewrite Hb in Hb''. inv Hb''.
      simpl. erewrite bind_OK by exact Hck'.
      erewrite bind_OK by reflexivity.
      unfold SC.ret. now rewrite app_nil_r.
    Qed.

    Lemma generate_leqn_constraint_lvars :
      forall xs es c s s',
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False
                         | _ => True
                         end) es ->
        generate_leqn_constraint GL env base_ty rst_ty cenv (xs, es) s
          = OK (c, s') ->
        exists ts bs si,
          assign_lexps GL env base_ty rst_ty es s = OK (ts, si)
          /\ get_mappings xs env = Some bs
          /\ generate_lvars_constraints env base_ty rst_ty cenv xs bs ts si
             = OK (c, s').
    Proof.
      intros xs es c s s' Hne H.
      destruct es as [|e [|e2 es2]].
      - rewrite generate_leqn_constraint_gen in H by (assumption || exact I).
        now apply generate_lgen_constraint_inv.
      - destruct xs as [|x [|x2 xs2]].
        + rewrite generate_leqn_constraint_gen in H by (assumption || exact I).
          now apply generate_lgen_constraint_inv.
        + inversion Hne as [|e0 es0 He1 _]; subst.
          rewrite generate_leqn_constraint_def in H by exact He1.
          pose proof H as H0.
          apply generate_ldef_constraint_inv in H0
            as (ck & ckty & t & bb & si & Hck & Hcl & Hte & Hb & Hc).
          exists [t], [bb], si. split; [|split].
          * apply assign_lexps_single_intro. exact Hte.
          * simpl. now rewrite Hb.
          * exact (generate_ldef_is_lvars x e bb t c s s' si Hb Hte H).
        + rewrite generate_leqn_constraint_gen in H by (assumption || exact I).
          now apply generate_lgen_constraint_inv.
      - rewrite generate_leqn_constraint_gen in H by (assumption || exact I).
        now apply generate_lgen_constraint_inv.
    Qed.

    (** * What a right-hand side comes back as

        Away from calls, every expression [unnest_rhs] returns is
        single-stream and has one type, whatever state it is typed from.
        That is what the split needs: it cuts the right-hand side into one
        equation per stream, and each of those equations types its own
        expression at its own state. *)

    Lemma unnest_fby_numstreams :
      forall e0s es anns,
        Forall (fun e => numstreams e = 1) (unnest_fby e0s es anns).
    Proof.
      intros e0s es anns. unfold unnest_fby.
      rewrite Forall_map. apply Forall_forall.
      intros ((e0 & e) & a) _. reflexivity.
    Qed.

    Lemma unnest_arrow_numstreams :
      forall e0s es anns,
        Forall (fun e => numstreams e = 1) (unnest_arrow e0s es anns).
    Proof.
      intros e0s es anns. unfold unnest_arrow.
      rewrite Forall_map. apply Forall_forall.
      intros ((e0 & e) & a) _. reflexivity.
    Qed.

    Lemma normalized_cexp_pinned :
      forall (es' : list exp) ts'' q q',
        Forall normalized_cexp es' ->
        assign_lexps GL env base_ty rst_ty es' q = OK (ts'', q') ->
        Forall2 rhs_pinned es' ts''.
    Proof.
      intros es' ts'' q q' Hn H.
      assert (Forall2 (fun e t =>
                (forall s, assign_lexp_type GL env base_ty rst_ty e s
                            = OK ([t], s)) /\ snd t = []) es' ts'') as Hew
          by exact
            (assign_lexps_elementwise_local es' ts'' q q' Hn H).
      apply (@Forall2_impl_In exp LST
               (fun e t =>
                  (forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK ([t], s)) /\ snd t = [])
               rhs_pinned es' ts''); [|exact Hew].
      intros e t He Ht (Hs & Hsnd).
      assert (normalized_cexp e) as Hne
          by (rewrite Forall_forall in Hn; exact (Hn e He)).
      split; [destruct e; try exact I; inv Hne; inv H0|split].
      - intros tss s0 s0' Hty. rewrite (Hs s0) in Hty. inv Hty.
        split; [reflexivity|split; [reflexivity|]].
        rewrite carried_single. exact Hsnd.
      - intros tf s0 s0' Hty. rewrite (Hs s0) in Hty. now inv Hty.
    Qed.

    Lemma unnest_rhs_pinned :
      forall P e es' eqs st st' ts'' q q',
        wl_exp P e ->
        (match e with Eapp _ _ _ _ => False | _ => True end) ->
        unnest_rhs P e st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es' q = OK (ts'', q') ->
        Forall (fun e' => numstreams e' = 1) es'
        /\ Forall2 rhs_pinned es' ts''.
    Proof.
      intros P e es' eqs st st' ts'' q q' Hwl He Hun Has.
      destruct e; try
        (rewrite unnest_rhs_other in Hun by exact I;
         assert (Forall normalized_cexp es') as Hnc
             by (match type of Hun with
                 | unnest_exp ?P0 true ?e0 ?st0 = (?es0, ?eqs0, ?st1) =>
                     exact (unnest_exp_normalized_cexp
                              P0 e0 es0 eqs0 st0 st1 Hun)
                 end);
         split;
         [match type of Hun with
          | unnest_exp ?P0 true ?e0 ?st0 = (?es0, ?eqs0, ?st1) =>
              exact (unnest_exp_numstreams
                       P0 e0 true es0 eqs0 st0 st1 Hun)
          end
         |exact (normalized_cexp_pinned es' ts'' q q' Hnc Has)]).
      - (** the delay *)
        inv Hwl.
        apply unnest_rhs_Efby_inv in Hun
          as (f0 & eqsa & st1 & f1 & eqsb & Hun0 & Hun1 & ? & ?); subst.
        apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
        apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
        assert (Forall normalized_lexp (List.concat ess0)) as Hn0
            by exact
              (map_bind2_unnest_normalized_lexp
                 P l ess0 eqss0 st st1 Hmap0).
        assert (Forall normalized_lexp (List.concat ess1)) as Hn1
            by exact
              (map_bind2_unnest_normalized_lexp
                 P l0 ess1 eqss1 st1 st' Hmap1).
        assert (Forall normalized_cexp (List.concat ess0)) as Hc0
            by exact (@Forall_impl exp normalized_lexp normalized_cexp
                        normalized_lexp_cexp (List.concat ess0) Hn0).
        assert (Forall normalized_cexp (List.concat ess1)) as Hc1
            by exact (@Forall_impl exp normalized_lexp normalized_cexp
                        normalized_lexp_cexp (List.concat ess1) Hn1).
        assert (List.length (List.concat ess0) = List.length l1) as Hle0
            by (erewrite map_bind2_unnest_exp_length with (es := l); eauto).
        assert (List.length (List.concat ess1) = List.length l1) as Hle1
            by (erewrite map_bind2_unnest_exp_length with (es := l0); eauto).
        edestruct (unnest_fby_operands_typed (List.concat ess0)
                     (List.concat ess1) l1 ts'' q q')
          as (ts0x & usx & Ht0x & Hux);
          [exact Hc0|exact Hc1|exact Hle0|exact Hle1|exact Has|].
        edestruct (unnest_fby_types_local (List.concat ess0) (List.concat ess1) l1
                     ts0x usx q) as (rs & Hjr & Hallr);
          [exact (assign_lexps_elementwise_local
                    (List.concat ess0) ts0x q q Hc0 (Ht0x q))
          |exact (assign_lexps_elementwise_local
                    (List.concat ess1) usx q q Hc1 (Hux q))
          |exact Hle0|exact Hle1|].
        assert (ts'' = rs /\ q' = q) as (? & ?)
            by exact (assign_lexps_determined
                        (unnest_fby (List.concat ess0) (List.concat ess1) l1)
                        rs q ts'' q' Hallr Has); subst.
        split; [apply unnest_fby_numstreams|exact Hallr].
      - (** the initialised delay *)
        inv Hwl.
        apply unnest_rhs_Earrow_inv in Hun
          as (f0 & eqsa & st1 & f1 & eqsb & Hun0 & Hun1 & ? & ?); subst.
        apply unnest_exps_inv in Hun0 as (ess0 & eqss0 & Hmap0 & ? & ?); subst.
        apply unnest_exps_inv in Hun1 as (ess1 & eqss1 & Hmap1 & ? & ?); subst.
        assert (Forall normalized_lexp (List.concat ess0)) as Hn0
            by exact
              (map_bind2_unnest_normalized_lexp
                 P l ess0 eqss0 st st1 Hmap0).
        assert (Forall normalized_lexp (List.concat ess1)) as Hn1
            by exact
              (map_bind2_unnest_normalized_lexp
                 P l0 ess1 eqss1 st1 st' Hmap1).
        assert (Forall normalized_cexp (List.concat ess0)) as Hc0
            by exact (@Forall_impl exp normalized_lexp normalized_cexp
                        normalized_lexp_cexp (List.concat ess0) Hn0).
        assert (Forall normalized_cexp (List.concat ess1)) as Hc1
            by exact (@Forall_impl exp normalized_lexp normalized_cexp
                        normalized_lexp_cexp (List.concat ess1) Hn1).
        assert (List.length (List.concat ess0) = List.length l1) as Hle0
            by (erewrite map_bind2_unnest_exp_length with (es := l); eauto).
        assert (List.length (List.concat ess1) = List.length l1) as Hle1
            by (erewrite map_bind2_unnest_exp_length with (es := l0); eauto).
        edestruct (unnest_arrow_operands_typed (List.concat ess0)
                     (List.concat ess1) l1 ts'' q q')
          as (ts0x & usx & Ht0x & Hux);
          [exact Hc0|exact Hc1|exact Hle0|exact Hle1|exact Has|].
        edestruct (unnest_arrow_types_local (List.concat ess0) (List.concat ess1) l1
                     ts0x usx q) as (rs & Hjr & Hallr);
          [exact (assign_lexps_elementwise_local
                    (List.concat ess0) ts0x q q Hc0 (Ht0x q))
          |exact (assign_lexps_elementwise_local
                    (List.concat ess1) usx q q Hc1 (Hux q))
          |exact Hle0|exact Hle1|].
        assert (ts'' = rs /\ q' = q) as (? & ?)
            by exact (assign_lexps_determined
                        (unnest_arrow (List.concat ess0) (List.concat ess1) l1)
                        rs q ts'' q' Hallr Has); subst.
        split; [apply unnest_arrow_numstreams|exact Hallr].
      - contradiction.
    Qed.

    Lemma unnest_rhss_pinned :
      forall P es ess eqss st st' ts'' q q',
        Forall (wl_exp P) es ->
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False
                         | _ => True
                         end) es ->
        map_bind2 (unnest_rhs P) es st = ((ess, eqss), st') ->
        assign_lexps GL env base_ty rst_ty (List.concat ess) q
          = OK (ts'', q') ->
        Forall (fun e' => numstreams e' = 1) (List.concat ess)
        /\ Forall2 rhs_pinned (List.concat ess) ts''.
    Proof.
      induction es as [|e es IH];
        intros ess eqss st st' ts'' q q' Hwl Hne Hun Has.
      - apply map_bind2_unnest_rhs_nil in Hun as (? & ? & ?); subst.
        simpl in Has.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        split; constructor.
      - inv Hwl. inv Hne.
        apply map_bind2_unnest_rhs_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        simpl in Has.
        apply assign_lexps_app_inv in Has as (u & v & ya & Hu & Hv & ?); subst.
        edestruct (unnest_rhs_pinned P e f1 eq1 st st1 u q ya)
          as (Hns1 & Hp1); try assumption.
        edestruct (IH fr eqsr st1 st' v ya q') as (Hns2 & Hp2); try assumption.
        split; [apply Forall_app; auto|apply Forall2_app; auto].
    Qed.

    (** * Reading the general rule apart

        Three facts about [generate_lvars_constraints], all by the same
        induction: what it releases of the right-hand side's own obligations,
        what its constraints can name, and -- for the split -- that the types
        it was given exist in the first place. *)

    Lemma generate_lvars_constraints_carried :
      forall dlt xs bs ts c s s',
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
          = OK (c, s') ->
        listSatisfiable dlt c ->
        listSatisfiable dlt (carried ts).
    Proof.
      intros dlt xs. induction xs as [|x xs IH];
        intros bs ts c s s' H Hsat.
      - simpl in H. destruct bs; [|discriminate H].
        destruct ts; [|discriminate H]. constructor.
      - destruct bs as [|b bs]; [simpl in H; discriminate H|].
        destruct ts as [|t ts]; [simpl in H; discriminate H|].
        simpl in H.
        apply sec_bind_inv in H as (ckty & s1 & Hck & H).
        apply sec_bind_inv in H as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret. inv Hret.
        apply listSatisfiable_app in Hsat as (Hsath & Hsatr).
        apply lconstrain_sound in Hsath as (Hdef & _).
        simpl. apply listSatisfiable_cmerge. split.
        2: { exact (IH bs ts rest s1 s' Hr Hsatr). }
        unfold lst_defined in Hdef. rewrite snd_ljoin in Hdef.
        unfold ambient in Hdef. rewrite snd_ljoin, snd_lvar in Hdef.
        cbn [snd] in Hdef. rewrite cmerge_nil, cmerge_nil2 in Hdef.
        exact Hdef.
    Qed.

    Lemma generate_lvars_constraints_scoped :
      forall sc xs bs ts c s s',
        In rst_ty sc ->
        (forall ck ckty,
            assign_clk_type env base_ty ck = Some ckty -> st_scoped sc ckty) ->
        Forall (fun b => In b sc) bs ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        constraints_scoped sc (carried ts) ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts s
          = OK (c, s') ->
        constraints_scoped sc c.
    Proof.
      intros sc xs. induction xs as [|x xs IH];
        intros bs ts c s s' Hrst Hclk Hbs Hts Hct H.
      - simpl in H. destruct bs; [|discriminate H].
        destruct ts; [|discriminate H].
        unfold SC.ret in H. inv H. constructor.
      - destruct bs as [|b bs]; [simpl in H; discriminate H|].
        destruct ts as [|t ts]; [simpl in H; discriminate H|].
        inversion Hbs as [|b0 bs0 Hb Hbsr]; subst.
        inversion Hts as [|t0 ts0 Ht Htsr]; subst.
        simpl in Hct. apply constraints_scoped_cmerge in Hct as (Hcth & Hctr).
        simpl in H.
        apply sec_bind_inv in H as (ckty & s1 & Hck & H).
        apply sec_bind_inv in H as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret. inv Hret.
        assert (st_scoped sc ckty) as Hcksc.
        { unfold eqn_clock_type in Hck.
          apply sec_bind_inv in Hck as (ck0 & sa & Hck0 & Hck).
          apply option_to_sec_inv in Hck as (Hck & ?); subst.
          exact (Hclk ck0 ckty Hck). }
        apply Forall_app. split.
        2: { exact (IH bs ts rest s1 s' Hrst Hclk Hbsr Htsr Hctr Hr). }
        unfold lconstrain. apply constraints_scoped_cmerge. split.
        + constructor; [|constructor].
          intros y Hy. apply in_app_or in Hy as [Hy|Hy].
          * rewrite fst_ljoin in Hy. apply in_merge_inv in Hy as [Hy|Hy].
            -- unfold ambient in Hy. rewrite fst_ljoin, fst_lvar in Hy.
               apply in_merge_inv in Hy as [Hy|Hy].
               ++ destruct Hy as [Hy|[]]; subst y. exact Hrst.
               ++ now apply Hcksc.
            -- now apply Ht.
          * destruct Hy as [Hy|[]]; subst y. exact Hb.
        + rewrite snd_ljoin. unfold ambient.
          rewrite snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hcth.
    Qed.

    Lemma vars_defined_split_equation :
      forall (xs : list ident) (es' : list exp),
        Forall (fun e => numstreams e = 1) es' ->
        List.length xs = List.length es' ->
        vars_defined (split_equation (xs, es')) = xs.
    Proof.
      induction xs as [|x xs IH]; intros es' Hns Hlen.
      - destruct es'; simpl in Hlen; [|discriminate Hlen].
        reflexivity.
      - destruct es' as [|e es']; simpl in Hlen; [discriminate Hlen|].
        inversion Hns as [|e0 es0 Hn1 Hnsr]; subst.
        rewrite split_equation_cons by exact Hn1.
        replace (vars_defined (([x], [e]) :: split_equation (xs, es')))
          with (x :: vars_defined (split_equation (xs, es'))) by reflexivity.
        f_equal. apply IH; auto.
    Qed.

    Lemma split_equation_operand_types :
      forall (xs : list ident) (es' : list exp) c s s',
        Forall (fun e => numstreams e = 1) es' ->
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False
                         | _ => True
                         end) es' ->
        List.length xs = List.length es' ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (split_equation (xs, es')) s = OK (c, s') ->
        exists ts'' q', assign_lexps GL env base_ty rst_ty es' s = OK (ts'', q').
    Proof.
      induction xs as [|x xs IH]; intros es' c s s' Hns Hne Hlen Hgen.
      - destruct es'; simpl in Hlen; [|discriminate Hlen].
        exists [], s. now rewrite assign_lexps_nil.
      - destruct es' as [|e es']; simpl in Hlen; [discriminate Hlen|].
        inversion Hns as [|e0 es0 Hn1 Hnsr]; subst.
        inversion Hne as [|e1 es1 He1 Hner]; subst.
        rewrite split_equation_cons in Hgen by exact Hn1.
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (ch & sh & Hch & Hgen).
        apply sec_bind_inv in Hgen as (ct & stt & Hct & _).
        rewrite generate_leqn_constraint_def in Hch by exact He1.
        pose proof Hch as Hch0.
        apply generate_ldef_constraint_inv in Hch0
          as (ck & ckty & t & bb & si & _ & _ & Hte & _ & Hc).
        destruct Hc as (? & _); subst sh.
        edestruct (IH es' ct si stt) as (ts0 & q0 & Hts0); auto.
        exists ([t] ++ ts0), q0. rewrite assign_lexps_cons.
        erewrite bind_OK by exact Hte.
        erewrite bind_OK by exact Hts0. reflexivity.
    Qed.

    (** The shape facts, which need no types and so can be established before
        them -- otherwise the split's operand types and the pinning would
        each be waiting on the other. *)

    Lemma normalized_cexp_not_app :
      forall e, normalized_cexp e ->
        match e with Eapp _ _ _ _ => False | _ => True end.
    Proof. intros e H. destruct e; try exact I; inv H; inv H0. Qed.

    Lemma unnest_fby_not_app :
      forall e0s es anns,
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False | _ => True end)
          (unnest_fby e0s es anns).
    Proof.
      intros e0s es anns. unfold unnest_fby.
      rewrite Forall_map. apply Forall_forall.
      intros ((e0 & e) & a) _. exact I.
    Qed.

    Lemma unnest_arrow_not_app :
      forall e0s es anns,
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False | _ => True end)
          (unnest_arrow e0s es anns).
    Proof.
      intros e0s es anns. unfold unnest_arrow.
      rewrite Forall_map. apply Forall_forall.
      intros ((e0 & e) & a) _. exact I.
    Qed.

    Lemma unnest_rhs_shape :
      forall P e es' eqs st st',
        wl_exp P e ->
        (match e with Eapp _ _ _ _ => False | _ => True end) ->
        unnest_rhs P e st = ((es', eqs), st') ->
        Forall (fun e' => numstreams e' = 1) es'
        /\ Forall (fun e' => match e' with
                             | Eapp _ _ _ _ => False | _ => True end) es'.
    Proof.
      intros P e es' eqs st st' Hwl He Hun.
      destruct e; try
        (rewrite unnest_rhs_other in Hun by exact I;
         assert (Forall normalized_cexp es') as Hnc
             by (match type of Hun with
                 | unnest_exp ?P0 true ?e0 ?st0 = (?es0, ?eqs0, ?st1) =>
                     exact (unnest_exp_normalized_cexp
                              P0 e0 es0 eqs0 st0 st1 Hun)
                 end);
         split;
         [match type of Hun with
          | unnest_exp ?P0 true ?e0 ?st0 = (?es0, ?eqs0, ?st1) =>
              exact (unnest_exp_numstreams
                       P0 e0 true es0 eqs0 st0 st1 Hun)
          end
         |exact (@Forall_impl exp normalized_cexp
                   (fun e' => match e' with
                              | Eapp _ _ _ _ => False | _ => True end)
                   normalized_cexp_not_app es' Hnc)]).
      - apply unnest_rhs_Efby_inv in Hun
          as (f0 & eqsa & st1 & f1 & eqsb & _ & _ & ? & _); subst.
        split; [apply unnest_fby_numstreams|apply unnest_fby_not_app].
      - apply unnest_rhs_Earrow_inv in Hun
          as (f0 & eqsa & st1 & f1 & eqsb & _ & _ & ? & _); subst.
        split; [apply unnest_arrow_numstreams|apply unnest_arrow_not_app].
      - contradiction.
    Qed.

    Lemma unnest_rhss_shape :
      forall P es ess eqss st st',
        Forall (wl_exp P) es ->
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False | _ => True end) es ->
        map_bind2 (unnest_rhs P) es st = ((ess, eqss), st') ->
        Forall (fun e' => numstreams e' = 1) (List.concat ess)
        /\ Forall (fun e' => match e' with
                             | Eapp _ _ _ _ => False | _ => True end)
             (List.concat ess).
    Proof.
      induction es as [|e es IH]; intros ess eqss st st' Hwl Hne Hun.
      - apply map_bind2_unnest_rhs_nil in Hun as (? & ? & ?); subst.
        split; constructor.
      - inv Hwl. inv Hne.
        apply map_bind2_unnest_rhs_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        edestruct (unnest_rhs_shape P e f1 eq1 st st1) as (Hn1 & Ha1); auto.
        edestruct (IH fr eqsr st1 st') as (Hn2 & Ha2); auto.
        simpl. split; apply Forall_app; auto.
    Qed.

    Lemma length_annots_single :
      forall es,
        Forall (fun e => numstreams e = 1) es ->
        List.length (annots es) = List.length es.
    Proof.
      induction es as [|e es IH]; intros H; [reflexivity|].
      inversion H as [|e0 es0 Hn Hr]; subst.
      unfold annots. simpl. rewrite app_length.
      rewrite length_annot_numstreams, Hn. simpl. f_equal.
      apply IH; auto.
    Qed.

    Lemma unnest_equation_inv :
      forall P xs es eqs' st st',
        unnest_equation P (xs, es) st = (eqs', st') ->
        exists es1 eqs1 ess eqss,
          map_bind2 (unnest_rhs P) es st = ((ess, eqss), st')
          /\ es1 = List.concat ess
          /\ eqs1 = List.concat eqss
          /\ eqs' = split_equation (xs, es1) ++ eqs1.
    Proof.
      intros P xs es eqs' st st' H.
      unfold unnest_equation, unnest_rhss in H. repeat inv_bind.
      repeat esplit; eauto.
    Qed.

    Lemma map_bind2_unnest_rhs_annots :
      forall P es ess eqss st st',
        Forall (wl_exp P) es ->
        map_bind2 (unnest_rhs P) es st = ((ess, eqss), st') ->
        annots (List.concat ess) = annots es.
    Proof.
      induction es as [|e es IH]; intros ess eqss st st' Hwl Hun.
      - apply map_bind2_unnest_rhs_nil in Hun as (? & ? & ?); subst.
        reflexivity.
      - inversion Hwl as [|e0 es0 Hwle Hwlrest]; subst.
        apply map_bind2_unnest_rhs_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        assert (annots f1 = annot e) as Ha1
            by exact (unnest_rhs_annot P e f1 eq1 st st1 Hwle Hun1).
        assert (annots (List.concat fr) = annots es) as Ha2
            by exact (IH fr eqsr st1 st' Hwlrest Hunr).
        simpl List.concat.
        replace (annots (f1 ++ List.concat fr))
          with (annots f1 ++ annots (List.concat fr))
          by (unfold annots; now rewrite <- flat_map_app).
        rewrite Ha1, Ha2. reflexivity.
    Qed.

    Lemma get_mappings_Forall2 :
      forall (xs : list ident) bs,
        get_mappings xs env = Some bs ->
        Forall2 (fun x b => Env.find x env = Some b) xs bs.
    Proof.
      induction xs as [|x xs IH]; intros bs H; simpl in H.
      - inv H. constructor.
      - destruct (Env.find x env) as [b|] eqn:Hb; [|discriminate H].
        destruct (get_mappings xs env) as [bs0|] eqn:Hbs; [|discriminate H].
        simpl in H. inv H. constructor; [exact Hb|now apply IH].
    Qed.

    (** * The equation level, away from calls

        Everything above meets here.  The source equation's rule and the
        split of its unnesting are the same [generate_lvars_constraints], run
        on the source's types and on the unnested ones; the induction
        hypothesis on the right-hand sides relates those two type lists
        modulo the ambient, and the general rule is monotone in exactly that.
        What the right-hand sides emitted is satisfied by the same witness.

        The one thing this level is *given* rather than proving is that the
        ambient lies below every variable the equation defines.  For this
        rule it is in fact free -- the source constraint says as much -- but
        stating it as a premise is what lets the call rule, where it is not
        free, be discharged separately at the node level. *)

    Lemma eqn_carries_plain :
      forall (P : global) (xs : list ident) (es : list exp)
             eqs' st st' ce xst xst' cet yst yst' dlt,
        Forall (fun e => match e with
                         | Eapp _ _ _ _ => False
                         | _ => True
                         end) es ->
        Forall (wl_exp P) es -> Forall (wc_exp P vars) es ->
        List.length xs = List.length (annots es) ->
        NoDup (vars_defined eqs' ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined eqs') -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of xs) -> satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        unnest_equation P (xs, es) st = (eqs', st') ->
        generate_leqn_constraint GL env base_ty rst_ty cenv (xs, es) xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.
    Proof.
      intros P xs es eqs' st st' ce xst xst' cet yst yst' dlt
        Hne Hwl Hwc Hlen Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.

      apply unnest_equation_inv in Hun
        as (es1 & eqs1 & ess & eqss & Hmap & ? & ? & ?); subst.
      apply generate_leqn_constraint_lvars in Hgen
        as (ts & bs & si & Hts & Hbs & Hlv); [|exact Hne].
      apply generate_leqns_constraints_app in Hgent
        as (cs & ce2 & ystm & Hgens & Hgen2 & ?); subst.

      edestruct (unnest_rhss_shape P es ess eqss st st') as (Hns & Hnea);
        [exact Hwl|exact Hne|exact Hmap|].
      assert (annots (List.concat ess) = annots es) as Hann
          by exact
            (map_bind2_unnest_rhs_annots P es ess eqss st st' Hwl Hmap).
      assert (List.length xs = List.length (List.concat ess)) as Hlx.
      { rewrite Hlen, <- Hann. now apply length_annots_single. }

      edestruct (split_equation_operand_types xs (List.concat ess) cs yst ystm)
        as (ts'' & q' & Hts'');
        [exact Hns|exact Hnea|exact Hlx|exact Hgens|].
      edestruct (unnest_rhss_pinned P es ess eqss st st' ts'' yst q')
        as (_ & Hpin); [exact Hwl|exact Hne|exact Hmap|exact Hts''|].

      assert (Forall2 (fun x b => Env.find x env = Some b) xs bs) as Hbsf
          by exact (get_mappings_Forall2 xs bs Hbs).
      assert (vars_defined (split_equation (xs, List.concat ess)) = xs) as Hvd
          by exact (vars_defined_split_equation xs (List.concat ess) Hns Hlx).
      rewrite vars_defined_app, Hvd in Hnd, Hamb.
      rewrite <- app_assoc in Hnd.

      assert (Forall (rhs_carries P) es) as Hrall.
      { exact (@Forall_impl exp
                 (fun e => match e with
                           | Eapp _ _ _ _ => False | _ => True end)
                 (rhs_carries P)
                 (fun e He => rhs_carries_exp P e He) es Hne). }

      assert (listSatisfiable dlt (carried ts)) as Hcarts
          by exact (generate_lvars_constraints_carried
                      dlt xs bs ts ce si xst' Hlv Hsat).

      edestruct (rhs_carries_list_intro P es Hrall
                   ess eqss st st' ts xst si ce2 ystm yst' ts'' yst q' dlt)
        as (dlt' & Hoff & Hce2 & Hcy & Hrel & Hscope2 & Hcs2 & Hts2).
      { exact Hwl. }
      { exact Hwc. }
      { exact (@NoDup_app_r ident xs
                 (vars_defined (List.concat eqss) ++ st_ids st) Hnd). }
      { exact Hmv. }
      { exact (source_lexps_carried_scoped es ts xst si Hts). }
      { exact (source_lexps_scoped es ts xst si Hts). }
      { intros y cky ckty Hy.
        exact (Hamb y cky ckty
                 (in_or_app xs (vars_defined (List.concat eqss)) y
                    (or_intror Hy))). }
      { exact Hmap. }
      { exact Hts. }
      { exact Hgen2. }
      { exact Hts''. }
      { exact Hcarts. }

      (** the split's constraints, as the general rule would have put them *)
      assert (generate_lvars_constraints env base_ty rst_ty cenv xs bs ts'' si
              = OK (cs, si)) as Hlv'
          by exact (split_equation_is_lvars xs (List.concat ess) bs ts''
                      cs yst ystm si Hns Hbsf Hpin Hlx Hgens).

      assert (Forall (fun b => In b scope) bs) as Hbssc.
      { exact (Forall2_right_In
                 (fun x b => Env.find x env = Some b)
                 (fun b => In b scope) xs bs Hbsf
                 (fun x b Hx Hf => env_range_scoped x b Hf)). }
      assert (Forall (fun b => satisfiable dlt' amb [b]) bs) as Hbs'.
      { apply (Forall2_right_In
                 (fun x b => Env.find x env = Some b)
                 (fun b => satisfiable dlt' amb [b]) xs bs Hbsf).
        intros x b Hx Hf.
        assert (In b (sec_of xs)) as Hbsec.
        { unfold sec_of. apply in_flat_map.
          exists x. split; [exact Hx|]. rewrite Hf. now left. }
        assert (In b scope) as Hbsc by exact (env_range_scoped x b Hf).
        assert (forall y, In y [b] -> ~ In y (moved_by st st')) as Hboff.
        { intros y Hy Hin. destruct Hy as [Hy|[]]. subst y.
          exact (Hmv b Hin Hbsc). }
        exact (satisfiable_off amb [b] (moved_by st st') dlt dlt' Hoff
                 (fun y Hy Hin => Hmv y Hin (amb_scoped y Hy))
                 Hboff
                 (Hbs0 b Hbsec)). }

      assert (listSatisfiable dlt' ce) as Hsat'
          by exact (listSatisfiable_off scope ce (moved_by st st')
                      dlt dlt' Hcesc Hmv Hoff Hsat).

      exists dlt'. split; [exact Hoff|split].
      - apply listSatisfiable_app. split; [|exact Hce2].
        exact (generate_lvars_constraints_mono dlt' xs bs ts ts'' ce cs
                 si xst' si si Hrel Hbs' Hcy Hlv Hlv' Hsat').
      - apply Forall_app. split; [|exact Hscope2].
        exact (generate_lvars_constraints_scoped
                 (scope ++ moved_by st st') xs bs ts'' cs si si
                 (in_or_app scope (moved_by st st') rst_ty
                    (or_introl rst_ty_scoped))
                 (fun ck ckty Hck =>
                    st_scoped_weaken scope (scope ++ moved_by st st') ckty
                      (@incl_appl ident scope (moved_by st st') scope
                         (incl_refl scope))
                      (clk_types_scoped ck ckty Hck))
                 (@Forall_impl ident (fun b => In b scope)
                    (fun b => In b (scope ++ moved_by st st'))
                    (fun b Hb => in_or_app scope (moved_by st st') b
                                   (or_introl Hb)) bs Hbssc)
                 Hts2 Hcs2 Hlv').
    Qed.

    (** * A call at the top of an equation

        [unnest_rhs] leaves it there -- the equation's own variables bind its
        results -- so the two sides instantiate the callee with the *same*
        outputs.  That removes the need for a witness on the results, and
        replaces it with the one thing this level is given: the ambient lies
        below each of them.

        The equation rule accepts a call whose reset is absent or already a
        variable.  A source call reset by something else falls to the general
        rule, which types the call as an expression with results of its own;
        that shape is not covered here. *)

    Lemma unnest_rhs_Eapp_inv :
      forall P f es er anns es' eqs st st',
        unnest_rhs P (Eapp f es er anns) st = ((es', eqs), st') ->
        exists es1 eqs1 st1 es2 eqs2 st2 er2 eqs3,
          unnest_exps P es st = ((es1, eqs1), st1)
          /\ unnest_noops_exps (find_node_incks P f) es1 st1
             = ((es2, eqs2), st2)
          /\ unnest_reset (unnest_exp P true) er st2 = ((er2, eqs3), st')
          /\ es' = [Eapp f es2 er2 anns]
          /\ eqs = eqs1 ++ eqs2 ++ eqs3.
    Proof.
      intros P f es er anns es' eqs st st' H.
      simpl in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma split_equation_single :
      forall (xs : list ident) e,
        List.length xs = numstreams e ->
        split_equation (xs, [e]) = [(xs, [e])].
    Proof.
      intros xs e Hlen. unfold split_equation.
      cbn [combine_for_numstreams]. rewrite <- Hlen, firstn_all.
      reflexivity.
    Qed.

    Lemma unnest_reset_var :
      forall P er st,
        (er = None \/ exists r an, er = Some (Evar r an)) ->
        unnest_reset (unnest_exp P true) er st = ((er, []), st).
    Proof.
      intros P er st [?|(r & an & ?)]; subst.
      - unfold unnest_reset. apply ret_spec.
      - unfold unnest_reset. rewrite bind2_spec.
        exists [Evar r an], [], st.
        split; [apply unnest_exp_Evar|]. simpl. apply ret_spec.
    Qed.

    Lemma eqn_carries_call :
      forall (P : global) (xs : list ident) f args er anns
             eqs' st st' ce xst xst' cet yst yst' dlt,
        wl_exp P (Eapp f args er anns) ->
        wc_exp P vars (Eapp f args er anns) ->
        List.length xs = List.length anns ->
        NoDup (vars_defined eqs' ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined eqs') -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of xs) -> satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        unnest_equation P (xs, [Eapp f args er anns]) st = (eqs', st') ->
        generate_leqn_constraint GL env base_ty rst_ty cenv
          (xs, [Eapp f args er anns]) xst = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.
    Proof.
      intros P xs f args er anns eqs' st st' ce xst xst' cet yst yst' dlt
        Hwl Hwc Hlen Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.
      pose proof Hwl as Hwl0. pose proof Hwc as Hwc0.
      assert (anns <> []) as Hanne.
      { intro Hc. subst anns. inv Hwl0;
          match goal with H : _ = List.length (n_out ?nn) |- _ =>
            pose proof (n_outgt0 nn); simpl in H; lia end. }
      assert (exists x0 xs0, xs = x0 :: xs0) as (x0 & xs0 & Exs).
      { destruct xs as [|x0 xs0]; [|now exists x0, xs0].
        exfalso. apply Hanne. simpl in Hlen.
        destruct anns; [reflexivity|discriminate Hlen]. }
      subst xs.
      assert (Forall (wl_exp P) args) as Hwles by (inv Hwl0; assumption).
      assert (Forall (wc_exp P vars) args) as Hwces by (inv Hwc0; assumption).

      (** the unnesting, and the one equation the split produced *)
      apply unnest_equation_inv in Hun
        as (es1 & eqs1 & ess & eqss & Hmap & ? & ? & ?); subst.
      apply map_bind2_unnest_rhs_cons in Hmap
        as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
      apply map_bind2_unnest_rhs_nil in Hunr as (? & ? & ?); subst.
      simpl List.concat in *. rewrite !app_nil_r in *.
      apply unnest_rhs_Eapp_inv in Hun1
        as (g1 & geqs1 & sta & g2 & geqs2 & stb & er2 & geqs3
            & Hune & Hunn & Hunr2 & ? & ?); subst.
      pose proof Hune as Hune0.
      apply unnest_exps_inv in Hune as (ess & eqss & Hmape & ? & ?); subst.

      assert (numstreams (Eapp f g2 er2 anns) = List.length (x0 :: xs0))
        as Hnsc by (simpl in Hlen |- *; now symmetry).
      rewrite split_equation_single in Hgent by (now symmetry).
      rewrite vars_defined_app in Hnd, Hamb.
      rewrite split_equation_single in Hnd, Hamb by (now symmetry).
      apply generate_leqns_constraints_app in Hgent
        as (ce0 & cer & ysta & Hgen0' & Hgenr & ?); subst.
      rewrite generate_leqns_constraints_cons in Hgen0'.
      apply sec_bind_inv in Hgen0' as (ce0a & y1 & Hgen0 & Hgen0').
      apply sec_bind_inv in Hgen0' as (ce0b & y2 & Hgen0b & Hret0).
      unfold SC.ret in Hret0. inv Hret0.
      apply generate_leqns_constraints_nil in Hgen0b as (? & ?); subst.
      rewrite app_nil_r in *.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & cerr & ystc & Hgen1 & Hgenrr & ?); subst.
      apply generate_leqns_constraints_app in Hgenrr
        as (ce2 & ce3 & ystd & Hgen2 & Hgen3 & ?); subst.

      (** the states the run passed through *)
      assert (st_follows st sta) as Hfa
          by exact (map_bind2_unnest_st_follows
                      P false args ess eqss st sta Hmape).
      assert (st_follows sta stb) as Hfb
          by exact (unnest_noops_exps_st_follows
                      (List.concat ess) (find_node_incks P f)
                      g2 geqs2 sta stb Hunn).
      assert (st_follows stb st1) as Hfc
          by exact (unnest_reset_st_follows
                      P true er (er2, geqs3) stb st1 Hunr2).
      assert (st_follows st stb) as Hf0b by (etransitivity; eauto).
      assert (st_follows sta st1) as Hfa1 by (etransitivity; eauto).
      assert (st_follows st st1) as Hf01 by (etransitivity; eauto).

      (** the source's call rule; the reset is typed as an expression *)
      assert (exists sg rstty ckty argts outs sti cs stm,
                 find_signature f GL = Some sg
                 /\ ((er = None /\ rstty = lvar rst_ty /\ stm = xst)
                     \/ (exists e1 a1 rck,
                           er = Some e1
                           /\ assign_lexp_type GL env base_ty rst_ty e1 xst
                              = OK ([a1], stm)
                           /\ assign_clk_type env base_ty
                                (hd Cbase (LSyn.clockof e1)) = Some rck
                           /\ rstty = ljoin (lvar rst_ty) (ljoin a1 (rck, []))))
                 /\ assign_clk_type env base_ty
                      (find_base_clock (LSyn.clocksof args)) = Some ckty
                 /\ assign_lexps GL env base_ty rst_ty args stm
                    = OK (argts, sti)
                 /\ SC.mmap (fun x => find_env x env) (x0 :: xs0) sti
                    = OK (outs, sti)
                 /\ generate_constraints sg (List.map fst argts) ckty
                      (fst rstty) outs sti = OK (cs, xst')
                 /\ ce = cmerge cs (cmerge (carried argts) (snd rstty)))
        as (sg & rstty & ckty & argts & outs & sti & cs & stm
            & Esg & Hrsh & Hck & Hargs & Houts & Hcs & Hce).
      { destruct er as [e1|].
        - rewrite gen_leqn_Eapp_someresetel in Hgen.
          apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
          apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
          apply single_inv in Ha1 as (? & ?); subst t1 s2.
          apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
          apply option_to_sec_inv in Hrck as (Hrck & ?); subst s3.
          apply generate_lcall_constraint_inv in Hgen
            as (sg & ckty & argts & outs & sti & cs
                & Esg & Hck & Hargs & Houts & Hcs & Hce).
          exists sg, (ljoin (lvar rst_ty) (ljoin a1 (rck, []))), ckty, argts,
                 outs, sti, cs, s1.
          split; [exact Esg|].
          split; [right; exists e1, a1, rck; repeat split; auto|].
          repeat split; auto.
        - rewrite gen_leqn_Eapp in Hgen.
          apply generate_lcall_constraint_inv in Hgen
            as (sg & ckty & argts & outs & sti & cs
                & Esg & Hck & Hargs & Houts & Hcs & Hce).
          exists sg, (lvar rst_ty), ckty, argts, outs, sti, cs, xst.
          split; [exact Esg|]. split; [left; repeat split; auto|].
          repeat split; auto. }

      (** and the emitted call's, whose outputs are the same *)
      pose proof Hunr2 as Hunr3.
      assert (exists rstty2 ckt argt outt stj cs0,
                 ((er = None /\ er2 = None /\ geqs3 = [] /\ st1 = stb
                   /\ rstty2 = lvar rst_ty)
                  \/ (exists e1 r ty0 ckr0 nm0 rty rstck,
                        er = Some e1
                        /\ er2 = Some (Evar r (ty0, (ckr0, nm0)))
                        /\ Env.find r env = Some rty
                        /\ assign_clk_type env base_ty ckr0 = Some rstck
                        /\ rstty2 = ljoin (lvar rst_ty)
                                      (merge [rty] rstck, [])))
                 /\ assign_clk_type env base_ty
                      (find_base_clock (LSyn.clocksof g2)) = Some ckt
                 /\ assign_lexps GL env base_ty rst_ty g2 yst = OK (argt, stj)
                 /\ SC.mmap (fun x => find_env x env) (x0 :: xs0) stj
                    = OK (outt, stj)
                 /\ generate_constraints sg (List.map fst argt) ckt
                      (fst rstty2) outt stj = OK (cs0, y1)
                 /\ ce0a = cmerge cs0 (cmerge (carried argt) (snd rstty2)))
        as (rstty2 & ckt & argt & outt & stj & cs0
            & Hrsh2 & Hckt & Hargt & Houtt & Hgc & Hce0).
      { apply unnest_reset_option_shape in Hunr3
          as [(Hern & Hn2 & Heq3 & Hst1)|(e1 & rv & ran & Her & Hs2)].
        - rewrite Hn2 in Hgen0. rewrite gen_leqn_Eapp in Hgen0.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & stj & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (lvar rst_ty), ckt, argt, outt, stj, cs0.
          split; [left; repeat split; auto|repeat split; auto].
        - destruct ran as (ty0 & ckr0 & nm0).
          rewrite Hs2 in Hgen0. rewrite gen_leqn_Eapp_reset in Hgen0.
          apply sec_bind_inv in Hgen0 as (rty & s1 & Hrty & Hgen0).
          apply find_env_inv in Hrty as (Hrty & ?); subst s1.
          apply sec_bind_inv in Hgen0 as (rstck & s2 & Hrstck & Hgen0).
          apply option_to_sec_inv in Hrstck as (Hrstck & ?); subst s2.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & stj & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (ljoin (lvar rst_ty) (merge [rty] rstck, [])),
                 ckt, argt, outt, stj, cs0.
          split; [|repeat split; auto].
          right. exists e1, rv, ty0, ckr0, nm0, rty, rstck. repeat split; auto. }
      subst ce ce0a.

      assert (outt = outs) as ?.
      { assert (state_pure (SC.mmap (fun x => find_env x env) (x0 :: xs0)))
          as Hp by (apply state_pure_mmap; intros; apply state_pure_find_env).
        destruct (Hp _ stj _ _ Houts) as (_ & Hq).
        rewrite Hq in Houtt. now inv Houtt. }
      subst outt.

      (** what the source carries, taken apart *)
      apply listSatisfiable_cmerge in Hsat as (Hcs1 & Hcarr).
      apply listSatisfiable_cmerge in Hcarr as (Hcarg & Hcrst).
      apply constraints_scoped_cmerge in Hcesc as (Hcssc & Hcarrsc).
      apply constraints_scoped_cmerge in Hcarrsc as (Hcargsc & Hcrstsc).

      (** the emitted equations, split between the three stages *)
      rewrite <- app_assoc in Hnd.
      assert (vars_defined [(x0 :: xs0, [Eapp f g2 er2 anns])]
              = x0 :: xs0) as Hvd0.
      { unfold vars_defined. simpl. now rewrite app_nil_r. }
      rewrite Hvd0 in Hnd.
      assert (NoDup (vars_defined (List.concat eqss ++ geqs2 ++ geqs3)
                       ++ st_ids st)) as Hndr
          by exact (@NoDup_app_r ident (x0 :: xs0)
                      (vars_defined (List.concat eqss ++ geqs2 ++ geqs3)
                         ++ st_ids st) Hnd).
      assert (Permutation (vars_defined (List.concat eqss) ++ st_ids st)
                (st_ids sta)) as Hp0
          by exact (map_bind2_unnest_vars_perm
                      P false args ess eqss st sta Hwles Hmape).
      assert (Permutation (vars_defined geqs2 ++ st_ids sta) (st_ids stb))
        as Hp2 by exact (unnest_noops_exps_vars_perm
                           (find_node_incks P f) (List.concat ess)
                           g2 geqs2 sta stb Hunn).
      assert (NoDup (vars_defined (List.concat eqss) ++ st_ids st)) as Hnd1
          by exact (NoDup_vd_app_l (List.concat eqss) (geqs2 ++ geqs3)
                      (st_ids st) Hndr).
      assert (NoDup (vars_defined (geqs2 ++ geqs3) ++ st_ids sta)) as Hnd23
          by exact (NoDup_vd_app_r (List.concat eqss) (geqs2 ++ geqs3)
                      (st_ids st) (st_ids sta) Hp0 Hndr).
      assert (NoDup (vars_defined geqs2 ++ st_ids sta)) as Hnd2
          by exact (NoDup_vd_app_l geqs2 geqs3 (st_ids sta) Hnd23).
      assert (NoDup (vars_defined geqs3 ++ st_ids stb)) as Hnd3
          by exact (NoDup_vd_app_r geqs2 geqs3 (st_ids sta) (st_ids stb)
                      Hp2 Hnd23).

      (** the arguments, as the pass left them *)
      assert (Forall normalized_lexp (List.concat ess)) as Hnorm1
          by exact (map_bind2_unnest_normalized_lexp
                      P args ess eqss st sta Hmape).
      assert (List.length (List.concat ess) = List.length (annots args))
        as Hlen1 by exact (map_bind2_unnest_exp_length
                            P false args ess eqss st sta Hwles Hmape).
      assert (List.length (find_node_incks P f)
              = List.length (List.concat ess)) as Hlck.
      { unfold find_node_incks. rewrite Hlen1.
        inv Hwl0;
          match goal with
          | H : find_node f P = Some ?nn |- _ => rewrite H
          end; rewrite map_length;
          match goal with
          | H : List.length (annots args) = _ |- _ => now rewrite H
          end. }
      edestruct (noops_operand_types_local (find_node_incks P f) (List.concat ess)
                   g2 geqs2 sta stb ce2 ystc ystd argt yst stj)
        as (argts1 & Hargts1);
        [exact Hlck|exact Hnorm1|exact Hunn|exact Hgen2|exact Hargt|].

      edestruct (carries_exps P args false ess eqss st sta argts
                   stm sti ce1 y1 ystc argts1 yst yst dlt)
        as (dlt1 & Hoff1 & Hce1' & Hrel1 & Hscope1 & Hsca1).
      { exact Hwles. }
      { exact Hwces. }
      { exact Hnd1. }
      { intros y Hy. apply Hmv.
        apply (eq_moved_by_prefix st sta st1 Hfa1). exact Hy. }
      { exact Hcargsc. }
      { exact (source_lexps_scoped args argts stm sti Hargs). }
      { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
        rewrite !vars_defined_app. apply in_or_app. now left. }
      { exact Hmape. }
      { exact Hargs. }
      { exact Hgen1. }
      { apply (Hargts1 yst). }
      { exact Hcarg. }

      assert (forall y, In y (moved_by sta stb) ->
                        ~ In y (scope ++ moved_by st sta)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - apply (Hmv y); [|exact Hy].
          apply (eq_moved_by_suffix st sta st1 Hfa).
          apply (eq_moved_by_prefix sta stb st1 Hfc). exact Hin.
        - exact (eq_moved_by_disjoint st sta stb y Hy Hin). }
      edestruct (noops_step_local (scope ++ moved_by st sta) (find_node_incks P f)
                   (List.concat ess) g2 geqs2 sta stb argts1 argt ce2
                   ystc ystd yst yst yst stj dlt1)
        as (dlt2 & Hoff2 & Hce2' & Hrel2 & Hscope2 & Hsca2).
      { exact Hlck. }
      { exact Hnorm1. }
      { exact Hunn. }
      { exact Hnd2. }
      { exact Hsep12. }
      { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
        rewrite !vars_defined_app. apply in_or_app. right.
        apply in_or_app. now left. }
      { exact (st_scoped_weaken scope (scope ++ moved_by st sta) amb
                 (@incl_appl ident scope (moved_by st sta) scope
                    (incl_refl scope)) amb_scoped). }
      { apply (Hargts1 yst). }
      { exact Hargt. }
      { exact Hsca1. }
      { exact Hgen2. }

      (** the reset, which unnesting lifts to a variable of its own *)
      assert (agree_off (moved_by st stb) dlt dlt2) as Hoff12.
      { exact (agree_off_trans (moved_by st stb) dlt dlt1 dlt2
                 (agree_off_incl (moved_by st sta) (moved_by st stb)
                    dlt dlt1 (eq_moved_by_prefix st sta stb Hfb) Hoff1)
                 (agree_off_incl (moved_by sta stb) (moved_by st stb)
                    dlt1 dlt2 (eq_moved_by_suffix st sta stb Hfa) Hoff2)). }
      assert (exists dlt3,
                 agree_off (moved_by stb st1) dlt2 dlt3
                 /\ listSatisfiable dlt3 ce3
                 /\ constraints_scoped (scope ++ moved_by stb st1) ce3
                 /\ satisfiable dlt3 (fst rstty2) (merge amb (fst rstty))
                 /\ st_scoped (scope ++ moved_by st st1) (fst rstty2))
        as (dlt3 & Hoff3 & Hce3' & Hscope3 & Hrelrst & Hscrst').
      { destruct Hrsh as [(Hern & Hr1 & Hstm)
                         |(e1 & a1 & rck & Her & Hty1 & Hrck & Hr1)];
          destruct Hrsh2 as [(Hern2 & Hn2 & Heq3 & Hst1 & Hr2)
                            |(e1' & rv & ty0 & ckr0 & nm0 & rty & rstck
                              & Her2 & Hs2 & Hrty & Hrstck & Hr2)].
        - (** no reset: nothing was emitted and nothing moved *)
          rewrite Heq3 in Hgen3.
          apply generate_leqns_constraints_nil in Hgen3 as (Hc3 & _).
          rewrite Hr1, Hr2, Hc3.
          exists dlt2. split; [apply agree_off_refl|].
          split; [constructor|]. split; [constructor|].
          split; [apply satisfiable_merge_r|].
          rewrite fst_lvar. intros y Hy. destruct Hy as [Hy|[]]; subst y.
          apply in_or_app. left. exact rst_ty_scoped.
        - rewrite Hern in Her2. discriminate Her2.
        - rewrite Her in Hern2. discriminate Hern2.
        - (** a reset: the reset step, on the variable it came back as *)
          assert (e1' = e1) as ? by congruence; subst e1'.
          rewrite Her in Hwl0, Hwc0, Hunr2.
          rewrite Hs2 in Hunr2.
          rewrite Hr2.
          assert (wl_exp P e1) as Hwle1 by (inv Hwl0; assumption).
          assert (wc_exp P vars e1) as Hwce1 by (inv Hwc0; assumption).
          assert (numstreams e1 = 1) as Hns1 by (inv Hwl0; assumption).
          assert (st_scoped scope (fst a1)) as Hsca1'.
          { assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hf
                by exact (source_types_scoped e1 [a1] xst stm Hty1).
            now inv Hf. }
          assert (snd rstty = snd a1) as Hsndr.
          { rewrite Hr1. rewrite !snd_ljoin, snd_lvar. simpl snd.
            now rewrite cmerge_nil, cmerge_nil2. }
          assert (rstck = rck) as Hcke.
          { assert (LSyn.clockof e1 = [ckr0]) as Hcl
                by exact (unnest_reset_ann_clock P e1 rv ty0 ckr0 nm0
                            geqs3 stb st1 Hwle1 Hns1 Hunr2).
            rewrite Hcl in Hrck. simpl hd in Hrck.
            rewrite Hrstck in Hrck. now inv Hrck. }
          edestruct (reset_step_local P e1 rv (ty0, (ckr0, nm0)) rty geqs3 stb st1
                       a1 xst stm ce3 ystd yst' yst dlt2)
            as (dlt3 & Hoff3 & Hce3' & Hrelr & Hinr & Hscope3).
          { apply carries_exp. }
          { exact Hwle1. }
          { exact Hwce1. }
          { exact Hns1. }
          { exact Hunr2. }
          { exact Hrty. }
          { exact Hnd3. }
          { intros y Hy. apply Hmv.
            apply (eq_moved_by_suffix st stb st1 Hf0b). exact Hy. }
          { intros y cky ckty0 Hy. apply Hamb. apply in_or_app. right.
            rewrite !vars_defined_app. apply in_or_app. right.
            apply in_or_app. now right. }
          { exact Hty1. }
          { rewrite carried_single, <- Hsndr. exact Hcrstsc. }
          { exact Hsca1'. }
          { exact Hgen3. }
          { rewrite carried_single, <- Hsndr.
            exact (listSatisfiable_off_scope (snd rstty) scope
                     (moved_by st stb) dlt dlt2 Hcrstsc
                     (fun y Hy Hin =>
                        Hmv y (eq_moved_by_prefix st stb st1 Hfc y Hy) Hin)
                     Hoff12 Hcrst). }
          exists dlt3. split; [exact Hoff3|]. split; [exact Hce3'|].
          split; [exact Hscope3|]. split.
          + rewrite Hr1, Hcke. rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            assert (satisfiable dlt3 [rst_ty]
                      (merge amb
                        (merge [rst_ty] (merge (fst a1) rck)))) as Hrstfin.
            { exact (satisfiable_trans dlt3 [rst_ty]
                       (merge [rst_ty] (merge (fst a1) rck))
                       (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                       (satisfiable_merge_l dlt3 [rst_ty]
                          (merge (fst a1) rck))
                       (satisfiable_merge_r dlt3 amb
                          (merge [rst_ty] (merge (fst a1) rck)))). }
            assert (satisfiable dlt3 amb
                      (merge amb
                        (merge [rst_ty] (merge (fst a1) rck)))) as Hambfin
              by exact (satisfiable_merge_l dlt3 amb
                          (merge [rst_ty] (merge (fst a1) rck))).
            assert (satisfiable dlt3 (fst a1)
                      (merge amb
                        (merge [rst_ty] (merge (fst a1) rck)))) as Ha1fin.
            { exact (satisfiable_trans dlt3 (fst a1)
                       (merge (fst a1) rck)
                       (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                       (satisfiable_merge_l dlt3 (fst a1) rck)
                       (satisfiable_trans dlt3 (merge (fst a1) rck)
                          (merge [rst_ty] (merge (fst a1) rck))
                          (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                          (satisfiable_merge_r dlt3 [rst_ty]
                             (merge (fst a1) rck))
                          (satisfiable_merge_r dlt3 amb
                             (merge [rst_ty] (merge (fst a1) rck))))). }
            assert (satisfiable dlt3 [rty]
                      (merge amb
                        (merge [rst_ty] (merge (fst a1) rck)))) as Hrtyfin.
            { exact (satisfiable_trans dlt3 [rty] (merge amb (fst a1))
                       (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                       Hrelr
                       (satisfiable_merge_intro dlt3 amb (fst a1)
                          (merge amb
                            (merge [rst_ty] (merge (fst a1) rck)))
                          Hambfin Ha1fin)). }
            assert (satisfiable dlt3 rck
                      (merge amb
                        (merge [rst_ty] (merge (fst a1) rck)))) as Hrckfin.
            { exact (satisfiable_trans dlt3 rck (merge (fst a1) rck)
                       (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                       (satisfiable_merge_r dlt3 (fst a1) rck)
                       (satisfiable_trans dlt3 (merge (fst a1) rck)
                          (merge [rst_ty] (merge (fst a1) rck))
                          (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                          (satisfiable_merge_r dlt3 [rst_ty]
                             (merge (fst a1) rck))
                          (satisfiable_merge_r dlt3 amb
                             (merge [rst_ty] (merge (fst a1) rck))))). }
            exact (satisfiable_merge_intro dlt3 [rst_ty]
                     (merge [rty] rck)
                     (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                     Hrstfin
                     (satisfiable_merge_intro dlt3 [rty] rck
                        (merge amb (merge [rst_ty] (merge (fst a1) rck)))
                        Hrtyfin Hrckfin)).
          + rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            intros y Hy. apply in_merge_inv in Hy as [Hy|Hy].
            * destruct Hy as [Hy|[]]; subst y. apply in_or_app. left.
              exact rst_ty_scoped.
            * apply in_merge_inv in Hy as [Hy|Hy].
              -- destruct Hy as [Hy|[]]; subst y.
                 apply in_app_or in Hinr as [Hinr|Hinr];
                   apply in_or_app; [now left|].
                 right. apply (eq_moved_by_suffix st stb st1 Hf0b). exact Hinr.
              -- apply in_or_app. left.
                 exact (clk_types_scoped ckr0 rstck Hrstck y Hy). }

      (** the witnesses, composed *)
      assert (agree_off (moved_by st st1) dlt dlt3) as Hoffall.
      { exact (agree_off_trans (moved_by st st1) dlt dlt2 dlt3
                 (agree_off_incl (moved_by st stb) (moved_by st st1)
                    dlt dlt2 (eq_moved_by_prefix st stb st1 Hfc) Hoff12)
                 (agree_off_incl (moved_by stb st1) (moved_by st st1)
                    dlt2 dlt3 (eq_moved_by_suffix st stb st1 Hf0b) Hoff3)). }
      assert (agree_off (moved_by sta st1) dlt1 dlt3) as Hoff1all.
      { exact (agree_off_trans (moved_by sta st1) dlt1 dlt2 dlt3
                 (agree_off_incl (moved_by sta stb) (moved_by sta st1)
                    dlt1 dlt2 (eq_moved_by_prefix sta stb st1 Hfc) Hoff2)
                 (agree_off_incl (moved_by stb st1) (moved_by sta st1)
                    dlt2 dlt3 (eq_moved_by_suffix sta stb st1 Hfb) Hoff3)). }

      (** the argument types, at the final witness *)
      assert (forall y, In y (moved_by stb st1) ->
                        ~ In y (scope ++ moved_by st stb)) as Hsep2.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - apply (Hmv y); [|exact Hy].
          apply (eq_moved_by_suffix st stb st1 Hf0b). exact Hin.
        - exact (eq_moved_by_disjoint st stb st1 y Hy Hin). }
      assert (forall y, In y (moved_by sta st1) ->
                        ~ In y (scope ++ moved_by st sta)) as Hsep1all.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - apply (Hmv y); [|exact Hy].
          apply (eq_moved_by_suffix st sta st1 Hfa). exact Hin.
        - exact (eq_moved_by_disjoint st sta st1 y Hy Hin). }
      assert (incl scope (scope ++ moved_by st stb)) as Hinc0b
        by exact (@incl_appl ident scope (moved_by st stb) scope
                    (incl_refl scope)).
      assert (incl (scope ++ moved_by st sta)
                   (scope ++ moved_by st stb)) as Hincab.
      { apply incl_app; [exact Hinc0b|].
        apply incl_appr. exact (eq_moved_by_prefix st sta stb Hfb). }
      assert (incl ((scope ++ moved_by st sta) ++ moved_by sta stb)
                   (scope ++ moved_by st stb)) as Hincstages.
      { apply incl_app; [exact Hincab|].
        apply incl_appr. exact (eq_moved_by_suffix st sta stb Hfa). }
      assert (st_scoped (scope ++ moved_by st stb) amb) as Hambsc2
          by exact (st_scoped_weaken scope (scope ++ moved_by st stb) amb
                      Hinc0b amb_scoped).
      assert (Forall (fun t => st_scoped scope (fst t)) argts) as Hscargts
          by exact (source_lexps_scoped args argts stm sti Hargs).
      assert (Forall (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                argts) as Hsc_argts.
      { exact (@Forall_impl LST
                 (fun t => st_scoped scope (fst t))
                 (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                 (fun t Ht => st_scoped_weaken scope
                    (scope ++ moved_by st stb) (fst t) Hinc0b Ht)
                 argts Hscargts). }
      assert (Forall (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                argts1) as Hsc_argts1.
      { exact (@Forall_impl LST
                 (fun t => st_scoped (scope ++ moved_by st sta) (fst t))
                 (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                 (fun t Ht => st_scoped_weaken (scope ++ moved_by st sta)
                    (scope ++ moved_by st stb) (fst t) Hincab Ht)
                 argts1 Hsca1). }
      assert (Forall (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                argt) as Hsc_argt.
      { exact (@Forall_impl LST
                 (fun t => st_scoped
                    ((scope ++ moved_by st sta) ++ moved_by sta stb) (fst t))
                 (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                 (fun t Ht => st_scoped_weaken
                    ((scope ++ moved_by st sta) ++ moved_by sta stb)
                    (scope ++ moved_by st stb) (fst t) Hincstages Ht)
                 argt Hsca2). }
      assert (st_scoped (scope ++ moved_by st sta) amb) as Hambsca.
      { exact (st_scoped_weaken scope (scope ++ moved_by st sta) amb
                 (@incl_appl ident scope (moved_by st sta) scope
                    (incl_refl scope)) amb_scoped). }
      assert (Forall
                (fun t => st_scoped (scope ++ moved_by st sta) (fst t))
                argts) as Hsc_argtsa.
      { exact (@Forall_impl LST
                 (fun t => st_scoped scope (fst t))
                 (fun t => st_scoped (scope ++ moved_by st sta) (fst t))
                 (fun t Ht => st_scoped_weaken scope
                    (scope ++ moved_by st sta) (fst t)
                    (@incl_appl ident scope (moved_by st sta) scope
                       (incl_refl scope)) Ht)
                 argts Hscargts). }
      assert (Forall2 (fun t1 t2 =>
                satisfiable dlt2 (fst t2) (merge amb (fst t1)))
                argts argts1) as Hrel12.
      { exact (Forall2_rel_off amb dlt1 dlt2 (moved_by sta stb)
                 argts argts1 (scope ++ moved_by st sta)
                 Hoff2 Hsep12 Hambsca Hsc_argtsa Hsca1 Hrel1). }
      assert (Forall2 (fun t1 t2 =>
                satisfiable dlt3 (fst t2) (merge amb (fst t1)))
                argts argts1) as Hrel13.
      { exact (Forall2_rel_off amb dlt2 dlt3 (moved_by stb st1)
                 argts argts1 (scope ++ moved_by st stb)
                 Hoff3 Hsep2 Hambsc2 Hsc_argts Hsc_argts1 Hrel12). }
      assert (Forall2 (fun t1 t2 =>
                satisfiable dlt3 (fst t2) (merge amb (fst t1)))
                argts1 argt) as Hrel23.
      { exact (Forall2_rel_off amb dlt2 dlt3 (moved_by stb st1)
                 argts1 argt (scope ++ moved_by st stb)
                 Hoff3 Hsep2 Hambsc2 Hsc_argts1 Hsc_argt Hrel2). }
      assert (Forall2 (fun t1 t2 =>
                satisfiable dlt3 (fst t2) (merge amb (fst t1))) argts argt)
        as Hrelargs.
      { exact (Forall2_amb_compose amb dlt3 argts argts1 argt
                 Hrel13 Hrel23). }

      (** the clock, and the results, which are the same on both sides *)
      assert (Forall (fun e => numstreams e = 1) (List.concat ess)) as Hns1s
          by exact (map_bind2_unnest_exp_numstreams
                      P args false ess eqss st sta Hmape).
      assert (ckt = ckty) as Hckeq.
      { assert (LSyn.clocksof g2 = LSyn.clocksof args) as Hcl
            by exact (unnest_call_clocksof P args (List.concat ess)
                        (List.concat eqss) st sta (find_node_incks P f)
                        g2 geqs2 stb Hwles Hune0 Hlck Hns1s Hunn).
        rewrite Hcl, Hck in Hckt. now inv Hckt. }
      assert (Forall2 (fun x b => Env.find x env = Some b) (x0 :: xs0) outs)
        as Houtsf by exact (mmap_find_env_Forall2 env
                             (x0 :: xs0) outs sti sti Houts).
      assert (Forall (fun b => In b scope) outs) as Houtssc.
      { exact (Forall2_right_In
                 (fun x b => Env.find x env = Some b)
                 (fun b => In b scope) (x0 :: xs0) outs Houtsf
                 (fun x b Hx Hf => env_range_scoped x b Hf)). }
      assert (Forall (fun b => satisfiable dlt3 amb [b]) outs) as Hamb2.
      { apply (Forall2_right_In
                 (fun x b => Env.find x env = Some b)
                 (fun b => satisfiable dlt3 amb [b])
                 (x0 :: xs0) outs Houtsf).
        intros x b Hx Hf.
        assert (In b scope) as Hbsc by exact (env_range_scoped x b Hf).
        assert (In b (sec_of (x0 :: xs0))) as Hbsec.
        { unfold sec_of. apply in_flat_map.
          exists x. split; [exact Hx|]. rewrite Hf. now left. }
        assert (forall y, In y [b] -> ~ In y (moved_by st st1)) as Hboff.
        { intros y Hy Hin. destruct Hy as [Hy|[]]. subst y.
          exact (Hmv b Hin Hbsc). }
        exact (satisfiable_off amb [b] (moved_by st st1) dlt dlt3
                 Hoffall (fun y Hy Hin => Hmv y Hin (amb_scoped y Hy))
                 Hboff (Hbs0 b Hbsec)). }
      assert (Forall2 (amb_pair_local dlt3) outs outs) as Hpairs.
      { clear - Hamb2. induction Hamb2 as [|b bs Hb Hr IH]; constructor; auto.
        split; [apply satisfiable_merge_r|].
        apply satisfiable_merge_intro; [exact Hb|apply satisfiable_refl]. }

      (** what the emitted call generates is just the instantiated block *)
      assert (carried argt = []) as Hcargt.
      { assert (Forall normalized_lexp g2) as Hng2
          by exact (unnest_noops_normalized (find_node_incks P f)
                      (List.concat ess) g2 geqs2 sta stb Hlck Hnorm1 Hunn).
        assert (Forall normalized_cexp g2) as Hncg2
          by exact (@Forall_impl exp normalized_lexp normalized_cexp
                      normalized_lexp_cexp g2 Hng2).
        destruct (assign_lexps_normalized_pure GL env base_ty rst_ty g2 Hncg2
                    argt yst stj Hargt) as (_ & _ & Hcarried & _).
        exact Hcarried. }
      assert (snd rstty2 = []) as Hsrst.
      { destruct Hrsh2 as [(_ & _ & _ & _ & Hr2)
                          |(e1 & rv & ty0 & ckr0 & nm0 & rty & rstck
                            & _ & _ & _ & _ & Hr2)]; rewrite Hr2; [reflexivity|].
        rewrite snd_ljoin, snd_lvar. cbn [snd]. apply cmerge_nil. }
      assert (cmerge cs0 (cmerge (carried argt) (snd rstty2)) = cs0) as Hce0'
          by (now rewrite Hcargt, Hsrst, !cmerge_nil).

      assert (listSatisfiable dlt3 cs) as Hcssat
          by exact (listSatisfiable_off scope cs (moved_by st st1)
                      dlt dlt3 Hcssc Hmv Hoffall Hcs1).
      assert (listSatisfiable dlt3 cs0) as Hcs02.
      { apply (generate_constraints_mono_sem amb dlt3 sg
                 (List.map fst argts) (List.map fst argt)
                 ckty ckt (fst rstty) (fst rstty2) outs outs cs cs0
                 sti xst' stj y1);
          [exact (sig_good f sg Esg)
          |exact (sig_nodup_pipeline_local f sg Esg)
          | | | | | |exact Hcs|exact Hgc|exact Hcssat].
        - exact (call_subst_fresh_pipeline sg
                   (List.map fst argts) (List.map fst argt)
                   ckty ckt (fst rstty) (fst rstty2) outs outs
                   (sig_actuals_fresh f sg (List.map fst argts) ckty
                      (fst rstty) outs cs sti xst' Esg Hcs)
                   (sig_actuals_fresh f sg (List.map fst argt) ckt
                      (fst rstty2) outs cs0 stj y1 Esg Hgc)).
        - rewrite Forall2_map_1, Forall2_map_2. exact Hrelargs.
        - rewrite Hckeq. exact (satisfiable_merge_r dlt3 amb ckty).
        - exact Hrelrst.
        - exact Hpairs. }

      exists dlt3. split; [exact Hoffall|split].
      - apply listSatisfiable_app. split; [rewrite Hce0'; exact Hcs02|].
        apply listSatisfiable_app. split.
        + exact (listSatisfiable_off_scope ce1
                   (scope ++ moved_by st sta) (moved_by sta st1) dlt1 dlt3
                   Hscope1 Hsep1all Hoff1all Hce1').
        + apply listSatisfiable_app. split.
          * assert (forall y, In y (moved_by stb st1) ->
                      ~ In y ((scope ++ moved_by st sta) ++ moved_by sta stb))
              as Hsep3.
            { intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
              - apply in_app_or in Hin as [Hin|Hin].
                + apply (Hmv y); [|exact Hin].
                  apply (eq_moved_by_suffix st stb st1 Hf0b). exact Hy.
                + exact (eq_moved_by_disjoint st sta st1 y Hin
                           (eq_moved_by_suffix sta stb st1 Hfb y Hy)).
              - exact (eq_moved_by_disjoint sta stb st1 y Hin Hy). }
            exact (listSatisfiable_off_scope ce2
                     ((scope ++ moved_by st sta) ++ moved_by sta stb)
                     (moved_by stb st1) dlt2 dlt3
                     Hscope2 Hsep3 Hoff3 Hce2').
          * exact Hce3'.
      - apply Forall_app. split.
        + rewrite Hce0'.
          assert (incl (scope ++ moved_by st stb)
                       (scope ++ moved_by st st1)) as Hincb1.
          { apply incl_app.
            - exact (@incl_appl ident scope (moved_by st st1) scope
                       (incl_refl scope)).
            - apply incl_appr. exact (eq_moved_by_prefix st stb st1 Hfc). }
          assert (Forall
                    (st_scoped (scope ++ moved_by st st1))
                    (List.map fst argt)) as Hinpsc.
          { rewrite Forall_map.
            exact (@Forall_impl LST
                     (fun t => st_scoped (scope ++ moved_by st stb) (fst t))
                     (fun t => st_scoped (scope ++ moved_by st st1) (fst t))
                     (fun t Ht => st_scoped_weaken
                        (scope ++ moved_by st stb) (scope ++ moved_by st st1)
                        (fst t) Hincb1 Ht) argt Hsc_argt). }
          assert (st_scoped (scope ++ moved_by st st1) ckt) as Hclksc.
          { rewrite Hckeq.
            exact (st_scoped_weaken scope (scope ++ moved_by st st1) ckty
                     (@incl_appl ident scope (moved_by st st1) scope
                        (incl_refl scope))
                     (clk_types_scoped (find_base_clock (clocksof args))
                        ckty Hck)). }
          assert (Forall (fun b => In b (scope ++ moved_by st st1)) outs)
            as Houtsc.
          { exact (@Forall_impl ident (fun b => In b scope)
                     (fun b => In b (scope ++ moved_by st st1))
                     (fun b Hb => in_or_app scope (moved_by st st1) b
                                    (or_introl Hb)) outs Houtssc). }
          exact (generate_constraints_scoped sg (scope ++ moved_by st st1)
                   (List.map fst argt) ckt (fst rstty2) outs cs0 stj y1
                   (sig_scoped f sg Esg) Hinpsc Hclksc Hscrst' Houtsc Hgc).
        + apply Forall_app. split.
          * assert (incl (scope ++ moved_by st sta)
                          (scope ++ moved_by st st1)) as Hinc1f.
            { apply incl_app.
              - exact (@incl_appl ident scope (moved_by st st1) scope
                         (incl_refl scope)).
              - apply incl_appr.
                exact (eq_moved_by_prefix st sta st1 Hfa1). }
            exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st sta))
                     (constraint_scoped (scope ++ moved_by st st1))
                     (fun cc Hcc => constraint_scoped_incl
                        (scope ++ moved_by st sta) (scope ++ moved_by st st1)
                        cc Hinc1f Hcc) ce1 Hscope1).
          * apply Forall_app. split.
            -- assert (incl ((scope ++ moved_by st sta) ++ moved_by sta stb)
                              (scope ++ moved_by st st1)) as Hinc2f.
               { apply incl_app.
                 - apply incl_app.
                   + exact (@incl_appl ident scope (moved_by st st1) scope
                              (incl_refl scope)).
                   + apply incl_appr.
                     exact (eq_moved_by_prefix st sta st1 Hfa1).
                 - apply incl_appr. apply incl_tran
                     with (m := moved_by sta st1).
                   + exact (eq_moved_by_prefix sta stb st1 Hfc).
                   + exact (eq_moved_by_suffix st sta st1 Hfa). }
               exact (@Forall_impl constraint
                        (constraint_scoped
                           ((scope ++ moved_by st sta) ++ moved_by sta stb))
                        (constraint_scoped (scope ++ moved_by st st1))
                        (fun cc Hcc => constraint_scoped_incl
                           ((scope ++ moved_by st sta) ++ moved_by sta stb)
                           (scope ++ moved_by st st1) cc Hinc2f Hcc)
                        ce2 Hscope2).
            -- assert (incl (scope ++ moved_by stb st1)
                              (scope ++ moved_by st st1)) as Hinc3f.
               { apply incl_app.
                 - exact (@incl_appl ident scope (moved_by st st1) scope
                            (incl_refl scope)).
                 - apply incl_appr.
                   exact (eq_moved_by_suffix st stb st1 Hf0b). }
               exact (@Forall_impl constraint
                        (constraint_scoped (scope ++ moved_by stb st1))
                        (constraint_scoped (scope ++ moved_by st st1))
                        (fun cc Hcc => constraint_scoped_incl
                           (scope ++ moved_by stb st1)
                           (scope ++ moved_by st st1) cc Hinc3f Hcc)
                        ce3 Hscope3).
    Qed.




    (** * One equation, either way

        The two equation rules, packaged.  [eqn_covered] names the shapes the
        generator's own rules cover: a right-hand side with no call in it, or
        a single call whose reset the call rule accepts. *)

    Lemma sec_of_scoped :
      forall ys b, In b (sec_of ys) -> In b scope.
    Proof.
      intros ys b Hb. unfold sec_of in Hb.
      apply in_flat_map in Hb as (x & _ & Hbx).
      destruct (Env.find x env) as [b0|] eqn:Hf; [|contradiction].
      destruct Hbx as [Hbx|[]]; subst b0.
      exact (env_range_scoped x b Hf).
    Qed.

    Lemma Permutation_swap3 :
      forall (A B C : list ident), Permutation (A ++ B ++ C) (B ++ A ++ C).
    Proof.
      intros A B C. rewrite !app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    Qed.

    Lemma NoDup_drop_middle :
      forall (A B C : list ident), NoDup (A ++ B ++ C) -> NoDup (A ++ C).
    Proof.
      intros A B C H.
      assert (NoDup (B ++ A ++ C)) as Hswap
        by exact (Permutation_NoDup (Permutation_swap3 A B C) H).
      exact (@NoDup_app_r ident B (A ++ C) Hswap).
    Qed.

    Lemma vars_defined_cons_eq :
      forall (eq : equation) eqs,
        vars_defined (eq :: eqs) = fst eq ++ vars_defined eqs.
    Proof. intros (xs, es) eqs. reflexivity. Qed.

    Definition eqn_covered (eq : equation) : Prop :=
      Forall (fun e => match e with
                       | Eapp _ _ _ _ => False
                       | _ => True
                       end) (snd eq)
      \/ (exists f args er anns, snd eq = [Eapp f args er anns]).

    Definition eqn_carries (P : global) (eq : equation) : Prop :=
      forall eqs' st st' ce xst xst' cet yst yst' dlt,
        wl_equation P eq -> wc_equation P vars eq ->
        NoDup (vars_defined eqs' ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined eqs') -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of (fst eq)) -> satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        unnest_equation P eq st = (eqs', st') ->
        generate_leqn_constraint GL env base_ty rst_ty cenv eq xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.

    Lemma eqn_carries_covered :
      forall P eq, eqn_covered eq -> eqn_carries P eq.
    Proof.
      intros P (xs, es) Hcov
        eqs' st st' ce xst xst' cet yst yst' dlt
        Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.
      unfold eqn_covered in Hcov. simpl in Hcov, Hbs0.
      destruct Hwl as (Hwles & Hlen).
      destruct Hwc as (Hwces & _ & _).
      destruct Hcov as [Hne|(f & args & er & anns & Hes)].
      - exact (eqn_carries_plain P xs es eqs' st st' ce xst xst'
                 cet yst yst' dlt Hne Hwles Hwces Hlen Hnd Hmv Hamb Hbs0
                 Hcesc Hun Hgen Hgent Hsat).
      - subst es.
        assert (List.length xs = List.length anns) as Hlen'.
        { rewrite Hlen. unfold annots. simpl.
          now rewrite app_nil_r. }
        assert (wl_exp P (Eapp f args er anns)) as Hwlapp by now inv Hwles.
        assert (wc_exp P vars (Eapp f args er anns)) as Hwcapp by now inv Hwces.
        exact (eqn_carries_call P xs f args er anns eqs' st st' ce
                 xst xst' cet yst yst' dlt Hwlapp Hwcapp Hlen' Hnd Hmv
                 Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat).
    Qed.

    (** * A right-hand side with several expressions on it

        Such an equation means the conjunction of the equations its split
        produces, and that is how the rule types it: chunk by chunk, each
        chunk by the rule its own expression asks for.  Unnesting produces
        exactly those chunks' equations -- but in a different order, every
        split equation before every auxiliary one, where the rule
        interleaves them.  The two are reconciled by
        [state_pure_generate_leqns]: what an emitted equation generates does
        not depend on the state it is generated at, so the one run over the
        emitted list can be cut into its four pieces and put back together
        two at a time. *)

    Lemma skipn_nil_any : forall (A : Type) n, @skipn A n [] = [].
    Proof. intros A n. destruct n; reflexivity. Qed.

    Lemma skipn_skipn_add : forall (A : Type) n m (l : list A),
        skipn n (skipn m l) = skipn (m + n) l.
    Proof.
      intros A n m. revert n.
      induction m as [|m IH]; intros n l; [reflexivity|].
      destruct l as [|a l]; simpl; [apply skipn_nil_any|apply IH].
    Qed.

    Lemma skipn_firstn_sub : forall (A : Type) n m (l : list A),
        skipn n (firstn m l) = firstn (m - n) (skipn n l).
    Proof.
      intros A n. induction n as [|n IH]; intros m l.
      - simpl. f_equal. lia.
      - destruct m as [|m]; simpl; [reflexivity|].
        destruct l as [|a l]; simpl; [|apply IH].
        destruct (m - n); reflexivity.
    Qed.

    Lemma skipn_length_any : forall (A : Type) n (l : list A),
        List.length (skipn n l) = List.length l - n.
    Proof.
      intros A n. induction n as [|n IH]; intros l;
        [simpl; lia|destruct l as [|a l]; simpl; [reflexivity|apply IH]].
    Qed.

    Lemma In_firstn_any : forall (A : Type) n (l : list A) x,
        In x (firstn n l) -> In x l.
    Proof.
      intros A n l x H. rewrite <- (firstn_skipn n l).
      apply in_or_app. now left.
    Qed.

    Lemma In_skipn_any : forall (A : Type) n (l : list A) x,
        In x (skipn n l) -> In x l.
    Proof.
      intros A n l x H. rewrite <- (firstn_skipn n l).
      apply in_or_app. now right.
    Qed.

    Lemma combine_for_numstreams_app :
      forall (B : Type) (es1 es2 : list exp) (l : list B),
        combine_for_numstreams (es1 ++ es2) l
        = combine_for_numstreams es1 (firstn (List.length (annots es1)) l)
          ++ combine_for_numstreams es2
               (skipn (List.length (annots es1)) l).
    Proof.
      intros B es1. induction es1 as [|e es1 IH]; intros es2 l; [reflexivity|].
      assert (List.length (annots (e :: es1))
              = numstreams e + List.length (annots es1)) as Hl.
      { unfold annots. simpl. rewrite app_length.
        now rewrite length_annot_numstreams. }
      simpl ((e :: es1) ++ es2).
      cbn [combine_for_numstreams]. rewrite Hl, IH.
      rewrite firstn_firstn, min_l by lia.
      rewrite skipn_firstn_sub.
      assert (numstreams e + List.length (annots es1) - numstreams e
              = List.length (annots es1)) as Hsub by lia.
      rewrite Hsub.
      now rewrite <- skipn_skipn_add.
    Qed.

    Lemma split_equation_app :
      forall xs es1 es2,
        split_equation (xs, es1 ++ es2)
        = split_equation (firstn (List.length (annots es1)) xs, es1)
          ++ split_equation (skipn (List.length (annots es1)) xs, es2).
    Proof.
      intros xs es1 es2. unfold split_equation.
      now rewrite combine_for_numstreams_app, map_app.
    Qed.

    Lemma generate_leqns_constraints_app_intro :
      forall eqs1 eqs2 ce1 ce2 xst xst1 xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs1 xst
          = OK (ce1, xst1) ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst1
          = OK (ce2, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv (eqs1 ++ eqs2) xst
          = OK (ce1 ++ ce2, xst').
    Proof.
      induction eqs1 as [|eq eqs1 IH]; intros eqs2 ce1 ce2 xst xst1 xst' H1 H2.
      - apply generate_leqns_constraints_nil in H1 as (? & ?); subst.
        simpl. exact H2.
      - rewrite generate_leqns_constraints_cons in H1.
        apply sec_bind_inv in H1 as (c & s1 & Hc & H1).
        apply sec_bind_inv in H1 as (cs & s2 & Hcs & Hret).
        unfold SC.ret in Hret. inv Hret.
        simpl app. rewrite generate_leqns_constraints_cons.
        assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                  (eqs1 ++ eqs2) s1 = OK (cs ++ ce2, xst')) as Htail
          by exact (IH eqs2 cs ce2 s1 xst1 xst' Hcs H2).
        erewrite bind_OK by exact Hc.
        erewrite bind_OK by exact Htail.
        unfold SC.ret. now rewrite app_assoc.
    Qed.

    (** One chunk: a single expression bound to the variables that its own
        streams fill.  This is [eqn_carries_covered] for a one-expression
        right-hand side, taking the clocking of the expression rather than
        of the equation, which is all either rule uses. *)
    Lemma eqn_carries_one :
      forall (P : global) ys e eqs' st st' ce xst xst' cet yst yst' dlt,
        wl_exp P e -> wc_exp P vars e ->
        List.length ys = numstreams e ->
        NoDup (vars_defined eqs' ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined eqs') -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of ys) -> satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        unnest_equation P (ys, [e]) st = (eqs', st') ->
        generate_leqn_constraint GL env base_ty rst_ty cenv (ys, [e]) xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.
    Proof.
      intros P ys e eqs' st st' ce xst xst' cet yst yst' dlt
        Hwl Hwc Hlen Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.
      assert (List.length ys = List.length (annots [e])) as Hlena.
      { rewrite Hlen. unfold annots. simpl. rewrite app_nil_r.
        now rewrite length_annot_numstreams. }
      assert ((match e with Eapp _ _ _ _ => False | _ => True end) ->
              exists dlt',
                agree_off (moved_by st st') dlt dlt'
                /\ listSatisfiable dlt' cet
                /\ constraints_scoped (scope ++ moved_by st st') cet)
        as Hplain.
      { intro Hnotapp.
        assert (Forall (fun z => match z with
                       | Eapp _ _ _ _ => False | _ => True end) [e]) as Hne0.
        { constructor; [exact Hnotapp|constructor]. }
        assert (Forall (wl_exp P) [e]) as Hwl0.
        { constructor; [exact Hwl|constructor]. }
        assert (Forall (wc_exp P vars) [e]) as Hwc0.
        { constructor; [exact Hwc|constructor]. }
        exact (eqn_carries_plain P ys [e] eqs' st st' ce
                 xst xst' cet yst yst' dlt Hne0 Hwl0 Hwc0 Hlena Hnd
                 Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat). }
      destruct e as [| | | | | | | | |f args er anns];
        try (apply Hplain; exact I).
      assert (List.length ys = List.length anns) as Hlencall.
      { simpl in Hlen. exact Hlen. }
      exact (eqn_carries_call P ys f args er anns eqs' st st' ce
               xst xst' cet yst yst' dlt Hwl Hwc Hlencall Hnd Hmv Hamb
               Hbs0 Hcesc Hun Hgen Hgent Hsat).
    Qed.

    Lemma eqn_carries_split :
      forall (P : global) es xs eqs' st st' ce xst xst' cet yst yst' dlt,
        Forall (wl_exp P) es ->
        Forall (wc_exp P vars) es ->
        List.length xs = List.length (annots es) ->
        NoDup (vars_defined eqs' ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        (forall x ck ckty,
            In x (vars_defined eqs') -> find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        (forall b, In b (sec_of xs) -> satisfiable dlt amb [b]) ->
        constraints_scoped scope ce ->
        unnest_equation P (xs, es) st = (eqs', st') ->
        generate_lsplit_constraints GL env base_ty rst_ty cenv xs es xst
          = OK (ce, xst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs' yst
          = OK (cet, yst') ->
        listSatisfiable dlt ce ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' cet
          /\ constraints_scoped (scope ++ moved_by st st') cet.
    Proof.
      intros P es. induction es as [|e es IH];
        intros xs eqs' st st' ce xst xst' cet yst yst' dlt
          Hwles Hwces Hlen Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.
      - (** nothing on the right: nothing emitted, nothing generated *)
        apply unnest_equation_inv in Hun
          as (es1 & eqs1 & ess & eqss & Hmap & ? & ? & ?); subst.
        apply map_bind2_unnest_rhs_nil in Hmap as (? & ? & ?); subst.
        simpl List.concat in *. simpl app in *.
        apply generate_leqns_constraints_nil in Hgent as (? & ?); subst.
        exists dlt. split; [apply agree_off_refl|split; constructor].
      - inversion Hwles as [|ea esa Hwle Hwlr]; subst.
        inversion Hwces as [|eb esb Hwce Hwcr]; subst.
        apply unnest_equation_inv in Hun
          as (es1 & eqs1 & ess & eqss & Hmap & ? & ? & ?); subst.
        apply map_bind2_unnest_rhs_cons in Hmap
          as (esh & eqh & s1 & esr & eqr & Hunh & Hunr & ? & ?); subst.
        simpl List.concat in *.

        assert (List.length (annots esh) = numstreams e) as Hnh.
        { erewrite unnest_rhs_annot; [|exact Hwle|exact Hunh].
          apply length_annot_numstreams. }
        assert (List.length (annots (e :: es))
                = numstreams e + List.length (annots es)) as Hlsum.
        { unfold annots. simpl. rewrite app_length.
          now rewrite length_annot_numstreams. }

        (** the target equations, chunked *)
        rewrite split_equation_app, Hnh in Hnd, Hamb, Hgent.
        rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (ceh & xsth & Hgenh & Hgen).
        apply sec_bind_inv in Hgen as (cer & xstr & Hgenr & Hret).
        unfold SC.ret in Hret. inv Hret.
        rewrite generate_lone_is_leqn in Hgenh.
        apply listSatisfiable_app in Hsat as (Hsath & Hsatr).
        apply Forall_app in Hcesc as (Hcesch & Hcescr).

        (** the head chunk is an equation in its own right *)
        assert (unnest_equation P (firstn (numstreams e) xs, [e]) st
                = (split_equation (firstn (numstreams e) xs, esh) ++ eqh, s1))
          as Hunh'.
        { destruct (unnest_equation P (firstn (numstreams e) xs, [e]) st)
            as [eqsh sh] eqn:Hue.
          apply unnest_equation_inv in Hue
            as (u1 & u2 & uess & ueqss & Humap & ? & ? & ?); subst.
          apply map_bind2_unnest_rhs_cons in Humap
            as (ueh & ueq & us1 & uesr & ueqr & Huh & Hur & ? & ?); subst.
          apply map_bind2_unnest_rhs_nil in Hur as (? & ? & ?); subst.
          rewrite Hunh in Huh. inv Huh.
          simpl List.concat. now rewrite !app_nil_r. }
        assert (unnest_equation P (skipn (numstreams e) xs, es) s1
                = (split_equation (skipn (numstreams e) xs, List.concat esr)
                     ++ List.concat eqr, st')) as Hunr'.
        { destruct (unnest_equation P (skipn (numstreams e) xs, es) s1)
            as [eqsr sr] eqn:Hue.
          apply unnest_equation_inv in Hue
            as (u1 & u2 & uess & ueqss & Humap & ? & ? & ?); subst.
          rewrite Hunr in Humap. inv Humap. reflexivity. }

        assert (st_follows st s1) as Hf1
            by exact (unnest_equation_st_follows P
                        (firstn (numstreams e) xs, [e])
                        (split_equation (firstn (numstreams e) xs, esh) ++ eqh)
                        st s1 Hunh').
        assert (st_follows s1 st') as Hf2
            by exact (unnest_equation_st_follows P
                        (skipn (numstreams e) xs, es)
                        (split_equation
                           (skipn (numstreams e) xs, List.concat esr)
                           ++ List.concat eqr) s1 st' Hunr').
        assert (List.length (firstn (numstreams e) xs) = numstreams e)
          as HlenH by (rewrite firstn_length, Hlen, Hlsum; lia).
        assert (List.length (skipn (numstreams e) xs)
                = List.length (annots es)) as HlenT
            by (rewrite skipn_length_any, Hlen, Hlsum; lia).

        (** the target run, cut into its four pieces and reassembled *)
        assert (Forall (unnested_equation P)
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh))
          as HuneH.
        { assert (wl_equation P (firstn (numstreams e) xs, [e])) as HwleqH.
          { split; [repeat constructor; exact Hwle|].
            rewrite HlenH. unfold annots. simpl. rewrite app_nil_r.
            now rewrite length_annot_numstreams. }
          exact (unnest_equation_unnested_eq P
                   (firstn (numstreams e) xs, [e])
                   (split_equation (firstn (numstreams e) xs, esh) ++ eqh)
                   st s1 HwleqH Hunh'). }
        assert (Forall (unnested_equation P)
                  (split_equation (skipn (numstreams e) xs, List.concat esr)
                     ++ List.concat eqr)) as HuneT.
        { assert (wl_equation P (skipn (numstreams e) xs, es)) as HwleqT
            by exact (conj Hwlr HlenT).
          exact (unnest_equation_unnested_eq P
                   (skipn (numstreams e) xs, es)
                   (split_equation
                      (skipn (numstreams e) xs, List.concat esr)
                      ++ List.concat eqr) s1 st' HwleqT Hunr'). }
        apply Forall_app in HuneH as (HuneA1 & HuneB1).
        apply Forall_app in HuneT as (HuneA2 & HuneB2).

        apply generate_leqns_constraints_app in Hgent
          as (cA & cB & yA & HgA & HgB & ?); subst.
        apply generate_leqns_constraints_app in HgA
          as (cA1 & cA2 & yA1 & HgA1 & HgA2 & ?); subst.
        apply generate_leqns_constraints_app in HgB
          as (cB1 & cB2 & yB1 & HgB1 & HgB2 & ?); subst.
        destruct (state_pure_generate_leqns P _ HuneA1 _ yst _ _ HgA1)
          as (? & HgA1'); subst yA1.
        destruct (state_pure_generate_leqns P _ HuneA2 _ yst _ _ HgA2)
          as (? & HgA2'); subst yA.
        destruct (state_pure_generate_leqns P _ HuneB1 _ yst _ _ HgB1)
          as (? & HgB1'); subst yB1.
        destruct (state_pure_generate_leqns P _ HuneB2 _ yst _ _ HgB2)
          as (? & HgB2'); subst yst'.
        assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh) yst
                = OK (cA1 ++ cB1, yst)) as HgH
            by exact (generate_leqns_constraints_app_intro
                        (split_equation (firstn (numstreams e) xs, esh)) eqh
                        cA1 cB1 yst yst yst HgA1' HgB1').
        assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                  (split_equation (skipn (numstreams e) xs, List.concat esr)
                     ++ List.concat eqr) yst
                = OK (cA2 ++ cB2, yst)) as HgT
            by exact (generate_leqns_constraints_app_intro
                        (split_equation
                           (skipn (numstreams e) xs, List.concat esr))
                        (List.concat eqr) cA2 cB2 yst yst yst
                        HgA2' HgB2').

        (** the defined variables, chunked the same way *)
        assert (NoDup (vars_defined
                         (split_equation (firstn (numstreams e) xs, esh)
                            ++ eqh)
                       ++ vars_defined
                            (split_equation (skipn (numstreams e) xs,
                                             List.concat esr)
                               ++ List.concat eqr)
                       ++ st_ids st)) as Hnd'.
        { assert
            (Permutation
               (vars_defined
                  ((split_equation (firstn (numstreams e) xs, esh) ++
                    split_equation (skipn (numstreams e) xs,
                                    List.concat esr)) ++
                   eqh ++ List.concat eqr) ++ st_ids st)
               (vars_defined
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh) ++
                vars_defined
                  (split_equation (skipn (numstreams e) xs,
                                   List.concat esr) ++ List.concat eqr) ++
                st_ids st)) as Hperm.
          { rewrite !vars_defined_app.
            rewrite <- !app_assoc.
            exact
              (Permutation_app_head
                 (vars_defined
                    (split_equation (firstn (numstreams e) xs, esh)))
                 (Permutation_swap3
                    (vars_defined
                       (split_equation (skipn (numstreams e) xs,
                                        List.concat esr)))
                    (vars_defined eqh)
                    (vars_defined (List.concat eqr) ++ st_ids st))). }
          exact (@Permutation_NoDup ident _ _ Hperm Hnd). }
        assert (forall x,
                   In x (vars_defined
                           (split_equation (firstn (numstreams e) xs, esh)
                              ++ eqh)) ->
                   In x (vars_defined
                           ((split_equation (firstn (numstreams e) xs, esh)
                               ++ split_equation (skipn (numstreams e) xs,
                                                  List.concat esr))
                              ++ (eqh ++ List.concat eqr)))) as HinH.
        { intros x Hx.
          rewrite vars_defined_app in Hx.
          rewrite vars_defined_app.
          apply in_app_or in Hx as [Hx|Hx].
          - apply in_or_app. left.
            rewrite vars_defined_app. apply in_or_app. left. exact Hx.
          - apply in_or_app. right.
            rewrite vars_defined_app. apply in_or_app. left. exact Hx. }
        assert (forall x,
                   In x (vars_defined
                           (split_equation (skipn (numstreams e) xs,
                                            List.concat esr)
                              ++ List.concat eqr)) ->
                   In x (vars_defined
                           ((split_equation (firstn (numstreams e) xs, esh)
                               ++ split_equation (skipn (numstreams e) xs,
                                                  List.concat esr))
                              ++ (eqh ++ List.concat eqr)))) as HinT.
        { intros x Hx.
          rewrite vars_defined_app in Hx.
          rewrite vars_defined_app.
          apply in_app_or in Hx as [Hx|Hx].
          - apply in_or_app. left.
            rewrite vars_defined_app. apply in_or_app. right. exact Hx.
          - apply in_or_app. right.
            rewrite vars_defined_app. apply in_or_app. right. exact Hx. }

        (** the head *)
        edestruct (eqn_carries_one P (firstn (numstreams e) xs) e
                     (split_equation (firstn (numstreams e) xs, esh) ++ eqh)
                     st s1 ceh xst xsth (cA1 ++ cB1) yst yst dlt)
          as (dlt1 & Hoff1 & Hce1 & Hscope1).
        { exact Hwle. }
        { exact Hwce. }
        { exact HlenH. }
        { exact
            (NoDup_drop_middle
               (vars_defined
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh))
               (vars_defined
                  (split_equation (skipn (numstreams e) xs,
                                   List.concat esr) ++ List.concat eqr))
               (st_ids st) Hnd'). }
        { intros y Hy.
          exact (Hmv y (eq_moved_by_prefix st s1 st' Hf2 y Hy)). }
        { intros x ck ckty Hx. apply Hamb. now apply HinH. }
        { intros b Hb. apply Hbs0. unfold sec_of in *.
          apply in_flat_map in Hb as (x & Hx & Hbx). apply in_flat_map.
          exists x. split;
            [exact (In_firstn_any ident (numstreams e) xs x Hx)|exact Hbx]. }
        { exact Hcesch. }
        { exact Hunh'. }
        { exact Hgenh. }
        { exact HgH. }
        { exact Hsath. }

        (** and the rest *)
        assert (Permutation
                  (vars_defined
                     (split_equation (firstn (numstreams e) xs, esh) ++ eqh)
                     ++ st_ids st)
                  (firstn (numstreams e) xs ++ st_ids s1)) as Hp1'.
        { assert
            (wl_equation P (firstn (numstreams e) xs, [e])) as HwleqH.
          { split.
            - constructor; [exact Hwle|constructor].
            - simpl. rewrite app_nil_r, length_annot_numstreams.
              exact HlenH. }
          assert
            (Permutation
               (vars_defined
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh) ++
                st_ids st)
               (vars_defined [(firstn (numstreams e) xs, [e])] ++ st_ids s1))
            as Hunnestperm
            by exact
              (unnest_equation_vars_perm P
                 (firstn (numstreams e) xs, [e])
                 (split_equation (firstn (numstreams e) xs, esh) ++ eqh)
                 st s1 HwleqH Hunh').
          assert
            (Permutation
               (vars_defined [(firstn (numstreams e) xs, [e])] ++ st_ids s1)
               (firstn (numstreams e) xs ++ st_ids s1)) as Hsourceperm.
          { rewrite vars_defined_cons_eq. simpl. rewrite app_nil_r.
            reflexivity. }
          exact
            (@Permutation_trans ident
               (vars_defined
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh) ++
                st_ids st)
               (vars_defined [(firstn (numstreams e) xs, [e])] ++ st_ids s1)
               (firstn (numstreams e) xs ++ st_ids s1)
               Hunnestperm Hsourceperm). }
        edestruct (IH (skipn (numstreams e) xs)
                     (split_equation (skipn (numstreams e) xs,
                                      List.concat esr) ++ List.concat eqr)
                     s1 st' cer xsth xst' (cA2 ++ cB2) yst yst dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2).
        { exact Hwlr. }
        { exact Hwcr. }
        { exact HlenT. }
        { assert
            (NoDup
               (vars_defined
                  (split_equation (skipn (numstreams e) xs,
                                   List.concat esr) ++ List.concat eqr) ++
                vars_defined
                  (split_equation (firstn (numstreams e) xs, esh) ++ eqh) ++
                st_ids st)) as Hndswap
            by exact
              (@Permutation_NoDup ident _ _
                 (Permutation_swap3
                    (vars_defined
                       (split_equation (firstn (numstreams e) xs, esh) ++ eqh))
                    (vars_defined
                       (split_equation (skipn (numstreams e) xs,
                                        List.concat esr) ++ List.concat eqr))
                    (st_ids st)) Hnd').
          assert
            (NoDup
               (vars_defined
                  (split_equation (skipn (numstreams e) xs,
                                   List.concat esr) ++ List.concat eqr) ++
                firstn (numstreams e) xs ++ st_ids s1)) as Hndmapped
            by exact
              (@Permutation_NoDup ident _ _
                 (Permutation_app_head
                    (vars_defined
                       (split_equation (skipn (numstreams e) xs,
                                        List.concat esr) ++ List.concat eqr))
                    Hp1') Hndswap).
          exact
            (NoDup_drop_middle
               (vars_defined
                  (split_equation (skipn (numstreams e) xs,
                                   List.concat esr) ++ List.concat eqr))
               (firstn (numstreams e) xs) (st_ids s1) Hndmapped). }
        { intros y Hy.
          exact (Hmv y (eq_moved_by_suffix st s1 st' Hf1 y Hy)). }
        { intros x ck ckty Hx. apply Hamb. now apply HinT. }
        { intros b Hb.
          assert (In b (sec_of xs)) as Hb0.
          { unfold sec_of in *.
            apply in_flat_map in Hb as (x & Hx & Hbx). apply in_flat_map.
            exists x. split;
              [exact (In_skipn_any ident (numstreams e) xs x Hx)|exact Hbx]. }
          assert (forall y, In y amb -> ~ In y (moved_by st s1)) as Hamboff.
          { intros y Hy Hin.
            exact
              (Hmv y (eq_moved_by_prefix st s1 st' Hf2 y Hin)
                 (amb_scoped y Hy)). }
          assert (forall y, In y [b] -> ~ In y (moved_by st s1)) as Hboff.
          { intros y Hy Hin. destruct Hy as [Hy|[]]. subst y.
            exact
              (Hmv b (eq_moved_by_prefix st s1 st' Hf2 b Hin)
                 (sec_of_scoped xs b Hb0)). }
          exact
            (satisfiable_off amb [b] (moved_by st s1) dlt dlt1
               Hoff1 Hamboff Hboff (Hbs0 b Hb0)). }
        { exact Hcescr. }
        { exact Hunr'. }
        { exact Hgenr. }
        { exact HgT. }
        { assert (forall y, In y (moved_by st s1) -> ~ In y scope)
            as Hprefixfresh.
          { intros y Hy.
            exact (Hmv y (eq_moved_by_prefix st s1 st' Hf2 y Hy)). }
          exact
            (listSatisfiable_off scope cer (moved_by st s1) dlt dlt1
               Hcescr Hprefixfresh Hoff1 Hsatr). }

        assert (forall y, In y (moved_by s1 st') ->
                          ~ In y (scope ++ moved_by st s1)) as Hsep.
        { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
          - apply (Hmv y); [|exact Hy].
            apply (eq_moved_by_suffix st s1 st' Hf1). exact Hin.
          - exact (eq_moved_by_disjoint st s1 st' y Hy Hin). }
        assert (incl (scope ++ moved_by st s1)
                     (scope ++ moved_by st st')) as Hinc1.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_prefix st s1 st' Hf2). }
        assert (incl (scope ++ moved_by s1 st')
                     (scope ++ moved_by st st')) as Hinc2.
        { apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. exact (eq_moved_by_suffix st s1 st' Hf1). }

        (** the two halves, put back in the order the run produced *)
        apply listSatisfiable_app in Hce2 as (HceA2 & HceB2).
        assert (listSatisfiable dlt2 (cA1 ++ cB1)) as Hce1'
            by exact
              (listSatisfiable_off_scope (cA1 ++ cB1)
                 (scope ++ moved_by st s1) (moved_by s1 st') dlt1 dlt2
                 Hscope1 Hsep Hoff2 Hce1).
        apply listSatisfiable_app in Hce1' as (HceA1 & HceB1).
        apply Forall_app in Hscope1 as (HscA1 & HscB1).
        apply Forall_app in Hscope2 as (HscA2 & HscB2).

        exists dlt2. split; [|split].
        + exact
            (agree_off_trans (moved_by st st') dlt dlt1 dlt2
               (agree_off_incl (moved_by st s1) (moved_by st st') dlt dlt1
                  (eq_moved_by_prefix st s1 st' Hf2) Hoff1)
               (agree_off_incl (moved_by s1 st') (moved_by st st') dlt1 dlt2
                  (eq_moved_by_suffix st s1 st' Hf1) Hoff2)).
        + apply listSatisfiable_app. split;
            [apply listSatisfiable_app; split; assumption|].
          apply listSatisfiable_app. split; assumption.
        + apply Forall_app. split; [apply Forall_app; split|
                                    apply Forall_app; split].
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st s1))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st s1) (scope ++ moved_by st st')
                        c Hinc1 Hc) cA1 HscA1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by s1 st'))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by s1 st') (scope ++ moved_by st st')
                        c Hinc2 Hc) cA2 HscA2).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by st s1))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by st s1) (scope ++ moved_by st st')
                        c Hinc1 Hc) cB1 HscB1).
          * exact (@Forall_impl constraint
                     (constraint_scoped (scope ++ moved_by s1 st'))
                     (constraint_scoped (scope ++ moved_by st st'))
                     (fun c Hc => constraint_scoped_incl
                        (scope ++ moved_by s1 st') (scope ++ moved_by st st')
                        c Hinc2 Hc) cB2 HscB2).
    Qed.

    Lemma eqn_carries_all : forall P eq, eqn_carries P eq.
    Proof.
      intros P (xs, es).
      destruct es as [|e [|e2 es2]].
      - apply eqn_carries_covered. left. constructor.
      - apply eqn_carries_covered.
        destruct e as [c | x a | op e a | op e1 e2 a
                      | es0 es1 anns | es0 es1 anns | es x b a
                      | x es0 es1 a | e es0 es1 a | f args er anns];
          try (left; repeat constructor; exact I).
        right. exists f, args, er, anns. reflexivity.
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          [|apply eqn_carries_covered; left; now apply has_lcall_false_inv].
        intros eqs' st st' ce xst xst' cet yst yst' dlt
          Hwl Hwc Hnd Hmv Hamb Hbs0 Hcesc Hun Hgen Hgent Hsat.
        destruct Hwl as (Hwles & Hlen).
        destruct Hwc as (Hwces & _ & _).
        rewrite gen_leqn_split in Hgen by exact Hh.
        exact
          (eqn_carries_split P (e :: e2 :: es2) xs eqs' st st' ce xst xst'
             cet yst yst' dlt Hwles Hwces Hlen Hnd Hmv Hamb Hbs0 Hcesc
             Hun Hgen Hgent Hsat).
    Qed.


  End Preservation.

End SecLusUnnestingEquations.
