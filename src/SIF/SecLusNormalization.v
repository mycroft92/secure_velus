(** Programs typed against the naming of a larger program.

    The pipeline types the source program, the unnested one and the
    normalised one against a single naming pass -- the normalised program's,
    because it declares the most variables.  The fold facts of
    [SecLusTypingCorrectness.v] assume a node is typed against an environment
    that declares exactly its own variables; a node of a smaller program meets
    an environment with extra keys.  This file redoes the facts that read the
    environment's whole range ([signature_scoped], rootedness) against the
    node's own variables, guarded by clocking, and assembles the program-level
    lockstep and node-level instantiation of the two preservation legs. *)

From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Lia.
From Coq Require Import Sorting.Permutation.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import Lustre.Normalization.NormFby.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.NClocking.
From Velus Require Import Lustre.Normalization.NTyping.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
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
From Velus Require Import SIF.SecNamingTotality.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLNamingTotality.
From Velus Require Import SIF.SecLusNormFby.
From Velus Require Import SIF.SecLusTypingCorrectness.

From compcert Require Import common.Errors.

Module SecLusNormalization
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
  (Mem            : MEMORIES Ids Op CESyn NLSyn)
  (IsD            : ISDEFINED Ids Op CESyn NLSyn Mem)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
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
  (Caus           : LCAUSALITY Ids Op LSyn)
  (Import Typ     : LTYPING Ids Op LSyn)
  (Import Norm    : NORMALIZATION Ids Op OpAux LSyn Caus)
  (Import SECLNG  : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (Import SECNT   : SECNAMINGTOTALITY Ids Op CESyn NLSyn Mem IsD NLOrd NAMEGEN)
  (Import LOrd    : LORDERED Ids Op LSyn)
  (Import SECLNT  : SECLNAMINGTOTALITY Ids Op OpAux LSyn CESyn NLSyn Mem IsD
                      NLOrd NAMEGEN TR SECLNG SECNT LOrd)
.

Module UNN := Norm.Unnesting.
Module NF := Norm.NormFby.
Module NClo := NClockingFun Ids Op OpAux LSyn Caus LClo Norm.
Module NTyp := NTypingFun Ids Op OpAux LSyn Caus Typ Norm.

Module TC := SecLusTypingCorrectness Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn
               Mem IsD NLOrd STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN NF
               SECLNG SECNT LOrd SECLNT.
Include TC.

Import SECMONADNotations.

  Lemma res_to_sec_inv_ok :
    forall {A : Type} (r : res A) st a st',
      res_to_sec r st = OK (a, st') -> r = OK a /\ st' = st.
  Proof.
    intros A r st a st' H. unfold res_to_sec in H.
    destruct r as [a0|e]; [|discriminate H].
    inversion H; subst. split; reflexivity.
  Qed.

  (** * The equation level of the dichotomy, guarded by clocking

      [generate_leqns_constraints_scoped] asks for [exps_scoped_in S] and
      [clk_scoped S], which speak about every expression and every clock the
      environment can type.  Against an environment with extra keys neither
      holds, so the same induction is run with both guarded: the expressions
      are well clocked in [vars], and a clock is one the rules actually
      meet -- the base clock of a call's arguments, the clock of a reset, or
      the declared clock of a declared variable. *)

  Section GuardedScoped.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable P       : global.
    Variable vars    : list (ident * clock).
    Variable AN      : list ident.

    Definition exps_scoped_wc (S : list ident) : Prop :=
      (forall e ts s0 s1,
          wc_exp P vars e ->
          src_exp vars AN e ->
          incl (tgt_names (carried ts)) S ->
          assign_lexp_type G env base_ty rst_ty e s0 = OK (ts, s1) ->
          Forall (fun t => st_scoped S (fst t)) ts
          /\ constraints_scoped S (carried ts))
      /\ (forall es ts s0 s1,
             Forall (wc_exp P vars) es ->
             Forall (src_exp vars AN) es ->
             incl (tgt_names (carried ts)) S ->
             assign_lexps G env base_ty rst_ty es s0 = OK (ts, s1) ->
             Forall (fun t => st_scoped S (fst t)) ts
             /\ constraints_scoped S (carried ts)).

    (** A clock the rules meet is a declared variable's clock, or the base
        clock of a call's arguments, or a reset's.  The names in the last two
        may be nested calls' results, whose security names are targets of what
        the arguments carry; so the scoping is relative to the arguments' run,
        and to a scope that contains the targets it carried. *)
    Definition clk_scoped_wc (ckenv : Env.t (type * clock))
        (S : list ident) : Prop :=
      forall es ck ckty argts s s1,
        Forall (wc_exp P vars) es ->
        (clk_src vars es ck \/
         exists x, In x (List.map fst vars) /\ find_clock ckenv x = OK ck) ->
        incl (tgt_names (carried argts)) S ->
        assign_lexps G env base_ty rst_ty es s = OK (argts, s1) ->
        assign_clk_type env base_ty ck = Some ckty ->
        st_scoped S ckty.

    Lemma assign_lexps_nil_ok :
      forall s, assign_lexps G env base_ty rst_ty [] s = OK ([], s).
    Proof. intros s. rewrite assign_lexps_nil. reflexivity. Qed.

    Lemma assign_lexps_single_ok :
      forall e s ts s1,
        assign_lexp_type G env base_ty rst_ty e s = OK (ts, s1) ->
        assign_lexps G env base_ty rst_ty [e] s = OK (ts, s1).
    Proof.
      intros e s ts s1 H. rewrite assign_lexps_cons, assign_lexps_nil.
      cbn. unfold SC.bind, SC.ret. rewrite H. cbn. rewrite app_nil_r.
      reflexivity.
    Qed.

    Lemma generate_lvars_constraints_scoped_tgt_wc :
      forall S ckenv xs bs ts c s s',
        clk_scoped_wc ckenv S ->
        incl xs (List.map fst vars) ->
        In rst_ty S ->
        incl bs S ->
        Forall (fun t => st_scoped S (fst t)) ts ->
        constraints_scoped S (carried ts) ->
        generate_lvars_constraints env base_ty rst_ty ckenv xs bs ts s
          = OK (c, s') ->
        constraints_scoped S c.
    Proof.
      intros S ckenv xs. induction xs as [|x xs IH];
        intros bs ts c s s' Hclk Hxv Hrs Hbs Hfs Hcs Hgen.
      - destruct bs as [|b bs]; destruct ts as [|t ts];
          cbn in Hgen; try discriminate.
        unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst c.
        constructor.
      - destruct bs as [|b bs]; [destruct ts; cbn in Hgen; discriminate|].
        destruct ts as [|t ts]; [cbn in Hgen; discriminate|].
        rewrite carried_cons in Hcs.
        apply cscoped_cmerge_inv in Hcs as (Hct & Hctr).
        inversion Hfs as [|? ? Hft Hfr]; subst.
        rewrite gen_lvars_cons_eq in Hgen.
        apply sec_bind_inv in Hgen as (ckty & s1 & Hck & Hgen).
        apply sec_bind_inv in Hgen as (rest & s2 & Hr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hc & _); subst c.
        apply cscoped_app.
        + unfold lconstrain. apply cscoped_cmerge.
          * apply cscoped_one; [|intros y [Hy|[]]; subst y; apply Hbs; now left].
            rewrite fst_ljoin. unfold ambient.
            rewrite fst_ljoin, fst_lvar.
            apply st_scoped_merge; [|exact Hft].
            apply st_scoped_merge;
              [intros y [Hy|[]]; subst y; exact Hrs|].
            unfold eqn_clock_type in Hck.
            apply sec_bind_inv in Hck as (ck & sa & Hfc & Hck).
            apply option_to_sec_inv in Hck as (Hck & _).
            apply res_to_sec_inv_ok in Hfc as (Hfc & _).
            exact (Hclk [] ck ckty [] s s (Forall_nil _)
                     (or_intror (ex_intro _ x
                        (conj (Hxv x (or_introl (@Logic.eq_refl _ x))) Hfc)))
                     (fun y Hy => match Hy with end)
                     (assign_lexps_nil_ok s) Hck).
          * rewrite snd_ljoin. unfold ambient.
            rewrite snd_ljoin, snd_lvar. cbn [snd].
            rewrite cmerge_nil, cmerge_nil2. exact Hct.
        + eapply IH;
            [exact Hclk| |exact Hrs| |exact Hfr|exact Hctr|exact Hr].
          * intros y Hy. apply Hxv. now right.
          * intros y Hy. apply Hbs. now right.
    Qed.

    Lemma generate_ldef_constraint_scoped_wc :
      forall S ckenv x e cs s s',
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        wc_exp P vars e ->
        src_exp vars AN e ->
        In x (List.map fst vars) ->
        incl (CALLS.sec_of env [x]) S ->
        incl (tgt_names cs) S ->
        generate_ldef_constraint G env base_ty rst_ty ckenv x e s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv x e cs s s' Hclk Hrs (Hexp & _) Hwce Hsx Hxv Hxs Htc Hgen.
      apply generate_ldef_constraint_inv in Hgen
        as (ck & ckty & tf & b & s1 & Hfc & Hck & Hte & Hb & Hs1 & Hcs).
      subst s1.
      assert (incl (tgt_names (carried [tf])) S) as Hci.
      { rewrite carried_single. eapply incl_tran; [|exact Htc].
        apply tgt_names_incl_of_In. intros cc Hcc. rewrite Hcs.
        apply (proj2 (cmerge_In _ _ cc)). now right. }
      destruct (Hexp e [tf] s s' Hwce Hsx Hci Hte) as (Hft & Hct).
      rewrite carried_single in Hct. rewrite Hcs.
      inversion Hft as [|? ? Hf1 ?]; subst.
      apply cscoped_cmerge; [|exact Hct].
      apply cscoped_one; [|intros y [Hy|[]]; subst y].
      - apply st_scoped_merge; [|exact Hf1].
        apply st_scoped_merge;
          [intros y [Hy|[]]; subst y; exact Hrs|].
        exact (Hclk [] ck ckty [] s s (Forall_nil _)
                 (or_intror (ex_intro _ x (conj Hxv Hfc)))
                 (fun y Hy => match Hy with end)
                 (assign_lexps_nil_ok s) Hck).
      - apply Hxs. unfold CALLS.sec_of. cbn [flat_map].
        rewrite Hb. now left.
    Qed.

    Lemma generate_lgen_constraint_scoped_wc :
      forall S ckenv xs es cs s s',
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        Forall (wc_exp P vars) es ->
        Forall (src_exp vars AN) es ->
        incl xs (List.map fst vars) ->
        incl (CALLS.sec_of env xs) S ->
        incl (tgt_names cs) S ->
        generate_lgen_constraint G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv xs es cs s s' Hclk Hrs (_ & Hexps) Hwces Hsxs Hxv Hxs Htc Hgen.
      unfold generate_lgen_constraint in Hgen.
      apply sec_bind_inv in Hgen as (ts & s1 & Hts & Hgen).
      apply sec_bind_inv in Hgen as (bs & s2 & Hbs & Hlv).
      apply option_to_sec_inv in Hbs as (Hbs & ?); subst s2.
      assert (s' = s1) as ?
          by (destruct (state_pure_generate_lvars_constraints env base_ty
                          rst_ty ckenv xs bs ts s1 s1 _ _ Hlv) as (Hp & _);
              exact Hp).
      subst s'.
      assert (incl (tgt_names (carried ts)) S) as Hci.
      { eapply incl_tran; [|exact Htc]. apply tgt_names_incl_of_In.
        intros cc Hcc.
        exact (generate_lvars_constraints_carried_in env base_ty rst_ty ckenv
                 xs bs ts cs s1 s1 Hlv cc Hcc). }
      destruct (Hexps es ts s s1 Hwces Hsxs Hci Hts) as (Hfs & Hcs).
      eapply generate_lvars_constraints_scoped_tgt_wc;
        [exact Hclk|exact Hxv|exact Hrs| |exact Hfs|exact Hcs|exact Hlv].
      assert (Forall2 (fun x b => Env.find x env = Some b) xs bs) as Hf2
          by (eapply (get_mappings_Forall2 env xs bs); exact Hbs).
      rewrite <- (Forall2_sec_of env xs bs Hf2). exact Hxs.
    Qed.

    Lemma generate_lcall_constraint_scoped_wc :
      forall S ckenv xs f es rstty cs s s',
        secglobal_scoped G ->
        clk_scoped_wc ckenv S ->
        exps_scoped_wc S ->
        Forall (wc_exp P vars) es ->
        Forall (src_exp vars AN) es ->
        Forall (nested_src vars AN) es ->
        incl (CALLS.sec_of env xs) S ->
        st_scoped S (fst rstty) ->
        constraints_scoped S (snd rstty) ->
        incl (tgt_names cs) S ->
        generate_lcall_constraint G env base_ty rst_ty xs f es rstty s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv xs f es rstty cs s s' Hsg Hclk (_ & Hexps) Hwces Hsxs Hnsx Hxs
        Hfr Hcr Htc Hgen.
      apply generate_lcall_constraint_inv in Hgen
        as (sg & ckty & argts & outs & sti & cs0
            & Esg & Hck & Hargs & Houts & Hgc & Hcs).
      assert (s' = sti) as ?
          by (destruct (state_pure_generate_constraints sg
                          (List.map fst argts) ckty (fst rstty) outs
                          sti sti _ _ Hgc) as (Hp & _); exact Hp).
      subst s'.
      assert (incl (tgt_names (carried argts)) S) as Hci.
      { eapply incl_tran; [|exact Htc]. apply tgt_names_incl_of_In.
        intros cc Hcc. rewrite Hcs.
        apply (proj2 (cmerge_In _ _ cc)). right.
        apply (proj2 (cmerge_In _ _ cc)). now left. }
      destruct (Hexps es argts s sti Hwces Hsxs Hci Hargs) as (Hfa & Hca).
      assert (Forall2 (fun x b => Env.find x env = Some b) xs outs) as Hf2
          by (eapply CALLS.mmap_find_env_Forall2; exact Houts).
      rewrite Hcs. apply cscoped_cmerge; [|apply cscoped_cmerge].
      - eapply generate_constraints_scoped;
          [exact (Hsg _ _ Esg)| |
           exact (Hclk es _ _ argts s sti Hwces
                    (or_introl (clk_src_base vars es)) Hci Hargs Hck)
          |exact Hfr| |exact Hgc].
        + apply Forall_forall. intros X HX.
          apply in_map_iff in HX as (t & Ht & Htin); subst X.
          rewrite Forall_forall in Hfa. exact (Hfa t Htin).
        + apply Forall_forall. intros d Hd. apply Hxs.
          exact (eq_ind_r (fun l => In d l) Hd
                   (Forall2_sec_of env xs outs Hf2)).
      - exact Hca.
      - exact Hcr.
    Qed.

    Lemma generate_lone_constraint_scoped_wc :
      forall S ckenv ys e cs s s',
        secglobal_scoped G ->
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        wc_exp P vars e ->
        src_exp vars AN e ->
        incl ys (List.map fst vars) ->
        incl (CALLS.sec_of env ys) S ->
        incl (tgt_names cs) S ->
        generate_lone_constraint G env base_ty rst_ty ckenv ys e s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv ys e cs s s' Hsg Hclk Hrs Hexp Hwce Hsx Hyv Hys Htc Hgen.
      assert (Hwce1s : Forall (wc_exp P vars) [e])
        by (constructor; [exact Hwce|constructor]).
      assert (Hsx1s : Forall (src_exp vars AN) [e])
        by (constructor; [exact Hsx|constructor]).
      destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                    |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns].
      1-9: destruct ys as [|x [|y ys]];
        [refine (generate_lgen_constraint_scoped_wc S ckenv _ _ cs s s'
                   Hclk Hrs Hexp Hwce1s Hsx1s Hyv Hys Htc Hgen)
        |refine (generate_ldef_constraint_scoped_wc S ckenv x _ cs s s'
                   Hclk Hrs Hexp Hwce Hsx
                   (Hyv x (or_introl (@Logic.eq_refl _ x))) Hys Htc Hgen)
        |refine (generate_lgen_constraint_scoped_wc S ckenv _ _ cs s s'
                   Hclk Hrs Hexp Hwce1s Hsx1s Hyv Hys Htc Hgen)].
      destruct Hexp as (Hexp1 & Hexps).
      assert (Forall (wc_exp P vars) args) as Hwcargs by (inv Hwce; assumption).
      assert (Forall (src_exp vars AN) args) as Hsxargs
        by (eapply src_exp_imm_forall; [|exact Hsx];
            intros e' He'; exact (imm_Eapp_arg f args ro anns e' He')).
      assert (Forall (nested_src vars AN) args) as Hnsargs
        by (eapply nested_src_args; exact Hsx).
      destruct ro as [e1|]; destruct ys as [|y ys].
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - cbn [generate_lone_constraint] in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply single_inv in Ha1 as (? & ?); subst t1 s2.
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        apply option_to_sec_inv in Hrck as (Hrck & ?); subst s3.
        pose proof Hgen as Hgen0.
        apply generate_lcall_constraint_inv in Hgen0
          as (sg0 & ckty0 & argts0 & outs0 & sti0 & cs00
              & _ & _ & _ & _ & _ & Hshape).
        assert (wc_exp P vars e1) as Hwce1 by (inv Hwce; assumption).
        assert (src_exp vars AN e1) as Hsx1
          by (eapply src_exp_imm; [apply imm_Eapp_rst|exact Hsx]).
        assert (nested_src vars AN e1) as Hns1
          by (eapply nested_src_reset; exact Hsx).
        assert (incl (tgt_names (carried [a1])) S) as Hci.
        { rewrite carried_single. eapply incl_tran; [|exact Htc].
          apply tgt_names_incl_of_In. intros cc Hcc. rewrite Hshape.
          apply (proj2 (cmerge_In _ _ cc)). right.
          apply (proj2 (cmerge_In _ _ cc)). right.
          rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hcc. }
        destruct (Hexp1 e1 [a1] s s1 Hwce1 Hsx1 Hci Ht1) as (Hf1 & Hc1).
        rewrite carried_single in Hc1.
        inversion Hf1 as [|? ? Hs1 ?]; subst.
        refine (generate_lcall_constraint_scoped_wc S ckenv _ f args _ _ s1 s'
                  Hsg Hclk (conj Hexp1 Hexps) Hwcargs Hsxargs Hnsargs Hys
                  ?[Hfr] ?[Hcr] Htc Hgen).
        + rewrite !fst_ljoin, fst_lvar.
          apply st_scoped_merge;
            [intros y0 [Hy0|[]]; subst y0; exact Hrs|].
          apply st_scoped_merge; [exact Hs1|].
          exact (Hclk [e1] (hd Cbase (LSyn.clockof e1)) rck [a1] s s1
                   (Forall_cons _ Hwce1 (Forall_nil _))
                   (or_introl (clk_src_hd_clockof vars e1)) Hci
                   (assign_lexps_single_ok e1 s [a1] s1 Ht1) Hrck).
        + rewrite !snd_ljoin, snd_lvar. cbn [snd].
          rewrite cmerge_nil, cmerge_nil2. exact Hc1.
      - unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - refine (generate_lcall_constraint_scoped_wc S ckenv _ f args _ cs s s'
                  Hsg Hclk (conj Hexp1 Hexps) Hwcargs Hsxargs Hnsargs Hys
                  ?[Hfr] ?[Hcr] Htc Hgen).
        + rewrite fst_lvar. intros y0 [Hy0|[]]; subst y0; exact Hrs.
        + rewrite snd_lvar. constructor.
    Qed.

    Lemma generate_lsplit_constraints_scoped_wc :
      forall S ckenv es xs cs s s',
        secglobal_scoped G ->
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        Forall (wc_exp P vars) es ->
        Forall (src_exp vars AN) es ->
        incl xs (List.map fst vars) ->
        incl (CALLS.sec_of env xs) S ->
        incl (tgt_names cs) S ->
        generate_lsplit_constraints G env base_ty rst_ty ckenv xs es s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv es. induction es as [|e es IH];
        intros xs cs s s' Hsg Hclk Hrs Hexp Hwces Hsxs Hxv Hxs Htc Hgen.
      - cbn [generate_lsplit_constraints] in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hc & _); subst cs. constructor.
      - inversion Hwces as [|e' es' Hwce Hwcr]; subst.
        inversion Hsxs as [|e'' es'' Hsxe Hsxr]; subst.
        rewrite gen_lsplit_cons in Hgen.
        apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
        apply sec_bind_inv in Hgen as (cr & s2 & Hcr & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        rewrite tgt_names_app in Htc.
        apply cscoped_app.
        + refine (generate_lone_constraint_scoped_wc S ckenv
                    (firstn (numstreams e) xs) e c s s1
                    Hsg Hclk Hrs Hexp Hwce Hsxe ?[Hyv1] ?[Hys1] ?[Htc1] Hc).
          * intros y Hy. apply Hxv.
            exact (In_firstn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_firstn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Htc]. apply incl_appl, incl_refl.
        + refine (IH (skipn (numstreams e) xs) cr s1 s2
                    Hsg Hclk Hrs Hexp Hwcr Hsxr ?[Hyv2] ?[Hys2] ?[Htc2] Hcr).
          * intros y Hy. apply Hxv.
            exact (In_skipn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Hxs]. apply sec_of_incl.
            intros y Hy. exact (In_skipn_any ident (numstreams e) xs y Hy).
          * eapply incl_tran; [|exact Htc]. apply incl_appr, incl_refl.
    Qed.

    Lemma generate_leqn_constraint_scoped_wc :
      forall S ckenv eqn cs s s',
        secglobal_scoped G ->
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        wc_equation P vars eqn ->
        Forall (src_exp vars AN) (snd eqn) ->
        incl (CALLS.sec_of env (fst eqn)) S ->
        incl (tgt_names cs) S ->
        generate_leqn_constraint G env base_ty rst_ty ckenv eqn s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv eqn cs s s' Hsg Hclk Hrs Hexp Hwceq Hsxs Hxs Htc Hgen.
      destruct eqn as (xs & es). cbn [fst snd] in Hxs, Hsxs.
      pose proof (wc_equation_lhs_vars P vars xs es Hwceq) as Hxv.
      destruct Hwceq as (Hwces & _ & _).
      destruct es as [|e [|e2 es2]].
      - exact (generate_lgen_constraint_scoped_wc S ckenv xs [] cs s s'
                 Hclk Hrs Hexp Hwces Hsxs Hxv Hxs Htc Hgen).
      - inversion Hwces as [|? ? Hwce ?]; subst.
        inversion Hsxs as [|? ? Hsxe ?]; subst.
        rewrite <- generate_lone_is_leqn in Hgen.
        exact (generate_lone_constraint_scoped_wc S ckenv xs e cs s s'
                 Hsg Hclk Hrs Hexp Hwce Hsxe Hxv Hxs Htc Hgen).
      - destruct (has_lcall (e :: e2 :: es2)) eqn:Hh;
          cbn [generate_leqn_constraint] in Hgen; rewrite Hh in Hgen.
        + destruct e; try destruct o;
            (refine (generate_lsplit_constraints_scoped_wc S ckenv _ xs cs s s'
                       Hsg Hclk Hrs Hexp Hwces Hsxs Hxv Hxs Htc Hgen)).
        + destruct e; try destruct o;
            (refine (generate_lgen_constraint_scoped_wc S ckenv xs _ cs s s'
                       Hclk Hrs Hexp Hwces Hsxs Hxv Hxs Htc Hgen)).
    Qed.

    Theorem generate_leqns_constraints_scoped_wc :
      forall S ckenv eqs cs s s',
        secglobal_scoped G ->
        clk_scoped_wc ckenv S ->
        In rst_ty S ->
        exps_scoped_wc S ->
        Forall (wc_equation P vars) eqs ->
        Forall (fun eq => Forall (src_exp vars AN) (snd eq)) eqs ->
        incl (CALLS.sec_of env (vars_defined eqs)) S ->
        incl (tgt_names cs) S ->
        generate_leqns_constraints G env base_ty rst_ty ckenv eqs s
          = OK (cs, s') ->
        constraints_scoped S cs.
    Proof.
      intros S ckenv eqs. induction eqs as [|eqn eqs IH];
        intros cs s s' Hsg Hclk Hrs Hexp Hwc Hsxe Hxs Htc Hgen.
      - apply generate_leqns_constraints_nil in Hgen as (Hc & _).
        rewrite Hc. constructor.
      - inversion Hwc as [|? ? Hwc1 Hwcr]; subst.
        inversion Hsxe as [|? ? Hsx1 Hsxr]; subst.
        rewrite generate_leqns_constraints_cons in Hgen.
        apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
        apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & ?); subst cs s'.
        rewrite vars_defined_cons_eq, sec_of_app in Hxs.
        rewrite tgt_names_app in Htc.
        apply cscoped_app.
        + refine (generate_leqn_constraint_scoped_wc S ckenv eqn c1 s s1
                    Hsg Hclk Hrs Hexp Hwc1 Hsx1 ?[Hxs1] ?[Htc1] Hc1).
          * eapply incl_tran; [|exact Hxs]. apply incl_appl, incl_refl.
          * eapply incl_tran; [|exact Htc]. apply incl_appl, incl_refl.
        + refine (IH c2 s1 s2
                    Hsg Hclk Hrs Hexp Hwcr Hsxr ?[Hxs2] ?[Htc2] Hc2).
          * eapply incl_tran; [|exact Hxs]. apply incl_appr, incl_refl.
          * eapply incl_tran; [|exact Htc]. apply incl_appr, incl_refl.
    Qed.

    (** The dichotomy at the declared names, for a source expression: the
        well-clockedness the clock names need is [wc_exp_clock_names]'s, so
        nothing is asked of the program beyond [wc]. *)
    Theorem lexp_scoped_tgt_all_src :
      forall decl,
        In base_ty decl -> In rst_ty decl ->
        (forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                     In b decl) ->
        wc_global P -> wc_env vars ->
        secglobal_scoped G ->
        forall e, wc_exp P vars e /\ src_exp vars AN e ->
                  lexp_scoped_tgt G env base_ty rst_ty decl e.
    Proof.
      intros decl Hbase Hrstd Henv Hg Hwenv Hsg e (Hwc & _).
      exact (lexp_scoped_tgt_all_wc G env base_ty rst_ty P vars decl Hbase
               Hrstd Henv Hg Hwenv Hsg e Hwc).
    Qed.

    (** The guarded premises, from the dichotomy at the node's declared
        names. *)
    Lemma exps_scoped_wc_of_decl :
      forall decl S,
        In base_ty decl -> In rst_ty decl ->
        (forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                     In b decl) ->
        wc_global P -> wc_env vars ->
        secglobal_scoped G ->
        incl decl S ->
        exps_scoped_wc S.
    Proof.
      intros decl S Hb Hr Henv Hg Hwenv Hsg Hds.
      split.
      - intros e ts s0 s1 Hwc Hsx Hci Hgen.
        destruct (lexp_scoped_tgt_all_src decl Hb Hr Henv Hg Hwenv Hsg e
                    (conj Hwc Hsx) ts s0 s1 Hgen) as (Hf & Hc).
        assert (incl (decl ++ tgt_names (carried ts)) S) as Hi
            by (apply incl_app; [exact Hds|exact Hci]).
        split;
          [eapply Forall_impl; [|exact Hf]; intros t Ht;
           eapply st_scoped_weaken; [exact Hi|exact Ht]
          |eapply constraints_scoped_weaken; [exact Hi|exact Hc]].
      - intros es ts s0 s1 Hwcs Hsxs Hci Hgen.
        assert (Forall (lexp_scoped_tgt G env base_ty rst_ty decl) es) as Hall.
        { rewrite Forall_forall in Hwcs, Hsxs |- *. intros e0 He0.
          exact (lexp_scoped_tgt_all_src decl Hb Hr Henv Hg Hwenv Hsg e0
                   (conj (Hwcs e0 He0) (Hsxs e0 He0))). }
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es Hall
                    ts s0 s1 Hgen) as (Hf & Hc).
        assert (incl (decl ++ tgt_names (carried ts)) S) as Hi
            by (apply incl_app; [exact Hds|exact Hci]).
        split;
          [eapply Forall_impl; [|exact Hf]; intros t Ht;
           eapply st_scoped_weaken; [exact Hi|exact Ht]
          |eapply constraints_scoped_weaken; [exact Hi|exact Hc]].
    Qed.

  End GuardedScoped.

  (** The clock-scoping premise of the rules, from the node's declared
      variables and what the arguments carried: a clock the rules meet is a
      declared clock, or the base clock of a call's arguments / a reset's,
      whose names are declared variables or streams the arguments name -- and
      those are targets of what the arguments carry. *)
  Section ClkScopedWc.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable cenv    : Env.t (type * clock).
    Variable P       : global.
    Variable vars    : list (ident * clock).
    Variable decl    : list ident.
    Variable S       : list ident.

    Hypothesis Hb : In base_ty decl.
    Hypothesis Henv :
      forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                  In b decl.
    Hypothesis Hwenv : wc_env vars.
    Hypothesis Hcenv :
      forall x ck, In x (List.map fst vars) -> find_clock cenv x = OK ck ->
                   incl (clock_vars ck) (List.map fst vars).
    Hypothesis Hds : incl decl S.

    Lemma clk_vars_images_scoped_wc :
      forall ck ckty,
        incl (clock_vars ck) (List.map fst vars) ->
        assign_clk_type env base_ty ck = Some ckty ->
        st_scoped decl ckty.
    Proof.
      intros ck ckty Hv H y Hy.
      destruct (assign_clk_type_images env base_ty ck ckty H y Hy)
        as [->|(x & Hx & Hf)]; [exact Hb|exact (Henv x y (Hv x Hx) Hf)].
    Qed.

    Theorem clk_scoped_wc_holds :
      wc_global P ->
      clk_scoped_wc G env base_ty rst_ty P vars cenv S.
    Proof.
      intros Hg es ck ckty argts s s1 Hwes Hsrc HT Hargs H.
      destruct Hsrc as [Hs|(x & Hx & Hfc)].
      - eapply st_scoped_weaken; [apply incl_app; [exact Hds|exact HT]|].
        refine (clk_scoped_named env base_ty P vars decl es ck ckty
                  (tgt_names (carried argts)) Hg Hwenv Hb Henv Hwes Hs _ H).
        exact (proj2 (lexp_named_tgt_list G env base_ty rst_ty P vars es Hwes
                        argts s s1 Hargs)).
      - eapply st_scoped_weaken; [exact Hds|].
        exact (clk_vars_images_scoped_wc ck ckty (Hcenv x ck Hx Hfc) H).
    Qed.

  End ClkScopedWc.

  (** The environment's names for a node's anonymous streams are distinct,
      and apart from the declared variables' and the two levels'. *)
  Lemma flat_map_opt_NoDup :
    forall env (l : list ident),
      env_injective env -> NoDup l ->
      NoDup (flat_map (fun w => match Env.find w env with
                                | Some b => [b] | None => [] end) l).
  Proof.
    intros env l Hinj. induction l as [|w l IH]; intros Hnd; simpl.
    - constructor.
    - inversion Hnd as [|? ? Hw Hl]; subst.
      destruct (Env.find w env) as [b|] eqn:Eb; [|exact (IH Hl)].
      constructor; [|exact (IH Hl)].
      intro Hin. apply in_flat_map in Hin as (w' & Hw' & Hb').
      destruct (Env.find w' env) as [b'|] eqn:Eb'; [|destruct Hb'].
      destruct Hb' as [Hb'|[]]. subst b'.
      assert (w' = w) as -> by (exact (Hinj w' w b b Eb' Eb Logic.eq_refl)).
      exact (Hw Hw').
  Qed.

  Lemma anon_images_NoDup :
    forall env (n : node),
      env_injective env -> NoDup (anon_images env n).
  Proof.
    intros env n Hinj. unfold anon_images.
    assert (forall (A : Type) (l : list (ident * A)),
              flat_map (fun p => match Env.find (fst p) env with
                                 | Some b => [b] | None => [] end) l
              = flat_map (fun w => match Env.find w env with
                                   | Some b => [b] | None => [] end)
                  (List.map fst l)) as ->.
    { induction l as [|p l IH]; [reflexivity|]. simpl. now rewrite IH. }
    apply flat_map_opt_NoDup; [exact Hinj|].
    apply fst_NoDupMembers.
    pose proof (n_nodup n) as H.
    rewrite !app_assoc in H. apply NoDupMembers_app_r in H. exact H.
  Qed.

  Lemma anon_images_not_declared :
    forall env (n : node) d,
      env_injective env ->
      In d (anon_images env n) ->
      ~ In d (CALLS.sec_of env
                (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
  Proof.
    intros env n d Hinj Hin Hdecl.
    unfold anon_images in Hin. apply in_flat_map in Hin as ((w, a) & Hp & Hb).
    cbn [fst] in Hb.
    destruct (Env.find w env) as [b0|] eqn:Ew; [|destruct Hb].
    destruct Hb as [Hb|[]]. subst b0.
    unfold CALLS.sec_of in Hdecl. apply in_flat_map in Hdecl as (x & Hx & Hxd).
    destruct (Env.find x env) as [b|] eqn:Ex; [|destruct Hxd].
    destruct Hxd as [Hxd|[]]. subst b.
    assert (x = w) as -> by (exact (Hinj x w d d Ex Ew Logic.eq_refl)).
    assert (Hnd : NoDupMembers ((n.(n_in) ++ n.(n_vars) ++ n.(n_out))
                                ++ anon_in_eqs n.(n_eqs)))
      by (rewrite <- !app_assoc; exact (n_nodup n)).
    exact (NoDupMembers_app_InMembers w _ _ Hnd
             (proj2 (fst_InMembers _ _) Hx)
             (proj2 (fst_InMembers _ _) (in_map _ _ _ Hp))).
  Qed.

  Theorem generate_lnode_sig_scoped_wc :
    forall (G : secglobal) (P : global) (AN : list ident) (n : node)
           env aux sg st0 st1,
      env_injective env ->
      secglobal_scoped G ->
      wl_node P n ->
      wc_global P ->
      wc_node P n ->
      Forall (fun eq =>
                Forall (src_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) AN)
                  (snd eq)) n.(n_eqs) ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      (forall clk_id rst_id,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          ~ In clk_id (List.map fst (anon_in_eqs n.(n_eqs)))
          /\ ~ In rst_id (List.map fst (anon_in_eqs n.(n_eqs)))) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      signature_scoped sg.
  Proof.
    intros G P AN n env aux sg st0 st1 Hinj Hsgs Hwl Hwcg Hwcn Hsrc Hsep Hauxna
      Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    destruct (Hauxna ci ri Haux) as (Hnca & Hnra).
    assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
        by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
        by (eapply get_mappings_from_node_sec_of; exact Hout).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt]).
    set (NI := anon_images env n).
    assert (Hsplit : decl = (inp ++ locals ++ out) ++ [ct; rt])
        by (unfold decl; rewrite Hi, Hl, Ho, !map_app, !sec_of_app;
            reflexivity).
    (** no declared name was minted *)
    assert (Hdm : forall d, In d decl -> ~ In d (minted st0 st1)).
    { intros d Hd. unfold decl in Hd. apply in_app_or in Hd as [Hd|Hd].
      - unfold CALLS.sec_of in Hd. apply in_flat_map in Hd as (x & _ & Hd).
        destruct (Env.find x env) as [b|] eqn:Hx; [|contradiction].
        destruct Hd as [Hd|[]]; subst b. exact (Hsep x d Hx).
      - destruct Hd as [Hd|[Hd|[]]]; subst d;
          [exact (Hsep ci ct Hct)|exact (Hsep ri rt Hrt)]. }
    (** the anonymous streams' names: distinct, not declared, not the two
        levels, not minted *)
    assert (HNInd : NoDup NI) by exact (anon_images_NoDup env n Hinj).
    assert (HNIdecl : forall d, In d NI -> ~ In d decl).
    { intros d Hd Hdd. unfold decl in Hdd. apply in_app_or in Hdd as [Hdd|Hdd].
      - exact (anon_images_not_declared env n d Hinj Hd Hdd).
      - destruct Hdd as [<-|[<-|[]]].
        + exact (anon_images_apart env n ci _ Hinj Hct Hnca Hd).
        + exact (anon_images_apart env n ri _ Hinj Hrt Hnra Hd). }
    assert (HNImin : forall d, In d NI -> ~ In d (minted st0 st1)).
    { intros d Hd Hm. unfold NI, anon_images in Hd.
      apply in_flat_map in Hd as ((w, a) & _ & Hb). cbn [fst] in Hb.
      destruct (Env.find w env) as [b|] eqn:Ew; [|destruct Hb].
      destruct Hb as [Hb|[]]. subst b. exact (Hsep w d Ew Hm). }
    assert (Hbd : In ct decl)
      by (unfold decl; apply in_or_app; right; now left).
    assert (Hrd : In rt decl)
      by (unfold decl; apply in_or_app; right; right; now left).
    set (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    assert (Hvm : List.map fst vars
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold vars, idck; rewrite map_map; reflexivity).
    assert (Hrg : forall x b, In x (List.map fst vars) ->
                              Env.find x env = Some b -> In b decl).
    { intros x b Hx Hf. rewrite Hvm in Hx. unfold decl.
      apply in_or_app. left. exact (sec_of_In_intro env _ x b Hx Hf). }
    destruct Hwcn as (_ & _ & Hwenv0 & Hweqs).
    assert (Hwenv : wc_env vars).
    { unfold vars.
      assert (Permutation (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                (idck (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))) as Hperm.
      { unfold idck. apply Permutation_map.
        apply Permutation_app_head. apply Permutation_app_comm. }
      rewrite Hperm. exact Hwenv0. }
    assert (Hcenv : forall x ck, In x (List.map fst vars) ->
                    find_clock (lnode_clock_env n) x = OK ck ->
                    incl (clock_vars ck) (List.map fst vars)).
    { intros x ck Hx Hfc. rewrite Hvm in Hx.
      apply in_map_iff in Hx as ((x' & tc) & Hxe & Hin). cbn in Hxe. subst x'.
      rewrite (lnode_clock_env_find n x tc Hin) in Hfc.
      inversion Hfc; subst ck.
      assert (In (x, snd tc) vars) as Hv.
      { unfold vars, idck. apply in_map_iff. exists (x, tc). split;
          [reflexivity|exact Hin]. }
      unfold wc_env in Hwenv. rewrite Forall_forall in Hwenv.
      intros y Hy.
      destruct (clock_vars_wc vars (snd tc) (Hwenv _ Hv) y Hy) as (cky & Hyv).
      apply in_map_iff. exists (y, cky). split; [reflexivity|exact Hyv]. }
    (** item 7: every target is a defined name, an anonymous stream's, or a
        minted one *)
    destruct (generate_leqns_constraints_shape NI G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (NI ++ minted st0 st1)
                (conj (incl_appr _ (incl_refl _)) (incl_appl _ (incl_refl _)))
                (proj2 (Forall_forall _ _) (fun eq H => eqs_named_in env n eq H))
                (fun x b Hx Hf Hin =>
                   match in_app_or _ _ _ Hin with
                   | or_introl H =>
                       defined_not_in_anon_images env n x b Hinj Hx Hf H
                   | or_intror H => Hsep x b Hf H
                   end)
                (wl_node_arity P n Hwl) Hcns)
      as (ms & Hm & Hms).
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) decl).
    { unfold decl. eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    assert (Htb : incl (tgt_names cns) (decl ++ NI ++ minted st0 st1)).
    { eapply incl_tran; [eapply tgt_names_of_targets_of; exact Hm|].
      apply incl_app;
        [eapply incl_tran; [exact Hdefd|apply incl_appl, incl_refl]
        |eapply incl_tran; [exact Hms|apply incl_appr, incl_refl]]. }
    (** the scoping, at the scope that carries the dichotomy *)
    set (S := decl ++ tgt_names cns).
    assert (HclkS : clk_scoped_wc G env ct rt P vars (lnode_clock_env n) S).
    { apply (clk_scoped_wc_holds G env ct rt (lnode_clock_env n) P vars decl S
               Hbd Hrg Hwenv Hcenv (incl_appl _ (incl_refl _)) Hwcg). }
    assert (Hcsc : constraints_scoped S cns).
    { eapply generate_leqns_constraints_scoped_wc;
        [exact Hsgs|exact HclkS| |
         eapply exps_scoped_wc_of_decl;
           [exact Hbd|exact Hrd|exact Hrg|exact Hwcg|exact Hwenv|exact Hsgs
           |unfold S; apply incl_appl, incl_refl]
        |exact Hweqs|exact Hsrc
        |eapply incl_tran; [exact Hdefd|unfold S; apply incl_appl, incl_refl]
        |unfold S; apply incl_appr, incl_refl|exact Hcns].
      unfold S, decl. apply in_or_app. left. apply in_or_app. right.
      right. now left. }
    assert (Hcol : constraints_scoped S (collapse cns))
        by (apply collapse_scoped; exact Hcsc).
    assert (Hlen1c : Forall singleton_rhs cns).
    { pose proof (generate_leqns_constraints_len1 G env ct rt
                    (lnode_clock_env n) n.(n_eqs) cns st0 st1 Hcns) as Hl1.
      rewrite Forall_forall in Hl1. apply Forall_forall.
      intros c Hc. specialize (Hl1 c Hc).
      destruct c as (lhs, rhs). cbn [snd] in Hl1 |- *.
      destruct rhs as [|b [|? ?]]; [discriminate Hl1|now exists b
                                   |discriminate Hl1]. }
    assert (Hlen1 : Forall singleton_rhs (collapse cns))
        by (apply collapse_singleton_rhs;
            exact (generate_leqns_constraints_len1 G env ct rt
                     (lnode_clock_env n) n.(n_eqs) cns st0 st1 Hcns)).
    (** and the elimination *)
    unfold signature_scoped. cbn [s_constraints s_in s_out s_clk s_reset].
    eapply simplify_scoped_weak.
    - (** distinct *)
      apply NoDup_app'.
      + first [rewrite Hl, <- (get_mappings_from_node_sec_of _ _ _ Hloc)|idtac].
        eapply get_mappings_nodup_gen;
          [|exact Hinj|eapply get_mappings_from_node_eq; exact Hloc].
        rewrite <- fst_NoDupMembers.
        pose proof (n_nodup n) as Hnd.
        repeat rewrite app_assoc in Hnd.
        apply NoDupMembers_app_l in Hnd.
        apply NoDupMembers_app_l in Hnd.
        apply NoDupMembers_app_r in Hnd. exact Hnd.
      + apply NoDup_app'.
        * exact HNInd.
        * apply minted_NoDup.
        * apply Forall_forall. intros y Hy Hin. exact (HNImin y Hy Hin).
      + apply Forall_forall. intros y Hy Hin.
        apply in_app_or in Hin as [Hin|Hin].
        * apply (HNIdecl y Hin). rewrite Hsplit. apply in_or_app. left.
          apply in_or_app. right. apply in_or_app. left. exact Hy.
        * apply (Hdm y); [|exact Hin].
          rewrite Hsplit. apply in_or_app. left.
          apply in_or_app. right. apply in_or_app. left. exact Hy.
    - (** scoped, after moving [decl ++ tgt_names cns] into place *)
      eapply constraints_scoped_weaken; [|exact Hcol].
      intros y Hy. unfold S in Hy. apply in_app_or in Hy as [Hy|Hy].
      + rewrite Hsplit in Hy. apply in_app_or in Hy as [Hy|Hy].
        * apply in_app_or in Hy as [Hy|Hy];
            [apply in_or_app; left; apply in_or_app; now left|].
          apply in_app_or in Hy as [Hy|Hy];
            [apply in_or_app; right; apply in_or_app; now left
            |apply in_or_app; left; apply in_or_app; right;
             apply in_or_app; now left].
        * apply in_or_app. left. apply in_or_app. right.
          apply in_or_app. now right.
      + apply Htb in Hy. apply in_app_or in Hy as [Hy|Hy].
        * rewrite Hsplit in Hy. apply in_app_or in Hy as [Hy|Hy].
          -- apply in_app_or in Hy as [Hy|Hy];
               [apply in_or_app; left; apply in_or_app; now left|].
             apply in_app_or in Hy as [Hy|Hy];
               [apply in_or_app; right; apply in_or_app; now left
               |apply in_or_app; left; apply in_or_app; right;
                apply in_or_app; now left].
          -- apply in_or_app. left. apply in_or_app. right.
             apply in_or_app. now right.
        * apply in_or_app. right. apply in_or_app. right. exact Hy.
    - (** a target, or absent *)
      intros d Hd. apply in_app_or in Hd as [Hd|Hd].
      + (** a local: defined by some equation, so item 7 gives it a
            constraint, and [collapse] keeps the target *)
        left. apply collapse_rhs_in.
        eapply Permutation_in; [apply Permutation_sym; exact Hm|].
        apply in_map_iff. exists d. split; [reflexivity|].
        apply in_or_app. left.
        rewrite Hl in Hd. unfold CALLS.sec_of in Hd |- *.
        apply in_flat_map in Hd as (x & Hx & Hdx).
        apply in_flat_map. exists x. split; [|exact Hdx].
        eapply Permutation_in; [apply Permutation_sym; exact (n_defd n)|].
        rewrite map_app. apply in_or_app. now left.
      + (** an anonymous stream's name or a minted one: a target if it occurs
            at all, because the same scoping says an occurring name is
            declared or a target, and neither kind is declared *)
        assert (Hnd : ~ In d decl).
        { apply in_app_or in Hd as [Hd|Hd];
            [exact (HNIdecl d Hd)|intro Hdd; exact (Hdm d Hdd Hd)]. }
        destruct (In_dec ident_eq_dec d (tgt_names (collapse cns)))
          as [Ht|Ht].
        * left. exact (In_tgt_names_target (collapse cns) d Hlen1 Ht).
        * right. intros (c & Hc & Hx).
          assert (In d S) as Hin
              by (eapply constraints_scoped_In; [exact Hcol|exact Hc|exact Hx]).
          unfold S in Hin. apply in_app_or in Hin as [Hin|Hin].
          -- exact (Hnd Hin).
          -- apply Ht. apply target_In_tgt_names. apply collapse_rhs_in.
             exact (In_tgt_names_target cns d Hlen1c Hin).
  Qed.

  Theorem generate_lnode_sig_rooted_ext :
    forall (G : secglobal) (P : global) (n : node) env aux sg st0 st1
           (X : list ident),
      env_injective env ->
      secglobal_scoped G ->
      (forall f sg,
          find_signature f G = Some sg ->
          NoDup (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out))) ->
      (forall f sg,
          find_signature f G = Some sg ->
          CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
          /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints)) ->
      wl_node P n ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      (forall clk_id rst_id ct rt,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          Env.find clk_id env = Some ct ->
          Env.find rst_id env = Some rt ->
          (forall x b, Env.find x env = Some b ->
             In b (CALLS.sec_of env
                     (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                   ++ [ct; rt] ++ X))
          /\ (forall f sg,
                 find_signature f G = Some sg ->
                 scope_fresh
                   ((CALLS.sec_of env
                       (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                     ++ [ct; rt] ++ X) ++ minted st0 st1) sg)) ->
      (forall clk_id rst_id,
          get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
          ~ In clk_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
          /\ ~ In rst_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
          /\ ~ In clk_id (List.map fst (anon_in_eqs n.(n_eqs)))
          /\ ~ In rst_id (List.map fst (anon_in_eqs n.(n_eqs)))) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
      /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints).
  Proof.
    intros G P n env aux sg st0 st1 X Hinj Hsgs Hnd Hroot Hwl Hsep Hrf Haux0 Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    destruct (Haux0 ci ri Haux) as (Hnc & Hnr & Hnca & Hnra).
    destruct (Hrf ci ri ct rt Haux Hct Hrt) as (Hrg & Hnsf).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt] ++ X).
    assert (Hdk : decl_ok env ct rt decl).
    { split; [|split].
      - unfold decl. apply in_or_app. right. cbn. auto.
      - unfold decl. apply in_or_app. right. cbn. auto.
      - exact Hrg. }
    assert (Hclk : clk_scoped env ct decl).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env; [|exact Hrg|exact Hck].
      unfold decl. apply in_or_app. right. cbn. auto. }
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) decl).
    { unfold decl. eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    assert (Hcr : constraints_rooted ct rt cns).
    { eapply (generate_leqns_constraints_rooted_win (anon_images env n)
                G env ct rt decl (decl ++ minted st0 st1) Hdk Hclk Hsgs);
        [apply incl_appl, incl_refl|exact Hnsf|exact Hnd|exact Hroot
        |split; [apply incl_appr, incl_refl
                |intros d Hd; apply in_or_app; left;
                 unfold anon_images in Hd; apply in_flat_map in Hd
                   as ((w, a) & _ & Hb); cbn [fst] in Hb;
                 destruct (Env.find w env) as [b|] eqn:Ew; [|destruct Hb];
                 destruct Hb as [Hb|[]]; subst b; exact (Hrg w d Ew)]
        |exact (proj2 (Forall_forall _ _) (fun eq H => eqs_named_in env n eq H))
        |eapply incl_tran; [exact Hdefd|apply incl_appl, incl_refl]
        |exact Hcns]. }
    (** the levels are neither declared names nor minted ones *)
    assert (Hav : forall y, In y (CALLS.sec_of env (List.map fst n.(n_vars)))
                            -> y <> ct /\ y <> rt).
    { intros y Hy. split; intros ->.
      - eapply (sec_of_apart env ci ct); [exact Hinj|exact Hct| |exact Hy].
        intros Hin. apply Hnc. rewrite !map_app.
        apply in_or_app. right. apply in_or_app. now left.
      - eapply (sec_of_apart env ri rt); [exact Hinj|exact Hrt| |exact Hy].
        intros Hin. apply Hnr. rewrite !map_app.
        apply in_or_app. right. apply in_or_app. now left. }
    set (NI := anon_images env n).
    destruct (generate_leqns_constraints_shape NI G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (NI ++ minted st0 st1)
                (conj (incl_appr _ (incl_refl _)) (incl_appl _ (incl_refl _)))
                (proj2 (Forall_forall _ _) (fun eq H => eqs_named_in env n eq H))
                (fun x b Hx Hf Hin =>
                   match in_app_or _ _ _ Hin with
                   | or_introl H =>
                       defined_not_in_anon_images env n x b Hinj Hx Hf H
                   | or_intror H => Hsep x b Hf H
                   end)
                (wl_node_arity P n Hwl) Hcns)
      as (ms & Hm & Hms).
    assert (Htg : forall y, In y (tgt_names cns) -> y <> ct /\ y <> rt).
    { intros y Hy.
      apply (tgt_names_of_targets_of _ _ Hm) in Hy.
      apply in_app_or in Hy as [Hy|Hy].
      - assert (In y (CALLS.sec_of env (List.map fst (n.(n_vars) ++ n.(n_out)))))
          as Hy'
            by (eapply Permutation_in;
                [apply sec_of_Permutation; exact (n_defd n)|exact Hy]).
        split; intros ->.
        + eapply (sec_of_apart env ci ct); [exact Hinj|exact Hct| |exact Hy'].
          intros Hin. apply Hnc. rewrite map_app in Hin. rewrite !map_app.
          apply in_or_app. right. exact Hin.
        + eapply (sec_of_apart env ri rt); [exact Hinj|exact Hrt| |exact Hy'].
          intros Hin. apply Hnr. rewrite map_app in Hin. rewrite !map_app.
          apply in_or_app. right. exact Hin.
      - apply Hms in Hy. apply in_app_or in Hy as [Hy|Hy].
        + split; intros ->;
            [exact (anon_images_apart env n ci _ Hinj Hct Hnca Hy)
            |exact (anon_images_apart env n ri _ Hinj Hrt Hnra Hy)].
        + split; intros ->;
            [exact (Hsep ci _ Hct Hy)|exact (Hsep ri _ Hrt Hy)]. }
    assert (Hrs : constraints_rooted ct rt
                    (simplify (collapse cns) (locals ++ NI ++ minted st0 st1))).
    { apply simplify_rooted with (keep := [ct; rt]).
      - now left.
      - right. now left.
      - intros d Hd [Hdc|[Hdr|[]]]; subst d; apply in_app_or in Hd as [Hd|Hd];
          try (apply in_app_or in Hd as [Hd|Hd]).
        + rewrite Hl in Hd. exact (proj1 (Hav _ Hd) Logic.eq_refl).
        + exact (anon_images_apart env n ci _ Hinj Hct Hnca Hd).
        + exact (Hsep ci _ Hct Hd).
        + rewrite Hl in Hd. exact (proj2 (Hav _ Hd) Logic.eq_refl).
        + exact (anon_images_apart env n ri _ Hinj Hrt Hnra Hd).
        + exact (Hsep ri _ Hrt Hd).
      - intros c Hc y Hy [Hyc|[Hyr|[]]].
        + assert (In (snd c) (List.map snd (collapse cns)))
            by (apply in_map; exact Hc).
          apply (proj1 (collapse_rhs_in cns _)) in H.
          apply in_map_iff in H as (c' & Hc'e & Hc').
          assert (In y (tgt_names cns)) as Hyt.
          { unfold tgt_names. apply in_flat_map. exists c'.
            split; [exact Hc'|].
            destruct c' as (l', r'). destruct c as (l, r).
            cbn [snd] in Hc'e, Hy |- *. subst r'. exact Hy. }
          exact (proj1 (Htg y Hyt) (Logic.eq_sym Hyc)).
        + assert (In (snd c) (List.map snd (collapse cns)))
            by (apply in_map; exact Hc).
          apply (proj1 (collapse_rhs_in cns _)) in H.
          apply in_map_iff in H as (c' & Hc'e & Hc').
          assert (In y (tgt_names cns)) as Hyt.
          { unfold tgt_names. apply in_flat_map. exists c'.
            split; [exact Hc'|].
            destruct c' as (l', r'). destruct c as (l, r).
            cbn [snd] in Hc'e, Hy |- *. subst r'. exact Hy. }
          exact (proj2 (Htg y Hyt) (Logic.eq_sym Hyr)).
      - apply collapse_rooted. exact Hcr. }
    cbn [s_constraints s_clk s_reset]. split.
    - unfold CALLS.all_sources_have. eapply Forall_impl; [|exact Hrs].
      intros c (Hc1 & Hc2). exact Hc1.
    - unfold CALLS.all_sources_have. eapply Forall_impl; [|exact Hrs].
      intros c (Hc1 & Hc2). exact Hc2.
  Qed.

  (** * The canonical ambients, restricted to declared variables

      [canonical_ambients_scoped] asks every clock the environment can type to
      have a scoped type, which an environment with extra keys refuses.  The
      guarded assignment gives a variable outside the declared ones the empty
      ambient, so that the scoping hypothesis is about declared variables
      only; on a source equation's own variables it is the canonical one. *)

  Definition canonical_ambient_g (vars : list (ident * clock))
      (env : Env.t ident) (base_ty rst_ty : ident)
      (cenv : Env.t (type * clock)) (x : ident) : ST :=
    if in_dec ident_eq_dec x (List.map fst vars)
    then canonical_ambient env base_ty rst_ty cenv x
    else [].

  Definition canonical_ambients_g (vars : list (ident * clock))
      (env : Env.t ident) (base_ty rst_ty : ident)
      (cenv : Env.t (type * clock)) (eq : equation) : list ST :=
    List.map (canonical_ambient_g vars env base_ty rst_ty cenv) (fst eq).

  Lemma canonical_ambients_g_length :
    forall vars env base_ty rst_ty cenv eq,
      List.length (canonical_ambients_g vars env base_ty rst_ty cenv eq)
      = List.length (fst eq).
  Proof.
    intros vars env base_ty rst_ty cenv eq.
    unfold canonical_ambients_g. apply map_length.
  Qed.

  Lemma canonical_ambients_g_spec :
    forall vars env base_ty rst_ty cenv eq,
      incl (fst eq) (List.map fst vars) ->
      eqn_ambients env base_ty rst_ty cenv (fst eq)
        (canonical_ambients_g vars env base_ty rst_ty cenv eq).
  Proof.
    intros vars env base_ty rst_ty cenv (xs, es) Hin.
    unfold eqn_ambients, canonical_ambients_g. cbn [fst] in *.
    induction xs as [|x xs IH]; [constructor|].
    cbn [List.map]. constructor.
    - intros ck ckty Hfc Hac. unfold canonical_ambient_g.
      destruct (in_dec ident_eq_dec x (List.map fst vars)) as [_|Hn].
      + unfold canonical_ambient. rewrite Hfc, Hac. reflexivity.
      + exfalso. apply Hn. apply Hin. now left.
    - apply IH. intros y Hy. apply Hin. now right.
  Qed.

  Lemma canonical_ambients_g_scoped :
    forall vars env base_ty rst_ty cenv scope,
      In rst_ty scope ->
      (forall x ck ckty,
          In x (List.map fst vars) ->
          find_clock cenv x = OK ck ->
          assign_clk_type env base_ty ck = Some ckty ->
          st_scoped scope ckty) ->
      forall eq,
        stream_ambients_scoped scope
          (canonical_ambients_g vars env base_ty rst_ty cenv eq).
  Proof.
    intros vars env base_ty rst_ty cenv scope Hrst Hclk eq.
    unfold stream_ambients_scoped, canonical_ambients_g.
    apply Forall_forall. intros a Ha.
    apply in_map_iff in Ha as (x & Ha & _). subst a.
    unfold canonical_ambient_g.
    destruct (in_dec ident_eq_dec x (List.map fst vars)) as [Hx|Hx];
      [|intros z Hz; contradiction].
    unfold canonical_ambient.
    destruct (find_clock cenv x) as [ck|e] eqn:Efc;
      [|intros z Hz; contradiction].
    destruct (assign_clk_type env base_ty ck) as [ckty|] eqn:Ea;
      [|intros z Hz; contradiction].
    intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
    - destruct Hz as [Hz|[]]; subst z. exact Hrst.
    - exact (Hclk x ck ckty Hx Efc Ea z Hz).
  Qed.

  Lemma canonical_ambients_g_cover :
    forall vars env base_ty rst_ty cenv (eq : equation),
      (forall x ck, In (x, ck) vars -> find_clock cenv x = OK ck) ->
      (forall ck, In ck (clocksof (snd eq)) ->
                  exists ckty, assign_clk_type env base_ty ck = Some ckty) ->
      Forall2 (fun x ck => In (x, ck) vars) (fst eq) (clocksof (snd eq)) ->
      clocks_covered env base_ty rst_ty (clocksof (snd eq))
        (canonical_ambients_g vars env base_ty rst_ty cenv eq).
  Proof.
    intros vars env base_ty rst_ty cenv eq Hagree Hdef Hwc.
    unfold clocks_covered, canonical_ambients_g.
    revert Hdef. induction Hwc as [|x ck xs cks Hin Hr IH]; intros Hdef.
    - constructor.
    - cbn [List.map]. constructor.
      + destruct (Hdef ck (or_introl (@Logic.eq_refl _ ck))) as (ckty & Hac).
        exists ckty. split; [exact Hac|].
        unfold canonical_ambient_g.
        destruct (in_dec ident_eq_dec x (List.map fst vars)) as [_|Hn].
        * unfold canonical_ambient. rewrite (Hagree x ck Hin), Hac.
          apply incl_refl.
        * exfalso. apply Hn. apply in_map_iff. exists (x, ck).
          split; [reflexivity|exact Hin].
      + apply IH. intros ck0 Hck0. apply Hdef. now right.
  Qed.

  Definition env_images (env : Env.t ident) : list ident :=
    List.map snd (Env.elements env).

  Lemma env_images_spec :
    forall env x b, Env.find x env = Some b -> In b (env_images env).
  Proof.
    intros env x b H. unfold env_images. apply in_map_iff.
    exists (x, b). split; [reflexivity|]. apply Env.elements_correct. exact H.
  Qed.


  Definition anon_names (n : node) : list ident :=
    List.map fst (anon_in_eqs n.(n_eqs)).

  Definition node_typed_facts (n nall : node) : Prop :=
    exists P,
      wl_node P n /\ wc_global P /\ wc_node P n
      /\ Forall (fun eq =>
                   Forall (src_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                             (anon_names n)) (snd eq)) n.(n_eqs)
      /\ (forall w, In w (anon_names n) ->
                    ~ In w (List.map fst (idck (n.(n_in) ++ n.(n_vars)
                                                ++ n.(n_out)))))
      /\ PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs).
  Lemma lsig_step_ext :
    forall (P : global) (AN : list ident) (all : list node) envs aux stN
           (n nall : node) env (r : node_aux_names) st0 stl
           acc st sg st1,
      generate_lnode_scoped_env_st all = OK (envs, aux, stN) ->
      find_node_env n.(n_name) envs = Some env ->
      get_node_aux n.(n_name) aux = Some (r.(nclk), r.(nrst)) ->
      generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
      (st0 <= stN)%positive ->
      wl_node P n ->
      wc_global P ->
      wc_node P n ->
      Forall (fun eq =>
                Forall (src_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) AN)
                  (snd eq)) n.(n_eqs) ->
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      lsig_inv stN st0 acc st ->
      generate_lnode_sig acc n env aux st = OK (sg, st1) ->
      lsig_inv stN stl (sg :: acc) st1.
  Proof.
    intros P AN all envs aux stN n nall env r st0 stl acc st sg st1
           Hfull Hfind Haux Hloc Hst0 Hwl Hwcg Hwcn Hsrc Hsub
           (Hgood & Hsc & Hnd & Hroot & Hbd & Hle) Hsig.
    destruct (generate_local_env_for_lnode_facts nall st0 env r stl Hloc)
      as (Hinj & Hrng & Hclk & Hrst).
    assert (Hsep : forall x b, Env.find x env = Some b ->
                               ~ In b (minted st st1))
      by (intros x b Hb;
          exact (env_apart_from_minted all envs aux stN n.(n_name) env st st1
                   Hfull Hfind Hle x b Hb)).
    assert (Hlev : forall ci ri,
               get_node_aux n.(n_name) aux = Some (ci, ri) ->
               ci = r.(nclk) /\ ri = r.(nrst)).
    { intros ci ri Ha. rewrite Haux in Ha. inversion Ha. split; reflexivity. }
    set (X := env_images env).
    assert (Hrf : forall ct rt,
               Env.find r.(nclk) env = Some ct ->
               Env.find r.(nrst) env = Some rt ->
               (forall x b, Env.find x env = Some b ->
                  In b (CALLS.sec_of env
                          (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        ++ [ct; rt] ++ X))
               /\ (forall f sg0, find_signature f acc = Some sg0 ->
                     scope_fresh
                       ((CALLS.sec_of env
                           (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                         ++ [ct; rt] ++ X) ++ minted st st1) sg0)).
    { intros ct rt Hct Hrt. split.
      - intros x b Hb. apply in_or_app. right. cbn. right. right.
        exact (env_images_spec env x b Hb).
      - intros f sg0 Hf.
        eapply scope_fresh_from_bounds; [|eapply Hbd; exact Hf].
        intros ty Hty. apply in_app_or in Hty as [Hty|Hty].
        + apply in_app_or in Hty as [Hty|Hty].
          * apply sec_of_In_inv in Hty as (x & _ & Hx).
            destruct (Hrng x ty Hx) as (k & Hk & Hlo & _). eauto.
          * cbn in Hty. destruct Hty as [Hty|[Hty|Hty]].
            -- subst ty. destruct (Hrng _ _ Hct) as (k & Hk & Hlo & _). eauto.
            -- subst ty. destruct (Hrng _ _ Hrt) as (k & Hk & Hlo & _). eauto.
            -- unfold X, env_images in Hty.
               apply in_map_iff in Hty as ((x & b) & Hxb & Hin).
               cbn in Hxb. subst b.
               apply Env.elements_complete in Hin.
               destruct (Hrng x ty Hin) as (k & Hk & Hlo & _). eauto.
        + apply minted_spec in Hty as (k & Hlo & _ & Hk).
          exists k. split; [exact Hk|].
          eapply Pos.le_trans; [exact Hst0|].
          eapply Pos.le_trans; [exact Hle|exact Hlo]. }
    assert (Haux0 : forall ci ri,
               get_node_aux n.(n_name) aux = Some (ci, ri) ->
               ci <> ri
               /\ ~ In ci (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
               /\ ~ In ri (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { intros ci ri Ha. destruct (Hlev ci ri Ha) as (-> & ->).
      rewrite Hclk, Hrst. repeat split.
      - intros Heq. apply gensym_injective in Heq as [_ Heq].
        exact (Pos.succ_discr st0 Heq).
      - intros Hin. exact (lnode_var_not_sec n _ st0 Hsub Hin Logic.eq_refl).
      - intros Hin. exact (lnode_var_not_sec n _ (Pos.succ st0) Hsub Hin
                             Logic.eq_refl). }
    assert (Hauxna : forall ci ri,
               get_node_aux n.(n_name) aux = Some (ci, ri) ->
               ~ In ci (List.map fst (anon_in_eqs n.(n_eqs)))
               /\ ~ In ri (List.map fst (anon_in_eqs n.(n_eqs)))).
    { intros ci ri Ha. destruct (Hlev ci ri Ha) as (-> & ->).
      rewrite Hclk, Hrst. split.
      - intros Hin. exact (anon_stream_not_sec n _ st0 Hsub
                             (proj2 (fst_InMembers _ _) Hin) Logic.eq_refl).
      - intros Hin. exact (anon_stream_not_sec n _ (Pos.succ st0) Hsub
                             (proj2 (fst_InMembers _ _) Hin) Logic.eq_refl). }
    assert (Hgd : signature_good sg)
      by exact (generate_lnode_sig_good acc P n env aux sg st st1 Hinj Hwl
                  Hsep Hsig).
    assert (Hscd : signature_scoped sg)
      by exact (generate_lnode_sig_scoped_wc acc P AN n env aux sg st st1
                  Hinj Hsc Hwl Hwcg Hwcn Hsrc Hsep Hauxna Hsig).
    assert (Hnodup : NoDup (signature_scope sg)).
    { eapply generate_lnode_sig_scope_nodup;
        [exact Hinj| |exact Hsig].
      exact Haux0. }
    assert (Hrooted : sig_rt sg).
    { eapply generate_lnode_sig_rooted_ext;
        [exact Hinj|exact Hsc|exact Hnd|exact Hroot|exact Hwl|exact Hsep| |
         |exact Hsig].
      - intros ci ri ct rt Ha Hct Hrt0.
        destruct (Hlev ci ri Ha) as (-> & ->).
        exact (Hrf ct rt Hct Hrt0).
      - intros ci ri Ha. destruct (Haux0 ci ri Ha) as (_ & H1 & H2).
        destruct (Hauxna ci ri Ha) as (H3 & H4).
        repeat split; assumption. }
    destruct (lnode_sig_inv env acc n aux sg st st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux' & Hct & Hrt' & Hinp & Hout & Hloc' & Hcns & Hsg).
    destruct (Hlev ci ri Haux') as (-> & ->).
    refine (conj (secglobal_good_cons sg acc Hgd Hgood)
              (conj (secglobal_scoped_cons sg acc Hscd Hsc)
                 (conj (secglobal_all_cons sig_nd sg acc
                          (sig_nd_of_scope sg Hnodup) Hnd)
                    (conj (secglobal_all_cons sig_rt sg acc Hrooted Hroot)
                       (conj _ _))))).
    - apply secglobal_scope_bounded_above_cons.
      + intros ty Hty. subst sg. cbn [signature_scope s_in s_out s_clk s_reset]
          in Hty.
        assert (Hall : forall x b, Env.find x env = Some b ->
                         exists k, b = Ids.gensym Ids.sec k
                                   /\ (k < stl)%positive)
          by (intros x b Hb; destruct (Hrng x b Hb) as (k & Hk & _ & Hhi);
              eauto).
        assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
            by (eapply get_mappings_from_node_sec_of; exact Hinp).
        assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
            by (eapply get_mappings_from_node_sec_of; exact Hout).
        apply in_app_or in Hty as [Hty|Hty].
        * rewrite Hi in Hty. apply sec_of_In_inv in Hty as (x & _ & Hx).
          exact (Hall x ty Hx).
        * apply in_app_or in Hty as [Hty|Hty].
          -- rewrite Ho in Hty. apply sec_of_In_inv in Hty as (x & _ & Hx).
             exact (Hall x ty Hx).
          -- destruct Hty as [Hty|[Hty|[]]]; subst ty;
               [exact (Hall _ _ Hct)|exact (Hall _ _ Hrt')].
      + eapply secglobal_scope_bounded_above_monotone; [exact Hbd|].
        eapply generate_local_env_for_lnode_state_monotone; exact Hloc.
    - subst sg.
      eapply Pos.le_trans; [exact Hle|].
      eapply generate_leqns_constraints_sec_le; exact Hcns.
  Qed.

  (** One step of the naming pass, read off the run: the node's environment
      and auxiliary levels are what the final run publishes, and the rest of
      the run continues from the extended accumulators. *)
  Lemma naming_step_facts :
    forall envsF auxF stN (nall : node) (alls : list node) envs0 acc0 st0,
      NoDup (List.map n_name (nall :: alls)) ->
      generate_lnode_scoped_env' (nall :: alls) envs0 acc0 st0
        = OK ((envsF, auxF), stN) ->
      exists le0 r0 stl,
        generate_local_env_for_lnode nall st0 = OK ((le0, r0), stl)
        /\ find_node_env nall.(n_name) envsF = Some le0
        /\ get_node_aux nall.(n_name) auxF = Some (r0.(nclk), r0.(nrst))
        /\ (st0 <= stN)%positive
        /\ NoDup (List.map n_name alls)
        /\ generate_lnode_scoped_env' alls
              (Env.add nall.(n_name) le0 envs0) (r0 :: acc0) stl
            = OK ((envsF, auxF), stN).
  Proof.
    intros envsF auxF stN nall alls envs0 acc0 st0 Hnd Hrun.
    cbn in Hrun.
    apply name_bind_inv in Hrun as (p & stl & Hloc & Hrun).
    destruct p as (le0 & r0).
    apply name_bind_inv in Hrun as (envs1 & st2 & Hins & Hrun).
    apply name_bind_inv in Hrun as (q & st3 & Hrec & Hret).
    destruct q as (envs2 & aux2).
    unfold NMret in Hret. inversion Hret; subst envs2 aux2 st3.
    assert (envs1 = Env.add nall.(n_name) le0 envs0 /\ st2 = stl)
      as (? & ?).
    { unfold fresh_insert_node_env in Hins.
      destruct (Env.mem nall.(n_name) envs0); [discriminate Hins|].
      unfold insert_node_env, NMret in Hins.
      inversion Hins; split; reflexivity. }
    subst envs1 st2.
    inversion Hnd as [|z zs Hnotin Hnd']; subst z zs.
    assert (Hrname : r0.(nname) = nall.(n_name)).
    { unfold generate_local_env_for_lnode in Hloc.
      apply name_bind_inv in Hloc as (c1 & s1 & _ & Hl).
      apply name_bind_inv in Hl as (c2 & s2 & _ & Hl).
      apply name_bind_inv in Hl as (c3 & s3 & _ & Hl).
      apply name_bind_inv in Hl as (c4 & s4 & _ & Hl).
      apply name_bind_inv in Hl as (c5 & s5 & _ & Hret0).
      unfold NMret in Hret0. inversion Hret0. reflexivity. }
    exists le0, r0, stl. split; [exact Hloc|].
    split.
    { eapply generate_lnode_scoped_env'_envs_mono;
        [exact Hrec|exact Hnotin|].
      unfold find_node_env. apply Env.gss. }
    split.
    { rewrite (generate_lnode_scoped_env'_aux_mono alls
                 (Env.add nall.(n_name) le0 envs0) (r0 :: acc0) stl
                 envsF auxF stN nall.(n_name) Hrec Hnotin).
      unfold get_node_aux. cbn [find_node_names].
      rewrite Hrname, ident_eqb_refl. reflexivity. }
    split.
    { eapply Pos.le_trans;
        [eapply generate_local_env_for_lnode_state_monotone; exact Hloc
        |eapply generate_lnode_scoped_env'_state_mono; exact Hrec]. }
    split; [exact Hnd'|exact Hrec].
  Qed.

  (** A node's anonymous streams are not among its declared variables. *)
  Lemma anon_names_not_declared :
    forall (n : node) w,
      In w (anon_names n) ->
      ~ In w (List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
  Proof.
    intros n w Hw Hd.
    pose proof (n_nodup n) as H. rewrite fst_NoDupMembers in H.
    assert (Heq : List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)
                                ++ anon_in_eqs n.(n_eqs))
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))
                    ++ anon_names n).
    { unfold anon_names. rewrite !map_app. repeat rewrite <- app_assoc.
      reflexivity. }
    rewrite Heq in H.
    assert (Hv : List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold idck; rewrite map_map; reflexivity).
    rewrite Hv in Hd.
    eapply NoDup_app_In; [exact H|exact Hd|exact Hw].
  Qed.

  Theorem generate_all_lsignatures'_inv_ext :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall (R : node -> node -> Prop),
        (forall n nall, R n nall ->
           n_name n = n_name nall /\ node_typed_facts n nall) ->
        forall ns alls envs0 acc0 st0,
          Forall2 R ns alls ->
          NoDup (List.map n_name alls) ->
          generate_lnode_scoped_env' alls envs0 acc0 st0
            = OK ((envsF, auxF), stN) ->
          forall acc st G stf,
            lsig_inv stN st0 acc st ->
            generate_all_lsignatures' acc ns envsF auxF st = OK (G, stf) ->
            lsig_inv stN stN G stf.
  Proof.
    intros all envsF auxF stN Hfull R HR.
    intros ns alls. revert ns.
    induction alls as [|nall alls IH];
      intros ns envs0 acc0 st0 HF2 Hnd Hrun acc st G stf Hinv Hgen.
    - inversion HF2; subst. cbn in Hrun. unfold NMret in Hrun.
      inversion Hrun; subst.
      cbn in Hgen. inversion Hgen; subst. exact Hinv.
    - inversion HF2 as [|n nall0 ns' alls0 HRn HF2']; subst.
      destruct (HR n nall HRn) as (Hname & P & Hwln & Hwcg & Hwcn & Hsrc
                                    & Hdisj & Hsubn).
      destruct (naming_step_facts envsF auxF stN nall alls envs0 acc0 st0
                  Hnd Hrun) as (le0 & r0 & stl & Hloc & Hfind & Haux & Hst0
                                & Hnd' & Hrec).
      cbn in Hgen.
      destruct (generate_lnode_sig_scoped_env acc n envsF auxF st)
        as [[sg stg]|e] eqn:Hs; [|discriminate Hgen].
      unfold generate_lnode_sig_scoped_env in Hs.
      rewrite Hname, Hfind in Hs.
      eapply (IH ns' (Env.add nall.(n_name) le0 envs0) (r0 :: acc0) stl
                 HF2' Hnd' Hrec (sg :: acc) stg G stf); [|exact Hgen].
      eapply lsig_step_ext;
        [exact Hfull|rewrite Hname; exact Hfind|rewrite Hname; exact Haux
        |exact Hloc|exact Hst0|exact Hwln|exact Hwcg|exact Hwcn|exact Hsrc
        |exact Hsubn|exact Hinv|exact Hs].
  Qed.


  (** * The lockstep, with the invariants

      [generate_all_lsignatures_weakens'] with the node-level step handed what
      the program level knows at that point: both accumulators satisfy
      [lsig_inv] against the naming run, and the states are above its final
      state.  The invariants are re-established after each node by
      [lsig_step_ext]. *)

  (** The lockstep relation also records the callee program the node is
      read against: the source nodes already processed, so that at the node
      the program [P] is the rest of the source program.  [Jinv] is an
      invariant of the target accumulator against that program, extended by
      every node. *)
  Inductive Forall3P {A B C : Type} (R : list A -> A -> B -> C -> Prop)
    : list A -> list A -> list B -> list C -> Prop :=
  | Forall3P_nil : forall P, Forall3P R P [] [] []
  | Forall3P_cons : forall P a b c l1 l2 l3,
      R P a b c -> Forall3P R (a :: P) l1 l2 l3 ->
      Forall3P R P (a :: l1) (b :: l2) (c :: l3).

  Theorem generate_all_lsignatures_weakens_ext :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall (R : global -> node -> node -> node -> Prop)
             (Jinv : secglobal -> global -> Prop),
        (forall P nS nM nall, R P nS nM nall ->
           n_name nS = n_name nall /\ node_typed_facts nS nall
           /\ n_name nM = n_name nall /\ node_typed_facts nM nall) ->
        (forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
                accT sgT stT0 stT1,
            R P nS nM nall ->
            generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
            find_node_env nall.(n_name) envsF = Some env ->
            get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
            (st0 <= stN)%positive ->
            lsig_inv stN st0 accT stT0 ->
            Jinv accT P ->
            generate_lnode_sig_scoped_env accT nM envsF auxF stT0
              = OK (sgT, stT1) ->
            Jinv (sgT :: accT) (nS :: P)) ->
        (forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
                accS accT sgS stS0 stS1 sgT stT0 stT1,
            R P nS nM nall ->
            generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
            find_node_env nall.(n_name) envsF = Some env ->
            get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
            (st0 <= stN)%positive ->
            lsig_inv stN st0 accS stS0 ->
            lsig_inv stN st0 accT stT0 ->
            call_weakens accS accT ->
            Jinv accT P ->
            generate_lnode_sig_scoped_env accS nS envsF auxF stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nM envsF auxF stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        forall P0 nsS nsM alls envs0 acc0 st0,
          Forall3P R P0 nsS nsM alls ->
          NoDup (List.map n_name alls) ->
          generate_lnode_scoped_env' alls envs0 acc0 st0
            = OK ((envsF, auxF), stN) ->
          forall accS accT stS stT GS GT stfS stfT,
            lsig_inv stN st0 accS stS ->
            lsig_inv stN st0 accT stT ->
            call_weakens accS accT ->
            sigs_preserved accS accT ->
            Jinv accT P0 ->
            generate_all_lsignatures' accS nsS envsF auxF stS = OK (GS, stfS) ->
            generate_all_lsignatures' accT nsM envsF auxF stT = OK (GT, stfT) ->
            call_weakens GS GT /\ sigs_preserved GS GT /\ Jinv GT
              (List.rev nsS ++ P0).
  Proof.
    intros all envsF auxF stN Hfull R Jinv HR HJ Hstep.
    intros P0 nsS nsM alls. revert P0 nsS nsM.
    induction alls as [|nall alls IH];
      intros P0 nsS nsM envs0 acc0 st0 HF3 Hnd Hrun accS accT stS stT GS GT
        stfS stfT HinvS HinvT Hw Hp Hj HgS HgT.
    - inversion HF3; subst. cbn in HgS, HgT.
      inversion HgS; subst. inversion HgT; subst. cbn.
      repeat split; assumption.
    - inversion HF3 as [|P1 nS nM nall0 nsS' nsM' alls0 HRn HF3']; subst.
      destruct (HR P0 nS nM nall HRn) as (HnameS & (PS & HwlS & HwcgS & HwcnS
                                         & HsrcS & HdisjS & HsubS)
                                         & HnameM & (PM & HwlM & HwcgM & HwcnM
                                         & HsrcM & HdisjM & HsubM)).
      destruct (naming_step_facts envsF auxF stN nall alls envs0 acc0 st0
                  Hnd Hrun) as (le0 & r0 & stl & Hloc & Hfind & Haux & Hst0
                                & Hnd' & Hrec).
      cbn in HgS, HgT.
      destruct (generate_lnode_sig_scoped_env accS nS envsF auxF stS)
        as [[sgS stS1]|e] eqn:HsS; [|discriminate HgS].
      destruct (generate_lnode_sig_scoped_env accT nM envsF auxF stT)
        as [[sgT stT1]|e] eqn:HsT; [|discriminate HgT].
      destruct (Hstep P0 nS nM nall le0 r0 st0 stl accS accT sgS stS stS1 sgT
                  stT stT1 HRn Hloc Hfind Haux Hst0 HinvS HinvT Hw Hj HsS HsT)
        as (Hname & Hpres & Hcall).
      pose proof (HJ P0 nS nM nall le0 r0 st0 stl accT sgT stT stT1 HRn Hloc
                    Hfind Haux Hst0 HinvT Hj HsT) as Hj'.
      unfold generate_lnode_sig_scoped_env in HsS, HsT.
      rewrite HnameS, Hfind in HsS. rewrite HnameM, Hfind in HsT.
      assert (Hrev : List.rev (nS :: nsS') ++ P0 = List.rev nsS' ++ (nS :: P0)).
      { cbn [List.rev]. rewrite <- app_assoc. reflexivity. }
      rewrite Hrev.
      eapply (IH (nS :: P0) nsS' nsM' (Env.add nall.(n_name) le0 envs0)
                 (r0 :: acc0) stl HF3' Hnd' Hrec (sgS :: accS) (sgT :: accT)
                 stS1 stT1 GS GT stfS stfT); try assumption.
      + eapply lsig_step_ext;
          [exact Hfull|rewrite HnameS; exact Hfind|rewrite HnameS; exact Haux
          |exact Hloc|exact Hst0|exact HwlS|exact HwcgS|exact HwcnS|exact HsrcS
          |exact HsubS|exact HinvS|exact HsS].
      + eapply lsig_step_ext;
          [exact Hfull|rewrite HnameM; exact Hfind|rewrite HnameM; exact Haux
          |exact Hloc|exact Hst0|exact HwlM|exact HwcgM|exact HwcnM|exact HsrcM
          |exact HsubM|exact HinvT|exact HsT].
      + exact (call_weakens_cons sgS sgT accS accT Hname Hcall Hw).
      + exact (sigs_preserved_cons sgS sgT accS accT Hname Hpres Hp).
  Qed.


  (** * Leg I, one node *)

  Lemma lsig_inv_head :
    forall stN low sg acc st,
      lsig_inv stN low (sg :: acc) st ->
      signature_good sg /\ signature_scoped sg /\ NoDup (signature_scope sg).
  Proof.
    intros stN low sg acc st (Hg & Hs & Hnd & _).
    assert (Hf : find_signature sg.(s_name) (sg :: acc) = Some sg)
      by (simpl; rewrite ident_eqb_refl; reflexivity).
    split; [exact (Hg _ _ Hf)|split; [exact (Hs _ _ Hf)|]].
    pose proof (Hnd _ _ Hf) as H. unfold sig_nd in H.
    unfold signature_scope. eapply Permutation_NoDup; [|exact H].
    apply Permutation_app_head.
    exact (Permutation_app_comm [sg.(s_clk); sg.(s_reset)] sg.(s_out)).
  Qed.



  Lemma assign_lexp_fby_operands :
    forall G env base_ty rst_ty e0s es ans ts s s',
      assign_lexp_type G env base_ty rst_ty (Efby e0s es ans) s = OK (ts, s') ->
      (exists ts0 r r', assign_lexps G env base_ty rst_ty e0s r = OK (ts0, r'))
      /\ (exists ts1 r r', assign_lexps G env base_ty rst_ty es r = OK (ts1, r')).
  Proof.
    intros G env base_ty rst_ty e0s es ans ts s s' H.
    rewrite assign_lexp_Efby in H.
    apply sec_bind_inv in H as (ts0 & s1 & Hts0 & H).
    apply sec_bind_inv in H as (us & s2 & Hus & _).
    split; [exists ts0, s, s1|exists us, s1, s2]; assumption.
  Qed.

  Lemma assign_lexp_arrow_operands :
    forall G env base_ty rst_ty e0s es ans ts s s',
      assign_lexp_type G env base_ty rst_ty (Earrow e0s es ans) s = OK (ts, s') ->
      (exists ts0 r r', assign_lexps G env base_ty rst_ty e0s r = OK (ts0, r'))
      /\ (exists ts1 r r', assign_lexps G env base_ty rst_ty es r = OK (ts1, r')).
  Proof.
    intros G env base_ty rst_ty e0s es ans ts s s' H.
    rewrite assign_lexp_Earrow in H.
    apply sec_bind_inv in H as (ts0 & s1 & Hts0 & H).
    apply sec_bind_inv in H as (us & s2 & Hus & _).
    split; [exists ts0, s, s1|exists us, s1, s2]; assumption.
  Qed.

  (** A delayed definition in an equation list whose run succeeded: its
      operands were typed at some state. *)
  Lemma leqns_run_exp :
    forall G env base_ty rst_ty ckenv eqs cs s s' x e,
      generate_leqns_constraints G env base_ty rst_ty ckenv eqs s = OK (cs, s') ->
      In ([x], [e]) eqs ->
      (match e with Eapp _ _ _ _ => False | _ => True end) ->
      exists ts r r', assign_lexp_type G env base_ty rst_ty e r = OK (ts, r').
  Proof.
    intros G env base_ty rst_ty ckenv eqs. induction eqs as [|eq eqs IH];
      intros cs s s' x e Hgen Hin Hne.
    - destruct Hin.
    - rewrite generate_leqns_constraints_cons in Hgen.
      apply sec_bind_inv in Hgen as (c1 & s1 & Hc1 & Hgen).
      apply sec_bind_inv in Hgen as (c2 & s2 & Hc2 & Hret).
      destruct Hin as [Heq|Hin].
      + subst eq. rewrite <- generate_lone_is_leqn in Hc1.
        destruct e as [c0|x0 a0|op0 e0 a0|op0 e1 e2 a0|e0s es0 an0|e0s es0 an0
                      |es0 x0 b0 a0|x0 ets efs a0|e0 ets efs a0|f args ro anns];
          try contradiction;
          (cbn [generate_lone_constraint] in Hc1;
           apply generate_ldef_constraint_inv in Hc1
             as (ck & ckty & tf & b & s3 & _ & _ & Hte & _);
           eexists; eexists; eexists; exact Hte).
      + exact (IH c2 s1 s2 x e Hc2 Hin Hne).
  Qed.

  Lemma fby_operands_pure :
    forall G env base_ty rst_ty ckenv (Q : global) eqs cs s s' x e0 e ann,
      generate_leqns_constraints G env base_ty rst_ty ckenv eqs s = OK (cs, s') ->
      Forall (unnested_equation Q) eqs ->
      In ([x], [Efby [e0] [e] [ann]]) eqs ->
      (exists s0, forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
      /\ (exists s1, forall r, assign_lexp_type G env base_ty rst_ty e r
                               = OK ([(s1, [])], r)).
  Proof.
    intros G env base_ty rst_ty ckenv Q eqs cs s s' x e0 e ann Hgen Hun Hin.
    destruct (leqns_run_exp G env base_ty rst_ty ckenv eqs cs s s' x
                (Efby [e0] [e] [ann]) Hgen Hin I) as (ts & r & r' & Hrun).
    destruct (assign_lexp_fby_operands G env base_ty rst_ty [e0] [e] [ann] ts
                r r' Hrun) as ((ts0 & ra & ra' & H0) & (ts1 & rb & rb' & H1)).
    rewrite Forall_forall in Hun.
    pose proof (Hun _ Hin) as Hu.
    inversion Hu; subst;
      try (exfalso;
           match goal with
           | H : normalized_cexp _ |- _ =>
               inversion H; subst;
               try (match goal with H2 : normalized_lexp _ |- _ => inversion H2 end)
           end).
    - assert (Hn0 : normalized_cexp e0) by (apply normalized_lexp_cexp; assumption).
      assert (Hn1 : normalized_cexp e) by (apply normalized_lexp_cexp; assumption).
      apply assign_lexps_single in H0. apply assign_lexps_single in H1.
      destruct (assign_lexp_normalized_cexp_pure G env base_ty rst_ty e0 Hn0
                  ts0 ra ra' H0) as (_ & Hl0 & Hc0 & Hs0).
      destruct (assign_lexp_normalized_cexp_pure G env base_ty rst_ty e Hn1
                  ts1 rb rb' H1) as (_ & Hl1 & Hc1 & Hs1).
      destruct ts0 as [|t0 [|]]; simpl in Hl0; try discriminate.
      destruct ts1 as [|t1 [|]]; simpl in Hl1; try discriminate.
      rewrite carried_single in Hc0, Hc1.
      destruct t0 as (s0 & rho0). destruct t1 as (s1 & rho1).
      cbn [snd] in Hc0, Hc1. subst rho0 rho1.
      split; [exists s0|exists s1]; assumption.
  Qed.

  Lemma arrow_operands_pure :
    forall G env base_ty rst_ty ckenv (Q : global) eqs cs s s' x e0 e ann,
      generate_leqns_constraints G env base_ty rst_ty ckenv eqs s = OK (cs, s') ->
      Forall (unnested_equation Q) eqs ->
      In ([x], [Earrow [e0] [e] [ann]]) eqs ->
      (exists s0, forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
      /\ (exists s1, forall r, assign_lexp_type G env base_ty rst_ty e r
                               = OK ([(s1, [])], r)).
  Proof.
    intros G env base_ty rst_ty ckenv Q eqs cs s s' x e0 e ann Hgen Hun Hin.
    destruct (leqns_run_exp G env base_ty rst_ty ckenv eqs cs s s' x
                (Earrow [e0] [e] [ann]) Hgen Hin I) as (ts & r & r' & Hrun).
    destruct (assign_lexp_arrow_operands G env base_ty rst_ty [e0] [e] [ann] ts
                r r' Hrun) as ((ts0 & ra & ra' & H0) & (ts1 & rb & rb' & H1)).
    rewrite Forall_forall in Hun.
    pose proof (Hun _ Hin) as Hu.
    inversion Hu; subst;
      try (exfalso;
           match goal with
           | H : normalized_cexp _ |- _ =>
               inversion H; subst;
               try (match goal with H2 : normalized_lexp _ |- _ => inversion H2 end)
           end).
    - assert (Hn0 : normalized_cexp e0) by (apply normalized_lexp_cexp; assumption).
      assert (Hn1 : normalized_cexp e) by (apply normalized_lexp_cexp; assumption).
      apply assign_lexps_single in H0. apply assign_lexps_single in H1.
      destruct (assign_lexp_normalized_cexp_pure G env base_ty rst_ty e0 Hn0
                  ts0 ra ra' H0) as (_ & Hl0 & Hc0 & Hs0).
      destruct (assign_lexp_normalized_cexp_pure G env base_ty rst_ty e Hn1
                  ts1 rb rb' H1) as (_ & Hl1 & Hc1 & Hs1).
      destruct ts0 as [|t0 [|]]; simpl in Hl0; try discriminate.
      destruct ts1 as [|t1 [|]]; simpl in Hl1; try discriminate.
      rewrite carried_single in Hc0, Hc1.
      destruct t0 as (s0 & rho0). destruct t1 as (s1 & rho1).
      cbn [snd] in Hc0, Hc1. subst rho0 rho1.
      split; [exists s0|exists s1]; assumption.
  Qed.

  Lemma created_disj :
    forall {A : Type} (a b c d : list (ident * A)) y,
      NoDupMembers (a ++ (b ++ c) ++ d) ->
      InMembers y c ->
      ~ In y (List.map fst a) /\ ~ In y (List.map fst b)
      /\ ~ In y (List.map fst d).
  Proof.
    intros A a b c d y Hnd Hc.
    rewrite <- !fst_InMembers.
    pose proof (NoDupMembers_app_r _ _ Hnd) as Hnd1.
    pose proof (NoDupMembers_app_l _ _ Hnd1) as Hnd2.
    repeat split.
    - intro Ha.
      apply (NoDupMembers_app_InMembers y a ((b ++ c) ++ d) Hnd Ha).
      rewrite !InMembers_app. left. right. exact Hc.
    - intro Hb.
      apply (NoDupMembers_app_InMembers y b c Hnd2 Hb Hc).
    - intro Hd.
      apply (NoDupMembers_app_InMembers_l y (b ++ c) d Hnd1 Hd).
      rewrite !InMembers_app. now right.
  Qed.

  Lemma node_wc_clock_facts :
    forall P (n : node),
      wc_node P n ->
      wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      /\ (forall x ck,
            In x (List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
            find_clock (lnode_clock_env n) x = OK ck ->
            incl (clock_vars ck)
              (List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))).
  Proof.
    intros P n Hwcn.
    destruct Hwcn as (_ & _ & Hwenv0 & _).
    assert (Hwenv : wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { assert (Permutation (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                (idck (n.(n_in) ++ n.(n_out) ++ n.(n_vars)))) as Hperm.
      { unfold idck. apply Permutation_map.
        apply Permutation_app_head. apply Permutation_app_comm. }
      rewrite Hperm. exact Hwenv0. }
    split; [exact Hwenv|].
    intros x ck Hx Hfc.
    assert (Hvm : List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold idck; rewrite map_map; reflexivity).
    rewrite Hvm in Hx.
    apply in_map_iff in Hx as ((x' & tc) & Hxe & Hin). cbn in Hxe. subst x'.
    rewrite (lnode_clock_env_find n x tc Hin) in Hfc.
    inversion Hfc; subst ck.
    assert (Hv : In (x, snd tc) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { unfold idck. apply in_map_iff. exists (x, tc). split;
        [reflexivity|exact Hin]. }
    unfold wc_env in Hwenv. rewrite Forall_forall in Hwenv.
    intros y Hy.
    destruct (clock_vars_wc _ (snd tc) (Hwenv _ Hv) y Hy) as (cky & Hyv).
    apply in_map_iff. exists (y, cky). split; [reflexivity|exact Hyv].
  Qed.

  Lemma delayed_children :
    forall P vars AN E e0 e a,
      (E = Efby [e0] [e] [a] \/ E = Earrow [e0] [e] [a]) ->
      wc_exp P vars E -> src_exp vars AN E ->
      wc_exp P vars e0 /\ wc_exp P vars e /\ src_exp vars AN e0
      /\ src_exp vars AN e.
  Proof.
    intros P vars AN E e0 e a HE Hw Hs.
    destruct HE as [HE|HE]; subst E.
    - destruct (wc_Efby_sub P vars _ _ _ Hw) as (H0 & H1).
      refine (conj (Forall_inv H0) (conj (Forall_inv H1) (conj _ _))).
      + exact (src_exp_imm vars AN _ _ (imm_Efby_0 [e0] [e] [a] e0 (or_introl Logic.eq_refl)) Hs).
      + exact (src_exp_imm vars AN _ _ (imm_Efby_1 [e0] [e] [a] e (or_introl Logic.eq_refl)) Hs).
    - destruct (wc_Earrow_sub P vars _ _ _ Hw) as (H0 & H1).
      refine (conj (Forall_inv H0) (conj (Forall_inv H1) (conj _ _))).
      + exact (src_exp_imm vars AN _ _ (imm_Earrow_0 [e0] [e] [a] e0 (or_introl Logic.eq_refl)) Hs).
      + exact (src_exp_imm vars AN _ _ (imm_Earrow_1 [e0] [e] [a] e (or_introl Logic.eq_refl)) Hs).
  Qed.

  Lemma delayed_operands_pure :
    forall G env base_ty rst_ty ckenv (Q : global) eqs cs s s' x E e0 e a,
      (E = Efby [e0] [e] [a] \/ E = Earrow [e0] [e] [a]) ->
      generate_leqns_constraints G env base_ty rst_ty ckenv eqs s = OK (cs, s') ->
      Forall (unnested_equation Q) eqs ->
      In ([x], [E]) eqs ->
      (exists s0, forall r, assign_lexp_type G env base_ty rst_ty e0 r
                            = OK ([(s0, [])], r))
      /\ (exists s1, forall r, assign_lexp_type G env base_ty rst_ty e r
                               = OK ([(s1, [])], r)).
  Proof.
    intros G env base_ty rst_ty ckenv Q eqs cs s s' x E e0 e a HE Hgen Hun Hin.
    destruct HE as [HE|HE]; subst E.
    - exact (fby_operands_pure G env base_ty rst_ty ckenv Q eqs cs s s' x e0 e a
               Hgen Hun Hin).
    - exact (arrow_operands_pure G env base_ty rst_ty ckenv Q eqs cs s s' x e0 e a
               Hgen Hun Hin).
  Qed.

  Section PassFacts.
  Import UNN.Fresh.Facts.
  Import UNN.Fresh.Tactics.

  (** * Pass fact: the clocks of the variables fby normalisation creates

      Every variable the pass adds is annotated with the clock of a [fby] or
      [->] it rewrites, so its clock mentions only the variables that clock
      already mentioned. *)

  Definition anns_clocks_in (V : list ident)
             (l : list (ident * ((type * clock) * bool))) : Prop :=
    forall y a, In (y, a) l -> incl (clock_vars (snd (fst a))) V.

  Definition eq_ann_clock_in (V : list ident) (eq : equation) : Prop :=
    forall e0 e ann,
      (snd eq = [Efby [e0] [e] [ann]] \/ snd eq = [Earrow [e0] [e] [ann]]) ->
      incl (clock_vars (fst (snd ann))) V.

  Lemma fresh_ident_anns_clocks_in :
    forall V b id st st',
      fresh_ident norm2 b st = (id, st') ->
      anns_clocks_in V (st_anns st) ->
      incl (clock_vars (snd (fst b))) V ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V b id st st' Hf Hst Hb.
    rewrite (fresh_ident_anns _ _ _ _ _ Hf).
    intros y a [H|H]; [inversion H; subst; exact Hb|exact (Hst y a H)].
  Qed.

  Lemma init_var_anns_clocks_in :
    forall V cl res st st',
      init_var_for_clock cl st = (res, st') ->
      incl (clock_vars cl) V ->
      anns_clocks_in V (st_anns st) ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V cl res st st' Hinit Hcl Hst.
    unfold init_var_for_clock in Hinit. repeat inv_bind.
    destruct (find _ _) as [p|].
    - destruct p. inversion Hinit; subst. exact Hst.
    - destruct (fresh_ident _ _ _) eqn:Hf. inversion Hinit; subst.
      eapply fresh_ident_anns_clocks_in; [exact Hf|exact Hst|exact Hcl].
  Qed.

  Lemma fby_iteexp_anns_clocks_in :
    forall V e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      incl (clock_vars (fst (snd ann))) V ->
      anns_clocks_in V (st_anns st) ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V e0 e (ty & ck & nm) e' eqs' st st' Hf Hck Hst. cbn in Hck.
    unfold fby_iteexp in Hf. repeat inv_bind.
    eapply fresh_ident_anns_clocks_in;
      [eassumption| |exact Hck].
    eapply init_var_anns_clocks_in; [eassumption|exact Hck|exact Hst].
  Qed.

  Lemma arrow_iteexp_anns_clocks_in :
    forall V e0 e ann e' eqs' st st',
      arrow_iteexp e0 e ann st = (e', eqs', st') ->
      incl (clock_vars (fst (snd ann))) V ->
      anns_clocks_in V (st_anns st) ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V e0 e (ty & ck & nm) e' eqs' st st' Hf Hck Hst. cbn in Hck.
    unfold arrow_iteexp in Hf. repeat inv_bind.
    eapply init_var_anns_clocks_in; [eassumption|exact Hck|exact Hst].
  Qed.

  Lemma fby_equation_anns_clocks_in :
    forall V to_cut eq eqs' st st',
      eq_ann_clock_in V eq ->
      anns_clocks_in V (st_anns st) ->
      fby_equation to_cut eq st = (eqs', st') ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V to_cut eq eqs' st st' Hann Hst Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x2 as (ty & ck & nm).
      pose proof (Hann x0 x1 (ty, (ck, nm)) (or_introl Logic.eq_refl)) as Hck.
      cbn in Hck.
      destruct (PS.mem _ _); repeat inv_bind; auto.
      eapply fresh_ident_anns_clocks_in; [eassumption|exact Hst|exact Hck].
    - eapply fby_iteexp_anns_clocks_in; [eassumption| |exact Hst].
      exact (Hann _ _ _ (or_introl Logic.eq_refl)).
    - eapply arrow_iteexp_anns_clocks_in; [eassumption| |exact Hst].
      exact (Hann _ _ _ (or_intror Logic.eq_refl)).
  Qed.

  Lemma map_bind_fby_anns_clocks_in :
    forall V to_cut eqs eqs' st st',
      Forall (eq_ann_clock_in V) eqs ->
      anns_clocks_in V (st_anns st) ->
      map_bind (fby_equation to_cut) eqs st = (eqs', st') ->
      anns_clocks_in V (st_anns st').
  Proof.
    intros V to_cut. induction eqs as [|eq eqs IH]; intros eqs' st st' Hf Hst Hm;
      cbn [map_bind] in Hm; repeat inv_bind; auto.
    inversion Hf; subst.
    eapply IH; [assumption| |eassumption].
    eapply fby_equation_anns_clocks_in; eassumption.
  Qed.

  Lemma normalized_lexp_fresh_in :
    forall e, normalized_lexp e -> fresh_in e = [].
  Proof.
    intros e H. induction H; cbn [fresh_in]; try reflexivity.
    - exact IHnormalized_lexp.
    - rewrite IHnormalized_lexp1, IHnormalized_lexp2. reflexivity.
    - cbn [map concat]. rewrite app_nil_r. exact IHnormalized_lexp.
  Qed.

  Lemma eq_ann_clock_in_of_wc :
    forall Q vars eq,
      wc_global Q ->
      wc_env vars ->
      unnested_equation Q eq ->
      wc_equation Q vars eq ->
      eq_ann_clock_in (List.map fst vars) eq.
  Proof.
    intros Q vars (xs, es) Hg Hwe Hun Hwc e0 e ann Hs.
    destruct Hwc as (Hwc & _ & _). cbn [snd] in Hs.
    assert (Hn0 : normalized_lexp e0).
    { destruct Hs as [Hs|Hs]; subst es; inversion Hun; subst;
        first [assumption
              |(match goal with
                | H : normalized_cexp (Efby _ _ _) |- _ =>
                  exfalso; inversion H as [| |e1 Hl]; inversion Hl
                | H : normalized_cexp (Earrow _ _ _) |- _ =>
                  exfalso; inversion H as [| |e1 Hl]; inversion Hl
                end)]. }
    assert (Hck : Forall2 (@Logic.eq clock) (List.map clock_of_nclock [ann]) (clocksof [e0])).
    { destruct Hs as [Hs|Hs]; subst es;
        inversion Hwc as [|? ? Hw _]; subst; inversion Hw; subst; assumption. }
    rewrite Forall2_eq in Hck.
    unfold clocksof in Hck. cbn [flat_map] in Hck. rewrite app_nil_r in Hck.
    assert (Hw0 : wc_exp Q vars e0).
    { destruct Hs as [Hs|Hs]; subst es;
        inversion Hwc as [|? ? Hw _]; subst; inversion Hw; subst;
        match goal with H : Forall (wc_exp _ _) [_] |- _ =>
          exact (Forall_inv H) end. }
    pose proof (wc_exp_clockof Q vars e0 Hg Hwe Hw0) as Hcl.
    rewrite (normalized_lexp_fresh_in e0 Hn0) in Hcl.
    cbn [idck map app] in Hcl. rewrite app_nil_r in Hcl.
    assert (Hin : In (clock_of_nclock ann) (clockof e0)).
    { cbn [List.map] in Hck. rewrite <- Hck. left. reflexivity. }
    rewrite Forall_forall in Hcl.
    intros y Hy.
    destruct (clock_vars_wc vars _ (Hcl _ Hin) y) as (cky & Hyv).
    - exact Hy.
    - apply in_map_iff. exists (y, cky). split; [reflexivity|exact Hyv].
  Qed.

  Lemma normfby_clocks_pass_fact :
    forall Q c (n : node),
      wc_global Q ->
      wc_node Q n ->
      unnested_node Q n ->
      forall eqs' stf,
        map_bind (fby_equation
                    (PS.union c (ps_from_list (List.map fst (n_out n)))))
          n.(n_eqs) init_st = (eqs', stf) ->
        forall y a, In (y, a) (st_anns stf) ->
          incl (clock_vars (snd (fst a)))
            (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
  Proof.
    intros Q c n Hg Hwcn Hun eqs' stf Hrun y a Hya.
    destruct (node_wc_clock_facts Q n Hwcn) as (Hwenv & _).
    destruct Hwcn as (_ & _ & _ & Hweqs).
    assert (Hvm : List.map fst (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold idck; rewrite map_map; reflexivity).
    rewrite <- Hvm.
    refine (map_bind_fby_anns_clocks_in _ _ _ _ init_st stf _ _ Hrun y a Hya).
    - unfold unnested_node in Hun.
      rewrite Forall_forall in Hun, Hweqs |- *. intros eq Hin.
      exact (eq_ann_clock_in_of_wc Q _ eq Hg Hwenv (Hun eq Hin) (Hweqs eq Hin)).
    - rewrite init_st_anns. intros y0 a0 [].
  Qed.

  End PassFacts.

  (** * Unnested and normalised nodes have no anonymous streams

      Nested calls are what carry anonymous names; the operands of an
      unnested equation contain none. *)

  Lemma normalized_cexp_fresh_in :
    forall e, normalized_cexp e -> fresh_in e = [].
  Proof.
    intros e H. induction H; cbn [fresh_in].
    - cbn [map concat]. rewrite !app_nil_r, IHnormalized_cexp1,
        IHnormalized_cexp2. reflexivity.
    - cbn [map concat]. rewrite !app_nil_r, IHnormalized_cexp1,
        IHnormalized_cexp2, (normalized_lexp_fresh_in _ H). reflexivity.
    - exact (normalized_lexp_fresh_in _ H).
  Qed.

  Lemma normalized_constant_fresh_in :
    forall e, normalized_constant e -> fresh_in e = [].
  Proof.
    intros e H. induction H; cbn [fresh_in]; [reflexivity|].
    cbn [map concat]. rewrite app_nil_r. exact IHnormalized_constant.
  Qed.

  Lemma anon_in_nil_of_fresh_in :
    forall e, fresh_in e = [] -> (forall f es r a, e <> Eapp f es r a) ->
              anon_in e = [].
  Proof.
    intros e H Hne. destruct e; cbn [anon_in]; try exact H.
    exfalso. eapply Hne. reflexivity.
  Qed.

  Lemma normalized_lexps_fresh_ins :
    forall es, Forall normalized_lexp es -> concat (List.map fresh_in es) = [].
  Proof.
    intros es H. induction H as [|e0 es0 He Hes IH]; [reflexivity|].
    cbn [List.map concat]. rewrite (normalized_lexp_fresh_in _ He), IH.
    reflexivity.
  Qed.

  Lemma normalized_lexp_anon_in :
    forall e, normalized_lexp e -> anon_in e = [].
  Proof.
    intros e H. pose proof (normalized_lexp_fresh_in e H) as Hf.
    destruct H; exact Hf.
  Qed.

  Lemma normalized_cexp_anon_in :
    forall e, normalized_cexp e -> anon_in e = [].
  Proof.
    intros e H. pose proof (normalized_cexp_fresh_in e H) as Hf.
    destruct H; [exact Hf|exact Hf|exact (normalized_lexp_anon_in _ H)].
  Qed.

  Lemma unnested_equation_anon_in :
    forall G eq, unnested_equation G eq -> anon_in_eq eq = [].
  Proof.
    intros G eq H. unfold anon_in_eq, anon_ins.
    inversion H as [xs0 f0 n0 es0 lann0 Hn Hf Hk
                   | xs0 f0 n0 es0 x0 ty0 cl0 lann0 Hn Hf Hk
                   | x0 e0 e1 ann0 H0 H1 | x0 e0 e1 ann0 H0 H1 | x0 e0 Hc];
      subst; cbn [snd List.map concat]; rewrite app_nil_r.
    - exact (normalized_lexps_fresh_ins _ Hn).
    - change (fresh_ins es0 ++ fresh_in (Evar x0 (ty0, cl0)) = []).
      cbn [fresh_in]. rewrite app_nil_r.
      exact (normalized_lexps_fresh_ins _ Hn).
    - cbn [anon_in fresh_in List.map concat].
      rewrite !app_nil_r, (normalized_lexp_fresh_in _ H0),
        (normalized_lexp_fresh_in _ H1). reflexivity.
    - cbn [anon_in fresh_in List.map concat].
      rewrite !app_nil_r, (normalized_lexp_fresh_in _ H0),
        (normalized_lexp_fresh_in _ H1). reflexivity.
    - exact (normalized_cexp_anon_in _ Hc).
  Qed.

  Lemma normalized_equation_anon_in :
    forall G out eq, normalized_equation G out eq -> anon_in_eq eq = [].
  Proof.
    intros G out eq H. unfold anon_in_eq, anon_ins.
    inversion H as [out0 xs0 f0 n0 es0 lann0 Hn Hf Hk
                   | out0 xs0 f0 n0 es0 x0 ty0 cl0 lann0 Hn Hf Hk
                   | out0 x0 e0 e1 ann0 Hno H0 H1 | out0 x0 e0 Hc];
      subst; cbn [snd List.map concat]; rewrite app_nil_r.
    - exact (normalized_lexps_fresh_ins _ Hn).
    - change (fresh_ins es0 ++ fresh_in (Evar x0 (ty0, cl0)) = []).
      cbn [fresh_in]. rewrite app_nil_r.
      exact (normalized_lexps_fresh_ins _ Hn).
    - cbn [anon_in fresh_in List.map concat].
      rewrite !app_nil_r, (normalized_constant_fresh_in _ H0),
        (normalized_lexp_fresh_in _ H1). reflexivity.
    - exact (normalized_cexp_anon_in _ Hc).
  Qed.

  Lemma anon_names_unnested :
    forall G (n : node), unnested_node G n -> anon_names n = [].
  Proof.
    intros G n H. unfold anon_names, anon_in_eqs.
    assert (Hz : concat (List.map anon_in_eq (n_eqs n)) = []).
    { unfold unnested_node in H.
      induction (n_eqs n) as [|eq eqs IH]; [reflexivity|].
      inversion H as [|? ? He Hes]; subst. cbn [List.map concat].
      rewrite (unnested_equation_anon_in _ _ He), (IH Hes). reflexivity. }
    rewrite Hz. reflexivity.
  Qed.

  Lemma anon_names_normalized :
    forall G (n : node), normalized_node G n -> anon_names n = [].
  Proof.
    intros G n H. unfold anon_names, anon_in_eqs.
    assert (Hz : concat (List.map anon_in_eq (n_eqs n)) = []).
    { unfold normalized_node in H.
      induction (n_eqs n) as [|eq eqs IH]; [reflexivity|].
      inversion H as [|? ? He Hes]; subst. cbn [List.map concat].
      rewrite (normalized_equation_anon_in _ _ _ He), (IH Hes). reflexivity. }
    rewrite Hz. reflexivity.
  Qed.


  Lemma normfby_instance :
    forall (all : list node) envsF auxF stN
           Q c (n : node) (Hunt : unnested_node Q n)
           (Hpref : n_prefixes n = norm1_prefs)
           (env : Env.t ident) (r : node_aux_names) st0 stl
           accS accT sgS stS0 stS1 sgT stT0 stT1,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      generate_local_env_for_lnode (normfby_node Q c n Hunt Hpref) st0
        = OK ((env, r), stl) ->
      find_node_env n.(n_name) envsF = Some env ->
      get_node_aux n.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
      (st0 <= stN)%positive ->
      lsig_inv stN st0 accS stS0 ->
      lsig_inv stN st0 accT stT0 ->
      call_weakens accS accT ->
      node_typed_facts n (normfby_node Q c n Hunt Hpref) ->
      node_typed_facts (normfby_node Q c n Hunt Hpref)
        (normfby_node Q c n Hunt Hpref) ->
      (forall eqs' stf,
          map_bind (fby_equation
                      (PS.union c (ps_from_list (List.map fst (n_out n)))))
            n.(n_eqs) init_st = (eqs', stf) ->
          forall y a, In (y, a) (st_anns stf) ->
            incl (clock_vars (snd (fst a)))
              (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
      generate_lnode_sig_scoped_env accS n envsF auxF stS0 = OK (sgS, stS1) ->
      generate_lnode_sig_scoped_env accT (normfby_node Q c n Hunt Hpref)
        envsF auxF stT0 = OK (sgT, stT1) ->
      sig_head_weakens sgS sgT.
  Proof.
    intros all envsF auxF stN Q c n Hunt Hpref env r st0 stl accS accT sgS stS0
      stS1 sgT stT0 stT1 Hfull Hloc Hfind Haux0 Hst0 HinvS HinvT Hw HfS HfT
      Hclkc HsS0 HsT0.
    set (N := normfby_node Q c n Hunt Hpref) in *.
    destruct HfS as (P & HwlS & HwcgS & HwcnS & HsrcS & HdisjS & HsubS).
    destruct HfT as (PT & HwlT & HwcgT & HwcnT & HsrcT & HdisjT & HsubT).
    assert (HfindN : find_node_env (n_name N) envsF = Some env) by exact Hfind.
    assert (HauxN : get_node_aux (n_name N) auxF = Some (r.(nclk), r.(nrst)))
      by exact Haux0.
    assert (HsS : generate_lnode_sig accS n env auxF stS0 = OK (sgS, stS1)).
    { unfold generate_lnode_sig_scoped_env in HsS0. rewrite Hfind in HsS0.
      exact HsS0. }
    assert (HsT : generate_lnode_sig accT N env auxF stT0 = OK (sgT, stT1)).
    { unfold generate_lnode_sig_scoped_env in HsT0. rewrite HfindN in HsT0.
      exact HsT0. }
    assert (HinvS' : lsig_inv stN stl (sgS :: accS) stS1)
      by (eapply lsig_step_ext;
          [exact Hfull|exact Hfind|exact Haux0|exact Hloc|exact Hst0|exact HwlS
          |exact HwcgS|exact HwcnS|exact HsrcS|exact HsubS
          |exact HinvS|exact HsS]).
    assert (HinvT' : lsig_inv stN stl (sgT :: accT) stT1)
      by (eapply lsig_step_ext;
          [exact Hfull|exact HfindN|exact HauxN|exact Hloc|exact Hst0|exact HwlT
          |exact HwcgT|exact HwcnT|exact HsrcT|exact HsubT
          |exact HinvT|exact HsT]).
    destruct (lsig_inv_head _ _ _ _ _ HinvS') as (Hgs & Hscs & Hnds).
    destruct (lsig_inv_head _ _ _ _ _ HinvT') as (Hgt & Hsct & Hndt).
    destruct HinvS as (HgoodS0 & HscS0 & HndS0 & HrootS0 & HbdS0 & HleS0).
    destruct HinvT as (HgoodT0 & HscT0 & HndT0 & HrootT0 & HbdT0 & HleT0).
    destruct (generate_local_env_for_lnode_facts N st0 env r stl Hloc)
      as (Hinj & Hrng & Hclk0 & Hrst0).
    destruct (lnode_sig_inv env accS n auxF sgS stS0 stS1 HsS)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hlocs & Hcns & HsgS).
    assert (Hci : ci = nclk r /\ ri = nrst r)
      by (rewrite Haux0 in Haux; inversion Haux; split; reflexivity).
    destruct Hci as (-> & ->).
    assert (Hi : inp = CALLS.sec_of env (List.map fst n.(n_in)))
      by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (Ho : out = CALLS.sec_of env (List.map fst n.(n_out)))
      by (eapply get_mappings_from_node_sec_of; exact Hout).
    assert (Hl : locals = CALLS.sec_of env (List.map fst n.(n_vars)))
      by (eapply get_mappings_from_node_sec_of; exact Hlocs).
    set (scope := CALLS.sec_of env
                    (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  ++ [ct; rt]).
    set (scope0 := CALLS.sec_of env (List.map fst (n.(n_in) ++ n.(n_out)))
                   ++ [ct; rt]).
    assert (Hsub0 : incl scope0 scope).
    { intros z Hz. unfold scope0, scope in *.
      apply in_app_or in Hz as [Hz|Hz]; apply in_or_app.
      - left. revert z Hz. apply sec_of_incl. intros y Hy.
        rewrite !map_app in *.
        apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
          [now left|right; apply in_or_app; now right].
      - right. exact Hz. }
    assert (Hbs : In ct scope) by (unfold scope; apply in_or_app; right; cbn; auto).
    assert (Hrs : In rt scope) by (unfold scope; apply in_or_app; right; cbn; auto).
    assert (Hsep : forall s s', sec_le stN s ->
                     forall x b, Env.find x env = Some b -> ~ In b (minted s s'))
      by (intros s s' Hle x b Hb;
          exact (env_apart_from_minted all envsF auxF stN (n_name N) env s s'
                   Hfull HfindN Hle x b Hb)).
    set (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    assert (Hvm : List.map fst vars
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold vars, idck; rewrite map_map; reflexivity).
    assert (Hrg : forall x b, In x (List.map fst vars) ->
                              Env.find x env = Some b -> In b scope).
    { intros x b Hx Hf. rewrite Hvm in Hx. unfold scope.
      apply in_or_app. left. exact (sec_of_In_intro env _ x b Hx Hf). }
    destruct (node_wc_clock_facts P n HwcnS) as (Hwenv & Hcenv).
    assert (Hclk : clk_scoped_wc accT env ct rt P vars (lnode_clock_env n) scope)
      by exact (clk_scoped_wc_holds accT env ct rt (lnode_clock_env n) P vars
                  scope scope Hbs Hrg Hwenv Hcenv (incl_refl _) HwcgS).
    assert (Hfi : n_in N = n.(n_in)) by reflexivity.
    assert (Hfo : n_out N = n.(n_out)) by reflexivity.
    assert (Hfv : n_vars N
                  = n.(n_vars)
                    ++ idty (st_anns
                               (snd (fby_equations
                                       (PS.union c (ps_from_list
                                                      (List.map fst (n_out n))))
                                       n.(n_eqs) init_st)))) by reflexivity.
    (** fresh-ness of the call instantiations the source run makes *)
    set (D := env_images env).
    assert (Hdeclall : forall y, In y D -> name_above st0 y).
    { intros y Hy. unfold D, env_images in Hy.
      apply in_map_iff in Hy as ((x & b) & Hxb & Hin). cbn in Hxb. subst b.
      apply Env.elements_complete in Hin.
      destruct (Hrng x y Hin) as (k & Hk & Hlo & _). exists k. split; assumption. }
    assert (HdkA : decl_ok env ct rt D).
    { split; [|split].
      - exact (env_images_spec env _ _ Hct).
      - exact (env_images_spec env _ _ Hrt).
      - exact (fun x b H => env_images_spec env x b H). }
    assert (HclkA : clk_scoped env ct D).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env;
        [exact (env_images_spec env _ _ Hct)
        |exact (fun x b H => env_images_spec env x b H)|exact Hck]. }
    assert (Hef : eapp_fresh_prop accS env ct rt st0)
      by exact (eapp_fresh_prop_holds accS env ct rt D st0 HdkA HclkA HscS0
                  Hdeclall HbdS0).
    assert (Hlf : lcall_fresh_prop accS env ct rt st0)
      by exact (lcall_fresh_prop_holds accS env ct rt D st0 HdkA HclkA HscS0
                  Hdeclall HbdS0 Hinj).
    assert (Hlo : sec_le st0 stS0) by exact (Pos.le_trans _ _ _ Hst0 HleS0).
    destruct (generate_leqns_constraints_weaken accS accT env ct rt
                (lnode_clock_env n) n.(n_eqs) cns stS0 stS1 st0 Hw Hef Hlf
                (NoDup_vars_defined_n_eqs n) Hlo Hcns)
      as (cs' & Hcns' & _).
    pose proof (normalized_node_unnested_node Q N
                  (normfby_node_normalized_node Q n c Hunt Hpref)) as Hunn.
    assert (Hndv : NoDupMembers (n_in N ++ n_vars N ++ n_out N)).
    { pose proof (n_nodup N) as Hnd. rewrite !app_assoc in Hnd.
      apply NoDupMembers_app_l in Hnd. rewrite <- !app_assoc in Hnd.
      exact Hnd. }
    assert (Hkeys : forall x, In x (List.map fst (n.(n_in) ++ n.(n_vars)
                                                  ++ n.(n_out))) ->
                              exists b, Env.find x env = Some b).
    { intros x Hx.
      apply (generate_local_env_for_lnode_binds N st0 env r stl Hloc x).
      right. right. rewrite Hfi, Hfv, Hfo.
      apply in_map_iff in Hx as (p & Hpx & Hp).
      apply in_map_iff. exists p. split; [exact Hpx|].
      apply in_app_or in Hp as [Hp|Hp].
      - apply in_or_app. now left.
      - apply in_or_app. right. apply in_app_or in Hp as [Hp|Hp].
        + apply in_or_app. left. apply in_or_app. now left.
        + apply in_or_app. now right. }
    assert (Hnotaux : ~ In (nclk r) (List.map fst (n_in N ++ n_vars N ++ n_out N))
                      /\ ~ In (nrst r) (List.map fst (n_in N ++ n_vars N
                                                      ++ n_out N))).
    { split; intro Hin.
      - exact (lnode_var_not_sec N _ st0 HsubT Hin Hclk0).
      - exact (lnode_var_not_sec N _ (Pos.succ st0) HsubT Hin Hrst0). }
    assert (Hstate : forall eqs' stf,
              map_bind (fby_equation
                          (PS.union c (ps_from_list (List.map fst (n_out n)))))
                n.(n_eqs) init_st = (eqs', stf) ->
              (forall y a, In (y, a) (st_anns stf) ->
                  exists d, Env.find y env = Some d /\ ~ In d scope)
              /\ (forall v a, In (v, a) (st_anns stf) ->
                    exists ckty,
                      assign_clk_type env ct (snd (fst a)) = Some ckty
                      /\ (forall z, In z ckty -> In z scope))).
    { intros eqs' stf Hrun.
      assert (Hfbys : fby_equations
                        (PS.union c (ps_from_list (List.map fst (n_out n))))
                        n.(n_eqs) init_st = (List.concat eqs', stf)).
      { unfold fby_equations. apply bind_spec. exists eqs', stf.
        split; [exact Hrun|apply ret_spec]. }
      assert (HNv : n_vars N = n.(n_vars) ++ idty (st_anns stf)).
      { rewrite Hfv, Hfbys. reflexivity. }
      split.
      - intros y a Hya.
        assert (HyN : In y (List.map fst (n_in N ++ n_vars N ++ n_out N))).
        { rewrite HNv, !map_app, map_fst_idty.
          apply in_or_app. right. apply in_or_app. left.
          apply in_or_app. right. apply in_map_iff. exists (y, a).
          split; [reflexivity|exact Hya]. }
        destruct (generate_local_env_for_lnode_binds N st0 env r stl Hloc y)
          as (d & Hd); [right; right; exact HyN|].
        exists d. split; [exact Hd|].
        intro Hdin. unfold scope in Hdin.
        apply in_app_or in Hdin as [Hdin|Hdin].
        + apply sec_of_In_inv in Hdin as (x & Hx & Hxd).
          assert (x = y) as Hxy
            by (eapply Hinj; [exact Hxd|exact Hd|reflexivity]).
          subst x.
          pose proof Hndv as Hnd2. rewrite HNv in Hnd2.
          rewrite Hfi, Hfo in Hnd2.
          assert (HyC : InMembers y (idty (st_anns stf))).
          { apply fst_InMembers. rewrite map_fst_idty.
            apply in_map_iff. exists (y, a). split; [reflexivity|exact Hya]. }
          destruct (created_disj (n_in n) (n_vars n) (idty (st_anns stf))
                      (n_out n) y Hnd2 HyC) as (H1 & H2 & H3).
          rewrite !map_app in Hx.
          apply in_app_or in Hx as [Hx|Hx]; [exact (H1 Hx)|].
          apply in_app_or in Hx as [Hx|Hx]; [exact (H2 Hx)|exact (H3 Hx)].
        + destruct Hdin as [<-|[<-|[]]].
          * assert (y = nclk r) as Hy
              by (eapply Hinj; [exact Hd|exact Hct|reflexivity]).
            subst y. exact (proj1 Hnotaux HyN).
          * assert (y = nrst r) as Hy
              by (eapply Hinj; [exact Hd|exact Hrt|reflexivity]).
            subst y. exact (proj2 Hnotaux HyN).
      - intros v a Hva.
        assert (Htot : exists ckty, assign_clk_type env ct (snd (fst a))
                                    = Some ckty).
        { apply assign_clk_type_total_of_vars. intros x Hx.
          apply Hkeys. exact (Hclkc eqs' stf Hrun v a Hva x Hx). }
        destruct Htot as (ckty & Hck).
        exists ckty. split; [exact Hck|].
        intros z Hz. unfold scope. 
        destruct (assign_clk_type_images env ct _ ckty Hck z Hz)
          as [->|(x & Hx & Hxz)].
        + apply in_or_app. right. cbn. auto.
        + apply in_or_app. left.
          apply (sec_of_In_intro env _ x z); [|exact Hxz].
          exact (Hclkc eqs' stf Hrun v a Hva x Hx).
    }
    pose proof HwcnS as HwcnS'.
    destruct HwcnS' as (_ & _ & _ & Hweqs).
    assert (Hnd_n : NoDupMembers (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    { pose proof (n_nodup n) as Hnd. rewrite !app_assoc in Hnd.
      apply NoDupMembers_app_l in Hnd. rewrite <- !app_assoc in Hnd.
      exact Hnd. }
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) scope).
    { unfold scope. eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    (** the delayed equations *)
    assert (Hdat : forall x e0 e ty ck name,
              In ([x], [Efby [e0] [e] [(ty, (ck, name))]]) n.(n_eqs)
              \/ In ([x], [Earrow [e0] [e] [(ty, (ck, name))]]) n.(n_eqs) ->
              exists ckty s0 s1 b,
                find_clock (lnode_clock_env N) x = OK ck
                /\ assign_clk_type env ct ck = Some ckty
                /\ Env.find x env = Some b
                /\ In b scope
                /\ (forall r0, assign_lexp_type accT env ct rt e0 r0
                               = OK ([(s0, [])], r0))
                /\ (forall r0, assign_lexp_type accT env ct rt e r0
                               = OK ([(s1, [])], r0))
                /\ (forall z, In z (merge (merge [rt] ckty) (merge s0 s1)) ->
                              In z scope)).
    { intros x e0 e ty ck name Hin.
      assert (Hineq : exists E,
                (E = Efby [e0] [e] [(ty, (ck, name))]
                 \/ E = Earrow [e0] [e] [(ty, (ck, name))])
                /\ In ([x], [E]) n.(n_eqs)).
      { destruct Hin as [H|H];
          [exists (Efby [e0] [e] [(ty, (ck, name))])
          |exists (Earrow [e0] [e] [(ty, (ck, name))])]; auto. }
      destruct Hineq as (E & HE & HinE).
      pose proof (proj1 (Forall_forall _ _) Hweqs _ HinE) as Hwceq.
      destruct Hwceq as (Hwces & _ & Hxck).
      assert (Hcl : LSyn.clocksof [E] = [ck])
        by (destruct HE as [HE|HE]; subst E; reflexivity).
      rewrite Hcl in Hxck.
      inversion Hxck as [|x0 ck0 xs0 cks0 Hxv Hrest]; subst.
      assert (Hwcsub : wc_exp P vars E)
        by (inversion Hwces; subst; assumption).
      pose proof (proj1 (Forall_forall _ _) HsrcS _ HinE) as Hsxs.
      cbn [snd] in Hsxs.
      assert (Hsxsub : src_exp vars (anon_names n) E)
        by (inversion Hsxs; subst; assumption).
      destruct (delayed_children P vars (anon_names n) E e0 e (ty, (ck, name))
                  HE Hwcsub Hsxsub) as (Hw0 & Hw1 & Hs0 & Hs1).
      assert (Hxin : In x (List.map fst vars)).
      { apply in_map_iff. exists (x, ck). split; [reflexivity|exact Hxv]. }
      assert (Htcm : exists tc, In (x, tc) (n.(n_in) ++ n.(n_vars) ++ n.(n_out))
                                /\ snd tc = ck).
      { unfold vars, idck in Hxv. apply in_map_iff in Hxv as ((x1 & tc) & Heq & Hin1).
        inversion Heq; subst. exists tc. split; [exact Hin1|reflexivity]. }
      destruct Htcm as (tc & Htc & Htcck).
      assert (HfcN : find_clock (lnode_clock_env N) x = OK ck).
      { rewrite (lnode_clock_env_find N x tc); [now rewrite Htcck|].
        rewrite Hfi, Hfv, Hfo.
        apply in_app_or in Htc as [Htc|Htc]; apply in_or_app.
        - now left.
        - right. apply in_app_or in Htc as [Htc|Htc]; apply in_or_app.
          + left. apply in_or_app. now left.
          + now right. }
      assert (Hfcn : find_clock (lnode_clock_env n) x = OK ck)
        by (rewrite (lnode_clock_env_find n x tc Htc); now rewrite Htcck).
      destruct (Hkeys x) as (b & Hb).
      { rewrite <- Hvm. exact Hxin. }
      assert (Htot : exists ckty, assign_clk_type env ct ck = Some ckty).
      { apply assign_clk_type_total_of_vars. intros z Hz.
        apply Hkeys. rewrite <- Hvm.
        exact (Hcenv x ck Hxin Hfcn z Hz). }
      destruct Htot as (ckty & Hckty).
      destruct (delayed_operands_pure accT env ct rt (lnode_clock_env n) Q
                  n.(n_eqs) cs' stS0 stS1 x E e0 e (ty, (ck, name)) HE Hcns'
                  Hunt HinE) as ((s0 & Hp0) & (s1 & Hp1)).
      assert (Hsc0 : forall z, In z s0 -> In z scope).
      { intros z Hz.
        destruct (lexp_scoped_tgt_all_src accT env ct rt P vars (anon_names n)
                    scope Hbs Hrs Hrg HwcgS Hwenv HscT0 e0 (conj Hw0 Hs0)
                    [(s0, [])] stS0 stS0 (Hp0 stS0)) as (Hf0 & _).
        inversion Hf0 as [|? ? Hz0 ?]; subst. cbn [fst] in Hz0.
        pose proof (Hz0 z Hz) as Hzs. rewrite app_nil_r in Hzs.
        exact Hzs. }
      assert (Hsc1 : forall z, In z s1 -> In z scope).
      { intros z Hz.
        destruct (lexp_scoped_tgt_all_src accT env ct rt P vars (anon_names n)
                    scope Hbs Hrs Hrg HwcgS Hwenv HscT0 e (conj Hw1 Hs1)
                    [(s1, [])] stS0 stS0 (Hp1 stS0)) as (Hf1 & _).
        inversion Hf1 as [|? ? Hz1 ?]; subst. cbn [fst] in Hz1.
        pose proof (Hz1 z Hz) as Hzs. rewrite app_nil_r in Hzs.
        exact Hzs. }
      exists ckty, s0, s1, b.
      repeat split; try assumption.
      - exact (Hrg x b Hxin Hb).
      - intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
        + apply in_merge_inv in Hz as [Hz|Hz].
          * destruct Hz as [<-|[]]. exact Hrs.
          * exact (Hclk [] ck ckty [] stS0 stS0 (Forall_nil _)
                     (or_intror (ex_intro _ x (conj Hxin Hfcn)))
                     (fun z0 Hz0 => match Hz0 with end)
                     (assign_lexps_nil_ok accT env ct rt stS0) Hckty z Hz).
        + apply in_merge_inv in Hz as [Hz|Hz]; [exact (Hsc0 z Hz)|exact (Hsc1 z Hz)]. }
    assert (HNI0o : anon_images env n = []).
    { pose proof (anon_names_unnested Q n Hunt) as H00.
      unfold anon_names in H00. apply map_eq_nil in H00.
      unfold anon_images. rewrite H00. reflexivity. }
    (** the raw run, against the target accumulator, is scoped *)
    assert (Htgt : forall ce ct1,
              generate_leqns_constraints accT env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (ce, ct1) -> constraints_scoped scope ce).
    { intros ce ct1 Hg.
      destruct (state_pure_generate_leqns accT env ct rt (lnode_clock_env n) Q
                  n.(n_eqs) Hunt stS0 stS0 ce ct1 Hg) as (Hs_eq & _).
      subst ct1.
      destruct (generate_leqns_constraints_shape (anon_images env n) accT env ct
                  rt (lnode_clock_env n) n.(n_eqs) ce stS0 stS0
                  (anon_images env n ++ minted stS0 stS0)
                  (conj (incl_appr _ (incl_refl _)) (incl_appl _ (incl_refl _)))
                  (proj2 (Forall_forall _ _) (fun eq H => eqs_named_in env n eq H))
                  (fun x b Hx Hf Hin =>
                     match in_app_or _ _ _ Hin with
                     | or_introl H =>
                         defined_not_in_anon_images env n x b Hinj Hx Hf H
                     | or_intror H => Hsep stS0 stS0 HleS0 x b Hf H
                     end)
                  (wl_node_arity P n HwlS) Hg)
        as (ms & Hm & Hms).
      assert (HNI0 : anon_images env n = []).
      { pose proof (anon_names_unnested Q n Hunt) as H00.
        unfold anon_names in H00. apply map_eq_nil in H00.
        unfold anon_images. rewrite H00. reflexivity. }
      assert (Hms0 : ms = []).
      { destruct ms as [|m ms']; [reflexivity|exfalso].
        pose proof (Hms m (or_introl Logic.eq_refl)) as Hmin.
        rewrite HNI0 in Hmin. cbn [app] in Hmin.
        apply minted_spec in Hmin as (k & Hk1 & Hk2 & _).
        exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hk1 Hk2)). }
      subst ms.
      eapply (generate_leqns_constraints_scoped_wc accT env ct rt P vars
                (anon_names n) scope (lnode_clock_env n) n.(n_eqs) ce stS0 stS0
                HscT0 Hclk Hrs);
        [|exact Hweqs|exact HsrcS|exact Hdefd| |exact Hg].
      - eapply exps_scoped_wc_of_decl;
          [exact Hbs|exact Hrs|exact Hrg|exact HwcgS|exact Hwenv|exact HscT0|apply incl_refl].
      - eapply incl_tran; [eapply tgt_names_of_targets_of; exact Hm|].
        apply incl_app; [exact Hdefd|intros z []]. }
    (** and what the source run eliminates is not on the interface *)
    assert (Hdisj' : forall locals0 cns0 ct1,
              get_mappings_from_node n.(n_vars) env = Some locals0 ->
              generate_leqns_constraints accS env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (cns0, ct1) ->
              forall y, In y (locals0 ++ anon_images env n ++ minted stS0 ct1) -> ~ In y scope0).
    { intros locals0 cns0 ct1 Hl0 Hg0 y Hy Hy0.
      rewrite HNI0o in Hy. cbn [app] in Hy.
      apply in_app_or in Hy as [Hy|Hy].
      - unfold scope0 in Hy0. apply in_app_or in Hy0 as [Hy0|Hy0].
        + exact (locals_not_interface env Hinj n locals0 Hnd_n Hl0 y Hy Hy0).
        + apply get_mappings_from_node_eq in Hl0.
          destruct (get_mappings_In _ env locals0 y Hl0 Hy) as (v & Hv & Hfv').
          destruct Hy0 as [<-|[<-|[]]].
          * assert (v = nclk r) as Hvc
              by (eapply Hinj; [exact Hfv'|exact Hct|reflexivity]).
            subst v. apply (proj1 Hnotaux).
            rewrite Hfi, Hfv, Hfo. rewrite !map_app. apply in_or_app. right.
            apply in_or_app. left. apply in_or_app. left.
            apply in_map_iff in Hv as ((v' & tc) & Hvv & Hin). cbn in Hvv.
            subst v'.
            apply in_map_iff. exists (nclk r, tc). split; [reflexivity|exact Hin].
          * assert (v = nrst r) as Hvc
              by (eapply Hinj; [exact Hfv'|exact Hrt|reflexivity]).
            subst v. apply (proj2 Hnotaux).
            rewrite Hfi, Hfv, Hfo. rewrite !map_app. apply in_or_app. right.
            apply in_or_app. left. apply in_or_app. left.
            apply in_map_iff in Hv as ((v' & tc) & Hvv & Hin). cbn in Hvv.
            subst v'.
            apply in_map_iff. exists (nrst r, tc). split; [reflexivity|exact Hin].
      - assert (Hex : exists x, Env.find x env = Some y).
        { unfold scope0 in Hy0. apply in_app_or in Hy0 as [Hy0|Hy0].
          - apply sec_of_In_inv in Hy0 as (x & _ & Hx). exists x. exact Hx.
          - destruct Hy0 as [<-|[<-|[]]]; [exists (nclk r); exact Hct
                                         |exists (nrst r); exact Hrt]. }
        destruct Hex as (x & Hx).
        exact (Hsep stS0 ct1 HleS0 x y Hx Hy). }
    assert (Hincl : forall z, In z (signature_scope sgS) -> In z scope0).
    { intros z Hz. rewrite HsgS in Hz.
      cbn [signature_scope s_in s_out s_clk s_reset] in Hz.
      rewrite Hi, Ho in Hz. unfold scope0. rewrite map_app, sec_of_app.
      apply in_app_or in Hz as [Hz|Hz]; apply in_or_app.
      - left. apply in_or_app. now left.
      - apply in_app_or in Hz as [Hz|Hz].
        + left. apply in_or_app. now right.
        + right. exact Hz. }
    assert (Haux' : forall clk_id rst_id,
              get_node_aux (n_name n) auxF = Some (clk_id, rst_id) ->
              Env.find clk_id env = Some ct /\ Env.find rst_id env = Some rt)
      by (intros ci' ri' H; rewrite Haux0 in H; inversion H; subst;
          split; assumption).
    assert (Hwf : forall ce ct1,
              generate_leqns_constraints accS env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (ce, ct1) ->
              Forall (fun c0 => List.length (snd c0) = 1%nat) ce)
      by (intros ce ct1 Hg;
          exact (generate_leqns_constraints_len1 accS env ct rt
                   (lnode_clock_env n) n.(n_eqs) ce stS0 ct1 Hg)).
    exact (normfby_node_step env ct rt scope scope0 Hsub0 accT
             (lnode_clock_env N) Q c n Hunt Hpref Q envsF auxF st0 accS sgS
             stS0 stS1 sgT stT0 stT1 Hfind Haux' Logic.eq_refl Hunn Hinj Hrs Hstate
             Hdat Htgt Hwf Hdisj' Hgs Hnds Hgt Hsct Hincl Hef Hlf Hlo Hw HsS0
             HsT0).
  Qed.

  (** * Leg U, one node *)

  Lemma sig_nd_scope_nodup :
    forall sg, sig_nd sg -> NoDup (signature_scope sg).
  Proof.
    intros sg H. unfold sig_nd in H. unfold signature_scope.
    eapply Permutation_NoDup; [|exact H].
    apply Permutation_app_head.
    exact (Permutation_app_comm [sg.(s_clk); sg.(s_reset)] sg.(s_out)).
  Qed.

  Section SourceScopedG.

    Variable G       : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable vars    : list (ident * clock).
    Variable AN      : list ident.
    Variable decl    : list ident.
    Variable NI      : list ident.
    Variable scope   : list ident.
    Variable stLo stF : sec_state.

    Hypothesis Hb : In base_ty decl.
    Hypothesis Hr : In rst_ty decl.
    Hypothesis Henv :
      forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                  In b decl.
    Hypothesis Hwenv : wc_env vars.
    Hypothesis HNI :
      forall w b, In w AN -> Env.find w env = Some b -> In b NI.
    Hypothesis Hsgs : secglobal_scoped G.
    Hypothesis Hincl : incl (decl ++ NI) scope.
    Hypothesis Hwin :
      forall s s', (stLo <= s)%positive -> (s' <= stF)%positive ->
                   incl (minted s s') scope.

    (** a source expression names only anonymous streams and declared
        variables, whose security names are in [decl ++ NI] *)
    Lemma named_in_src :
      forall e, src_exp vars AN e -> named_in env (decl ++ NI) e.
    Proof.
      intros e Hsx f es r anns w b Hsub Hw Hb'.
      destruct (Hsx _ Hsub) as (_ & Hn). cbn in Hn.
      destruct (Hn w Hw) as [Hw1|Hw1]; apply in_or_app.
      - right. exact (HNI w b Hw1 Hb').
      - left. exact (Henv w b Hw1 Hb').
    Qed.

    Lemma tgt_in_scope_g :
      forall (cs : list SymTypes.constraint),
        Forall (fun c => incl (snd c) scope) cs ->
        incl (decl ++ tgt_names cs) scope.
    Proof.
      intros cs Hc y Hy. apply in_app_or in Hy as [Hy|Hy];
        [apply Hincl; apply in_or_app; now left|].
      unfold tgt_names in Hy. apply in_flat_map in Hy as (c & Hc1 & Hyc).
      rewrite Forall_forall in Hc. exact (Hc c Hc1 y Hyc).
    Qed.

    Lemma source_types_scoped_upto_g_holds :
      source_types_scoped_upto_g G env base_ty rst_ty vars AN scope stLo stF.
    Proof.
      intros P e ts s s' Hg Hwc Hsx Hlo H Hhi.
      destruct (lexp_scoped_tgt_all_src G env base_ty rst_ty P vars AN decl Hb
                  Hr Henv Hg Hwenv Hsgs e (conj Hwc Hsx) ts s s' H)
        as (Hf & _).
      pose proof (lexp_carried_minted_all (decl ++ NI) G env base_ty rst_ty e
                    ts s s' scope
                    (conj (Hwin s s' Hlo Hhi) Hincl) (named_in_src e Hsx) H)
        as Hm.
      pose proof (tgt_in_scope_g (carried ts) Hm) as Hs.
      eapply Forall_impl; [|exact Hf]. intros t Ht.
      eapply st_scoped_weaken; [exact Hs|exact Ht].
    Qed.

    Lemma source_lexps_pair_g :
      forall P es ts s s',
        wc_global P ->
        Forall (wc_exp P vars) es ->
        Forall (src_exp vars AN) es ->
        (stLo <= s)%positive ->
        assign_lexps G env base_ty rst_ty es s = OK (ts, s') ->
        (s' <= stF)%positive ->
        Forall (fun t => st_scoped scope (fst t)) ts
        /\ constraints_scoped scope (carried ts).
    Proof.
      intros P es ts s s' Hg Hwc Hsx Hlo H Hhi.
      assert (Hall : Forall (lexp_scoped_tgt G env base_ty rst_ty decl) es).
      { rewrite Forall_forall in Hwc, Hsx |- *. intros e He.
        exact (lexp_scoped_tgt_all_src G env base_ty rst_ty P vars AN decl Hb
                 Hr Henv Hg Hwenv Hsgs e (conj (Hwc e He) (Hsx e He))). }
      destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es Hall ts s s'
                  H) as (Hf & Hc).
      assert (Hmin : Forall (lexp_carried_minted (decl ++ NI) G env base_ty
                               rst_ty) es)
        by (apply Forall_forall; intros e0 _;
            apply (lexp_carried_minted_all (decl ++ NI) G env base_ty rst_ty)).
      pose proof (lexps_carried_minted_of (decl ++ NI) G env base_ty rst_ty es
                    Hmin ts s s' scope
                    (conj (Hwin s s' Hlo Hhi) Hincl)
                    (proj2 (Forall_forall _ _)
                       (fun e0 He0 => named_in_src e0 (proj1 (Forall_forall _ _)
                                                          Hsx e0 He0))) H)
        as Hm.
      pose proof (tgt_in_scope_g (carried ts) Hm) as Hs.
      split.
      - eapply Forall_impl; [|exact Hf]. intros t Ht.
        eapply st_scoped_weaken; [exact Hs|exact Ht].
      - eapply constraints_scoped_weaken; [exact Hs|exact Hc].
    Qed.

    Lemma source_lexps_scoped_upto_g_holds :
      source_lexps_scoped_upto_g G env base_ty rst_ty vars AN scope stLo stF.
    Proof.
      intros P es ts s s' Hg Hwc Hsx Hlo H Hhi.
      exact (proj1 (source_lexps_pair_g P es ts s s' Hg Hwc Hsx Hlo H Hhi)).
    Qed.

    Lemma source_lexps_carried_scoped_upto_g_holds :
      source_lexps_carried_scoped_upto_g G env base_ty rst_ty vars AN scope
        stLo stF.
    Proof.
      intros P es ts s s' Hg Hwc Hsx Hlo H Hhi.
      exact (proj2 (source_lexps_pair_g P es ts s s' Hg Hwc Hsx Hlo H Hhi)).
    Qed.

  End SourceScopedG.

  Section AnonDeclared.
  Import UNN.Fresh.

Lemma st_follows_ids : forall (st st' : fresh_st (type * clock)%type),
    st_follows st st' -> incl (st_ids st) (st_ids st').
Proof.
  intros st st' H w Hw. unfold st_ids in *.
  apply in_map_iff in Hw as (p & <- & Hp). apply in_map_iff.
  exists p. split; [reflexivity|]. exact (st_follows_incl _ _ H p Hp).
Qed.

Ltac ib :=
  simpl in *;
  match goal with
  | H : @bind _ _ _ _ _ _ = (_, _) |- _ =>
      apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
  | H : @bind2 _ _ _ _ _ _ _ = (_, _) |- _ =>
      apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
  | H : @ret _ _ _ _ = (_, _) |- _ =>
      rewrite ret_spec in H
  | H : (_, _) = (_, _) |- _ =>
      inversion H; subst; clear H
  end.

Lemma idents_for_anns'_named_ids :
  forall anns ids (st st' : fresh_st (type * clock)%type),
    idents_for_anns' anns st = (ids, st') ->
    forall w, In (Some w) (map LSyn.stream_name anns) -> In w (map fst ids).
Proof.
  induction anns as [|[ty [ck nm]] tl IH]; intros ids st st' H w Hw.
  - destruct Hw.
  - destruct nm as [nm|]; simpl in H; repeat ib.
    + destruct Hw as [Hw|Hw].
      * inversion Hw; subst. left. reflexivity.
      * right. match goal with Hi : idents_for_anns' tl _ = (_, _) |- _ =>
          exact (IH _ _ _ Hi w Hw) end.
    + destruct Hw as [Hw|Hw]; [discriminate Hw|].
      right. match goal with Hi : idents_for_anns' tl _ = (_, _) |- _ =>
          exact (IH _ _ _ Hi w Hw) end.
Qed.

Section MB.
  Context {A A1 A2 : Type}.
  Variable k : A -> Fresh (A1 * A2)%type (type * clock)%type.
  Variable W : A -> ident -> Prop.

  Lemma map_bind2_ids :
    forall l st l1 l2 st',
      map_bind2 k l st = (l1, l2, st') ->
      Forall (fun a => forall a1 a2 s s', k a s = (a1, a2, s') ->
                st_follows s s' /\ forall w, W a w -> In w (st_ids s')) l ->
      forall a, In a l -> forall w, W a w -> In w (st_ids st').
  Proof.
    induction l as [|a0 l IH]; intros st l1 l2 st' H HF a Ha w Hw;
      simpl in H; repeat ib.
    - destruct Ha.
    - inversion HF as [|? ? Hh Ht]; subst.
      destruct Ha as [<-|Ha].
      + destruct (Hh _ _ _ _ H) as (_ & Hid).
        assert (Hf2 : Forall (fun a => forall a1 a2 s s',
                          k a s = (a1, a2, s') -> st_follows s s') l).
        { eapply Forall_impl; [|exact Ht].
          intros a Hq a1 a2 s s' Hk. exact (proj1 (Hq a1 a2 s s' Hk)). }
        pose proof (map_bind2_st_follows k l x2 x3 x1 st' H0 Hf2) as Hfl.
        exact (st_follows_ids _ _ Hfl w (Hid w Hw)).
      + exact (IH _ _ _ _ H0 Ht a Ha w Hw).
  Qed.
End MB.


Lemma fresh_ins_In :
  forall es w, In w (map fst (concat (map fresh_in es))) ->
               exists e, In e es /\ In w (map fst (fresh_in e)).
Proof.
  induction es as [|e es IH]; intros w H; simpl in H.
  - destruct H.
  - rewrite map_app in H. apply in_app_or in H as [H|H].
    + exists e. split; [now left|exact H].
    + destruct (IH _ H) as (e' & He' & Hw). exists e'. split; [now right|exact Hw].
Qed.

Lemma mb_exps_follows :
  forall G b es st l1 l2 (st' : fresh_st (type * clock)%type),
    map_bind2 (unnest_exp G b) es st = (l1, l2, st') -> st_follows st st'.
Proof.
  intros G b es st l1 l2 st' H.
  eapply map_bind2_st_follows; [exact H|].
  apply Forall_forall. intros e _ a1 a2 s s' Hk.
  exact (unnest_exp_st_follows G e b _ s s' Hk).
Qed.

Ltac sf := repeat (reflexivity || (etransitivity;
  [ first [ eapply mb_exps_follows; eassumption
          | eapply idents_for_anns_st_follows; eassumption
          | eapply idents_for_anns'_st_follows; eassumption
          | eapply unnest_noops_exps_st_follows; eassumption
          | eapply unnest_reset_st_follows; eassumption
          | eapply unnest_exp_st_follows; eassumption ] | ])).

Lemma mb_exps_ids :
  forall G b es,
    Forall (fun e => forall bb res (st st' : fresh_st (type * clock)%type),
              unnest_exp G bb e st = (res, st') ->
              forall w, In w (map fst (fresh_in e)) -> In w (st_ids st')) es ->
    forall st l1 l2 (st' : fresh_st (type * clock)%type),
      map_bind2 (unnest_exp G b) es st = (l1, l2, st') ->
      forall w, In w (map fst (concat (map fresh_in es))) ->
                In w (st_ids st').
Proof.
  intros G b es IH st l1 l2 st' H w Hw.
  destruct (fresh_ins_In es w Hw) as (e & He & Hwe).
  refine (map_bind2_ids (unnest_exp G b) (fun e w => In w (map fst (fresh_in e)))
            es st l1 l2 st' H _ e He w Hwe).
  apply Forall_forall. intros e' He' a1 a2 s s' Hk. split.
  - exact (unnest_exp_st_follows G e' b _ s s' Hk).
  - intros w' Hw'.
    exact (proj1 (Forall_forall _ _) IH e' He' b _ s s' Hk w' Hw').
Qed.


Lemma anon_streams_named :
  forall anns w, In w (map fst (LSyn.anon_streams anns)) ->
                 In (Some w) (map LSyn.stream_name anns).
Proof.
  induction anns as [|[ty [ck nm]] tl IH]; intros w H; simpl in H.
  - destruct H.
  - destruct nm as [nm|]; simpl in H.
    + destruct H as [<-|H]; [now left|right; exact (IH _ H)].
    + right. exact (IH _ H).
Qed.

Lemma unnest_reset_ids :
  forall G r (st st' : fresh_st (type * clock)%type) res,
    (forall bb res (st st' : fresh_st (type * clock)%type),
        unnest_exp G bb r st = (res, st') ->
        forall w, In w (map fst (fresh_in r)) -> In w (st_ids st')) ->
    unnest_reset (unnest_exp G true) (Some r) st = (res, st') ->
    forall w, In w (map fst (fresh_in r)) -> In w (st_ids st').
Proof.
  intros G r st st' res IH H w Hw.
  destruct (unnest_exp G true r st) as [[es' eqs'] s1] eqn:Hk.
  pose proof (unnest_reset_spec (unnest_exp G true) r es' eqs' st s1 Hk)
    as [(v & ann & _ & Hr)|(ty & ck & o & x & s2 & _ & Hf & Hr)];
    rewrite Hr in H; inversion H; subst.
  - exact (IH true _ st st' Hk w Hw).
  - refine (st_follows_ids _ _ _ w (IH true _ st s1 Hk w Hw)).
    eapply fresh_ident_st_follows. exact Hf.
Qed.

Lemma unnest_exp_fresh_ids :
  forall G e b res (st st' : fresh_st (type * clock)%type),
    unnest_exp G b e st = (res, st') ->
    forall w, In w (map fst (fresh_in e)) -> In w (st_ids st').
Proof.
  induction e using exp_ind2; intros bb res st st' Hun w Hw.
  - simpl in Hw. destruct Hw.
  - simpl in Hw. destruct Hw.
  - (* unop *)
    simpl in Hun; repeat ib. simpl in Hw.
    match goal with Hr : unnest_exp _ _ _ _ = (_, _, _) |- _ => exact (IHe _ _ _ _ Hr w Hw) end.
  - (* binop *)
    simpl in Hun; repeat ib. simpl in Hw. rewrite map_app in Hw.
    apply in_app_or in Hw as [Hw|Hw].
    + exact (st_follows_ids _ _ (unnest_exp_st_follows G e2 false _ _ _ H0) w (IHe1 _ _ _ _ H w Hw)).
    + exact (IHe2 _ _ _ _ H0 w Hw).
  - (* fby *) simpl in Hun; repeat ib. simpl in Hw. rewrite map_app in Hw.
    apply in_app_or in Hw as [Hw|Hw].
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false e0s H _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false es H0 _ _ _ _ H2 w Hw)). sf.
  - (* arrow *) simpl in Hun; repeat ib. simpl in Hw. rewrite map_app in Hw.
    apply in_app_or in Hw as [Hw|Hw].
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false e0s H _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false es H0 _ _ _ _ H2 w Hw)). sf.
  - (* when *) destruct a. simpl in Hun; repeat ib. simpl in Hw.
    match goal with Hm : map_bind2 _ _ _ = (_, _, _) |- _ =>
      exact (mb_exps_ids G false es H _ _ _ _ Hm w Hw) end.
  - (* merge *) destruct a. destruct bb; simpl in Hun; repeat ib; simpl in Hw;
      repeat rewrite map_app in Hw; apply in_app_or in Hw as [Hw|Hw].
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true ets H _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true efs H0 _ _ _ _ H2 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true ets H _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true efs H0 _ _ _ _ H2 w Hw)). sf.
  - (* ite *) destruct a. destruct bb; simpl in Hun; repeat ib; simpl in Hw;
      repeat rewrite map_app in Hw; apply in_app_or in Hw as [Hw|Hw];
      try (apply in_app_or in Hw as [Hw|Hw]).
    + refine (st_follows_ids _ _ _ w (IHe _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true ets H _ _ _ _ H2 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true efs H0 _ _ _ _ H3 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (IHe _ _ _ _ H1 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true ets H _ _ _ _ H2 w Hw)). sf.
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G true efs H0 _ _ _ _ H3 w Hw)). sf.
  - (* app *) simpl in Hun; repeat ib. simpl in Hw.
    destruct ro as [r|]; repeat rewrite map_app in Hw.
    + apply in_app_or in Hw as [Hw|Hw]; [|apply in_app_or in Hw as [Hw|Hw]].
      * refine (st_follows_ids _ _ _ w (mb_exps_ids G false es H0 _ _ _ _ H1 w Hw)). sf.
      * refine (st_follows_ids _ _ _ w (unnest_reset_ids G r _ _ _ H H3 w Hw)). sf.
      * exact (idents_for_anns'_incl_ids _ _ _ _ H4 w
                 (idents_for_anns'_named_ids _ _ _ _ H4 w (anon_streams_named _ _ Hw))).
    + apply in_app_or in Hw as [Hw|Hw].
      * refine (st_follows_ids _ _ _ w (mb_exps_ids G false es H0 _ _ _ _ H1 w Hw)). sf.
      * exact (idents_for_anns'_incl_ids _ _ _ _ H4 w
                 (idents_for_anns'_named_ids _ _ _ _ H4 w (anon_streams_named _ _ Hw))).
Qed.

Lemma anon_ins_In :
  forall es w, In w (map fst (concat (map anon_in es))) ->
               exists e, In e es /\ In w (map fst (anon_in e)).
Proof.
  induction es as [|e es IH]; intros w H; simpl in H.
  - destruct H.
  - rewrite map_app in H. apply in_app_or in H as [H|H].
    + exists e. split; [now left|exact H].
    + destruct (IH _ H) as (e' & He' & Hw). exists e'. split; [now right|exact Hw].
Qed.

Lemma exps_IH :
  forall G es,
    Forall (fun e => forall bb res (st st' : fresh_st (type * clock)%type),
              unnest_exp G bb e st = (res, st') ->
              forall w, In w (map fst (fresh_in e)) -> In w (st_ids st')) es.
Proof.
  intros G es. apply Forall_forall. intros e _ bb res st st' H w Hw.
  exact (unnest_exp_fresh_ids G e bb res st st' H w Hw).
Qed.

Lemma unnest_rhs_ids :
  forall G e res (st st' : fresh_st (type * clock)%type),
    unnest_rhs G e st = (res, st') ->
    forall w, In w (map fst (anon_in e)) -> In w (st_ids st').
Proof.
  intros G e res st st' H w Hw.
  destruct e; try (solve [exact (unnest_exp_fresh_ids G _ true _ _ _ H w Hw)]).
  - (* fby *) simpl in H; unfold unnest_exps in H; repeat ib. simpl in Hw.
    rewrite map_app in Hw. apply in_app_or in Hw as [Hw|Hw].
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H w Hw)). sf.
    + exact (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H0 w Hw).
  - (* arrow *) simpl in H; unfold unnest_exps in H; repeat ib. simpl in Hw.
    rewrite map_app in Hw. apply in_app_or in Hw as [Hw|Hw].
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H w Hw)). sf.
    + exact (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H0 w Hw).
  - (* app *) simpl in H; unfold unnest_exps in H; repeat ib. simpl in Hw.
    destruct o as [r|].
    + rewrite map_app in Hw. apply in_app_or in Hw as [Hw|Hw].
      * refine (st_follows_ids _ _ _ w (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H w Hw)). sf.
      * refine (unnest_reset_ids G r _ _ _
                  (fun bb res s s' Hr w0 Hw0 => unnest_exp_fresh_ids G r bb res s s' Hr w0 Hw0)
                  H1 w Hw).
    + refine (st_follows_ids _ _ _ w (mb_exps_ids G false _ (exps_IH G _) _ _ _ _ H w Hw)). sf.
Qed.

Lemma mb_rhs_ids :
  forall G es st l1 l2 (st' : fresh_st (type * clock)%type),
    map_bind2 (unnest_rhs G) es st = (l1, l2, st') ->
    forall w, In w (map fst (concat (map anon_in es))) -> In w (st_ids st').
Proof.
  intros G es st l1 l2 st' H w Hw.
  destruct (anon_ins_In es w Hw) as (e & He & Hwe).
  refine (map_bind2_ids (unnest_rhs G) (fun e w => In w (map fst (anon_in e)))
            es st l1 l2 st' H _ e He w Hwe).
  apply Forall_forall. intros e' He' a1 a2 s s' Hk. split.
  - exact (unnest_rhs_st_follows G e' _ s s' Hk).
  - intros w' Hw'. exact (unnest_rhs_ids G e' _ s s' Hk w' Hw').
Qed.

Lemma unnest_equation_ids :
  forall G eq res (st st' : fresh_st (type * clock)%type),
    unnest_equation G eq st = (res, st') ->
    forall w, In w (map fst (anon_in_eq eq)) -> In w (st_ids st').
Proof.
  intros G [xs es] res st st' H w Hw.
  unfold unnest_equation in H; unfold unnest_rhss in H; repeat ib.
  exact (mb_rhs_ids G es _ _ _ _ H w Hw).
Qed.

Section MB1.
  Context {A A1 : Type}.
  Variable k : A -> Fresh A1 (type * clock)%type.
  Variable W : A -> ident -> Prop.

  Lemma map_bind_ids :
    forall l st l1 st',
      map_bind k l st = (l1, st') ->
      Forall (fun a => forall a1 s s', k a s = (a1, s') ->
                st_follows s s' /\ forall w, W a w -> In w (st_ids s')) l ->
      forall a, In a l -> forall w, W a w -> In w (st_ids st').
  Proof.
    induction l as [|a0 l IH]; intros st l1 st' H HF a Ha w Hw;
      simpl in H; repeat ib.
    - destruct Ha.
    - inversion HF as [|? ? Hh Ht]; subst.
      destruct Ha as [<-|Ha].
      + destruct (Hh _ _ _ H) as (_ & Hid).
        assert (Hf2 : Forall (fun a => forall a1 s s',
                          k a s = (a1, s') -> st_follows s s') l).
        { eapply Forall_impl; [|exact Ht].
          intros a Hq a1 s s' Hk. exact (proj1 (Hq a1 s s' Hk)). }
        pose proof (map_bind_st_follows k l _ _ _ H0 Hf2) as Hfl.
        exact (st_follows_ids _ _ Hfl w (Hid w Hw)).
      + exact (IH _ _ _ H0 Ht a Ha w Hw).
  Qed.
End MB1.

Lemma anon_eqs_In :
  forall eqs w, In w (map fst (concat (map anon_in_eq eqs))) ->
                exists eq, In eq eqs /\ In w (map fst (anon_in_eq eq)).
Proof.
  induction eqs as [|e es IH]; intros w H; simpl in H.
  - destruct H.
  - rewrite map_app in H. apply in_app_or in H as [H|H].
    + exists e. split; [now left|exact H].
    + destruct (IH _ H) as (e' & He' & Hw). exists e'. split; [now right|exact Hw].
Qed.

Lemma unnest_equations_ids :
  forall G eqs res (st st' : fresh_st (type * clock)%type),
    unnest_equations G eqs st = (res, st') ->
    forall w, In w (map fst (anon_in_eqs eqs)) -> In w (st_ids st').
Proof.
  intros G eqs res st st' H w Hw.
  unfold unnest_equations in H; repeat ib.
  unfold anon_in_eqs in Hw.
  destruct (anon_eqs_In eqs w Hw) as (eq & Heq & Hwe).
  refine (map_bind_ids (unnest_equation G) (fun e w => In w (map fst (anon_in_eq e)))
            eqs st _ st' H _ eq Heq w Hwe).
  apply Forall_forall. intros e' He' a1 s s' Hk. split.
  - exact (unnest_equation_st_follows G e' _ s s' Hk).
  - intros w' Hw'. exact (unnest_equation_ids G e' _ s s' Hk w' Hw').
Qed.

Lemma anon_names_declared_M :
  forall P (n : node) (Hwl : wl_node P n) (Hpref : n_prefixes n = elab_prefs) w,
    In w (anon_names n) ->
    In w (List.map fst (n_in (unnest_node P n Hwl Hpref)
                        ++ n_vars (unnest_node P n Hwl Hpref)
                        ++ n_out (unnest_node P n Hwl Hpref))).
Proof.
  intros P n Hwl Hpref w Hw.
  assert (Hfv : n_vars (unnest_node P n Hwl Hpref)
                = n.(n_vars)
                  ++ st_anns (snd (unnest_equations P n.(n_eqs) init_st)))
    by exact (proj2 (unnest_node_fields P n Hwl Hpref)).
  destruct (unnest_equations P n.(n_eqs) init_st) as [res st'] eqn:E.
  pose proof (unnest_equations_ids P n.(n_eqs) res init_st st' E w Hw) as Hid.
  unfold st_ids in Hid. cbn [snd] in Hfv. rewrite Hfv.
  rewrite !map_app. apply in_or_app. right. apply in_or_app. left.
  apply in_or_app. right. exact Hid.
Qed.

  (** A source node's anonymous streams are apart from the names the
      unnesting pass mints: those are [gensym norm1 _], and the node's names
      are atoms or [gensym] of its own prefixes. *)
  Lemma anon_stream_not_gensym :
    forall (n : node) w pref k,
      ~ PS.In pref n.(n_prefixes) ->
      InMembers w (anon_in_eqs n.(n_eqs)) -> w <> Ids.gensym pref k.
  Proof.
    intros n w pref k Hp Hin Heq.
    destruct n.(n_good) as [Hgood _].
    rewrite Forall_forall in Hgood.
    assert (Ha : AtomOrGensym n.(n_prefixes) w).
    { apply Hgood. rewrite !map_app. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. right.
      now apply fst_InMembers. }
    destruct Ha as [Hat|Hex].
    - rewrite Heq in Hat. eapply gensym_not_atom; eauto.
    - unfold PS.Exists in Hex.
      destruct Hex as (pre & Hinpre & m & Hm).
      rewrite Heq in Hm. apply gensym_injective in Hm as [Hpre _].
      subst pre. exact (Hp Hinpre).
  Qed.

  Lemma fresh_ident_gensym_n :
    forall pref (b : type * clock) x st st',
      UNN.Fresh.fresh_ident pref b st = (x, st') ->
      exists k, x = Ids.gensym pref k.
  Proof.
    intros pref b x st st' H.
    exact (UNN.Fresh.fresh_ident_gensym pref b x st st' H).
  Qed.

  Lemma idents_for_anns_gensym :
    forall anns xs st st',
      UNN.idents_for_anns anns st = (xs, st') ->
      forall x, In x (List.map fst xs) -> exists k, x = Ids.gensym Ids.norm1 k.
  Proof.
    induction anns as [|[ty [cl nm]] tl IH]; intros xs st st' H x Hx.
    - simpl in H; repeat ib. simpl in Hx. destruct Hx.
    - simpl in H; repeat ib. simpl in Hx. destruct Hx as [<-|Hx].
      + match goal with
        | Hf : UNN.Fresh.fresh_ident _ _ _ = (_, _) |- _ =>
            exact (fresh_ident_gensym_n _ _ _ _ _ Hf)
        end.
      + match goal with
        | Hi : UNN.idents_for_anns tl _ = (_, _) |- _ =>
            exact (IH _ _ _ Hi x Hx)
        end.
  Qed.

  Lemma idents_for_anns'_gensym :
    forall anns xs st st',
      UNN.idents_for_anns' anns st = (xs, st') ->
      forall x a, In (x, a) xs -> LSyn.stream_name a = None ->
                  exists k, x = Ids.gensym Ids.norm1 k.
  Proof.
    induction anns as [|[ty [ck nm]] tl IH]; intros xs st st' H x a Hx Hn.
    - simpl in H; repeat ib. destruct Hx.
    - destruct nm as [nm|]; simpl in H; repeat ib.
      + destruct Hx as [Hx|Hx].
        * inversion Hx; subst. discriminate Hn.
        * match goal with
          | Hi : UNN.idents_for_anns' tl _ = (_, _) |- _ =>
              exact (IH _ _ _ Hi x a Hx Hn)
          end.
      + destruct Hx as [Hx|Hx].
        * inversion Hx; subst.
          match goal with
          | Hf : UNN.Fresh.fresh_ident _ _ _ = (_, _) |- _ =>
              exact (fresh_ident_gensym_n _ _ _ _ _ Hf)
          end.
        * match goal with
          | Hi : UNN.idents_for_anns' tl _ = (_, _) |- _ =>
              exact (IH _ _ _ Hi x a Hx Hn)
          end.
  Qed.

  End AnonDeclared.

  Lemma unnest_instance :
    forall (all : list node) envsF auxF stN
           (P : global) (n : node) (Hwl : wl_node P n)
           (Hpref : n_prefixes n = elab_prefs) (nall : node)
           (env : Env.t ident) (r : node_aux_names) st0 stl
           accS accT sgS stS0 stS1 sgT stT0 stT1,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
      find_node_env n.(n_name) envsF = Some env ->
      get_node_aux n.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
      (st0 <= stN)%positive ->
      lsig_inv stN st0 accS stS0 ->
      lsig_inv stN st0 accT stT0 ->
      call_weakens accS accT ->
      node_typed_facts n nall ->
      node_typed_facts (unnest_node P n Hwl Hpref) nall ->
      incl (n_in (unnest_node P n Hwl Hpref) ++ n_vars (unnest_node P n Hwl Hpref)
            ++ n_out (unnest_node P n Hwl Hpref))
           (n_in nall ++ n_vars nall ++ n_out nall) ->
      NoDupMembers (n_in nall ++ n_vars nall ++ n_out nall) ->
      wc_global P -> wc_node P n ->
      CALLS.sig_inputs_ok accT P ->
      generate_lnode_sig_scoped_env accS n envsF auxF stS0 = OK (sgS, stS1) ->
      generate_lnode_sig_scoped_env accT (unnest_node P n Hwl Hpref)
        envsF auxF stT0 = OK (sgT, stT1) ->
      sig_head_weakens sgS sgT.
  Proof.
    intros all envsF auxF stN P n Hwl Hpref nall env r st0 stl accS accT sgS
      stS0 stS1 sgT stT0 stT1 Hfull Hloc Hfind Haux0 Hst0 HinvS HinvT Hw HfS
      HfM Hext Hndall Hwcg Hwcn Hinputs HsS0 HsT0.
    set (M := unnest_node P n Hwl Hpref) in *.
    destruct HfS as (P1 & HwlS & HwcgS & HwcnS & HsrcS & HdisjS & HsubS).
    destruct HfM as (P2 & HwlM & HwcgM & HwcnM & HsrcM & HdisjM & HsubM).
    assert (HfindM : find_node_env (n_name M) envsF = Some env) by exact Hfind.
    assert (HauxM : get_node_aux (n_name M) auxF = Some (r.(nclk), r.(nrst)))
      by exact Haux0.
    assert (HsS : generate_lnode_sig accS n env auxF stS0 = OK (sgS, stS1)).
    { unfold generate_lnode_sig_scoped_env in HsS0. rewrite Hfind in HsS0.
      exact HsS0. }
    assert (HsT : generate_lnode_sig accT M env auxF stT0 = OK (sgT, stT1)).
    { unfold generate_lnode_sig_scoped_env in HsT0. rewrite HfindM in HsT0.
      exact HsT0. }
    assert (HanS : forall w, In w (anon_names n) ->
                             ~ In w (List.map fst (idck (n.(n_in) ++ n.(n_vars)
                                                         ++ n.(n_out)))))
      by exact HdisjS.
    assert (HinvS' : lsig_inv stN stl (sgS :: accS) stS1)
      by (eapply lsig_step_ext;
          [exact Hfull|exact Hfind|exact Haux0|exact Hloc|exact Hst0|exact HwlS
          |exact HwcgS|exact HwcnS|exact HsrcS|exact HsubS
          |exact HinvS|exact HsS]).
    assert (HinvT' : lsig_inv stN stl (sgT :: accT) stT1)
      by (eapply lsig_step_ext;
          [exact Hfull|exact HfindM|exact HauxM|exact Hloc|exact Hst0|exact HwlM
          |exact HwcgM|exact HwcnM|exact HsrcM|exact HsubM
          |exact HinvT|exact HsT]).
    destruct (lsig_inv_head _ _ _ _ _ HinvS') as (Hgs & Hscs & Hnds).
    destruct (lsig_inv_head _ _ _ _ _ HinvT') as (Hgt & Hsct & Hndt).
    destruct HinvS as (HgoodS0 & HscS0 & HndS0 & HrootS0 & HbdS0 & HleS0).
    destruct HinvT as (HgoodT0 & HscT0 & HndT0 & HrootT0 & HbdT0 & HleT0).
    destruct (generate_local_env_for_lnode_facts nall st0 env r stl Hloc)
      as (Hinj & Hrng & Hclk0 & Hrst0).
    destruct (lnode_sig_inv env accS n auxF sgS stS0 stS1 HsS)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hlocs & Hcns & HsgS).
    assert (Hci : ci = nclk r /\ ri = nrst r)
      by (rewrite Haux0 in Haux; inversion Haux; split; reflexivity).
    destruct Hci as (-> & ->).
    assert (Hi : inp = CALLS.sec_of env (List.map fst n.(n_in)))
      by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (Ho : out = CALLS.sec_of env (List.map fst n.(n_out)))
      by (eapply get_mappings_from_node_sec_of; exact Hout).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt]).
    set (NI := anon_images env n).
    set (scope := decl ++ NI ++ minted stS0 stS1).
    set (scope0 := CALLS.sec_of env (List.map fst (n.(n_in) ++ n.(n_out)))
                   ++ [ct; rt]).
    assert (Hdecl_scope : incl decl scope) by (intros z Hz; unfold scope; apply in_or_app; now left).
    assert (Hsub0 : incl scope0 scope).
    { intros z Hz. unfold scope0 in Hz. unfold scope, decl. apply in_or_app. left.
      apply in_or_app.
      apply in_app_or in Hz as [Hz|Hz].
      - left. revert z Hz. apply sec_of_incl. intros y Hy.
        rewrite !map_app in *.
        apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
          [now left|right; apply in_or_app; now right].
      - right. exact Hz. }
    assert (Hbd : In ct decl) by (unfold decl; apply in_or_app; right; cbn; auto).
    assert (Hrd : In rt decl) by (unfold decl; apply in_or_app; right; cbn; auto).
    assert (Hbs : In ct scope) by exact (Hdecl_scope _ Hbd).
    assert (Hrs : In rt scope) by exact (Hdecl_scope _ Hrd).
    assert (Hsep : forall s s', sec_le stN s ->
                     forall x b, Env.find x env = Some b -> ~ In b (minted s s'))
      by (intros s s' Hle x b Hb;
          exact (env_apart_from_minted all envsF auxF stN (n_name M) env s s'
                   Hfull HfindM Hle x b Hb)).
    set (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    assert (Hvm : List.map fst vars
                  = List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
      by (unfold vars, idck; rewrite map_map; reflexivity).
    assert (Hrg : forall x b, In x (List.map fst vars) ->
                              Env.find x env = Some b -> In b decl).
    { intros x b Hx Hf. rewrite Hvm in Hx. unfold decl.
      apply in_or_app. left. exact (sec_of_In_intro env _ x b Hx Hf). }
    destruct (node_wc_clock_facts P n Hwcn) as (Hwenv & Hcenv).
    assert (HcenvM : forall x ck, In x (List.map fst vars) ->
                       find_clock (lnode_clock_env M) x = OK ck ->
                       incl (clock_vars ck) (List.map fst vars)).
    { intros x ck Hx Hfc. rewrite Hvm in Hx.
      apply in_map_iff in Hx as ((x' & tc) & Hxe & Hin). cbn in Hxe. subst x'.
      assert (HfcM : find_clock (lnode_clock_env M) x = OK (snd tc)).
      { apply (unnest_node_cenv_vars P n Hwl Hpref x (snd tc)).
        unfold idck. apply in_map_iff. exists (x, tc). split;
          [reflexivity|exact Hin]. }
      rewrite HfcM in Hfc. inversion Hfc; subst ck.
      apply (Hcenv x (snd tc)).
      - change (In x (List.map fst vars)). rewrite Hvm.
        apply in_map_iff. exists (x, tc). split; [reflexivity|exact Hin].
      - rewrite (lnode_clock_env_find n x tc Hin). reflexivity. }
    assert (HNI : forall w b, In w (anon_names n) ->
                              Env.find w env = Some b -> In b NI).
    { intros w b Hwn Hb. unfold anon_names in Hwn.
      apply in_map_iff in Hwn as ((w' & a) & Hwe & Hp). cbn [fst] in Hwe.
      subst w'. unfold NI, anon_images. apply in_flat_map.
      exists (w, a). split; [exact Hp|]. cbn [fst]. rewrite Hb. now left. }
    assert (HNIsc : incl NI scope).
    { intros z Hz. unfold scope. apply in_or_app. right. apply in_or_app.
      now left. }
    assert (Hdn_sc : incl (decl ++ NI) scope).
    { apply incl_app; [exact Hdecl_scope|exact HNIsc]. }
    assert (Hnca : ~ In (nclk r) (List.map fst (anon_in_eqs n.(n_eqs)))).
    { intro Hin. exact (anon_stream_not_sec n _ st0 HsubS
                          (proj2 (fst_InMembers _ _) Hin) Hclk0). }
    assert (Hnra : ~ In (nrst r) (List.map fst (anon_in_eqs n.(n_eqs)))).
    { intro Hin. exact (anon_stream_not_sec n _ (Pos.succ st0) HsubS
                          (proj2 (fst_InMembers _ _) Hin) Hrst0). }
    assert (Hrg' : forall x b, In x (List.map fst vars) ->
                               Env.find x env = Some b -> In b scope)
      by (intros x b Hx Hf; exact (Hdecl_scope _ (Hrg x b Hx Hf))).
    assert (HclkN : clk_scoped_wc accT env ct rt P vars (lnode_clock_env n)
                      scope)
      by exact (clk_scoped_wc_holds accT env ct rt (lnode_clock_env n) P vars
                  scope scope Hbs Hrg' Hwenv Hcenv (incl_refl _) Hwcg).
    assert (Hwin : forall s s', (stS0 <= s)%positive -> (s' <= stS1)%positive ->
                     incl (minted s s') scope).
    { intros s s' H1 H2. unfold scope.
      eapply incl_tran; [|apply incl_appr, incl_appr, incl_refl].
      apply minted_window; [exact H1|exact H2]. }
    assert (Hclkg : forall (P0 : global) es ck ckty,
              wc_global P0 -> Forall (wc_exp P0 vars) es ->
              Forall (nested_src vars (anon_names n)) es ->
              (clk_src vars es ck \/
               exists x, In x (List.map fst vars)
                         /\ find_clock (lnode_clock_env M) x = OK ck) ->
              assign_clk_type env ct ck = Some ckty -> st_scoped scope ckty).
    { intros P0 es ck ckty Hg Hw1 Hn1 [Hs1|(x & Hx & Hfc)] Hc1.
      - eapply st_scoped_weaken; [exact Hdn_sc|].
        refine (clk_scoped_named env ct P0 vars decl es ck ckty NI Hg Hwenv
                  Hbd Hrg Hw1 Hs1 _ Hc1).
        intros w b Hwn Hb.
        apply (proj1 (fst_InMembers _ _)) in Hwn.
        apply in_map_iff in Hwn as ((w' & a) & Hwe & Hin). cbn [fst] in Hwe.
        subst w'. unfold fresh_ins in Hin.
        apply in_concat in Hin as (l & Hin & Hl).
        apply in_map_iff in Hl as (e & <- & He).
        rewrite Forall_forall in Hn1.
        exact (HNI w b ((proj2 (Hn1 e He)) w a Hin) Hb).
      - eapply st_scoped_weaken; [exact Hdecl_scope|].
        intros y Hy.
        destruct (assign_clk_type_images env ct ck ckty Hc1 y Hy)
          as [->|(x' & Hx' & Hf)]; [exact Hbd|].
        exact (Hrg x' y (HcenvM x ck Hx Hfc x' Hx') Hf). }
    assert (Hsty : source_types_scoped_upto_g accT env ct rt vars (anon_names n)
                     scope stS0 stS1)
      by exact (source_types_scoped_upto_g_holds accT env ct rt vars
                  (anon_names n) decl NI scope stS0 stS1 Hbd Hrd Hrg Hwenv HNI HscT0
                  Hdn_sc Hwin).
    assert (Hslx : source_lexps_scoped_upto_g accT env ct rt vars
                     (anon_names n) scope stS0 stS1)
      by exact (source_lexps_scoped_upto_g_holds accT env ct rt vars
                  (anon_names n) decl NI scope stS0 stS1 Hbd Hrd Hrg Hwenv HNI HscT0
                  Hdn_sc Hwin).
    assert (Hslc : source_lexps_carried_scoped_upto_g accT env ct rt vars
                     (anon_names n) scope stS0 stS1)
      by exact (source_lexps_carried_scoped_upto_g_holds accT env ct rt vars
                  (anon_names n) decl NI scope stS0 stS1 Hbd Hrd Hrg Hwenv HNI HscT0
                  Hdn_sc Hwin).
    pose proof Hwcn as Hwcn'.
    destruct Hwcn' as (_ & _ & _ & Hweqs).
    assert (Hfv : n_vars M
                  = n.(n_vars)
                    ++ st_anns (snd (unnest_equations P n.(n_eqs) init_st)))
      by exact (proj2 (unnest_node_fields P n Hwl Hpref)).
    assert (Hfi : n_in M = n.(n_in)) by reflexivity.
    assert (Hfo : n_out M = n.(n_out)) by reflexivity.
    assert (Hnd_n : NoDupMembers (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    { pose proof (n_nodup n) as Hnd. rewrite !app_assoc in Hnd.
      apply NoDupMembers_app_l in Hnd. rewrite <- !app_assoc in Hnd.
      exact Hnd. }
    assert (Hnd_M : NoDupMembers (n_in M ++ n_vars M ++ n_out M)).
    { pose proof (n_nodup M) as Hnd. rewrite !app_assoc in Hnd.
      apply NoDupMembers_app_l in Hnd. rewrite <- !app_assoc in Hnd.
      exact Hnd. }
    assert (HinN : forall p, In p (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
                             In p (n_in nall ++ n_vars nall ++ n_out nall)).
    { intros p Hp. apply Hext.
      change (In p (n_in M ++ n_vars M ++ n_out M)).
      rewrite Hfi, Hfv, Hfo.
      apply in_app_or in Hp as [Hp|Hp]; apply in_or_app.
      - now left.
      - right. apply in_app_or in Hp as [Hp|Hp]; apply in_or_app.
        + left. apply in_or_app. now left.
        + now right. }
    assert (Hkeys : forall x, In x (List.map fst (n.(n_in) ++ n.(n_vars)
                                                  ++ n.(n_out))) ->
                              exists b, Env.find x env = Some b).
    { intros x Hx.
      apply (generate_local_env_for_lnode_binds nall st0 env r stl Hloc x).
      right. right.
      apply in_map_iff in Hx as (p & Hpx & Hp).
      apply in_map_iff. exists p. split; [exact Hpx|exact (HinN p Hp)]. }
    assert (Hnotaux_M : ~ In (nclk r) (List.map fst (n_in M ++ n_vars M ++ n_out M))
                        /\ ~ In (nrst r) (List.map fst (n_in M ++ n_vars M
                                                        ++ n_out M))).
    { split; intro Hin.
      - exact (lnode_var_not_sec M _ st0 HsubM Hin Hclk0).
      - exact (lnode_var_not_sec M _ (Pos.succ st0) HsubM Hin Hrst0). }
    assert (Hnotaux_n : ~ In (nclk r) (List.map fst (n.(n_in) ++ n.(n_vars)
                                                     ++ n.(n_out)))
                        /\ ~ In (nrst r) (List.map fst (n.(n_in) ++ n.(n_vars)
                                                        ++ n.(n_out)))).
    { split; intro Hin.
      - exact (lnode_var_not_sec n _ st0 HsubS Hin Hclk0).
      - exact (lnode_var_not_sec n _ (Pos.succ st0) HsubS Hin Hrst0). }
    (** fresh-ness of the call instantiations the source run makes *)
    set (D := env_images env).
    assert (Hdeclall : forall y, In y D -> name_above st0 y).
    { intros y Hy. unfold D, env_images in Hy.
      apply in_map_iff in Hy as ((x & b) & Hxb & Hin). cbn in Hxb. subst b.
      apply Env.elements_complete in Hin.
      destruct (Hrng x y Hin) as (k & Hk & Hlo & _). exists k. split; assumption. }
    assert (HdkA : decl_ok env ct rt D).
    { split; [|split].
      - exact (env_images_spec env _ _ Hct).
      - exact (env_images_spec env _ _ Hrt).
      - exact (fun x b H => env_images_spec env x b H). }
    assert (HclkA : clk_scoped env ct D).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env;
        [exact (env_images_spec env _ _ Hct)
        |exact (fun x b H => env_images_spec env x b H)|exact Hck]. }
    assert (Hef : eapp_fresh_prop accS env ct rt st0)
      by exact (eapp_fresh_prop_holds accS env ct rt D st0 HdkA HclkA HscS0
                  Hdeclall HbdS0).
    assert (Hlf : lcall_fresh_prop accS env ct rt st0)
      by exact (lcall_fresh_prop_holds accS env ct rt D st0 HdkA HclkA HscS0
                  Hdeclall HbdS0 Hinj).
    assert (Hlo : sec_le st0 stS0) by exact (Pos.le_trans _ _ _ Hst0 HleS0).
    assert (Hsaf : forall f sg inp ck rst os cns sa sb,
              find_signature f accT = Some sg ->
              Forall (caller_st env scope) inp ->
              caller_st env scope ck -> caller_st env scope rst ->
              Forall (caller_name env scope) os ->
              generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
              call_subst_fresh sg inp ck rst os).
    { eapply sig_actuals_fresh_holds with (lo := st0).
      - exact HbdT0.
      - intros y Hy. unfold scope, decl in Hy.
        apply in_app_or in Hy as [Hy|Hy].
        + apply in_app_or in Hy as [Hy|Hy].
          * apply (Hdeclall y). unfold D, env_images.
            apply sec_of_In_inv in Hy as (x & _ & Hx).
            exact (env_images_spec env x y Hx).
          * destruct Hy as [<-|[<-|[]]]; apply Hdeclall;
              [exact (env_images_spec env _ _ Hct)
              |exact (env_images_spec env _ _ Hrt)].
        + apply in_app_or in Hy as [HyN|HyM].
          * apply (Hdeclall y). unfold NI, anon_images in HyN.
            apply in_flat_map in HyN as ((w & a) & _ & Hb'). cbn [fst] in Hb'.
            destruct (Env.find w env) as [b0|] eqn:Ew; [|destruct Hb'].
            destruct Hb' as [Hb'|[]]. subst b0.
            unfold D, env_images. exact (env_images_spec env w y Ew).
          * exact (name_above_minted st0 stS0 stS1 y Hlo HyM).
      - intros x b Hx. apply Hdeclall. exact (env_images_spec env x b Hx). }
    destruct (generate_leqns_constraints_weaken accS accT env ct rt
                (lnode_clock_env n) n.(n_eqs) cns stS0 stS1 st0 Hw Hef Hlf
                (NoDup_vars_defined_n_eqs n) Hlo Hcns)
      as (cs' & Hcns' & _).
    pose proof (unnest_node_unnested_node P n Hwl Hpref) as Hunn.
    (** what unnesting moved is not on the interface *)
    assert (Hmv : forall y,
              In y (moved_by env (anon_names n) init_st
                      (snd (unnest_equations P n.(n_eqs) init_st))) ->
              ~ In y scope).
    { intros y Hy Hys.
      destruct (moved_by_In_inv env (anon_names n) init_st
                  (snd (unnest_equations P n.(n_eqs) init_st)) y Hy)
        as (x & Hx & Hxan & Hxy).
      apply new_ids_spec in Hx as (Hx1 & _).
      assert (HxC : InMembers x
                      (st_anns (snd (unnest_equations P n.(n_eqs) init_st)))).
      { apply fst_InMembers. exact Hx1. }
      unfold scope, decl in Hys. apply in_app_or in Hys as [Hys|Hys].
      - apply in_app_or in Hys as [Hys|Hys].
        + apply sec_of_In_inv in Hys as (x' & Hx' & Hx'y).
          assert (x' = x) as Hxx
            by (eapply Hinj; [exact Hx'y|exact Hxy|reflexivity]).
          subst x'.
          pose proof Hnd_M as Hnd2. rewrite Hfi, Hfv, Hfo in Hnd2.
          destruct (created_disj (n_in n) (n_vars n) _ (n_out n) x Hnd2 HxC)
            as (H1 & H2 & H3).
          rewrite !map_app in Hx'.
          apply in_app_or in Hx' as [Hx'|Hx']; [exact (H1 Hx')|].
          apply in_app_or in Hx' as [Hx'|Hx']; [exact (H2 Hx')|exact (H3 Hx')].
        + destruct Hys as [<-|[<-|[]]].
          * assert (x = nclk r) as Hxc
              by (eapply Hinj; [exact Hxy|exact Hct|reflexivity]).
            subst x. apply (proj1 Hnotaux_M).
            rewrite Hfi, Hfv, Hfo. rewrite !map_app. apply in_or_app. right.
            apply in_or_app. left. apply in_or_app. right.
            apply fst_InMembers. exact HxC.
          * assert (x = nrst r) as Hxc
              by (eapply Hinj; [exact Hxy|exact Hrt|reflexivity]).
            subst x. apply (proj2 Hnotaux_M).
            rewrite Hfi, Hfv, Hfo. rewrite !map_app. apply in_or_app. right.
            apply in_or_app. left. apply in_or_app. right.
            apply fst_InMembers. exact HxC.
      - apply in_app_or in Hys as [HysN|HysM].
        + unfold NI, anon_images in HysN.
          apply in_flat_map in HysN as ((w & a) & Hp & Hb'). cbn [fst] in Hb'.
          destruct (Env.find w env) as [b0|] eqn:Ew; [|destruct Hb'].
          destruct Hb' as [Hb'|[]]. subst b0.
          assert (x = w) as ->
            by (eapply Hinj; [exact Hxy|exact Ew|reflexivity]).
          apply Hxan. unfold anon_names. apply in_map_iff.
          exists (w, a). split; [reflexivity|exact Hp].
        + exact (Hsep stS0 stS1 HleS0 x y Hxy HysM). }
    (** the ambients *)
    assert (Hag : forall x ck, In (x, ck) vars ->
                    find_clock (lnode_clock_env M) x = OK ck)
      by (intros x ck Hxc;
          exact (unnest_node_cenv_vars P n Hwl Hpref x ck Hxc)).
    assert (Hamb1 : forall eq, In eq n.(n_eqs) ->
              clocks_covered env ct rt (clocksof (snd eq))
                (canonical_ambients_g vars env ct rt (lnode_clock_env M) eq)
              /\ List.length (canonical_ambients_g vars env ct rt
                                (lnode_clock_env M) eq)
                 = List.length (fst eq)).
    { intros eq Heq. pose proof (proj1 (Forall_forall _ _) Hweqs _ Heq) as Hwceq.
      destruct eq as (xs & es). destruct Hwceq as (_ & _ & Hxck).
      cbn [fst snd] in *. split.
      - refine (canonical_ambients_g_cover vars env ct rt
                  (lnode_clock_env M) (xs, es) Hag _ Hxck).
        intros ck Hck.
        destruct (Forall2_in_right (fun x ck' => In (x, ck') vars) xs
                    (clocksof es) ck Hxck Hck) as (x & _ & Hxv).
        apply assign_clk_type_total_of_vars. intros z Hz.
        apply Hkeys. rewrite <- Hvm.
        apply (HcenvM x ck); [|exact (Hag x ck Hxv)|exact Hz].
        apply in_map_iff. exists (x, ck). split; [reflexivity|exact Hxv].
      - apply canonical_ambients_g_length. }
    assert (Hamb2 : forall eq, In eq n.(n_eqs) ->
              eqn_ambients env ct rt (lnode_clock_env M) (fst eq)
                (canonical_ambients_g vars env ct rt (lnode_clock_env M) eq)).
    { intros eq Heq. destruct eq as (xs & es).
      apply canonical_ambients_g_spec.
      exact (wc_equation_lhs_vars P vars xs es
               (proj1 (Forall_forall _ _) Hweqs _ Heq)). }
    assert (Hassc : forall eq, stream_ambients_scoped scope
              (canonical_ambients_g vars env ct rt (lnode_clock_env M) eq)).
    { intros eq. apply canonical_ambients_g_scoped; [exact Hrs|].
      intros x ck ckty Hx Hfc Hc.
      exact (Hclkg P [] ck ckty Hwcg (Forall_nil _) (Forall_nil _)
               (or_intror (ex_intro _ x (conj Hx Hfc))) Hc). }
    assert (Hdefd : incl (CALLS.sec_of env (vars_defined n.(n_eqs))) scope).
    { eapply incl_tran; [|exact Hdecl_scope]. unfold decl.
      eapply incl_tran; [|apply incl_appl, incl_refl].
      apply sec_of_incl. intros y Hy.
      assert (In y (List.map fst (n.(n_vars) ++ n.(n_out)))) as Hy'
          by (eapply Permutation_in; [exact (n_defd n)|exact Hy]).
      rewrite map_app in Hy' |- *. rewrite map_app.
      apply in_app_or in Hy' as [Hy'|Hy'];
        [apply in_or_app; right; apply in_or_app; now left
        |apply in_or_app; right; apply in_or_app; now right]. }
    assert (Htgtok : forall ce ct1,
              generate_leqns_constraints accT env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (ce, ct1) ->
              constraints_scoped scope ce /\ sec_le ct1 stS1).
    { intros ce ct1 Hg.
      assert (Hcc : ce = cs' /\ ct1 = stS1)
        by (rewrite Hcns' in Hg; inversion Hg; split; reflexivity).
      destruct Hcc as (-> & ->).
      split; [|apply Pos.le_refl].
      destruct (generate_leqns_constraints_shape NI accT env ct rt
                  (lnode_clock_env n) n.(n_eqs) cs' stS0 stS1
                  (NI ++ minted stS0 stS1)
                  (conj (incl_appr _ (incl_refl _)) (incl_appl _ (incl_refl _)))
                  (proj2 (Forall_forall _ _) (fun eq H => eqs_named_in env n eq H))
                  (fun x b Hx Hf Hin =>
                     match in_app_or _ _ _ Hin with
                     | or_introl H =>
                         defined_not_in_anon_images env n x b Hinj Hx Hf H
                     | or_intror H => Hsep stS0 stS1 HleS0 x b Hf H
                     end)
                  (wl_node_arity P n Hwl) Hcns') as (ms & Hm & Hms).
      refine (generate_leqns_constraints_scoped_wc accT env ct rt P vars
                (anon_names n) scope (lnode_clock_env n) n.(n_eqs) cs' stS0 stS1
                HscT0 _ Hrs _ Hweqs HsrcS Hdefd _ Hcns').
      - exact HclkN.
      - eapply exps_scoped_wc_of_decl;
          [exact Hbd|exact Hrd|exact Hrg|exact Hwcg|exact Hwenv|exact HscT0
          |exact Hdecl_scope].
      - eapply incl_tran; [eapply tgt_names_of_targets_of; exact Hm|].
        apply incl_app; [exact Hdefd|].
        eapply incl_tran; [exact Hms|].
        unfold scope. apply incl_appr, incl_refl. }
    assert (Hdisj' : forall locals0 cns0 ct1,
              get_mappings_from_node n.(n_vars) env = Some locals0 ->
              generate_leqns_constraints accS env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (cns0, ct1) ->
              forall y, In y (locals0 ++ anon_images env n ++ minted stS0 ct1) ->
                        ~ In y scope0).
    { intros locals0 cns0 ct1 Hl0 Hg0 y Hy Hy0.
      apply in_app_or in Hy as [Hy|Hy].
      - unfold scope0 in Hy0. apply in_app_or in Hy0 as [Hy0|Hy0].
        + exact (locals_not_interface env Hinj n locals0 Hnd_n Hl0 y Hy Hy0).
        + apply get_mappings_from_node_eq in Hl0.
          destruct (get_mappings_In _ env locals0 y Hl0 Hy) as (v & Hv & Hfv').
          destruct Hy0 as [<-|[<-|[]]].
          * assert (v = nclk r) as Hvc
              by (eapply Hinj; [exact Hfv'|exact Hct|reflexivity]).
            subst v. apply (proj1 Hnotaux_n).
            rewrite !map_app. apply in_or_app. right. apply in_or_app. left.
            exact Hv.
          * assert (v = nrst r) as Hvc
              by (eapply Hinj; [exact Hfv'|exact Hrt|reflexivity]).
            subst v. apply (proj2 Hnotaux_n).
            rewrite !map_app. apply in_or_app. right. apply in_or_app. left.
            exact Hv.
      - apply in_app_or in Hy as [HyN|Hy].
        + unfold scope0 in Hy0. apply in_app_or in Hy0 as [Hy0|Hy0].
          * refine (anon_images_not_declared env n y Hinj HyN _).
            eapply sec_of_incl; [|exact Hy0].
            intros q Hq. apply in_map_iff in Hq as (p & <- & Hp).
            apply in_map_iff. exists p. split; [reflexivity|].
            apply in_app_or in Hp as [Hp|Hp]; apply in_or_app;
              [now left|right; apply in_or_app; now right].
          * destruct Hy0 as [<-|[<-|[]]];
              [exact (anon_images_apart env n (nclk r) _ Hinj Hct Hnca HyN)
              |exact (anon_images_apart env n (nrst r) _ Hinj Hrt Hnra HyN)].
        + assert (Hex : exists x, Env.find x env = Some y).
        { unfold scope0 in Hy0. apply in_app_or in Hy0 as [Hy0|Hy0].
          - apply sec_of_In_inv in Hy0 as (x & _ & Hx). exists x. exact Hx.
          - destruct Hy0 as [<-|[<-|[]]]; [exists (nclk r); exact Hct
                                         |exists (nrst r); exact Hrt]. }
        destruct Hex as (x & Hx).
        exact (Hsep stS0 ct1 HleS0 x y Hx Hy). }
    assert (Hincl : forall z, In z (signature_scope sgS) -> In z scope0).
    { intros z Hz. rewrite HsgS in Hz.
      cbn [signature_scope s_in s_out s_clk s_reset] in Hz.
      rewrite Hi, Ho in Hz. unfold scope0. rewrite map_app, sec_of_app.
      apply in_app_or in Hz as [Hz|Hz]; apply in_or_app.
      - left. apply in_or_app. now left.
      - apply in_app_or in Hz as [Hz|Hz].
        + left. apply in_or_app. now right.
        + right. exact Hz. }
    assert (Haux' : forall clk_id rst_id,
              get_node_aux (n_name n) auxF = Some (clk_id, rst_id) ->
              Env.find clk_id env = Some ct /\ Env.find rst_id env = Some rt)
      by (intros ci' ri' H; rewrite Haux0 in H; inversion H; subst;
          split; assumption).
    assert (Hwf : forall ce ct1,
              generate_leqns_constraints accS env ct rt (lnode_clock_env n)
                n.(n_eqs) stS0 = OK (ce, ct1) ->
              Forall (fun c0 => List.length (snd c0) = 1%nat) ce)
      by (intros ce ct1 Hg;
          exact (generate_leqns_constraints_len1 accS env ct rt
                   (lnode_clock_env n) n.(n_eqs) ce stS0 ct1 Hg)).
    assert (Henvtot : forall x ck, In (x, ck) vars ->
                       exists b, Env.find x env = Some b).
    { intros x ck Hxc. apply Hkeys. rewrite <- Hvm.
      apply in_map_iff. exists (x, ck). split; [reflexivity|exact Hxc]. }
    assert (Hef1 : eapp_fresh_prop accS env ct rt stS0).
    { intros f es er anns s0 sg argts rstty ckty outs cs sta stb stc s' Hle1.
      eapply Hef. exact (Pos.le_trans _ _ _ Hlo Hle1). }
    assert (Hlf1 : lcall_fresh_prop accS env ct rt stS0).
    { intros xs f es rstty s0 sg ckty argts outs sti cs0 s' Hnd1 Hsh Hle1.
      eapply Hlf; [exact Hnd1| |exact (Pos.le_trans _ _ _ Hlo Hle1)].
      destruct Hsh as [Hsh|(e1 & t1 & a1 & rck & s1 & s1' & Hl1 & Hr)];
        [left; exact Hsh|right].
      exists e1, t1, a1, rck, s1, s1'. split;
        [exact (Pos.le_trans _ _ _ Hlo Hl1)|exact Hr]. }
    assert (HAN_anns : forall anns xs st st',
               UNN.idents_for_anns anns st = (xs, st') ->
               forall x, In x (List.map fst xs) -> ~ In x (anon_names n)).
    { intros anns xs st st' Hi' x Hx Hxan.
      destruct (idents_for_anns_gensym anns xs st st' Hi' x Hx) as (k & Hk).
      unfold anon_names in Hxan.
      refine (anon_stream_not_gensym n x Ids.norm1 k _
                (proj2 (fst_InMembers _ _) Hxan) Hk).
      rewrite Hpref. exact UNN.norm1_not_in_elab_prefs. }
    assert (HAN_fresh : forall (b : type * clock) x st st',
               UNN.Fresh.fresh_ident Ids.norm1 b st = (x, st') ->
               ~ In x (anon_names n)).
    { intros b x st st' Hf Hxan.
      destruct (fresh_ident_gensym_n _ _ _ _ _ Hf) as (k & Hk).
      unfold anon_names in Hxan.
      refine (anon_stream_not_gensym n x Ids.norm1 k _
                (proj2 (fst_InMembers _ _) Hxan) Hk).
      rewrite Hpref. exact UNN.norm1_not_in_elab_prefs. }
    assert (HAN_anns' : forall anns xs st st',
               UNN.idents_for_anns' anns st = (xs, st') ->
               forall x a, In (x, a) xs -> LSyn.stream_name a = None ->
                           ~ In x (anon_names n)).
    { intros anns xs st st' Hi' x a Hx Hn Hxan.
      destruct (idents_for_anns'_gensym anns xs st st' Hi' x a Hx Hn)
        as (k & Hk).
      unfold anon_names in Hxan.
      refine (anon_stream_not_gensym n x Ids.norm1 k _
                (proj2 (fst_InMembers _ _) Hxan) Hk).
      rewrite Hpref. exact UNN.norm1_not_in_elab_prefs. }
    assert (Hank : forall w, In w (anon_names n) ->
                             exists b, Env.find w env = Some b).
    { intros w Hwn.
      pose proof (anon_names_declared_M P n Hwl Hpref w Hwn) as Hwd.
      apply (generate_local_env_for_lnode_binds nall st0 env r stl Hloc w).
      right. right.
      apply in_map_iff in Hwd as (p & Hpw & Hp). apply in_map_iff.
      exists p. split; [exact Hpw|]. apply Hext. exact Hp. }
    exact (unnest_node_step_streams accT env ct rt vars (lnode_clock_env M)
             scope scope0 Hsub0 stS0 stS1 (anon_names n)
             HAN_anns HAN_fresh HAN_anns' Hinj HgoodT0
             (fun f sg H => sig_nd_scope_nodup sg (HndT0 f sg H))
             Hsty Hslx Hrs Hclkg
             Hrg' Hslc HscT0 Hsaf
             Henvtot Hwenv Hank (fun f sg H => HrootT0 f sg H)
             (canonical_ambients_g vars env ct rt (lnode_clock_env M)) Hassc
             P P n Hwl Hpref envsF auxF accS sgS stS0 stS1 sgT stT0 stT1
             Hwcg Hinputs Hfind Haux' Logic.eq_refl Hunn Hwl Hweqs HsrcS Hmv
             Hamb1 Hamb2 (Pos.le_refl stS0) Htgtok Hwf Hdisj' Hgs Hnds Hgt Hsct Hincl Hef1 Hlf1
             Hw HsS0 HsT0).
  Qed.


  (** * The program level

      Source expressions of the pass outputs, and the prefix facts the node
      hypotheses ask for. *)

  Lemma imm_sub_normalized_lexp :
    forall e e1, normalized_lexp e -> imm_sub e1 e -> normalized_lexp e1.
  Proof.
    intros e e1 H Himm. inversion H; subst; inversion Himm; subst;
      first [assumption
            |(match goal with
              | Hin : In _ [_] |- _ =>
                destruct Hin as [<-|[]]; assumption
              end)].
  Qed.

  Lemma sub_exp_normalized_lexp :
    forall e' e, sub_exp e' e -> normalized_lexp e -> normalized_lexp e'.
  Proof.
    intros e' e Hs. induction Hs as [e|e'' e' e Himm Hs IH]; intro H;
      [exact H|].
    exact (IH (imm_sub_normalized_lexp _ _ H Himm)).
  Qed.

  Lemma sub_exp_inv :
    forall e' e, sub_exp e' e ->
                 e' = e \/ exists e1, imm_sub e1 e /\ sub_exp e' e1.
  Proof.
    intros e' e H. inversion H; subst; [left; reflexivity|right; eauto].
  Qed.

  Lemma src_exp_lexp :
    forall vars e, normalized_lexp e -> src_exp vars [] e.
  Proof.
    intros vars e H e' Hs.
    pose proof (sub_exp_normalized_lexp _ _ Hs H) as H'.
    split.
    - intros w a Hin. rewrite (normalized_lexp_anon_in _ H') in Hin.
      destruct Hin.
    - destruct H'; exact I.
  Qed.

  Lemma normalized_constant_lexp :
    forall e, normalized_constant e -> normalized_lexp e.
  Proof.
    intros e H. induction H; constructor; assumption.
  Qed.

  Lemma imm_sub_normalized_cexp :
    forall e e1, normalized_cexp e -> imm_sub e1 e -> normalized_cexp e1.
  Proof.
    intros e e1 H Himm. inversion H; subst.
    - inversion Himm; subst;
        match goal with
        | Hin : In _ [_] |- _ => destruct Hin as [<-|[]]; assumption
        end.
    - inversion Himm; subst;
        first [(apply normalized_lexp_cexp; assumption)
              |(match goal with
                | Hin : In _ [_] |- _ => destruct Hin as [<-|[]]; assumption
                end)].
    - apply normalized_lexp_cexp. exact (imm_sub_normalized_lexp _ _ H0 Himm).
  Qed.

  Lemma sub_exp_normalized_cexp :
    forall e' e, sub_exp e' e -> normalized_cexp e -> normalized_cexp e'.
  Proof.
    intros e' e Hs. induction Hs as [e|e'' e' e Himm Hs IH]; intro H;
      [exact H|].
    exact (IH (imm_sub_normalized_cexp _ _ H Himm)).
  Qed.

  Lemma named_ok_normalized_lexp :
    forall (vars : list (ident * clock)) e, normalized_lexp e -> named_ok vars e.
  Proof.
    intros vars e H f es r anns w Hs _.
    pose proof (sub_exp_normalized_lexp _ _ Hs H) as H'. inversion H'.
  Qed.

  Lemma named_ok_normalized_cexp :
    forall (vars : list (ident * clock)) e, normalized_cexp e -> named_ok vars e.
  Proof.
    intros vars e H f es r anns w Hs _.
    pose proof (sub_exp_normalized_cexp _ _ Hs H) as H'.
    inversion H'; subst;
      match goal with Hl : normalized_lexp _ |- _ => inversion Hl end.
  Qed.

  Lemma src_exp_cexp :
    forall vars e, normalized_cexp e -> src_exp vars [] e.
  Proof.
    intros vars e H e' Hs.
    pose proof (sub_exp_normalized_cexp _ _ Hs H) as H'.
    split.
    - intros w a Hin. rewrite (normalized_cexp_anon_in _ H') in Hin.
      destruct Hin.
    - destruct H' as [x et ef ty cl|e0 et ef ty cl|e0 Hl]; try exact I.
      destruct Hl; exact I.
  Qed.

  Lemma src_exp_Eapp :
    forall vars f es ro anns,
      Forall normalized_lexp es ->
      (match ro with None => True | Some r => normalized_lexp r end) ->
      (forall w, In (Some w) (List.map stream_name anns) ->
                 In w (List.map fst vars)) ->
      src_exp vars [] (Eapp f es ro anns).
  Proof.
    intros vars f es ro anns Hn Hr Hnames e' Hs.
    apply sub_exp_inv in Hs as [->|(e1 & Himm & Hs1)].
    - split.
      + intros w a Hin. exfalso. destruct ro as [r|]; cbn [anon_in] in Hin.
        * unfold fresh_ins in Hin.
          rewrite (normalized_lexps_fresh_ins _ Hn),
            (normalized_lexp_fresh_in _ Hr) in Hin. destruct Hin.
        * unfold fresh_ins in Hin.
          rewrite (normalized_lexps_fresh_ins _ Hn) in Hin. destruct Hin.
      + intros w Hw. right. exact (Hnames w Hw).
    - inversion Himm; subst.
      + match goal with
        | Hin : In _ es |- _ =>
          exact (src_exp_lexp vars _
                   (proj1 (Forall_forall _ _) Hn _ Hin) _ Hs1)
        end.
      + exact (src_exp_lexp vars _ Hr _ Hs1).
  Qed.

  Lemma src_exp_Efby :
    forall vars e0 e ann,
      normalized_lexp e0 -> normalized_lexp e ->
      src_exp vars [] (Efby [e0] [e] [ann]).
  Proof.
    intros vars e0 e ann H0 H1 e' Hs.
    apply sub_exp_inv in Hs as [->|(e1 & Himm & Hs1)].
    - split.
      + intros w a Hin. cbn [anon_in fresh_in List.map concat] in Hin.
        rewrite !app_nil_r, (normalized_lexp_fresh_in _ H0),
          (normalized_lexp_fresh_in _ H1) in Hin. destruct Hin.
      + exact I.
    - inversion Himm; subst;
        match goal with
        | Hin : In _ [_] |- _ =>
          destruct Hin as [<-|[]];
          first [exact (src_exp_lexp vars _ H0 _ Hs1)
                |exact (src_exp_lexp vars _ H1 _ Hs1)]
        end.
  Qed.

  Lemma src_exp_Earrow :
    forall vars e0 e ann,
      normalized_lexp e0 -> normalized_lexp e ->
      src_exp vars [] (Earrow [e0] [e] [ann]).
  Proof.
    intros vars e0 e ann H0 H1 e' Hs.
    apply sub_exp_inv in Hs as [->|(e1 & Himm & Hs1)].
    - split.
      + intros w a Hin. cbn [anon_in fresh_in List.map concat] in Hin.
        rewrite !app_nil_r, (normalized_lexp_fresh_in _ H0),
          (normalized_lexp_fresh_in _ H1) in Hin. destruct Hin.
      + exact I.
    - inversion Himm; subst;
        match goal with
        | Hin : In _ [_] |- _ =>
          destruct Hin as [<-|[]];
          first [exact (src_exp_lexp vars _ H0 _ Hs1)
                |exact (src_exp_lexp vars _ H1 _ Hs1)]
        end.
  Qed.

  Lemma wc_call_names :
    forall (vars : list (ident * clock)) (xs : list ident) f es ro
           (anns : list LSyn.ann),
      Forall2 (fun x nc => LiftO True (Logic.eq x) (snd nc)) xs
        (nclocksof [Eapp f es ro anns]) ->
      Forall2 (fun x ck => In (x, ck) vars) xs
        (clocksof [Eapp f es ro anns]) ->
      forall w, In (Some w) (List.map stream_name anns) ->
                In w (List.map fst vars).
  Proof.
    intros vars xs f es ro anns Heq Hvs w Hw.
    apply in_map_iff in Hw as (ann & Hann & Hin).
    assert (In (snd ann) (nclocksof [Eapp f es ro anns])) as Hnc.
    { simpl. rewrite app_nil_r. apply in_map_iff. exists ann.
      split; [reflexivity|exact Hin]. }
    destruct (Forall2_in_right _ xs (nclocksof [Eapp f es ro anns]) (snd ann)
                Heq Hnc) as (x & Hx & Hxe).
    unfold stream_name in Hann. simpl in Hxe. rewrite Hann in Hxe.
    simpl in Hxe. subst x.
    assert (Hlen : List.length xs = List.length (clocksof [Eapp f es ro anns]))
      by exact (Forall2_length _ _ _ Hvs).
    destruct (Forall2_in_left _ _ _ w Hvs Hx) as (ck & _ & Hv).
    apply in_map_iff. exists (w, ck). split; [reflexivity|exact Hv].
  Qed.

  Lemma wc_args_clocks :
    forall Q vars es,
      wc_global Q -> wc_env vars ->
      Forall (wc_exp Q vars) es ->
      Forall normalized_lexp es ->
      Forall (fun e' => Forall (wc_clock vars) (clockof e')) es.
  Proof.
    intros Q vars es Hg Hwe Hw Hn.
    rewrite Forall_forall in Hw, Hn |- *. intros e He.
    pose proof (wc_exp_clockof Q vars e Hg Hwe (Hw e He)) as Hc.
    rewrite (normalized_lexp_fresh_in _ (Hn e He)) in Hc.
    cbn [idck List.map] in Hc. rewrite app_nil_r in Hc. exact Hc.
  Qed.

  Lemma wc_reset_inv :
    forall Q vars f es r anns,
      wc_exp Q vars (Eapp f es (Some r) anns) -> wc_exp Q vars r.
  Proof. intros Q vars f es r anns H. inversion H; assumption. Qed.

  Lemma wc_reset_clocks :
    forall Q vars r,
      wc_global Q -> wc_env vars -> wc_exp Q vars r -> normalized_lexp r ->
      Forall (wc_clock vars) (clockof r).
  Proof.
    intros Q vars r Hg Hwe Hw Hn.
    pose proof (wc_exp_clockof Q vars r Hg Hwe Hw) as Hc.
    rewrite (normalized_lexp_fresh_in _ Hn) in Hc.
    cbn [idck List.map] in Hc. rewrite app_nil_r in Hc. exact Hc.
  Qed.

  Lemma unnested_node_src :
    forall Q (X : node),
      wc_global Q -> wc_node Q X -> unnested_node Q X ->
      Forall (fun eq =>
                Forall (src_exp (idck (X.(n_in) ++ X.(n_vars) ++ X.(n_out)))
                          []) (snd eq)) X.(n_eqs).
  Proof.
    intros Q X Hg Hwcn Hun.
    destruct (node_wc_clock_facts Q X Hwcn) as (Hwenv & _).
    destruct Hwcn as (_ & _ & _ & Hweqs).
    unfold unnested_node in Hun.
    rewrite Forall_forall in Hun, Hweqs |- *. intros eq Hin.
    pose proof (Hun eq Hin) as Hu. pose proof (Hweqs eq Hin) as Hw.
    destruct eq as [xs es]. cbn in Hw.
    destruct Hw as (Hwe & Hweq & Hwv).
    inversion Hu as [xs0 f0 n0 es0 lann0 Hn Hf Hk
                    | xs0 f0 n0 es0 x0 ty0 cl0 lann0 Hn Hf Hk
                    | x0 e0 e1 ann0 H0 H1 | x0 e0 e1 ann0 H0 H1 | x0 e0 Hc];
      subst; cbn [snd]; (apply Forall_cons; [|apply Forall_nil]).
    - apply src_exp_Eapp; [exact Hn|exact I| exact (wc_call_names _ _ _ _ _ _ Hweq Hwv)].
    - apply src_exp_Eapp; [exact Hn|constructor| exact (wc_call_names _ _ _ _ _ _ Hweq Hwv)].
    - exact (src_exp_Efby _ _ _ _ H0 H1).
    - exact (src_exp_Earrow _ _ _ _ H0 H1).
    - exact (src_exp_cexp _ _ Hc).
  Qed.

  Lemma normalized_node_src :
    forall Q (X : node),
      wc_global Q -> wc_node Q X -> normalized_node Q X ->
      Forall (fun eq =>
                Forall (src_exp (idck (X.(n_in) ++ X.(n_vars) ++ X.(n_out)))
                          []) (snd eq)) X.(n_eqs).
  Proof.
    intros Q X Hg Hwcn Hun.
    destruct (node_wc_clock_facts Q X Hwcn) as (Hwenv & _).
    destruct Hwcn as (_ & _ & _ & Hweqs).
    unfold normalized_node in Hun.
    rewrite Forall_forall in Hun, Hweqs |- *. intros eq Hin.
    pose proof (Hun eq Hin) as Hu. pose proof (Hweqs eq Hin) as Hw.
    destruct eq as [xs es]. cbn in Hw.
    destruct Hw as (Hwe & Hweq & Hwv).
    inversion Hu as [out0 xs0 f0 n0 es0 lann0 Hn Hf Hk
                    | out0 xs0 f0 n0 es0 x0 ty0 cl0 lann0 Hn Hf Hk
                    | out0 x0 e0 e1 ann0 Hno H0 H1 | out0 x0 e0 Hc];
      subst; cbn [snd]; (apply Forall_cons; [|apply Forall_nil]).
    - apply src_exp_Eapp; [exact Hn|exact I| exact (wc_call_names _ _ _ _ _ _ Hweq Hwv)].
    - apply src_exp_Eapp; [exact Hn|constructor| exact (wc_call_names _ _ _ _ _ _ Hweq Hwv)].
    - exact (src_exp_Efby _ _ _ _ (normalized_constant_lexp _ H0) H1).
    - exact (src_exp_cexp _ _ Hc).
  Qed.

  Lemma prefs_subset_gensym :
    forall x, In x gensym_prefs -> PS.In x (PSP.of_list gensym_prefs).
  Proof.
    intros x Hx. apply PSP.of_list_1. apply SetoidList.InA_alt. exists x. split;
      [reflexivity|exact Hx].
  Qed.

  Lemma elab_prefs_subset : PS.Subset elab_prefs (PSP.of_list gensym_prefs).
  Proof.
    intros x Hx. unfold elab_prefs in Hx. apply PS.singleton_spec in Hx.
    subst x. apply prefs_subset_gensym. cbn. auto.
  Qed.

  Lemma norm1_prefs_subset : PS.Subset norm1_prefs (PSP.of_list gensym_prefs).
  Proof.
    intros x Hx. unfold norm1_prefs in Hx. apply PS.add_spec in Hx as [Hx|Hx].
    - subst x. apply prefs_subset_gensym. cbn. auto.
    - exact (elab_prefs_subset x Hx).
  Qed.

  Lemma norm2_prefs_subset :
    PS.Subset (PS.add norm2 norm1_prefs) (PSP.of_list gensym_prefs).
  Proof.
    intros x Hx. apply PS.add_spec in Hx as [Hx|Hx].
    - subst x. apply prefs_subset_gensym. cbn. auto.
    - exact (norm1_prefs_subset x Hx).
  Qed.



  (** * The source expressions' anonymous streams are the node's

      What [src_exp] still asks -- the anonymous streams of every
      subexpression of an equation are among the node's -- is a fact about the
      node, not about the program: [anon_in] of a subexpression is inside
      [anon_in] of the expression, and [anon_in_eqs] collects the equations'. *)

  Lemma imm_sub_fresh_anon :
    forall e' e, imm_sub e' e -> incl (fresh_in e') (anon_in e).
  Proof.
    intros e' e H x Hx.
    inversion H; subst; simpl.
    - exact Hx.
    - apply in_or_app. left. exact Hx.
    - apply in_or_app. right. exact Hx.
    - apply in_or_app. left. exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. right. exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. left. exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. right. exact (fresh_in_incl _ _ H0 x Hx).
    - exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. left. exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. right. exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. left. exact Hx.
    - apply in_or_app. right. apply in_or_app. left.
      exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. right. apply in_or_app. right.
      exact (fresh_in_incl _ _ H0 x Hx).
    - destruct ro as [r|]; simpl; [apply in_or_app; left|];
        exact (fresh_in_incl _ _ H0 x Hx).
    - apply in_or_app. right. exact Hx.
  Qed.

  Lemma imm_sub_anon_in :
    forall e' e, imm_sub e' e -> incl (anon_in e') (anon_in e).
  Proof.
    intros e' e H x Hx. apply anon_in_fresh_in in Hx.
    exact (imm_sub_fresh_anon _ _ H x Hx).
  Qed.

  Lemma imm_sub_fresh_in :
    forall e' e, imm_sub e' e -> incl (fresh_in e') (fresh_in e).
  Proof.
    intros e' e H x Hx. apply anon_in_fresh_in.
    exact (imm_sub_fresh_anon _ _ H x Hx).
  Qed.

  Lemma sub_exp_anon_in :
    forall e'' e, sub_exp e'' e -> incl (anon_in e'') (anon_in e).
  Proof.
    intros e'' e H. induction H as [e|e'' e' e Himm Hs IH].
    - apply incl_refl.
    - eapply incl_tran; [exact IH|exact (imm_sub_anon_in _ _ Himm)].
  Qed.

  Lemma sub_exp_fresh_in :
    forall e'' e, sub_exp e'' e -> incl (fresh_in e'') (fresh_in e).
  Proof.
    intros e'' e H. induction H as [e|e'' e' e Himm Hs IH].
    - apply incl_refl.
    - eapply incl_tran; [exact IH|exact (imm_sub_fresh_in _ _ Himm)].
  Qed.

  Lemma wc_call_names_gen :
    forall (vars : list (ident * clock)) (xs : list ident) (es : list exp) f es0
           ro (anns : list LSyn.ann),
      Forall2 (fun x nc => LiftO True (Logic.eq x) (snd nc)) xs (nclocksof es) ->
      Forall2 (fun x ck => In (x, ck) vars) xs (clocksof es) ->
      In (Eapp f es0 ro anns) es ->
      forall w, In (Some w) (List.map stream_name anns) ->
                In w (List.map fst vars).
  Proof.
    intros vars xs es f es0 ro anns Heq Hvs Hin w Hw.
    apply in_map_iff in Hw as (ann & Hann & Hina).
    assert (In (snd ann) (nclocksof es)) as Hnc.
    { unfold nclocksof. apply in_flat_map. exists (Eapp f es0 ro anns).
      split; [exact Hin|]. simpl. apply in_map_iff. exists ann.
      split; [reflexivity|exact Hina]. }
    destruct (Forall2_in_right _ xs (nclocksof es) (snd ann) Heq Hnc)
      as (x & Hx & Hxe).
    unfold stream_name in Hann. simpl in Hxe. rewrite Hann in Hxe.
    simpl in Hxe. subst x.
    destruct (Forall2_in_left _ _ _ w Hvs Hx) as (ck & _ & Hv).
    apply in_map_iff. exists (w, ck). split; [reflexivity|exact Hv].
  Qed.

  Lemma source_exp_node :
    forall (Q : global) (n : node) eq e,
      wc_equation Q (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) eq ->
      In eq n.(n_eqs) -> In e (snd eq) ->
      src_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) (anon_names n) e.
  Proof.
    intros Q n eq e Hweq Heq He e' Hs. split.
    - intros w a Hin.
      apply sub_exp_anon_in in Hs. apply Hs in Hin.
      assert (Hin' : In (w, a) (anon_in_eqs n.(n_eqs))).
      { eapply anon_in_eq_incl; [exact Heq|].
        eapply anon_in_incl; [exact He|exact Hin]. }
      apply in_map_iff. exists (w, a). split; [reflexivity|exact Hin'].
    - destruct e' as [c|x a|op e1 a|op e1 e2 a|e0s es a|e0s es a|es x b a
                     |x ets efs a|e0 ets efs a|f es0 ro anns]; try exact I.
      intros w Hw.
      apply sub_exp_inv in Hs as [Heqe|(e1 & Himm & Hs1)].
      + (* the call is the equation's own: its names are the lhs *)
        right. destruct eq as (xs, es). destruct Hweq as (_ & Hweq1 & Hweq2).
        cbn [snd] in He. subst e.
        exact (wc_call_names_gen _ xs es f es0 ro anns Hweq1 Hweq2 He w Hw).
      + (* nested: its names are anonymous streams of the equation *)
        left. destruct (anon_streams_name w anns Hw) as (a & Ha).
        assert (Hf : In (w, a) (fresh_in (Eapp f es0 ro anns)))
          by exact (nested_call_name_fresh f es0 ro anns w a Ha).
        apply (sub_exp_fresh_in _ _ Hs1) in Hf.
        apply (imm_sub_fresh_anon _ _ Himm) in Hf.
        assert (Hin' : In (w, a) (anon_in_eqs n.(n_eqs))).
        { eapply anon_in_eq_incl; [exact Heq|].
          eapply anon_in_incl; [exact He|exact Hf]. }
        apply in_map_iff. exists (w, a). split; [reflexivity|exact Hin'].
  Qed.

  (** * The two legs' node relations *)

  Definition source_guard (n : node) : Prop :=
    Forall (fun eq =>
              Forall (src_exp (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                        (anon_names n)) (snd eq)) n.(n_eqs).

  Lemma source_guard_holds :
    forall (Q : global) n, wc_node Q n -> source_guard n.
  Proof.
    intros Q n Hwcn. unfold source_guard. apply Forall_forall. intros eq Heq.
    apply Forall_forall. intros e He.
    destruct Hwcn as (_ & _ & _ & Hweqs). rewrite Forall_forall in Hweqs.
    exact (source_exp_node Q n eq e (Hweqs eq Heq) Heq He).
  Qed.

  Lemma wc_global_source_guard :
    forall G, wc_global G -> Forall source_guard G.
  Proof.
    intros G H. induction H as [|n ns Hg IH Hn Hd]; constructor.
    - exact (source_guard_holds ns n Hn).
    - exact IH.
  Qed.

  (** Leg U: [P] is the source program the node is read against. *)
  Definition RU (P : global) (nS nM nN : node) : Prop :=
    exists (Hwl : wl_node P nS) (Hpref : n_prefixes nS = elab_prefs)
           (Q : global) (Hunt : unnested_node Q nM)
           (Hpref1 : n_prefixes nM = norm1_prefs),
      nM = unnest_node P nS Hwl Hpref
      /\ nN = normfby_node Q PS.empty nM Hunt Hpref1
      /\ wc_global P /\ wt_node P nS /\ wc_node P nS
      /\ global_iface_eq P Q /\ wc_global Q
      /\ source_guard nS.

  (** Leg I: [Q] is the unnested program the node is read against. *)
  Definition RI (Q : global) (nM nN nall : node) : Prop :=
    exists (Hunt : unnested_node Q nM) (Hpref1 : n_prefixes nM = norm1_prefs),
      nN = normfby_node Q PS.empty nM Hunt Hpref1
      /\ nall = nN
      /\ wc_global Q /\ wt_node Q nM /\ wc_node Q nM.

  Lemma typed_facts_unnested :
    forall Q (M nall : node),
      unnested_node Q M -> wc_global Q -> wt_node Q M -> wc_node Q M ->
      n_prefixes M = norm1_prefs ->
      node_typed_facts M nall.
  Proof.
    intros Q M nall Hunt Hgq Hwt Hwc Hpref.
    exists Q. refine (conj (wt_node_wl_node _ _ Hwt) (conj Hgq (conj Hwc _))).
    rewrite (anon_names_unnested Q M Hunt).
    refine (conj (unnested_node_src Q M Hgq Hwc Hunt) (conj _ _)).
    - intros w Hw. destruct Hw.
    - rewrite Hpref. exact norm1_prefs_subset.
  Qed.

  Lemma typed_facts_normfby :
    forall Q (M nall : node) (Hunt : unnested_node Q M)
           (Hpref : n_prefixes M = norm1_prefs),
      wc_global Q -> wt_node Q M -> wc_node Q M ->
      node_typed_facts (normfby_node Q PS.empty M Hunt Hpref) nall.
  Proof.
    intros Q M nall Hunt Hpref Hgq Hwt Hwc.
    set (N := normfby_node Q PS.empty M Hunt Hpref).
    assert (HwtN : wt_node Q N)
      by exact (NTyp.normfby_node_wt Q PS.empty M Hunt Hpref Hwt).
    assert (HwcN : wc_node Q N)
      by exact (NClo.normfby_node_wc Q PS.empty M Hunt Hpref Hwc).
    assert (HnN : normalized_node Q N)
      by exact (normfby_node_normalized_node Q M PS.empty Hunt Hpref).
    exists Q. refine (conj (wt_node_wl_node _ _ HwtN) (conj Hgq (conj HwcN _))).
    rewrite (anon_names_normalized Q N HnN).
    refine (conj (normalized_node_src Q N Hgq HwcN HnN) (conj _ _)).
    - intros w Hw. destruct Hw.
    - intros x Hx. apply norm2_prefs_subset. cbn in Hx.
      rewrite Hpref in Hx. exact Hx.
  Qed.

  Lemma typed_facts_source :
    forall P (nS nall : node),
      wl_node P nS -> wc_global P -> wc_node P nS ->
      n_prefixes nS = elab_prefs -> source_guard nS ->
      node_typed_facts nS nall.
  Proof.
    intros P nS nall Hwl Hgp Hwc Hpref Hsrc.
    exists P. refine (conj Hwl (conj Hgp (conj Hwc _))).
    refine (conj Hsrc (conj _ _)).
    - exact (anon_names_not_declared nS).
    - rewrite Hpref. exact elab_prefs_subset.
  Qed.

  Lemma normfby_vars_incl :
    forall Q (M : node) (Hunt : unnested_node Q M)
           (Hpref : n_prefixes M = norm1_prefs),
      incl (n_in M ++ n_vars M ++ n_out M)
           (n_in (normfby_node Q PS.empty M Hunt Hpref)
            ++ n_vars (normfby_node Q PS.empty M Hunt Hpref)
            ++ n_out (normfby_node Q PS.empty M Hunt Hpref)).
  Proof.
    intros Q M Hunt Hpref x Hx.
    assert (Hi : n_in (normfby_node Q PS.empty M Hunt Hpref) = n_in M)
      by reflexivity.
    assert (Ho : n_out (normfby_node Q PS.empty M Hunt Hpref) = n_out M)
      by reflexivity.
    assert (Hv : exists l, n_vars (normfby_node Q PS.empty M Hunt Hpref)
                           = n_vars M ++ l) by (eexists; reflexivity).
    destruct Hv as (l & Hv). rewrite Hi, Hv, Ho.
    apply in_app_or in Hx as [H|H].
    - apply in_or_app. left. exact H.
    - apply in_app_or in H as [H|H]; apply in_or_app; right.
      + apply in_or_app. left. apply in_or_app. left. exact H.
      + apply in_or_app. right. exact H.
  Qed.

  Lemma normalized_vars_nodup :
    forall Q (N : node),
      normalized_node Q N ->
      NoDupMembers (n_in N ++ n_vars N ++ n_out N).
  Proof.
    intros Q N Hn.
    pose proof (n_nodup N) as H.
    assert (Hz : anon_in_eqs (n_eqs N) = []).
    { pose proof (anon_names_normalized Q N Hn) as Ha.
      unfold anon_names in Ha. apply map_eq_nil in Ha. exact Ha. }
    rewrite Hz, app_nil_r in H. exact H.
  Qed.

  Lemma unnested_vars_incl :
    forall P (nS : node) (Hwl : wl_node P nS) (Hpref : n_prefixes nS = elab_prefs)
           Q (Hunt : unnested_node Q (unnest_node P nS Hwl Hpref))
           (Hpref1 : n_prefixes (unnest_node P nS Hwl Hpref) = norm1_prefs),
      incl (n_in (unnest_node P nS Hwl Hpref)
            ++ n_vars (unnest_node P nS Hwl Hpref)
            ++ n_out (unnest_node P nS Hwl Hpref))
           (n_in (normfby_node Q PS.empty (unnest_node P nS Hwl Hpref) Hunt Hpref1)
            ++ n_vars (normfby_node Q PS.empty (unnest_node P nS Hwl Hpref)
                         Hunt Hpref1)
            ++ n_out (normfby_node Q PS.empty (unnest_node P nS Hwl Hpref)
                        Hunt Hpref1)).
  Proof.
    intros. apply normfby_vars_incl.
  Qed.

  Lemma RU_facts :
    forall P nS nM nN, RU P nS nM nN ->
      n_name nS = n_name nN /\ n_name nM = n_name nN
      /\ node_typed_facts nS nN /\ node_typed_facts nM nN
      /\ node_typed_facts nN nN.
  Proof.
    intros P nS nM nN
      (Hwl & Hpref & Q & Hunt & Hpref1 & HM & HN & Hgp & Hwtn & Hwcn & Hif
       & Hgq & Hguard).
    subst nM nN.
    set (M := unnest_node P nS Hwl Hpref) in *.
    assert (HwtM : wt_node P M)
      by exact (NTyp.unnest_node_wt P nS Hwl Hpref Hwtn).
    assert (HwcM : wc_node P M)
      by exact (NClo.unnest_node_wc P nS Hwl Hpref Hgp Hwcn).
    assert (HwtMQ : wt_node Q M) by exact (iface_eq_wt_node P Q M Hif HwtM).
    assert (HwcMQ : wc_node Q M) by exact (iface_eq_wc_node P Q M Hif HwcM).
    refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ (conj _ _)))).
    - exact (typed_facts_source P nS _ Hwl Hgp Hwcn Hpref Hguard).
    - exact (typed_facts_unnested Q M _ Hunt Hgq HwtMQ HwcMQ Hpref1).
    - exact (typed_facts_normfby Q M _ Hunt Hpref1 Hgq HwtMQ HwcMQ).
  Qed.

  Lemma RI_facts :
    forall Q nM nN nall, RI Q nM nN nall ->
      n_name nM = n_name nall /\ n_name nN = n_name nall
      /\ node_typed_facts nM nall /\ node_typed_facts nN nall.
  Proof.
    intros Q nM nN nall (Hunt & Hpref1 & HN & Hall & Hgq & Hwt & Hwc).
    subst nN nall.
    refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ _))).
    - exact (typed_facts_unnested Q nM _ Hunt Hgq Hwt Hwc Hpref1).
    - exact (typed_facts_normfby Q nM _ Hunt Hpref1 Hgq Hwt Hwc).
  Qed.

  (** * One node of each leg, in the lockstep's shape *)

  Lemma stepU :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        RU P nS nM nall ->
        generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
        find_node_env nall.(n_name) envsF = Some env ->
        get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
        (st0 <= stN)%positive ->
        lsig_inv stN st0 accS stS0 ->
        lsig_inv stN st0 accT stT0 ->
        call_weakens accS accT ->
        CALLS.sig_inputs_ok accT P ->
        generate_lnode_sig_scoped_env accS nS envsF auxF stS0
          = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT nM envsF auxF stT0
          = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
  Proof.
    intros all envsF auxF stN Hfull P nS nM nall env r st0 stl accS accT sgS
      stS0 stS1 sgT stT0 stT1 HRU Hloc Hfind Haux Hst0 HinvS HinvT Hw Hj HsS HsT.
    destruct (RU_facts P nS nM nall HRU) as (Hn1 & Hn2 & tfS & tfM & tfN).
    destruct HRU as (Hwl & Hpref & Q & Hunt & Hpref1 & HM & HN & Hgp & Hwtn
                     & Hwcn & Hif & Hgq & Hguard).
    subst nM nall.
    rewrite <- Hn1 in Hfind, Haux.
    exact (unnest_instance all envsF auxF stN P nS Hwl Hpref _ env r st0 stl
             accS accT sgS stS0 stS1 sgT stT0 stT1 Hfull Hloc Hfind Haux Hst0
             HinvS HinvT Hw tfS tfM
             (normfby_vars_incl Q _ Hunt Hpref1)
             (normalized_vars_nodup Q _
                (normfby_node_normalized_node Q _ PS.empty Hunt Hpref1))
             Hgp Hwcn Hj HsS HsT).
  Qed.

  Lemma stepI :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall Q nM nN nall (env : Env.t ident) (r : node_aux_names) st0 stl
             accS accT sgS stS0 stS1 sgT stT0 stT1,
        RI Q nM nN nall ->
        generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
        find_node_env nall.(n_name) envsF = Some env ->
        get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
        (st0 <= stN)%positive ->
        lsig_inv stN st0 accS stS0 ->
        lsig_inv stN st0 accT stT0 ->
        call_weakens accS accT ->
        True ->
        generate_lnode_sig_scoped_env accS nM envsF auxF stS0
          = OK (sgS, stS1) ->
        generate_lnode_sig_scoped_env accT nN envsF auxF stT0
          = OK (sgT, stT1) ->
        sig_head_weakens sgS sgT.
  Proof.
    intros all envsF auxF stN Hfull Q nM nN nall env r st0 stl accS accT sgS
      stS0 stS1 sgT stT0 stT1 HRI Hloc Hfind Haux Hst0 HinvS HinvT Hw _ HsS HsT.
    destruct (RI_facts Q nM nN nall HRI) as (Hn1 & Hn2 & tfM & tfN).
    destruct HRI as (Hunt & Hpref1 & HN & Hall & Hgq & Hwt & Hwc).
    subst nN nall.
    rewrite <- Hn1 in Hfind, Haux.
    exact (normfby_instance all envsF auxF stN Q PS.empty nM Hunt Hpref1 env r
             st0 stl accS accT sgS stS0 stS1 sgT stT0 stT1 Hfull Hloc Hfind
             Haux Hst0 HinvS HinvT Hw tfM tfN
             (normfby_clocks_pass_fact Q PS.empty nM Hgq Hwc Hunt) HsS HsT).
  Qed.

  (** * The builders of the lockstep relation *)

  Lemma Forall3P_snoc :
    forall {A B C : Type} (R : list A -> A -> B -> C -> Prop) P0 l1 l2 l3 a b c,
      Forall3P R P0 l1 l2 l3 ->
      R (List.rev l1 ++ P0) a b c ->
      Forall3P R P0 (l1 ++ [a]) (l2 ++ [b]) (l3 ++ [c]).
  Proof.
    intros A B C R P0 l1 l2 l3 a b c H. revert a b c.
    induction H as [P|P a0 b0 c0 l1 l2 l3 Hr Hrest IH]; intros a b c HR.
    - cbn in HR. cbn [app]. exact (Forall3P_cons R P a b c [] [] []
                                     HR (Forall3P_nil R (a :: P))).
    - cbn [app]. apply Forall3P_cons; [exact Hr|].
      apply IH. cbn [List.rev] in HR. rewrite <- app_assoc in HR.
      exact HR.
  Qed.

  Lemma RU_intro :
    forall P nS (Hwl : wl_node P nS) (Hpref : n_prefixes nS = elab_prefs)
           Q (Hunt : unnested_node Q (unnest_node P nS Hwl Hpref))
           (Hpref1 : n_prefixes (unnest_node P nS Hwl Hpref) = norm1_prefs),
      wc_global P -> wt_node P nS -> wc_node P nS ->
      global_iface_eq P Q -> wc_global Q -> source_guard nS ->
      RU P nS (unnest_node P nS Hwl Hpref)
         (normfby_node Q PS.empty (unnest_node P nS Hwl Hpref) Hunt Hpref1).
  Proof.
    intros P nS Hwl Hpref Q Hunt Hpref1 Hg Hwt Hwc Hif Hgq Hguard.
    exists Hwl, Hpref, Q, Hunt, Hpref1.
    refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
    exact (conj Hg (conj Hwt (conj Hwc (conj Hif (conj Hgq Hguard))))).
  Qed.

  Lemma RI_intro :
    forall Q nM (Hunt : unnested_node Q nM)
           (Hpref1 : n_prefixes nM = norm1_prefs),
      wc_global Q -> wt_node Q nM -> wc_node Q nM ->
      RI Q nM (normfby_node Q PS.empty nM Hunt Hpref1)
         (normfby_node Q PS.empty nM Hunt Hpref1).
  Proof.
    intros Q nM Hunt Hpref1 Hg Hwt Hwc.
    exists Hunt, Hpref1.
    exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg (conj Hwt Hwc)))).
  Qed.

  Lemma build_U :
    forall G (Hwl : wl_global G)
           (Hpr : Forall (fun n => n_prefixes n = elab_prefs) G)
           (Hunt : unnested_global (unnest_global G Hwl Hpr))
           (Hpref1 : Forall (fun n => n_prefixes n = norm1_prefs)
                       (unnest_global G Hwl Hpr)),
      wc_global G -> wt_global G -> Forall source_guard G ->
      Forall3P RU []
        (List.rev G) (List.rev (unnest_global G Hwl Hpr))
        (List.rev (normfby_global (unnest_global G Hwl Hpr) Hunt Hpref1)).
  Proof.
    induction G as [|a tl IH]; intros Hwl Hpr Hunt Hpref1 Hwc Hwt Hguard.
    - cbn. constructor.
    - inversion Hwc as [|? ? Hwc' Hwcn Hnm]; subst.
      inversion Hwt as [|? ? Hwt' Hwtn Hnm']; subst.
      inversion Hguard as [|? ? Hga Hgt]; subst.
      cbn [unnest_global normfby_global List.rev].
      apply Forall3P_snoc.
      + eapply IH; assumption.
      + rewrite List.rev_involutive, app_nil_r.
        eapply RU_intro; try assumption.
        * exact (unnest_global_eq _ _ _).
        * exact (NClo.unnest_global_wc _ _ _ Hwc').
  Qed.

  Lemma build_I :
    forall G1 (Hunt : unnested_global G1)
           (Hp : Forall (fun n => n_prefixes n = norm1_prefs) G1),
      wc_global G1 -> wt_global G1 ->
      Forall3P RI []
        (List.rev G1) (List.rev (normfby_global G1 Hunt Hp))
        (List.rev (normfby_global G1 Hunt Hp)).
  Proof.
    induction G1 as [|a tl IH]; intros Hunt Hp Hwc Hwt.
    - cbn. constructor.
    - inversion Hwc as [|? ? Hwc' Hwcn Hnm]; subst.
      inversion Hwt as [|? ? Hwt' Hwtn Hnm']; subst.
      cbn [normfby_global List.rev].
      apply Forall3P_snoc.
      + eapply IH; assumption.
      + rewrite List.rev_involutive, app_nil_r.
        eapply RI_intro; assumption.
  Qed.

  (** * The program driver, with the invariants *)

  Theorem generate_all_lsignatures_weakens_ext_driver :
    forall (all : list node) envsF auxF stN st,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall (R : global -> node -> node -> node -> Prop)
             (Jinv : secglobal -> global -> Prop),
        (forall P nS nM nall, R P nS nM nall ->
           n_name nS = n_name nall /\ node_typed_facts nS nall
           /\ n_name nM = n_name nall /\ node_typed_facts nM nall) ->
        (forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
                accT sgT stT0 stT1,
            R P nS nM nall ->
            generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
            find_node_env nall.(n_name) envsF = Some env ->
            get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
            (st0 <= stN)%positive ->
            lsig_inv stN st0 accT stT0 ->
            Jinv accT P ->
            generate_lnode_sig_scoped_env accT nM envsF auxF stT0
              = OK (sgT, stT1) ->
            Jinv (sgT :: accT) (nS :: P)) ->
        (forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
                accS accT sgS stS0 stS1 sgT stT0 stT1,
            R P nS nM nall ->
            generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
            find_node_env nall.(n_name) envsF = Some env ->
            get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
            (st0 <= stN)%positive ->
            lsig_inv stN st0 accS stS0 ->
            lsig_inv stN st0 accT stT0 ->
            call_weakens accS accT ->
            Jinv accT P ->
            generate_lnode_sig_scoped_env accS nS envsF auxF stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nM envsF auxF stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        forall nsS nsM,
          Forall3P R [] nsS nsM all ->
          NoDup (List.map n_name all) ->
          sec_le stN st ->
          Jinv [] [] ->
          forall GS GT,
            generate_all_lsignatures_scoped_env nsS envsF auxF st = OK GS ->
            generate_all_lsignatures_scoped_env nsM envsF auxF st = OK GT ->
            call_weakens GS GT /\ sigs_preserved GS GT
            /\ Jinv GT (List.rev nsS).
  Proof.
    intros all envsF auxF stN st Hfull R Jinv HR HJ Hstep nsS nsM HF3 Hnd Hle
      Hj0 GS GT HgS HgT.
    unfold generate_all_lsignatures_scoped_env in HgS, HgT.
    destruct (generate_all_lsignatures' [] nsS envsF auxF st)
      as [[GS' stfS]|e] eqn:HallS; [|discriminate HgS].
    destruct (generate_all_lsignatures' [] nsM envsF auxF st)
      as [[GT' stfT]|e] eqn:HallT; [|discriminate HgT].
    inversion HgS; subst GS'. inversion HgT; subst GT'.
    pose proof Hfull as Hfull0.
    unfold generate_lnode_scoped_env_st in Hfull.
    destruct (generate_lnode_scoped_env' all (Env.empty _) [] init_state)
      as [[[envs0 aux0] st0]|e] eqn:Hrun; [|discriminate Hfull].
    inversion Hfull; subst envs0 aux0 st0.
    destruct (generate_all_lsignatures_weakens_ext all envsF auxF stN Hfull0
                R Jinv HR HJ Hstep [] nsS nsM all (Env.empty _) [] init_state
                HF3 Hnd Hrun [] [] st st GS GT stfS stfT
                (lsig_inv_nil stN init_state st Hle)
                (lsig_inv_nil stN init_state st Hle)
                call_weakens_nil sigs_preserved_nil Hj0 HallS HallT)
      as (Hc & Hp & Hj).
    rewrite app_nil_r in Hj. auto.
  Qed.

  Lemma sig_inputs_ok_nil : CALLS.sig_inputs_ok [] [].
  Proof. intros f n sg Hf. simpl in Hf. discriminate Hf. Qed.

  (** * The program theorem for both legs *)

  Lemma unnest_global_map_names :
    forall G (Hwl : wl_global G)
           (Hpr : Forall (fun n => n_prefixes n = elab_prefs) G),
      List.map n_name (unnest_global G Hwl Hpr) = List.map n_name G.
  Proof.
    induction G as [|a tl IH]; intros Hwl Hpr; [reflexivity|].
    simpl. f_equal. apply IH.
  Qed.

  Lemma normfby_global_map_names :
    forall G (Hunt : unnested_global G)
           (Hp : Forall (fun n => n_prefixes n = norm1_prefs) G),
      List.map n_name (normfby_global G Hunt Hp) = List.map n_name G.
  Proof.
    induction G as [|a tl IH]; intros Hunt Hp; [reflexivity|].
    simpl. f_equal. apply IH.
  Qed.

  Lemma wc_global_names_nodup :
    forall G, wc_global G -> NoDup (List.map n_name G).
  Proof.
    intros G H. induction H as [|n ns Hg IH Hwc Hnm]; cbn [List.map];
      [constructor|].
    constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin as (n' & Hn' & Hin').
    rewrite Forall_forall in Hnm. exact (Hnm n' Hin' (@Logic.eq_sym _ _ _ Hn')).
  Qed.



  (** * The source signatures are good

      The invariants the lockstep keeps on the source accumulator, read off at
      the end: every source signature is [signature_good] with a duplicate-free
      scope.  This is what the composition with the translation leg asks of the
      source side. *)

  Lemma Forall3P_Forall2_13 :
    forall {A B C : Type} (R : list A -> A -> B -> C -> Prop) P0 l1 l2 l3,
      Forall3P R P0 l1 l2 l3 ->
      Forall2 (fun a c => exists P b, R P a b c) l1 l3.
  Proof.
    intros A B C R P0 l1 l2 l3 H.
    induction H as [P|P a b c l1 l2 l3 Hr Hrest IH]; constructor;
      [eauto|exact IH].
  Qed.

  Lemma lsig_inv_find_good :
    forall stN low acc st f sg,
      lsig_inv stN low acc st ->
      find_signature f acc = Some sg ->
      signature_good sg /\ NoDup (signature_scope sg).
  Proof.
    intros stN low acc st f sg (Hg & Hs & Hnd & _) Hf.
    split; [exact (Hg _ _ Hf)|].
    pose proof (Hnd _ _ Hf) as H. unfold sig_nd in H.
    unfold signature_scope. eapply Permutation_NoDup; [|exact H].
    apply Permutation_app_head.
    exact (Permutation_app_comm [sg.(s_clk); sg.(s_reset)] sg.(s_out)).
  Qed.

  Theorem source_signatures_good :
    forall (G : global) (Hwl : wl_global G)
           (Hpr : Forall (fun n => n_prefixes n = elab_prefs) G)
           (Hunt : unnested_global (unnest_global G Hwl Hpr))
           (Hpref1 : Forall (fun n => n_prefixes n = norm1_prefs)
                       (unnest_global G Hwl Hpr)),
      wc_global G -> wt_global G ->
      forall envsF auxF stN st GS,
        generate_lnode_scoped_env_st
          (List.rev (normfby_global (unnest_global G Hwl Hpr) Hunt Hpref1))
          = OK (envsF, auxF, stN) ->
        sec_le stN st ->
        generate_all_lsignatures_scoped_env (List.rev G) envsF auxF st = OK GS ->
        forall f sg, find_signature f GS = Some sg ->
          signature_good sg /\ NoDup (signature_scope sg).
  Proof.
    intros G Hwl Hpr Hunt Hpref1 Hwc Hwt envsF auxF stN st GS
      Hnaming Hle HgS f sg Hf.
    pose proof (wc_global_source_guard G Hwc) as Hguard.
    set (G1 := unnest_global G Hwl Hpr) in *.
    set (G2 := normfby_global G1 Hunt Hpref1) in *.
    assert (Hnd : NoDup (List.map n_name (List.rev G2))).
    { rewrite List.map_rev.
      apply (Permutation_NoDup (Permutation_rev _)).
      unfold G2. rewrite normfby_global_map_names. unfold G1.
      rewrite unnest_global_map_names. exact (wc_global_names_nodup G Hwc). }
    pose proof (Forall3P_Forall2_13 RU [] _ _ _
                  (build_U G Hwl Hpr Hunt Hpref1 Hwc Hwt Hguard)) as HF2.
    unfold generate_all_lsignatures_scoped_env in HgS.
    destruct (generate_all_lsignatures' [] (List.rev G) envsF auxF st)
      as [[GS' stf]|e] eqn:HallS; [|discriminate HgS].
    inversion HgS; subst GS'.
    pose proof Hnaming as Hnaming0.
    unfold generate_lnode_scoped_env_st in Hnaming.
    destruct (generate_lnode_scoped_env' (List.rev G2) (Env.empty _) []
                init_state) as [[[envs0 aux0] st0]|e] eqn:Hrun;
      [|discriminate Hnaming].
    inversion Hnaming; subst envs0 aux0 st0.
    pose proof (generate_all_lsignatures'_inv_ext (List.rev G2) envsF auxF stN
                Hnaming0 (fun n nall => exists P b, RU P n b nall)
                (fun n nall HR =>
                   match HR with
                   | ex_intro P (ex_intro b HRU) =>
                     match RU_facts P n b nall HRU with
                     | conj Hn1 (conj _ (conj tfS _)) => conj Hn1 tfS
                     end
                   end)
                (List.rev G) (List.rev G2) (Env.empty _) [] init_state HF2 Hnd
                Hrun [] st GS stf (lsig_inv_nil stN init_state st Hle) HallS)
      as Hinv.
    exact (lsig_inv_find_good _ _ _ _ f sg Hinv Hf).
  Qed.


  (** * Item 8: the clock closure of a generated signature's inputs

      [sig_inputs_ok] asks, of a callee's generated signature, that a stored
      constraint mentioning an input's security name also mentions the names of
      the clock variables of that input's declared clock.  Everything here is
      relative to a set [ins] of declared variables (the inputs) and a
      predicate [zs] on the names a clock type can contain: the base name and
      the names of [ins] themselves, none of which is ever a constraint's
      target or an eliminated local. *)

  Definition icl (env : Env.t ident) (ct : ident)
             (ins : list (ident * clock)) (c : SymTypes.constraint) : Prop :=
    forall v b ckv ckvty,
      Env.find v env = Some b -> In b (fst c) -> In (v, ckv) ins ->
      assign_clk_type env ct ckv = Some ckvty -> incl ckvty (fst c).

  Definition ntg (zs : ident -> Prop) (c : SymTypes.constraint) : Prop :=
    forall t, In t (snd c) -> ~ zs t.

  Lemma join_into_ok :
    forall env ct ins zs l r acc,
      icl env ct ins (l, r) -> ntg zs (l, r) ->
      Forall (icl env ct ins) acc -> Forall (ntg zs) acc ->
      Forall (icl env ct ins) (SymTypes.join_into l r acc)
      /\ Forall (ntg zs) (SymTypes.join_into l r acc).
  Proof.
    intros env ct ins zs l r acc Hc Ht.
    induction acc as [|[l' r'] acc IH]; intros Hi Hn; cbn [SymTypes.join_into].
    - split; constructor; [exact Hc|constructor|exact Ht|constructor].
    - inversion Hi as [|? ? Hi1 Hi2]; subst.
      inversion Hn as [|? ? Hn1 Hn2]; subst.
      destruct (SymTypes.st_eq_dec r r') as [Heq|Hne].
      + split; constructor; try assumption.
        intros v b ckv ckvty Hf Hb Hin Hck. cbn [fst] in Hb.
        apply in_merge_inv in Hb as [Hb|Hb]; intros z Hz; cbn [fst].
        * apply in_merge_left. exact (Hc v b ckv ckvty Hf Hb Hin Hck z Hz).
        * apply in_merge_right.
          exact (Hi1 v b ckv ckvty Hf Hb Hin Hck z Hz).
      + destruct (IH Hi2 Hn2) as [A B]. split; constructor; assumption.
  Qed.

  Lemma collapse_ok :
    forall env ct ins zs cs,
      Forall (icl env ct ins) cs -> Forall (ntg zs) cs ->
      Forall (icl env ct ins) (SymTypes.collapse cs)
      /\ Forall (ntg zs) (SymTypes.collapse cs).
  Proof.
    intros env ct ins zs cs. induction cs as [|[l r] cs IH]; intros Hi Hn.
    - split; constructor.
    - inversion Hi as [|? ? Hi1 Hi2]; subst.
      inversion Hn as [|? ? Hn1 Hn2]; subst.
      destruct (IH Hi2 Hn2) as [A B]. cbn [SymTypes.collapse].
      exact (join_into_ok env ct ins zs l r _ Hi1 Hn1 A B).
  Qed.

  Lemma subST_in :
    forall a d b z,
      In z (SymTypes.subST a d b) ->
      z <> d /\ (In z a \/ (In d a /\ In z b)).
  Proof.
    intros a d b z Hz. unfold SymTypes.subST in Hz.
    destruct (SymTypes.st_mem d a) eqn:Ha.
    - assert (Hda : In d a)
        by (apply SymTypes.my_set_mem_correct; exact Ha).
      destruct (SymTypes.st_mem d b) eqn:Hb.
      + apply in_merge_inv in Hz as [Hz|Hz].
        * destruct (SymTypes.st_remove_in_inv _ _ _ Hz) as [H1 H2].
          split; [exact H2|left; exact H1].
        * destruct (SymTypes.st_remove_in_inv _ _ _ Hz) as [H1 H2].
          split; [exact H2|right; split; [exact Hda|exact H1]].
      + apply in_merge_inv in Hz as [Hz|Hz].
        * destruct (SymTypes.st_remove_in_inv _ _ _ Hz) as [H1 H2].
          split; [exact H2|left; exact H1].
        * assert (z <> d) as Hne.
          { intro Heq. subst z. 
            assert (SymTypes.st_mem d b = true)
              by (apply SymTypes.my_set_mem_correct; exact Hz).
            congruence. }
          split; [exact Hne|right; split; [exact Hda|exact Hz]].
    - split; [|left; exact Hz].
      intro Heq. subst z.
      assert (SymTypes.st_mem d a = true)
        by (apply SymTypes.my_set_mem_correct; exact Hz).
      congruence.
  Qed.

  Lemma subST_intro_l :
    forall a d b z, In z a -> z <> d -> In z (SymTypes.subST a d b).
  Proof.
    intros a d b z Hz Hne. unfold SymTypes.subST.
    destruct (SymTypes.st_mem d a) eqn:Ha.
    - destruct (SymTypes.st_mem d b);
        apply in_merge_left; apply SymTypes.st_remove_preserves_other_in;
        assumption.
    - exact Hz.
  Qed.

  Lemma subST_intro_r :
    forall a d b z, In d a -> In z b -> z <> d -> In z (SymTypes.subST a d b).
  Proof.
    intros a d b z Hd Hz Hne. unfold SymTypes.subST.
    assert (SymTypes.st_mem d a = true)
      by (apply SymTypes.my_set_mem_correct; exact Hd).
    rewrite H.
    destruct (SymTypes.st_mem d b);
      apply in_merge_right; [apply SymTypes.st_remove_preserves_other_in|];
      assumption.
  Qed.

  Section SimplifyClosed.

    Variable env : Env.t ident.
    Variable ct  : ident.
    Variable ins : list (ident * clock).
    Variable zs  : ident -> Prop.

    Hypothesis HZ :
      forall v ckv ckvty z,
        In (v, ckv) ins -> assign_clk_type env ct ckv = Some ckvty ->
        In z ckvty -> zs z.

    Lemma subAll_ok :
      forall cns d st,
        Forall (icl env ct ins) cns -> Forall (ntg zs) cns ->
        ~ zs d -> icl env ct ins (st, [d]) ->
        Forall (icl env ct ins) (SymTypes.subAll cns d st)
        /\ Forall (ntg zs) (SymTypes.subAll cns d st).
    Proof.
      intros cns d st. induction cns as [|[st0 rhs] cns IH]; intros Hi Hn Hd Hst;
        cbn [SymTypes.subAll].
      - split; constructor.
      - inversion Hi as [|? ? Hi1 Hi2]; subst.
        inversion Hn as [|? ? Hn1 Hn2]; subst.
        destruct (IH Hi2 Hn2 Hd Hst) as [A B].
        destruct rhs as [|d' [|d'' rhs']]; try exact (conj A B).
        destruct (ident_eqb d' d) eqn:Hdd; [exact (conj A B)|].
        split; constructor; try assumption.
        + unfold SymTypes.normalize_constraint.
          intros v b ckv ckvty Hf Hb Hin Hck. cbn [fst] in Hb.
          destruct (SymTypes.st_remove_in_inv _ _ _ Hb) as [HbL Hbd'].
          destruct (subST_in _ _ _ _ HbL) as [Hbd [Hb0|(Hdin & Hbst)]].
          * intros z Hz. cbn [fst].
            apply SymTypes.st_remove_preserves_other_in.
            -- intro Heq. subst z. exact (Hn1 d' (or_introl Logic.eq_refl)
                                           (HZ _ _ _ _ Hin Hck Hz)).
            -- apply subST_intro_l.
               ++ exact (Hi1 v b ckv ckvty Hf Hb0 Hin Hck z Hz).
               ++ intro Heq. subst z. exact (Hd (HZ _ _ _ _ Hin Hck Hz)).
          * intros z Hz. cbn [fst].
            apply SymTypes.st_remove_preserves_other_in.
            -- intro Heq. subst z. exact (Hn1 d' (or_introl Logic.eq_refl)
                                           (HZ _ _ _ _ Hin Hck Hz)).
            -- apply subST_intro_r.
               ++ exact Hdin.
               ++ exact (Hst v b ckv ckvty Hf Hbst Hin Hck z Hz).
               ++ intro Heq. subst z. exact (Hd (HZ _ _ _ _ Hin Hck Hz)).
    Qed.

    Lemma simplify_ok :
      forall ds cns,
        Forall (icl env ct ins) cns -> Forall (ntg zs) cns ->
        (forall d, In d ds -> ~ zs d) ->
        Forall (icl env ct ins) (SymTypes.simplify cns ds)
        /\ Forall (ntg zs) (SymTypes.simplify cns ds).
    Proof.
      intros ds. induction ds as [|d ds IH]; intros cns Hi Hn Hds;
        cbn [SymTypes.simplify].
      - exact (conj Hi Hn).
      - destruct (SymTypes.findST cns d) as [st|] eqn:Hf.
        + apply SymTypes.find_correct in Hf.
          assert (Hc : icl env ct ins (st, [d]))
            by (rewrite Forall_forall in Hi; exact (Hi _ Hf)).
          destruct (subAll_ok cns d st Hi Hn (Hds d (or_introl Logic.eq_refl))
                      Hc) as [A B].
          exact (IH _ A B (fun d0 H0 => Hds d0 (or_intror H0))).
        + exact (IH _ Hi Hn (fun d0 H0 => Hds d0 (or_intror H0))).
    Qed.

  End SimplifyClosed.

  Lemma assign_clk_type_vars_in :
    forall env bt ck ckty x y,
      assign_clk_type env bt ck = Some ckty ->
      In x (clock_vars ck) -> Env.find x env = Some y -> In y ckty.
  Proof.
    intros env bt ck. induction ck as [|ck0 IH x0 b]; intros ckty x y H Hx Hf.
    - simpl in Hx. contradiction.
    - apply assign_clk_type_Con_inv in H as (ckty0 & g & H0 & Hg & ->).
      simpl in Hx. destruct Hx as [Hx|Hx].
      + subst x0. rewrite Hg in Hf. apply option_Some_inj in Hf. subst g.
        apply in_merge_right. now left.
      + apply in_merge_left. exact (IH ckty0 x y H0 Hx Hf).
  Qed.

  (** From the per-constraint closure to the form the call rule consumes. *)
  Lemma closed_of_icl :
    forall env ct (ins : list (ident * clock)) (cs : list SymTypes.constraint),
      Forall (icl env ct ins) cs ->
      (forall x ck x', In (x, ck) ins -> In x' (clock_vars ck) ->
                       exists y', Env.find x' env = Some y') ->
      forall c, In c cs ->
      forall x ck y, In (x, ck) ins -> Env.find x env = Some y ->
        In y (fst c) ->
        forall x' y', In x' (clock_vars ck) -> Env.find x' env = Some y' ->
          In y' (fst c).
  Proof.
    intros env ct ins cs Hi Hkeys c Hc x ck y Hin Hx Hy x' y' Hx' Hy'.
    rewrite Forall_forall in Hi.
    destruct (assign_clk_type_total_of_vars env ct ck
                (fun x0 Hx0 => Hkeys x ck x0 Hin Hx0)) as (ckty & Hck).
    exact (Hi c Hc x y ck ckty Hx Hy Hin Hck y'
             (assign_clk_type_vars_in env ct ck ckty x' y' Hck Hx' Hy')).
  Qed.

  (** The expressions an unnested node's non-call equations hold. *)
  Definition cf_exp (e : exp) : Prop :=
    normalized_cexp e
    \/ exists e0 e1 a,
         (e = Efby [e0] [e1] [a] \/ e = Earrow [e0] [e1] [a])
         /\ normalized_lexp e0 /\ normalized_lexp e1.

  Lemma named_ok_cf :
    forall (vars : list (ident * clock)) e, cf_exp e -> named_ok vars e.
  Proof.
    intros vars e Hcf f es r anns w Hs Hw.
    destruct Hcf as [Hn|(e0 & e1 & a & He & H0 & H1)].
    - exact (named_ok_normalized_cexp vars e Hn f es r anns w Hs Hw).
    - destruct He as [He|He]; subst e;
        apply sub_exp_inv in Hs as [Heq|[e' [Himm Hs']]]; try discriminate;
        inversion Himm; subst;
        match goal with
        | Hin : In _ [_] |- _ =>
          destruct Hin as [<-|[]];
          first [exact (named_ok_normalized_lexp vars _ H0 f es r anns w Hs' Hw)
                |exact (named_ok_normalized_lexp vars _ H1 f es r anns w Hs' Hw)]
        end.
  Qed.

  Lemma assign_lexp_delay_pure :
    forall G env bt rt e0 e1 e a st ts st',
      normalized_lexp e0 -> normalized_lexp e1 ->
      (e = Efby [e0] [e1] [a] \/ e = Earrow [e0] [e1] [a]) ->
      assign_lexp_type G env bt rt e st = OK (ts, st') ->
      st' = st /\ List.length ts = 1 /\ carried ts = [].
  Proof.
    intros G env bt rt e0 e1 e a st ts st' H0 H1 He Hrun.
    assert (Hr : (do ts0 <- assign_lexps G env bt rt [e0];
                  do us <- assign_lexps G env bt rt [e1];
                  ljoin_list ts0 us) st = OK (ts, st')).
    { destruct He as [ -> | -> ].
      - rewrite assign_lexp_Efby in Hrun. exact Hrun.
      - rewrite assign_lexp_Earrow in Hrun. exact Hrun. }
    eapply sec_bind_inv in Hr as (ts0 & sa & Hts0 & Hr).
    eapply sec_bind_inv in Hr as (us & sb & Hus & Hj).
    assert (Forall normalized_cexp [e0]) as Hc0
      by (constructor; [apply normalized_lexp_cexp; exact H0|constructor]).
    assert (Forall normalized_cexp [e1]) as Hc1
      by (constructor; [apply normalized_lexp_cexp; exact H1|constructor]).
    destruct (assign_lexps_normalized_pure G env bt rt [e0] Hc0 ts0 st sa Hts0)
      as (? & Hl0 & Hca0 & _); subst sa.
    destruct (assign_lexps_normalized_pure G env bt rt [e1] Hc1 us st sb Hus)
      as (? & Hl1 & Hca1 & _); subst sb.
    assert (st' = st) as ? by (eapply ljoin_list_pure; exact Hj); subst st'.
    destruct ts0 as [|p [|]]; simpl in Hl0; try discriminate.
    destruct us as [|q [|]]; simpl in Hl1; try discriminate.
    simpl in Hj. eapply sec_bind_inv in Hj as (r & s2 & Hr2 & Hret).
    unfold ret in Hr2. inversion Hr2; subst r. unfold ret in Hret.
    inversion Hret; subst ts.
    rewrite carried_single in Hca0, Hca1.
    split; [reflexivity|split; [reflexivity|]].
    rewrite carried_single. rewrite snd_ljoin, Hca0, Hca1. reflexivity.
  Qed.

  Lemma ldef_ok :
    forall (G : secglobal) env ct rt (cenv : Env.t (type * clock)) (P : global)
           (vars ins : list (ident * clock)) (zs : ident -> Prop)
           x e ckx cs st st',
      env_injective env -> NoDupMembers vars ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> ct) ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> rt) ->
      (forall v ckv, In (v, ckv) ins -> In (v, ckv) vars) ->
      wc_global P -> wc_env vars ->
      wc_exp P vars e -> cf_exp e ->
      clockof e = [ckx] -> find_clock cenv x = OK ckx -> In (x, ckx) vars ->
      (forall b, Env.find x env = Some b -> ~ zs b) ->
      generate_ldef_constraint G env ct rt cenv x e st = OK (cs, st') ->
      Forall (icl env ct ins) cs /\ Forall (ntg zs) cs.
  Proof.
    intros G env ct rt cenv P vars ins zs x e ckx cs st st' Hinj Hnd Hbase Hrst
      Hins Hg Hwenv Hwc Hcf Hclk Hfc Hxin Hbz Hgen.
    destruct (generate_ldef_constraint_inv G env ct rt cenv x e cs st st' Hgen)
      as (ck & ckty & tf & b & st1 & Hck & Hckty & Hrun & Hb & Hst' & Hcs).
    destruct tf as (sa, rho).
    rewrite Hfc in Hck. inversion Hck; subst ck. clear Hck.
    assert (st1 = st /\ carried [(sa, rho)] = []) as (Hst & Hcar).
    { destruct Hcf as [Hn|(e0 & e1 & a & He & H0 & H1)].
      - destruct (assign_lexp_normalized_cexp_pure G env ct rt e Hn _ _ _ Hrun)
          as (? & _ & Hc & _). auto.
      - destruct (assign_lexp_delay_pure G env ct rt e0 e1 e a st _ st1 H0 H1 He
                    Hrun) as (? & _ & Hc). auto. }
    subst st1. subst st'. rewrite carried_single in Hcar. cbn [snd] in Hcar.
    subst rho.
    rewrite cmerge_nil in Hcs. cbn [fst] in Hcs. subst cs.
    assert (wc_clock vars ckx) as Hwck.
    { unfold wc_env in Hwenv. rewrite Forall_forall in Hwenv.
      exact (Hwenv _ Hxin). }
    pose proof (assign_lexp_type_clock_closed G env ct rt P vars Hinj Hnd e Hwc
                  (named_ok_cf vars e Hcf)
                  [(sa, [])] st st [] ltac:(rewrite minted_refl; intros z []) Hrun)
      as Hlcc.
    rewrite Hclk in Hlcc. inversion Hlcc as [|t0 c0 ts0 cs0 Hl1 Hl2]; subst.
    split; constructor; [|constructor| |constructor].
    - intros v b' ckv ckvty Hf Hb' Hin Hck'. cbn [fst] in Hb'.
      intros z Hz. cbn [fst].
      apply in_merge_inv in Hb' as [Hb'|Hb'].
      + apply in_merge_inv in Hb' as [Hb'|Hb'].
        * exfalso. destruct Hb' as [Hb'|[]]. subst b'.
          exact (Hrst v ckv rt (Hins _ _ Hin) Hf Logic.eq_refl).
        * apply in_merge_left. apply in_merge_right.
          exact (assign_clk_type_clock_closed env ct vars Hinj Hnd Hbase ckx
                   ckty Hwck Hckty v b' ckv ckvty Hf Hb' (Hins _ _ Hin) Hck'
                   z Hz).
      + pose proof (Hl1 ckty b' Hckty (fun H => H) Hb' v ckv ckvty Hf
                      (Hins _ _ Hin) Hck' z Hz) as Hz'.
        apply in_merge_inv in Hz' as [Hz'|Hz'].
        * apply in_merge_left. apply in_merge_right. exact Hz'.
        * apply in_merge_right. exact Hz'.
    - intros t Ht. cbn [snd] in Ht. destruct Ht as [<-|[]]. exact (Hbz b Hb).
  Qed.


  (** The names a clock type of an input can contain: the base name and the
      security names of the inputs. *)
  Definition zset (env : Env.t ident) (ct : ident)
             (ins : list (ident * clock)) (z : ident) : Prop :=
    z = ct \/ exists x ck, In (x, ck) ins /\ Env.find x env = Some z.

  Lemma HZ_of_ins :
    forall env ct (ins : list (ident * clock)),
      wc_env ins ->
      forall v ckv ckvty z,
        In (v, ckv) ins -> assign_clk_type env ct ckv = Some ckvty ->
        In z ckvty -> zset env ct ins z.
  Proof.
    intros env ct ins Hwc v ckv ckvty z Hin Hck Hz.
    destruct (assign_clk_type_images env ct ckv ckvty Hck z Hz)
      as [->|(x & Hx & Hf)].
    - left. reflexivity.
    - right. unfold wc_env in Hwc. rewrite Forall_forall in Hwc.
      pose proof (Hwc _ Hin) as Hw. cbn [snd] in Hw.
      destruct (clock_vars_wc ins ckv Hw x Hx) as (ckx & Hxin).
      exists x, ckx. split; assumption.
  Qed.

  Lemma icl_of_closed_mod :
    forall env ct ins cs,
      CALLS.constraints_closed_mod env ct ins [] [] cs ->
      Forall (icl env ct ins) cs.
  Proof.
    intros env ct ins cs H. unfold CALLS.constraints_closed_mod in H.
    eapply Forall_impl; [|exact H].
    intros c Hc v b ckv ckvty Hf Hb Hin Hck z Hz.
    pose proof (Hc v b ckv ckvty Hf (fun H => H) Hb Hin Hck z Hz) as Hz'.
    apply in_merge_inv in Hz' as [Hz'|Hz']; [contradiction|exact Hz'].
  Qed.

  Lemma normalized_lexp_not_Eapp :
    forall e f es ro anns, normalized_lexp e -> e <> Eapp f es ro anns.
  Proof. intros e f es ro anns H. inversion H; discriminate. Qed.

  Lemma scope_fresh_for_env_of :
    forall env ct rt st0 stl sg,
      (exists ci, Env.find ci env = Some ct) ->
      (exists ri, Env.find ri env = Some rt) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (st0 <= k)%positive /\ (k < stl)%positive) ->
      signature_scope_bounded_above sg st0 ->
      CALLS.sig_scope_fresh_for_env env ct rt sg.
  Proof.
    intros env ct rt st0 stl sg (ci & Hct) (ri & Hrt) Hrng Hbd.
    assert (Hall : forall b, (exists x, Env.find x env = Some b) ->
                             ~ In b (signature_scope sg)).
    { intros b (x & Hx) Hin.
      destruct (Hrng x b Hx) as (k & Hk & Hlo & _). subst b.
      destruct (Hbd _ Hin) as (n & Hn & Hlt).
      apply gensym_injective in Hn as [_ Hn]. subst n. lia. }
    refine (conj _ (conj _ _)).
    - exact (Hall ct (ex_intro _ ci Hct)).
    - exact (Hall rt (ex_intro _ ri Hrt)).
    - intros x b Hx. exact (Hall b (ex_intro _ x Hx)).
  Qed.

  Lemma lcall_fresh_of_env :
    forall G env ct rt st0 stl,
      env_injective env ->
      (exists ci, Env.find ci env = Some ct) ->
      (exists ri, Env.find ri env = Some rt) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (st0 <= k)%positive /\ (k < stl)%positive) ->
      secglobal_scoped G -> secglobal_scope_bounded_above G st0 ->
      lcall_fresh_prop G env ct rt st0.
  Proof.
    intros G env ct rt st0 stl Hinj (ci & Hct) (ri & Hrt) Hrng HscS HbdS.
    set (D := env_images env).
    assert (Hdeclall : forall y, In y D -> name_above st0 y).
    { intros y Hy. unfold D, env_images in Hy.
      apply in_map_iff in Hy as ((x & b) & Hxb & Hin). cbn in Hxb. subst b.
      apply Env.elements_complete in Hin.
      destruct (Hrng x y Hin) as (k & Hk & Hlo & _). exists k.
      split; assumption. }
    assert (HdkA : decl_ok env ct rt D).
    { split; [|split].
      - exact (env_images_spec env _ _ Hct).
      - exact (env_images_spec env _ _ Hrt).
      - exact (fun x b H => env_images_spec env x b H). }
    assert (HclkA : clk_scoped env ct D).
    { intros ck ckty Hck.
      eapply clk_scoped_of_env;
        [exact (env_images_spec env _ _ Hct)
        |exact (fun x b H => env_images_spec env x b H)|exact Hck]. }
    exact (lcall_fresh_prop_holds G env ct rt D st0 HdkA HclkA HscS Hdeclall
             HbdS Hinj).
  Qed.

  Lemma aug_closed :
    forall env ct (vars ins : list (ident * clock)) (nd : node) bck sub es
           argts ckty,
      env_injective env -> NoDupMembers vars ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> ct) ->
      (forall v ckv, In (v, ckv) ins -> In (v, ckv) vars) ->
      (forall x ck, In (x, ck) vars -> exists b, Env.find x env = Some b) ->
      Forall2 (WellInstantiated bck sub) (idck nd.(n_in)) (nclocksof es) ->
      Forall (fun e => Forall (wc_clock vars) (clockof e)) es ->
      Forall2 (lst_clock_closed env ct vars []) argts (clocksof es) ->
      List.length argts = List.length (nclocksof es) ->
      assign_clk_type env ct bck = Some ckty ->
      Forall (CALLS.st_closed_mod env ct ins [] ckty)
        (CALLS.augment_actuals env sub (idck nd.(n_in)) argts).
  Proof.
    intros env ct vars ins nd bck sub es argts ckty Hinj Hnd Hbase Hins Hkeys
      Hwi Hargcl Hlcc Hlen Hbck.
    rewrite Forall_forall. intros w Hw.
    apply In_nth_error in Hw as (i & Hi).
    assert (Hl2 : List.length (idck nd.(n_in)) = List.length (nclocksof es))
      by exact (Forall2_length _ _ _ Hwi).
    assert (Hl3 : List.length (idck nd.(n_in)) = List.length argts)
      by (rewrite Hl2; symmetry; exact Hlen).
    assert (Hlt : (i < List.length (idck nd.(n_in)))%nat).
    { unfold CALLS.augment_actuals in Hi. apply nth_error_lt_inv in Hi.
      rewrite map_length, combine_length in Hi. lia. }
    destruct (nth_error_lt _ _ Hlt) as ((x & ckf) & Hxi).
    assert (Hlta : (i < List.length argts)%nat) by lia.
    destruct (nth_error_lt _ _ Hlta) as (t & Hti).
    rewrite (CALLS.augment_actuals_nth env sub (idck nd.(n_in)) argts i x ckf t
               Hxi Hti) in Hi.
    inversion Hi; subst w. clear Hi.
    assert (Hltn : (i < List.length (nclocksof es))%nat) by lia.
    destruct (nth_error_lt _ _ Hltn) as (nck & Hni).
    destruct (Forall2_nth_error _ (idck nd.(n_in)) (nclocksof es) i (x, ckf)
                nck Hwi Hxi Hni) as (_ & Hinst).
    cbn [fst snd] in Hinst.
    assert (Hnck : nth_error (clocksof es) i = Some (fst nck)).
    { rewrite clocksof_nclocksof.
      exact (map_nth_error stripname i (nclocksof es) Hni). }
    pose proof (Forall2_nth_error _ argts (clocksof es) i t (fst nck) Hlcc Hti
                  Hnck) as Hlt1.
    assert (Hwcj : wc_clock vars (fst nck)).
    { pose proof (nth_error_In _ _ Hnck) as Hin. unfold clocksof in Hin.
      apply in_flat_map in Hin as (e & He & Hce).
      rewrite Forall_forall in Hargcl.
      pose proof (Hargcl e He) as Hw. rewrite Forall_forall in Hw.
      exact (Hw _ Hce). }
    destruct (assign_clk_type_total_of_vars env ct (fst nck)
                (fun x0 Hx0 =>
                   match clock_vars_wc vars (fst nck) Hwcj x0 Hx0 with
                   | ex_intro ckx Hin => Hkeys x0 ckx Hin
                   end)) as (cktj & Hcktj).
    assert (Hincl : incl cktj (merge ckty
                                 (CALLS.clock_actuals env sub ckf))).
    { eapply assign_clk_type_instck_incl;
        [exact Hinst|exact Hbck|exact Hcktj|].
      intros x0 x' z Hx0 Hs Hz.
      exact (CALLS.clock_actuals_intro env sub ckf x0 x' z Hx0 Hs Hz). }
    assert (Hup : forall z, In z cktj ->
                    In z (merge ckty (merge (fst t)
                                        (CALLS.clock_actuals env sub ckf)))).
    { intros z Hz. apply Hincl in Hz. apply in_merge_inv in Hz as [Hz|Hz].
      - apply in_merge_left. exact Hz.
      - apply in_merge_right. apply in_merge_right. exact Hz. }
    intros v b ckv ckvty Hf _ Hb Hin Hck z Hz. cbn [fst] in Hb |- *.
    apply in_merge_inv in Hb as [Hb|Hb].
    - pose proof (Hlt1 cktj b Hcktj (fun H => H) Hb v ckv ckvty Hf
                    (Hins _ _ Hin) Hck z Hz) as Hz'.
      apply in_merge_inv in Hz' as [Hz'|Hz'].
      + exact (Hup z Hz').
      + apply in_merge_right. apply in_merge_left. exact Hz'.
    - unfold CALLS.clock_actuals in Hb.
      destruct (CALLS.sub_names_inv env sub (clock_vars ckf) b Hb)
        as (x0 & u & Hx0 & Hs & Hu).
      pose proof (instck_clock_vars bck sub ckf (fst nck) x0 u Hinst Hx0 Hs)
        as Hucj.
      pose proof (assign_clk_type_vars_in env ct (fst nck) cktj u b Hcktj Hucj
                    Hu) as Hbj.
      pose proof (assign_clk_type_clock_closed env ct vars Hinj Hnd Hbase
                    (fst nck) cktj Hwcj Hcktj v b ckv ckvty Hf Hbj
                    (Hins _ _ Hin) Hck z Hz) as Hzj.
      exact (Hup z Hzj).
  Qed.

  Lemma call_eq_icl :
    forall (G : secglobal) env ct rt (P : global)
           (vars ins : list (ident * clock)) stN lo stl stx
           (xs : list ident) f es (ro : option exp) anns (rstty : LST)
           cs st st',
      lsig_inv stN lo G stx ->
      CALLS.sig_inputs_ok G P ->
      env_injective env -> NoDupMembers vars ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> ct) ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> rt) ->
      (forall v ckv, In (v, ckv) ins -> In (v, ckv) vars) ->
      (forall x ck, In (x, ck) vars -> exists b, Env.find x env = Some b) ->
      wc_global P -> wc_env vars ->
      wl_exp P (Eapp f es ro anns) -> wc_exp P vars (Eapp f es ro anns) ->
      Forall normalized_lexp es ->
      Forall (fun e => Forall (wc_clock vars) (clockof e)) es ->
      lcall_fresh_prop G env ct rt lo -> lcall_rst_shape G env ct rt lo rstty ->
      sec_le lo st ->
      (exists ci, Env.find ci env = Some ct) ->
      (exists ri, Env.find ri env = Some rt) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (lo <= k)%positive /\ (k < stl)%positive) ->
      snd rstty = [] ->
      (forall ckty, CALLS.st_closed_mod env ct ins [] ckty (fst rstty)) ->
      NoDup xs ->
      (forall x, In x xs ->
                 (exists ck, In (x, ck) vars) /\ forall ck, ~ In (x, ck) ins) ->
      generate_lcall_constraint G env ct rt xs f es rstty st = OK (cs, st') ->
      Forall (icl env ct ins) cs /\ Forall (ntg (zset env ct ins)) cs.
  Proof.
    intros G env ct rt P vars ins stN lo stl stx xs f es ro anns rstty cs st st'
      Hinv Hsigin Hinj Hnd Hbase Hrst Hins Hkeys Hg Hwenv Hwl Hwc Hesn Hargcl
      Hlf Hshape Hlo Hci Hri Hrng Hsr Hrstcl Hndx Hxs Hgen.
    destruct (generate_lcall_constraint_inv G env ct rt xs f es rstty cs st st'
                Hgen)
      as (sg & ckty & argts & outs & sti & cs0 & Hfs & Hckty & Hargs & Houts
          & Hgc & Hcs).
    assert (Hesc : Forall normalized_cexp es).
    { eapply Forall_impl; [|exact Hesn]. intros e He.
      exact (normalized_lexp_cexp e He). }
    destruct (assign_lexps_normalized_pure G env ct rt es Hesc argts st sti
                Hargs) as (Hsti & Hlarg & Hcar & _). subst sti.
    assert (Hcs0 : cs = cs0).
    { rewrite Hcs, Hcar, Hsr.
      change (cmerge [] []) with (@nil SymTypes.constraint).
      apply cmerge_nil. }
    clear Hcs. subst cs.
    destruct Hinv as (Hgood & Hsc & Hndall & Hroot & Hbd & Hle).
    assert (Hcallsite : exists (nd : node) bck sub,
              find_node f P = Some nd
              /\ Forall2 (WellInstantiated bck sub) (idck nd.(n_in))
                   (nclocksof es)
              /\ Forall2 (WellInstantiated bck sub) (idck nd.(n_out))
                   (List.map snd anns))
      by (inversion Hwc; repeat esplit; eauto).
    destruct Hcallsite as (nd & bck & sub & Hfn & Hwi & Hwo).
    assert (Hwcin : wc_env (idck nd.(n_in))).
    { destruct (wc_find_node P f nd Hg Hfn) as (G' & (Wcin & _)). exact Wcin. }
    pose proof (wc_exp_Eapp_base_clock P nd f es bck sub Hg Hfn Hwi) as Hbck.
    pose proof Hckty as Hckty0.
    rewrite Hbck in Hckty.
    assert (Hbckin : In bck (List.map stripname (nclocksof es))).
    { eapply WellInstantiated_bck; [exact Hwcin| |exact Hwi].
      unfold idck. rewrite map_length. exact (n_ingt0 nd). }
    assert (Hwcbck : wc_clock vars bck).
    { rewrite <- clocksof_nclocksof in Hbckin. unfold clocksof in Hbckin.
      apply in_flat_map in Hbckin as (e & He & Hce).
      rewrite Forall_forall in Hargcl.
      pose proof (Hargcl e He) as Hw. rewrite Forall_forall in Hw.
      exact (Hw _ Hce). }
    assert (Hwces : Forall (wc_exp P vars) es)
      by exact (wc_Eapp_inv' P vars f es ro anns Hwc).
    assert (Hwles : Forall (wl_exp P) es) by (inversion Hwl; assumption).
    assert (Hnamed : Forall2 (fun t nck => forall w g,
                                 snd nck = Some w -> ~ (fun _ : ident => False) w ->
                                 Env.find w env = Some g -> In g (fst t))
                       argts (nclocksof es)).
    { eapply (assign_lexps_named_covered (fun _ : ident => False) P G env ct
                rt vars es Hwles Hwces); [|exact Hargs].
      intros e f' es' ro' anns' He Heq w Hw. exfalso.
      rewrite Forall_forall in Hesn.
      exact (normalized_lexp_not_Eapp e f' es' ro' anns' (Hesn e He) Heq). }
    destruct (Hlf xs f es rstty st sg ckty argts outs st cs0 st' Hndx Hshape
                Hlo Hfs Hckty0 Hargs Houts Hgc) as (Hfr & _).
    assert (Hfenv : CALLS.sig_scope_fresh_for_env env ct rt sg)
      by exact (scope_fresh_for_env_of env ct rt lo stl sg Hci Hri Hrng
                  (Hbd f sg Hfs)).
    pose proof (CALLS.mmap_find_env_Forall2 env xs outs st st Houts)
      as Hout_env.
    assert (Hlcc : Forall2 (lst_clock_closed env ct vars []) argts
                     (clocksof es)).
    { refine (assign_lexps_closed_of G env ct rt P vars es _ Hwces
                (proj2 (Forall_forall _ _)
                   (fun e He => named_ok_normalized_lexp vars e
                                  (proj1 (Forall_forall _ _) Hesn e He)))
                argts st st [] _ Hargs).
      - rewrite Forall_forall. intros e _.
        exact (assign_lexp_type_clock_closed G env ct rt P vars Hinj Hnd e).
      - rewrite minted_refl. intros z []. }
    assert (Hlarg' : List.length argts = List.length (nclocksof es))
      by exact (Forall2_length _ _ _ Hnamed).
    assert (Hckcl : CALLS.st_closed_mod env ct ins [] ckty ckty).
    { intros v b ckv ckvty Hf _ Hb Hin Hck z Hz.
      apply in_merge_left.
      exact (assign_clk_type_clock_closed env ct vars Hinj Hnd Hbase bck ckty
               Hwcbck Hckty v b ckv ckvty Hf Hb (Hins _ _ Hin) Hck z Hz). }
    assert (Houtcl : Forall (fun v => CALLS.st_closed_mod env ct ins [] ckty [v])
                       outs).
    { rewrite Forall_forall. intros o Ho v b ckv ckvty Hf _ Hb Hin Hck.
      exfalso. destruct Hb as [Hb|[]]. subst b.
      destruct (Forall2_in_right _ xs outs o Hout_env Ho) as (x & Hx & Hxo).
      assert (v = x) as ->
          by exact (Hinj v x o o Hf Hxo Logic.eq_refl).
      exact (proj2 (Hxs x Hx) ckv Hin). }
    pose proof (CALLS.generate_constraints_icl G env ct rt ins
                  (fun _ : ident => False) P f nd sg es bck sub argts ckty
                  (fst rstty) outs cs0 st st' Hsigin Hfn Hfs (Hsc f sg Hfs)
                  Hfenv (Hndall f sg Hfs) (proj1 (Hroot f sg Hfs)) Hwcin Hwi
                  Hnamed (fun i x ck x' u _ _ _ H => H) Hfr
                  (aug_closed env ct vars ins nd bck sub es argts ckty Hinj Hnd
                     Hbase Hins Hkeys Hwi Hargcl Hlcc Hlarg' Hckty)
                  Hckcl (Hrstcl ckty) Houtcl Hgc) as Hcl.
    split.
    - exact (icl_of_closed_mod env ct ins cs0 Hcl).
    - rewrite Forall_forall. intros c Hc t Ht Hz.
      pose proof (CALLS.generate_constraints_targets sg _ _ _ _ _ _ _ Hgc)
        as Htg.
      assert (Hs : In (snd c) (List.map snd cs0))
        by (apply in_map_iff; exists c; split; [reflexivity|exact Hc]).
      rewrite Htg in Hs. apply in_map_iff in Hs as (o & Heq & Ho).
      rewrite <- Heq in Ht. destruct Ht as [Ht|[]]. subst o.
      destruct (Forall2_in_right _ xs outs t Hout_env Ho) as (x & Hx & Hxo).
      destruct (Hxs x Hx) as ((ckx & Hxv) & Hnin).
      destruct Hz as [Hz|(y & cky & Hyin & Hy)].
      + exact (Hbase x ckx t Hxv Hxo Hz).
      + assert (y = x) as Hyx by exact (Hinj y x t t Hy Hxo Logic.eq_refl).
        subst y. exact (Hnin cky Hyin).
  Qed.

  Lemma gen_leqn_ldef :
    forall G env bt rt cenv x e,
      (forall f es ro a, e <> Eapp f es ro a) ->
      generate_leqn_constraint G env bt rt cenv ([x], [e])
      = generate_ldef_constraint G env bt rt cenv x e.
  Proof.
    intros G env bt rt cenv x e He.
    destruct e as [c|x0 a|op e1 a|op e1 e2 a|e0s es a|e0s es a|es x0 b a
                  |x0 ets efs a|e0 ets efs a|f es ro a]; try reflexivity.
    exfalso. exact (He f es ro a Logic.eq_refl).
  Qed.

  Lemma normalized_cexp_not_Eapp :
    forall e f es ro anns, normalized_cexp e -> e <> Eapp f es ro anns.
  Proof.
    intros e f es ro anns H. inversion H; try discriminate.
    subst. eapply normalized_lexp_not_Eapp; eauto.
  Qed.

  Lemma reset_closed :
    forall (G : secglobal) env ct rt (P : global)
           (vars ins : list (ident * clock)) e1 t1 a1 rck st,
      env_injective env -> NoDupMembers vars ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> ct) ->
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> rt) ->
      (forall v ckv, In (v, ckv) ins -> In (v, ckv) vars) ->
      wc_global P -> wc_env vars ->
      wc_exp P vars e1 -> normalized_lexp e1 ->
      assign_lexp_type G env ct rt e1 st = OK (t1, st) ->
      single t1 st = OK (a1, st) ->
      assign_clk_type env ct (hd Cbase (clockof e1)) = Some rck ->
      snd (ljoin (lvar rt) (ljoin a1 (rck, []))) = []
      /\ forall ckty,
           CALLS.st_closed_mod env ct ins [] ckty
             (fst (ljoin (lvar rt) (ljoin a1 (rck, [])))).
  Proof.
    intros G env ct rt P vars ins e1 t1 a1 rck st Hinj Hnd Hbase Hrst Hins Hg
      Hwenv Hwc Hn Hrun Hsingle Hrck.
    destruct (assign_lexp_normalized_lexp_pure G env ct rt e1 Hn t1 st st Hrun)
      as (_ & Hl & Hc & _).
    apply single_inv in Hsingle as (-> & _).
    rewrite carried_single in Hc.
    pose proof (wc_reset_clocks P vars e1 Hg Hwenv Hwc Hn) as Hwcl.
    pose proof (assign_lexp_type_clock_closed G env ct rt P vars Hinj Hnd e1 Hwc
                  (named_ok_normalized_lexp vars e1 Hn)
                  [a1] st st [] ltac:(rewrite minted_refl; intros z [])
                  Hrun) as Hlcc.
    destruct (clockof e1) as [|ckr rest] eqn:Hce; [inversion Hlcc|].
    inversion Hlcc as [|t0 c0 ts0 cs0 Hl1 Hl2]; subst.
    inversion Hl2; subst rest.
    cbn [hd] in Hrck.
    inversion Hwcl as [|c1 l1 Hwckr _]; subst.
    split.
    - rewrite !snd_ljoin, Hc. reflexivity.
    - intros ckty v b ckv ckvty Hf _ Hb Hin Hck z Hz.
      rewrite !fst_ljoin, fst_lvar in Hb |- *. cbn [fst] in Hb |- *.
      apply in_merge_right.
      apply in_merge_inv in Hb as [Hb|Hb].
      + exfalso. destruct Hb as [Hb|[]]. subst b.
        exact (Hrst v ckv rt (Hins _ _ Hin) Hf Logic.eq_refl).
      + apply in_merge_inv in Hb as [Hb|Hb].
        * pose proof (Hl1 rck b Hrck (fun H => H) Hb v ckv ckvty Hf
                        (Hins _ _ Hin) Hck z Hz) as Hz'.
          apply in_merge_right.
          apply in_merge_inv in Hz' as [Hz'|Hz'].
          -- apply in_merge_right. exact Hz'.
          -- apply in_merge_left. exact Hz'.
        * apply in_merge_right. apply in_merge_right.
          exact (assign_clk_type_clock_closed env ct vars Hinj Hnd Hbase ckr
                   rck Hwckr Hrck v b ckv ckvty Hf Hb (Hins _ _ Hin) Hck z Hz).
  Qed.

  Lemma wc_eq_single :
    forall P vars x e,
      wc_equation P vars ([x], [e]) ->
      exists ck, clockof e = [ck] /\ In (x, ck) vars /\ wc_exp P vars e.
  Proof.
    intros P vars x e (Hwe & _ & Hin).
    unfold clocksof in Hin. cbn [flat_map] in Hin. rewrite app_nil_r in Hin.
    remember (clockof e) as l eqn:Hl.
    inversion Hin as [|x' ck l0 l1 Hxck Hrest Hx Hl0]; subst.
    inversion Hrest; subst.
    exists ck. split; [reflexivity|]. split; [exact Hxck|exact (Forall_inv Hwe)].
  Qed.

  Lemma rst_plain_closed :
    forall env ct rt (vars ins : list (ident * clock)),
      (forall v ckv b, In (v, ckv) vars -> Env.find v env = Some b -> b <> rt) ->
      (forall v ckv, In (v, ckv) ins -> In (v, ckv) vars) ->
      forall ckty,
        CALLS.st_closed_mod env ct ins [] ckty (fst (lvar rt)).
  Proof.
    intros env ct rt vars ins Hrst Hins ckty v b ckv ckvty Hf _ Hb Hin Hck z Hz.
    rewrite fst_lvar in Hb. destruct Hb as [<-|[]]. exfalso.
    exact (Hrst v ckv rt (Hins _ _ Hin) Hf Logic.eq_refl).
  Qed.

  Lemma leqn_icl :
    forall (G : secglobal) env ct rt (n : node) (P Q : global) stN lo stl stx
           (eq : equation) cs st st',
      lsig_inv stN lo G stx ->
      CALLS.sig_inputs_ok G P ->
      env_injective env ->
      NoDupMembers (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      (forall v ckv b, In (v, ckv) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                       Env.find v env = Some b -> b <> ct) ->
      (forall v ckv b, In (v, ckv) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                       Env.find v env = Some b -> b <> rt) ->
      (forall x ck, In (x, ck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                    exists b, Env.find x env = Some b) ->
      wc_global P -> wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      unnested_equation Q eq -> wl_equation P eq ->
      wc_equation P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) eq ->
      lcall_fresh_prop G env ct rt lo -> sec_le lo st ->
      (exists ci, Env.find ci env = Some ct) ->
      (exists ri, Env.find ri env = Some rt) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (lo <= k)%positive /\ (k < stl)%positive) ->
      NoDup (fst eq) ->
      (forall x, In x (fst eq) ->
                 (exists ck, In (x, ck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
                 /\ forall ck, ~ In (x, ck) (idck n.(n_in))) ->
      generate_leqn_constraint G env ct rt (lnode_clock_env n) eq st
        = OK (cs, st') ->
      Forall (icl env ct (idck n.(n_in))) cs
      /\ Forall (ntg (zset env ct (idck n.(n_in)))) cs.
  Proof.
    intros G env ct rt n P Q stN lo stl stx eq cs st st' Hinv Hsigin Hinj Hnd
      Hbase Hrst Hkeys Hg Hwenv Hun Hwl Hwc Hlf Hlo Hci Hri Hrng Hndx Hxs Hgen.
    set (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) in *.
    set (ins := idck n.(n_in)) in *.
    assert (Hins : forall v ckv, In (v, ckv) ins -> In (v, ckv) vars).
    { intros v ckv H. unfold ins, vars, idck in *.
      apply in_map_iff in H as (q & Hq & Hin). apply in_map_iff.
      exists q. split; [exact Hq|]. apply in_or_app. left. exact Hin. }
    assert (Hfc : forall x ck, In (x, ck) vars ->
                   find_clock (lnode_clock_env n) x = OK ck).
    { intros x ck H. unfold vars, idck in H.
      apply in_map_iff in H as ((x' & tc) & Hq & Hin).
      inversion Hq; subst x' ck. exact (lnode_clock_env_find n x tc Hin). }
    assert (Hbz : forall x ckx b, In (x, ckx) vars ->
                    (forall ck, ~ In (x, ck) ins) ->
                    Env.find x env = Some b -> ~ zset env ct ins b).
    { intros x ckx b Hxv Hnin Hf [Hz|(y & cky & Hyin & Hy)].
      - exact (Hbase x ckx b Hxv Hf Hz).
      - assert (y = x) as Hyx by exact (Hinj y x b b Hy Hf Logic.eq_refl).
        subst y. exact (Hnin cky Hyin). }
    destruct eq as (xs, es). cbn [fst] in Hndx, Hxs.
    inversion Hun as [xs0 f0 n0 es0 lann0 Hn Hfn Hk
                     | xs0 f0 n0 es0 x0 ty0 cl0 lann0 Hn Hfn Hk
                     | x0 e0 e1 ann0 H0 H1 | x0 e0 e1 ann0 H0 H1 | x0 e0 Hc];
      subst.
    - (** a call without reset *)
      destruct Hwl as (Hwle & _). destruct Hwc as (Hwce & _ & _).
      destruct xs as [|x xs'].
      + cbn in Hgen. unfold SC.ret in Hgen. inversion Hgen; subst.
        split; constructor.
      + rewrite gen_leqn_Eapp in Hgen.
        refine (call_eq_icl G env ct rt P vars ins stN lo stl stx (x :: xs') f0
                  es0 None lann0 (lvar rt) cs st st' Hinv Hsigin Hinj Hnd Hbase
                  Hrst Hins Hkeys Hg Hwenv (Forall_inv Hwle) (Forall_inv Hwce)
                  Hn _ Hlf (or_introl Logic.eq_refl) Hlo Hci Hri Hrng
                  (snd_lvar rt) (rst_plain_closed env ct rt vars ins Hrst Hins)
                  Hndx Hxs Hgen).
        exact (wc_args_clocks P vars es0 Hg Hwenv
                 (wc_Eapp_inv' P vars f0 es0 None lann0 (Forall_inv Hwce)) Hn).
    - (** a call with a reset variable *)
      destruct Hwl as (Hwle & _). destruct Hwc as (Hwce & _ & _).
      destruct xs as [|x xs'].
      + cbn in Hgen. unfold SC.ret in Hgen. inversion Hgen; subst.
        split; constructor.
      + rewrite gen_leqn_Eapp_someresetel in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s2 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (rck & s3 & Hrck & Hgen).
        assert (Hnev : normalized_lexp (Evar x0 (ty0, cl0)))
          by exact (unnested_Evar x0 ty0 cl0).
        destruct (assign_lexp_normalized_lexp_pure G env ct rt _ Hnev t1 st s1
                    Ht1) as (? & _ & _ & _); subst s1.
        pose proof Ha1 as Ha1c.
        apply single_inv in Ha1c as (Ht1eq & Hs2). subst s2.
        apply option_to_sec_inv in Hrck as (Hrck & Hs3). subst s3.
        destruct (reset_closed G env ct rt P vars ins (Evar x0 (ty0, cl0)) t1
                    a1 rck st Hinj Hnd Hbase Hrst Hins Hg Hwenv
                    (wc_reset_inv P vars f0 es0 _ lann0 (Forall_inv Hwce)) Hnev
                    Ht1 Ha1 Hrck) as (Hsr & Hrstcl).
        refine (call_eq_icl G env ct rt P vars ins stN lo stl stx (x :: xs') f0
                  es0 (Some (Evar x0 (ty0, cl0))) lann0
                  (ljoin (lvar rt) (ljoin a1 (rck, []))) cs st st' Hinv Hsigin
                  Hinj Hnd Hbase Hrst Hins Hkeys Hg Hwenv (Forall_inv Hwle)
                  (Forall_inv Hwce) Hn
                  (wc_args_clocks P vars es0 Hg Hwenv
                     (wc_Eapp_inv' P vars f0 es0 _ lann0 (Forall_inv Hwce)) Hn)
                  Hlf
                  (or_intror (ex_intro _ (Evar x0 (ty0, cl0))
                    (ex_intro _ t1 (ex_intro _ a1 (ex_intro _ rck
                      (ex_intro _ st (ex_intro _ st
                        (conj Hlo (conj Ht1 (conj Ha1 (conj Hrck
                           Logic.eq_refl)))))))))))
                  Hlo Hci Hri Hrng Hsr Hrstcl Hndx Hxs Hgen).
    - (** a delayed definition *)
      destruct (wc_eq_single P vars x0 (Efby [e0] [e1] [ann0]) Hwc)
        as (ckx & Hce & Hxck & Hwcexp).
      rewrite gen_leqn_ldef in Hgen by (intros f es ro a H; discriminate H).
      refine (ldef_ok G env ct rt (lnode_clock_env n) P vars ins
                (zset env ct ins) x0 _ ckx cs st st' Hinj Hnd Hbase Hrst Hins
                Hg Hwenv Hwcexp _ Hce (Hfc x0 ckx Hxck) Hxck _ Hgen).
      + right. exists e0, e1, ann0. split; [left; reflexivity|exact (conj H0 H1)].
      + intros b Hb. exact (Hbz x0 ckx b Hxck
                              (proj2 (Hxs x0 (or_introl Logic.eq_refl))) Hb).
    - (** [->] *)
      destruct (wc_eq_single P vars x0 (Earrow [e0] [e1] [ann0]) Hwc)
        as (ckx & Hce & Hxck & Hwcexp).
      rewrite gen_leqn_ldef in Hgen by (intros f es ro a H; discriminate H).
      refine (ldef_ok G env ct rt (lnode_clock_env n) P vars ins
                (zset env ct ins) x0 _ ckx cs st st' Hinj Hnd Hbase Hrst Hins
                Hg Hwenv Hwcexp _ Hce (Hfc x0 ckx Hxck) Hxck _ Hgen).
      + right. exists e0, e1, ann0. split; [right; reflexivity|exact (conj H0 H1)].
      + intros b Hb. exact (Hbz x0 ckx b Hxck
                              (proj2 (Hxs x0 (or_introl Logic.eq_refl))) Hb).
    - (** control expressions *)
      destruct (wc_eq_single P vars x0 e0 Hwc)
        as (ckx & Hce & Hxck & Hwcexp).
      rewrite gen_leqn_ldef in Hgen
        by (intros f es ro a H; exact (normalized_cexp_not_Eapp e0 f es ro a Hc H)).
      refine (ldef_ok G env ct rt (lnode_clock_env n) P vars ins
                (zset env ct ins) x0 e0 ckx cs st st' Hinj Hnd Hbase Hrst Hins
                Hg Hwenv Hwcexp _ Hce (Hfc x0 ckx Hxck) Hxck _ Hgen).
      + left. exact Hc.
      + intros b Hb. exact (Hbz x0 ckx b Hxck
                              (proj2 (Hxs x0 (or_introl Logic.eq_refl))) Hb).
  Qed.

  Lemma leqns_icl :
    forall (G : secglobal) env ct rt (n : node) (P Q : global) stN lo stl stx
           (eqs : list equation) cs st st',
      lsig_inv stN lo G stx ->
      CALLS.sig_inputs_ok G P ->
      env_injective env ->
      NoDupMembers (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      (forall v ckv b, In (v, ckv) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                       Env.find v env = Some b -> b <> ct) ->
      (forall v ckv b, In (v, ckv) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                       Env.find v env = Some b -> b <> rt) ->
      (forall x ck, In (x, ck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                    exists b, Env.find x env = Some b) ->
      wc_global P -> wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      Forall (unnested_equation Q) eqs -> Forall (wl_equation P) eqs ->
      Forall (wc_equation P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) eqs ->
      lcall_fresh_prop G env ct rt lo -> sec_le lo st ->
      (exists ci, Env.find ci env = Some ct) ->
      (exists ri, Env.find ri env = Some rt) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (lo <= k)%positive /\ (k < stl)%positive) ->
      NoDup (vars_defined eqs) ->
      (forall x, In x (vars_defined eqs) ->
                 (exists ck, In (x, ck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
                 /\ forall ck, ~ In (x, ck) (idck n.(n_in))) ->
      generate_leqns_constraints G env ct rt (lnode_clock_env n) eqs st
        = OK (cs, st') ->
      Forall (icl env ct (idck n.(n_in))) cs
      /\ Forall (ntg (zset env ct (idck n.(n_in)))) cs.
  Proof.
    intros G env ct rt n P Q stN lo stl stx eqs.
    induction eqs as [|eq eqs IH]; intros cs st st' Hinv Hsigin Hinj Hnd Hbase
      Hrst Hkeys Hg Hwenv Hun Hwl Hwc Hlf Hlo Hci Hri Hrng Hndx Hxs Hgen.
    - apply generate_leqns_constraints_nil in Hgen as (-> & _).
      split; constructor.
    - rewrite generate_leqns_constraints_cons in Hgen.
      apply sec_bind_inv in Hgen as (c & s1 & Hc & Hgen).
      apply sec_bind_inv in Hgen as (cs2 & s2 & Hcs2 & Hret).
      unfold SC.ret in Hret. destruct (OK_pair_inv _ _ _ _ Hret) as (Heq & _).
      subst cs.
      inversion Hun as [|? ? Hun1 Hun2]; subst.
      inversion Hwl as [|? ? Hwl1 Hwl2]; subst.
      inversion Hwc as [|? ? Hwc1 Hwc2]; subst.
      unfold vars_defined in Hndx, Hxs. cbn [flat_map] in Hndx, Hxs.
      assert (Hnd1 : NoDup (fst eq)) by (eapply NoDup_app_l; exact Hndx).
      assert (Hnd2 : NoDup (flat_map fst eqs))
        by (eapply NoDup_app_r; exact Hndx).
      destruct (leqn_icl G env ct rt n P Q stN lo stl stx eq c st s1 Hinv
                  Hsigin Hinj Hnd Hbase Hrst Hkeys Hg Hwenv Hun1 Hwl1 Hwc1 Hlf
                  Hlo Hci Hri Hrng Hnd1
                  (fun x Hx => Hxs x (in_or_app _ _ _ (or_introl Hx))) Hc)
        as (A1 & B1).
      assert (Hlo1 : sec_le lo s1).
      { eapply Pos.le_trans; [exact Hlo|].
        eapply generate_leqn_constraint_sec_le; exact Hc. }
      destruct (IH cs2 s1 s2 Hinv Hsigin Hinj Hnd Hbase Hrst Hkeys Hg Hwenv Hun2
                  Hwl2 Hwc2 Hlf Hlo1 Hci Hri Hrng Hnd2
                  (fun x Hx => Hxs x (in_or_app _ _ _ (or_intror Hx))) Hcs2)
        as (A2 & B2).
      split; apply Forall_app; split; assumption.
  Qed.


  Lemma get_mappings_from_node_nth :
    forall {A : Type} (xs : list (ident * A)) env inp,
      get_mappings_from_node xs env = Some inp ->
      List.length inp = List.length xs
      /\ forall i x a y,
           nth_error xs i = Some (x, a) -> nth_error inp i = Some y ->
           Env.find x env = Some y.
  Proof.
    intros A xs env. induction xs as [|[x0 a0] xs IH]; intros inp H.
    - cbn in H. inversion H; subst. split; [reflexivity|].
      intros i x a y Hx; destruct i; discriminate.
    - cbn in H.
      destruct (Env.find x0 env) as [t|] eqn:Ht; [|discriminate].
      destruct (get_mappings_from_node xs env) as [ts|] eqn:Hts;
        [|discriminate].
      inversion H; subst. destruct (IH ts Logic.eq_refl) as (Hl & Hn).
      split; [simpl; f_equal; exact Hl|].
      intros i x a y Hx Hy. destruct i as [|i]; simpl in Hx, Hy.
      + inversion Hx; inversion Hy; subst. exact Ht.
      + exact (Hn i x a y Hx Hy).
  Qed.

  Lemma defined_decl_not_input :
    forall (n : node) x,
      In x (vars_defined n.(n_eqs)) ->
      (exists ck, In (x, ck) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
      /\ forall ck, ~ In (x, ck) (idck n.(n_in)).
  Proof.
    intros n x Hx.
    assert (Hm : In x (List.map fst (n.(n_vars) ++ n.(n_out))))
      by (eapply Permutation_in; [exact (n_defd n)|exact Hx]).
    split.
    - rewrite map_app in Hm. apply in_app_or in Hm as [Hm|Hm].
      + apply in_map_iff in Hm as ((x' & tc) & Hq & Hin). cbn in Hq. subst x'.
        exists (snd tc). unfold idck. apply in_map_iff.
        exists (x, tc). split; [reflexivity|].
        apply in_or_app. right. apply in_or_app. left. exact Hin.
      + apply in_map_iff in Hm as ((x' & tc) & Hq & Hin). cbn in Hq. subst x'.
        exists (snd tc). unfold idck. apply in_map_iff.
        exists (x, tc). split; [reflexivity|].
        apply in_or_app. right. apply in_or_app. right. exact Hin.
    - intros ck Hin. unfold idck in Hin.
      apply in_map_iff in Hin as ((x' & tc) & Hq & Hin'). cbn in Hq.
      inversion Hq; subst x'.
      pose proof (n_nodup n) as Hnd. rewrite fst_NoDupMembers in Hnd.
      rewrite !map_app in Hnd.
      assert (Hin1 : In x (List.map fst n.(n_in)))
        by (apply in_map_iff; exists (x, tc); split; [reflexivity|exact Hin']).
      rewrite map_app in Hm. apply in_app_or in Hm as [Hm|Hm].
      + eapply NoDup_app_In; [exact Hnd|exact Hin1|].
        apply in_or_app. left. exact Hm.
      + eapply NoDup_app_In; [exact Hnd|exact Hin1|].
        apply in_or_app. right. apply in_or_app. left. exact Hm.
  Qed.


  Lemma node_sig_inputs :
    forall (G : secglobal) (P Q : global) (n : node) env aux sg st0 st1
           stN lo stl,
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      wl_node P n -> wc_global P -> wc_node P n -> unnested_node Q n ->
      env_injective env ->
      lsig_inv stN lo G st0 -> sec_le lo st0 ->
      CALLS.sig_inputs_ok G P ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      (forall x b, Env.find x env = Some b ->
                   exists k, b = Ids.gensym Ids.sec k
                             /\ (lo <= k)%positive /\ (k < stl)%positive) ->
      (forall ci ri, get_node_aux n.(n_name) aux = Some (ci, ri) ->
         ~ In ci (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
         /\ ~ In ri (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
      (forall x, In x (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
                 exists b, Env.find x env = Some b) ->
      List.length (idck n.(n_in)) = List.length (s_in sg)
      /\ (forall i x ck y,
            nth_error (idck n.(n_in)) i = Some (x, ck) ->
            nth_error (s_in sg) i = Some y -> Env.find x env = Some y)
      /\ CALLS.sig_inputs_clock_closed sg (idck n.(n_in))
           (fun x => Env.find x env).
  Proof.
    intros G P Q n env aux sg st0 st1 stN lo stl Hsig Hwl Hg Hwcn Hun Hinj Hinv
      Hlo Hsigin Hsep Hrng Haux Hbind.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns & Haux' & Hct & Hrt
          & Hinp & Hout & Hloc & Hcns & Hsg).
    subst sg.
    destruct (Haux ci ri Haux') as (Hcind & Hrind).
    destruct (node_wc_clock_facts P n Hwcn) as (Hwenv & _).
    destruct Hwcn as (Hwin & _ & _ & Hweqs).
    destruct (get_mappings_from_node_nth _ env inp Hinp) as (Hlen & Hnth).
    assert (HndN : NoDup (List.map fst n.(n_in)
                          ++ List.map fst n.(n_vars) ++ List.map fst n.(n_out))).
    { pose proof (n_nodup n) as H0. rewrite fst_NoDupMembers in H0.
      rewrite !map_app in H0. rewrite !app_assoc in H0.
      apply NoDup_app_l in H0. rewrite <- !app_assoc in H0. exact H0. }
    assert (Hnd : NoDupMembers (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { rewrite NoDupMembers_idck, fst_NoDupMembers, !map_app. exact HndN. }
    set (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) in *.
    set (ins := idck n.(n_in)) in *.
    assert (HinD : forall v ckv, In (v, ckv) vars ->
                     In v (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { intros v ckv H. unfold vars, idck in H.
      apply in_map_iff in H as ((x' & tc) & Hq & Hin). inversion Hq; subst x'.
      apply in_map_iff. exists (v, tc). split; [reflexivity|exact Hin]. }
    assert (Hins : forall v ckv, In (v, ckv) ins -> In (v, ckv) vars).
    { intros v ckv H. unfold ins, vars, idck in *.
      apply in_map_iff in H as (q & Hq & Hin). apply in_map_iff.
      exists q. split; [exact Hq|]. apply in_or_app. left. exact Hin. }
    assert (Hbase : forall v ckv b, In (v, ckv) vars ->
                      Env.find v env = Some b -> b <> ct).
    { intros v ckv b Hv Hf Heq. subst b.
      assert (v = ci) as -> by exact (Hinj v ci ct ct Hf Hct Logic.eq_refl).
      exact (Hcind (HinD _ _ Hv)). }
    assert (Hrst : forall v ckv b, In (v, ckv) vars ->
                      Env.find v env = Some b -> b <> rt).
    { intros v ckv b Hv Hf Heq. subst b.
      assert (v = ri) as -> by exact (Hinj v ri rt rt Hf Hrt Logic.eq_refl).
      exact (Hrind (HinD _ _ Hv)). }
    assert (Hkeys : forall x ck, In (x, ck) vars ->
                      exists b, Env.find x env = Some b)
      by (intros x ck H; exact (Hbind x (HinD _ _ H))).
    pose proof Hinv as Hinv0.
    destruct Hinv0 as (Hgood & Hsc & Hndsig & Hroot & Hbd & Hle).
    assert (Hlf : lcall_fresh_prop G env ct rt lo)
      by exact (lcall_fresh_of_env G env ct rt lo stl Hinj
                  (ex_intro _ ci Hct) (ex_intro _ ri Hrt) Hrng Hsc Hbd).
    destruct (leqns_icl G env ct rt n P Q stN lo stl st0 n.(n_eqs) cns st0 st1
                Hinv Hsigin Hinj Hnd Hbase Hrst Hkeys Hg Hwenv Hun Hwl Hweqs Hlf
                Hlo (ex_intro _ ci Hct) (ex_intro _ ri Hrt) Hrng
                (NoDup_vars_defined_n_eqs n) (defined_decl_not_input n) Hcns)
      as (A & B).
    destruct (collapse_ok env ct ins (zset env ct ins) cns A B) as (A1 & B1).
    assert (Hds : forall d, In d (locals ++ minted st0 st1) ->
                            ~ zset env ct ins d).
    { intros d Hd Hz. apply in_app_or in Hd as [Hd|Hd].
      - rewrite (get_mappings_from_node_sec_of _ env locals Hloc) in Hd.
        apply sec_of_In_inv in Hd as (y & Hy & Hfy).
        destruct Hz as [Hz|(x & ck & Hxin & Hfx)].
        + subst d.
          assert (y = ci) as -> by exact (Hinj y ci ct ct Hfy Hct Logic.eq_refl).
          apply Hcind. rewrite !map_app. apply in_or_app. right.
          apply in_or_app. left. exact Hy.
        + assert (x = y) as -> by exact (Hinj x y d d Hfx Hfy Logic.eq_refl).
          unfold ins, idck in Hxin. apply in_map_iff in Hxin as ((x' & tc) & Hq & Hin).
          inversion Hq; subst x'.
          eapply NoDup_app_In; [exact HndN| |apply in_or_app; left; exact Hy].
          apply in_map_iff. exists (y, tc). split; [reflexivity|exact Hin].
      - destruct Hz as [Hz|(x & ck & Hxin & Hfx)].
        + subst d. exact (Hsep ci ct Hct Hd).
        + exact (Hsep x d Hfx Hd). }
    destruct (simplify_ok env ct ins (zset env ct ins)
                (HZ_of_ins env ct ins Hwin)
                (locals ++ minted st0 st1) (SymTypes.collapse cns) A1 B1 Hds)
      as (A2 & _).
    refine (conj _ (conj _ _)).
    - cbn [s_in]. unfold ins, idck. rewrite map_length. symmetry. exact Hlen.
    - cbn [s_in]. intros i x ck y Hx Hy.
      unfold ins, idck in Hx. apply nth_error_map_inv in Hx as ((x' & (ty & ck0)) & Hxn & Heq).
      inversion Heq; subst x' ck0. exact (Hnth i x (ty, ck) y Hxn Hy).
    - cbn [s_constraints].
      assert (Hanon0 : anon_images env n = []).
      { pose proof (anon_names_unnested Q n Hun) as H00.
        unfold anon_names in H00. apply map_eq_nil in H00.
        unfold anon_images. rewrite H00. reflexivity. }
      rewrite Hanon0. cbn [app].
      intros c Hc x ck y Hin Hx Hy x' y' Hx' Hy'.
      refine (closed_of_icl env ct ins _ A2 _ c Hc x ck y Hin Hx Hy x' y' Hx' Hy').
      intros x0 ck0 x1 Hin0 Hx1.
      unfold ins in Hin0. pose proof (Hins _ _ Hin0) as Hv.
      unfold wc_env in Hwenv. rewrite Forall_forall in Hwenv.
      pose proof (Hwenv _ Hv) as Hw. cbn [snd] in Hw.
      destruct (clock_vars_wc vars ck0 Hw x1 Hx1) as (ck1 & Hin1).
      exact (Hkeys x1 ck1 Hin1).
  Qed.


  Lemma sig_inputs_step :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall P nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
             accT sgT stT0 stT1,
        RU P nS nM nall ->
        generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
        find_node_env nall.(n_name) envsF = Some env ->
        get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
        (st0 <= stN)%positive ->
        lsig_inv stN st0 accT stT0 ->
        CALLS.sig_inputs_ok accT P ->
        generate_lnode_sig_scoped_env accT nM envsF auxF stT0
          = OK (sgT, stT1) ->
        CALLS.sig_inputs_ok (sgT :: accT) (nS :: P).
  Proof.
    intros all envsF auxF stN Hfull P nS nM nall env r st0 stl accT sgT stT0
      stT1 HRU Hloc Hfind Haux Hst0 HinvT Hj Hs.
    destruct (RU_facts P nS nM nall HRU)
      as (Hn1 & Hn2 & tfS & tfM & tfN).
    destruct tfM as (P2 & HwlM & HwcgM & HwcnM & HsrcM & HdisjM & HsubM).
    destruct HRU as (Hwl & Hpref & Q & Hunt & Hpref1 & HM & HN & Hgp & Hwtn
                     & Hwcn & Hif & Hgq & Hguard).
    subst nM nall.
    set (M := unnest_node P nS Hwl Hpref) in *.
    assert (HwtM : wt_node P M)
      by exact (NTyp.unnest_node_wt P nS Hwl Hpref Hwtn).
    assert (HwcM : wc_node P M)
      by exact (NClo.unnest_node_wc P nS Hwl Hpref Hgp Hwcn).
    assert (HwlMP : wl_node P M) by exact (wt_node_wl_node _ _ HwtM).
    assert (HfindM : find_node_env (n_name M) envsF = Some env) by exact Hfind.
    unfold generate_lnode_sig_scoped_env in Hs. rewrite HfindM in Hs.
    destruct (generate_local_env_for_lnode_facts _ st0 env r stl Hloc)
      as (Hinj & Hrng & Hclk0 & Hrst0).
    pose proof HinvT as HinvT0.
    destruct HinvT0 as (_ & _ & _ & _ & _ & Hle).
    assert (HinN : forall p, In p (n_in M ++ n_vars M ++ n_out M) ->
                    In p (n_in (normfby_node Q PS.empty M Hunt Hpref1)
                          ++ n_vars (normfby_node Q PS.empty M Hunt Hpref1)
                          ++ n_out (normfby_node Q PS.empty M Hunt Hpref1)))
      by exact (normfby_vars_incl Q M Hunt Hpref1).
    destruct (lnode_sig_inv env accT M auxF sgT stT0 stT1 Hs)
      as (ci & ri & ct & rt & inp & out & locals & cns & Haux' & _ & _ & _ & _
          & _ & _ & Hsg).
    assert (Hsgname : s_name sgT = n_name nS) by (rewrite Hsg; reflexivity).
    assert (Hauxn : forall ci0 ri0, get_node_aux (n_name M) auxF = Some (ci0, ri0) ->
                ~ In ci0 (List.map fst (n_in M ++ n_vars M ++ n_out M))
                /\ ~ In ri0 (List.map fst (n_in M ++ n_vars M ++ n_out M))).
    { intros ci0 ri0 Ha. change (n_name M) with
        (n_name (normfby_node Q PS.empty M Hunt Hpref1)) in Ha.
      rewrite Haux in Ha. inversion Ha; subst ci0 ri0. split; intro Hin.
      - exact (lnode_var_not_sec M _ st0 HsubM Hin Hclk0).
      - exact (lnode_var_not_sec M _ (Pos.succ st0) HsubM Hin Hrst0). }
    assert (Hbind : forall x, In x (List.map fst (n_in M ++ n_vars M ++ n_out M)) ->
                    exists b, Env.find x env = Some b).
    { intros x Hx.
      apply (generate_local_env_for_lnode_binds
               (normfby_node Q PS.empty M Hunt Hpref1) st0 env r stl Hloc x).
      right. right.
      apply in_map_iff in Hx as (p & Hpx & Hp).
      apply in_map_iff. exists p. split; [exact Hpx|exact (HinN p Hp)]. }
    destruct (node_sig_inputs accT P Q M env auxF sgT stT0 stT1 stN st0 stl Hs
                HwlMP Hgp HwcM Hunt Hinj HinvT
                (Pos.le_trans _ _ _ Hst0 Hle) Hj
                (fun x b Hb => env_apart_from_minted all envsF auxF stN
                                 (n_name M) env stT0 stT1 Hfull HfindM Hle x b
                                 Hb)
                (fun x b Hb => match Hrng x b Hb with
                               | ex_intro k (conj Hk (conj Hl Hh)) =>
                                 ex_intro _ k (conj Hk (conj Hl Hh))
                               end)
                Hauxn Hbind)
      as (Hlen & Hnth & Hcl).
    unfold CALLS.sig_inputs_ok. intros f n sg Hfn Hfs.
    unfold find_node in Hfn. unfold find_signature in Hfs. simpl in Hfn, Hfs.
    destruct (ident_eqb (n_name nS) f) eqn:Hnf.
    - inversion Hfn; subst n.
      assert (Hsn : ident_eqb (s_name sgT) f = true)
        by (rewrite Hsgname; exact Hnf).
      rewrite Hsn in Hfs. inversion Hfs; subst sg.
      exists (fun x => Env.find x env).
      exact (conj Hlen (conj Hnth Hcl)).
    - assert (Hsn : ident_eqb (s_name sgT) f = false)
        by (rewrite Hsgname; exact Hnf).
      rewrite Hsn in Hfs. exact (Hj f n sg Hfn Hfs).
  Qed.


  Theorem normalization_signatures_preserved :
    forall (G : global) (Hwl : wl_global G)
           (Hpr : Forall (fun n => n_prefixes n = elab_prefs) G)
           (Hunt : unnested_global (unnest_global G Hwl Hpr))
           (Hpref1 : Forall (fun n => n_prefixes n = norm1_prefs)
                       (unnest_global G Hwl Hpr)),
      wc_global G -> wt_global G ->
      forall envsF auxF stN st GS GT GM,
        generate_lnode_scoped_env_st
          (List.rev (normfby_global (unnest_global G Hwl Hpr) Hunt Hpref1))
          = OK (envsF, auxF, stN) ->
        sec_le stN st ->
        generate_all_lsignatures_scoped_env (List.rev G) envsF auxF st = OK GS ->
        generate_all_lsignatures_scoped_env
          (List.rev (unnest_global G Hwl Hpr)) envsF auxF st = OK GT ->
        generate_all_lsignatures_scoped_env
          (List.rev (normfby_global (unnest_global G Hwl Hpr) Hunt Hpref1))
          envsF auxF st = OK GM ->
        call_weakens GS GM /\ sigs_preserved GS GM.
  Proof.
    intros G Hwl Hpr Hunt Hpref1 Hwc Hwt envsF auxF stN st GS GT GM
      Hnaming Hle HgS HgT HgM.
    pose proof (wc_global_source_guard G Hwc) as Hguard.
    set (G1 := unnest_global G Hwl Hpr) in *.
    set (G2 := normfby_global G1 Hunt Hpref1) in *.
    assert (Hwc1 : wc_global G1) by exact (NClo.unnest_global_wc G Hwl Hpr Hwc).
    assert (Hwt1 : wt_global G1) by exact (NTyp.unnest_global_wt G Hwl Hpr Hwt).
    assert (Hnd : NoDup (List.map n_name (List.rev G2))).
    { rewrite List.map_rev.
      apply (Permutation_NoDup (Permutation_rev _)).
      unfold G2. rewrite normfby_global_map_names. unfold G1.
      rewrite unnest_global_map_names. exact (wc_global_names_nodup G Hwc). }
    (** the unnesting leg *)
    destruct (generate_all_lsignatures_weakens_ext_driver
                (List.rev G2) envsF auxF stN st Hnaming RU
                (fun acc P => CALLS.sig_inputs_ok acc P)
                (fun P nS nM nall HR =>
                   match RU_facts P nS nM nall HR with
                   | conj Hn1 (conj Hn2 (conj tfS (conj tfM _))) =>
                     conj Hn1 (conj tfS (conj Hn2 tfM))
                   end)
                (fun P nS nM nall env r st0 stl accT sgT stT0 stT1 HR Hloc Hfind
                     Haux Hst0 HiT Hj Hs =>
                   sig_inputs_step (List.rev G2) envsF auxF stN Hnaming P nS nM
                     nall env r st0 stl accT sgT stT0 stT1 HR Hloc Hfind Haux
                     Hst0 HiT Hj Hs)
                (fun P nS nM nall env r st0 stl accS accT sgS stS0 stS1 sgT
                     stT0 stT1 HR Hloc Hfind Haux Hst0 HiS HiT Hw Hj HsS HsT =>
                   stepU (List.rev G2) envsF auxF stN Hnaming P nS nM nall env r
                     st0 stl accS accT sgS stS0 stS1 sgT stT0 stT1 HR Hloc
                     Hfind Haux Hst0 HiS HiT Hw Hj HsS HsT)
                (List.rev G) (List.rev G1)
                (build_U G Hwl Hpr Hunt Hpref1 Hwc Hwt Hguard) Hnd Hle
                sig_inputs_ok_nil GS GT HgS HgT)
      as (Hc1 & Hp1 & _).
    (** the [fby] leg *)
    destruct (generate_all_lsignatures_weakens_ext_driver
                (List.rev G2) envsF auxF stN st Hnaming RI
                (fun _ _ => True)
                (fun P nS nM nall HR =>
                   match RI_facts P nS nM nall HR with
                   | conj Hn1 (conj Hn2 (conj tfM tfN)) =>
                     conj Hn1 (conj tfM (conj Hn2 tfN))
                   end)
                (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => I)
                (fun P nS nM nall env r st0 stl accS accT sgS stS0 stS1 sgT
                     stT0 stT1 HR Hloc Hfind Haux Hst0 HiS HiT Hw Hj HsS HsT =>
                   stepI (List.rev G2) envsF auxF stN Hnaming P nS nM nall env r
                     st0 stl accS accT sgS stS0 stS1 sgT stT0 stT1 HR Hloc
                     Hfind Haux Hst0 HiS HiT Hw Hj HsS HsT)
                (List.rev G1) (List.rev G2)
                (build_I G1 Hunt Hpref1 Hwc1 Hwt1) Hnd Hle I GT GM HgT HgM)
      as (Hc2 & Hp2 & _).
    split.
    - exact (call_weakens_trans _ _ _ Hc1 Hc2).
    - exact (sigs_preserved_trans _ _ _ Hp1 Hp2).
  Qed.

End SecLusNormalization.
