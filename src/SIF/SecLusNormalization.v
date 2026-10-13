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
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import Lustre.Normalization.NormFby.
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
  (Import UNN     : UNNESTING Ids Op OpAux LSyn)
  (Import NF      : NORMFBY Ids Op OpAux LSyn UNN)
  (Import SECLNG  : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (Import SECNT   : SECNAMINGTOTALITY Ids Op CESyn NLSyn Mem IsD NLOrd NAMEGEN)
  (Import LOrd    : LORDERED Ids Op LSyn)
  (Import SECLNT  : SECLNAMINGTOTALITY Ids Op OpAux LSyn CESyn NLSyn Mem IsD
                      NLOrd NAMEGEN TR SECLNG SECNT LOrd)
.

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

    Definition clk_scoped_wc (ckenv : Env.t (type * clock))
        (S : list ident) : Prop :=
      forall es ck ckty,
        Forall (wc_exp P vars) es ->
        Forall (nested_src vars AN) es ->
        (clk_src vars es ck \/
         exists x, In x (List.map fst vars) /\ find_clock ckenv x = OK ck) ->
        assign_clk_type env base_ty ck = Some ckty ->
        st_scoped S ckty.

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
            exact (Hclk [] ck ckty (Forall_nil _) (Forall_nil _)
                     (or_intror (ex_intro _ x
                        (conj (Hxv x (or_introl (@Logic.eq_refl _ x))) Hfc)))
                     Hck).
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
        exact (Hclk [] ck ckty (Forall_nil _) (Forall_nil _)
                 (or_intror (ex_intro _ x (conj Hxv Hfc))) Hck).
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
           exact (Hclk es _ _ Hwces Hnsx (or_introl (clk_src_base vars es)) Hck)
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
          exact (Hclk [e1] (hd Cbase (LSyn.clockof e1)) rck
                   (Forall_cons _ Hwce1 (Forall_nil _))
                   (Forall_cons _ Hns1 (Forall_nil _))
                   (or_introl (clk_src_hd_clockof vars e1)) Hrck).
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

    Theorem lexp_scoped_tgt_all_src :
      forall decl,
        In base_ty decl -> In rst_ty decl ->
        (forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                     In b decl) ->
        (forall es ck ckty,
            Forall (wc_exp P vars) es -> Forall (nested_src vars AN) es ->
            clk_src vars es ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            st_scoped decl ckty) ->
        secglobal_scoped G ->
        forall e, wc_exp P vars e /\ src_exp vars AN e ->
                  lexp_scoped_tgt G env base_ty rst_ty decl e.
    Proof.
      intros decl Hbase Hrstd Henv Hclk Hsg e.
      induction e using exp_ind2; intros (Hwc & Hsx) ts s s' Hgen.
      - rewrite assign_lexp_Econst in Hgen. unfold SC.ret in Hgen.
        destruct (OK_pair_inv _ _ _ _ Hgen) as (Hts & _); subst ts.
        split.
        + constructor; [|constructor]. cbn [fst lbot]. intros ? [].
        + cbn [carried lbot snd]. constructor.
      - apply assign_lexp_Evar_inv in Hgen as (xt & Hxt & Hts & _); subst ts.
        split.
        + constructor; [|constructor]. cbn [fst].
          intros y [Hy|[]]; subst y. apply in_or_app. left.
          exact (Henv _ _ (wc_Evar_vars P vars _ _ Hwc) Hxt).
        + cbn [carried snd]. constructor.
      - exact (IHe (conj (wc_Eunop_sub P vars _ _ _ Hwc)
                      (src_exp_imm vars AN _ _ (imm_Eunop _ _ _) Hsx))
                 ts s s' Hgen).
      - rewrite assign_lexp_Ebinop in Hgen.
        apply sec_bind_inv in Hgen as (t1 & s1 & Ht1 & Hgen).
        apply sec_bind_inv in Hgen as (t2 & s2 & Ht2 & Hgen).
        apply sec_bind_inv in Hgen as (a1 & s3 & Ha1 & Hgen).
        apply sec_bind_inv in Hgen as (a2 & s4 & Ha2 & Hret).
        apply single_inv in Ha1 as (? & ?); subst t1 s3.
        apply single_inv in Ha2 as (? & ?); subst t2 s4.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        destruct (wc_Ebinop_sub P vars _ _ _ _ Hwc) as (Hw1 & Hw2).
        destruct (IHe1 (conj Hw1 (src_exp_imm vars AN _ _ (imm_Ebinop_l _ _ _ _) Hsx))
                    [a1] s s1 Ht1) as (Hf1 & Hc1).
        destruct (IHe2 (conj Hw2 (src_exp_imm vars AN _ _ (imm_Ebinop_r _ _ _ _) Hsx))
                    [a2] s1 s2 Ht2) as (Hf2 & Hc2).
        rewrite carried_single in Hf1, Hc1, Hf2, Hc2.
        rewrite carried_single, snd_ljoin.
        inversion Hf1 as [|? ? Hs1 ?]; subst.
        inversion Hf2 as [|? ? Hs2 ?]; subst.
        split.
        + constructor; [|constructor]. rewrite fst_ljoin.
          apply st_scoped_merge.
          * eapply st_scoped_weaken;
              [apply incl_decl_tgt, tgt_names_cmerge_l|exact Hs1].
          * eapply st_scoped_weaken;
              [apply incl_decl_tgt, tgt_names_cmerge_r|exact Hs2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Efby in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (wc_Efby_sub P vars _ _ _ Hwc) as (Hw0 & Hw1).
        pose proof (src_exp_imm_forall vars AN e0s _
                      (fun e' He' => imm_Efby_0 _ _ _ e' He') Hsx) as Hs0.
        pose proof (src_exp_imm_forall vars AN es _
                      (fun e' He' => imm_Efby_1 _ _ _ e' He') Hsx) as Hs1.
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl e0s
                    (Forall_wc_impl _ _ _ H (Forall_and _ _ _ Hw0 Hs0))
                    ts0 s s1 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es
                    (Forall_wc_impl _ _ _ H0 (Forall_and _ _ _ Hw1 Hs1))
                    us s1 s2 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        split.
        + eapply CALLS.ljoin_list_scoped_plain; [exact Hj| |].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Earrow in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s2 & Hus & Hj).
        assert (s' = s2) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (wc_Earrow_sub P vars _ _ _ Hwc) as (Hw0 & Hw1).
        pose proof (src_exp_imm_forall vars AN e0s _
                      (fun e' He' => imm_Earrow_0 _ _ _ e' He') Hsx) as Hs0.
        pose proof (src_exp_imm_forall vars AN es _
                      (fun e' He' => imm_Earrow_1 _ _ _ e' He') Hsx) as Hs1.
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl e0s
                    (Forall_wc_impl _ _ _ H (Forall_and _ _ _ Hw0 Hs0))
                    ts0 s s1 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es
                    (Forall_wc_impl _ _ _ H0 (Forall_and _ _ _ Hw1 Hs1))
                    us s1 s2 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried ts0 us ts s2 s2 Hj).
        split.
        + eapply CALLS.ljoin_list_scoped_plain; [exact Hj| |].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - rewrite assign_lexp_Ewhen in Hgen.
        apply sec_bind_inv in Hgen as (ts0 & s1 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (g & s2 & Hg & Hret).
        apply find_env_inv in Hg as (Hg & ?); subst s2.
        unfold SC.ret in Hret.
        destruct (OK_pair_inv _ _ _ _ Hret) as (Hts & ?); subst ts s'.
        destruct (wc_Ewhen_sub P vars _ _ _ _ Hwc) as (Hw0 & Hwx).
        pose proof (src_exp_imm_forall vars AN es _
                      (fun e' He' => imm_Ewhen _ _ _ _ e' He') Hsx) as Hs0.
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es
                    (Forall_wc_impl _ _ _ H (Forall_and _ _ _ Hw0 Hs0))
                    ts0 s s1 Hts0) as (Hf1 & Hc1).
        rewrite carried_map_when.
        split; [|exact Hc1].
        apply Forall_forall. intros t Ht.
        apply in_map_iff in Ht as (t0 & Ht0 & Hin0); subst t.
        rewrite fst_ljoin, fst_lvar. apply st_scoped_merge.
        + rewrite Forall_forall in Hf1. exact (Hf1 t0 Hin0).
        + intros y [Hy|[]]; subst y. apply in_or_app. left.
          exact (Henv _ _ Hwx Hg).
      - destruct a as (tys & cl).
        rewrite assign_lexp_Emerge in Hgen.
        apply sec_bind_inv in Hgen as (g & s1 & Hg & Hgen).
        apply find_env_inv in Hg as (Hg & ?); subst s1.
        apply sec_bind_inv in Hgen as (ts0 & s2 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s3 & Hus & Hj).
        assert (s' = s3) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (wc_Emerge_sub P vars _ _ _ _ Hwc) as (Hw0 & Hw1 & Hwx).
        pose proof (src_exp_imm_forall vars AN ets _
                      (fun e' He' => imm_Emerge_t _ _ _ _ e' He') Hsx) as Hs0.
        pose proof (src_exp_imm_forall vars AN efs _
                      (fun e' He' => imm_Emerge_f _ _ _ _ e' He') Hsx) as Hs1.
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl ets
                    (Forall_wc_impl _ _ _ H (Forall_and _ _ _ Hw0 Hs0))
                    ts0 s s2 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl efs
                    (Forall_wc_impl _ _ _ H0 (Forall_and _ _ _ Hw1 Hs1))
                    us s2 s3 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried _ us ts s3 s3 Hj), carried_map_merge_l.
        split.
        + eapply CALLS.ljoin_list_scoped; [|exact Hj| |].
          * apply in_or_app. left. exact (Henv _ _ Hwx Hg).
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hf1].
          * eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
        + apply cscoped_cmerge;
            [eapply cscoped_tgt_widen; [apply tgt_names_cmerge_l|exact Hc1]
            |eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2]].
      - destruct a as (tys & cl).
        rewrite assign_lexp_Eite in Hgen.
        apply sec_bind_inv in Hgen as (t0 & s1 & Ht0 & Hgen).
        apply sec_bind_inv in Hgen as (th & s2 & Hth & Hgen).
        apply single_inv in Hth as (? & ?); subst t0 s2.
        apply sec_bind_inv in Hgen as (ts0 & s3 & Hts0 & Hgen).
        apply sec_bind_inv in Hgen as (us & s4 & Hus & Hj).
        assert (s' = s4) as ? by (eapply ljoin_list_pure; exact Hj); subst s'.
        destruct (wc_Eite_sub P vars _ _ _ _ Hwc) as (Hw0 & Hw1 & Hw2).
        pose proof (src_exp_imm vars AN _ _ (imm_Eite_c _ _ _ _) Hsx) as Hsc.
        pose proof (src_exp_imm_forall vars AN ets _
                      (fun e' He' => imm_Eite_t _ _ _ _ e' He') Hsx) as Hs1.
        pose proof (src_exp_imm_forall vars AN efs _
                      (fun e' He' => imm_Eite_f _ _ _ _ e' He') Hsx) as Hs2.
        destruct (IHe (conj Hw0 Hsc) [th] s s1 Ht0) as (Hfh & Hch).
        rewrite carried_single in Hfh, Hch.
        inversion Hfh as [|? ? Hsh ?]; subst.
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl ets
                    (Forall_wc_impl _ _ _ H (Forall_and _ _ _ Hw1 Hs1))
                    ts0 s1 s3 Hts0) as (Hf1 & Hc1).
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl efs
                    (Forall_wc_impl _ _ _ H0 (Forall_and _ _ _ Hw2 Hs2))
                    us s3 s4 Hus) as (Hf2 & Hc2).
        rewrite (ljoin_list_carried _ us ts s4 s4 Hj).
        destruct ts0 as [|t00 ts0'].
        + cbn [List.map carried]. rewrite cmerge_nil2.
          split.
          * eapply CALLS.ljoin_list_scoped_plain; [exact Hj|constructor|].
            exact Hf2.
          * exact Hc2.
        + rewrite carried_map_ljoin_eq by (intros HF; inversion HF).
          split.
          * eapply CALLS.ljoin_list_scoped_head; [|exact Hj| |].
            -- eapply st_scoped_weaken; [|exact Hsh].
               apply incl_decl_tgt.
               eapply incl_tran;
                 [apply tgt_names_cmerge_l|apply tgt_names_cmerge_l].
            -- eapply scoped_tgt_widen; [|exact Hf1].
               eapply incl_tran;
                 [apply tgt_names_cmerge_r|apply tgt_names_cmerge_l].
            -- eapply scoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hf2].
          * apply cscoped_cmerge; [apply cscoped_cmerge|].
            -- eapply cscoped_tgt_widen; [|exact Hch].
               eapply incl_tran;
                 [apply tgt_names_cmerge_l|apply tgt_names_cmerge_l].
            -- eapply cscoped_tgt_widen; [|exact Hc1].
               eapply incl_tran;
                 [apply tgt_names_cmerge_r|apply tgt_names_cmerge_l].
            -- eapply cscoped_tgt_widen; [apply tgt_names_cmerge_r|exact Hc2].
      - apply assign_lexp_Eapp_inv in Hgen
          as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & Hck & Hrst & Hsgf & Houts & Hcs & Hts).
        destruct (wc_Eapp_sub P vars _ _ _ _ Hwc) as (Hwes & Hwro).
        assert (Forall (src_exp vars AN) es) as Hsxes
          by (eapply src_exp_imm_forall; [|exact Hsx];
              intros e' He'; exact (imm_Eapp_arg _ _ _ _ e' He')).
        assert (Forall (nested_src vars AN) es) as Hnses
          by (eapply nested_src_args; exact Hsx).
        destruct (lexps_scoped_tgt_of G env base_ty rst_ty decl es
                    (Forall_wc_impl _ _ _ H0 (Forall_and _ _ _ Hwes Hsxes))
                    argts s sta Hargs) as (Hfa & Hca).
        assert (exists rs, st_scoped (decl ++ tgt_names rs) (fst rstty)
                           /\ constraints_scoped (decl ++ tgt_names rs)
                                (snd rstty)
                           /\ incl (tgt_names rs) (tgt_names (snd rstty)))
          as (rs & Hfr & Hcr & Hir).
        { destruct ro as [e1|].
          - destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Hsg1 & Hrck & Hr).
            apply single_inv in Hsg1 as (? & ?); subst t1 stb.
            assert (Hwe1 : wc_exp P vars e1)
              by exact (Hwro e1 Logic.eq_refl).
            assert (src_exp vars AN e1) as Hsxe1
              by (eapply src_exp_imm; [apply imm_Eapp_rst|exact Hsx]).
            assert (nested_src vars AN e1) as Hnse1
              by (eapply nested_src_reset; exact Hsx).
            destruct (H (conj Hwe1 Hsxe1) [a1] sta stm Ht1) as (Hf1 & Hc1).
            rewrite carried_single in Hf1, Hc1.
            inversion Hf1 as [|? ? Hs1 ?]; subst.
            exists (snd a1). try subst rstty.
            rewrite !fst_ljoin, !snd_ljoin, fst_lvar, snd_lvar.
            cbn [fst snd]. rewrite cmerge_nil, cmerge_nil2.
            split; [|split; [exact Hc1|apply incl_refl]].
            apply st_scoped_merge;
              [intros y [Hy|[]]; subst y; apply in_or_app; now left|].
            apply st_scoped_merge; [exact Hs1|].
            eapply st_scoped_weaken;
              [|exact (Hclk [e1] _ _ (Forall_cons _ Hwe1 (Forall_nil _))
                         (Forall_cons _ Hnse1 (Forall_nil _))
                         (clk_src_hd_clockof vars e1) Hrck)].
            intros y Hy. apply in_or_app. left. exact Hy.
          - destruct Hrst as (Hr & _). subst rstty.
            exists []. rewrite fst_lvar, snd_lvar.
            split; [intros y [Hy|[]]; subst y; apply in_or_app; now left|].
            split; [constructor|intros y []]. }
        pose proof (CALLS.generate_constraints_targets sg
                      (List.map fst argts) ckty (fst rstty) outs cs
                      stc s' Hcs) as Hsnd.
        subst ts. rewrite carried_uniform.
        destruct outs as [|o os].
        + split; [constructor|constructor].
        + assert (Hcsi : incl (tgt_names cs)
                           (tgt_names (cmerge cs
                              (cmerge (carried argts) (snd rstty)))))
              by apply tgt_names_cmerge_l.
          assert (Hargi : incl (tgt_names (carried argts))
                            (tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty))))).
          { eapply incl_tran;
              [apply tgt_names_cmerge_l|apply tgt_names_cmerge_r]. }
          assert (Hrsti : incl (tgt_names (snd rstty))
                            (tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty))))).
          { eapply incl_tran;
              [apply tgt_names_cmerge_r|apply tgt_names_cmerge_r]. }
          assert (Hoin : forall d, In d (o :: os) ->
                           In d (decl ++ tgt_names (cmerge cs
                                   (cmerge (carried argts) (snd rstty))))).
          { intros d Hd. apply in_or_app. right.
            apply Hcsi. exact (tgt_names_of_targets cs (o :: os) Hsnd d Hd). }
          assert (Hcscs : constraints_scoped
                            (decl ++ tgt_names (cmerge cs
                               (cmerge (carried argts) (snd rstty)))) cs).
          { eapply generate_constraints_scoped;
              [exact (Hsg _ _ Hsgf)| | | | |exact Hcs].
            - apply Forall_forall. intros X HX.
              apply in_map_iff in HX as (t & Ht & Htin); subst X.
              eapply st_scoped_weaken; [apply incl_decl_tgt, Hargi|].
              rewrite Forall_forall in Hfa. exact (Hfa t Htin).
            - eapply st_scoped_weaken;
                [|exact (Hclk es _ _ Hwes Hnses (clk_src_base vars es) Hck)].
              intros y Hy. apply in_or_app. left. exact Hy.
            - eapply st_scoped_weaken; [apply incl_decl_tgt, Hrsti|].
              eapply st_scoped_weaken; [apply incl_decl_tgt, Hir|exact Hfr].
            - apply Forall_forall. exact Hoin. }
          split.
          * apply Forall_forall. intros t Ht.
            apply in_map_iff in Ht as (d & Hd & Hdin); subst t.
            cbn [fst]. intros y [Hy|[]]; subst y. exact (Hoin d Hdin).
          * apply cscoped_cmerge; [exact Hcscs|].
            apply cscoped_cmerge.
            -- eapply cscoped_tgt_widen; [exact Hargi|exact Hca].
            -- eapply cscoped_tgt_widen; [exact Hrsti|].
               eapply cscoped_tgt_widen; [exact Hir|exact Hcr].
    Qed.

    (** The guarded premises, from the dichotomy at the node's declared
        names. *)
    Lemma exps_scoped_wc_of_decl :
      forall decl S ckenv,
        In base_ty decl -> In rst_ty decl ->
        (forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                     In b decl) ->
        clk_scoped_wc ckenv decl ->
        secglobal_scoped G ->
        incl decl S ->
        exps_scoped_wc S.
    Proof.
      intros decl S ckenv Hb Hr Henv Hclk Hsg Hds.
      assert (Hclk' : forall es ck ckty,
                 Forall (wc_exp P vars) es -> Forall (nested_src vars AN) es ->
                 clk_src vars es ck ->
                 assign_clk_type env base_ty ck = Some ckty ->
                 st_scoped decl ckty)
        by (intros es ck ckty Hw Hn Hsrc Hck;
            exact (Hclk es ck ckty Hw Hn (or_introl Hsrc) Hck)).
      split.
      - intros e ts s0 s1 Hwc Hsx Hci Hgen.
        destruct (lexp_scoped_tgt_all_src decl Hb Hr Henv Hclk' Hsg e
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
          exact (lexp_scoped_tgt_all_src decl Hb Hr Henv Hclk' Hsg e0
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

  (** The clock-scoping premise of the guarded rules, from the node's
      declared variables: a clock the rules meet samples on declared variables
      only, because it is a declared clock, or the clock of a source
      expression, whose anonymous names are not environment keys. *)
  Section ClkScopedWc.

    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable cenv    : Env.t (type * clock).
    Variable vars    : list (ident * clock).
    Variable AN      : list ident.
    Variable decl    : list ident.

    Hypothesis Hb : In base_ty decl.
    Hypothesis Henv :
      forall x b, In x (List.map fst vars) -> Env.find x env = Some b ->
                  In b decl.
    Hypothesis Hwenv : wc_env vars.
    Hypothesis Hanon :
      forall w b, Env.find w env = Some b -> ~ In w AN.
    Hypothesis Hcenv :
      forall x ck, In x (List.map fst vars) -> find_clock cenv x = OK ck ->
                   incl (clock_vars ck) (List.map fst vars).

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
      forall (P : global),
        wc_global P ->
        clk_scoped_wc env base_ty P vars AN cenv decl.
    Proof.
      intros P Hg es ck ckty Hwes Hnes Hsrc H.
      destruct Hsrc as [Hs|(x & Hx & Hfc)].
      - intros y Hy.
        destruct (assign_clk_type_images env base_ty ck ckty H y Hy)
          as [->|(x & Hx & Hf)]; [exact Hb|].
        unfold clk_src in Hs. rewrite ck_vars_eq in Hs.
        apply Hs in Hx. apply in_app_or in Hx as [Hx|Hx];
          [exact (Henv x y Hx Hf)|].
        apply in_flat_map in Hx as (c & Hc & Hxc).
        rewrite ck_vars_eq in Hxc.
        unfold clocksof in Hc. apply in_flat_map in Hc as (e & He & Hce).
        rewrite Forall_forall in Hwes, Hnes.
        pose proof (wc_exp_clockof P vars e Hg Hwenv (Hwes e He)) as Hcl.
        rewrite Forall_forall in Hcl.
        destruct (clock_vars_wc _ c (Hcl c Hce) x Hxc) as (ckx & Hin).
        apply in_app_or in Hin as [Hin|Hin].
        + apply (Henv x y).
          * apply in_map_iff. exists (x, ckx). split; [reflexivity|exact Hin].
          * exact Hf.
        + exfalso.
          unfold idck in Hin. apply in_map_iff in Hin as ((x' & (ty & ckx')) & Heq & Hin').
          inversion Heq; subst x' ckx'.
          destruct (Hnes e He) as (_ & Hfresh).
          exact (Hanon x y Hf (Hfresh x _ Hin')).
      - exact (clk_vars_images_scoped_wc ck ckty (Hcenv x ck Hx Hfc) H).
    Qed.

  End ClkScopedWc.

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
      (forall w b, Env.find w env = Some b -> ~ In w AN) ->
      (forall x b, Env.find x env = Some b -> ~ In b (minted st0 st1)) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      signature_scoped sg.
  Proof.
    intros G P AN n env aux sg st0 st1 Hinj Hsgs Hwl Hwcg Hwcn Hsrc Hanon Hsep Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    assert (inp = CALLS.sec_of env (List.map fst n.(n_in))) as Hi
        by (eapply get_mappings_from_node_sec_of; exact Hinp).
    assert (out = CALLS.sec_of env (List.map fst n.(n_out))) as Ho
        by (eapply get_mappings_from_node_sec_of; exact Hout).
    assert (locals = CALLS.sec_of env (List.map fst n.(n_vars))) as Hl
        by (eapply get_mappings_from_node_sec_of; exact Hloc).
    set (decl := CALLS.sec_of env
                   (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                 ++ [ct; rt]).
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
    assert (Hclk : clk_scoped_wc env ct P vars AN (lnode_clock_env n) decl)
      by exact (clk_scoped_wc_holds env ct (lnode_clock_env n) vars AN decl
                  Hbd Hrg Hwenv Hanon Hcenv P Hwcg).
    (** item 7: every target is a defined name or a minted one *)
    destruct (generate_leqns_constraints_shape G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (minted st0 st1)
                (incl_refl _) Hsep (wl_node_arity P n Hwl) Hcns)
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
    assert (Htb : incl (tgt_names cns) (decl ++ minted st0 st1)).
    { eapply incl_tran; [eapply tgt_names_of_targets_of; exact Hm|].
      apply incl_app;
        [eapply incl_tran; [exact Hdefd|apply incl_appl, incl_refl]
        |eapply incl_tran; [exact Hms|apply incl_appr, incl_refl]]. }
    (** the scoping, at the scope that carries the dichotomy *)
    set (S := decl ++ tgt_names cns).
    assert (HclkS : clk_scoped_wc env ct P vars AN (lnode_clock_env n) S).
    { intros es ck ckty Hw Hn Hsr Hck.
      eapply st_scoped_weaken;
        [unfold S; apply incl_appl, incl_refl|exact (Hclk es ck ckty Hw Hn Hsr Hck)]. }
    assert (Hcsc : constraints_scoped S cns).
    { eapply generate_leqns_constraints_scoped_wc;
        [exact Hsgs|exact HclkS| |
         eapply exps_scoped_wc_of_decl;
           [exact Hbd|exact Hrd|exact Hrg|exact Hclk|exact Hsgs
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
      + apply minted_NoDup.
      + apply Forall_forall. intros y Hy Hin. apply (Hdm y); [|exact Hin].
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
        * apply in_or_app. right. apply in_or_app. now right.
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
      + (** a minted name: a target if it occurs at all *)
        destruct (In_dec ident_eq_dec d (tgt_names (collapse cns)))
          as [Ht|Ht].
        * left. exact (In_tgt_names_target (collapse cns) d Hlen1 Ht).
        * right. intros (c & Hc & Hx).
          assert (In d S) as Hin
              by (eapply constraints_scoped_In; [exact Hcol|exact Hc|exact Hx]).
          unfold S in Hin. apply in_app_or in Hin as [Hin|Hin].
          -- exact (Hdm d Hin Hd).
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
          /\ ~ In rst_id (List.map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))) ->
      generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
      CALLS.all_sources_have sg.(s_clk) sg.(s_constraints)
      /\ CALLS.all_sources_have sg.(s_reset) sg.(s_constraints).
  Proof.
    intros G P n env aux sg st0 st1 X Hinj Hsgs Hnd Hroot Hwl Hsep Hrf Haux0 Hsig.
    destruct (lnode_sig_inv env G n aux sg st0 st1 Hsig)
      as (ci & ri & ct & rt & inp & out & locals & cns
          & Haux & Hct & Hrt & Hinp & Hout & Hloc & Hcns & ?); subst sg.
    destruct (Haux0 ci ri Haux) as (Hnc & Hnr).
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
    { eapply (generate_leqns_constraints_rooted_win G env ct rt decl
                (decl ++ minted st0 st1) Hdk Hclk Hsgs);
        [apply incl_appl, incl_refl|exact Hnsf|exact Hnd|exact Hroot
        |apply incl_appr, incl_refl
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
    destruct (generate_leqns_constraints_shape G env ct rt
                (lnode_clock_env n) n.(n_eqs) cns st0 st1 (minted st0 st1)
                (incl_refl _) Hsep (wl_node_arity P n Hwl) Hcns)
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
      - apply Hms in Hy. split; intros ->;
          [exact (Hsep ci _ Hct Hy)|exact (Hsep ri _ Hrt Hy)]. }
    assert (Hrs : constraints_rooted ct rt
                    (simplify (collapse cns) (locals ++ minted st0 st1))).
    { apply simplify_rooted with (keep := [ct; rt]).
      - now left.
      - right. now left.
      - intros d Hd [Hdc|[Hdr|[]]]; subst d; apply in_app_or in Hd as [Hd|Hd].
        + rewrite Hl in Hd. exact (proj1 (Hav _ Hd) Logic.eq_refl).
        + exact (Hsep ci _ Hct Hd).
        + rewrite Hl in Hd. exact (proj2 (Hav _ Hd) Logic.eq_refl).
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
                    ~ In w (List.map fst (nall.(n_in) ++ nall.(n_vars)
                                          ++ nall.(n_out))))
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
      (forall w b, Env.find w env = Some b -> ~ In w AN) ->
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      lsig_inv stN st0 acc st ->
      generate_lnode_sig acc n env aux st = OK (sg, st1) ->
      lsig_inv stN stl (sg :: acc) st1.
  Proof.
    intros P AN all envs aux stN n nall env r st0 stl acc st sg st1
           Hfull Hfind Haux Hloc Hst0 Hwl Hwcg Hwcn Hsrc Hanon Hsub
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
    assert (Hgd : signature_good sg)
      by exact (generate_lnode_sig_good acc P n env aux sg st st1 Hinj Hwl
                  Hsep Hsig).
    assert (Hscd : signature_scoped sg)
      by exact (generate_lnode_sig_scoped_wc acc P AN n env aux sg st st1
                  Hinj Hsc Hwl Hwcg Hwcn Hsrc Hanon Hsep Hsig).
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
        split; assumption. }
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
      apply name_bind_inv in Hl as (c4 & s4 & _ & Hret0).
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

  Lemma anon_names_not_env_key :
    forall n nall st0 le0 r0 stl w b,
      PS.Subset n.(n_prefixes) (PSP.of_list gensym_prefs) ->
      (forall w, In w (anon_names n) ->
                 ~ In w (List.map fst (nall.(n_in) ++ nall.(n_vars)
                                       ++ nall.(n_out)))) ->
      generate_local_env_for_lnode nall st0 = OK ((le0, r0), stl) ->
      Env.find w le0 = Some b -> ~ In w (anon_names n).
  Proof.
    intros n nall st0 le0 r0 stl w b Hsubn Hdisj Hloc Hb Hin.
    destruct (generate_local_env_for_lnode_facts nall st0 le0 r0 stl Hloc)
      as (_ & _ & Hclk & Hrst).
    destruct (generate_local_env_for_lnode_domain nall st0 le0 r0 stl w b
                Hloc Hb) as [Hw|[Hw|Hw]].
    - rewrite Hw, Hclk in Hin. unfold anon_names in Hin.
      apply fst_InMembers in Hin.
      exact (anon_stream_not_sec n _ st0 Hsubn Hin Logic.eq_refl).
    - rewrite Hw, Hrst in Hin. unfold anon_names in Hin.
      apply fst_InMembers in Hin.
      exact (anon_stream_not_sec n _ (Pos.succ st0) Hsubn Hin Logic.eq_refl).
    - apply (Hdisj w Hin).
      rewrite !map_app in Hw |- *.
      apply in_app_or in Hw as [Hw|Hw]; [apply in_or_app; now left|].
      apply in_app_or in Hw as [Hw|Hw]; apply in_or_app; right;
        apply in_or_app; [now right|now left].
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
        |exact (fun w b Hb => anon_names_not_env_key n nall st0 le0 r0 stl w b
                  Hsubn Hdisj Hloc Hb)
        |exact Hsubn|exact Hinv|exact Hs].
  Qed.


  (** * The lockstep, with the invariants

      [generate_all_lsignatures_weakens'] with the node-level step handed what
      the program level knows at that point: both accumulators satisfy
      [lsig_inv] against the naming run, and the states are above its final
      state.  The invariants are re-established after each node by
      [lsig_step_ext]. *)

  Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop)
    : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall a b c l1 l2 l3,
      R a b c -> Forall3 R l1 l2 l3 -> Forall3 R (a :: l1) (b :: l2) (c :: l3).

  Theorem generate_all_lsignatures_weakens_ext :
    forall (all : list node) envsF auxF stN,
      generate_lnode_scoped_env_st all = OK (envsF, auxF, stN) ->
      forall (R : node -> node -> node -> Prop),
        (forall nS nM nall, R nS nM nall ->
           n_name nS = n_name nall /\ node_typed_facts nS nall
           /\ n_name nM = n_name nall /\ node_typed_facts nM nall) ->
        (forall nS nM nall (env : Env.t ident) (r : node_aux_names) st0 stl
                accS accT sgS stS0 stS1 sgT stT0 stT1,
            R nS nM nall ->
            generate_local_env_for_lnode nall st0 = OK ((env, r), stl) ->
            find_node_env nall.(n_name) envsF = Some env ->
            get_node_aux nall.(n_name) auxF = Some (r.(nclk), r.(nrst)) ->
            (st0 <= stN)%positive ->
            lsig_inv stN st0 accS stS0 ->
            lsig_inv stN st0 accT stT0 ->
            call_weakens accS accT ->
            generate_lnode_sig_scoped_env accS nS envsF auxF stS0
              = OK (sgS, stS1) ->
            generate_lnode_sig_scoped_env accT nM envsF auxF stT0
              = OK (sgT, stT1) ->
            sig_head_weakens sgS sgT) ->
        forall nsS nsM alls envs0 acc0 st0,
          Forall3 R nsS nsM alls ->
          NoDup (List.map n_name alls) ->
          generate_lnode_scoped_env' alls envs0 acc0 st0
            = OK ((envsF, auxF), stN) ->
          forall accS accT stS stT GS GT stfS stfT,
            lsig_inv stN st0 accS stS ->
            lsig_inv stN st0 accT stT ->
            call_weakens accS accT ->
            sigs_preserved accS accT ->
            generate_all_lsignatures' accS nsS envsF auxF stS = OK (GS, stfS) ->
            generate_all_lsignatures' accT nsM envsF auxF stT = OK (GT, stfT) ->
            call_weakens GS GT /\ sigs_preserved GS GT.
  Proof.
    intros all envsF auxF stN Hfull R HR Hstep.
    intros nsS nsM alls. revert nsS nsM.
    induction alls as [|nall alls IH];
      intros nsS nsM envs0 acc0 st0 HF3 Hnd Hrun accS accT stS stT GS GT stfS stfT
        HinvS HinvT Hw Hp HgS HgT.
    - inversion HF3; subst. cbn in HgS, HgT.
      inversion HgS; subst. inversion HgT; subst. split; assumption.
    - inversion HF3 as [|nS nM nall0 nsS' nsM' alls0 HRn HF3']; subst.
      destruct (HR nS nM nall HRn) as (HnameS & (PS & HwlS & HwcgS & HwcnS
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
      destruct (Hstep nS nM nall le0 r0 st0 stl accS accT sgS stS stS1 sgT
                  stT stT1 HRn Hloc Hfind Haux Hst0 HinvS HinvT Hw HsS HsT)
        as (Hname & Hpres & Hcall).
      unfold generate_lnode_sig_scoped_env in HsS, HsT.
      rewrite HnameS, Hfind in HsS. rewrite HnameM, Hfind in HsT.
      eapply (IH nsS' nsM' (Env.add nall.(n_name) le0 envs0) (r0 :: acc0) stl
                 HF3' Hnd' Hrec (sgS :: accS) (sgT :: accT) stS1 stT1 GS GT
                 stfS stfT); try assumption.
      + eapply lsig_step_ext;
          [exact Hfull|rewrite HnameS; exact Hfind|rewrite HnameS; exact Haux
          |exact Hloc|exact Hst0|exact HwlS|exact HwcgS|exact HwcnS|exact HsrcS
          |exact (fun w b Hb => anon_names_not_env_key nS nall st0 le0 r0 stl
                                  w b HsubS HdisjS Hloc Hb)
          |exact HsubS|exact HinvS|exact HsS].
      + eapply lsig_step_ext;
          [exact Hfull|rewrite HnameM; exact Hfind|rewrite HnameM; exact Haux
          |exact Hloc|exact Hst0|exact HwlM|exact HwcgM|exact HwcnM|exact HsrcM
          |exact (fun w b Hb => anon_names_not_env_key nM nall st0 le0 r0 stl
                                  w b HsubM HdisjM Hloc Hb)
          |exact HsubM|exact HinvT|exact HsT].
      + exact (call_weakens_cons sgS sgT accS accT Hname Hcall Hw).
      + exact (sigs_preserved_cons sgS sgT accS accT Hname Hpres Hp).
  Qed.

  Set Printing Width 130.
  Check @unnest_node_step_streams.
  Check @normfby_node_step.

End SecLusNormalization.
