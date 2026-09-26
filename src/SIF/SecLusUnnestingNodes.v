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

  (** * Two signature globals

      The program level does not generate a node's signature against one
      signature global.  The source run reads the accumulator built from the
      source callees; the target run reads the one built from the *unnested*
      callees.  Those two are not equal -- a callee whose body held a nested
      call publishes weaker constraints after unnesting, which is the whole
      content of this leg -- so the node-level entailment, which fixes a
      single [GL], does not by itself compose along a program.

      What bridges them is that the difference is confined to a callee's
      stored constraints, and that at a call site an instantiated block is
      scoped to the *caller*.  So [preserves_on] on the callee's own scope
      collapses to plain implication under the caller's valuation --
      [signatures_preserved_equal_calls_from_good] followed by
      [preserves_on_sat] -- and the weakening travels through the generator as
      an implication between constraint lists at a *fixed* valuation.  There
      is no witness to move and no scope to track, so it composes over
      [cmerge] and over lists by nothing but [listSatisfiable_cmerge].

      That is the same observation the transcription leg makes, and for the
      same reason; the difference is only which two globals are being
      compared. *)

  Definition cs_entails (cs1 cs2 : list constraint) : Prop :=
    forall dlt, listSatisfiable dlt cs1 -> listSatisfiable dlt cs2.

  Definition lst_entails (t1 t2 : LST) : Prop :=
    fst t1 = fst t2 /\ cs_entails (snd t1) (snd t2).

  Lemma cs_entails_refl : forall cs, cs_entails cs cs.
  Proof. intros cs dlt H. exact H. Qed.

  Lemma cs_entails_trans :
    forall a b c, cs_entails a b -> cs_entails b c -> cs_entails a c.
  Proof. intros a b c H1 H2 dlt H. exact (H2 dlt (H1 dlt H)). Qed.

  Lemma cs_entails_cmerge :
    forall a1 a2 b1 b2,
      cs_entails a1 a2 -> cs_entails b1 b2 ->
      cs_entails (cmerge a1 b1) (cmerge a2 b2).
  Proof.
    intros a1 a2 b1 b2 Ha Hb dlt H.
    apply listSatisfiable_cmerge in H as (H1 & H2).
    apply listSatisfiable_cmerge. split; [exact (Ha dlt H1)|exact (Hb dlt H2)].
  Qed.

  Lemma cs_entails_app :
    forall a1 a2 b1 b2,
      cs_entails a1 a2 -> cs_entails b1 b2 ->
      cs_entails (a1 ++ b1) (a2 ++ b2).
  Proof.
    intros a1 a2 b1 b2 Ha Hb dlt H.
    unfold listSatisfiable in *.
    apply Forall_app in H as (H1 & H2).
    apply Forall_app. split; [exact (Ha dlt H1)|exact (Hb dlt H2)].
  Qed.

  Lemma lst_entails_refl : forall t, lst_entails t t.
  Proof. intros t. split; [reflexivity|apply cs_entails_refl]. Qed.

  Lemma lst_entails_ljoin :
    forall a1 a2 b1 b2,
      lst_entails a1 a2 -> lst_entails b1 b2 ->
      lst_entails (ljoin a1 b1) (ljoin a2 b2).
  Proof.
    intros a1 a2 b1 b2 (Hfa & Hca) (Hfb & Hcb). split.
    - rewrite !fst_ljoin, Hfa, Hfb. reflexivity.
    - rewrite !snd_ljoin. exact (cs_entails_cmerge _ _ _ _ Hca Hcb).
  Qed.

  Lemma lconstrain_entails :
    forall p1 p2 b,
      lst_entails p1 p2 -> cs_entails (lconstrain p1 b) (lconstrain p2 b).
  Proof.
    intros p1 p2 b (Hf & Hc). unfold lconstrain. rewrite Hf.
    apply cs_entails_cmerge; [apply cs_entails_refl|exact Hc].
  Qed.

  Lemma lst_entails_fst :
    forall ts1 ts2,
      Forall2 lst_entails ts1 ts2 ->
      List.map fst ts1 = List.map fst ts2.
  Proof.
    induction 1 as [|t1 t2 ts1 ts2 (Hf & _) Hr IH]; simpl;
      [reflexivity|rewrite Hf, IH; reflexivity].
  Qed.

  Lemma carried_entails :
    forall ts1 ts2,
      Forall2 lst_entails ts1 ts2 -> cs_entails (carried ts1) (carried ts2).
  Proof.
    induction 1 as [|t1 t2 ts1 ts2 (_ & Hc) Hr IH];
      [apply cs_entails_refl|].
    rewrite !carried_cons. exact (cs_entails_cmerge _ _ _ _ Hc IH).
  Qed.

  (** Mapping a join over one side, on either side of the join: the shapes
      [Ewhen], [Emerge] and [Eite] produce. *)

  Lemma Forall2_map_ljoin_r :
    forall u1 u2 ts1 ts2,
      lst_entails u1 u2 -> Forall2 lst_entails ts1 ts2 ->
      Forall2 lst_entails (List.map (fun t => ljoin t u1) ts1)
                          (List.map (fun t => ljoin t u2) ts2).
  Proof.
    intros u1 u2 ts1 ts2 Hu H. induction H as [|t1 t2 ts1 ts2 Ht Hr IH];
      simpl; constructor; [exact (lst_entails_ljoin _ _ _ _ Ht Hu)|exact IH].
  Qed.

  Lemma Forall2_map_ljoin_l :
    forall u1 u2 ts1 ts2,
      lst_entails u1 u2 -> Forall2 lst_entails ts1 ts2 ->
      Forall2 lst_entails (List.map (fun t => ljoin u1 t) ts1)
                          (List.map (fun t => ljoin u2 t) ts2).
  Proof.
    intros u1 u2 ts1 ts2 Hu H. induction H as [|t1 t2 ts1 ts2 Ht Hr IH];
      simpl; constructor; [exact (lst_entails_ljoin _ _ _ _ Hu Ht)|exact IH].
  Qed.

  (** [single] and [ljoin_list] are state-pure and blind to the signature
      global, so both transport an entailment without any side condition. *)

  Lemma single_entails :
    forall ts1 ts2 t1 s s',
      Forall2 lst_entails ts1 ts2 ->
      single ts1 s = OK (t1, s') ->
      exists t2, single ts2 s = OK (t2, s) /\ lst_entails t1 t2.
  Proof.
    intros ts1 ts2 t1 s s' H Hs.
    apply single_inv in Hs as (? & ?); subst ts1 s'.
    inversion H as [|a b l1 l2 Hab Hl]; subst.
    inversion Hl; subst. exists b. split; [reflexivity|exact Hab].
  Qed.

  Lemma ljoin_list_entails :
    forall ts1 ts2 us1 us2 rs1 s s',
      Forall2 lst_entails ts1 ts2 ->
      Forall2 lst_entails us1 us2 ->
      ljoin_list ts1 us1 s = OK (rs1, s') ->
      exists rs2, ljoin_list ts2 us2 s = OK (rs2, s)
                  /\ Forall2 lst_entails rs1 rs2.
  Proof.
    intros ts1 ts2 us1 us2 rs1 s s' Ht.
    revert us1 us2 rs1 s s'.
    induction Ht as [|t1 t2 ts1 ts2 Ht12 Htr IH];
      intros us1 us2 rs1 s s' Hu H;
      destruct us1 as [|u1 vs1].
    - inversion Hu; subst us2.
      simpl in H. unfold SC.ret in H. inversion H; subst.
      exists []. split; [reflexivity|constructor].
    - simpl in H. unfold SC.error in H. discriminate H.
    - simpl in H. unfold SC.error in H. discriminate H.
    - inversion Hu as [|w1 u2 ws1 vs2 Hu12 Hur]; subst.
      simpl in H. apply sec_bind_inv in H as (r & sa & Hr & Hret).
      unfold SC.ret in Hret. inversion Hret; subst.
      destruct (IH vs1 vs2 r _ _ Hur Hr) as (r2 & Hr2 & Hre).
      exists (ljoin t2 u2 :: r2). split.
      + simpl. eapply sec_bind_ok; [exact Hr2|reflexivity].
      + constructor; [exact (lst_entails_ljoin _ _ _ _ Ht12 Hu12)|exact Hre].
  Qed.

  (** One layer of the call case, so that a target run can be *built* and not
      only taken apart.  [assign_lexp_Eapp_inv] does the taking apart; there
      is no companion for the other direction because no proof needed one
      until now. *)

  Lemma assign_lexp_Eapp_eq :
    forall G env base_ty rst_ty f es er anns,
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns)
      = (do argts <- assign_lexps G env base_ty rst_ty es;
         do rstty <- (match er with
                      | None => SC.ret (lvar rst_ty)
                      | Some e1 =>
                          do t1  <- assign_lexp_type G env base_ty rst_ty e1;
                          do a1  <- single t1;
                          do rck <- option_to_sec
                                      (assign_clk_type env base_ty
                                         (hd Cbase (LSyn.clockof e1)));
                          SC.ret (ljoin (lvar rst_ty) (ljoin a1 (rck, [])))
                      end);
         do ckty <- option_to_sec
                      (assign_clk_type env base_ty
                         (find_base_clock (LSyn.clocksof es)));
         match find_signature f G with
         | None => SC.error (MSG "Signature not found for: " :: [CTX f])
         | Some sg =>
             do outs <- fresh_idents (List.length anns);
             do cs   <- generate_constraints sg (List.map fst argts) ckty
                                             (fst rstty) outs;
             SC.ret (List.map
                    (fun o => (([o] : ST),
                               cmerge cs (cmerge (carried argts) (snd rstty))))
                    outs)
         end).
  Proof. reflexivity. Qed.

  (** A call's result names are pairwise distinct: [fresh_ident] mints at the
      state it is at and then moves past it, so the first name cannot be in
      the window the rest are minted in.  [generate_constraints_ok_from_good]
      asks for this, and nothing until now did. *)

  Lemma fresh_ident_notin_minted :
    forall x s s1 s',
      SC.fresh_ident s = OK (x, s1) -> ~ In x (minted s1 s').
  Proof.
    intros x s s1 s' H Hin.
    unfold SC.fresh_ident in H. inversion H; subst x s1.
    apply minted_spec in Hin as (j & Hle & _ & Hj).
    apply gensym_injective in Hj as (_ & ?); subst j.
    apply Pos.le_succ_l in Hle. exact (Pos.lt_irrefl s Hle).
  Qed.

  Lemma fresh_idents_NoDup :
    forall n xs s s', fresh_idents n s = OK (xs, s') -> NoDup xs.
  Proof.
    induction n as [|n IH]; intros xs s s' H; simpl in H.
    - unfold SC.ret in H. inversion H; subst. constructor.
    - apply sec_bind_inv in H as (x & s1 & Hx & H).
      apply sec_bind_inv in H as (ys & s2 & Hys & Hret).
      unfold SC.ret in Hret. inversion Hret; subst.
      constructor.
      + intro Hin.
        eapply fresh_ident_notin_minted; [exact Hx|].
        eapply fresh_idents_minted; [exact Hys|exact Hin].
      + eapply IH; exact Hys.
  Qed.

  (** [preserves_on] read at a fixed valuation.  When the target list is
      scoped to the same names the witness is allowed to move on, the witness
      can be carried back and the extension disappears. *)

  Lemma preserves_on_sat :
    forall scope a b,
      constraints_scoped scope b ->
      preserves_on scope a b ->
      cs_entails a b.
  Proof.
    intros scope a b Hsc Hp dlt Hsat.
    destruct (Hp dlt Hsat) as (dlt' & Hagree & Hsat').
    eapply listSatisfiable_ext; [exact Hsc| |exact Hsat'].
    intros x Hin. symmetry. exact (Hagree x Hin).
  Qed.

  (** The scope a call site can always offer: the actuals' own names.  Every
      side condition [signatures_preserved_equal_calls_from_good] asks for is
      then either trivial or exactly [call_subst_fresh]. *)

  Definition actuals_scope (inp : list ST) (ck rst : ST) (outs : list ident)
    : list ident := List.concat inp ++ ck ++ rst ++ outs.

  Lemma In_concat_intro :
    forall {A : Type} (x : A) (t : list A) (ls : list (list A)),
      In t ls -> In x t -> In x (List.concat ls).
  Proof.
    intros A x t ls. induction ls as [|l ls IH]; simpl; [contradiction|].
    intros [Hl|Hl] Hx;
      [subst l; apply in_or_app; now left
      |apply in_or_app; right; exact (IH Hl Hx)].
  Qed.

  Lemma actuals_scope_scoped :
    forall inp ck rst outs,
      call_subst_scoped (actuals_scope inp ck rst outs) inp ck rst outs.
  Proof.
    intros inp ck rst outs. unfold actuals_scope.
    unfold call_subst_scoped, call_actuals_scoped.
    split; [split; [|split]|].
    - apply Forall_forall. intros t Ht y Hy.
      apply in_or_app. left. exact (In_concat_intro y t inp Ht Hy).
    - intros y Hy. apply in_or_app. right. apply in_or_app. now left.
    - apply Forall_forall. intros y Hy.
      apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. now right.
    - intros y Hy. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. now left.
  Qed.

  Lemma actuals_scope_fresh :
    forall sg inp ck rst outs,
      call_subst_fresh sg inp ck rst outs ->
      scope_fresh (actuals_scope inp ck rst outs) sg.
  Proof.
    intros sg inp ck rst outs (Hinp & Hck & Hrst & Hout) x Hx.
    unfold actuals_scope in Hx.
    apply in_app_or in Hx as [Hx|Hx].
    { apply in_concat in Hx as (t & Ht & Hxt).
      unfold types_fresh in Hinp. rewrite Forall_forall in Hinp.
      unfold type_fresh in Hinp. specialize (Hinp t Hxt).
      rewrite Forall_forall in Hinp. exact (Hinp x Ht). }
    apply in_app_or in Hx as [Hx|Hx].
    { unfold type_fresh in Hck. rewrite Forall_forall in Hck.
      exact (Hck x Hx). }
    apply in_app_or in Hx as [Hx|Hx].
    { unfold type_fresh in Hrst. rewrite Forall_forall in Hrst.
      exact (Hrst x Hx). }
    unfold outputs_fresh in Hout. rewrite Forall_forall in Hout.
    exact (Hout x Hx).
  Qed.


  Lemma Forall2_map_pair :
    forall (h1 h2 : list constraint) (outs : list ident),
      cs_entails h1 h2 ->
      Forall2 lst_entails
        (List.map (fun o => (([o] : ST), h1)) outs)
        (List.map (fun o => (([o] : ST), h2)) outs).
  Proof.
    intros h1 h2 outs Hh. induction outs as [|o outs IH]; simpl; [constructor|].
    constructor; [split; [reflexivity|exact Hh]|exact IH].
  Qed.

  (** * The generator is monotone in its callees

      Reading the same expression against a weaker signature global gives the
      same types, in the same state, carrying weaker constraints.  The types
      and the state do not move because the only thing a signature's
      constraints reach is the block [generate_constraints] builds, and that
      block is state-pure and appears only in the *carried* component.  So the
      whole statement is a [Forall2] of [lst_entails]: equal on the left,
      entailed on the right. *)

  Section CalleeWeakening.

    Variable G1 G2   : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.

    (** Every callee is found on both sides, with the same interface and
        constraints the source's entail.  This is what the program-level
        lockstep carries, and what each node's signature preservation
        contributes to it. *)
    Hypothesis G_entails :
      forall f sg1,
        find_signature f G1 = Some sg1 ->
        exists sg2,
          find_signature f G2 = Some sg2
          /\ SIGPROOFS.signatures_preserved sg1 sg2.

    Hypothesis sig_good1 :
      forall f sg, find_signature f G1 = Some sg -> signature_good sg.
    Hypothesis sig_nodup1 :
      forall f sg, find_signature f G1 = Some sg -> NoDup (signature_scope sg).
    Hypothesis sig_good2 :
      forall f sg, find_signature f G2 = Some sg -> signature_good sg.
    Hypothesis sig_scoped2 :
      forall f sg, find_signature f G2 = Some sg -> signature_scoped sg.
    Hypothesis sig_actuals_fresh1 :
      forall f sg inp ck rst os cns sa sb,
        find_signature f G1 = Some sg ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    (** Stated, like [sig_actuals_fresh1], as a property of the
        instantiations the generator actually makes rather than of arbitrary
        actuals -- which is what makes it true.  A nested call's results are
        freshly minted, so distinct by [fresh_idents_NoDup]; an equation's are
        the security names of the variables it defines, so distinct because
        [env] is injective and a node defines each variable once. *)
    Hypothesis sig_out_nodup1 :
      forall f sg inp ck rst os cns sa sb,
        find_signature f G1 = Some sg ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        NoDup os.

    Local Notation T1  := (assign_lexp_type G1 env base_ty rst_ty).
    Local Notation T2  := (assign_lexp_type G2 env base_ty rst_ty).
    Local Notation Ts1 := (assign_lexps G1 env base_ty rst_ty).
    Local Notation Ts2 := (assign_lexps G2 env base_ty rst_ty).

    (** One call site.  The target block exists because the two signatures
        have the same interface, so every premise of
        [generate_constraints_ok_from_good] transfers; and it is entailed
        because an instantiated block is scoped to the actuals, which is all
        [preserves_on_sat] needs to drop the witness. *)
    Lemma call_block_entails_G :
      forall f sg1 inp ck rst outs cs1 st st1,
        find_signature f G1 = Some sg1 ->
        generate_constraints sg1 inp ck rst outs st = OK (cs1, st1) ->
        exists sg2 cs2,
          find_signature f G2 = Some sg2
          /\ generate_constraints sg2 inp ck rst outs st = OK (cs2, st)
          /\ cs_entails cs1 cs2.
    Proof.
      intros f sg1 inp ck rst outs cs1 st st1 Hf1 Hg1.
      pose proof (sig_out_nodup1 f sg1 inp ck rst outs cs1 st st1 Hf1 Hg1)
        as Hnd.
      destruct (G_entails f sg1 Hf1) as (sg2 & Hf2 & Hpres).
      pose proof Hpres as Hpres0. destruct Hpres0 as (Hfields & _).
      pose proof (signature_fields_agree_scope_eq _ _ Hfields) as Hscope.
      pose proof (sig_actuals_fresh1 f sg1 inp ck rst outs cs1 st st1 Hf1 Hg1)
        as Hfresh.
      destruct (SIGPROOFS.generate_constraints_lengths _ _ _ _ _ _ _ _ Hg1)
        as (Hleni & Hleno).
      pose proof Hfields as Hfields0.
      destruct Hfields0 as (Hin & Hout & Hrst & Hclk).
      destruct (SIGPROOFS.generate_constraints_ok_from_good sg2 inp ck rst outs st)
        as (cs2 & Hg2).
      { apply SIGPROOFS.signature_good_targets_out. exact (sig_good2 f sg2 Hf2). }
      { rewrite <- Hscope. exact (sig_nodup1 f sg1 Hf1). }
      { rewrite <- Hin. exact Hleni. }
      { rewrite <- Hout. exact Hleno. }
      { rewrite <- Hscope.
        destruct Hfresh as (_ & _ & _ & Ho). exact Ho. }
      { exact Hnd. }
      exists sg2, cs2. split; [exact Hf2|split; [exact Hg2|]].
      pose proof (actuals_scope_scoped inp ck rst outs) as Hsc.
      pose proof Hsc as Hsc0.
      destruct Hsc0 as ((Hsi & Hsc' & Hso) & Hsr).
      eapply preserves_on_sat with (scope := actuals_scope inp ck rst outs).
      - eapply generate_constraints_scoped;
          [exact (sig_scoped2 f sg2 Hf2)|exact Hsi|exact Hsc'|exact Hsr|exact Hso
          |exact Hg2].
      - eapply SIGPROOFS.signatures_preserved_equal_calls_from_good;
          [exact (sig_good1 f sg1 Hf1)
          |exact (sig_nodup1 f sg1 Hf1)
          |exact (sig_scoped2 f sg2 Hf2)
          |exact Hpres
          |exact (actuals_scope_fresh sg1 inp ck rst outs Hfresh)
          |exact Hsc
          |exact Hfresh
          |exact Hg1
          |exact Hg2].
    Qed.

    Definition lexp_entails_G (e : exp) : Prop :=
      forall ts1 s s1,
        T1 e s = OK (ts1, s1) ->
        exists ts2, T2 e s = OK (ts2, s1) /\ Forall2 lst_entails ts1 ts2.

    Lemma assign_lexps_entails_of :
      forall es,
        Forall lexp_entails_G es ->
        forall ts1 s s1,
          Ts1 es s = OK (ts1, s1) ->
          exists ts2, Ts2 es s = OK (ts2, s1) /\ Forall2 lst_entails ts1 ts2.
    Proof.
      intros es Hall. induction Hall as [|e es He Hes IH]; intros ts1 s s1 H.
      - rewrite assign_lexps_nil in H. unfold SC.ret in H. inversion H; subst.
        exists []. split; [rewrite assign_lexps_nil; reflexivity|constructor].
      - rewrite assign_lexps_cons in H.
        apply sec_bind_inv in H as (t & sa & Ht & H).
        apply sec_bind_inv in H as (r & sb & Hr & Hret).
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (He t _ _ Ht) as (t2 & Ht2 & Het).
        destruct (IH r _ _ Hr) as (r2 & Hr2 & Her).
        exists (t2 ++ r2). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [exact Ht2|].
          eapply sec_bind_ok; [exact Hr2|reflexivity].
        + apply Forall2_app; [exact Het|exact Her].
    Qed.

    Theorem assign_lexp_type_entails_G : forall e, lexp_entails_G e.
    Proof.
      intro e. induction e using exp_ind2.

      - (** Econst *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Econst in Hrun.
        unfold SC.ret in Hrun. inversion Hrun; subst.
        exists [lbot]. split;
          [rewrite assign_lexp_Econst; reflexivity
          |constructor; [apply lst_entails_refl|constructor]].

      - (** Evar *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Evar in Hrun.
        apply sec_bind_inv in Hrun as (b & sa & Hb & Hret).
        pose proof Hb as Hb0. apply find_env_inv in Hb0 as (_ & ?); subst sa.
        unfold SC.ret in Hret. inversion Hret; subst.
        exists [lvar b]. split.
        + rewrite assign_lexp_Evar.
          eapply sec_bind_ok; [exact Hb|reflexivity].
        + constructor; [apply lst_entails_refl|constructor].

      - (** Eunop *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Eunop in Hrun.
        destruct (IHe ts1 _ _ Hrun) as (ts2 & Ht2 & Hr).
        exists ts2. split; [rewrite assign_lexp_Eunop; exact Ht2|exact Hr].

      - (** Ebinop *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Ebinop in Hrun.
        apply sec_bind_inv in Hrun as (t1 & sa & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sb & Ht2 & Hrun).
        apply sec_bind_inv in Hrun as (a1 & sc & Ha1 & Hrun).
        pose proof Ha1 as Ha1'. apply single_inv in Ha1' as (_ & ?); subst sc.
        apply sec_bind_inv in Hrun as (a2 & sd & Ha2 & Hret).
        pose proof Ha2 as Ha2'. apply single_inv in Ha2' as (_ & ?); subst sd.
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (IHe1 t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (IHe2 t2 _ _ Ht2) as (u2 & Hu2 & Hr2).
        destruct (single_entails t1 u1 a1 _ _ Hr1 Ha1) as (b1 & Hb1 & Hrb1).
        destruct (single_entails t2 u2 a2 _ _ Hr2 Ha2) as (b2 & Hb2 & Hrb2).
        exists [ljoin b1 b2]. split.
        + rewrite assign_lexp_Ebinop.
          eapply sec_bind_ok; [exact Hu1|].
          eapply sec_bind_ok; [exact Hu2|].
          eapply sec_bind_ok; [exact Hb1|].
          eapply sec_bind_ok; [exact Hb2|reflexivity].
        + constructor;
            [exact (lst_entails_ljoin _ _ _ _ Hrb1 Hrb2)|constructor].

      - (** Efby *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Efby in Hrun.
        apply sec_bind_inv in Hrun as (t1 & sa & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sb & Ht2 & Hj).
        assert (s1 = sb) as Hsb by (eapply ljoin_list_pure; exact Hj).
        subst s1.
        destruct (assign_lexps_entails_of e0s H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (assign_lexps_entails_of es H0 t2 _ _ Ht2) as (u2 & Hu2 & Hr2).
        destruct (ljoin_list_entails t1 u1 t2 u2 ts1 _ _ Hr1 Hr2 Hj)
          as (rs2 & Hrs2 & Hre).
        exists rs2. split; [|exact Hre].
        rewrite assign_lexp_Efby.
        eapply sec_bind_ok; [exact Hu1|].
        eapply sec_bind_ok; [exact Hu2|exact Hrs2].

      - (** Earrow: the same body *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Earrow in Hrun.
        apply sec_bind_inv in Hrun as (t1 & sa & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sb & Ht2 & Hj).
        assert (s1 = sb) as Hsb by (eapply ljoin_list_pure; exact Hj).
        subst s1.
        destruct (assign_lexps_entails_of e0s H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (assign_lexps_entails_of es H0 t2 _ _ Ht2) as (u2 & Hu2 & Hr2).
        destruct (ljoin_list_entails t1 u1 t2 u2 ts1 _ _ Hr1 Hr2 Hj)
          as (rs2 & Hrs2 & Hre).
        exists rs2. split; [|exact Hre].
        rewrite assign_lexp_Earrow.
        eapply sec_bind_ok; [exact Hu1|].
        eapply sec_bind_ok; [exact Hu2|exact Hrs2].

      - (** Ewhen *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Ewhen in Hrun.
        apply sec_bind_inv in Hrun as (t1 & sa & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (g & sb & Hg & Hret).
        pose proof Hg as Hg0. apply find_env_inv in Hg0 as (_ & ?); subst sb.
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (assign_lexps_entails_of es H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        exists (List.map (fun t => ljoin t (lvar g)) u1). split.
        + rewrite assign_lexp_Ewhen.
          eapply sec_bind_ok; [exact Hu1|].
          eapply sec_bind_ok; [exact Hg|reflexivity].
        + apply Forall2_map_ljoin_r; [apply lst_entails_refl|exact Hr1].

      - (** Emerge *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Emerge in Hrun.
        apply sec_bind_inv in Hrun as (g & sa & Hg & Hrun).
        pose proof Hg as Hg0. apply find_env_inv in Hg0 as (_ & ?); subst sa.
        apply sec_bind_inv in Hrun as (t1 & sb & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sc & Ht2 & Hj).
        assert (s1 = sc) as Hsc by (eapply ljoin_list_pure; exact Hj).
        subst s1.
        destruct (assign_lexps_entails_of ets H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (assign_lexps_entails_of efs H0 t2 _ _ Ht2) as (u2 & Hu2 & Hr2).
        destruct (ljoin_list_entails
                    (List.map (fun t => ljoin (lvar g) t) t1)
                    (List.map (fun t => ljoin (lvar g) t) u1)
                    t2 u2 ts1 _ _
                    (Forall2_map_ljoin_l _ _ _ _ (lst_entails_refl (lvar g)) Hr1)
                    Hr2 Hj)
          as (rs2 & Hrs2 & Hre).
        exists rs2. split; [|exact Hre].
        rewrite assign_lexp_Emerge.
        eapply sec_bind_ok; [exact Hg|].
        eapply sec_bind_ok; [exact Hu1|].
        eapply sec_bind_ok; [exact Hu2|exact Hrs2].

      - (** Eite *)
        intros ts1 s s1 Hrun. rewrite assign_lexp_Eite in Hrun.
        apply sec_bind_inv in Hrun as (t0 & sa & Ht0 & Hrun).
        apply sec_bind_inv in Hrun as (th & sb & Hth & Hrun).
        pose proof Hth as Hth0. apply single_inv in Hth0 as (_ & ?); subst sb.
        apply sec_bind_inv in Hrun as (t1 & sc & Ht1 & Hrun).
        apply sec_bind_inv in Hrun as (t2 & sd & Ht2 & Hj).
        assert (s1 = sd) as Hsd by (eapply ljoin_list_pure; exact Hj).
        subst s1.
        destruct (IHe t0 _ _ Ht0) as (u0 & Hu0 & Hr0).
        destruct (single_entails t0 u0 th _ _ Hr0 Hth) as (vh & Hvh & Hrh).
        destruct (assign_lexps_entails_of ets H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (assign_lexps_entails_of efs H0 t2 _ _ Ht2) as (u2 & Hu2 & Hr2).
        destruct (ljoin_list_entails
                    (List.map (fun t => ljoin th t) t1)
                    (List.map (fun t => ljoin vh t) u1)
                    t2 u2 ts1 _ _
                    (Forall2_map_ljoin_l _ _ _ _ Hrh Hr1) Hr2 Hj)
          as (rs2 & Hrs2 & Hre).
        exists rs2. split; [|exact Hre].
        rewrite assign_lexp_Eite.
        eapply sec_bind_ok; [exact Hu0|].
        eapply sec_bind_ok; [exact Hvh|].
        eapply sec_bind_ok; [exact Hu1|].
        eapply sec_bind_ok; [exact Hu2|exact Hrs2].

      - (** Eapp: the only case a signature is read at *)
        intros ts1 s s1 Hrun.
        apply assign_lexp_Eapp_inv in Hrun
          as (sg1 & argts & rstty & ckty & outs & cs & sta & stb & stc
              & Hargs & Hck & Hrst & Hsg1 & Houts & Hcs & Hts1).
        (** the state is fixed by the block being state-pure *)
        assert (s1 = stc) as Hstc.
        { destruct (state_pure_generate_constraints sg1 (List.map fst argts)
                      ckty (fst rstty) outs stc stc cs s1 Hcs) as (Hq & _).
          exact Hq. }
        subst s1.
        (** the arguments *)
        destruct (assign_lexps_entails_of es H0 argts _ _ Hargs)
          as (argts2 & Hargs2 & Hra).
        (** the reset actual, built as a run *)
        assert (exists rstty2,
                   (match ro with
                    | None => SC.ret (lvar rst_ty)
                    | Some e1 =>
                        do t1  <- T2 e1;
                        do a1  <- single t1;
                        do rck <- option_to_sec
                                    (assign_clk_type env base_ty
                                       (hd Cbase (LSyn.clockof e1)));
                        SC.ret (ljoin (lvar rst_ty) (ljoin a1 (rck, [])))
                    end) sta = OK (rstty2, stb)
                   /\ lst_entails rstty rstty2)
          as (rstty2 & Hrst2 & Hrr).
        { destruct ro as [e1|].
          - destruct Hrst as (t1 & a1 & rck & stm & Ht1 & Ha1 & Hrck & Hre).
            pose proof Ha1 as Ha1'. apply single_inv in Ha1' as (_ & ?); subst stb.
            destruct (H t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
            destruct (single_entails t1 u1 a1 _ _ Hr1 Ha1) as (b1 & Hb1 & Hrb1).
            exists (ljoin (lvar rst_ty) (ljoin b1 (rck, []))). split.
            + eapply sec_bind_ok; [exact Hu1|].
              eapply sec_bind_ok; [exact Hb1|].
              eapply sec_bind_ok; [rewrite Hrck; reflexivity|reflexivity].
            + subst rstty. apply lst_entails_ljoin; [apply lst_entails_refl|].
              apply lst_entails_ljoin; [exact Hrb1|apply lst_entails_refl].
          - destruct Hrst as (Hre & ?); subst rstty stb.
            exists (lvar rst_ty).
            split; [reflexivity|apply lst_entails_refl]. }
        (** the actuals coincide, so the two blocks are instantiated alike *)
        pose proof (lst_entails_fst _ _ Hra) as Hfa.
        pose proof Hrr as Hrr0. destruct Hrr0 as (Hfr & Hcr).
        destruct (call_block_entails_G f sg1 (List.map fst argts) ckty
                    (fst rstty) outs cs stc stc Hsg1 Hcs)
          as (sg2 & cs2 & Hsg2 & Hg2 & Hce).
        exists (List.map
                  (fun o => (([o] : ST),
                             cmerge cs2 (cmerge (carried argts2) (snd rstty2))))
                  outs).
        split.
        + rewrite assign_lexp_Eapp_eq.
          eapply sec_bind_ok; [exact Hargs2|].
          eapply sec_bind_ok; [exact Hrst2|].
          eapply sec_bind_ok; [rewrite Hck; reflexivity|].
          rewrite Hsg2.
          eapply sec_bind_ok; [exact Houts|].
          eapply sec_bind_ok; [rewrite <- Hfa, <- Hfr; exact Hg2|reflexivity].
        + subst ts1. apply Forall2_map_pair.
          apply cs_entails_cmerge; [exact Hce|].
          apply cs_entails_cmerge; [exact (carried_entails _ _ Hra)|exact Hcr].
    Qed.

    Corollary assign_lexps_entails_G :
      forall es ts1 s s1,
        Ts1 es s = OK (ts1, s1) ->
        exists ts2, Ts2 es s = OK (ts2, s1) /\ Forall2 lst_entails ts1 ts2.
    Proof.
      intros es ts1 s s1 H.
      eapply assign_lexps_entails_of; [|exact H].
      apply Forall_forall. intros e _. exact (assign_lexp_type_entails_G e).
    Qed.


    (** * The same, for the constraint generator

        [eqn_clock_type], [find_env] and [get_mappings] never look at a
        signature, so every rule's only sensitive parts are the expression
        runs it makes and, at a call, the block it instantiates.  Each rule
        therefore transports the entailment by [cs_entails_app] and
        [lconstrain_entails], and the two runs still finish in the same
        state. *)

    Variable cenv : Env.t (type * clock).

    Lemma gen_lvars_cons_eq :
      forall x xs b bs t ts,
        generate_lvars_constraints env base_ty rst_ty cenv
          (x :: xs) (b :: bs) (t :: ts)
        = (do ckty <- eqn_clock_type env base_ty cenv x;
           do rest <- generate_lvars_constraints env base_ty rst_ty cenv xs bs ts;
           SC.ret (lconstrain (ljoin (ambient rst_ty ckty) t) b ++ rest)).
    Proof. reflexivity. Qed.

    Lemma generate_lvars_constraints_entails_G :
      forall xs bs ts1 ts2 cs1 s s1,
        Forall2 lst_entails ts1 ts2 ->
        generate_lvars_constraints env base_ty rst_ty cenv xs bs ts1 s
          = OK (cs1, s1) ->
        exists cs2,
          generate_lvars_constraints env base_ty rst_ty cenv xs bs ts2 s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      induction xs as [|x xs IH]; intros bs ts1 ts2 cs1 s s1 Hts H;
        destruct bs as [|b bs]; destruct ts1 as [|t ts1];
        simpl in H; try (unfold SC.error in H; discriminate H).
      - inversion Hts; subst ts2. unfold SC.ret in H. inversion H; subst.
        exists []. split; [reflexivity|apply cs_entails_refl].
      - inversion Hts as [|t' u ts1' us Htu Htr]; subst.
        apply sec_bind_inv in H as (ckty & sa & Hck & H).
        apply sec_bind_inv in H as (rest & sb & Hrest & Hret).
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (IH bs ts1 us rest _ _ Htr Hrest) as (rest2 & Hrest2 & Hre).
        exists (lconstrain (ljoin (ambient rst_ty ckty) u) b ++ rest2). split.
        + rewrite gen_lvars_cons_eq.
          eapply sec_bind_ok; [exact Hck|].
          eapply sec_bind_ok; [exact Hrest2|reflexivity].
        + apply cs_entails_app; [|exact Hre].
          apply lconstrain_entails, lst_entails_ljoin;
            [apply lst_entails_refl|exact Htu].
    Qed.

    Lemma generate_ldef_constraint_entails_G :
      forall x e cs1 s s1,
        generate_ldef_constraint G1 env base_ty rst_ty cenv x e s = OK (cs1, s1) ->
        exists cs2,
          generate_ldef_constraint G2 env base_ty rst_ty cenv x e s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      intros x e cs1 s s1 H. unfold generate_ldef_constraint in H |- *.
      apply sec_bind_inv in H as (ckty & sa & Hck & H).
      apply sec_bind_inv in H as (ts & sb & Hts & H).
      apply sec_bind_inv in H as (t & sc & Ht & H).
      pose proof Ht as Ht'. apply single_inv in Ht' as (_ & ?); subst sc.
      apply sec_bind_inv in H as (b & sd & Hb & Hret).
      pose proof Hb as Hb'. apply find_env_inv in Hb' as (_ & ?); subst sd.
      unfold SC.ret in Hret. inversion Hret; subst.
      destruct (assign_lexp_type_entails_G e ts _ _ Hts) as (us & Hus & Hre).
      destruct (single_entails ts us t _ _ Hre Ht) as (u & Hu & Hru).
      exists (lconstrain (ljoin (ambient rst_ty ckty) u) b). split.
      + eapply sec_bind_ok; [exact Hck|].
        eapply sec_bind_ok; [exact Hus|].
        eapply sec_bind_ok; [exact Hu|].
        eapply sec_bind_ok; [exact Hb|reflexivity].
      + apply lconstrain_entails, lst_entails_ljoin;
          [apply lst_entails_refl|exact Hru].
    Qed.

    Lemma generate_lcall_constraint_entails_G :
      forall xs f es rstty1 rstty2 cs1 s s1,
        lst_entails rstty1 rstty2 ->
        generate_lcall_constraint G1 env base_ty rst_ty xs f es rstty1 s
          = OK (cs1, s1) ->
        exists cs2,
          generate_lcall_constraint G2 env base_ty rst_ty xs f es rstty2 s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      intros xs f es rstty1 rstty2 cs1 s s1 Hr H.
      unfold generate_lcall_constraint in H |- *.
      destruct (find_signature f G1) as [sg1|] eqn:Esg1;
        [|unfold SC.error in H; discriminate H].
      apply sec_bind_inv in H as (ckty & sa & Hck & H).
      pose proof Hck as Hck'.
      apply option_to_sec_inv in Hck' as (Hckv & ?); subst sa.
      apply sec_bind_inv in H as (argts & sb & Hargs & H).
      apply sec_bind_inv in H as (outs & sc & Houts & H).
      assert (Hpure : state_pure (SC.mmap (fun x => find_env x env) xs))
        by (apply state_pure_mmap; intros; apply state_pure_find_env).
      pose proof Houts as Houts'.
      destruct (Hpure sb sb _ _ Houts') as (? & _); subst sc.
      apply sec_bind_inv in H as (cs0 & sd & Hgc & Hret).
      assert (sd = sb) as Hsd.
      { destruct (state_pure_generate_constraints sg1 (List.map fst argts) ckty
                    (fst rstty1) outs sb sb cs0 sd Hgc) as (Hq & _).
        exact Hq. }
      subst sd.
      unfold SC.ret in Hret. inversion Hret; subst.
      destruct (assign_lexps_entails_G es argts _ _ Hargs)
        as (argts2 & Hargs2 & Hra).
      pose proof (lst_entails_fst _ _ Hra) as Hfa.
      pose proof Hr as Hr0. destruct Hr0 as (Hfr & Hcr).
      destruct (call_block_entails_G f sg1 (List.map fst argts) ckty
                  (fst rstty1) outs cs0 _ _ Esg1 Hgc)
        as (sg2 & cs2 & Esg2 & Hgc2 & Hce).
      rewrite Esg2.
      exists (cmerge cs2 (cmerge (carried argts2) (snd rstty2))). split.
      + eapply sec_bind_ok; [exact Hck|].
        eapply sec_bind_ok; [exact Hargs2|].
        eapply sec_bind_ok; [exact Houts|].
        eapply sec_bind_ok; [rewrite <- Hfa, <- Hfr; exact Hgc2|reflexivity].
      + apply cs_entails_cmerge; [exact Hce|].
        apply cs_entails_cmerge; [exact (carried_entails _ _ Hra)|exact Hcr].
    Qed.

    Lemma generate_lgen_constraint_entails_G :
      forall xs es cs1 s s1,
        generate_lgen_constraint G1 env base_ty rst_ty cenv xs es s
          = OK (cs1, s1) ->
        exists cs2,
          generate_lgen_constraint G2 env base_ty rst_ty cenv xs es s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      intros xs es cs1 s s1 H.
      unfold generate_lgen_constraint in H |- *.
      apply sec_bind_inv in H as (ts & sa & Hts & H).
      apply sec_bind_inv in H as (bs & sb & Hbs & H).
      pose proof Hbs as Hbs'.
      apply option_to_sec_inv in Hbs' as (_ & ?); subst sb.
      destruct (assign_lexps_entails_G es ts _ _ Hts) as (us & Hus & Hre).
      destruct (generate_lvars_constraints_entails_G xs bs ts us cs1 _ _ Hre H)
        as (cs2 & Hcs2 & Hce).
      exists cs2. split; [|exact Hce].
      eapply sec_bind_ok; [exact Hus|].
      eapply sec_bind_ok; [exact Hbs|exact Hcs2].
    Qed.

    Lemma generate_lone_constraint_entails_G :
      forall ys e cs1 s s1,
        generate_lone_constraint G1 env base_ty rst_ty cenv ys e s
          = OK (cs1, s1) ->
        exists cs2,
          generate_lone_constraint G2 env base_ty rst_ty cenv ys e s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      intros ys e cs1 s s1 H.
      destruct e as [| | | | | | | | |f args ro a].
      1-9: (destruct ys as [|x [|x2 xs2]];
            [ eapply generate_lgen_constraint_entails_G; exact H
            | eapply generate_ldef_constraint_entails_G; exact H
            | eapply generate_lgen_constraint_entails_G; exact H ]).
      destruct ro as [e1|]; destruct ys as [|x xs2].
      - unfold generate_lone_constraint, SC.ret in H |- *. inversion H; subst.
        exists []. split; [reflexivity|apply cs_entails_refl].
      - unfold generate_lone_constraint in H |- *.
        apply sec_bind_inv in H as (t1 & sa & Ht1 & H).
        apply sec_bind_inv in H as (a1 & sb & Ha1 & H).
        pose proof Ha1 as Ha1'. apply single_inv in Ha1' as (_ & ?); subst sb.
        apply sec_bind_inv in H as (rck & sc & Hrck & H).
        pose proof Hrck as Hrck'.
        apply option_to_sec_inv in Hrck' as (_ & ?); subst sc.
        destruct (assign_lexp_type_entails_G e1 t1 _ _ Ht1) as (u1 & Hu1 & Hr1).
        destruct (single_entails t1 u1 a1 _ _ Hr1 Ha1) as (b1 & Hb1 & Hrb1).
        destruct (generate_lcall_constraint_entails_G (x :: xs2) f args
                    (ljoin (lvar rst_ty) (ljoin a1 (rck, [])))
                    (ljoin (lvar rst_ty) (ljoin b1 (rck, [])))
                    cs1 _ _
                    (lst_entails_ljoin _ _ _ _ (lst_entails_refl (lvar rst_ty))
                       (lst_entails_ljoin _ _ _ _ Hrb1
                          (lst_entails_refl (rck, []))))
                    H)
          as (cs2 & Hcs2 & Hce).
        exists cs2. split; [|exact Hce].
        eapply sec_bind_ok; [exact Hu1|].
        eapply sec_bind_ok; [exact Hb1|].
        eapply sec_bind_ok; [exact Hrck|exact Hcs2].
      - unfold generate_lone_constraint, SC.ret in H |- *. inversion H; subst.
        exists []. split; [reflexivity|apply cs_entails_refl].
      - eapply generate_lcall_constraint_entails_G;
          [apply lst_entails_refl|exact H].
    Qed.

    Lemma generate_lsplit_constraints_entails_G :
      forall es xs cs1 s s1,
        generate_lsplit_constraints G1 env base_ty rst_ty cenv xs es s
          = OK (cs1, s1) ->
        exists cs2,
          generate_lsplit_constraints G2 env base_ty rst_ty cenv xs es s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      induction es as [|e es IH]; intros xs cs1 s s1 H.
      - rewrite gen_lsplit_nil in H. unfold SC.ret in H. inversion H; subst.
        exists []. split;
          [rewrite gen_lsplit_nil; reflexivity|apply cs_entails_refl].
      - rewrite gen_lsplit_cons in H.
        apply sec_bind_inv in H as (ch & sa & Hh & H).
        apply sec_bind_inv in H as (ct & sb & Ht & Hret).
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (generate_lone_constraint_entails_G
                    (firstn (numstreams e) xs) e ch _ _ Hh)
          as (ch2 & Hh2 & Hceh).
        destruct (IH (skipn (numstreams e) xs) ct _ _ Ht) as (ct2 & Ht2 & Hcet).
        exists (ch2 ++ ct2). split.
        + rewrite gen_lsplit_cons.
          eapply sec_bind_ok; [exact Hh2|].
          eapply sec_bind_ok; [exact Ht2|reflexivity].
        + apply cs_entails_app; [exact Hceh|exact Hcet].
    Qed.

    Lemma generate_leqn_constraint_entails_G :
      forall eq cs1 s s1,
        generate_leqn_constraint G1 env base_ty rst_ty cenv eq s = OK (cs1, s1) ->
        exists cs2,
          generate_leqn_constraint G2 env base_ty rst_ty cenv eq s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      intros (xs, es) cs1 s s1 H.
      destruct es as [|e [|e2 es2]].
      - eapply generate_lgen_constraint_entails_G; exact H.
      - rewrite <- generate_lone_is_leqn in H.
        destruct (generate_lone_constraint_entails_G xs e cs1 _ _ H)
          as (cs2 & Hcs2 & Hce).
        exists cs2. split; [rewrite <- generate_lone_is_leqn; exact Hcs2|exact Hce].
      - rewrite gen_leqn_cons2 in H. rewrite gen_leqn_cons2.
        destruct (has_lcall (e :: e2 :: es2));
          [eapply generate_lsplit_constraints_entails_G
          |eapply generate_lgen_constraint_entails_G]; exact H.
    Qed.

    (** The statement the program level reads: a node's raw constraints,
        generated against the source accumulator, entail the ones generated
        against the weaker one -- at the same valuation, and finishing in the
        same state, so the two [simplify] windows coincide as well. *)
    Theorem generate_leqns_constraints_entails_G :
      forall eqs cs1 s s1,
        generate_leqns_constraints G1 env base_ty rst_ty cenv eqs s
          = OK (cs1, s1) ->
        exists cs2,
          generate_leqns_constraints G2 env base_ty rst_ty cenv eqs s
            = OK (cs2, s1)
          /\ cs_entails cs1 cs2.
    Proof.
      induction eqs as [|eq eqs IH]; intros cs1 s s1 H.
      - apply generate_leqns_constraints_nil in H as (? & ?); subst.
        exists []. split; [reflexivity|apply cs_entails_refl].
      - rewrite generate_leqns_constraints_cons in H.
        apply sec_bind_inv in H as (ch & sa & Hh & H).
        apply sec_bind_inv in H as (ct & sb & Ht & Hret).
        unfold SC.ret in Hret. inversion Hret; subst.
        destruct (generate_leqn_constraint_entails_G eq ch _ _ Hh)
          as (ch2 & Hh2 & Hceh).
        destruct (IH ct _ _ Ht) as (ct2 & Ht2 & Hcet).
        exists (ch2 ++ ct2). split.
        + rewrite generate_leqns_constraints_cons.
          eapply sec_bind_ok; [exact Hh2|].
          eapply sec_bind_ok; [exact Ht2|reflexivity].
        + apply cs_entails_app; [exact Hceh|exact Hcet].
    Qed.
  End CalleeWeakening.

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
