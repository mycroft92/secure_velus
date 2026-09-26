(** Pointwise ambient infrastructure for multi-stream unnesting. *)

From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Lia.

From Velus Require Import Common Environment Operators Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import CoreExpr.CESyntax CoreExpr.CEIsFree CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax Transcription.Tr.
From Velus Require Import SIF.Helpers SIF.SecLattice SIF.SymTypes.
From Velus Require Import SIF.SecTypes SIF.SecLusTypes SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping SIF.SecContext SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature SIF.NameInterface SIF.SecLTyping.
From Velus Require Import SIF.SecLusUnnestingCalls.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module SecLusUnnestingStreams
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

Module CALLS := SecLusUnnestingCalls Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include CALLS.

Import SECMONADNotations.

(** The pointwise replacement for the scalar relation used by the original
    expression proof.  All three lists have the same length by construction:
    the ambient at a position belongs only to that source/target stream. *)
Definition stream_rel
    (dlt : ident -> Lat.t) (ambs : list ST) (srcs tgts : list LST) : Prop :=
  Forall3
    (fun a src tgt => satisfiable dlt (fst tgt) (merge a (fst src)))
    ambs srcs tgts.

Definition stream_bounds
    (dlt : ident -> Lat.t) (ambs : list ST) (bs : list ident) : Prop :=
  Forall2 (fun a b => satisfiable dlt a [b]) ambs bs.

Definition stream_ambients_scoped (scope : list ident) (ambs : list ST) : Prop :=
  Forall (st_scoped scope) ambs.

Definition carries_result_streams
    (scope moved : list ident) (ambs : list ST) (srcs tgts : list LST)
    (ce : list constraint) (dlt dlt' : ident -> Lat.t) : Prop :=
  CALLS.agree_off moved dlt dlt'
  /\ listSatisfiable dlt' ce
  /\ stream_rel dlt' ambs srcs tgts
  /\ constraints_scoped (scope ++ moved) ce
  /\ Forall (fun tgt => st_scoped (scope ++ moved) (fst tgt)) tgts.

Lemma stream_rel_lengths :
  forall dlt ambs srcs tgts,
    stream_rel dlt ambs srcs tgts ->
    List.length ambs = List.length srcs
    /\ List.length srcs = List.length tgts.
Proof.
  intros dlt ambs srcs tgts Hrel.
  exact (Forall3_length _ ambs srcs tgts Hrel).
Qed.

(** * Weakening the per-stream ambients

    The streams contract is *contravariant* in its ambients: a larger ambient
    makes the relation easier.  That is what lets the call case establish its
    results at the call's single ambient -- which is all
    [generate_constraints_mono_sem] produces -- and then read them off at each
    result's own, since the call's is inside every one of them
    ([call_amb_below_result_ambients]). *)

Lemma stream_rel_amb_weaken :
  forall dlt ambs1 ambs2 srcs tgts,
    Forall2 (fun a1 a2 => incl a1 a2) ambs1 ambs2 ->
    stream_rel dlt ambs1 srcs tgts ->
    stream_rel dlt ambs2 srcs tgts.
Proof.
  intros dlt ambs1 ambs2 srcs tgts Hincl Hrel.
  revert ambs2 Hincl.
  induction Hrel as [|a src tgt as0 ss ts Hr Hrest IH];
    intros ambs2 Hincl.
  - inversion Hincl; subst. constructor.
  - inversion Hincl as [|a1 a2 l1 l2 Ha Hl]; subst.
    constructor; [|exact (IH l2 Hl)].
    eapply satisfiable_trans; [exact Hr|].
    apply satisfiable_of_incl. intros z Hz.
    apply in_merge_inv in Hz as [Hz|Hz];
      [apply in_merge_left; exact (Ha z Hz)|now apply in_merge_right].
Qed.

Corollary stream_rel_amb_weaken_all :
  forall dlt a ambs srcs tgts,
    Forall (fun a2 => incl a a2) ambs ->
    List.length ambs = List.length srcs ->
    stream_rel dlt (List.map (fun _ => a) ambs) srcs tgts ->
    stream_rel dlt ambs srcs tgts.
Proof.
  intros dlt a ambs srcs tgts Hall Hlen Hrel.
  eapply stream_rel_amb_weaken; [|exact Hrel].
  clear Hlen Hrel. induction Hall as [|a2 ambs0 Ha Hr IH];
    [constructor|constructor; [exact Ha|exact IH]].
Qed.

Lemma stream_rel_refl :
  forall dlt ambs ts,
    List.length ambs = List.length ts ->
    stream_rel dlt ambs ts ts.
Proof.
  intros dlt ambs. induction ambs as [|a ambs IH]; intros ts Hlen.
  - destruct ts; [constructor|discriminate].
  - destruct ts as [|t ts]; [discriminate|].
    simpl in Hlen. injection Hlen as Hlenr.
    constructor.
    + apply satisfiable_merge_r.
    + exact (IH ts Hlenr).
Qed.

Lemma stream_rel_constant :
  forall dlt amb srcs tgts,
    Forall2
      (fun src tgt => satisfiable dlt (fst tgt) (merge amb (fst src)))
      srcs tgts ->
    stream_rel dlt (repeat amb (List.length srcs)) srcs tgts.
Proof.
  intros dlt amb srcs tgts Hrel.
  induction Hrel as [|src tgt srcs tgts Hhead Htail IH].
  - constructor.
  - simpl. constructor; assumption.
Qed.

Lemma stream_bounds_constant :
  forall dlt amb bs,
    Forall (fun b => satisfiable dlt amb [b]) bs ->
    stream_bounds dlt (repeat amb (List.length bs)) bs.
Proof.
  intros dlt amb bs Hbounds.
  induction Hbounds as [|b bs Hhead Htail IH].
  - constructor.
  - simpl. constructor; assumption.
Qed.

Lemma stream_ambients_scoped_constant :
  forall scope amb n,
    st_scoped scope amb ->
    stream_ambients_scoped scope (repeat amb n).
Proof.
  intros scope amb n Hsc. induction n as [|n IH].
  - constructor.
  - simpl. constructor; assumption.
Qed.

Lemma stream_rel_app :
  forall dlt ambs1 ambs2 srcs1 srcs2 tgts1 tgts2,
    stream_rel dlt ambs1 srcs1 tgts1 ->
    stream_rel dlt ambs2 srcs2 tgts2 ->
    stream_rel dlt (ambs1 ++ ambs2) (srcs1 ++ srcs2) (tgts1 ++ tgts2).
Proof.
  intros dlt ambs1 ambs2 srcs1 srcs2 tgts1 tgts2 Hrel1 Hrel2.
  induction Hrel1 as [|a src tgt ambs srcs tgts Hhead Htail IH].
  - exact Hrel2.
  - simpl. constructor; assumption.
Qed.

Lemma stream_bounds_app :
  forall dlt ambs1 ambs2 bs1 bs2,
    stream_bounds dlt ambs1 bs1 ->
    stream_bounds dlt ambs2 bs2 ->
    stream_bounds dlt (ambs1 ++ ambs2) (bs1 ++ bs2).
Proof.
  intros dlt ambs1 ambs2 bs1 bs2 Hbounds1 Hbounds2.
  apply Forall2_app; assumption.
Qed.

Lemma stream_rel_off_scope :
  forall scope moved dlt dlt' ambs srcs tgts,
    stream_ambients_scoped scope ambs ->
    Forall (fun src => st_scoped scope (fst src)) srcs ->
    Forall (fun tgt => st_scoped scope (fst tgt)) tgts ->
    (forall x, In x moved -> ~ In x scope) ->
    CALLS.agree_off moved dlt dlt' ->
    stream_rel dlt ambs srcs tgts ->
    stream_rel dlt' ambs srcs tgts.
Proof.
  intros scope moved dlt dlt' ambs srcs tgts
    Hambs Hsrcs Htgts Hfresh Hoff Hrel.
  apply
    (@Forall3_impl_In ST LST LST
       (fun a src tgt =>
          satisfiable dlt (fst tgt) (merge a (fst src)))
       (fun a src tgt =>
          satisfiable dlt' (fst tgt) (merge a (fst src)))
       ambs srcs tgts).
  - intros a src tgt Ha Hsrc Htgt Hsat.
    pose proof Hambs as Hambs_all.
    pose proof Hsrcs as Hsrcs_all.
    pose proof Htgts as Htgts_all.
    unfold stream_ambients_scoped in Hambs_all.
    rewrite Forall_forall in Hambs_all.
    rewrite Forall_forall in Hsrcs_all.
    rewrite Forall_forall in Htgts_all.
    assert (forall x, In x (fst tgt) -> ~ In x moved) as Hleft.
    { intros x Hx Hmoved.
      exact (Hfresh x Hmoved (Htgts_all tgt Htgt x Hx)). }
    assert
      (forall x, In x (merge a (fst src)) -> ~ In x moved) as Hright.
    { intros x Hx Hmoved. apply in_merge_inv in Hx as [Hx|Hx].
      - exact (Hfresh x Hmoved (Hambs_all a Ha x Hx)).
      - exact (Hfresh x Hmoved (Hsrcs_all src Hsrc x Hx)). }
    exact
      (CALLS.satisfiable_off
         (fst tgt) (merge a (fst src)) moved dlt dlt'
         Hoff Hleft Hright Hsat).
  - exact Hrel.
Qed.

Lemma carries_result_streams_constant :
  forall scope moved amb srcs tgts ce dlt dlt',
    CALLS.agree_off moved dlt dlt' ->
    listSatisfiable dlt' ce ->
    Forall2
      (fun src tgt =>
         satisfiable dlt' (fst tgt) (merge amb (fst src)))
      srcs tgts ->
    constraints_scoped (scope ++ moved) ce ->
    Forall (fun tgt => st_scoped (scope ++ moved) (fst tgt)) tgts ->
    carries_result_streams scope moved
      (repeat amb (List.length srcs)) srcs tgts ce dlt dlt'.
Proof.
  intros scope moved amb srcs tgts ce dlt dlt'
    Hoff Hsat Hrel Hscoped Htgts.
  unfold carries_result_streams. repeat split; try assumption.
  exact (stream_rel_constant dlt' amb srcs tgts Hrel).
Qed.

Lemma carries_unchanged_streams :
  forall scope moved ambs (ts ts' : list LST) ce dlt,
    ts' = ts ->
    ce = [] ->
    List.length ambs = List.length ts ->
    Forall (fun t => st_scoped scope (fst t)) ts ->
    exists dlt',
      carries_result_streams scope moved ambs ts ts' ce dlt dlt'.
Proof.
  intros scope moved ambs ts ts' ce dlt Hts Hce Hlen Hsc.
  subst ts' ce. exists dlt.
  unfold carries_result_streams. split.
  - intros x Hx. reflexivity.
  - split.
    + constructor.
    + split.
      * exact (stream_rel_refl dlt ambs ts Hlen).
      * split.
        -- constructor.
        -- assert
             (forall (t : LST),
                st_scoped scope (fst t) ->
                st_scoped (scope ++ moved) (fst t)) as Hweaken.
           { intros t Ht.
             apply st_scoped_weaken with (scope1 := scope); [|exact Ht].
             apply incl_appl, incl_refl. }
           exact
             (@Forall_impl LST
                (fun t => st_scoped scope (fst t))
                (fun t => st_scoped (scope ++ moved) (fst t))
                Hweaken ts Hsc).
Qed.

Section StreamAmbients.

  Variable GL      : secglobal.
  Variable env     : Env.t ident.
  Variable base_ty : ident.
  Variable rst_ty  : ident.
  Variable cenv    : Env.t (type * clock).

  Hypothesis env_inj : env_injective env.

  Local Notation sec_of := (CALLS.sec_of env).
  Local Notation agree_off := CALLS.agree_off.

  Definition clock_covered (ck : clock) (a : ST) : Prop :=
    exists ckty,
      assign_clk_type env base_ty ck = Some ckty
      /\ incl (merge [rst_ty] ckty) a.

  Lemma clock_covered_incl :
    forall ck a ckty,
      clock_covered ck a ->
      assign_clk_type env base_ty ck = Some ckty ->
      incl (merge [rst_ty] ckty) a.
  Proof.
    intros ck a ckty (found & Hfound & Hincl) Hckty.
    rewrite Hfound in Hckty. inversion Hckty; subst. exact Hincl.
  Qed.

  Definition clocks_covered (cks : list clock) (ambs : list ST) : Prop :=
    Forall2 clock_covered cks ambs.


  (** * A call's uniform ambient sits below every result's

      The streams contract gives each source stream its own ambient, but
      [generate_constraints_mono_sem] transports satisfaction under a single
      one.  The two are reconciled by taking that single one to be the call's
      own -- [merge [rst_ty] bckty] -- and observing that it is below every
      result's ambient: every output clock instantiates the *same* base clock,
      so [bck]'s type is inside each output clock's type.

      This is the [amb_pair] obligation of the design in force, in the form the
      streams call case needs it. *)

  Lemma wc_Eapp_out_instck :
    forall (outs : list (ident * clock)) bck sub (anns : list LSyn.ann),
      Forall2 (WellInstantiated bck sub) outs (List.map snd anns) ->
      forall ck, In ck (List.map clock_of_nclock anns) ->
                 exists ckf, instck bck sub ckf = Some ck.
  Proof.
    intros outs bck sub anns Hwi ck Hin.
    apply in_map_iff in Hin as (ann & Hck & Hann).
    assert (In (snd ann) (List.map snd anns)) as Hin2
        by (apply in_map_iff; exists ann; split; [reflexivity|exact Hann]).
    apply In_nth_error in Hin2 as (i & Hni).
    assert (exists p, nth_error outs i = Some p) as (p & Hpi).
    { apply nth_error_lt.
      rewrite (Forall2_length _ _ _ Hwi).
      exact (nth_error_lt_inv _ i (snd ann) Hni). }
    destruct p as (x & ckf).
    destruct (Forall2_nth_error _ outs (List.map snd anns) i (x, ckf) (snd ann)
                Hwi Hpi Hni) as (_ & Hi).
    exists ckf. cbn [fst snd] in Hi. rewrite Hi.
    unfold clock_of_nclock, stripname in Hck. now rewrite Hck.
  Qed.

  Lemma call_amb_below_result_ambients :
    forall bck sub (outcks : list clock) ambs bckty,
      assign_clk_type env base_ty bck = Some bckty ->
      (forall ck, In ck outcks -> exists ckf, instck bck sub ckf = Some ck) ->
      clocks_covered outcks ambs ->
      Forall (fun a => incl (merge [rst_ty] bckty) a) ambs.
  Proof.
    intros bck sub outcks ambs bckty Hbk Hinst Hcov.
    induction Hcov as [|ck a cks ambs0 Hca Hr IH]; [constructor|].
    constructor.
    - destruct Hca as (ckty & Hckty & Hincl).
      destruct (Hinst ck (or_introl (@Coq.Init.Logic.eq_refl _ ck)))
        as (ckf & Hi).
      assert (incl bckty ckty) as Hbi
          by exact (assign_clk_type_instck_base_incl env base_ty bck sub ckf ck
                      bckty ckty Hi Hbk Hckty).
      intros z Hz. apply Hincl.
      exact (incl_merge_mono [rst_ty] [rst_ty] bckty ckty
               (incl_refl [rst_ty]) Hbi z Hz).
    - apply IH. intros ck0 Hck0. apply Hinst. now right.
  Qed.

  Definition declared_ambients (xs : list ident) (ambs : list ST) : Prop :=
    Forall2
      (fun x a =>
         forall ck,
           find_clock cenv x = OK ck -> clock_covered ck a)
      xs ambs.

  Definition state_clocks_found (st : fresh_st (type * clock)) : Prop :=
    forall x an,
      In (x, an) (st_anns st) ->
      find_clock cenv x = OK (snd an).

  Lemma state_clocks_found_prefix :
    forall st st',
      st_follows st st' ->
      state_clocks_found st' ->
      state_clocks_found st.
  Proof.
    intros st st' Hfollows Hfound x an Hin.
    apply Hfound.
    exact (st_follows_incl st st' Hfollows (x, an) Hin).
  Qed.

  Lemma declared_ambients_of_clocks :
    forall xs cks ambs,
      Forall2 (fun x ck => find_clock cenv x = OK ck) xs cks ->
      clocks_covered cks ambs ->
      declared_ambients xs ambs.
  Proof.
    intros xs cks ambs Hfind Hcovered.
    revert ambs Hcovered.
    induction Hfind as [|x ck xs cks Hfind Hfinds IH];
      intros ambs Hcovered.
    - inversion Hcovered. constructor.
    - inversion Hcovered as
        [|ck0 a cks0 ambs0 Hcover Hcovers]; subst.
      constructor.
      + intros ck' Hfind'. rewrite Hfind in Hfind'.
        inversion Hfind'; subst. exact Hcover.
      + exact (IH ambs0 Hcovers).
  Qed.

  Lemma declared_ambients_of_state :
    forall (ids : list (ident * (type * clock))) st cks ambs,
      incl ids (st_anns st) ->
      Forall2 (fun xa ck => snd (snd xa) = ck) ids cks ->
      state_clocks_found st ->
      clocks_covered cks ambs ->
      declared_ambients (List.map fst ids) ambs.
  Proof.
    intros ids st cks ambs Hin Hclock Hfound.
    assert
      (Forall2
         (fun x ck => find_clock cenv x = OK ck)
         (List.map fst ids) cks) as Hfind.
    { induction Hclock as [|xa ck ids cks Hxa Hrest IH].
      - constructor.
      - destruct xa as (x & an). simpl in Hxa |- *.
        constructor.
        + rewrite <- Hxa. apply Hfound.
          apply Hin. now left.
        + apply IH. intros z Hz. apply Hin. now right. }
    intros Hcovered.
    exact (declared_ambients_of_clocks _ _ _ Hfind Hcovered).
  Qed.

  (** [lifted_defs] with one ambient per emitted result.  The three aligned
      lists make explicit the correspondence that the scalar theorem loses:
      an emitted identifier, its source type, and its clock ambient occupy the
      same position. *)
  Lemma lifted_defs_streams :
    forall bound (xs : list ident) (rhss : list exp) (srcs : list LST)
           (ambs : list ST) ce xst xst' dlt,
      NoDup xs ->
      List.length xs = List.length rhss ->
      (forall b, In b (sec_of xs) -> ~ In b bound) ->
      declared_ambients xs ambs ->
      Forall (st_scoped bound) ambs ->
      Forall
        (fun e =>
           (match e with Eapp _ _ _ _ => False | _ => True end)
           /\ forall ts s s',
                assign_lexp_type GL env base_ty rst_ty e s = OK (ts, s') ->
                s' = s /\ List.length ts = 1 /\ carried ts = [])
        rhss ->
      Forall (fun src => st_scoped bound (fst src)) srcs ->
      Forall3
        (fun a e src =>
           forall tf s s',
             assign_lexp_type GL env base_ty rst_ty e s = OK ([tf], s') ->
             satisfiable dlt (fst tf) (merge a (fst src))
             /\ st_scoped bound (fst tf))
        ambs rhss srcs ->
      generate_leqns_constraints GL env base_ty rst_ty cenv
        (List.map (fun '(x, e) => ([x], [e])) (combine xs rhss)) xst
        = OK (ce, xst') ->
      exists dlt',
        agree_off (sec_of xs) dlt dlt'
        /\ listSatisfiable dlt' ce
        /\ constraints_scoped (bound ++ sec_of xs) ce
        /\ Forall3
             (fun a x src =>
                forall b, Env.find x env = Some b ->
                  satisfiable dlt' [b] (merge a (fst src)))
             ambs xs srcs.
  Proof.
      intros bound xs. revert bound.
    induction xs as [|x xs IH];
      intros bound rhss srcs ambs ce xst xst' dlt
        Hnd Hlen Hsep Hclks Hambsc Hpure Hsrcsc Hrel Hgen.
    all: unfold declared_ambients in Hclks.
    - destruct rhss; simpl in Hlen; [|discriminate].
      destruct ambs as [|a ambs]; [|inversion Hclks].
      destruct srcs as [|src srcs]; [|inversion Hrel].
      simpl in Hgen.
      destruct
        (CALLS.generate_leqns_constraints_nil
           GL env base_ty rst_ty cenv ce xst xst' Hgen)
        as (Hce & Hstate).
      subst ce xst'. exists dlt.
      split; [intros y Hy; reflexivity|].
      split.
      + constructor.
      + split.
        * constructor.
        * constructor.
    - destruct rhss as [|e rhss]; simpl in Hlen; [discriminate|].
      injection Hlen as Hlenr.
      destruct ambs as [|a ambs]; [inversion Hclks|].
      inversion Hclks as [|x0 a0 xs0 ambs0 Hclk Hclksr]; subst.
      inversion Hambsc as [|a0 ambs0 Hasc Hambscr]; subst.
      inversion Hrel as
        [|a0 e0 src0 ambs0 rhss0 srcs0 Hr Hrelr]; subst.
      inversion Hnd as [|x0 xs0 Hxn Hndr]; subst.
      inversion Hpure as [|e0 rhss0 Hhead Hpurer]; subst.
      inversion Hsrcsc as [|src1 srcs1 Hs0 Hsrcsr]; subst.
      replace
        (List.map (fun '(x0, e0) => ([x0], [e0]))
           (combine (x :: xs) (e :: rhss)))
        with
        (([x], [e]) ::
           List.map (fun '(x0, e0) => ([x0], [e0])) (combine xs rhss))
        in Hgen by reflexivity.
      rewrite generate_leqns_constraints_cons in Hgen.
      apply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
      apply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
      unfold ret in Hret. inversion Hret; subst.
      rewrite generate_leqn_constraint_def in Hc by tauto.
      apply generate_ldef_constraint_inv in Hc
        as (ck & ckty & tf & b & xstm & Hck & Hcl & Htf & Hb
            & Hxstm & Hceq).
      subst xstm c.
      destruct Hhead as (Hnoncall & Hp).
      specialize (Hp _ _ _ Htf) as (Hxstm & Hsingle & Hcar).
      subst xst1. rewrite carried_single in Hcar.
      rewrite Hcar, cmerge_nil.
      specialize (Hr _ _ _ Htf) as (Hdom & Hsc).

      assert (forall b', In b' (sec_of xs) -> ~ In b' bound) as Hsepr.
      { intros b' Hb'. apply Hsep. now apply sec_of_incl_cons. }
      destruct
        (IH bound rhss srcs0 ambs cs xst xst' dlt
           Hndr Hlenr Hsepr Hclksr Hambscr Hpurer Hsrcsr Hrelr Hcs)
        as (dlt1 & Hoff1 & Hce1 & Hscope1 & Hrel1).

      assert (~ In b (sec_of xs)) as Hbx.
      { exact (sec_of_nIn env env_inj x xs b Hxn Hb). }
      assert (~ In b bound) as Hbb.
      { apply Hsep. exact (sec_of_cons_In env x xs b Hb). }
      assert
        (forall X, st_scoped bound X -> hm_ext dlt1 X = hm_ext dlt X)
        as Hstable.
      { intros X HX. symmetry.
        apply (CALLS.hm_ext_off X (sec_of xs) dlt dlt1 Hoff1).
        intros y Hy Hin. exact (Hsepr y Hin (HX y Hy)). }
      assert
        (st_scoped bound (merge (merge [rst_ty] ckty) (fst tf))) as Hlsc.
      { apply st_scoped_merge; [|exact Hsc].
        intros y Hy. apply Hasc.
        apply
          (clock_covered_incl
             ck a ckty (Hclk ck Hck) Hcl).
        exact Hy. }
      assert (st_scoped bound (merge a (fst src0))) as Hmsc.
      { apply st_scoped_merge; assumption. }
      assert
        (forall X, st_scoped bound X ->
           hm_ext
             (upd b
                (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1)
             X = hm_ext dlt1 X) as Hstable'.
      { intros X HX.
        apply (CALLS.hm_ext_off X [b]
                 (upd b
                    (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1)
                 dlt1).
        - intros y Hy. unfold upd.
          destruct (ident_eq_dec y b) as [Heq|Hneq].
          + exfalso. apply Hy. now left.
          + reflexivity.
        - intros y Hy Hin. destruct Hin as [Hin|[]]. subst y.
          exact (Hbb (HX b Hy)). }
      assert
        (satisfiable dlt (merge (merge [rst_ty] ckty) (fst tf))
           (merge a (fst src0))) as Hkey.
      { apply satisfiable_merge_intro; [|exact Hdom].
        apply Lat.order_trans
          with (y := hm_ext dlt a).
        - apply hm_ext_incl.
          exact
            (clock_covered_incl
               ck a ckty (Hclk ck Hck) Hcl).
        - apply satisfiable_merge_l. }

      exists
        (upd b (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1).
      split; [|split; [|split]].
      + intros y Hy. rewrite (Hoff1 y).
        2: { intro Hin. apply Hy. now apply sec_of_incl_cons. }
        unfold upd. destruct (ident_eq_dec y b) as [Heq|Hneq].
        * subst y. exfalso. apply Hy. exact (sec_of_cons_In env x xs b Hb).
        * reflexivity.
      + apply listSatisfiable_app. split.
        * constructor; [|constructor].
          unfold constraintSatisfiable, satisfiable.
          rewrite hm_ext_single, upd_same, (Hstable' _ Hlsc).
          apply Lat.join_bound1.
        * assert
            (forall y, In y [b] -> ~ In y (bound ++ sec_of xs)) as Hfreshb.
          { intros y Hy Hin. destruct Hy as [Hy|[]]. subst y.
            apply in_app_or in Hin as [Hin|Hin].
            - exact (Hbb Hin).
            - exact (Hbx Hin). }
          assert
            (agree_off [b] dlt1
               (upd b
                  (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1))
            as Hoffb.
          { intros y Hy. unfold upd.
            destruct (ident_eq_dec y b) as [Heq|Hneq].
            - exfalso. apply Hy. now left.
            - reflexivity. }
          exact
            (CALLS.listSatisfiable_off_scope
               cs (bound ++ sec_of xs) [b] dlt1
               (upd b
                  (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1)
               Hscope1 Hfreshb Hoffb Hce1).
      + apply Forall_app. split.
        * constructor; [|constructor].
          intros y Hy. unfold constraint_scope in Hy. simpl in Hy.
          apply in_app_or in Hy as [Hy|Hy].
          -- apply in_or_app. left. exact (Hlsc y Hy).
          -- destruct Hy as [Hy|[]]. subst y. apply in_or_app. right.
             exact (sec_of_cons_In env x xs b Hb).
        * assert
            (forall c0,
               constraint_scoped (bound ++ sec_of xs) c0 ->
               constraint_scoped (bound ++ sec_of (x :: xs)) c0)
            as Hscope_weaken.
          { intros c0 Hc0. apply constraint_scoped_incl with
              (scope1 := bound ++ sec_of xs); [|exact Hc0].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, sec_of_incl_cons. }
          exact
            (@Forall_impl constraint
               (fun c0 => constraint_scoped (bound ++ sec_of xs) c0)
               (fun c0 => constraint_scoped
                  (bound ++ sec_of (x :: xs)) c0)
               Hscope_weaken cs Hscope1).
      + constructor.
        * intros b' Hb'. rewrite Hb in Hb'. inversion Hb'; subst.
          apply satisfiable_singleton. rewrite upd_same.
          rewrite (Hstable' _ Hmsc), (Hstable _ Hlsc), (Hstable _ Hmsc).
          exact Hkey.
        * apply
            (@Forall3_impl_In ST ident LST
               (fun a' y src =>
                  forall b', Env.find y env = Some b' ->
                    satisfiable dlt1 [b'] (merge a' (fst src)))
               (fun a' y src =>
                  forall b', Env.find y env = Some b' ->
                    satisfiable
                      (upd b
                         (hm_ext dlt1
                            (merge (merge [rst_ty] ckty) (fst tf))) dlt1)
                      [b'] (merge a' (fst src)))
               ambs xs srcs0).
          -- intros a' y src Ha Hy Hsrc Hyr b' Hb'.
             assert
               (agree_off [b] dlt1
                  (upd b
                     (hm_ext dlt1
                        (merge (merge [rst_ty] ckty) (fst tf))) dlt1))
               as Hoffb.
             { intros z Hz. unfold upd.
               destruct (ident_eq_dec z b) as [Heq|Hneq].
               - exfalso. apply Hz. now left.
               - reflexivity. }
             assert (forall z, In z [b'] -> ~ In z [b]) as Hleft.
             { intros z Hz Hin. destruct Hz as [Hz|[]]. subst z.
               destruct Hin as [Hin|[]]. subst b'.
               apply Hbx. unfold sec_of. apply in_flat_map.
               exists y. split; [exact Hy|]. rewrite Hb'. now left. }
             assert
               (forall z, In z (merge a' (fst src)) -> ~ In z [b])
               as Hright.
             { intros z Hz Hin. destruct Hin as [Hin|[]]. subst z.
               apply in_merge_inv in Hz as [Hz|Hz].
               - pose proof Hambscr as Hambs_all.
                 rewrite Forall_forall in Hambs_all.
                 exact (Hbb (Hambs_all a' Ha b Hz)).
               - pose proof Hsrcsr as Hsrcs_all.
                 rewrite Forall_forall in Hsrcs_all.
                 exact (Hbb (Hsrcs_all src Hsrc b Hz)). }
             exact
               (CALLS.satisfiable_off
                  [b'] (merge a' (fst src)) [b] dlt1
                  (upd b
                     (hm_ext dlt1
                        (merge (merge [rst_ty] ckty) (fst tf))) dlt1)
                  Hoffb Hleft Hright (Hyr b' Hb')).
          -- exact Hrel1.
  Qed.

  Section ExpressionContract.

    Variable vars  : list (ident * clock).
    Variable scope : list ident.

    (** The expression contract with one clock ambient per source stream.
        [clocks_covered] fixes the positional meaning of [ambs], while
        [state_clocks_found] connects the clocks stored on variables freshly
        introduced by unnesting to the target node clock environment. *)
    Definition carries_at_streams
        (P : global) (is_control : bool) (e : exp) : Prop :=
      forall ambs es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        wl_exp P e ->
        wc_exp P vars e ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        (forall x,
            In x (CALLS.moved_by env st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        stream_ambients_scoped scope ambs ->
        clocks_covered (clockof e) ambs ->
        List.length ambs = List.length ts ->
        state_clocks_found st' ->
        unnest_exp P is_control e st = ((es', eqs), st') ->
        assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty es' yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          carries_result_streams scope (CALLS.moved_by env st st')
            ambs ts ts'' ce dlt dlt'.

    Definition carries_streams (P : global) (e : exp) : Prop :=
      forall is_control, carries_at_streams P is_control e.

    Lemma unnest_exp_one_streams :
      forall P e es' eqs st st',
        wl_exp P e ->
        numstreams e = 1 ->
        unnest_exp P false e st = ((es', eqs), st') ->
        es' = [hd_default es'].
    Proof.
      intros P e es' eqs st st' Hwl Hnum Hun.
      pose proof
        (unnest_exp_length P e false es' eqs st st' Hwl Hun) as Hlength.
      rewrite Hnum in Hlength.
      destruct es' as [|e0 [|e1 es']];
        simpl in Hlength; try discriminate; reflexivity.
    Qed.

    Lemma carries_Econst_streams :
      forall P c, carries_streams P (Econst c).
    Proof.
      intros P c is_control ambs es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt
        _ _ _ _ _ Htsc _ _ Hlen _ Hun Has Hgen Has' _.
      rewrite unnest_exp_Econst in Hun. inversion Hun; subst; clear Hun.
      destruct
        (CALLS.generate_leqns_constraints_nil
           GL env base_ty rst_ty cenv ce xst xst' Hgen)
        as (Hce & Hxst).
      subst ce xst'.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Econst in Has, Has'.
      unfold ret in Has, Has'. inversion Has; subst; clear Has.
      inversion Has'; subst; clear Has'.
      exact
        (carries_unchanged_streams
           scope (CALLS.moved_by env st' st') ambs [lbot] [lbot] [] dlt
           (@Coq.Init.Logic.eq_refl (list LST) [lbot])
           (@Coq.Init.Logic.eq_refl (list constraint) []) Hlen Htsc).
    Qed.

    Lemma carries_Evar_streams :
      forall P x a, carries_streams P (Evar x a).
    Proof.
      intros P x a is_control ambs es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt
        _ _ _ _ _ Htsc _ _ Hlen _ Hun Has Hgen Has' _.
      rewrite unnest_exp_Evar in Hun. inversion Hun; subst; clear Hun.
      destruct
        (CALLS.generate_leqns_constraints_nil
           GL env base_ty rst_ty cenv ce xst xst' Hgen)
        as (Hce & Hxst).
      subst ce xst'.
      apply assign_lexps_single in Has'.
      apply assign_lexp_Evar_inv in Has as (b & Hb & Hts & Hsst).
      subst ts sst'.
      apply assign_lexp_Evar_inv in Has' as (b' & Hb' & Hts' & Hyst).
      subst ts'' yst'.
      rewrite Hb in Hb'. inversion Hb'; subst b'; clear Hb'.
      exact
        (carries_unchanged_streams
           scope (CALLS.moved_by env st' st')
           ambs [([b], [])] [([b], [])] [] dlt
           (@Coq.Init.Logic.eq_refl (list LST) [([b], [])])
           (@Coq.Init.Logic.eq_refl (list constraint) []) Hlen Htsc).
    Qed.

    Lemma carries_Eunop_streams :
      forall P op e a,
        carries_streams P e -> carries_streams P (Eunop op e a).
    Proof.
      intros P op e a IH is_control ambs es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      apply unnest_exp_Eunop_inv in Hun as (e1' & st1 & Hun & Hst & Hes').
      subst st' es'.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Eunop in Has, Has'.
      assert
        (assign_lexps GL env base_ty rst_ty e1' yst = OK (ts'', yst'))
        as Has1'.
      { pose proof
          (unnest_exp_one_streams P e e1' eqs st st1 H2 H4 Hun)
          as Hone.
        rewrite Hone at 1.
        exact
          (assign_lexps_single_intro
             GL env base_ty rst_ty (hd_default e1') ts'' yst yst' Has'). }
      assert (clocks_covered (clockof e) ambs) as Hcovered1.
      { rewrite H5. exact Hcovered. }
      exact
        (IH false ambs e1' eqs st st1 ts sst sst'
           ce xst xst' ts'' yst yst' dlt
           H2 H1 Hnd Hmv Hcsc Htsc Hambsc Hcovered1 Hlen Hfound
           Hun Has Hgen Has1' Hsat).
    Qed.

    Lemma carries_Ebinop_streams :
      forall P op e1 e2 a,
        carries_streams P e1 ->
        carries_streams P e2 ->
        carries_streams P (Ebinop op e1 e2 a).
    Proof.
      intros P op e1 e2 a IH1 IH2 is_control
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      apply unnest_exp_Ebinop_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & Heqs & Hes').
      subst eqs es'.
      assert (st_follows st st1) as Hf1.
      { exact
          (unnest_exp_st_follows P e1 false (f1, eqs1) st st1 Hun1). }
      assert (st_follows st1 st') as Hf2.
      { exact
          (unnest_exp_st_follows P e2 false (f2, eqs2) st1 st' Hun2). }

      rewrite assign_lexp_Ebinop in Has.
      apply sec_bind_inv in Has as (t1 & sa & Ht1 & Has).
      apply sec_bind_inv in Has as (t2 & sb & Ht2 & Has).
      apply sec_bind_inv in Has as (a1 & sc1 & Ha1 & Has).
      apply sec_bind_inv in Has as (a2 & sc2 & Ha2 & Hret).
      unfold ret in Hret. inversion Hret; subst; clear Hret.
      apply single_inv in Ha1 as (Ht1s & Ha1); subst t1.
      apply single_inv in Ha2 as (Ht2s & Ha2); subst t2.

      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Ebinop in Has'.
      apply sec_bind_inv in Has' as (u1 & ya & Hu1 & Has').
      apply sec_bind_inv in Has' as (u2 & yb & Hu2 & Has').
      apply sec_bind_inv in Has' as (b1 & yc & Hb1 & Has').
      apply sec_bind_inv in Has' as (b2 & yd & Hb2 & Hret').
      unfold ret in Hret'. inversion Hret'; subst; clear Hret'.
      apply single_inv in Hb1 as (Hu1s & Hb1); subst u1.
      apply single_inv in Hb2 as (Hu2s & Hb2); subst u2.

      pose proof
        (unnest_exp_one_streams P e1 f1 eqs1 st st1 H4 H6 Hun1)
        as Hone1.
      pose proof
        (unnest_exp_one_streams P e2 f2 eqs2 st1 st' H5 H7 Hun2)
        as Hone2.
      assert
        (assign_lexps GL env base_ty rst_ty f1 yst = OK ([b1], ya))
        as Hu1'.
      { rewrite Hone1 at 1.
        exact
          (assign_lexps_single_intro
             GL env base_ty rst_ty (hd_default f1) [b1] yst ya Hu1). }
      assert
        (assign_lexps GL env base_ty rst_ty f2 ya = OK ([b2], yb))
        as Hu2'.
      { rewrite Hone2 at 1.
        exact
          (assign_lexps_single_intro
             GL env base_ty rst_ty (hd_default f2) [b2] ya yb Hu2). }

      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv eqs1 eqs2 ce xst xst' Hgen)
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & Hce).
      subst ce.

      rewrite carried_ljoin in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (Hcsc1 & Hcsc2).
      apply listSatisfiable_cmerge in Hsat as (Hsat1 & Hsat2).
      inversion Htsc as [|src srcr Hsrcsc Hsrcscr]; subst.
      simpl in Hsrcsc.
      apply st_scoped_merge_inv in Hsrcsc as (Ha1sc & Ha2sc).
      assert (carried [a1] = snd a1) as Hcar1.
      { simpl. apply cmerge_nil. }
      assert (carried [a2] = snd a2) as Hcar2.
      { simpl. apply cmerge_nil. }

      destruct ambs as [|amb ambs]; [discriminate|].
      destruct ambs as [|amb' ambs]; [|discriminate].
      inversion Hambsc as [|amb0 ambs0 Hambsc0 Hambscr]; subst.
      assert (clocks_covered (clockof e1) [amb]) as Hcovered1.
      { rewrite H9. exact Hcovered. }
      assert (clocks_covered (clockof e2) [amb]) as Hcovered2.
      { rewrite H10. exact Hcovered. }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st' Hf2 Hfound). }
      assert
        (NoDup (vars_defined eqs1 ++ st_ids st)) as Hnd1.
      { apply CALLS.NoDup_vd_app_l with (eqs2 := eqs2). exact Hnd. }
      assert
        (Permutation (vars_defined eqs1 ++ st_ids st) (st_ids st1))
        as Hperm1.
      { exact (unnest_exp_vars_perm P e1 false f1 eqs1 st st1 H4 Hun1). }
      assert
        (NoDup (vars_defined eqs2 ++ st_ids st1)) as Hnd2.
      { apply CALLS.NoDup_vd_app_r with (eqs1 := eqs1) (s := st_ids st).
        - exact Hperm1.
        - exact Hnd. }
      assert
        (forall x,
            In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        exact
          (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hx). }
      assert
        (forall x,
            In x (CALLS.moved_by env st1 st') -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        exact
          (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hx). }
      assert
        (Forall (fun t => st_scoped scope (fst t)) [a1]) as Ha1scs.
      { constructor; [exact Ha1sc|constructor]. }
      assert
        (Forall (fun t => st_scoped scope (fst t)) [a2]) as Ha2scs.
      { constructor; [exact Ha2sc|constructor]. }
      assert (stream_ambients_scoped scope [amb]) as Hambscs.
      { constructor; [exact Hambsc0|constructor]. }

      destruct
        (IH1 false [amb] f1 eqs1 st st1 [a1] sst sa
           ce1 xst xst1 [b1] yst ya dlt
           H4 H3 Hnd1 Hmv1
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc1 Hcar1)
           Ha1scs Hambscs
           Hcovered1 (@Coq.Init.Logic.eq_refl nat 1) Hfound1
           Hun1 Ht1 Hgen1 Hu1'
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat1 Hcar1))
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried [a2])) as Hsat2'.
      { apply
          (CALLS.listSatisfiable_off
             scope (carried [a2]) (CALLS.moved_by env st st1)
             dlt dlt1).
        - rewrite Hcar2. exact Hcsc2.
        - exact Hmv1.
        - exact Hoff1.
        - rewrite Hcar2. exact Hsat2. }
      destruct
        (IH2 false [amb] f2 eqs2 st1 st' [a2] sa sb
           ce2 xst1 xst' [b2] ya yb dlt1
           H5 H8 Hnd2 Hmv2
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc2 Hcar2)
           Ha2scs Hambscs
           Hcovered2 (@Coq.Init.Logic.eq_refl nat 1) Hfound
           Hun2 Ht2 Hgen2 Hu2' Hsat2')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      inversion Hrel1 as [|amb1 src1 tgt1 ambsr srcsr tgtsr Hr1 Hrel1r];
        subst.
      inversion Hrel2 as [|amb2 src2 tgt2 ambsr srcsr tgtsr Hr2 Hrel2r];
        subst.
      inversion Htgt1 as [|tgt1 tgts1 Hb1sc Htgt1r]; subst.
      inversion Htgt2 as [|tgt2 tgts2 Hb2sc Htgt2r]; subst.

      exists dlt2.
      unfold carries_result_streams. split.
      - intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hin). }
        apply Hoff2. intro Hin. apply Hx.
        exact
          (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hin).
      - split.
        + apply listSatisfiable_app. split; [|exact Hce2].
          exact
            (CALLS.listSatisfiable_off_scope
               ce1 (scope ++ CALLS.moved_by env st st1)
               (CALLS.moved_by env st1 st') dlt1 dlt2
               Hscope1
               (fun x Hin Hxin =>
                  match in_app_or _ _ _ Hxin with
                  | or_introl Hscope =>
                      Hmv2 x Hin Hscope
                  | or_intror Hfirst =>
                      CALLS.moved_by_disjoint_local
                        env env_inj st st1 st' x Hfirst Hin
                  end)
               Hoff2 Hce1).
        + split.
          * constructor; [|constructor]. unfold ljoin; simpl.
            apply satisfiable_merge_intro.
            -- apply CALLS.satisfiable_merge_grow_l.
               apply
                 (CALLS.satisfiable_off
                    (fst b1) (merge amb (fst a1))
                    (CALLS.moved_by env st1 st') dlt1 dlt2).
               ++ exact Hoff2.
               ++ intros x Hx Hin. apply Hb1sc in Hx.
                  apply in_app_or in Hx as [Hx|Hx].
                  ** exact (Hmv2 x Hin Hx).
                  ** exact
                       (CALLS.moved_by_disjoint_local
                          env env_inj st st1 st' x Hx Hin).
               ++ intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
                  ** exact (Hmv2 x Hin (Hambsc0 x Hx)).
                  ** exact (Hmv2 x Hin (Ha1sc x Hx)).
               ++ exact Hr1.
            -- exact (CALLS.satisfiable_merge_grow_r dlt2 (fst b2)
                        amb (fst a2) Hr2 (fst a1)).
          * split.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st1))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc. apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st1).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact (CALLS.moved_by_prefix_local env st st1 st' Hf2).
                  ** exact Hscope1.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st1 st'))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc. apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st1 st').
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact (CALLS.moved_by_suffix_local env st st1 st' Hf1).
                  ** exact Hscope2.
            -- constructor; [|constructor]. unfold ljoin; simpl.
               apply st_scoped_merge.
               ++ apply st_scoped_weaken with
                    (scope1 := scope ++ CALLS.moved_by env st st1).
                  2: exact Hb1sc.
                  apply incl_app; [apply incl_appl, incl_refl|].
                  apply incl_appr.
                  exact (CALLS.moved_by_prefix_local env st st1 st' Hf2).
               ++ apply st_scoped_weaken with
                    (scope1 := scope ++ CALLS.moved_by env st1 st').
                  2: exact Hb2sc.
                  apply incl_app; [apply incl_appl, incl_refl|].
                  apply incl_appr.
                  exact (CALLS.moved_by_suffix_local env st st1 st' Hf1).
    Qed.

    Definition carries_list_streams (P : global) (es : list exp) : Prop :=
      forall ic ambs es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        Forall (wl_exp P) es ->
        Forall (wc_exp P vars) es ->
        NoDup (vars_defined (List.concat eqs) ++ st_ids st) ->
        (forall x,
            In x (CALLS.moved_by env st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        stream_ambients_scoped scope ambs ->
        clocks_covered (clocksof es) ambs ->
        List.length ambs = List.length ts ->
        state_clocks_found st' ->
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.concat eqs) xst = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty (List.concat es') yst
          = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          carries_result_streams scope (CALLS.moved_by env st st')
            ambs ts ts'' ce dlt dlt'.

    Lemma split_at_length :
      forall (A : Type) n (xs : list A),
        n <= List.length xs ->
        exists xs1 xs2,
          xs = xs1 ++ xs2 /\ List.length xs1 = n.
    Proof.
      intros A n xs Hle.
      exists (firstn n xs), (skipn n xs). split.
      - symmetry. apply firstn_skipn.
      - rewrite firstn_length. apply Min.min_l. exact Hle.
    Qed.

    Lemma carries_list_streams_intro :
      forall P es,
        Forall (carries_streams P) es -> carries_list_streams P es.
    Proof.
      intros P es Hall.
      induction Hall as [|e es IHe IHes IH];
        intros ic ambs es' eqs st st' ts sst sst'
          ce xst xst' ts'' yst yst' dlt
          Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
          Hun Has Hgen Has' Hsat.
      - destruct
          (CALLS.map_bind2_unnest_nil P ic es' eqs st st' Hun)
          as (Hes' & Heqs & Hst').
        subst es' eqs st'.
        destruct
          (assign_lexps_carried_nil
             GL env base_ty rst_ty ts sst sst' Has)
          as (Hts & Hcar & Hsst).
        subst ts sst'.
        destruct
          (assign_lexps_carried_nil
             GL env base_ty rst_ty ts'' yst yst' Has')
          as (Hts'' & Hcar' & Hyst).
        subst ts'' yst'.
        destruct
          (CALLS.generate_leqns_constraints_nil
             GL env base_ty rst_ty cenv ce xst xst' Hgen)
          as (Hce & Hxst).
        subst ce xst'.
        destruct ambs as [|amb ambs]; [|discriminate].
        exact
          (carries_unchanged_streams
             scope (CALLS.moved_by env st st) [] [] [] [] dlt
             (@Coq.Init.Logic.eq_refl (list LST) [])
             (@Coq.Init.Logic.eq_refl (list constraint) []) Hlen Htsc).
      - inversion Hwl as [|e0 es0 Hwle Hwles]; subst.
        inversion Hwc as [|e0 es0 Hwce Hwces]; subst.
        destruct
          (CALLS.map_bind2_unnest_cons P ic e es es' eqs st st' Hun)
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & Hes' & Heqs).
        subst es' eqs.
        assert (st_follows st st1) as Hf1.
        { exact
            (unnest_exp_st_follows P e ic (f1, eq1) st st1 Hun1). }
        assert (st_follows st1 st') as Hf2.
        { exact
            (CALLS.map_bind2_unnest_st_follows
               P ic es fr eqsr st1 st' Hunr). }

        destruct
          (assign_lexps_carried_cons
             GL env base_ty rst_ty e es ts sst sst' Has)
          as (t & r & sa & Ht & Hr & Hts & Hcarried).
        subst ts.
        destruct
          (CALLS.assign_lexps_app_inv
             GL env base_ty rst_ty f1 (List.concat fr)
             ts'' yst yst' Has')
          as (u & v & ya & Hu & Hv & Hts'').
        subst ts''.
        destruct
          (CALLS.generate_leqns_constraints_app
             GL env base_ty rst_ty cenv eq1 (List.concat eqsr)
             ce xst xst' Hgen)
          as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & Hce).
        subst ce.

        rewrite Hcarried in Hcsc, Hsat.
        apply constraints_scoped_cmerge in Hcsc as (Hcsc1 & Hcsc2).
        apply listSatisfiable_cmerge in Hsat as (Hsat1 & Hsat2).
        apply Forall_app in Htsc as (Htsc1 & Htsc2).

        assert (List.length t <= List.length ambs) as Htle.
        { rewrite Hlen, app_length. lia. }
        destruct (split_at_length ST (List.length t) ambs Htle)
          as (ambs1 & ambs2 & Hambs & Hambs1len).
        subst ambs.
        apply Forall_app in Hambsc as (Hambsc1 & Hambsc2).
        assert (List.length (clockof e) = List.length ambs1) as Hclocklen.
        { rewrite length_clockof_numstreams, Hambs1len.
          symmetry.
          exact
            (assign_lexp_type_length
               P GL env base_ty rst_ty e Hwle t sst sa Ht). }
        change
          (clocks_covered (clockof e ++ clocksof es) (ambs1 ++ ambs2))
          in Hcovered.
        destruct
          (Forall2_app_split
             clock_covered (clockof e) ambs1 (clocksof es) ambs2
             Hcovered Hclocklen)
          as (Hcovered1 & Hcovered2).
        assert (List.length ambs2 = List.length r) as Hambs2len.
        { rewrite !app_length in Hlen. lia. }
        assert (state_clocks_found st1) as Hfound1.
        { exact (state_clocks_found_prefix st1 st' Hf2 Hfound). }

        assert
          (NoDup (vars_defined eq1 ++ st_ids st)) as Hnd1.
        { apply CALLS.NoDup_vd_app_l with (eqs2 := List.concat eqsr).
          exact Hnd. }
        assert
          (Permutation (vars_defined eq1 ++ st_ids st) (st_ids st1))
          as Hperm1.
        { exact (unnest_exp_vars_perm P e ic f1 eq1 st st1 Hwle Hun1). }
        assert
          (NoDup (vars_defined (List.concat eqsr) ++ st_ids st1)) as Hnd2.
        { apply CALLS.NoDup_vd_app_r with
            (eqs1 := eq1) (s := st_ids st).
          - exact Hperm1.
          - exact Hnd. }
        assert
          (forall x,
              In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
        { intros x Hx. apply Hmv.
          exact
            (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hx). }
        assert
          (forall x,
              In x (CALLS.moved_by env st1 st') -> ~ In x scope) as Hmv2.
        { intros x Hx. apply Hmv.
          exact
            (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hx). }

        destruct
          (IHe ic ambs1 f1 eq1 st st1 t sst sa
             ce1 xst xst1 u yst ya dlt
             Hwle Hwce Hnd1 Hmv1 Hcsc1 Htsc1 Hambsc1 Hcovered1
             Hambs1len Hfound1 Hun1 Ht Hgen1 Hu Hsat1)
          as (dlt1 & Hres1).
        unfold carries_result_streams in Hres1.
        destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

        assert (listSatisfiable dlt1 (carried r)) as Hsat2'.
        { apply
            (CALLS.listSatisfiable_off
               scope (carried r) (CALLS.moved_by env st st1) dlt dlt1).
          - exact Hcsc2.
          - exact Hmv1.
          - exact Hoff1.
          - exact Hsat2. }
        destruct
          (IH ic ambs2 fr eqsr st1 st' r sa sst'
             ce2 xst1 xst' v ya yst' dlt1
             Hwles Hwces Hnd2 Hmv2 Hcsc2 Htsc2 Hambsc2 Hcovered2
             Hambs2len Hfound Hunr Hr Hgen2 Hv Hsat2')
          as (dlt2 & Hres2).
        unfold carries_result_streams in Hres2.
        destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

        assert
          (stream_rel dlt2 ambs1 t u) as Hrel1'.
        { apply
            (stream_rel_off_scope
               (scope ++ CALLS.moved_by env st st1)
               (CALLS.moved_by env st1 st') dlt1 dlt2 ambs1 t u).
          - apply
              (@Forall_impl ST
                 (st_scoped scope)
                 (st_scoped (scope ++ CALLS.moved_by env st st1))).
            + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
              * apply incl_appl, incl_refl.
              * exact Ha0.
            + exact Hambsc1.
          - apply
              (@Forall_impl LST
                 (fun src => st_scoped scope (fst src))
                 (fun src =>
                    st_scoped
                      (scope ++ CALLS.moved_by env st st1) (fst src))).
            + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
              * apply incl_appl, incl_refl.
              * exact Hsrc.
            + exact Htsc1.
          - exact Htgt1.
          - intros x Hin Hxin. apply in_app_or in Hxin as [Hxin|Hxin].
            + exact (Hmv2 x Hin Hxin).
            + exact
                (CALLS.moved_by_disjoint_local
                   env env_inj st st1 st' x Hxin Hin).
          - exact Hoff2.
          - exact Hrel1. }

        exists dlt2.
        unfold carries_result_streams. split.
        + intros x Hx.
          rewrite Hoff1.
          2: { intro Hin. apply Hx.
               exact
                 (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hin). }
          apply Hoff2. intro Hin. apply Hx.
          exact
            (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hin).
        + split.
          * apply listSatisfiable_app. split; [|exact Hce2].
            exact
              (CALLS.listSatisfiable_off_scope
                 ce1 (scope ++ CALLS.moved_by env st st1)
                 (CALLS.moved_by env st1 st') dlt1 dlt2
                 Hscope1
                 (fun x Hin Hxin =>
                    match in_app_or _ _ _ Hxin with
                    | or_introl Hscope => Hmv2 x Hin Hscope
                    | or_intror Hfirst =>
                        CALLS.moved_by_disjoint_local
                          env env_inj st st1 st' x Hfirst Hin
                    end)
                 Hoff2 Hce1).
          * split.
            -- exact
                 (stream_rel_app
                    dlt2 ambs1 ambs2 t r u v Hrel1' Hrel2).
            -- split.
               ++ apply Forall_app. split.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st1))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc. apply constraint_scoped_incl with
                           (scope1 := scope ++ CALLS.moved_by env st st1).
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_prefix_local
                              env st st1 st' Hf2).
                     --- exact Hscope1.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st1 st'))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc. apply constraint_scoped_incl with
                           (scope1 := scope ++ CALLS.moved_by env st1 st').
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                     --- exact Hscope2.
               ++ apply Forall_app. split.
                  ** apply
                       (@Forall_impl LST
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st1)
                               (fst tgt))
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st')
                               (fst tgt))).
                     --- intros tgt Htgt. apply st_scoped_weaken with
                           (scope1 := scope ++ CALLS.moved_by env st st1).
                         2: exact Htgt.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_prefix_local
                              env st st1 st' Hf2).
                     --- exact Htgt1.
                  ** apply
                       (@Forall_impl LST
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st1 st')
                               (fst tgt))
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st')
                               (fst tgt))).
                     --- intros tgt Htgt. apply st_scoped_weaken with
                           (scope1 := scope ++ CALLS.moved_by env st1 st').
                         2: exact Htgt.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                     --- exact Htgt2.
    Qed.

    Lemma stream_rel_map_when :
      forall dlt g ambs srcs tgts,
        stream_rel dlt ambs srcs tgts ->
        stream_rel dlt ambs
          (List.map (fun t => ljoin t (lvar g)) srcs)
          (List.map (fun t => ljoin t (lvar g)) tgts).
    Proof.
      intros dlt g ambs srcs tgts Hrel.
      induction Hrel as
        [|amb src tgt ambs srcs tgts Hhead Htail IH].
      - constructor.
      - simpl. constructor; [|exact IH].
        unfold ljoin. simpl.
        apply satisfiable_merge_intro.
        + exact (CALLS.satisfiable_merge_grow_l
                   dlt (fst tgt) amb (fst src) Hhead [g]).
        + apply satisfiable_trans with (b := merge (fst src) [g]).
          * apply satisfiable_merge_r.
          * apply satisfiable_merge_r.
    Qed.

    Lemma scoped_map_when :
      forall sc g ts,
        In g sc ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall
          (fun t => st_scoped sc (fst t))
          (List.map (fun t => ljoin t (lvar g)) ts).
    Proof.
      intros sc g ts Hg Hsc.
      induction Hsc as [|t ts Ht Hts IH].
      - constructor.
      - simpl. constructor; [|exact IH].
        unfold ljoin. simpl. apply st_scoped_merge.
        + exact Ht.
        + intros x Hx. destruct Hx as [Hx|[]]. subst x. exact Hg.
    Qed.

    Lemma clock_covered_on_inv :
      forall ck x b g amb,
        Env.find x env = Some g ->
        clock_covered (Con ck x b) amb ->
        clock_covered ck amb.
    Proof.
      intros ck x b g amb Hfind (parent_ty & Hparent & Hincl).
      apply assign_clk_inv in Hparent
        as (ckty & g' & Hparent_ty & Hckty & Hfind').
      rewrite Hfind in Hfind'. inversion Hfind'; subst g'; clear Hfind'.
      subst parent_ty. exists ckty. split; [exact Hckty|].
      intros z Hz. apply Hincl.
      apply in_merge_inv in Hz as [Hz|Hz].
      - apply in_merge_left. exact Hz.
      - apply in_merge_right. apply in_merge_left. exact Hz.
    Qed.

    Lemma clock_covered_on :
      forall ck x b g amb,
        Env.find x env = Some g ->
        clock_covered ck amb ->
        clock_covered (Con ck x b) (merge [g] amb).
    Proof.
      intros ck x b g amb Hfind (ckty & Hckty & Hincl).
      exists (merge ckty [g]). split.
      - simpl. rewrite Hckty, Hfind. reflexivity.
      - intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
        + apply in_merge_right. apply Hincl. apply in_merge_left. exact Hz.
        + apply in_merge_inv in Hz as [Hz|Hz].
          * apply in_merge_right. apply Hincl. apply in_merge_right. exact Hz.
          * apply in_merge_left. exact Hz.
    Qed.

    Lemma satisfiable_ambient_on_normalize :
      forall dlt g amb src tgt,
        satisfiable dlt tgt (merge (merge [g] amb) src) ->
        satisfiable dlt tgt (merge amb (merge [g] src)).
    Proof.
      intros dlt g amb src tgt Hsat.
      apply satisfiable_trans with
        (b := merge (merge [g] amb) src); [exact Hsat|].
      apply satisfiable_merge_intro.
      - apply satisfiable_merge_intro.
        + apply satisfiable_trans with (b := merge [g] src).
          * apply satisfiable_merge_l.
          * apply satisfiable_merge_r.
        + apply satisfiable_merge_l.
      - apply satisfiable_trans with (b := merge [g] src).
        + apply satisfiable_merge_r.
        + apply satisfiable_merge_r.
    Qed.

    Lemma stream_rel_ambient_on_normalize :
      forall dlt g ambs srcs tgts,
        stream_rel dlt (List.map (fun amb => merge [g] amb) ambs)
          srcs tgts ->
        Forall3
          (fun amb src tgt =>
             satisfiable dlt (fst tgt)
               (merge amb (merge [g] (fst src))))
          ambs srcs tgts.
    Proof.
      intros dlt g ambs. induction ambs as [|amb ambs IH];
        intros srcs tgts Hrel.
      - inversion Hrel. constructor.
      - simpl in Hrel.
        inversion Hrel as
          [|amb' src tgt ambs' srcs' tgts' Hhead Htail]; subst.
        constructor.
        + exact
            (satisfiable_ambient_on_normalize
               dlt g amb (fst src) (fst tgt) Hhead).
        + exact (IH srcs' tgts' Htail).
    Qed.

    Lemma clocks_covered_when_inv :
      forall ck x b g (tys : list type) cks ambs,
        Env.find x env = Some g ->
        Forall (Logic.eq ck) cks ->
        List.length tys = List.length cks ->
        clocks_covered
          (List.map (fun _ => Con ck x b) tys) ambs ->
        clocks_covered cks ambs.
    Proof.
      intros ck x b g tys cks ambs Hfind Hclocks.
      revert tys ambs.
      induction Hclocks as [|ck' cks Hck' Hclocks IH];
        intros tys ambs Hlen Hcovered.
      - destruct tys; [|discriminate].
        inversion Hcovered. constructor.
      - destruct tys as [|ty tys]; [discriminate|].
        simpl in Hlen. injection Hlen as Hlen.
        inversion Hcovered as
          [|parent amb parents ambs' Hhead Htail]; subst.
        constructor.
        + exact (clock_covered_on_inv ck' x b g amb Hfind Hhead).
        + exact (IH tys ambs' Hlen Htail).
    Qed.

    Lemma clocks_covered_on_map :
      forall ck x b g (tys : list type) cks ambs,
        Env.find x env = Some g ->
        Forall (Logic.eq (Con ck x b)) cks ->
        List.length tys = List.length cks ->
        clocks_covered (List.map (fun _ => ck) tys) ambs ->
        clocks_covered cks
          (List.map (fun amb => merge [g] amb) ambs).
    Proof.
      intros ck x b g tys cks ambs Hfind Hclocks.
      revert tys ambs.
      induction Hclocks as [|ck' cks Hck' Hclocks IH];
        intros tys ambs Hlen Hcovered.
      - destruct tys; [|discriminate].
        inversion Hcovered. constructor.
      - destruct tys as [|ty tys]; [discriminate|].
        simpl in Hlen. injection Hlen as Hlen.
        inversion Hcovered as
          [|base amb bases ambs' Hhead Htail]; subst.
        simpl. constructor.
        + exact (clock_covered_on ck x b g amb Hfind Hhead).
        + exact (IH tys ambs' Hlen Htail).
    Qed.

    Lemma stream_ambients_scoped_on :
      forall sc g ambs,
        In g sc ->
        stream_ambients_scoped sc ambs ->
        stream_ambients_scoped sc
          (List.map (fun amb => merge [g] amb) ambs).
    Proof.
      intros sc g ambs Hg Hsc.
      induction Hsc as [|amb ambs Hamb Hambs IH].
      - constructor.
      - change
          (stream_ambients_scoped sc
             (merge [g] amb ::
                List.map (fun a => merge [g] a) ambs)).
        constructor; [|exact IH].
        apply st_scoped_merge.
        + intros x Hx. destruct Hx as [Hx|[]]. subst x. exact Hg.
        + exact Hamb.
    Qed.

    Lemma carries_Ewhen_streams :
      forall P es x b a,
        Forall (carries_streams P) es ->
        carries_streams P (Ewhen es x b a).
    Proof.
      intros P es x b [tys ck] Hall is_control
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      apply unnest_exp_Ewhen_inv in Hun as (es1 & Hunn & Hes').
      subst es'.
      assert (List.length es1 = List.length tys) as Hes1len.
      { pose proof
          (unnest_exps_length P es es1 eqs st st' H2 Hunn) as Hlength.
        rewrite H6 in Hlength. exact Hlength. }
      destruct
        (CALLS.unnest_exps_inv P es es1 eqs st st' Hunn)
        as (ess & eqss & Hmap & Hess & Heqss).
      subst es1 eqs.

      rewrite assign_lexp_Ewhen in Has.
      apply sec_bind_inv in Has as (tes & sa & Htes & Has).
      apply sec_bind_inv in Has as (g & sb & Hg & Hret).
      unfold ret in Hret. inversion Hret; subst; clear Hret.
      apply find_env_inv in Hg as (Hg & Hstate).

      destruct
        (CALLS.assign_lexps_unnest_when_inv
           GL env base_ty rst_ty x b tys (Con ck0 x b, None) g
           (List.concat ess)
           ts'' yst yst' Hg Hes1len Has')
        as (tes'' & Htes'' & Hts'').
      subst ts''.

      assert (tes = [] \/ In g scope) as Hgs.
      { destruct tes as [|t0 tes0]; [left; reflexivity|right].
        inversion Htsc as [|z zs Hz Hzr]; subst.
        simpl in Hz. apply Hz. apply in_merge_right. now left. }
      rewrite CALLS.carried_map_when in Hcsc, Hsat.
      assert
        (Forall (fun t => st_scoped scope (fst t)) tes) as Htes_scoped.
      { clear - Htsc.
        induction tes as [|t0 tes0 IHtes].
        - constructor.
        - inversion Htsc as [|z zs Hz Hzr]; subst.
          constructor.
          + simpl in Hz.
            exact (proj1 (st_scoped_merge_inv scope (fst t0) [g] Hz)).
          + exact (IHtes Hzr). }
      assert (clocks_covered (clocksof es) ambs) as Hcovered_es.
      { exact
          (clocks_covered_when_inv
             ck0 x b g tys (clocksof es) ambs Hg H8 H9 Hcovered). }
      assert (List.length ambs = List.length tes) as Hlen_tes.
      { rewrite Hlen, map_length. reflexivity. }

      destruct
        (carries_list_streams_intro P es Hall false ambs ess eqss st st'
           tes sst sa ce xst xst' tes'' yst yst' dlt
           H2 H4 Hnd Hmv Hcsc Htes_scoped Hambsc Hcovered_es Hlen_tes
           Hfound Hmap Htes Hgen Htes'' Hsat)
        as (dlt' & Hres).
      unfold carries_result_streams in Hres.
      destruct Hres as (Hoff & Hce & Hrel & Hscope & Htgt).

      exists dlt'.
      unfold carries_result_streams. split; [exact Hoff|].
      split; [exact Hce|].
      split.
      - exact (stream_rel_map_when dlt' g ambs tes tes'' Hrel).
      - split; [exact Hscope|].
        destruct Hgs as [Hempty|Hgscope].
        + subst tes. inversion Hrel; subst. constructor.
        + apply scoped_map_when.
          * apply in_or_app. left. exact Hgscope.
          * exact Htgt.
    Qed.

    (** Pointwise counterpart of the scalar [ljoin_list_rel] helper.  The
        same ambient list indexes both branches because the joins are made
        stream by stream. *)
    Lemma ljoin_list_rel_streams :
      forall dlt g ambs ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s1
          = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts') us' s2
          = OK (rs', s2') ->
        stream_rel dlt ambs ts ts' ->
        stream_rel dlt ambs us us' ->
        stream_rel dlt ambs rs rs'.
    Proof.
      intros dlt g ambs ts us rs ts' us' rs' s1 s1' s2 s2'
        Hjoin Hjoin' Hts Hus.
      revert us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hus.
      induction Hts as
        [|amb t t' ambs ts ts' Ht Hts IH];
        intros us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hus.
      - inversion Hus. destruct us; simpl in Hjoin; [|discriminate].
        unfold ret in Hjoin. inversion Hjoin; subst.
        simpl in Hjoin'. unfold ret in Hjoin'. inversion Hjoin'; subst.
        constructor.
      - inversion Hus as
          [|amb0 u u' ambs0 us0 us0' Hu Hus0]; subst.
        simpl in Hjoin.
        apply sec_bind_inv in Hjoin as (r & sa & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst; clear Hret.
        simpl in Hjoin'.
        apply sec_bind_inv in Hjoin' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inversion Hret'; subst; clear Hret'.
        constructor.
        + rewrite !fst_ljoin.
          apply satisfiable_merge_intro.
          * apply satisfiable_merge_intro.
            -- apply CALLS.satisfiable_merge_grow_l.
               apply CALLS.satisfiable_merge_grow_l.
               apply satisfiable_merge_r.
            -- apply CALLS.satisfiable_merge_grow_l.
               apply satisfiable_trans with
                 (b := merge amb (fst t)).
               ++ exact Ht.
               ++ apply satisfiable_merge_intro.
                  ** apply satisfiable_merge_l.
                  ** apply satisfiable_trans with
                       (b := merge (fst (lvar g)) (fst t)).
                     --- apply satisfiable_merge_r.
                     --- apply satisfiable_merge_r.
          * apply CALLS.satisfiable_merge_grow_r.
            exact Hu.
        + exact
            (IH us0 r us0' r' s1 s1' s2 s2' Hr Hr' Hus0).
    Qed.

    (** The componentwise join with no head in front: [Efby] and [Earrow]
        join their two operand lists directly, and each result stays above
        its own ambient. *)
    Lemma ljoin_list_rel_plain_streams :
      forall dlt ambs ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list ts us s1 = OK (rs, s1') ->
        ljoin_list ts' us' s2 = OK (rs', s2') ->
        stream_rel dlt ambs ts ts' ->
        stream_rel dlt ambs us us' ->
        stream_rel dlt ambs rs rs'.
    Proof.
      intros dlt ambs ts us rs ts' us' rs' s1 s1' s2 s2'
        Hjoin Hjoin' Hts Hus.
      revert us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hus.
      induction Hts as [|amb t t' ambs0 ts0 ts0' Ht Hts IH];
        intros us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hus.
      - inversion Hus. destruct us; simpl in Hjoin; [|discriminate].
        unfold ret in Hjoin. inversion Hjoin; subst.
        simpl in Hjoin'. unfold ret in Hjoin'. inversion Hjoin'; subst.
        constructor.
      - inversion Hus as [|amb0 u u' ambs1 us0 us0' Hu Hus0]; subst.
        simpl in Hjoin.
        apply sec_bind_inv in Hjoin as (r & sa & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst; clear Hret.
        simpl in Hjoin'.
        apply sec_bind_inv in Hjoin' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inversion Hret'; subst; clear Hret'.
        constructor.
        + rewrite !fst_ljoin.
          apply satisfiable_merge_intro.
          * exact
              (CALLS.satisfiable_merge_grow_l
                 dlt (fst t') amb (fst t) Ht (fst u)).
          * exact
              (CALLS.satisfiable_merge_grow_r
                 dlt (fst u') amb (fst u) Hu (fst t)).
        + exact (IH us0 r us0' r' s1 s1' s2 s2' Hr Hr' Hus0).
    Qed.

    Lemma ljoin_list_rel_streams_on :
      forall dlt g ambs ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s1
          = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts') us' s2
          = OK (rs', s2') ->
        stream_rel dlt (List.map (fun amb => merge [g] amb) ambs) ts ts' ->
        stream_rel dlt (List.map (fun amb => merge [g] amb) ambs) us us' ->
        stream_rel dlt ambs rs rs'.
    Proof.
      intros dlt g ambs ts us rs ts' us' rs' s1 s1' s2 s2'
        Hjoin Hjoin' Hts Hus.
      pose proof
        (stream_rel_ambient_on_normalize dlt g ambs ts ts' Hts) as Htsn.
      pose proof
        (stream_rel_ambient_on_normalize dlt g ambs us us' Hus) as Husn.
      clear Hts Hus.
      revert us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Husn.
      induction Htsn as
        [|amb t t' ambs ts ts' Ht Hts IH];
        intros us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hus.
      - inversion Hus. destruct us; simpl in Hjoin; [|discriminate].
        unfold ret in Hjoin. inversion Hjoin; subst.
        simpl in Hjoin'. unfold ret in Hjoin'. inversion Hjoin'; subst.
        constructor.
      - inversion Hus as
          [|amb0 u u' ambs0 us0 us0' Hu Hus0]; subst.
        simpl in Hjoin.
        apply sec_bind_inv in Hjoin as (r & sa & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst; clear Hret.
        simpl in Hjoin'.
        apply sec_bind_inv in Hjoin' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inversion Hret'; subst; clear Hret'.
        constructor.
        + rewrite !fst_ljoin.
          apply satisfiable_merge_intro.
          * apply satisfiable_merge_intro.
            -- apply satisfiable_trans with
                 (b := merge [g] (fst t)).
               ++ apply satisfiable_merge_l.
               ++ apply satisfiable_trans with
                    (b := merge (merge [g] (fst t)) (fst u)).
                  ** apply satisfiable_merge_l.
                  ** apply satisfiable_merge_r.
            -- exact
                 (CALLS.satisfiable_merge_grow_l
                    dlt (fst t') amb (merge [g] (fst t)) Ht (fst u)).
          * apply satisfiable_trans with
              (b := merge amb (merge [g] (fst u))); [exact Hu|].
            apply satisfiable_merge_intro.
            -- apply satisfiable_merge_l.
            -- apply satisfiable_merge_intro.
               ++ apply satisfiable_trans with
                    (b := merge [g] (fst t)).
                  ** apply satisfiable_merge_l.
                  ** apply satisfiable_trans with
                       (b := merge (merge [g] (fst t)) (fst u)).
                     --- apply satisfiable_merge_l.
                     --- apply satisfiable_merge_r.
               ++ apply satisfiable_trans with
                    (b := merge (merge [g] (fst t)) (fst u)).
                  ** apply satisfiable_merge_r.
                  ** apply satisfiable_merge_r.
        + exact
            (IH us0 r us0' r' s1 s1' s2 s2' Hr Hr' Hus0).
    Qed.

    Lemma clocks_covered_constant_inv :
      forall ck (tys : list type) ambs,
        clocks_covered (List.map (fun _ => ck) tys) ambs ->
        Forall (clock_covered ck) ambs.
    Proof.
      intros ck tys. induction tys as [|ty tys IH];
        intros ambs Hcovered.
      - inversion Hcovered. constructor.
      - inversion Hcovered as
          [|ck' amb cks ambs' Hhead Htail]; subst.
        constructor; [exact Hhead|exact (IH ambs' Htail)].
    Qed.

    Lemma clocks_covered_same :
      forall ck (tys : list type) cks ambs,
        Forall (Logic.eq ck) cks ->
        List.length tys = List.length cks ->
        clocks_covered (List.map (fun _ => ck) tys) ambs ->
        clocks_covered cks ambs.
    Proof.
      intros ck tys cks ambs Hclocks. revert tys ambs.
      induction Hclocks as [|ck' cks Hck' Hclocks IH];
        intros tys ambs Hlen Hcovered.
      - destruct tys; [|discriminate]. inversion Hcovered. constructor.
      - destruct tys as [|ty tys]; [discriminate|].
        simpl in Hlen. injection Hlen as Hlen.
        inversion Hcovered as
          [|clock0 amb clocks ambs' Hhead Htail]; subst.
        constructor; [exact Hhead|exact (IH tys ambs' Hlen Htail)].
    Qed.

    Lemma ljoin_list_input_lengths :
      forall ts us rs st st',
        ljoin_list ts us st = OK (rs, st') ->
        List.length ts = List.length us.
    Proof.
      intros ts. induction ts as [|t ts IH];
        intros us rs st st' Hjoin.
      - destruct us; simpl in Hjoin; [reflexivity|discriminate].
      - destruct us as [|u us]; simpl in Hjoin; [discriminate|].
        apply sec_bind_inv in Hjoin as (r & sm & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst; clear Hret.
        simpl. f_equal. exact (IH us r st st' Hr).
    Qed.

    Lemma stream_head_rel_of_clock :
      forall dlt ck ckty ambs (src tgt : LST),
        assign_clk_type env base_ty ck = Some ckty ->
        satisfiable dlt (fst tgt)
          (merge (merge [rst_ty] ckty) (fst src)) ->
        Forall (clock_covered ck) ambs ->
        Forall
          (fun amb =>
             satisfiable dlt (fst tgt) (merge amb (fst src)))
          ambs.
    Proof.
      intros dlt ck ckty ambs src tgt Hckty Hhead Hcovered.
      induction Hcovered as [|amb ambs Hamb Hambs IH].
      - constructor.
      - constructor; [|exact IH].
        apply satisfiable_trans with
          (b := merge (merge [rst_ty] ckty) (fst src)); [exact Hhead|].
        apply satisfiable_merge_intro.
        + unfold satisfiable. apply hm_ext_incl.
          intros z Hz. apply in_merge_left.
          exact (clock_covered_incl ck amb ckty Hamb Hckty z Hz).
        + apply satisfiable_merge_r.
    Qed.

    Lemma ljoin_list_rel_head_streams :
      forall dlt ambs h h' ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin h t) ts) us s1
          = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin h' t) ts') us' s2
          = OK (rs', s2') ->
        Forall
          (fun amb =>
             satisfiable dlt (fst h') (merge amb (fst h))) ambs ->
        stream_rel dlt ambs ts ts' ->
        stream_rel dlt ambs us us' ->
        stream_rel dlt ambs rs rs'.
    Proof.
      intros dlt ambs h h' ts us rs ts' us' rs' s1 s1' s2 s2'
        Hjoin Hjoin' Hheads Hts Hus.
      revert us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hheads Hus.
      induction Hts as
        [|amb t t' ambs ts ts' Ht Hts IH];
        intros us rs us' rs' s1 s1' s2 s2' Hjoin Hjoin' Hheads Hus.
      - inversion Hheads. inversion Hus.
        destruct us; simpl in Hjoin; [|discriminate].
        unfold ret in Hjoin. inversion Hjoin; subst.
        simpl in Hjoin'. unfold ret in Hjoin'. inversion Hjoin'; subst.
        constructor.
      - inversion Hheads as [|amb0 ambs0 Hhead Hheadsr]; subst.
        inversion Hus as
          [|amb0 u u' ambs0 us0 us0' Hu Hus0]; subst.
        simpl in Hjoin.
        apply sec_bind_inv in Hjoin as (r & sa & Hr & Hret).
        unfold ret in Hret. inversion Hret; subst; clear Hret.
        simpl in Hjoin'.
        apply sec_bind_inv in Hjoin' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inversion Hret'; subst; clear Hret'.
        constructor.
        + rewrite !fst_ljoin.
          apply satisfiable_merge_intro.
          * apply satisfiable_merge_intro.
            -- apply CALLS.satisfiable_merge_grow_l.
               apply CALLS.satisfiable_merge_grow_l.
               exact Hhead.
            -- apply CALLS.satisfiable_merge_grow_l.
               apply satisfiable_trans with
                 (b := merge amb (fst t)); [exact Ht|].
               apply satisfiable_merge_intro.
               ++ apply satisfiable_merge_l.
               ++ apply satisfiable_trans with
                    (b := merge (fst h) (fst t)).
                  ** apply satisfiable_merge_r.
                  ** apply satisfiable_merge_r.
          * exact
              (CALLS.satisfiable_merge_grow_r
                 dlt (fst u') amb (fst u) Hu
                 (merge (fst h) (fst t))).
        + exact
            (IH us0 r us0' r' s1 s1' s2 s2'
               Hr Hr' Hheadsr Hus0).
    Qed.

    Lemma carries_Emerge_control_streams :
      forall P ckid es1 es2 tys cl,
        Forall (carries_streams P) es1 ->
        Forall (carries_streams P) es2 ->
        carries_at_streams P true (Emerge ckid es1 es2 (tys, cl)).
    Proof.
      intros P ckid es1 es2 tys cl Hall1 Hall2
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      apply unnest_exp_Emerge_control_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & Hes' & Heqs).
      subst es' eqs.
      assert (st_follows st st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es1 f1 eqs1 st st1 Hun1). }
      assert (st_follows st1 st') as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es2 f2 eqs2 st1 st' Hun2). }

      rewrite assign_lexp_Emerge in Has.
      apply sec_bind_inv in Has as (g & sa & Hg & Has).
      apply sec_bind_inv in Has as (tes1 & sb & Htes1 & Has).
      apply sec_bind_inv in Has as (tes2 & sc & Htes2 & Hj).
      apply find_env_inv in Hg as (Hg & Hsa). subst sa.

      assert (Forall normalized_cexp (List.concat f1)) as Hnorm1.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es1 f1 eqs1 st st1 Hun1). }
      assert (Forall normalized_cexp (List.concat f2)) as Hnorm2.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es2 f2 eqs2 st1 st' Hun2). }
      assert (List.length (List.concat f1) = List.length tys) as Hflen1.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es1 f1 eqs1 st st1 H4 Hun1) as Hlength.
        rewrite H7 in Hlength. exact Hlength. }
      assert (List.length (List.concat f2) = List.length tys) as Hflen2.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es2 f2 eqs2 st1 st' H6 Hun2) as Hlength.
        rewrite H8 in Hlength. exact Hlength. }
      destruct
        (CALLS.assign_lexps_unnest_merge_inv
           GL env base_ty rst_ty ckid (ck, None) g
           (List.concat f1) (List.concat f2) tys ts'' yst yst'
           Hg Hnorm1 Hnorm2 Hflen1 Hflen2 Has')
        as (tes1'' & tes2'' & Htes1'' & Htes2'' & Hyst & Hj'').
      subst yst'.

      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqs1) (List.concat eqs2) ce xst xst' Hgen)
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & Hce).
      subst ce.

      assert
        (carried ts = cmerge (carried tes1) (carried tes2)) as Hcarried.
      { rewrite (ljoin_list_carried
                   (List.map (fun t => ljoin (lvar g) t) tes1)
                   tes2 ts sc sst' Hj).
        rewrite CALLS.carried_map_merge_l. reflexivity. }
      rewrite Hcarried in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (Hcsc1 & Hcsc2).
      apply listSatisfiable_cmerge in Hsat as (Hsat1 & Hsat2).
      destruct
        (CALLS.ljoin_list_scoped_inv
           scope g tes1 tes2 ts sc sst' Hj Htsc)
        as (Htsc1 & Htsc2 & Hgs).

      set (on_ambs := List.map (fun amb => merge [g] amb) ambs).
      assert (stream_ambients_scoped scope on_ambs) as Hon_scoped.
      { destruct Hgs as [Hempty|Hgscope].
        - subst tes1.
          pose proof
            (ljoin_list_length
               (List.map (fun t => ljoin (lvar g) t) []) tes2
               ts sc sst' Hj) as Htslen.
          simpl in Htslen. apply length_zero_iff_nil in Htslen. subst ts.
          simpl in Hlen. apply length_zero_iff_nil in Hlen. subst ambs.
          constructor.
        - exact
            (stream_ambients_scoped_on scope g ambs Hgscope Hambsc). }
      assert
        (clocks_covered (clocksof es1) on_ambs) as Hcovered1.
      { exact
          (clocks_covered_on_map
             ck ckid true g tys (clocksof es1) ambs
             Hg H11 H13 Hcovered). }
      assert
        (clocks_covered (clocksof es2) on_ambs) as Hcovered2.
      { exact
          (clocks_covered_on_map
             ck ckid false g tys (clocksof es2) ambs
             Hg H12 H14 Hcovered). }
      pose proof
        (ljoin_list_length
           (List.map (fun t => ljoin (lvar g) t) tes1) tes2
           ts sc sst' Hj) as Hjoinlen.
      rewrite map_length in Hjoinlen.
      assert (List.length on_ambs = List.length tes1) as Hon_len1.
      { unfold on_ambs. rewrite map_length, Hlen, Hjoinlen. reflexivity. }
      assert (List.length on_ambs = List.length tes2) as Hon_len2.
      { unfold on_ambs. rewrite map_length, Hlen, Hjoinlen.
        assert (List.length tes1 = List.length tes2) as Hbranches.
        { clear - Hj.
          revert tes2 ts sc sst' Hj.
          induction tes1 as [|t tes1 IH];
            intros tes2 ts sc sst' Hj.
          - destruct tes2; simpl in Hj; [reflexivity|discriminate].
          - destruct tes2 as [|u tes2]; simpl in Hj; [discriminate|].
            apply sec_bind_inv in Hj as (r & sm & Hr & Hret).
            unfold ret in Hret. inversion Hret; subst; clear Hret.
            simpl. f_equal. exact (IH tes2 r sc sst' Hr). }
        exact Hbranches. }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st' Hf2 Hfound). }

      assert
        (Permutation
           (vars_defined (List.concat eqs1) ++ st_ids st) (st_ids st1))
        as Hperm1.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P true es1 f1 eqs1 st st1 H4 Hun1). }
      assert
        (NoDup (vars_defined (List.concat eqs1) ++ st_ids st)) as Hnd1.
      { apply CALLS.NoDup_vd_app_l with
          (eqs2 := List.concat eqs2). exact Hnd. }
      assert
        (NoDup (vars_defined (List.concat eqs2) ++ st_ids st1)) as Hnd2.
      { apply CALLS.NoDup_vd_app_r with
          (eqs1 := List.concat eqs1) (s := st_ids st).
        - exact Hperm1.
        - exact Hnd. }
      assert
        (forall x,
            In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        exact
          (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hx). }
      assert
        (forall x,
            In x (CALLS.moved_by env st1 st') -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        exact
          (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hx). }

      destruct
        (carries_list_streams_intro P es1 Hall1 true on_ambs
           f1 eqs1 st st1 tes1 sst sb ce1 xst xst1 tes1'' yst yst dlt
           H4 H5 Hnd1 Hmv1 Hcsc1 Htsc1 Hon_scoped Hcovered1 Hon_len1
           Hfound1 Hun1 Htes1 Hgen1 Htes1'' Hsat1)
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried tes2)) as Hsat2'.
      { apply
          (CALLS.listSatisfiable_off
             scope (carried tes2) (CALLS.moved_by env st st1)
             dlt dlt1).
        - exact Hcsc2.
        - exact Hmv1.
        - exact Hoff1.
        - exact Hsat2. }
      destruct
        (carries_list_streams_intro P es2 Hall2 true on_ambs
           f2 eqs2 st1 st' tes2 sb sc ce2 xst1 xst' tes2'' yst yst dlt1
           H6 H9 Hnd2 Hmv2 Hcsc2 Htsc2 Hon_scoped Hcovered2 Hon_len2
           Hfound Hun2 Htes2 Hgen2 Htes2'' Hsat2')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      assert (stream_rel dlt2 on_ambs tes1 tes1'') as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st1)
             (CALLS.moved_by env st1 st') dlt1 dlt2
             on_ambs tes1 tes1'').
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hon_scoped.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc1.
        - exact Htgt1.
        - intros x Hin Hxin. apply in_app_or in Hxin as [Hxin|Hxin].
          + exact (Hmv2 x Hin Hxin).
          + exact
              (CALLS.moved_by_disjoint_local
                 env env_inj st st1 st' x Hxin Hin).
        - exact Hoff2.
        - exact Hrel1. }

      exists dlt2.
      unfold carries_result_streams. split.
      - intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st1 st' Hf2 x Hin). }
        apply Hoff2. intro Hin. apply Hx.
        exact
          (CALLS.moved_by_suffix_local env st st1 st' Hf1 x Hin).
      - split.
        + apply listSatisfiable_app. split; [|exact Hce2].
          exact
            (CALLS.listSatisfiable_off_scope
               ce1 (scope ++ CALLS.moved_by env st st1)
               (CALLS.moved_by env st1 st') dlt1 dlt2
               Hscope1
               (fun x Hin Hxin =>
                  match in_app_or _ _ _ Hxin with
                  | or_introl Hscope => Hmv2 x Hin Hscope
                  | or_intror Hfirst =>
                      CALLS.moved_by_disjoint_local
                        env env_inj st st1 st' x Hfirst Hin
                  end)
               Hoff2 Hce1).
        + split.
          * exact
              (ljoin_list_rel_streams_on
                 dlt2 g ambs tes1 tes2 ts tes1'' tes2'' ts''
                 sc sst' yst yst Hj Hj'' Hrel1' Hrel2).
          * split.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st1))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc. apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st1).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact (CALLS.moved_by_prefix_local env st st1 st' Hf2).
                  ** exact Hscope1.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st1 st'))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc. apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st1 st').
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact (CALLS.moved_by_suffix_local env st st1 st' Hf1).
                  ** exact Hscope2.
            -- destruct Hgs as [Hempty|Hgscope].
               ++ subst tes1. inversion Hrel1'; subst.
                  simpl in Hj''. destruct tes2''; [|discriminate].
                  unfold ret in Hj''. inversion Hj''; subst. constructor.
               ++ apply
                    (CALLS.ljoin_list_scoped
                       (scope ++ CALLS.moved_by env st st') g
                       tes1'' tes2'' ts'' yst yst).
                  ** apply in_or_app. left. exact Hgscope.
                  ** exact Hj''.
                  ** apply
                       (@Forall_impl LST
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st1)
                               (fst tgt))
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st')
                               (fst tgt))).
                     --- intros tgt Htgt. apply st_scoped_weaken with
                           (scope1 := scope ++ CALLS.moved_by env st st1).
                         2: exact Htgt.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_prefix_local
                              env st st1 st' Hf2).
                     --- exact Htgt1.
                  ** apply
                       (@Forall_impl LST
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st1 st')
                               (fst tgt))
                          (fun tgt =>
                             st_scoped
                               (scope ++ CALLS.moved_by env st st')
                               (fst tgt))).
                     --- intros tgt Htgt. apply st_scoped_weaken with
                           (scope1 := scope ++ CALLS.moved_by env st1 st').
                         2: exact Htgt.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                     --- exact Htgt2.
    Qed.

    Lemma carries_Eite_control_streams :
      forall P e0 es1 es2 tys ck,
        carries_streams P e0 ->
        Forall (carries_streams P) es1 ->
        Forall (carries_streams P) es2 ->
        carries_at_streams P true (Eite e0 es1 es2 (tys, ck)).
    Proof.
      intros P e0 es1 es2 tys ck IH0 Hall1 Hall2
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      apply unnest_exp_Eite_control_inv in Hun
        as (f0 & eqs0 & st0 & f1 & eqs1 & st1 & f2 & eqs2
            & Hun0 & Hun1 & Hun2 & Hes' & Heqs).
      subst es' eqs.
      assert (st_follows st st0) as Hf0.
      { exact (unnest_exp_st_follows P e0 false (f0, eqs0) st st0 Hun0). }
      assert (st_follows st0 st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es1 f1 eqs1 st0 st1 Hun1). }
      assert (st_follows st1 st') as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es2 f2 eqs2 st1 st' Hun2). }
      assert (st_follows st0 st') as Hf0'.
      { transitivity st1; assumption. }
      assert (st_follows st st1) as Hf01.
      { transitivity st0; assumption. }

      rewrite assign_lexp_Eite in Has.
      apply sec_bind_inv in Has as (t0 & sa & Ht0 & Has).
      apply sec_bind_inv in Has as (th & sb & Hth & Has).
      apply sec_bind_inv in Has as (tes1 & sc & Htes1 & Has).
      apply sec_bind_inv in Has as (tes2 & sd & Htes2 & Hj).
      apply single_inv in Hth as (Ht0single & Hth). subst t0.
      assert (List.length tes1 = List.length tys) as Htes1len.
      { pose proof
          (assign_lexps_length
             P GL env base_ty rst_ty es1 H6 tes1 sb sc Htes1) as Hlength.
        rewrite H9 in Hlength. exact Hlength. }
      assert (tes1 <> []) as Htes1_nonempty.
      { intro Hempty. subst tes1. simpl in Htes1len. lia. }

      assert (Forall normalized_lexp f0) as Hnorm0.
      { exact (unnest_exp_normalized_lexp P e0 f0 eqs0 st st0 Hun0). }
      pose proof
        (unnest_exp_one_streams P e0 f0 eqs0 st st0 H4 H8 Hun0)
        as Hfone.
      assert (Forall normalized_cexp (List.concat f1)) as Hnorm1.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es1 f1 eqs1 st0 st1 Hun1). }
      assert (Forall normalized_cexp (List.concat f2)) as Hnorm2.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es2 f2 eqs2 st1 st' Hun2). }
      assert (List.length (List.concat f1) = List.length tys) as Hflen1.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es1 f1 eqs1 st0 st1 H6 Hun1) as Hlength.
        rewrite H9 in Hlength. exact Hlength. }
      assert (List.length (List.concat f2) = List.length tys) as Hflen2.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es2 f2 eqs2 st1 st' H7 Hun2) as Hlength.
        rewrite H10 in Hlength. exact Hlength. }
      assert (normalized_lexp (hd_default f0)) as Hnorm0'.
      { rewrite Hfone in Hnorm0. inversion Hnorm0; subst. assumption. }
      apply CALLS.assign_lexps_unnest_ite_inv in Has'
        as (ignored & tes1'' & tes2'' & Htes1'' & Htes2'' & Htarget).
      2: exact Hnorm0'.
      2: exact Hnorm1.
      2: exact Hnorm2.
      2: exact Hflen1.
      2: exact Hflen2.
      assert (List.length tes1'' = List.length tys) as Htes1''len.
      { rewrite <- Hflen1.
        destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat f1)
             Hnorm1 tes1'' yst yst Htes1'')
          as (Hstate & Hlength & Hcarried & Hpure).
        exact Hlength. }
      destruct Htarget as
        [(th'' & Hth'' & Hj'')|(Hnil & Hnil1 & Hnil2)].
      2: { rewrite Hnil in Htes1''len. simpl in Htes1''len. lia. }

      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv eqs0
           (List.concat eqs1 ++ List.concat eqs2) ce xst xst' Hgen)
        as (ce0 & cer & xst0 & Hgen0 & Hgenr & Hce).
      subst ce.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqs1) (List.concat eqs2) cer xst0 xst' Hgenr)
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & Hcer).
      subst cer.

      assert
        (carried ts =
           cmerge (carried (List.map (fun t => ljoin th t) tes1))
             (carried tes2)) as Hcarried.
      { exact
          (ljoin_list_carried
             (List.map (fun t => ljoin th t) tes1) tes2 ts sd sst' Hj). }
      rewrite Hcarried in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (HcscM & Hcsc2).
      apply listSatisfiable_cmerge in Hsat as (HsatM & Hsat2).
      assert (constraints_scoped scope (carried tes1)) as Hcsc1.
      { apply constraints_scoped_sub with
          (cs := carried (List.map (fun t => ljoin th t) tes1)).
        - intros c Hc. exact (CALLS.carried_map_ljoin_mono th tes1 c Hc).
        - exact HcscM. }
      assert (listSatisfiable dlt (carried tes1)) as Hsat1.
      { apply listSatisfiable_sub with
          (cs := carried (List.map (fun t => ljoin th t) tes1)).
        - intros c Hc. exact (CALLS.carried_map_ljoin_mono th tes1 c Hc).
        - exact HsatM. }
      destruct tes1 as [|tf tes1r]; [contradiction|].
      assert (constraints_scoped scope (snd th)) as Hcsc0.
      { apply constraints_scoped_sub with
          (cs := carried (List.map (fun t => ljoin th t) (tf :: tes1r))).
        - intros c Hc.
          exact (CALLS.carried_map_ljoin_head th tf tes1r c Hc).
        - exact HcscM. }
      assert (listSatisfiable dlt (snd th)) as Hsat0.
      { apply listSatisfiable_sub with
          (cs := carried (List.map (fun t => ljoin th t) (tf :: tes1r))).
        - intros c Hc.
          exact (CALLS.carried_map_ljoin_head th tf tes1r c Hc).
        - exact HsatM. }
      destruct
        (CALLS.ljoin_list_scoped_head_inv
           scope th (tf :: tes1r) tes2 ts sd sst' Hj Htsc)
        as (Htsc1 & Htsc2 & Hhead_scoped).
      destruct Hhead_scoped as [Himpossible|Hth_scoped]; [discriminate|].

      destruct tys as [|ty tys]; [simpl in H18; lia|].
      inversion Hcovered as
        [|clock0 amb amb_clocks ambs0 Hamb_covered Hambs_covered]; subst.
      inversion Hambsc as [|amb0 ambs1 Hamb_scoped Hambs_scoped]; subst.
      destruct Hamb_covered as (ckty & Hckty & Hamb_incl).
      set (clock_amb := merge [rst_ty] ckty).
      assert (st_scoped scope clock_amb) as Hclock_amb_scoped.
      { intros x Hx. apply Hamb_scoped. exact (Hamb_incl x Hx). }
      assert (clock_covered ck0 clock_amb) as Hclock_amb_covered.
      { exists ckty. split; [exact Hckty|apply incl_refl]. }
      assert (Forall (clock_covered ck0) (amb :: ambs0)) as Hall_covered.
      { exact
          (clocks_covered_constant_inv
             ck0 (ty :: tys) (amb :: ambs0) Hcovered). }

      assert (state_clocks_found st0) as Hfound0.
      { exact (state_clocks_found_prefix st0 st' Hf0' Hfound). }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st' Hf2 Hfound). }
      assert
        (Permutation (vars_defined eqs0 ++ st_ids st) (st_ids st0))
        as Hperm0.
      { exact (unnest_exp_vars_perm P e0 false f0 eqs0 st st0 H4 Hun0). }
      assert
        (NoDup (vars_defined eqs0 ++ st_ids st)) as Hnd0a.
      { apply CALLS.NoDup_vd_app_l with
          (eqs2 := List.concat eqs1 ++ List.concat eqs2). exact Hnd. }
      assert
        (NoDup
           (vars_defined (List.concat eqs1 ++ List.concat eqs2)
              ++ st_ids st0)) as Hnd12.
      { apply CALLS.NoDup_vd_app_r with (eqs1 := eqs0) (s := st_ids st).
        - exact Hperm0.
        - exact Hnd. }
      assert
        (Permutation
           (vars_defined (List.concat eqs1) ++ st_ids st0) (st_ids st1))
        as Hperm1.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P true es1 f1 eqs1 st0 st1 H6 Hun1). }
      assert
        (NoDup (vars_defined (List.concat eqs1) ++ st_ids st0)) as Hnd1.
      { apply CALLS.NoDup_vd_app_l with
          (eqs2 := List.concat eqs2). exact Hnd12. }
      assert
        (NoDup (vars_defined (List.concat eqs2) ++ st_ids st1)) as Hnd2.
      { apply CALLS.NoDup_vd_app_r with
          (eqs1 := List.concat eqs1) (s := st_ids st0).
        - exact Hperm1.
        - exact Hnd12. }
      assert
        (forall x,
            In x (CALLS.moved_by env st st0) -> ~ In x scope) as Hmv0.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_prefix_local env st st0 st' Hf0' x Hx). }
      assert
        (forall x,
            In x (CALLS.moved_by env st0 st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st0 st' Hf0 x).
        exact (CALLS.moved_by_prefix_local env st0 st1 st' Hf2 x Hx). }
      assert
        (forall x,
            In x (CALLS.moved_by env st1 st') -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_suffix_local env st st1 st' Hf01 x Hx). }

      assert
        (assign_lexps GL env base_ty rst_ty f0 yst = OK ([th''], yst))
        as Hth_target.
      { rewrite Hfone at 1.
        exact
          (assign_lexps_single_intro
             GL env base_ty rst_ty (hd_default f0) [th''] yst yst Hth''). }
      assert
        (Forall (fun t => st_scoped scope (fst t)) [th]) as Hth_scopeds.
      { constructor; [exact Hth_scoped|constructor]. }
      assert (stream_ambients_scoped scope [clock_amb]) as Hclock_amb_scopeds.
      { constructor; [exact Hclock_amb_scoped|constructor]. }
      assert (clocks_covered [ck0] [clock_amb]) as Hclock_amb_covereds.
      { constructor; [exact Hclock_amb_covered|constructor]. }
      assert (clocks_covered (clockof e0) [clock_amb]) as He0_covered.
      { rewrite H13. exact Hclock_amb_covereds. }
      destruct
        (IH0 false [clock_amb] f0 eqs0 st st0 [th] sst sa
           ce0 xst xst0 [th''] yst yst dlt
           H4 H5 Hnd0a Hmv0
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc0
              (CALLS.carried_single th))
           Hth_scopeds Hclock_amb_scopeds He0_covered
           (@Coq.Init.Logic.eq_refl nat 1) Hfound0
           Hun0 Ht0 Hgen0 Hth_target
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat0
              (CALLS.carried_single th)))
        as (dlt0 & Hres0).
      unfold carries_result_streams in Hres0.
      destruct Hres0 as (Hoff0 & Hce0 & Hrel0 & Hscope0 & Htgt0).

      assert
        (clocks_covered (clocksof es1) (amb :: ambs0)) as Hbranch_covered1.
      { exact
          (clocks_covered_same
             ck0 (ty :: tys) (clocksof es1) (amb :: ambs0)
             H14 H16 Hcovered). }
      assert
        (clocks_covered (clocksof es2) (amb :: ambs0)) as Hbranch_covered2.
      { exact
          (clocks_covered_same
             ck0 (ty :: tys) (clocksof es2) (amb :: ambs0)
             H15 H17 Hcovered). }
      pose proof
        (ljoin_list_length
           (List.map (fun t => ljoin th t) (tf :: tes1r)) tes2
           ts sd sst' Hj) as Hjoin_length.
      rewrite map_length in Hjoin_length.
      assert
        (List.length (amb :: ambs0) = List.length (tf :: tes1r))
        as Hbranch_len1.
      { rewrite Hlen, Hjoin_length. reflexivity. }
      assert (List.length (tf :: tes1r) = List.length tes2) as Hinputs_length.
      { rewrite <- map_length with (f := fun t => ljoin th t).
        exact
          (ljoin_list_input_lengths
             (List.map (fun t => ljoin th t) (tf :: tes1r)) tes2
             ts sd sst' Hj). }
      assert (List.length (amb :: ambs0) = List.length tes2)
        as Hbranch_len2.
      { rewrite Hbranch_len1. exact Hinputs_length. }

      assert (listSatisfiable dlt0 (carried (tf :: tes1r))) as Hsat1'.
      { apply
          (CALLS.listSatisfiable_off
             scope (carried (tf :: tes1r))
             (CALLS.moved_by env st st0) dlt dlt0).
        - exact Hcsc1.
        - exact Hmv0.
        - exact Hoff0.
        - exact Hsat1. }
      destruct
        (carries_list_streams_intro P es1 Hall1 true (amb :: ambs0)
           f1 eqs1 st0 st1 (tf :: tes1r) sa sc
           ce1 xst0 xst1 tes1'' yst yst dlt0
           H6 H11 Hnd1 Hmv1 Hcsc1 Htsc1
           Hambsc Hbranch_covered1 Hbranch_len1
           Hfound1 Hun1 Htes1 Hgen1 Htes1'' Hsat1')
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried tes2)) as Hsat2'.
      { apply
          (CALLS.listSatisfiable_off
             scope (carried tes2) (CALLS.moved_by env st0 st1)
             dlt0 dlt1).
        - exact Hcsc2.
        - exact Hmv1.
        - exact Hoff1.
        - apply
            (CALLS.listSatisfiable_off
               scope (carried tes2) (CALLS.moved_by env st st0)
               dlt dlt0 Hcsc2 Hmv0 Hoff0 Hsat2). }
      destruct
        (carries_list_streams_intro P es2 Hall2 true (amb :: ambs0)
           f2 eqs2 st1 st' tes2 sc sd ce2 xst1 xst' tes2'' yst yst dlt1
           H7 H12 Hnd2 Hmv2 Hcsc2 Htsc2
           Hambsc Hbranch_covered2 Hbranch_len2
           Hfound Hun2 Htes2 Hgen2 Htes2'' Hsat2')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      assert
        (incl (CALLS.moved_by env st st0)
           (CALLS.moved_by env st st')) as Hin0.
      { exact (CALLS.moved_by_prefix_local env st st0 st' Hf0'). }
      assert
        (incl (CALLS.moved_by env st0 st1)
           (CALLS.moved_by env st st')) as Hin1.
      { intros x Hx.
        apply (CALLS.moved_by_suffix_local env st st0 st' Hf0 x).
        exact
          (CALLS.moved_by_prefix_local env st0 st1 st' Hf2 x Hx). }
      assert
        (incl (CALLS.moved_by env st1 st')
           (CALLS.moved_by env st st')) as Hin2.
      { exact (CALLS.moved_by_suffix_local env st st1 st' Hf01). }

      assert
        (CALLS.agree_off (CALLS.moved_by env st0 st') dlt0 dlt2)
        as Hoff02.
      { intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st0 st1 st' Hf2 x Hin). }
        apply Hoff2. intro Hin. apply Hx.
        exact
          (CALLS.moved_by_suffix_local env st0 st1 st' Hf1 x Hin). }
      assert
        (forall x,
           In x (CALLS.moved_by env st0 st') ->
           ~ In x (scope ++ CALLS.moved_by env st st0)) as Hsep0.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - apply (Hmv x).
          + exact
              (CALLS.moved_by_suffix_local env st st0 st' Hf0 x Hin).
          + exact Hscope.
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st0 st' x Hfirst Hin). }
      assert
        (forall x,
           In x (CALLS.moved_by env st1 st') ->
           ~ In x (scope ++ CALLS.moved_by env st0 st1)) as Hsep1.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - exact (Hmv2 x Hin Hscope).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st0 st1 st' x Hfirst Hin). }

      assert (stream_rel dlt2 [clock_amb] [th] [th'']) as Hrel0'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st0)
             (CALLS.moved_by env st0 st') dlt0 dlt2
             [clock_amb] [th] [th'']).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st0))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hclock_amb_scopeds.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st0) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Hth_scopeds.
        - exact Htgt0.
        - exact Hsep0.
        - exact Hoff02.
        - exact Hrel0. }
      assert
        (satisfiable dlt2 (fst th'')
           (merge clock_amb (fst th))) as Hhead.
      { inversion Hrel0' as
          [|a0 src tgt ambs' srcs' tgts' Hhead' Htail]; subst.
        exact Hhead'. }
      assert
        (Forall
           (fun a0 =>
              satisfiable dlt2 (fst th'') (merge a0 (fst th)))
           (amb :: ambs0)) as Hheads.
      { exact
          (stream_head_rel_of_clock
             dlt2 ck0 ckty (amb :: ambs0) th th''
             Hckty Hhead Hall_covered). }

      assert
        (stream_rel dlt2 (amb :: ambs0)
           (tf :: tes1r) tes1'') as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st0 st1)
             (CALLS.moved_by env st1 st') dlt1 dlt2
             (amb :: ambs0) (tf :: tes1r) tes1'').
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st0 st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hambsc.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st0 st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc1.
        - exact Htgt1.
        - exact Hsep1.
        - exact Hoff2.
        - exact Hrel1. }

      exists dlt2.
      unfold carries_result_streams. split.
      - intros x Hx.
        rewrite Hoff0.
        2: { intro Hin. apply Hx. exact (Hin0 x Hin). }
        apply Hoff02. intro Hin. apply Hx.
        exact
          (CALLS.moved_by_suffix_local env st st0 st' Hf0 x Hin).
      - split.
        + apply listSatisfiable_app. split.
          * exact
              (CALLS.listSatisfiable_off_scope
                 ce0 (scope ++ CALLS.moved_by env st st0)
                 (CALLS.moved_by env st0 st') dlt0 dlt2
                 Hscope0 Hsep0 Hoff02 Hce0).
          * apply listSatisfiable_app. split.
            -- exact
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st0 st1)
                    (CALLS.moved_by env st1 st') dlt1 dlt2
                    Hscope1 Hsep1 Hoff2 Hce1).
            -- exact Hce2.
        + split.
          * exact
              (ljoin_list_rel_head_streams
                 dlt2 (amb :: ambs0) th th''
                 (tf :: tes1r) tes2 ts tes1'' tes2'' ts''
                 sd sst' yst yst Hj Hj'' Hheads Hrel1' Hrel2).
          * split.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st0))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc. apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st0).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr. exact Hin0.
                  ** exact Hscope0.
               ++ apply Forall_app. split.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st0 st1))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc. apply constraint_scoped_incl with
                          (scope1 := scope ++ CALLS.moved_by env st0 st1).
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr. exact Hin1.
                     --- exact Hscope1.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st1 st'))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc. apply constraint_scoped_incl with
                          (scope1 := scope ++ CALLS.moved_by env st1 st').
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr. exact Hin2.
                     --- exact Hscope2.
            -- apply
                 (CALLS.ljoin_list_scoped_head
                    (scope ++ CALLS.moved_by env st st') th''
                    tes1'' tes2'' ts'' yst yst).
               ++ inversion Htgt0 as [|q qs Hq Hqs]; subst.
                  apply st_scoped_weaken with
                    (scope1 := scope ++ CALLS.moved_by env st st0).
                  ** apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr. exact Hin0.
                  ** exact Hq.
               ++ exact Hj''.
               ++ apply
                    (@Forall_impl LST
                       (fun tgt =>
                          st_scoped
                            (scope ++ CALLS.moved_by env st0 st1)
                            (fst tgt))
                       (fun tgt =>
                          st_scoped
                            (scope ++ CALLS.moved_by env st st')
                            (fst tgt))).
                  ** intros tgt Htgt. apply st_scoped_weaken with
                       (scope1 := scope ++ CALLS.moved_by env st0 st1).
                     --- apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr. exact Hin1.
                     --- exact Htgt.
                  ** exact Htgt1.
               ++ apply
                    (@Forall_impl LST
                       (fun tgt =>
                          st_scoped
                            (scope ++ CALLS.moved_by env st1 st')
                            (fst tgt))
                       (fun tgt =>
                          st_scoped
                            (scope ++ CALLS.moved_by env st st')
                            (fst tgt))).
                  ** intros tgt Htgt. apply st_scoped_weaken with
                       (scope1 := scope ++ CALLS.moved_by env st1 st').
                     --- apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr. exact Hin2.
                     --- exact Htgt.
                  ** exact Htgt2.
    Qed.



    (** * The lifting form of [Emerge]

        Under [is_control = false] the pass does not stop at the merges: it
        mints one variable per result with [idents_for_anns] and emits a
        definition for each.  The branches are unnested exactly as in the
        control form, so the first half of this proof is that one; what
        follows is [lifted_defs_streams], which needs one ambient per minted
        variable.  [declared_ambients_of_state] supplies them: the minted
        identifiers land in the fresh state with their annotations, the
        naming run knows their clocks, and the result clocks are the ones the
        contract already covers. *)

    Lemma carries_Emerge_lift_streams :
      forall P ckid es1 es2 tys cl,
        Forall (carries_streams P) es1 ->
        Forall (carries_streams P) es2 ->
        carries_at_streams P false (Emerge ckid es1 es2 (tys, cl)).
    Proof.
      intros P ckid es1 es2 tys cl Hall1 Hall2
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      pose proof Hun as Hunm. pose proof Hnd as Hnd0.
      apply CALLS.unnest_exp_Emerge_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & st2 & xs
            & Hun1 & Hun2 & Hids & Hes' & Heqs).
      subst es' eqs.

      (** the states the run passed through *)
      assert (st_follows st st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es1 f1 eqs1 st st1 Hun1). }
      assert (st_follows st1 st2) as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es2 f2 eqs2 st1 st2 Hun2). }
      assert (st_follows st2 st') as Hf3.
      { exact
          (idents_for_anns_st_follows
             (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids). }
      assert (st_follows st st2) as Hf12 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf23 by (etransitivity; eauto).
      assert (st_follows st st') as Hf13 by (etransitivity; eauto).
      assert (state_clocks_found st2) as Hfound2.
      { exact (state_clocks_found_prefix st2 st' Hf3 Hfound). }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st2 Hf2 Hfound2). }

      (** the source type, taken apart *)
      rewrite assign_lexp_Emerge in Has.
      apply sec_bind_inv in Has as (g & sa & Hg & Has).
      apply sec_bind_inv in Has as (tes1 & sb & Htes1 & Has).
      apply sec_bind_inv in Has as (tes2 & sc & Htes2 & Hj).
      apply find_env_inv in Hg as (Hg & Hsa). subst sa.

      (** the target: one variable per result *)
      destruct
        (CALLS.assign_lexps_evars GL env base_ty rst_ty xs ts'' yst yst' Has')
        as (Hyst & Hevars). subst yst'.

      (** the emitted equations: the definitions, then the branches *)
      rewrite CALLS.emitted_defs_combine_form in Hgen, Hnd.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.map (fun '(x, e) => ([x], [e]))
              (combine (List.map fst xs)
                 (unnest_merge ckid (List.concat f1) (List.concat f2)
                    tys (ck, None))))
           (List.concat eqs1 ++ List.concat eqs2) ce xst xst' Hgen)
        as (ced & cer & xstd & Hgend & Hgenr & Hce). subst ce.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqs1) (List.concat eqs2) cer xstd xst' Hgenr)
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & Hcer). subst cer.

      (** shapes and lengths of the unnested branches *)
      assert (Forall normalized_cexp (List.concat f1)) as Hc1.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es1 f1 eqs1 st st1 Hun1). }
      assert (Forall normalized_cexp (List.concat f2)) as Hc2.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es2 f2 eqs2 st1 st2 Hun2). }
      assert (List.length (List.concat f1) = List.length tys) as Hle1.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es1 f1 eqs1 st st1 H4 Hun1) as Hlength.
        rewrite H7 in Hlength. exact Hlength. }
      assert (List.length (List.concat f2) = List.length tys) as Hle2.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es2 f2 eqs2 st1 st2 H6 Hun2) as Hlength.
        rewrite H8 in Hlength. exact Hlength. }
      assert (List.length xs = List.length tys) as Hlxs.
      { rewrite
          (idents_for_anns_length
             (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids).
        apply map_length. }
      assert (List.length (List.map fst xs) = List.length tys) as Hlbs.
      { rewrite map_length. exact Hlxs. }

      (** the branches' target typings, read off the emitted merges *)
      destruct
        (CALLS.defs_operand_types_merge
           GL env base_ty rst_ty cenv (List.map fst xs) ckid (ck, None)
           (List.concat f1) (List.concat f2) tys ced xst xstd
           Hc1 Hc2 Hlbs Hle1 Hle2 Hgend)
        as (ts1x & ts2x & Ht1x & Ht2x).
      assert (assign_lexps GL env base_ty rst_ty (List.concat f1) yst
              = OK (ts1x, yst)) as Ht1y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat f1) Hc1 ts1x xst xst Ht1x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }
      assert (assign_lexps GL env base_ty rst_ty (List.concat f2) yst
              = OK (ts2x, yst)) as Ht2y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat f2) Hc2 ts2x xst xst Ht2x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }

      (** what the source carries, split along the join *)
      assert (carried ts = cmerge (carried tes1) (carried tes2)) as Hcarried.
      { rewrite (ljoin_list_carried
                   (List.map (fun t => ljoin (lvar g) t) tes1)
                   tes2 ts sc sst' Hj).
        rewrite CALLS.carried_map_merge_l. reflexivity. }
      rewrite Hcarried in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (Hcsc1 & Hcsc2).
      apply listSatisfiable_cmerge in Hsat as (Hsat1 & Hsat2).
      pose proof Htsc as Htscall.
      destruct
        (CALLS.ljoin_list_scoped_inv
           scope g tes1 tes2 ts sc sst' Hj Htsc)
        as (Htsc1 & Htsc2 & Hgs).

      (** the branches run under the sampled ambients *)
      set (on_ambs := List.map (fun amb => merge [g] amb) ambs).
      pose proof
        (ljoin_list_length
           (List.map (fun t => ljoin (lvar g) t) tes1) tes2
           ts sc sst' Hj) as Hjoinlen.
      rewrite map_length in Hjoinlen.
      assert (List.length tes1 = List.length tes2) as Hbranches.
      { clear - Hj.
        revert tes2 ts sc sst' Hj.
        induction tes1 as [|t tes1 IH];
          intros tes2 ts sc sst' Hj.
        - destruct tes2; simpl in Hj; [reflexivity|discriminate].
        - destruct tes2 as [|u tes2]; simpl in Hj; [discriminate|].
          apply sec_bind_inv in Hj as (r & sm & Hr & Hret).
          unfold ret in Hret. inversion Hret; subst; clear Hret.
          simpl. f_equal. exact (IH tes2 r sc sst' Hr). }
      assert (stream_ambients_scoped scope on_ambs) as Hon_scoped.
      { destruct Hgs as [Hempty|Hgscope].
        - subst tes1. simpl in Hjoinlen.
          assert (ts = []) as Hts0.
          { apply length_zero_iff_nil. now rewrite <- Hjoinlen. }
          subst ts. simpl in Hlen.
          apply length_zero_iff_nil in Hlen. subst ambs. constructor.
        - exact (stream_ambients_scoped_on scope g ambs Hgscope Hambsc). }
      assert (clocks_covered (clocksof es1) on_ambs) as Hcovered1.
      { exact
          (clocks_covered_on_map
             ck ckid true g tys (clocksof es1) ambs
             Hg H11 H13 Hcovered). }
      assert (clocks_covered (clocksof es2) on_ambs) as Hcovered2.
      { exact
          (clocks_covered_on_map
             ck ckid false g tys (clocksof es2) ambs
             Hg H12 H14 Hcovered). }
      assert (List.length on_ambs = List.length tes1) as Hon_len1.
      { unfold on_ambs. rewrite map_length, Hlen, Hjoinlen. reflexivity. }
      assert (List.length on_ambs = List.length tes2) as Hon_len2.
      { unfold on_ambs. rewrite map_length, Hlen, Hjoinlen.
        exact Hbranches. }

      (** the emitted branch equations are well separated *)
      assert
        (NoDup (vars_defined (List.concat eqs1 ++ List.concat eqs2)
                  ++ st_ids st)) as Hndr.
      { exact
          (CALLS.NoDup_vd_drop
             (List.map (fun '(x, e) => ([x], [e]))
                (combine (List.map fst xs)
                   (unnest_merge ckid (List.concat f1) (List.concat f2)
                      tys (ck, None))))
             (List.concat eqs1 ++ List.concat eqs2) (st_ids st) Hnd). }
      assert
        (Permutation
           (vars_defined (List.concat eqs1) ++ st_ids st) (st_ids st1))
        as Hperm1.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P true es1 f1 eqs1 st st1 H4 Hun1). }
      assert
        (NoDup (vars_defined (List.concat eqs1) ++ st_ids st)) as Hnd1.
      { exact
          (CALLS.NoDup_vd_app_l
             (List.concat eqs1) (List.concat eqs2) (st_ids st) Hndr). }
      assert
        (NoDup (vars_defined (List.concat eqs2) ++ st_ids st1)) as Hnd2.
      { exact
          (CALLS.NoDup_vd_app_r
             (List.concat eqs1) (List.concat eqs2) (st_ids st) (st_ids st1)
             Hperm1 Hndr). }
      assert
        (forall x, In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hx). }
      assert
        (forall x, In x (CALLS.moved_by env st1 st2) -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        exact
          (CALLS.moved_by_suffix_local
             env st st1 st' Hf1 x
             (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hx)). }

      (** the two branch witnesses *)
      destruct
        (carries_list_streams_intro P es1 Hall1 true on_ambs
           f1 eqs1 st st1 tes1 sst sb ce1 xstd xstm ts1x yst yst dlt
           H4 H5 Hnd1 Hmv1 Hcsc1 Htsc1 Hon_scoped Hcovered1 Hon_len1
           Hfound1 Hun1 Htes1 Hgen1 Ht1y Hsat1)
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried tes2)) as Hsat2'.
      { exact
          (CALLS.listSatisfiable_off
             scope (carried tes2) (CALLS.moved_by env st st1)
             dlt dlt1 Hcsc2 Hmv1 Hoff1 Hsat2). }
      destruct
        (carries_list_streams_intro P es2 Hall2 true on_ambs
           f2 eqs2 st1 st2 tes2 sb sc ce2 xstm xst' ts2x yst yst dlt1
           H6 H9 Hnd2 Hmv2 Hcsc2 Htsc2 Hon_scoped Hcovered2 Hon_len2
           Hfound2 Hun2 Htes2 Hgen2 Ht2y Hsat2')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      (** the first branch's relation, at the second branch's witness *)
      assert (stream_rel dlt2 on_ambs tes1 ts1x) as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st1)
             (CALLS.moved_by env st1 st2) dlt1 dlt2
             on_ambs tes1 ts1x).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hon_scoped.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc1.
        - exact Htgt1.
        - intros x Hin Hxin. apply in_app_or in Hxin as [Hxin|Hxin].
          + exact (Hmv2 x Hin Hxin).
          + exact
              (CALLS.moved_by_disjoint_local
                 env env_inj st st1 st2 x Hxin Hin).
        - exact Hoff2.
        - exact Hrel1. }

      (** the merges the pass built, and their pointwise relation *)
      assert
        (Forall2
           (fun e t =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
              /\ snd t = []) (List.concat f1) ts1x) as Hew1.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat f1) ts1x xst xst
             Hc1 Ht1x). }
      assert
        (Forall2
           (fun e t =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
              /\ snd t = []) (List.concat f2) ts2x) as Hew2.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat f2) ts2x xst xst
             Hc2 Ht2x). }
      destruct
        (CALLS.unnest_merge_types
           GL env base_ty rst_ty ckid (ck, None) g
           (List.concat f1) (List.concat f2) tys ts1x ts2x xst
           Hg Hew1 Hew2 Hle1 Hle2)
        as (rs & Hjr & Hallr).
      assert (stream_rel dlt2 ambs ts rs) as Hrelrs.
      { exact
          (ljoin_list_rel_streams_on
             dlt2 g ambs tes1 tes2 ts ts1x ts2x rs sc sst' xst xst
             Hj Hjr Hrel1' Hrel2). }

      (** one ambient per minted variable, read off its declared clock *)
      assert
        (List.map fst
           (List.map (fun '(id, (ty, (cl0, _))) => (id, (ty, cl0))) xs)
         = List.map fst xs) as Hmapfst.
      { rewrite map_map. apply map_ext.
        intros (id & (ty0 & (cl0 & nm0))). reflexivity. }
      assert
        (Forall2 (fun xa ck' => snd (snd xa) = ck')
           (List.map (fun '(id, (ty, (cl0, _))) => (id, (ty, cl0))) xs)
           (List.map (fun _ : type => ck) tys)) as Hclkalign.
      { pose proof
          (idents_for_anns_values
             (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids)
          as Hvals.
        clear - Hvals. revert tys Hvals.
        induction xs as [|xa xs IH]; intros tys Hvals.
        - destruct tys; [constructor|discriminate Hvals].
        - destruct tys as [|ty tys]; [discriminate Hvals|].
          simpl in Hvals. injection Hvals as Hhd Htl.
          destruct xa as (id & a). simpl in Hhd. subst a.
          simpl. constructor; [reflexivity|exact (IH tys Htl)]. }
      assert (declared_ambients (List.map fst xs) ambs) as Hdecl.
      { rewrite <- Hmapfst.
        exact
          (declared_ambients_of_state
             (List.map (fun '(id, (ty, (cl0, _))) => (id, (ty, cl0))) xs)
             st' (List.map (fun _ : type => ck) tys) ambs
             (idents_for_anns_incl
                (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids)
             Hclkalign Hfound Hcovered). }

      (** the minted variables are fresh, and their names with them *)
      assert
        (Permutation
           (vars_defined
              (combine (List.map (fun '(id, _) => [id]) xs)
                 (List.map (fun e => [e])
                    (unnest_merge ckid (List.concat f1) (List.concat f2)
                       tys (ck, None)))
               ++ List.concat eqs1 ++ List.concat eqs2) ++ st_ids st)
           (st_ids st')) as Hpall.
      { exact
          (unnest_exp_vars_perm
             P (Emerge ckid es1 es2 (tys, (ck, None))) false
             (List.map (fun '(id, ann0) => Evar id ann0) xs)
             (combine (List.map (fun '(id, _) => [id]) xs)
                (List.map (fun e => [e])
                   (unnest_merge ckid (List.concat f1) (List.concat f2)
                      tys (ck, None)))
              ++ List.concat eqs1 ++ List.concat eqs2)
             st st' Hwl Hunm). }
      assert (NoDup (st_ids st')) as Hndst'.
      { exact (Permutation_NoDup Hpall Hnd0). }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx.
      { exact
          (idents_for_anns_vars_perm
             (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids). }
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx.
      { rewrite Hpx. exact Hndst'. }
      assert (NoDup (List.map fst xs)) as Hndfst.
      { exact (NoDup_app_l (List.map fst xs) (st_ids st2) Hndx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st2 st')) as Hbnew.
      { intros b Hb.
        unfold CALLS.sec_of in Hb. apply in_flat_map in Hb as (x & Hx & Hb).
        unfold CALLS.moved_by, CALLS.EXPR.moved_by, CALLS.sec_of.
        apply in_flat_map. exists x. split; [|exact Hb].
        apply CALLS.new_ids_spec. split.
        - exact
            (idents_for_anns_incl_ids
               (List.map (fun ty => (ty, (ck, None))) tys) xs st2 st' Hids
               x Hx).
        - exact
            (NoDup_app_In x (List.map fst xs) (st_ids st2) Hndx Hx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   ~ In b (scope ++ CALLS.moved_by env st st2)) as Hsepx.
      { intros b Hb Hin. apply in_app_or in Hin as [Hin|Hin].
        - apply (Hmv b); [|exact Hin].
          exact
            (CALLS.moved_by_suffix_local
               env st st2 st' Hf12 b (Hbnew b Hb)).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st2 st' b Hin (Hbnew b Hb)). }

      (** the merges' types live in the scope the definitions run at *)
      assert (List.length tes1 = List.length tys) as Hlents1.
      { rewrite
          (CALLS.assign_lexps_length
             P GL env base_ty rst_ty es1 H4 tes1 sst sb Htes1).
        exact H7. }
      assert
        (Forall
           (fun t => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t))
           ts1x) as Htgt1'.
      { apply
          (@Forall_impl LST
             (fun t => st_scoped (scope ++ CALLS.moved_by env st st1) (fst t))
             (fun t =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t))).
        - intros t0 Ht0.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st st1).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_prefix_local env st st1 st2 Hf2).
          + exact Ht0.
        - exact Htgt1. }
      assert
        (Forall
           (fun t => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t))
           ts2x) as Htgt2'.
      { apply
          (@Forall_impl LST
             (fun t => st_scoped (scope ++ CALLS.moved_by env st1 st2) (fst t))
             (fun t =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t))).
        - intros t0 Ht0.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st1 st2).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_suffix_local env st st1 st2 Hf1).
          + exact Ht0.
        - exact Htgt2. }
      assert
        (Forall
           (fun r => st_scoped (scope ++ CALLS.moved_by env st st2) (fst r))
           rs) as Hscrs.
      { destruct Hgs as [Hempty|Hgscope].
        - assert (tys = []) as Htys0.
          { rewrite Hempty in Hlents1. simpl in Hlents1.
            destruct tys; [reflexivity|discriminate Hlents1]. }
          rewrite Htys0 in Hallr.
          rewrite CALLS.unnest_merge_tys_nil in Hallr.
          inversion Hallr; subst. constructor.
        - exact
            (CALLS.ljoin_list_scoped
               (scope ++ CALLS.moved_by env st st2) g ts1x ts2x rs xst xst
               (in_or_app scope (CALLS.moved_by env st st2) g
                  (or_introl Hgscope))
               Hjr Htgt1' Htgt2'). }

      (** the aligned premise the emitted definitions consume *)
      assert
        (Forall3
           (fun a e src =>
              forall tf s s',
                assign_lexp_type GL env base_ty rst_ty e s = OK ([tf], s') ->
                satisfiable dlt2 (fst tf) (merge a (fst src))
                /\ st_scoped (scope ++ CALLS.moved_by env st st2) (fst tf))
           ambs
           (unnest_merge ckid (List.concat f1) (List.concat f2) tys (ck, None))
           ts) as Hlift3.
      { unfold stream_rel in Hrelrs. clear - Hallr Hrelrs Hscrs.
        revert Hallr Hscrs.
        generalize
          (unnest_merge ckid (List.concat f1) (List.concat f2) tys (ck, None))
          as rhss.
        induction Hrelrs as [|a src r ambs0 ts0 rs0 Hhead Hrest IH];
          intros rhss Hallr Hscrs.
        - inversion Hallr; subst. constructor.
        - destruct rhss as [|e rhss]; inversion Hallr as
            [|e0 r0 rhss0 rs1 Hq Hallr']; subst.
          inversion Hscrs as [|r1 rs2 Hsc0 Hscrs']; subst.
          constructor.
          + intros tf s s' Htf. destruct Hq as (_ & _ & Hq3).
            rewrite (Hq3 tf s s' Htf). split; [exact Hhead|exact Hsc0].
          + exact (IH rhss Hallr' Hscrs'). }
      assert
        (Forall
           (fun e =>
              (match e with Eapp _ _ _ _ => False | _ => True end)
              /\ forall ts0 s s',
                   assign_lexp_type GL env base_ty rst_ty e s = OK (ts0, s') ->
                   s' = s /\ List.length ts0 = 1 /\ carried ts0 = [])
           (unnest_merge ckid (List.concat f1) (List.concat f2)
              tys (ck, None))) as Hpure.
      { clear - Hallr.
        induction Hallr as [|e r rhss0 rs0 Hq Hrest IH]; [constructor|].
        destruct Hq as (Hq1 & Hq2 & _).
        constructor; [split; [exact Hq1|exact Hq2]|exact IH]. }
      assert
        (List.length (List.map fst xs)
         = List.length
             (unnest_merge ckid (List.concat f1) (List.concat f2)
                tys (ck, None))) as Hlend.
      { rewrite Hlbs. symmetry.
        exact
          (unnest_merge_length
             ckid (List.concat f1) (List.concat f2) tys (ck, None)
             Hle1 Hle2). }

      (** the emitted definitions *)
      destruct
        (lifted_defs_streams
           (scope ++ CALLS.moved_by env st st2) (List.map fst xs)
           (unnest_merge ckid (List.concat f1) (List.concat f2)
              tys (ck, None))
           ts ambs ced xst xstd dlt2
           Hndfst Hlend Hsepx Hdecl
           (@Forall_impl ST (st_scoped scope)
              (st_scoped (scope ++ CALLS.moved_by env st st2))
              (fun a0 Ha0 =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) a0
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Ha0)
              ambs Hambsc)
           Hpure
           (@Forall_impl LST
              (fun src => st_scoped scope (fst src))
              (fun src =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst src))
              (fun src Hsrc =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) (fst src)
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Hsrc)
              ts Htscall)
           Hlift3 Hgend)
        as (dlt3 & Hoff3 & Hced & Hscoped & Hrel3).

      (** the minted names are among the ones the whole run moved *)
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st st')) as Hincx.
      { intros b Hb.
        exact
          (CALLS.moved_by_suffix_local
             env st st2 st' Hf12 b (Hbnew b Hb)). }

      (** the results' relation, at the names the pass bound them to *)
      assert (stream_rel dlt3 ambs ts ts'') as Hrelfin.
      { unfold stream_rel. clear - Hrel3 Hevars.
        revert ambs ts Hrel3.
        induction Hevars as [|xa t xs0 ts0 Hxa Hrest IH];
          intros ambs ts Hrel3.
        - inversion Hrel3; subst. constructor.
        - simpl in Hrel3.
          inversion Hrel3 as
            [|a0 x0 src0 ambs1 xs1 ts1 Hhead Hrest3]; subst.
          destruct Hxa as (b & Hb & Ht). subst t.
          constructor.
          + rewrite fst_lvar. exact (Hhead b Hb).
          + exact (IH ambs1 ts1 Hrest3). }

      exists dlt3. unfold carries_result_streams. split.
      - (** the witness moved only where the run did *)
        intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hin). }
        rewrite Hoff2.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_suffix_local
                  env st st1 st' Hf1 x
                  (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hin)). }
        apply Hoff3. intro Hin. apply Hx. exact (Hincx x Hin).
      - split.
        + (** every emitted constraint still holds *)
          apply listSatisfiable_app. split; [exact Hced|].
          apply listSatisfiable_app. split.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce1 (scope ++ CALLS.moved_by env st st1)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope1.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_prefix_local env st st1 st2 Hf2 y Hin).
            -- exact Hoff3.
            -- apply
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st st1)
                    (CALLS.moved_by env st1 st2) dlt1 dlt2).
               ++ exact Hscope1.
               ++ intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
                  ** exact (Hmv2 y Hy Hin).
                  ** exact
                       (CALLS.moved_by_disjoint_local
                          env env_inj st st1 st2 y Hin Hy).
               ++ exact Hoff2.
               ++ exact Hce1.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce2 (scope ++ CALLS.moved_by env st1 st2)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope2.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_suffix_local env st st1 st2 Hf1 y Hin).
            -- exact Hoff3.
            -- exact Hce2.
        + split; [exact Hrelfin|]. split.
          * (** and mentions only names in scope or moved *)
            apply Forall_app. split.
            -- apply
                 (@Forall_impl constraint
                    (constraint_scoped
                       ((scope ++ CALLS.moved_by env st st2)
                          ++ sec_of (List.map fst xs)))
                    (constraint_scoped
                       (scope ++ CALLS.moved_by env st st'))).
               ++ intros c Hc.
                  apply constraint_scoped_incl with
                    (scope1 := (scope ++ CALLS.moved_by env st st2)
                                 ++ sec_of (List.map fst xs)).
                  2: exact Hc.
                  apply incl_app; [apply incl_app|].
                  ** apply incl_appl, incl_refl.
                  ** apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st2 st' Hf3).
                  ** apply incl_appr. exact Hincx.
               ++ exact Hscoped.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st1))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st1).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st1 st' Hf23).
                  ** exact Hscope1.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st1 st2))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st1 st2).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     apply incl_tran with
                       (m := CALLS.moved_by env st1 st').
                     --- exact
                           (CALLS.moved_by_prefix_local
                              env st1 st2 st' Hf3).
                     --- exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                  ** exact Hscope2.
          * (** the bound results are names the run minted *)
            apply
              (CALLS.Forall2_right_In
                 (fun xa t =>
                    exists b, Env.find (fst xa) env = Some b /\ t = lvar b)
                 (fun tgt =>
                    st_scoped (scope ++ CALLS.moved_by env st st') (fst tgt))
                 xs ts'' Hevars).
            intros xa t Hxa Hp. destruct Hp as (b & Hb & Ht). subst t.
            rewrite fst_lvar. intros y Hy.
            destruct Hy as [Hy|[]]. subst y.
            apply in_or_app. right. apply Hincx.
            unfold CALLS.sec_of. apply in_flat_map. exists (fst xa).
            split; [now apply in_map|]. rewrite Hb. now left.
    Qed.


    (** * The lifting form of [Eite]

        The same shape as the merge's lifting form, with the scrutinee in
        front: its singleton relation is carried across both branch
        witnesses, [stream_head_rel_of_clock] spreads its declared-clock
        bound over the aligned result ambients, and what the join produces is
        then handed to [lifted_defs_streams] against the variables
        [idents_for_anns] minted. *)

    Lemma carries_Eite_lift_streams :
      forall P e0 es1 es2 tys ck,
        carries_streams P e0 ->
        Forall (carries_streams P) es1 ->
        Forall (carries_streams P) es2 ->
        carries_at_streams P false (Eite e0 es1 es2 (tys, ck)).
    Proof.
      intros P e0 es1 es2 tys ck IH0 Hall1 Hall2
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      pose proof Hun as Hunm. pose proof Hnd as Hnd0.
      apply CALLS.unnest_exp_Eite_inv in Hun
        as (f0 & eqs0 & st0 & f1 & eqs1 & st1 & f2 & eqs2 & st2 & xs
            & Hun0 & Hun1 & Hun2 & Hids & Hes' & Heqs).
      subst es' eqs.

      (** the four stages of the run *)
      assert (st_follows st st0) as Hf0.
      { exact (unnest_exp_st_follows P e0 false (f0, eqs0) st st0 Hun0). }
      assert (st_follows st0 st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es1 f1 eqs1 st0 st1 Hun1). }
      assert (st_follows st1 st2) as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P true es2 f2 eqs2 st1 st2 Hun2). }
      assert (st_follows st2 st') as Hf3.
      { exact
          (idents_for_anns_st_follows
             (List.map (fun ty => (ty, (ck0, None))) tys) xs st2 st' Hids). }
      assert (st_follows st st1) as Hf01 by (etransitivity; eauto).
      assert (st_follows st0 st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf13 by (etransitivity; eauto).
      assert (st_follows st st2) as Hf012 by (etransitivity; eauto).
      assert (st_follows st0 st') as Hf03 by (etransitivity; eauto).
      assert (st_follows st st') as Hfall by (etransitivity; eauto).
      assert (state_clocks_found st2) as Hfound2.
      { exact (state_clocks_found_prefix st2 st' Hf3 Hfound). }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st2 Hf2 Hfound2). }
      assert (state_clocks_found st0) as Hfound0.
      { exact (state_clocks_found_prefix st0 st1 Hf1 Hfound1). }

      (** the source type *)
      rewrite assign_lexp_Eite in Has.
      apply sec_bind_inv in Has as (t0 & sa & Ht0 & Has).
      apply sec_bind_inv in Has as (th & sb & Hth & Has).
      apply sec_bind_inv in Has as (tes1 & sc & Htes1 & Has).
      apply sec_bind_inv in Has as (tes2 & sd & Htes2 & Hj).
      apply single_inv in Hth as (Ht0single & Hth). subst t0 sb.

      (** the target: one variable per result *)
      destruct
        (CALLS.assign_lexps_evars GL env base_ty rst_ty xs ts'' yst yst' Has')
        as (Hyst & Hevars). subst yst'.

      (** the emitted equations *)
      rewrite CALLS.emitted_defs_combine_form in Hgen, Hnd.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.map (fun '(x, e) => ([x], [e]))
              (combine (List.map fst xs)
                 (unnest_ite (hd_default f0) (List.concat f1)
                    (List.concat f2) tys (ck0, None))))
           (eqs0 ++ List.concat eqs1 ++ List.concat eqs2) ce xst xst' Hgen)
        as (ced & cer & xstd & Hgend & Hgenr & Hce). subst ce.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           eqs0 (List.concat eqs1 ++ List.concat eqs2) cer xstd xst' Hgenr)
        as (ce0 & cer2 & xst0s & Hgen0 & Hgenr2 & Hcer). subst cer.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqs1) (List.concat eqs2) cer2 xst0s xst' Hgenr2)
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & Hcer2). subst cer2.

      (** shapes and lengths *)
      assert (Forall normalized_lexp f0) as Hnorm0.
      { exact (unnest_exp_normalized_lexp P e0 f0 eqs0 st st0 Hun0). }
      pose proof
        (unnest_exp_one_streams P e0 f0 eqs0 st st0 H4 H8 Hun0) as Hfone.
      assert (normalized_lexp (hd_default f0)) as Hnorm0'.
      { rewrite Hfone in Hnorm0. inversion Hnorm0; subst. assumption. }
      assert (Forall normalized_cexp (List.concat f1)) as Hnorm1.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es1 f1 eqs1 st0 st1 Hun1). }
      assert (Forall normalized_cexp (List.concat f2)) as Hnorm2.
      { exact
          (CALLS.map_bind2_unnest_normalized
             P es2 f2 eqs2 st1 st2 Hun2). }
      assert (List.length (List.concat f1) = List.length tys) as Hflen1.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es1 f1 eqs1 st0 st1 H6 Hun1) as Hlength.
        rewrite H9 in Hlength. exact Hlength. }
      assert (List.length (List.concat f2) = List.length tys) as Hflen2.
      { pose proof
          (map_bind2_unnest_exp_length
             P true es2 f2 eqs2 st1 st2 H7 Hun2) as Hlength.
        rewrite H10 in Hlength. exact Hlength. }
      assert (List.length xs = List.length tys) as Hlxs.
      { rewrite
          (idents_for_anns_length
             (List.map (fun ty => (ty, (ck0, None))) tys) xs st2 st' Hids).
        apply map_length. }
      assert (List.length (List.map fst xs) = List.length tys) as Hlbs.
      { rewrite map_length. exact Hlxs. }

      (** the branches' and the scrutinee's target typings *)
      destruct
        (CALLS.defs_operand_types_ite
           GL env base_ty rst_ty cenv (List.map fst xs) (hd_default f0)
           (ck0, None) (List.concat f1) (List.concat f2) tys ced xst xstd
           Hnorm0' Hnorm1 Hnorm2 Hlbs Hflen1 Hflen2 Hgend)
        as (ts1x & ts2x & Ht1x & Ht2x & Hheadty).
      assert (exists th'', forall s,
                 assign_lexp_type GL env base_ty rst_ty (hd_default f0) s
                 = OK ([th''], s)) as (th'' & Hth'').
      { destruct Hheadty as [Hbsnil|Hsome]; [|exact Hsome].
        exfalso. rewrite Hbsnil in Hlbs. simpl in Hlbs.
        rewrite <- Hlbs in H18. lia. }
      assert (assign_lexps GL env base_ty rst_ty (List.concat f1) yst
              = OK (ts1x, yst)) as Ht1y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat f1) Hnorm1 ts1x xst xst Ht1x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }
      assert (assign_lexps GL env base_ty rst_ty (List.concat f2) yst
              = OK (ts2x, yst)) as Ht2y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat f2) Hnorm2 ts2x xst xst Ht2x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }
      assert (assign_lexps GL env base_ty rst_ty f0 yst = OK ([th''], yst))
        as Hth_target.
      { rewrite Hfone at 1.
        exact
          (assign_lexps_single_intro
             GL env base_ty rst_ty (hd_default f0) [th''] yst yst
             (Hth'' yst)). }

      (** what the source carries, split along the join *)
      assert (List.length tes1 = List.length tys) as Htes1len.
      { pose proof
          (assign_lexps_length
             P GL env base_ty rst_ty es1 H6 tes1 sa sc Htes1) as Hlength.
        rewrite H9 in Hlength. exact Hlength. }
      assert
        (carried ts
         = cmerge (carried (List.map (fun t => ljoin th t) tes1))
             (carried tes2)) as Hcarried.
      { exact
          (ljoin_list_carried
             (List.map (fun t => ljoin th t) tes1) tes2 ts sd sst' Hj). }
      rewrite Hcarried in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (HcscM & Hcsc2).
      apply listSatisfiable_cmerge in Hsat as (HsatM & Hsat2).
      assert (constraints_scoped scope (carried tes1)) as Hcsc1.
      { apply constraints_scoped_sub with
          (cs := carried (List.map (fun t => ljoin th t) tes1)).
        - intros c Hc. exact (CALLS.carried_map_ljoin_mono th tes1 c Hc).
        - exact HcscM. }
      assert (listSatisfiable dlt (carried tes1)) as Hsat1.
      { apply listSatisfiable_sub with
          (cs := carried (List.map (fun t => ljoin th t) tes1)).
        - intros c Hc. exact (CALLS.carried_map_ljoin_mono th tes1 c Hc).
        - exact HsatM. }
      destruct tes1 as [|tf tes1r].
      { exfalso. simpl in Htes1len. rewrite <- Htes1len in H18. lia. }
      assert (constraints_scoped scope (snd th)) as Hcsc0.
      { apply constraints_scoped_sub with
          (cs := carried (List.map (fun t => ljoin th t) (tf :: tes1r))).
        - intros c Hc.
          exact (CALLS.carried_map_ljoin_head th tf tes1r c Hc).
        - exact HcscM. }
      assert (listSatisfiable dlt (snd th)) as Hsat0.
      { apply listSatisfiable_sub with
          (cs := carried (List.map (fun t => ljoin th t) (tf :: tes1r))).
        - intros c Hc.
          exact (CALLS.carried_map_ljoin_head th tf tes1r c Hc).
        - exact HsatM. }
      destruct
        (CALLS.ljoin_list_scoped_head_inv
           scope th (tf :: tes1r) tes2 ts sd sst' Hj Htsc)
        as (Htsc1 & Htsc2 & Hhead_scoped).
      destruct Hhead_scoped as [Himpossible|Hth_scoped]; [discriminate|].

      (** the result clocks, and the ambient the scrutinee runs under *)
      destruct tys as [|ty tys]; [simpl in H18; lia|].
      inversion Hcovered as
        [|clock0 amb amb_clocks ambs0 Hamb_covered Hambs_covered]; subst.
      inversion Hambsc as [|amb0 ambs1 Hamb_scoped Hambs_scoped]; subst.
      destruct Hamb_covered as (ckty & Hckty & Hamb_incl).
      set (clock_amb := merge [rst_ty] ckty).
      assert (st_scoped scope clock_amb) as Hclock_amb_scoped.
      { intros x Hx. apply Hamb_scoped. exact (Hamb_incl x Hx). }
      assert (clock_covered ck0 clock_amb) as Hclock_amb_covered.
      { exists ckty. split; [exact Hckty|apply incl_refl]. }
      assert (Forall (clock_covered ck0) (amb :: ambs0)) as Hall_covered.
      { exact
          (clocks_covered_constant_inv
             ck0 (ty :: tys) (amb :: ambs0) Hcovered). }

      (** the emitted branch equations are well separated *)
      assert
        (NoDup
           (vars_defined (eqs0 ++ List.concat eqs1 ++ List.concat eqs2)
              ++ st_ids st)) as Hndr.
      { exact
          (CALLS.NoDup_vd_drop
             (List.map (fun '(x, e) => ([x], [e]))
                (combine (List.map fst xs)
                   (unnest_ite (hd_default f0) (List.concat f1)
                      (List.concat f2) (ty :: tys) (ck0, None))))
             (eqs0 ++ List.concat eqs1 ++ List.concat eqs2)
             (st_ids st) Hnd). }
      assert
        (Permutation (vars_defined eqs0 ++ st_ids st) (st_ids st0))
        as Hperm0.
      { exact (unnest_exp_vars_perm P e0 false f0 eqs0 st st0 H4 Hun0). }
      assert (NoDup (vars_defined eqs0 ++ st_ids st)) as Hnd0a.
      { exact
          (CALLS.NoDup_vd_app_l
             eqs0 (List.concat eqs1 ++ List.concat eqs2)
             (st_ids st) Hndr). }
      assert
        (NoDup
           (vars_defined (List.concat eqs1 ++ List.concat eqs2)
              ++ st_ids st0)) as Hnd12.
      { exact
          (CALLS.NoDup_vd_app_r
             eqs0 (List.concat eqs1 ++ List.concat eqs2)
             (st_ids st) (st_ids st0) Hperm0 Hndr). }
      assert
        (Permutation
           (vars_defined (List.concat eqs1) ++ st_ids st0) (st_ids st1))
        as Hperm1.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P true es1 f1 eqs1 st0 st1 H6 Hun1). }
      assert
        (NoDup (vars_defined (List.concat eqs1) ++ st_ids st0)) as Hnd1.
      { exact
          (CALLS.NoDup_vd_app_l
             (List.concat eqs1) (List.concat eqs2) (st_ids st0) Hnd12). }
      assert
        (NoDup (vars_defined (List.concat eqs2) ++ st_ids st1)) as Hnd2.
      { exact
          (CALLS.NoDup_vd_app_r
             (List.concat eqs1) (List.concat eqs2)
             (st_ids st0) (st_ids st1) Hperm1 Hnd12). }
      assert
        (forall x, In x (CALLS.moved_by env st st0) -> ~ In x scope) as Hmv0.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_prefix_local env st st0 st' Hf03 x Hx). }
      assert
        (forall x, In x (CALLS.moved_by env st0 st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st0 st' Hf0 x).
        exact (CALLS.moved_by_prefix_local env st0 st1 st' Hf13 x Hx). }
      assert
        (forall x, In x (CALLS.moved_by env st1 st2) -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st1 st' Hf01 x).
        exact (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hx). }

      (** the scrutinee *)
      assert (Forall (fun t => st_scoped scope (fst t)) [th]) as Hth_scopeds.
      { constructor; [exact Hth_scoped|constructor]. }
      assert (stream_ambients_scoped scope [clock_amb]) as Hclock_amb_scopeds.
      { constructor; [exact Hclock_amb_scoped|constructor]. }
      assert (clocks_covered (clockof e0) [clock_amb]) as He0_covered.
      { rewrite H13. constructor; [exact Hclock_amb_covered|constructor]. }
      destruct
        (IH0 false [clock_amb] f0 eqs0 st st0 [th] sst sa
           ce0 xstd xst0s [th''] yst yst dlt
           H4 H5 Hnd0a Hmv0
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc0
              (CALLS.carried_single th))
           Hth_scopeds Hclock_amb_scopeds He0_covered
           (@Coq.Init.Logic.eq_refl nat 1) Hfound0
           Hun0 Ht0 Hgen0 Hth_target
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat0
              (CALLS.carried_single th)))
        as (dlt0 & Hres0).
      unfold carries_result_streams in Hres0.
      destruct Hres0 as (Hoff0 & Hce0 & Hrel0 & Hscope0 & Htgt0).

      (** the two branches *)
      assert
        (clocks_covered (clocksof es1) (amb :: ambs0)) as Hbranch_covered1.
      { exact
          (clocks_covered_same
             ck0 (ty :: tys) (clocksof es1) (amb :: ambs0)
             H14 H16 Hcovered). }
      assert
        (clocks_covered (clocksof es2) (amb :: ambs0)) as Hbranch_covered2.
      { exact
          (clocks_covered_same
             ck0 (ty :: tys) (clocksof es2) (amb :: ambs0)
             H15 H17 Hcovered). }
      pose proof
        (ljoin_list_length
           (List.map (fun t => ljoin th t) (tf :: tes1r)) tes2
           ts sd sst' Hj) as Hjoin_length.
      rewrite map_length in Hjoin_length.
      assert
        (List.length (amb :: ambs0) = List.length (tf :: tes1r))
        as Hbranch_len1.
      { rewrite Hlen, Hjoin_length. reflexivity. }
      assert (List.length (tf :: tes1r) = List.length tes2)
        as Hinputs_length.
      { rewrite <- map_length with (f := fun t => ljoin th t).
        exact
          (ljoin_list_input_lengths
             (List.map (fun t => ljoin th t) (tf :: tes1r)) tes2
             ts sd sst' Hj). }
      assert (List.length (amb :: ambs0) = List.length tes2)
        as Hbranch_len2.
      { rewrite Hbranch_len1. exact Hinputs_length. }

      assert (listSatisfiable dlt0 (carried (tf :: tes1r))) as Hsat1'.
      { exact
          (CALLS.listSatisfiable_off
             scope (carried (tf :: tes1r)) (CALLS.moved_by env st st0)
             dlt dlt0 Hcsc1 Hmv0 Hoff0 Hsat1). }
      destruct
        (carries_list_streams_intro P es1 Hall1 true (amb :: ambs0)
           f1 eqs1 st0 st1 (tf :: tes1r) sa sc
           ce1 xst0s xstm ts1x yst yst dlt0
           H6 H11 Hnd1 Hmv1 Hcsc1 Htsc1
           Hambsc Hbranch_covered1 Hbranch_len1
           Hfound1 Hun1 Htes1 Hgen1 Ht1y Hsat1')
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried tes2)) as Hsat2'.
      { apply
          (CALLS.listSatisfiable_off
             scope (carried tes2) (CALLS.moved_by env st0 st1)
             dlt0 dlt1).
        - exact Hcsc2.
        - exact Hmv1.
        - exact Hoff1.
        - exact
            (CALLS.listSatisfiable_off
               scope (carried tes2) (CALLS.moved_by env st st0)
               dlt dlt0 Hcsc2 Hmv0 Hoff0 Hsat2). }
      destruct
        (carries_list_streams_intro P es2 Hall2 true (amb :: ambs0)
           f2 eqs2 st1 st2 tes2 sc sd ce2 xstm xst' ts2x yst yst dlt1
           H7 H12 Hnd2 Hmv2 Hcsc2 Htsc2
           Hambsc Hbranch_covered2 Hbranch_len2
           Hfound2 Hun2 Htes2 Hgen2 Ht2y Hsat2')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      (** the three witnesses, composed up to the minting stage *)
      assert
        (CALLS.agree_off (CALLS.moved_by env st0 st2) dlt0 dlt2)
        as Hoff02.
      { intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st0 st1 st2 Hf2 x Hin). }
        apply Hoff2. intro Hin. apply Hx.
        exact
          (CALLS.moved_by_suffix_local env st0 st1 st2 Hf1 x Hin). }
      assert
        (forall x,
           In x (CALLS.moved_by env st0 st2) ->
           ~ In x (scope ++ CALLS.moved_by env st st0)) as Hsep0.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - apply (Hmv x).
          + apply (CALLS.moved_by_suffix_local env st st0 st' Hf0 x).
            exact
              (CALLS.moved_by_prefix_local env st0 st2 st' Hf3 x Hin).
          + exact Hscope.
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st0 st2 x Hfirst Hin). }
      assert
        (forall x,
           In x (CALLS.moved_by env st1 st2) ->
           ~ In x (scope ++ CALLS.moved_by env st0 st1)) as Hsep1.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - exact (Hmv2 x Hin Hscope).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st0 st1 st2 x Hfirst Hin). }

      assert (stream_rel dlt2 [clock_amb] [th] [th'']) as Hrel0'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st0)
             (CALLS.moved_by env st0 st2) dlt0 dlt2
             [clock_amb] [th] [th'']).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st0))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hclock_amb_scopeds.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st0) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Hth_scopeds.
        - exact Htgt0.
        - exact Hsep0.
        - exact Hoff02.
        - exact Hrel0. }
      assert
        (satisfiable dlt2 (fst th'') (merge clock_amb (fst th))) as Hhead.
      { inversion Hrel0' as
          [|a0 src tgt ambs' srcs' tgts' Hhead' Htail]; subst.
        exact Hhead'. }
      assert
        (Forall
           (fun a0 => satisfiable dlt2 (fst th'') (merge a0 (fst th)))
           (amb :: ambs0)) as Hheads.
      { exact
          (stream_head_rel_of_clock
             dlt2 ck0 ckty (amb :: ambs0) th th''
             Hckty Hhead Hall_covered). }
      assert
        (stream_rel dlt2 (amb :: ambs0) (tf :: tes1r) ts1x) as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st0 st1)
             (CALLS.moved_by env st1 st2) dlt1 dlt2
             (amb :: ambs0) (tf :: tes1r) ts1x).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st0 st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hambsc.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st0 st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc1.
        - exact Htgt1.
        - exact Hsep1.
        - exact Hoff2.
        - exact Hrel1. }

      (** the conditionals the pass built, and their pointwise relation *)
      assert (snd th'' = []) as Hthsnd.
      { destruct
          (CALLS.assign_lexp_normalized_lexp_pure
             GL env base_ty rst_ty (hd_default f0) Hnorm0'
             [th''] xst xst (Hth'' xst))
          as (_ & _ & Hcar0 & _).
        rewrite CALLS.carried_single in Hcar0. exact Hcar0. }
      assert
        (Forall2
           (fun e t =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
              /\ snd t = []) (List.concat f1) ts1x) as Hew1.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat f1) ts1x xst xst
             Hnorm1 Ht1x). }
      assert
        (Forall2
           (fun e t =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
              /\ snd t = []) (List.concat f2) ts2x) as Hew2.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat f2) ts2x xst xst
             Hnorm2 Ht2x). }
      destruct
        (CALLS.unnest_ite_types
           GL env base_ty rst_ty (hd_default f0) (ck0, None) th''
           (List.concat f1) (List.concat f2) (ty :: tys) ts1x ts2x xst
           Hth'' Hthsnd Hew1 Hew2 Hflen1 Hflen2)
        as (rs & Hjr & Hallr).
      assert (stream_rel dlt2 (amb :: ambs0) ts rs) as Hrelrs.
      { exact
          (ljoin_list_rel_head_streams
             dlt2 (amb :: ambs0) th th'' (tf :: tes1r) tes2 ts
             ts1x ts2x rs sd sst' xst xst Hj Hjr Hheads Hrel1' Hrel2). }

      (** one ambient per minted variable *)
      assert
        (List.map fst
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
         = List.map fst xs) as Hmapfst.
      { rewrite map_map. apply map_ext.
        intros (id & (ty0 & (cl0 & nm0))). reflexivity. }
      assert
        (Forall2 (fun xa ck' => snd (snd xa) = ck')
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
           (List.map (fun _ : type => ck0) (ty :: tys))) as Hclkalign.
      { pose proof
          (idents_for_anns_values
             (List.map (fun ty0 => (ty0, (ck0, None))) (ty :: tys))
             xs st2 st' Hids) as Hvals.
        clear - Hvals. revert Hvals.
        generalize (ty :: tys) as tys0. clear ty tys.
        revert xs.
        induction xs as [|xa xs IH]; intros tys0 Hvals.
        - destruct tys0; [constructor|discriminate Hvals].
        - destruct tys0 as [|ty0 tys0]; [discriminate Hvals|].
          simpl in Hvals. injection Hvals as Hhd Htl.
          destruct xa as (id & a). simpl in Hhd. subst a.
          simpl. constructor; [reflexivity|exact (IH tys0 Htl)]. }
      assert (declared_ambients (List.map fst xs) (amb :: ambs0)) as Hdecl.
      { rewrite <- Hmapfst.
        exact
          (declared_ambients_of_state
             (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
             st' (List.map (fun _ : type => ck0) (ty :: tys)) (amb :: ambs0)
             (idents_for_anns_incl
                (List.map (fun ty0 => (ty0, (ck0, None))) (ty :: tys))
                xs st2 st' Hids)
             Hclkalign Hfound Hcovered). }

      (** the minted variables are fresh, and their names with them *)
      assert
        (Permutation
           (vars_defined
              (combine (List.map (fun '(id, _) => [id]) xs)
                 (List.map (fun e => [e])
                    (unnest_ite (hd_default f0) (List.concat f1)
                       (List.concat f2) (ty :: tys) (ck0, None)))
               ++ eqs0 ++ List.concat eqs1 ++ List.concat eqs2) ++ st_ids st)
           (st_ids st')) as Hpall.
      { exact
          (unnest_exp_vars_perm
             P (Eite e0 es1 es2 (ty :: tys, (ck0, None))) false
             (List.map (fun '(id, ann0) => Evar id ann0) xs)
             (combine (List.map (fun '(id, _) => [id]) xs)
                (List.map (fun e => [e])
                   (unnest_ite (hd_default f0) (List.concat f1)
                      (List.concat f2) (ty :: tys) (ck0, None)))
              ++ eqs0 ++ List.concat eqs1 ++ List.concat eqs2)
             st st' Hwl Hunm). }
      assert (NoDup (st_ids st')) as Hndst'.
      { exact (Permutation_NoDup Hpall Hnd0). }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx.
      { exact
          (idents_for_anns_vars_perm
             (List.map (fun ty0 => (ty0, (ck0, None))) (ty :: tys))
             xs st2 st' Hids). }
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx.
      { rewrite Hpx. exact Hndst'. }
      assert (NoDup (List.map fst xs)) as Hndfst.
      { exact (NoDup_app_l (List.map fst xs) (st_ids st2) Hndx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st2 st')) as Hbnew.
      { intros b Hb.
        unfold CALLS.sec_of in Hb. apply in_flat_map in Hb as (x & Hx & Hb).
        unfold CALLS.moved_by, CALLS.EXPR.moved_by, CALLS.sec_of.
        apply in_flat_map. exists x. split; [|exact Hb].
        apply CALLS.new_ids_spec. split.
        - exact
            (idents_for_anns_incl_ids
               (List.map (fun ty0 => (ty0, (ck0, None))) (ty :: tys))
               xs st2 st' Hids x Hx).
        - exact
            (NoDup_app_In x (List.map fst xs) (st_ids st2) Hndx Hx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   ~ In b (scope ++ CALLS.moved_by env st st2)) as Hsepx.
      { intros b Hb Hin. apply in_app_or in Hin as [Hin|Hin].
        - apply (Hmv b); [|exact Hin].
          exact
            (CALLS.moved_by_suffix_local
               env st st2 st' Hf012 b (Hbnew b Hb)).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st2 st' b Hin (Hbnew b Hb)). }

      (** what the conditionals' types mention *)
      assert
        (st_scoped (scope ++ CALLS.moved_by env st st2) (fst th''))
        as Hthsc.
      { inversion Htgt0 as [|tqa tqs Htqa Htqr]; subst.
        apply st_scoped_weaken with
          (scope1 := scope ++ CALLS.moved_by env st st0).
        - apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr.
          exact (CALLS.moved_by_prefix_local env st st0 st2 Hf02).
        - exact Htqa. }
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           ts1x) as Htgt1'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st0 st1) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st0 st1).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr. apply incl_tran with
              (m := CALLS.moved_by env st0 st2).
            * exact (CALLS.moved_by_prefix_local env st0 st1 st2 Hf2).
            * exact (CALLS.moved_by_suffix_local env st st0 st2 Hf0).
          + exact Htq.
        - exact Htgt1. }
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           ts2x) as Htgt2'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st1 st2) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st1 st2).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_suffix_local env st st1 st2 Hf01).
          + exact Htq.
        - exact Htgt2. }
      assert
        (Forall
           (fun r => st_scoped (scope ++ CALLS.moved_by env st st2) (fst r))
           rs) as Hscrs.
      { exact
          (CALLS.ljoin_list_scoped_head
             (scope ++ CALLS.moved_by env st st2) th'' ts1x ts2x rs xst xst
             Hthsc Hjr Htgt1' Htgt2'). }

      (** the aligned premise the emitted definitions consume *)
      assert
        (Forall3
           (fun a e src =>
              forall tf0 s s',
                assign_lexp_type GL env base_ty rst_ty e s = OK ([tf0], s') ->
                satisfiable dlt2 (fst tf0) (merge a (fst src))
                /\ st_scoped (scope ++ CALLS.moved_by env st st2) (fst tf0))
           (amb :: ambs0)
           (unnest_ite (hd_default f0) (List.concat f1) (List.concat f2)
              (ty :: tys) (ck0, None))
           ts) as Hlift3.
      { unfold stream_rel in Hrelrs. clear - Hallr Hrelrs Hscrs.
        revert Hallr Hscrs.
        generalize
          (unnest_ite (hd_default f0) (List.concat f1) (List.concat f2)
             (ty :: tys) (ck0, None)) as rhss.
        induction Hrelrs as [|a src r ambs1 ts1 rs1 Hhead Hrest IH];
          intros rhss Hallr Hscrs.
        - inversion Hallr; subst. constructor.
        - destruct rhss as [|e rhss]; inversion Hallr as
            [|e0a r0 rhss0 rs2 Hq Hallr']; subst.
          inversion Hscrs as [|r1 rs3 Hsc0 Hscrs']; subst.
          constructor.
          + intros tf0 s s' Htf. destruct Hq as (_ & _ & Hq3).
            rewrite (Hq3 tf0 s s' Htf). split; [exact Hhead|exact Hsc0].
          + exact (IH rhss Hallr' Hscrs'). }
      assert
        (Forall
           (fun e =>
              (match e with Eapp _ _ _ _ => False | _ => True end)
              /\ forall ts0 s s',
                   assign_lexp_type GL env base_ty rst_ty e s = OK (ts0, s') ->
                   s' = s /\ List.length ts0 = 1 /\ carried ts0 = [])
           (unnest_ite (hd_default f0) (List.concat f1) (List.concat f2)
              (ty :: tys) (ck0, None))) as Hpure.
      { clear - Hallr.
        induction Hallr as [|e r rhss0 rs0 Hq Hrest IH]; [constructor|].
        destruct Hq as (Hq1 & Hq2 & _).
        constructor; [split; [exact Hq1|exact Hq2]|exact IH]. }
      assert
        (List.length (List.map fst xs)
         = List.length
             (unnest_ite (hd_default f0) (List.concat f1) (List.concat f2)
                (ty :: tys) (ck0, None))) as Hlend.
      { rewrite Hlbs. symmetry.
        exact
          (unnest_ite_length
             (hd_default f0) (List.concat f1) (List.concat f2)
             (ty :: tys) (ck0, None) Hflen1 Hflen2). }

      (** the emitted definitions *)
      destruct
        (lifted_defs_streams
           (scope ++ CALLS.moved_by env st st2) (List.map fst xs)
           (unnest_ite (hd_default f0) (List.concat f1) (List.concat f2)
              (ty :: tys) (ck0, None))
           ts (amb :: ambs0) ced xst xstd dlt2
           Hndfst Hlend Hsepx Hdecl
           (@Forall_impl ST (st_scoped scope)
              (st_scoped (scope ++ CALLS.moved_by env st st2))
              (fun a0 Ha0 =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) a0
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Ha0)
              (amb :: ambs0) Hambsc)
           Hpure
           (@Forall_impl LST
              (fun src => st_scoped scope (fst src))
              (fun src =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst src))
              (fun src Hsrc =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) (fst src)
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Hsrc)
              ts Htsc)
           Hlift3 Hgend)
        as (dlt3 & Hoff3 & Hced & Hscoped & Hrel3).

      (** the minted names are among the ones the whole run moved *)
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st st')) as Hincx.
      { intros b Hb.
        exact
          (CALLS.moved_by_suffix_local
             env st st2 st' Hf012 b (Hbnew b Hb)). }
      assert
        (forall y, In y (sec_of (List.map fst xs)) ->
                   ~ In y (scope ++ CALLS.moved_by env st st0)) as Hsepx0.
      { intros y Hy Hin. apply (Hsepx y Hy).
        apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
        right.
        exact (CALLS.moved_by_prefix_local env st st0 st2 Hf02 y Hin). }
      assert
        (forall y, In y (sec_of (List.map fst xs)) ->
                   ~ In y (scope ++ CALLS.moved_by env st0 st1)) as Hsepx1.
      { intros y Hy Hin. apply (Hsepx y Hy).
        apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
        right. apply (CALLS.moved_by_suffix_local env st st0 st2 Hf0 y).
        exact (CALLS.moved_by_prefix_local env st0 st1 st2 Hf2 y Hin). }
      assert
        (forall y, In y (sec_of (List.map fst xs)) ->
                   ~ In y (scope ++ CALLS.moved_by env st1 st2)) as Hsepx2.
      { intros y Hy Hin. apply (Hsepx y Hy).
        apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [now left|].
        right.
        exact (CALLS.moved_by_suffix_local env st st1 st2 Hf01 y Hin). }

      (** the results' relation, at the names the pass bound them to *)
      assert (stream_rel dlt3 (amb :: ambs0) ts ts'') as Hrelfin.
      { unfold stream_rel. clear - Hrel3 Hevars.
        revert Hrel3. generalize (amb :: ambs0) as ambsf. revert ts.
        induction Hevars as [|xa t0 xs0 ts0 Hxa Hrest IH];
          intros ts ambsf Hrel3.
        - inversion Hrel3; subst. constructor.
        - simpl in Hrel3.
          inversion Hrel3 as
            [|a0 x0 src0 ambs1 xs1 ts1 Hhead Hrest3]; subst.
          destruct Hxa as (b & Hb & Ht). subst t0.
          constructor.
          + rewrite fst_lvar. exact (Hhead b Hb).
          + exact (IH ts1 ambs1 Hrest3). }

      exists dlt3. unfold carries_result_streams. split.
      - (** the witness moved only where the run did *)
        intros x Hx.
        rewrite Hoff0.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st0 st' Hf03 x Hin). }
        rewrite Hoff02.
        2: { intro Hin. apply Hx.
             apply (CALLS.moved_by_suffix_local env st st0 st' Hf0 x).
             exact
               (CALLS.moved_by_prefix_local env st0 st2 st' Hf3 x Hin). }
        apply Hoff3. intro Hin. apply Hx. exact (Hincx x Hin).
      - split.
        + (** every emitted constraint still holds *)
          apply listSatisfiable_app. split; [exact Hced|].
          apply listSatisfiable_app. split.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce0 (scope ++ CALLS.moved_by env st st0)
                 (sec_of (List.map fst xs)) dlt2 dlt3
                 Hscope0 Hsepx0 Hoff3).
            exact
              (CALLS.listSatisfiable_off_scope
                 ce0 (scope ++ CALLS.moved_by env st st0)
                 (CALLS.moved_by env st0 st2) dlt0 dlt2
                 Hscope0 Hsep0 Hoff02 Hce0).
          * apply listSatisfiable_app. split.
            -- apply
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st0 st1)
                    (sec_of (List.map fst xs)) dlt2 dlt3
                    Hscope1 Hsepx1 Hoff3).
               exact
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st0 st1)
                    (CALLS.moved_by env st1 st2) dlt1 dlt2
                    Hscope1 Hsep1 Hoff2 Hce1).
            -- exact
                 (CALLS.listSatisfiable_off_scope
                    ce2 (scope ++ CALLS.moved_by env st1 st2)
                    (sec_of (List.map fst xs)) dlt2 dlt3
                    Hscope2 Hsepx2 Hoff3 Hce2).
        + split; [exact Hrelfin|]. split.
          * (** and mentions only names in scope or moved *)
            apply Forall_app. split.
            -- apply
                 (@Forall_impl constraint
                    (constraint_scoped
                       ((scope ++ CALLS.moved_by env st st2)
                          ++ sec_of (List.map fst xs)))
                    (constraint_scoped
                       (scope ++ CALLS.moved_by env st st'))).
               ++ intros c Hc.
                  apply constraint_scoped_incl with
                    (scope1 := (scope ++ CALLS.moved_by env st st2)
                                 ++ sec_of (List.map fst xs)).
                  2: exact Hc.
                  apply incl_app; [apply incl_app|].
                  ** apply incl_appl, incl_refl.
                  ** apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st2 st' Hf3).
                  ** apply incl_appr. exact Hincx.
               ++ exact Hscoped.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st0))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st0).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st0 st' Hf03).
                  ** exact Hscope0.
               ++ apply Forall_app. split.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st0 st1))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc.
                         apply constraint_scoped_incl with
                           (scope1 := scope ++ CALLS.moved_by env st0 st1).
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         apply incl_tran with
                           (m := CALLS.moved_by env st0 st').
                         +++ exact
                               (CALLS.moved_by_prefix_local
                                  env st0 st1 st' Hf13).
                         +++ exact
                               (CALLS.moved_by_suffix_local
                                  env st st0 st' Hf0).
                     --- exact Hscope1.
                  ** apply
                       (@Forall_impl constraint
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st1 st2))
                          (constraint_scoped
                             (scope ++ CALLS.moved_by env st st'))).
                     --- intros c Hc.
                         apply constraint_scoped_incl with
                           (scope1 := scope ++ CALLS.moved_by env st1 st2).
                         2: exact Hc.
                         apply incl_app; [apply incl_appl, incl_refl|].
                         apply incl_appr.
                         apply incl_tran with
                           (m := CALLS.moved_by env st1 st').
                         +++ exact
                               (CALLS.moved_by_prefix_local
                                  env st1 st2 st' Hf3).
                         +++ exact
                               (CALLS.moved_by_suffix_local
                                  env st st1 st' Hf01).
                     --- exact Hscope2.
          * (** the bound results are names the run minted *)
            apply
              (CALLS.Forall2_right_In
                 (fun xa t0 =>
                    exists b, Env.find (fst xa) env = Some b /\ t0 = lvar b)
                 (fun tgt =>
                    st_scoped (scope ++ CALLS.moved_by env st st') (fst tgt))
                 xs ts'' Hevars).
            intros xa t0 Hxa Hp. destruct Hp as (b & Hb & Ht). subst t0.
            rewrite fst_lvar. intros y Hy.
            destruct Hy as [Hy|[]]. subst y.
            apply in_or_app. right. apply Hincx.
            unfold CALLS.sec_of. apply in_flat_map. exists (fst xa).
            split; [now apply in_map|]. rewrite Hb. now left.
    Qed.


    (** * The delayed definition

        [Efby] always lifts: the pass binds every result to a variable of its
        own and emits a definition for each.  Both operand lists sit on the
        result clocks, so -- unlike the control operators -- they run at the
        very ambients the contract supplies, and the join needs no head. *)

    Lemma carries_Efby_streams :
      forall P ic e0s es anns,
        Forall (carries_streams P) e0s ->
        Forall (carries_streams P) es ->
        carries_at_streams P ic (Efby e0s es anns).
    Proof.
      intros P ic e0s es anns Hall0 Hall1
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      pose proof Hun as Hunm. pose proof Hnd as Hnd0.
      apply CALLS.unnest_exp_Efby_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & st2 & xs
            & Hun0 & Hun1 & Hids & Hes' & Heqs).
      subst es' eqs.
      apply CALLS.unnest_exps_inv in Hun0
        as (ess0 & eqss0 & Hmap0 & Hf0e & Heq0); subst.
      apply CALLS.unnest_exps_inv in Hun1
        as (ess1 & eqss1 & Hmap1 & Hf1e & Heq1); subst.

      (** the three stages of the run *)
      assert (st_follows st st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P false e0s ess0 eqss0 st st1 Hmap0). }
      assert (st_follows st1 st2) as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P false es ess1 eqss1 st1 st2 Hmap1). }
      assert (st_follows st2 st') as Hf3.
      { exact (idents_for_anns_st_follows anns xs st2 st' Hids). }
      assert (st_follows st st2) as Hf12 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf23 by (etransitivity; eauto).
      assert (st_follows st st') as Hf13 by (etransitivity; eauto).
      assert (state_clocks_found st2) as Hfound2.
      { exact (state_clocks_found_prefix st2 st' Hf3 Hfound). }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st2 Hf2 Hfound2). }

      (** the operands sit on the result clocks *)
      assert (clocksof e0s = List.map clock_of_nclock anns) as Hck0.
      { symmetry. apply Forall2_eq. exact H8. }
      assert (clocksof es = List.map clock_of_nclock anns) as Hck1.
      { symmetry. apply Forall2_eq. exact H9. }
      assert (clocks_covered (clocksof e0s) ambs) as Hcov0.
      { rewrite Hck0. exact Hcovered. }
      assert (clocks_covered (clocksof es) ambs) as Hcov1.
      { rewrite Hck1. exact Hcovered. }

      (** the source type: the two operand lists, joined componentwise *)
      rewrite assign_lexp_Efby in Has.
      apply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      apply sec_bind_inv in Has as (us & sb & Hus & Hj).

      (** the target: one variable per result *)
      destruct
        (CALLS.assign_lexps_evars GL env base_ty rst_ty xs ts'' yst yst' Has')
        as (Hyst & Hevars). subst yst'.

      (** the emitted equations *)
      rewrite CALLS.emitted_defs_map_form in Hgen, Hnd.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.map (fun '(x, e) => ([x], [e]))
              (combine (List.map fst xs)
                 (unnest_fby (List.concat ess0) (List.concat ess1) anns)))
           (List.concat eqss0 ++ List.concat eqss1) ce xst xst' Hgen)
        as (ced & cer & xstd & Hgend & Hgenr & Hce). subst ce.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqss0) (List.concat eqss1) cer xstd xst' Hgenr)
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & Hcer). subst cer.

      (** shapes and lengths *)
      assert (Forall normalized_lexp (List.concat ess0)) as Hn0.
      { exact
          (CALLS.map_bind2_unnest_normalized_lexp
             P e0s ess0 eqss0 st st1 Hmap0). }
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1.
      { exact
          (CALLS.map_bind2_unnest_normalized_lexp
             P es ess1 eqss1 st1 st2 Hmap1). }
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0.
      { apply
          (@Forall_impl exp normalized_lexp normalized_cexp);
          [intros e He; now constructor|exact Hn0]. }
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1.
      { apply
          (@Forall_impl exp normalized_lexp normalized_cexp);
          [intros e He; now constructor|exact Hn1]. }
      assert (List.length (List.concat ess0) = List.length anns) as Hle0.
      { pose proof
          (map_bind2_unnest_exp_length
             P false e0s ess0 eqss0 st st1 H2 Hmap0) as Hlength.
        rewrite H5 in Hlength. exact Hlength. }
      assert (List.length (List.concat ess1) = List.length anns) as Hle1.
      { pose proof
          (map_bind2_unnest_exp_length
             P false es ess1 eqss1 st1 st2 H4 Hmap1) as Hlength.
        rewrite H6 in Hlength. exact Hlength. }
      assert (List.length xs = List.length anns) as Hlxs.
      { exact (idents_for_anns_length anns xs st2 st' Hids). }
      assert (List.length (List.map fst xs) = List.length anns) as Hlbs.
      { rewrite map_length. exact Hlxs. }

      (** the operands' target typings, read back off the emitted delays *)
      destruct
        (CALLS.defs_operand_types_fby
           GL env base_ty rst_ty cenv (List.map fst xs)
           (List.concat ess0) (List.concat ess1) anns ced xst xstd
           Hn0 Hn1 Hlbs Hle0 Hle1 Hgend)
        as (ts0x & usx & Ht0x & Hux).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
              = OK (ts0x, yst)) as Ht0y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat ess0) Hc0 ts0x xst xst Ht0x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
              = OK (usx, yst)) as Huy.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat ess1) Hc1 usx xst xst Hux)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }

      (** what the source carries, split between the two operand lists *)
      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct.
      { exact (ljoin_list_carried ts0 us ts sb sst' Hj). }
      rewrite Hct in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (Hcsc0 & Hcsc1).
      apply listSatisfiable_cmerge in Hsat as (Hsat0 & Hsat1).
      pose proof Htsc as Htscall.
      destruct
        (CALLS.ljoin_list_scoped_plain_inv scope ts0 us ts sb sst' Hj Htsc)
        as (Htsc0 & Htsc1).

      (** the emitted operand equations are well separated *)
      assert
        (NoDup
           (vars_defined (List.concat eqss0 ++ List.concat eqss1)
              ++ st_ids st)) as Hndr.
      { exact
          (CALLS.NoDup_vd_drop
             (List.map (fun '(x, e) => ([x], [e]))
                (combine (List.map fst xs)
                   (unnest_fby (List.concat ess0) (List.concat ess1) anns)))
             (List.concat eqss0 ++ List.concat eqss1) (st_ids st) Hnd). }
      assert
        (Permutation
           (vars_defined (List.concat eqss0) ++ st_ids st) (st_ids st1))
        as Hperm0.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P false e0s ess0 eqss0 st st1 H2 Hmap0). }
      assert
        (NoDup (vars_defined (List.concat eqss0) ++ st_ids st)) as Hnd1.
      { exact
          (CALLS.NoDup_vd_app_l
             (List.concat eqss0) (List.concat eqss1) (st_ids st) Hndr). }
      assert
        (NoDup (vars_defined (List.concat eqss1) ++ st_ids st1)) as Hnd2.
      { exact
          (CALLS.NoDup_vd_app_r
             (List.concat eqss0) (List.concat eqss1)
             (st_ids st) (st_ids st1) Hperm0 Hndr). }
      assert
        (forall x, In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hx). }
      assert
        (forall x, In x (CALLS.moved_by env st1 st2) -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st1 st' Hf1 x).
        exact (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hx). }

      (** the ambients line up with each operand list *)
      pose proof (ljoin_list_length ts0 us ts sb sst' Hj) as Hjoinlen.
      assert (List.length ambs = List.length ts0) as Hlen0.
      { rewrite Hlen. exact Hjoinlen. }
      assert (List.length ts0 = List.length us) as Hinlen.
      { exact (ljoin_list_input_lengths ts0 us ts sb sst' Hj). }
      assert (List.length ambs = List.length us) as Hlen1.
      { rewrite Hlen0. exact Hinlen. }

      (** the two operand witnesses *)
      destruct
        (carries_list_streams_intro P e0s Hall0 false ambs
           ess0 eqss0 st st1 ts0 sst sa ce1 xstd xstm ts0x yst yst dlt
           H2 H3 Hnd1 Hmv1 Hcsc0 Htsc0 Hambsc Hcov0 Hlen0
           Hfound1 Hmap0 Hts0 Hgen1 Ht0y Hsat0)
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried us)) as Hsat1'.
      { exact
          (CALLS.listSatisfiable_off
             scope (carried us) (CALLS.moved_by env st st1)
             dlt dlt1 Hcsc1 Hmv1 Hoff1 Hsat1). }
      destruct
        (carries_list_streams_intro P es Hall1 false ambs
           ess1 eqss1 st1 st2 us sa sb ce2 xstm xst' usx yst yst dlt1
           H4 H7 Hnd2 Hmv2 Hcsc1 Htsc1 Hambsc Hcov1 Hlen1
           Hfound2 Hmap1 Hus Hgen2 Huy Hsat1')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      assert
        (forall x,
           In x (CALLS.moved_by env st1 st2) ->
           ~ In x (scope ++ CALLS.moved_by env st st1)) as Hsep1.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - exact (Hmv2 x Hin Hscope).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st1 st2 x Hfirst Hin). }
      assert (stream_rel dlt2 ambs ts0 ts0x) as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st1)
             (CALLS.moved_by env st1 st2) dlt1 dlt2 ambs ts0 ts0x).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hambsc.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc0.
        - exact Htgt1.
        - exact Hsep1.
        - exact Hoff2.
        - exact Hrel1. }

      (** the delays the pass built, and their pointwise relation *)
      assert
        (Forall2
           (fun e t0 =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t0], s))
              /\ snd t0 = []) (List.concat ess0) ts0x) as Hew0.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat ess0) ts0x xst xst
             Hc0 Ht0x). }
      assert
        (Forall2
           (fun e t0 =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t0], s))
              /\ snd t0 = []) (List.concat ess1) usx) as Hew1.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat ess1) usx xst xst
             Hc1 Hux). }
      destruct
        (CALLS.unnest_fby_types
           GL env base_ty rst_ty (List.concat ess0) (List.concat ess1)
           anns ts0x usx xst Hew0 Hew1 Hle0 Hle1)
        as (rs & Hjr & Hallr).
      assert (stream_rel dlt2 ambs ts rs) as Hrelrs.
      { exact
          (ljoin_list_rel_plain_streams
             dlt2 ambs ts0 us ts ts0x usx rs sb sst' xst xst
             Hj Hjr Hrel1' Hrel2). }

      (** one ambient per minted variable *)
      assert
        (List.map fst
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
         = List.map fst xs) as Hmapfst.
      { rewrite map_map. apply map_ext.
        intros (id & (ty0 & (cl0 & nm0))). reflexivity. }
      assert
        (Forall2 (fun xa ck' => snd (snd xa) = ck')
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
           (List.map clock_of_nclock anns)) as Hclkalign.
      { pose proof (idents_for_anns_values anns xs st2 st' Hids) as Hvals.
        clear - Hvals. revert anns Hvals.
        induction xs as [|xa xs IH]; intros anns0 Hvals.
        - destruct anns0; [constructor|discriminate Hvals].
        - destruct anns0 as [|a0 anns0]; [discriminate Hvals|].
          simpl in Hvals. injection Hvals as Hhd Htl.
          destruct xa as (id & a). simpl in Hhd. subst a.
          destruct a0 as (ty0 & (cl0 & nm0)).
          simpl. constructor; [reflexivity|exact (IH anns0 Htl)]. }
      assert (declared_ambients (List.map fst xs) ambs) as Hdecl.
      { rewrite <- Hmapfst.
        exact
          (declared_ambients_of_state
             (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
             st' (List.map clock_of_nclock anns) ambs
             (idents_for_anns_incl anns xs st2 st' Hids)
             Hclkalign Hfound Hcovered). }

      (** the minted variables are fresh, and their names with them *)
      assert
        (Permutation
           (vars_defined
              (List.map (fun '(x, _, fby) => ([x], [fby]))
                 (combine xs
                    (unnest_fby (List.concat ess0) (List.concat ess1) anns))
               ++ List.concat eqss0 ++ List.concat eqss1) ++ st_ids st)
           (st_ids st')) as Hpall.
      { exact
          (unnest_exp_vars_perm
             P (Efby e0s es anns) ic
             (List.map (fun '(x, ann0) => Evar x ann0) xs)
             (List.map (fun '(x, _, fby) => ([x], [fby]))
                (combine xs
                   (unnest_fby (List.concat ess0) (List.concat ess1) anns))
              ++ List.concat eqss0 ++ List.concat eqss1)
             st st' Hwl Hunm). }
      assert (NoDup (st_ids st')) as Hndst'.
      { exact (Permutation_NoDup Hpall Hnd0). }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx.
      { exact (idents_for_anns_vars_perm anns xs st2 st' Hids). }
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx.
      { rewrite Hpx. exact Hndst'. }
      assert (NoDup (List.map fst xs)) as Hndfst.
      { exact (NoDup_app_l (List.map fst xs) (st_ids st2) Hndx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st2 st')) as Hbnew.
      { intros b Hb.
        unfold CALLS.sec_of in Hb. apply in_flat_map in Hb as (x & Hx & Hb).
        unfold CALLS.moved_by, CALLS.EXPR.moved_by, CALLS.sec_of.
        apply in_flat_map. exists x. split; [|exact Hb].
        apply CALLS.new_ids_spec. split.
        - exact (idents_for_anns_incl_ids anns xs st2 st' Hids x Hx).
        - exact
            (NoDup_app_In x (List.map fst xs) (st_ids st2) Hndx Hx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   ~ In b (scope ++ CALLS.moved_by env st st2)) as Hsepx.
      { intros b Hb Hin. apply in_app_or in Hin as [Hin|Hin].
        - apply (Hmv b); [|exact Hin].
          exact
            (CALLS.moved_by_suffix_local
               env st st2 st' Hf12 b (Hbnew b Hb)).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st2 st' b Hin (Hbnew b Hb)). }

      (** what the delays' types mention *)
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           ts0x) as Htgt1'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st1) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st st1).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_prefix_local env st st1 st2 Hf2).
          + exact Htq.
        - exact Htgt1. }
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           usx) as Htgt2'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st1 st2) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st1 st2).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_suffix_local env st st1 st2 Hf1).
          + exact Htq.
        - exact Htgt2. }
      assert
        (Forall
           (fun r => st_scoped (scope ++ CALLS.moved_by env st st2) (fst r))
           rs) as Hscrs.
      { exact
          (CALLS.ljoin_list_scoped_plain
             (scope ++ CALLS.moved_by env st st2) ts0x usx rs xst xst
             Hjr Htgt1' Htgt2'). }

      (** the aligned premise the emitted definitions consume *)
      assert
        (Forall3
           (fun a e src =>
              forall tf0 s s',
                assign_lexp_type GL env base_ty rst_ty e s = OK ([tf0], s') ->
                satisfiable dlt2 (fst tf0) (merge a (fst src))
                /\ st_scoped (scope ++ CALLS.moved_by env st st2) (fst tf0))
           ambs
           (unnest_fby (List.concat ess0) (List.concat ess1) anns)
           ts) as Hlift3.
      { unfold stream_rel in Hrelrs. clear - Hallr Hrelrs Hscrs.
        revert Hallr Hscrs.
        generalize
          (unnest_fby (List.concat ess0) (List.concat ess1) anns) as rhss.
        induction Hrelrs as [|a src r ambs1 ts1 rs1 Hhead Hrest IH];
          intros rhss Hallr Hscrs.
        - inversion Hallr; subst. constructor.
        - destruct rhss as [|e rhss]; inversion Hallr as
            [|e0a r0 rhss0 rs2 Hq Hallr']; subst.
          inversion Hscrs as [|r1 rs3 Hsc0 Hscrs']; subst.
          constructor.
          + intros tf0 s s' Htf. destruct Hq as (_ & _ & Hq3).
            rewrite (Hq3 tf0 s s' Htf). split; [exact Hhead|exact Hsc0].
          + exact (IH rhss Hallr' Hscrs'). }
      assert
        (Forall
           (fun e =>
              (match e with Eapp _ _ _ _ => False | _ => True end)
              /\ forall ts0' s s',
                   assign_lexp_type GL env base_ty rst_ty e s = OK (ts0', s') ->
                   s' = s /\ List.length ts0' = 1 /\ carried ts0' = [])
           (unnest_fby (List.concat ess0) (List.concat ess1) anns)) as Hpure.
      { clear - Hallr.
        induction Hallr as [|e r rhss0 rs0 Hq Hrest IH]; [constructor|].
        destruct Hq as (Hq1 & Hq2 & _).
        constructor; [split; [exact Hq1|exact Hq2]|exact IH]. }
      assert
        (List.length (List.map fst xs)
         = List.length
             (unnest_fby (List.concat ess0) (List.concat ess1) anns))
        as Hlend.
      { rewrite Hlbs. symmetry.
        exact
          (unnest_fby_length
             (List.concat ess0) (List.concat ess1) anns Hle0 Hle1). }

      (** the emitted definitions *)
      destruct
        (lifted_defs_streams
           (scope ++ CALLS.moved_by env st st2) (List.map fst xs)
           (unnest_fby (List.concat ess0) (List.concat ess1) anns)
           ts ambs ced xst xstd dlt2
           Hndfst Hlend Hsepx Hdecl
           (@Forall_impl ST (st_scoped scope)
              (st_scoped (scope ++ CALLS.moved_by env st st2))
              (fun a0 Ha0 =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) a0
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Ha0)
              ambs Hambsc)
           Hpure
           (@Forall_impl LST
              (fun src => st_scoped scope (fst src))
              (fun src =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst src))
              (fun src Hsrc =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) (fst src)
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Hsrc)
              ts Htscall)
           Hlift3 Hgend)
        as (dlt3 & Hoff3 & Hced & Hscoped & Hrel3).

      (** the minted names are among the ones the whole run moved *)
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st st')) as Hincx.
      { intros b Hb.
        exact
          (CALLS.moved_by_suffix_local
             env st st2 st' Hf12 b (Hbnew b Hb)). }

      (** the results' relation, at the names the pass bound them to *)
      assert (stream_rel dlt3 ambs ts ts'') as Hrelfin.
      { unfold stream_rel. clear - Hrel3 Hevars.
        revert ambs ts Hrel3.
        induction Hevars as [|xa t xs0 ts0 Hxa Hrest IH];
          intros ambs ts Hrel3.
        - inversion Hrel3; subst. constructor.
        - simpl in Hrel3.
          inversion Hrel3 as
            [|a0 x0 src0 ambs1 xs1 ts1 Hhead Hrest3]; subst.
          destruct Hxa as (b & Hb & Ht). subst t.
          constructor.
          + rewrite fst_lvar. exact (Hhead b Hb).
          + exact (IH ambs1 ts1 Hrest3). }

      exists dlt3. unfold carries_result_streams. split.
      - (** the witness moved only where the run did *)
        intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hin). }
        rewrite Hoff2.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_suffix_local
                  env st st1 st' Hf1 x
                  (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hin)). }
        apply Hoff3. intro Hin. apply Hx. exact (Hincx x Hin).
      - split.
        + (** every emitted constraint still holds *)
          apply listSatisfiable_app. split; [exact Hced|].
          apply listSatisfiable_app. split.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce1 (scope ++ CALLS.moved_by env st st1)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope1.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_prefix_local env st st1 st2 Hf2 y Hin).
            -- exact Hoff3.
            -- apply
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st st1)
                    (CALLS.moved_by env st1 st2) dlt1 dlt2).
               ++ exact Hscope1.
               ++ intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
                  ** exact (Hmv2 y Hy Hin).
                  ** exact
                       (CALLS.moved_by_disjoint_local
                          env env_inj st st1 st2 y Hin Hy).
               ++ exact Hoff2.
               ++ exact Hce1.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce2 (scope ++ CALLS.moved_by env st1 st2)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope2.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_suffix_local env st st1 st2 Hf1 y Hin).
            -- exact Hoff3.
            -- exact Hce2.
        + split; [exact Hrelfin|]. split.
          * (** and mentions only names in scope or moved *)
            apply Forall_app. split.
            -- apply
                 (@Forall_impl constraint
                    (constraint_scoped
                       ((scope ++ CALLS.moved_by env st st2)
                          ++ sec_of (List.map fst xs)))
                    (constraint_scoped
                       (scope ++ CALLS.moved_by env st st'))).
               ++ intros c Hc.
                  apply constraint_scoped_incl with
                    (scope1 := (scope ++ CALLS.moved_by env st st2)
                                 ++ sec_of (List.map fst xs)).
                  2: exact Hc.
                  apply incl_app; [apply incl_app|].
                  ** apply incl_appl, incl_refl.
                  ** apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st2 st' Hf3).
                  ** apply incl_appr. exact Hincx.
               ++ exact Hscoped.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st1))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st1).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st1 st' Hf23).
                  ** exact Hscope1.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st1 st2))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st1 st2).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     apply incl_tran with
                       (m := CALLS.moved_by env st1 st').
                     --- exact
                           (CALLS.moved_by_prefix_local
                              env st1 st2 st' Hf3).
                     --- exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                  ** exact Hscope2.
          * (** the bound results are names the run minted *)
            apply
              (CALLS.Forall2_right_In
                 (fun xa t =>
                    exists b, Env.find (fst xa) env = Some b /\ t = lvar b)
                 (fun tgt =>
                    st_scoped (scope ++ CALLS.moved_by env st st') (fst tgt))
                 xs ts'' Hevars).
            intros xa t Hxa Hp. destruct Hp as (b & Hb & Ht). subst t.
            rewrite fst_lvar. intros y Hy.
            destruct Hy as [Hy|[]]. subst y.
            apply in_or_app. right. apply Hincx.
            unfold CALLS.sec_of. apply in_flat_map. exists (fst xa).
            split; [now apply in_map|]. rewrite Hb. now left.
    Qed.
    (** * The initialised delay

        [Earrow] is typed exactly as [Efby] -- the initialisation pass, not
        this one, is where the two part company -- so this is the delay's
        proof with the pass's own operator in place of [unnest_fby].  The
        emitted definitions come back in [combine] rather than [map] form,
        which is the only real difference. *)

    Lemma carries_Earrow_streams :
      forall P ic e0s es anns,
        Forall (carries_streams P) e0s ->
        Forall (carries_streams P) es ->
        carries_at_streams P ic (Earrow e0s es anns).
    Proof.
      intros P ic e0s es anns Hall0 Hall1
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat.
      inversion Hwl; subst.
      inversion Hwc; subst.
      pose proof Hun as Hunm. pose proof Hnd as Hnd0.
      apply CALLS.unnest_exp_Earrow_inv in Hun
        as (f0 & eqsa & st1 & f1 & eqsb & st2 & xs
            & Hun0 & Hun1 & Hids & Hes' & Heqs).
      subst es' eqs.
      apply CALLS.unnest_exps_inv in Hun0
        as (ess0 & eqss0 & Hmap0 & Hf0e & Heq0); subst.
      apply CALLS.unnest_exps_inv in Hun1
        as (ess1 & eqss1 & Hmap1 & Hf1e & Heq1); subst.

      (** the three stages of the run *)
      assert (st_follows st st1) as Hf1.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P false e0s ess0 eqss0 st st1 Hmap0). }
      assert (st_follows st1 st2) as Hf2.
      { exact
          (CALLS.map_bind2_unnest_st_follows
             P false es ess1 eqss1 st1 st2 Hmap1). }
      assert (st_follows st2 st') as Hf3.
      { exact (idents_for_anns_st_follows anns xs st2 st' Hids). }
      assert (st_follows st st2) as Hf12 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf23 by (etransitivity; eauto).
      assert (st_follows st st') as Hf13 by (etransitivity; eauto).
      assert (state_clocks_found st2) as Hfound2.
      { exact (state_clocks_found_prefix st2 st' Hf3 Hfound). }
      assert (state_clocks_found st1) as Hfound1.
      { exact (state_clocks_found_prefix st1 st2 Hf2 Hfound2). }

      (** the operands sit on the result clocks *)
      assert (clocksof e0s = List.map clock_of_nclock anns) as Hck0.
      { symmetry. apply Forall2_eq. exact H8. }
      assert (clocksof es = List.map clock_of_nclock anns) as Hck1.
      { symmetry. apply Forall2_eq. exact H9. }
      assert (clocks_covered (clocksof e0s) ambs) as Hcov0.
      { rewrite Hck0. exact Hcovered. }
      assert (clocks_covered (clocksof es) ambs) as Hcov1.
      { rewrite Hck1. exact Hcovered. }

      (** the source type: the two operand lists, joined componentwise *)
      rewrite assign_lexp_Earrow in Has.
      apply sec_bind_inv in Has as (ts0 & sa & Hts0 & Has).
      apply sec_bind_inv in Has as (us & sb & Hus & Hj).

      (** the target: one variable per result *)
      destruct
        (CALLS.assign_lexps_evars GL env base_ty rst_ty xs ts'' yst yst' Has')
        as (Hyst & Hevars). subst yst'.

      (** the emitted equations *)
      rewrite CALLS.emitted_defs_combine_form in Hgen, Hnd.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.map (fun '(x, e) => ([x], [e]))
              (combine (List.map fst xs)
                 (unnest_arrow (List.concat ess0) (List.concat ess1) anns)))
           (List.concat eqss0 ++ List.concat eqss1) ce xst xst' Hgen)
        as (ced & cer & xstd & Hgend & Hgenr & Hce). subst ce.
      destruct
        (CALLS.generate_leqns_constraints_app
           GL env base_ty rst_ty cenv
           (List.concat eqss0) (List.concat eqss1) cer xstd xst' Hgenr)
        as (ce1 & ce2 & xstm & Hgen1 & Hgen2 & Hcer). subst cer.

      (** shapes and lengths *)
      assert (Forall normalized_lexp (List.concat ess0)) as Hn0.
      { exact
          (CALLS.map_bind2_unnest_normalized_lexp
             P e0s ess0 eqss0 st st1 Hmap0). }
      assert (Forall normalized_lexp (List.concat ess1)) as Hn1.
      { exact
          (CALLS.map_bind2_unnest_normalized_lexp
             P es ess1 eqss1 st1 st2 Hmap1). }
      assert (Forall normalized_cexp (List.concat ess0)) as Hc0.
      { apply
          (@Forall_impl exp normalized_lexp normalized_cexp);
          [intros e He; now constructor|exact Hn0]. }
      assert (Forall normalized_cexp (List.concat ess1)) as Hc1.
      { apply
          (@Forall_impl exp normalized_lexp normalized_cexp);
          [intros e He; now constructor|exact Hn1]. }
      assert (List.length (List.concat ess0) = List.length anns) as Hle0.
      { pose proof
          (map_bind2_unnest_exp_length
             P false e0s ess0 eqss0 st st1 H2 Hmap0) as Hlength.
        rewrite H5 in Hlength. exact Hlength. }
      assert (List.length (List.concat ess1) = List.length anns) as Hle1.
      { pose proof
          (map_bind2_unnest_exp_length
             P false es ess1 eqss1 st1 st2 H4 Hmap1) as Hlength.
        rewrite H6 in Hlength. exact Hlength. }
      assert (List.length xs = List.length anns) as Hlxs.
      { exact (idents_for_anns_length anns xs st2 st' Hids). }
      assert (List.length (List.map fst xs) = List.length anns) as Hlbs.
      { rewrite map_length. exact Hlxs. }

      (** the operands' target typings, read back off the emitted delays *)
      destruct
        (CALLS.defs_operand_types_arrow
           GL env base_ty rst_ty cenv (List.map fst xs)
           (List.concat ess0) (List.concat ess1) anns ced xst xstd
           Hn0 Hn1 Hlbs Hle0 Hle1 Hgend)
        as (ts0x & usx & Ht0x & Hux).
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess0) yst
              = OK (ts0x, yst)) as Ht0y.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat ess0) Hc0 ts0x xst xst Ht0x)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }
      assert (assign_lexps GL env base_ty rst_ty (List.concat ess1) yst
              = OK (usx, yst)) as Huy.
      { destruct
          (CALLS.assign_lexps_normalized_pure
             GL env base_ty rst_ty (List.concat ess1) Hc1 usx xst xst Hux)
          as (_ & _ & _ & Hpure). exact (Hpure yst). }

      (** what the source carries, split between the two operand lists *)
      assert (carried ts = cmerge (carried ts0) (carried us)) as Hct.
      { exact (ljoin_list_carried ts0 us ts sb sst' Hj). }
      rewrite Hct in Hcsc, Hsat.
      apply constraints_scoped_cmerge in Hcsc as (Hcsc0 & Hcsc1).
      apply listSatisfiable_cmerge in Hsat as (Hsat0 & Hsat1).
      pose proof Htsc as Htscall.
      destruct
        (CALLS.ljoin_list_scoped_plain_inv scope ts0 us ts sb sst' Hj Htsc)
        as (Htsc0 & Htsc1).

      (** the emitted operand equations are well separated *)
      assert
        (NoDup
           (vars_defined (List.concat eqss0 ++ List.concat eqss1)
              ++ st_ids st)) as Hndr.
      { exact
          (CALLS.NoDup_vd_drop
             (List.map (fun '(x, e) => ([x], [e]))
                (combine (List.map fst xs)
                   (unnest_arrow (List.concat ess0) (List.concat ess1) anns)))
             (List.concat eqss0 ++ List.concat eqss1) (st_ids st) Hnd). }
      assert
        (Permutation
           (vars_defined (List.concat eqss0) ++ st_ids st) (st_ids st1))
        as Hperm0.
      { exact
          (CALLS.map_bind2_unnest_vars_perm
             P false e0s ess0 eqss0 st st1 H2 Hmap0). }
      assert
        (NoDup (vars_defined (List.concat eqss0) ++ st_ids st)) as Hnd1.
      { exact
          (CALLS.NoDup_vd_app_l
             (List.concat eqss0) (List.concat eqss1) (st_ids st) Hndr). }
      assert
        (NoDup (vars_defined (List.concat eqss1) ++ st_ids st1)) as Hnd2.
      { exact
          (CALLS.NoDup_vd_app_r
             (List.concat eqss0) (List.concat eqss1)
             (st_ids st) (st_ids st1) Hperm0 Hndr). }
      assert
        (forall x, In x (CALLS.moved_by env st st1) -> ~ In x scope) as Hmv1.
      { intros x Hx. apply Hmv.
        exact (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hx). }
      assert
        (forall x, In x (CALLS.moved_by env st1 st2) -> ~ In x scope) as Hmv2.
      { intros x Hx. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st1 st' Hf1 x).
        exact (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hx). }

      (** the ambients line up with each operand list *)
      pose proof (ljoin_list_length ts0 us ts sb sst' Hj) as Hjoinlen.
      assert (List.length ambs = List.length ts0) as Hlen0.
      { rewrite Hlen. exact Hjoinlen. }
      assert (List.length ts0 = List.length us) as Hinlen.
      { exact (ljoin_list_input_lengths ts0 us ts sb sst' Hj). }
      assert (List.length ambs = List.length us) as Hlen1.
      { rewrite Hlen0. exact Hinlen. }

      (** the two operand witnesses *)
      destruct
        (carries_list_streams_intro P e0s Hall0 false ambs
           ess0 eqss0 st st1 ts0 sst sa ce1 xstd xstm ts0x yst yst dlt
           H2 H3 Hnd1 Hmv1 Hcsc0 Htsc0 Hambsc Hcov0 Hlen0
           Hfound1 Hmap0 Hts0 Hgen1 Ht0y Hsat0)
        as (dlt1 & Hres1).
      unfold carries_result_streams in Hres1.
      destruct Hres1 as (Hoff1 & Hce1 & Hrel1 & Hscope1 & Htgt1).

      assert (listSatisfiable dlt1 (carried us)) as Hsat1'.
      { exact
          (CALLS.listSatisfiable_off
             scope (carried us) (CALLS.moved_by env st st1)
             dlt dlt1 Hcsc1 Hmv1 Hoff1 Hsat1). }
      destruct
        (carries_list_streams_intro P es Hall1 false ambs
           ess1 eqss1 st1 st2 us sa sb ce2 xstm xst' usx yst yst dlt1
           H4 H7 Hnd2 Hmv2 Hcsc1 Htsc1 Hambsc Hcov1 Hlen1
           Hfound2 Hmap1 Hus Hgen2 Huy Hsat1')
        as (dlt2 & Hres2).
      unfold carries_result_streams in Hres2.
      destruct Hres2 as (Hoff2 & Hce2 & Hrel2 & Hscope2 & Htgt2).

      assert
        (forall x,
           In x (CALLS.moved_by env st1 st2) ->
           ~ In x (scope ++ CALLS.moved_by env st st1)) as Hsep1.
      { intros x Hin Hxin. apply in_app_or in Hxin as [Hscope|Hfirst].
        - exact (Hmv2 x Hin Hscope).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st1 st2 x Hfirst Hin). }
      assert (stream_rel dlt2 ambs ts0 ts0x) as Hrel1'.
      { apply
          (stream_rel_off_scope
             (scope ++ CALLS.moved_by env st st1)
             (CALLS.moved_by env st1 st2) dlt1 dlt2 ambs ts0 ts0x).
        - apply
            (@Forall_impl ST
               (st_scoped scope)
               (st_scoped (scope ++ CALLS.moved_by env st st1))).
          + intros a0 Ha0. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Ha0.
          + exact Hambsc.
        - apply
            (@Forall_impl LST
               (fun src => st_scoped scope (fst src))
               (fun src =>
                  st_scoped
                    (scope ++ CALLS.moved_by env st st1) (fst src))).
          + intros src Hsrc. apply st_scoped_weaken with (scope1 := scope).
            * apply incl_appl, incl_refl.
            * exact Hsrc.
          + exact Htsc0.
        - exact Htgt1.
        - exact Hsep1.
        - exact Hoff2.
        - exact Hrel1. }

      (** the delays the pass built, and their pointwise relation *)
      assert
        (Forall2
           (fun e t0 =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t0], s))
              /\ snd t0 = []) (List.concat ess0) ts0x) as Hew0.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat ess0) ts0x xst xst
             Hc0 Ht0x). }
      assert
        (Forall2
           (fun e t0 =>
              (forall s,
                 assign_lexp_type GL env base_ty rst_ty e s = OK ([t0], s))
              /\ snd t0 = []) (List.concat ess1) usx) as Hew1.
      { exact
          (CALLS.assign_lexps_elementwise
             GL env base_ty rst_ty (List.concat ess1) usx xst xst
             Hc1 Hux). }
      destruct
        (CALLS.unnest_arrow_types
           GL env base_ty rst_ty (List.concat ess0) (List.concat ess1)
           anns ts0x usx xst Hew0 Hew1 Hle0 Hle1)
        as (rs & Hjr & Hallr).
      assert (stream_rel dlt2 ambs ts rs) as Hrelrs.
      { exact
          (ljoin_list_rel_plain_streams
             dlt2 ambs ts0 us ts ts0x usx rs sb sst' xst xst
             Hj Hjr Hrel1' Hrel2). }

      (** one ambient per minted variable *)
      assert
        (List.map fst
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
         = List.map fst xs) as Hmapfst.
      { rewrite map_map. apply map_ext.
        intros (id & (ty0 & (cl0 & nm0))). reflexivity. }
      assert
        (Forall2 (fun xa ck' => snd (snd xa) = ck')
           (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
           (List.map clock_of_nclock anns)) as Hclkalign.
      { pose proof (idents_for_anns_values anns xs st2 st' Hids) as Hvals.
        clear - Hvals. revert anns Hvals.
        induction xs as [|xa xs IH]; intros anns0 Hvals.
        - destruct anns0; [constructor|discriminate Hvals].
        - destruct anns0 as [|a0 anns0]; [discriminate Hvals|].
          simpl in Hvals. injection Hvals as Hhd Htl.
          destruct xa as (id & a). simpl in Hhd. subst a.
          destruct a0 as (ty0 & (cl0 & nm0)).
          simpl. constructor; [reflexivity|exact (IH anns0 Htl)]. }
      assert (declared_ambients (List.map fst xs) ambs) as Hdecl.
      { rewrite <- Hmapfst.
        exact
          (declared_ambients_of_state
             (List.map (fun '(id, (ty0, (cl0, _))) => (id, (ty0, cl0))) xs)
             st' (List.map clock_of_nclock anns) ambs
             (idents_for_anns_incl anns xs st2 st' Hids)
             Hclkalign Hfound Hcovered). }

      (** the minted variables are fresh, and their names with them *)
      assert
        (Permutation
           (vars_defined
              (combine (List.map (fun '(id, _) => [id]) xs)
                 (List.map (fun e => [e])
                    (unnest_arrow (List.concat ess0) (List.concat ess1) anns))
               ++ List.concat eqss0 ++ List.concat eqss1) ++ st_ids st)
           (st_ids st')) as Hpall.
      { exact
          (unnest_exp_vars_perm
             P (Earrow e0s es anns) ic
             (List.map (fun '(id, ann0) => Evar id ann0) xs)
             (combine (List.map (fun '(id, _) => [id]) xs)
                (List.map (fun e => [e])
                   (unnest_arrow (List.concat ess0) (List.concat ess1) anns))
              ++ List.concat eqss0 ++ List.concat eqss1)
             st st' Hwl Hunm). }
      assert (NoDup (st_ids st')) as Hndst'.
      { exact (Permutation_NoDup Hpall Hnd0). }
      assert (Permutation (List.map fst xs ++ st_ids st2) (st_ids st')) as Hpx.
      { exact (idents_for_anns_vars_perm anns xs st2 st' Hids). }
      assert (NoDup (List.map fst xs ++ st_ids st2)) as Hndx.
      { rewrite Hpx. exact Hndst'. }
      assert (NoDup (List.map fst xs)) as Hndfst.
      { exact (NoDup_app_l (List.map fst xs) (st_ids st2) Hndx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st2 st')) as Hbnew.
      { intros b Hb.
        unfold CALLS.sec_of in Hb. apply in_flat_map in Hb as (x & Hx & Hb).
        unfold CALLS.moved_by, CALLS.EXPR.moved_by, CALLS.sec_of.
        apply in_flat_map. exists x. split; [|exact Hb].
        apply CALLS.new_ids_spec. split.
        - exact (idents_for_anns_incl_ids anns xs st2 st' Hids x Hx).
        - exact
            (NoDup_app_In x (List.map fst xs) (st_ids st2) Hndx Hx). }
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   ~ In b (scope ++ CALLS.moved_by env st st2)) as Hsepx.
      { intros b Hb Hin. apply in_app_or in Hin as [Hin|Hin].
        - apply (Hmv b); [|exact Hin].
          exact
            (CALLS.moved_by_suffix_local
               env st st2 st' Hf12 b (Hbnew b Hb)).
        - exact
            (CALLS.moved_by_disjoint_local
               env env_inj st st2 st' b Hin (Hbnew b Hb)). }

      (** what the delays' types mention *)
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           ts0x) as Htgt1'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st1) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st st1).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_prefix_local env st st1 st2 Hf2).
          + exact Htq.
        - exact Htgt1. }
      assert
        (Forall
           (fun t0 => st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))
           usx) as Htgt2'.
      { apply
          (@Forall_impl LST
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st1 st2) (fst t0))
             (fun t0 =>
                st_scoped (scope ++ CALLS.moved_by env st st2) (fst t0))).
        - intros tq Htq.
          apply st_scoped_weaken with
            (scope1 := scope ++ CALLS.moved_by env st1 st2).
          + apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr.
            exact (CALLS.moved_by_suffix_local env st st1 st2 Hf1).
          + exact Htq.
        - exact Htgt2. }
      assert
        (Forall
           (fun r => st_scoped (scope ++ CALLS.moved_by env st st2) (fst r))
           rs) as Hscrs.
      { exact
          (CALLS.ljoin_list_scoped_plain
             (scope ++ CALLS.moved_by env st st2) ts0x usx rs xst xst
             Hjr Htgt1' Htgt2'). }

      (** the aligned premise the emitted definitions consume *)
      assert
        (Forall3
           (fun a e src =>
              forall tf0 s s',
                assign_lexp_type GL env base_ty rst_ty e s = OK ([tf0], s') ->
                satisfiable dlt2 (fst tf0) (merge a (fst src))
                /\ st_scoped (scope ++ CALLS.moved_by env st st2) (fst tf0))
           ambs
           (unnest_arrow (List.concat ess0) (List.concat ess1) anns)
           ts) as Hlift3.
      { unfold stream_rel in Hrelrs. clear - Hallr Hrelrs Hscrs.
        revert Hallr Hscrs.
        generalize
          (unnest_arrow (List.concat ess0) (List.concat ess1) anns) as rhss.
        induction Hrelrs as [|a src r ambs1 ts1 rs1 Hhead Hrest IH];
          intros rhss Hallr Hscrs.
        - inversion Hallr; subst. constructor.
        - destruct rhss as [|e rhss]; inversion Hallr as
            [|e0a r0 rhss0 rs2 Hq Hallr']; subst.
          inversion Hscrs as [|r1 rs3 Hsc0 Hscrs']; subst.
          constructor.
          + intros tf0 s s' Htf. destruct Hq as (_ & _ & Hq3).
            rewrite (Hq3 tf0 s s' Htf). split; [exact Hhead|exact Hsc0].
          + exact (IH rhss Hallr' Hscrs'). }
      assert
        (Forall
           (fun e =>
              (match e with Eapp _ _ _ _ => False | _ => True end)
              /\ forall ts0' s s',
                   assign_lexp_type GL env base_ty rst_ty e s = OK (ts0', s') ->
                   s' = s /\ List.length ts0' = 1 /\ carried ts0' = [])
           (unnest_arrow (List.concat ess0) (List.concat ess1) anns)) as Hpure.
      { clear - Hallr.
        induction Hallr as [|e r rhss0 rs0 Hq Hrest IH]; [constructor|].
        destruct Hq as (Hq1 & Hq2 & _).
        constructor; [split; [exact Hq1|exact Hq2]|exact IH]. }
      assert
        (List.length (List.map fst xs)
         = List.length
             (unnest_arrow (List.concat ess0) (List.concat ess1) anns))
        as Hlend.
      { rewrite Hlbs. symmetry.
        exact
          (unnest_arrow_length
             (List.concat ess0) (List.concat ess1) anns Hle0 Hle1). }

      (** the emitted definitions *)
      destruct
        (lifted_defs_streams
           (scope ++ CALLS.moved_by env st st2) (List.map fst xs)
           (unnest_arrow (List.concat ess0) (List.concat ess1) anns)
           ts ambs ced xst xstd dlt2
           Hndfst Hlend Hsepx Hdecl
           (@Forall_impl ST (st_scoped scope)
              (st_scoped (scope ++ CALLS.moved_by env st st2))
              (fun a0 Ha0 =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) a0
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Ha0)
              ambs Hambsc)
           Hpure
           (@Forall_impl LST
              (fun src => st_scoped scope (fst src))
              (fun src =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst src))
              (fun src Hsrc =>
                 st_scoped_weaken scope
                   (scope ++ CALLS.moved_by env st st2) (fst src)
                   (incl_appl (CALLS.moved_by env st st2) (incl_refl scope))
                   Hsrc)
              ts Htscall)
           Hlift3 Hgend)
        as (dlt3 & Hoff3 & Hced & Hscoped & Hrel3).

      (** the minted names are among the ones the whole run moved *)
      assert
        (forall b, In b (sec_of (List.map fst xs)) ->
                   In b (CALLS.moved_by env st st')) as Hincx.
      { intros b Hb.
        exact
          (CALLS.moved_by_suffix_local
             env st st2 st' Hf12 b (Hbnew b Hb)). }

      (** the results' relation, at the names the pass bound them to *)
      assert (stream_rel dlt3 ambs ts ts'') as Hrelfin.
      { unfold stream_rel. clear - Hrel3 Hevars.
        revert ambs ts Hrel3.
        induction Hevars as [|xa t xs0 ts0 Hxa Hrest IH];
          intros ambs ts Hrel3.
        - inversion Hrel3; subst. constructor.
        - simpl in Hrel3.
          inversion Hrel3 as
            [|a0 x0 src0 ambs1 xs1 ts1 Hhead Hrest3]; subst.
          destruct Hxa as (b & Hb & Ht). subst t.
          constructor.
          + rewrite fst_lvar. exact (Hhead b Hb).
          + exact (IH ambs1 ts1 Hrest3). }

      exists dlt3. unfold carries_result_streams. split.
      - (** the witness moved only where the run did *)
        intros x Hx.
        rewrite Hoff1.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_prefix_local env st st1 st' Hf23 x Hin). }
        rewrite Hoff2.
        2: { intro Hin. apply Hx.
             exact
               (CALLS.moved_by_suffix_local
                  env st st1 st' Hf1 x
                  (CALLS.moved_by_prefix_local env st1 st2 st' Hf3 x Hin)). }
        apply Hoff3. intro Hin. apply Hx. exact (Hincx x Hin).
      - split.
        + (** every emitted constraint still holds *)
          apply listSatisfiable_app. split; [exact Hced|].
          apply listSatisfiable_app. split.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce1 (scope ++ CALLS.moved_by env st st1)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope1.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_prefix_local env st st1 st2 Hf2 y Hin).
            -- exact Hoff3.
            -- apply
                 (CALLS.listSatisfiable_off_scope
                    ce1 (scope ++ CALLS.moved_by env st st1)
                    (CALLS.moved_by env st1 st2) dlt1 dlt2).
               ++ exact Hscope1.
               ++ intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
                  ** exact (Hmv2 y Hy Hin).
                  ** exact
                       (CALLS.moved_by_disjoint_local
                          env env_inj st st1 st2 y Hin Hy).
               ++ exact Hoff2.
               ++ exact Hce1.
          * apply
              (CALLS.listSatisfiable_off_scope
                 ce2 (scope ++ CALLS.moved_by env st1 st2)
                 (sec_of (List.map fst xs)) dlt2 dlt3).
            -- exact Hscope2.
            -- intros y Hy Hin. apply (Hsepx y Hy).
               apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
                 [now left|].
               right.
               exact
                 (CALLS.moved_by_suffix_local env st st1 st2 Hf1 y Hin).
            -- exact Hoff3.
            -- exact Hce2.
        + split; [exact Hrelfin|]. split.
          * (** and mentions only names in scope or moved *)
            apply Forall_app. split.
            -- apply
                 (@Forall_impl constraint
                    (constraint_scoped
                       ((scope ++ CALLS.moved_by env st st2)
                          ++ sec_of (List.map fst xs)))
                    (constraint_scoped
                       (scope ++ CALLS.moved_by env st st'))).
               ++ intros c Hc.
                  apply constraint_scoped_incl with
                    (scope1 := (scope ++ CALLS.moved_by env st st2)
                                 ++ sec_of (List.map fst xs)).
                  2: exact Hc.
                  apply incl_app; [apply incl_app|].
                  ** apply incl_appl, incl_refl.
                  ** apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st2 st' Hf3).
                  ** apply incl_appr. exact Hincx.
               ++ exact Hscoped.
            -- apply Forall_app. split.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st1))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st st1).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     exact
                       (CALLS.moved_by_prefix_local env st st1 st' Hf23).
                  ** exact Hscope1.
               ++ apply
                    (@Forall_impl constraint
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st1 st2))
                       (constraint_scoped
                          (scope ++ CALLS.moved_by env st st'))).
                  ** intros c Hc.
                     apply constraint_scoped_incl with
                       (scope1 := scope ++ CALLS.moved_by env st1 st2).
                     2: exact Hc.
                     apply incl_app; [apply incl_appl, incl_refl|].
                     apply incl_appr.
                     apply incl_tran with
                       (m := CALLS.moved_by env st1 st').
                     --- exact
                           (CALLS.moved_by_prefix_local
                              env st1 st2 st' Hf3).
                     --- exact
                           (CALLS.moved_by_suffix_local
                              env st st1 st' Hf1).
                  ** exact Hscope2.
          * (** the bound results are names the run minted *)
            apply
              (CALLS.Forall2_right_In
                 (fun xa t =>
                    exists b, Env.find (fst xa) env = Some b /\ t = lvar b)
                 (fun tgt =>
                    st_scoped (scope ++ CALLS.moved_by env st st') (fst tgt))
                 xs ts'' Hevars).
            intros xa t Hxa Hp. destruct Hp as (b & Hb & Ht). subst t.
            rewrite fst_lvar. intros y Hy.
            destruct Hy as [Hy|[]]. subst y.
            apply in_or_app. right. apply Hincx.
            unfold CALLS.sec_of. apply in_flat_map. exists (fst xa).
            split; [now apply in_map|]. rewrite Hb. now left.
    Qed.


  End ExpressionContract.

End StreamAmbients.

End SecLusUnnestingStreams.
