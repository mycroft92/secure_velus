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

  (** * What the no-op pass records about the variable it lifts

      [unnest_noops_exp_inv] says an argument is either kept or bound to a
      fresh variable, but not what clock that variable was given.  The
      pointwise contract needs it: the lifted variable's ambient has to be the
      one covering its *own* slot, and [state_clocks_found] reads a variable's
      clock off the state.  The pass stores the head of the argument's
      annotation, so the clock is the argument's own. *)
  Lemma unnest_noops_exp_inv_anns :
    forall cki e e' eqs st st',
      unnest_noops_exp cki e st = ((e', eqs), st') ->
      (e' = e /\ eqs = [] /\ st' = st)
      \/ (exists x ty cko o,
             hd (bool_type, (Cbase, None)) (annot e) = (ty, (cko, o))
             /\ e' = Evar x (ty, (cko, o))
             /\ eqs = [([x], [e])]
             /\ In (x, (ty, cko)) (st_anns st')
             /\ Permutation (x :: st_ids st) (st_ids st')).
  Proof.
    intros cki e e' eqs st st' H.
    unfold unnest_noops_exp in H.
    destruct (hd (bool_type, (Cbase, None)) (annot e))
      as (ty, (cko, o)) eqn:Han.
    destruct (is_noops_exp cki e) eqn:Enoop;
      repeat UNN.Fresh.Tactics.inv_bind.
    - now left.
    - match goal with
      | H : fresh_ident norm1 (ty, cko) st = _ |- _ => rename H into Ex
      end.
      right. exists x, ty, cko, o.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      + exact (UNN.Fresh.Facts.fresh_ident_In _ _ _ _ _ Ex).
      + exact (UNN.Fresh.Facts.fresh_ident_vars_perm _ _ _ _ _ Ex).
  Qed.

  (** And the clock it records is the one the contract's ambient covers: an
      argument the pass lifts is normalized, so it has exactly one stream, and
      that stream's clock is the head of its annotation. *)
  Lemma noops_lifted_clock :
    forall e ty cko o,
      numstreams e = 1 ->
      hd (bool_type, (Cbase, None)) (annot e) = (ty, (cko, o)) ->
      clockof e = [cko].
  Proof.
    intros e ty cko o Hns Han.
    rewrite clockof_annot.
    rewrite <- length_annot_numstreams in Hns.
    destruct (annot e) as [|an ans]; [cbn in Hns; discriminate Hns|].
    destruct ans; [|cbn in Hns; discriminate Hns].
    cbn [hd] in Han. subst an. reflexivity.
  Qed.

  (** A normalized argument has one stream, so one clock. *)
  Lemma normalized_lexp_clockof :
    forall e, normalized_lexp e -> exists ck, clockof e = [ck].
  Proof.
    intros e Hn.
    assert (List.length (clockof e) = 1) as Hl
        by (rewrite length_clockof_numstreams;
            exact (normalized_lexp_numstreams e Hn)).
    destruct (clockof e) as [|ck cks]; cbn in Hl; [discriminate|].
    destruct cks; cbn in Hl; [|discriminate].
    exists ck. reflexivity.
  Qed.

(** * The call's results, read at their own ambients

    The last step of the streams call case, and the one place the pointwise
    contract differs from the scalar one at the end of the proof.  The
    instantiated block relates each result to the call's *single* ambient --
    that is all [generate_constraints_mono_sem] produces -- and the pointwise
    conclusion asks for the relation at each result's own.  It goes through
    because the call's ambient is inside every one of them
    ([call_amb_below_result_ambients]) and [satisfiable] only gets easier as
    its right-hand side grows. *)

Lemma call_results_stream_rel :
  forall dlt amb_call (ambs : list ST) (outs outt : list ident)
         (ts'' : list LST) (held : list constraint),
    Forall (fun a => incl amb_call a) ambs ->
    Forall2 (fun o b => satisfiable dlt [b] (merge amb_call [o])) outs outt ->
    Forall2 (fun b t => t = lvar b) outt ts'' ->
    List.length ambs = List.length outs ->
    stream_rel dlt ambs
      (List.map (fun o => (([o] : ST), held)) outs) ts''.
Proof.
  intros dlt amb_call ambs outs outt ts'' held Hbelow Hpairs Hevars Hlen.
  revert ambs ts'' Hbelow Hevars Hlen.
  induction Hpairs as [|o b outs0 outt0 Hob Hr IH];
    intros ambs ts'' Hbelow Hevars Hlen.
  - inversion Hevars; subst ts''.
    destruct ambs as [|a ambs]; [|cbn in Hlen; discriminate].
    cbn [List.map]. constructor.
  - inversion Hevars as [|b0 t0 outt1 ts1 Ht0 Htr]; subst.
    destruct ambs as [|a ambs]; [cbn in Hlen; discriminate|].
    inversion Hbelow as [|a0 ambs0 Ha Habr]; subst.
    cbn [List.map]. constructor.
    + cbn [fst]. subst. rewrite fst_lvar.
      eapply order_trans; [exact Hob|].
      apply hm_ext_incl.
      exact (incl_merge_mono amb_call a [o] [o] Ha (incl_refl [o])).
    + apply IH; [exact Habr|exact Htr|cbn in Hlen; now inversion Hlen].
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

(** Two pointwise relations at the same ambients compose, slot by slot: the
    scalar [amb_trans], transposed.  The call case needs it because the
    arguments cross two passes -- the recursive unnesting and the no-op lift --
    and each relates its own pair of type lists. *)

Lemma stream_rel_compose :
  forall dlt ambs (l1 l2 l3 : list LST),
    stream_rel dlt ambs l1 l2 ->
    stream_rel dlt ambs l2 l3 ->
    stream_rel dlt ambs l1 l3.
Proof.
  intros dlt ambs l1 l2 l3 H1. revert l3.
  induction H1 as [|a p q as0 ps qs Hpq Hr IH]; intros l3 H2.
  - inversion H2; subst. constructor.
  - inversion H2 as [|a0 q0 w as1 qs1 ws Hqw Hrw]; subst. constructor.
    + eapply satisfiable_trans; [exact Hqw|].
      apply satisfiable_merge_intro; [apply satisfiable_merge_l|exact Hpq].
    + exact (IH ws Hrw).
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

  (** * The ambients the streams call case hands its arguments

      [carries_list_streams_intro] wants a [clocks_covered] for the argument
      streams.  The argument at slot [i] runs on the instantiated formal clock,
      so the ambient that covers it is the call's own joined with that slot's
      clock actuals -- which is [CALLS.call_arg_ambient], the same set the
      augmentation uses.  Here that is assembled into the list the contract
      expects, one entry per argument stream. *)

  Definition call_arg_ambients (sub : ident -> option ident) (bckty : ST)
      (ncks : list nclock) (ins : list (ident * clock)) : list ST :=
    List.map (fun p => CALLS.call_arg_ambient env rst_ty sub bckty
                         (snd (fst p)))
      (combine ins ncks).

  Lemma clocks_covered_call_args :
    forall bck sub (ins : list (ident * clock)) (ncks : list nclock) bckty,
      assign_clk_type env base_ty bck = Some bckty ->
      Forall2 (WellInstantiated bck sub) ins ncks ->
      (forall nck, In nck ncks ->
         exists ckty, assign_clk_type env base_ty (stripname nck) = Some ckty) ->
      clocks_covered (List.map stripname ncks)
        (call_arg_ambients sub bckty ncks ins).
  Proof.
    intros bck sub ins ncks bckty Hbk Hwi Hdef.
    unfold call_arg_ambients, clocks_covered.
    induction Hwi as [|p nck ins0 ncks0 Hp Hr IH]; [constructor|].
    cbn [combine List.map].
    constructor.
    - (** this stream's clock is the formal's, instantiated *)
      destruct (Hdef nck (or_introl (@Coq.Init.Logic.eq_refl _ nck)))
        as (ckty & Hck).
      exists ckty. split; [exact Hck|].
      destruct Hp as (_ & Hi).
      cbn [fst snd].
      eapply CALLS.call_arg_ambient_covers; [exact Hi|exact Hbk|exact Hck].
    - apply IH. intros nck0 Hn. apply Hdef. now right.
  Qed.

    (** * From the per-slot ambients to the augmented actuals

        The identity the augmentation design was for, read in the direction the
        streams call case needs it.  The contract delivers each argument at its
        own ambient,

          [merge (merge amb_call (clock_actuals sub ck_i)) (fst t_i)],

        and [generate_constraints_mono_sem_aug] asks for it at the call's own
        ambient over the *augmented* actual,

          [merge amb_call (merge (fst t_i) (clock_actuals sub ck_i))].

        Those name the same set, so one is the other; that is the whole content
        of the augmentation, and it is why the arguments never have to be
        weakened to a common ambient -- which they could not be, since the
        slots' clocks differ. *)

    Lemma call_arg_ambients_cons :
      forall sub bckty p ncks nck ins,
        call_arg_ambients sub bckty (nck :: ncks) (p :: ins)
        = CALLS.call_arg_ambient env rst_ty sub bckty (snd p)
          :: call_arg_ambients sub bckty ncks ins.
    Proof. reflexivity. Qed.

    Lemma satisfiable_reassoc :
      forall dlt x A B C,
        satisfiable dlt x (merge (merge A B) C) ->
        satisfiable dlt x (merge A (merge C B)).
    Proof.
      intros dlt x A B C H.
      eapply order_trans; [exact H|].
      apply hm_ext_incl. intros z Hz.
      apply SymTypes.in_merge_inv in Hz as [Hz|Hz].
      - apply SymTypes.in_merge_inv in Hz as [Hz|Hz];
          [apply in_merge_left; exact Hz
          |apply in_merge_right, in_merge_right; exact Hz].
      - apply in_merge_right, in_merge_left; exact Hz.
    Qed.

    Lemma call_args_augmented :
      forall dlt sub bckty (ins : list (ident * clock)) (ncks : list nclock)
             (argts argt : list LST),
        stream_rel dlt (call_arg_ambients sub bckty ncks ins) argts argt ->
        Forall2 (fun t1 t2 =>
                   satisfiable dlt t2 (merge (merge [rst_ty] bckty) t1))
          (CALLS.augment_actuals env sub ins argts) (List.map fst argt).
    Proof.
      intros dlt sub bckty ins.
      induction ins as [|p ins IH]; intros ncks argts argt Hrel.
      - (** no slots left, so no argument streams either *)
        unfold call_arg_ambients in Hrel.
        destruct ncks as [|nck ncks]; cbn [combine List.map] in Hrel;
          inversion Hrel; subst; constructor.
      - destruct ncks as [|nck ncks].
        + unfold call_arg_ambients in Hrel. cbn [combine List.map] in Hrel.
          inversion Hrel; subst. constructor.
        + rewrite call_arg_ambients_cons in Hrel.
          inversion Hrel as [|a t tg ambs0 argts0 argt0 Hhd Htl]; subst.
          rewrite (CALLS.augment_actuals_cons env). cbn [List.map].
          constructor.
          * unfold CALLS.call_arg_ambient in Hhd.
            exact (satisfiable_reassoc dlt (fst tg) (merge [rst_ty] bckty)
                     (CALLS.clock_actuals env sub (snd p)) (fst t) Hhd).
          * exact (IH ncks argts0 argt0 Htl).
    Qed.

  Lemma call_arg_ambients_length :
    forall sub bckty (ncks : list nclock) (ins : list (ident * clock)),
      List.length ins = List.length ncks ->
      List.length (call_arg_ambients sub bckty ncks ins)
      = List.length ncks.
  Proof.
    intros sub bckty ncks ins Hl.
    unfold call_arg_ambients. rewrite map_length.
    revert ncks Hl. induction ins as [|p ins IH]; intros ncks Hl.
    - destruct ncks; [reflexivity|discriminate].
    - destruct ncks as [|nck ncks]; [discriminate|].
      simpl. f_equal. apply IH. simpl in Hl; congruence.
  Qed.

  (** The argument ambients are scoped, which the contract also asks: the reset
      name and the base clock's type are, and what the clock actuals add are
      security names of caller variables. *)
  Lemma call_arg_ambients_scoped :
    forall scope sub bckty (ncks : list nclock) (ins : list (ident * clock)),
      In rst_ty scope ->
      st_scoped scope bckty ->
      (forall y ck nck,
          In ((y, ck), nck) (combine ins ncks) ->
          forall z, In z (CALLS.clock_actuals env sub ck) -> In z scope) ->
      stream_ambients_scoped scope (call_arg_ambients sub bckty ncks ins).
  Proof.
    intros scope sub bckty ncks ins Hrst Hbck Hrange.
    unfold stream_ambients_scoped, call_arg_ambients.
    apply Forall_forall. intros a Ha.
    apply in_map_iff in Ha as (p & Hp & Hpin). subst a.
    destruct p as ((y, ck), nck).
    unfold CALLS.call_arg_ambient. intros z Hz.
    apply in_merge_inv in Hz as [Hz|Hz].
    - apply in_merge_inv in Hz as [Hz|Hz].
      + destruct Hz as [Hz|[]]. subst z. exact Hrst.
      + exact (Hbck z Hz).
    - exact (Hrange y ck nck Hpin z Hz).
  Qed.

  Lemma Forall2_in_left_streams :
    forall {A B : Type} (R : A -> B -> Prop) xs ys x,
      Forall2 R xs ys -> In x xs -> exists y, In y ys /\ R x y.
  Proof.
    intros A B R xs ys x H. induction H as [|a b xs ys Hab H IH]; intros Hin;
      [contradiction|].
    destruct Hin as [<-|Hin]; [exists b; split; [now left|exact Hab]|].
    destruct (IH Hin) as (y & Hy & Hr). exists y. split; [now right|exact Hr].
  Qed.

  (** The slot ambients are scoped, with the clock actuals found among the
      argument streams' own security names -- which the call's source types
      already put in the scope -- instead of among the environment's range. *)
  Lemma call_arg_ambients_scoped_named :
    forall scope sub bck bckty (ncks : list nclock)
           (ins : list (ident * clock)) (argts : list LST),
      In rst_ty scope ->
      st_scoped scope bckty ->
      wc_env ins ->
      Forall2 (WellInstantiated bck sub) ins ncks ->
      Forall2 (fun t nck => forall w g, snd nck = Some w ->
                                         Env.find w env = Some g ->
                                         In g (fst t)) argts ncks ->
      Forall (fun t => st_scoped scope (fst t)) argts ->
      stream_ambients_scoped scope (call_arg_ambients sub bckty ncks ins).
  Proof.
    intros scope sub bck bckty ncks ins argts Hrst Hbk Hwcenv Hwi Hnamed Hsc.
    apply call_arg_ambients_scoped; [exact Hrst|exact Hbk|].
    intros y ck nck Hin z Hz.
    apply in_combine_l in Hin.
    unfold CALLS.clock_actuals in Hz.
    destruct (CALLS.sub_names_inv env sub (clock_vars ck) z Hz)
      as (x & u & Hx & Hsub & Hu).
    assert (wc_clock ins ck) as Hwck.
    { unfold wc_env in Hwcenv. rewrite Forall_forall in Hwcenv.
      exact (Hwcenv (y, ck) Hin). }
    destruct (clock_vars_wc ins ck Hwck x Hx) as (ckx & Hxin).
    destruct (Forall2_in_left_streams _ ins ncks (x, ckx) Hwi Hxin)
      as (nckx & Hnin & Hwix).
    destruct Hwix as (Hsx & _). simpl in Hsx. rewrite Hsub in Hsx.
    destruct (Forall2_in_right _ argts ncks nckx Hnamed Hnin)
      as (t & Ht & Hnt).
    pose proof (Hnt u z (Logic.eq_sym Hsx) Hu) as Hzt.
    rewrite Forall_forall in Hsc. exact (Hsc t Ht z Hzt).
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

  (** * The no-op pass, per slot

      [noops_step] relates the arguments before and after the no-op pass at one
      ambient, and that ambient has to contain the clock type of every variable
      the pass lifts.  A lifted variable sits on its *own* argument's clock, so
      no single ambient of the call will do -- not the call's base, which is too
      small, and not the join of the slots', because the transfer then wants the
      relation back at each slot, which is smaller again.

      So the pass is done per slot.  [lifted_defs_streams] is the per-slot form
      of the step this proof takes on the variable it lifts, and it asks for
      [declared_ambients] rather than a containment in one ambient;
      [unnest_noops_exp_inv_anns] with [state_clocks_found] supplies it, since
      the clock the pass records is the argument's own. *)
  Lemma noops_step_streams :
    forall bound (ambs : list ST) ckis es1 es2 eqs2 st st' ts1 ts2 ce
           xst xst' zst zst' yst yst' dlt,
      List.length ckis = List.length es1 ->
      Forall normalized_lexp es1 ->
      unnest_noops_exps ckis es1 st = ((es2, eqs2), st') ->
      NoDup (vars_defined eqs2 ++ st_ids st) ->
      (forall b, In b (CALLS.moved_by env st st') -> ~ In b bound) ->
      clocks_covered (clocksof es1) ambs ->
      stream_ambients_scoped bound ambs ->
      state_clocks_found st' ->
      assign_lexps GL env base_ty rst_ty es1 zst = OK (ts1, zst') ->
      assign_lexps GL env base_ty rst_ty es2 yst = OK (ts2, yst') ->
      Forall (fun t => st_scoped bound (fst t)) ts1 ->
      generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst
        = OK (ce, xst') ->
      exists dlt',
        CALLS.agree_off (CALLS.moved_by env st st') dlt dlt'
        /\ listSatisfiable dlt' ce
        /\ stream_rel dlt' ambs ts1 ts2
        /\ constraints_scoped (bound ++ CALLS.moved_by env st st') ce
        /\ Forall (fun t2 =>
                     st_scoped (bound ++ CALLS.moved_by env st st') (fst t2))
             ts2.
  Proof.
    intros bound ambs ckis es1. revert bound ambs ckis.
    induction es1 as [|e es1 IH];
      intros bound ambs ckis es2 eqs2 st st' ts1 ts2 ce
        xst xst' zst zst' yst yst' dlt
        Hlen Hnorm Hun Hnd Hmv Hcov Hambsc Hfound Has1 Has2 Hsc1 Hgen.

    - (** nothing left: the state has not moved *)
      destruct ckis; cbn in Hlen; [|discriminate].
      apply CALLS.unnest_noops_exps_nil_l in Hun as (? & ? & ?); subst.
      apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has1
        as (? & _ & ?); subst.
      apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has2
        as (? & _ & ?); subst.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      unfold clocks_covered in Hcov. cbn [clocksof flat_map] in Hcov.
      inversion Hcov; subst ambs.
      exists dlt. split; [|split; [|split; [|split]]];
        solve [apply agree_off_refl | constructor].

    - (** one argument, then the rest on top of it *)
      destruct ckis as [|ck ckis]; cbn in Hlen; [discriminate|].
      inversion Hlen as [Hlen'].
      inversion Hnorm as [|e0 es0 Hne Hnes]; subst.
      apply CALLS.unnest_noops_exps_cons in Hun
        as (e2 & eqh & st1 & es2t & eqt & Hh & Ht & ? & ?); subst.
      assert (st_follows st st1) as Hf0
          by (eapply unnest_noops_exp_st_follows; eauto).
      assert (st_follows st1 st') as Hf1
          by (eapply unnest_noops_exps_st_follows; eauto).
      assert (Permutation (vars_defined eqh ++ st_ids st) (st_ids st1))
        as Hp0 by (eapply CALLS.unnest_noops_exp_vars_perm; eauto).

      (** this slot's ambient, and the rest *)
      destruct (normalized_lexp_clockof e Hne) as (cke & Hcke).
      unfold clocks_covered in Hcov.
      cbn [clocksof flat_map] in Hcov. rewrite Hcke in Hcov.
      cbn [app] in Hcov.
      inversion Hcov as [|c0 a cs0 ambs0 Hca Hcovr]; subst ambs.
      inversion Hambsc as [|a0 ambs1 Hasc Hambscr]; subst.

      (** the two sides' types, head and tail *)
      apply assign_lexps_carried_cons in Has1
        as (t & r & sa & Ht0 & Hr & ? & _); subst.
      apply assign_lexps_carried_cons in Has2
        as (u & r2 & sb & Hu0 & Hr2 & ? & _); subst.
      assert (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK (t, s))
        as Hpure
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
      assert (List.length t = 1) as Hlt
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
      destruct t as [|t0 [|]]; cbn in Hlt; try discriminate.
      apply Forall_app in Hsc1 as (Hsc1h & Hsc1t).
      inversion Hsc1h as [|z zs Hz _]; subst.

      (** the emitted equations, head and tail *)
      apply generate_leqns_constraints_app in Hgen
        as (ceh & cet & xstm & Hgenh & Hgent & ?); subst.
      assert (NoDup (vars_defined eqt ++ st_ids st1)) as Hndt
          by (eapply NoDup_vd_app_r; [exact Hp0|exact Hnd]).
      assert (state_clocks_found st1) as Hfound1
          by (exact (state_clocks_found_prefix st1 st' Hf1 Hfound)).

      (** the rest of the arguments *)
      edestruct (IH bound ambs0 ckis es2t eqt st1 st' r r2 cet
                   xstm xst' sa zst' sb yst' dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hsc2t).
      { exact Hlen'. }
      { exact Hnes. }
      { exact Ht. }
      { exact Hndt. }
      { intros b Hb. apply Hmv.
        apply (CALLS.moved_by_suffix_local env st st1 st' Hf0). exact Hb. }
      { exact Hcovr. }
      { exact Hambscr. }
      { exact Hfound. }
      { exact Hr. }
      { exact Hr2. }
      { exact Hsc1t. }
      { exact Hgent. }

      (** and the head *)
      apply unnest_noops_exp_inv_anns in Hh
        as [(? & ? & ?)|(x & ty & cko & o & Han & ? & ? & Hxan & Hpx)]; subst.
      + (** kept: the same expression, so the same type, nothing emitted *)
        apply generate_leqns_constraints_nil in Hgenh as (? & ?); subst.
        rewrite (Hpure yst) in Hu0. inv Hu0.
        exists dlt1. split; [|split; [|split; [|split]]].
        * exact Hoff1.
        * exact Hce1.
        * constructor; [apply satisfiable_merge_r|exact Hrel1].
        * exact Hscope1.
        * constructor; [|exact Hsc2t].
          eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz].
      + (** bound: [lifted_defs_streams] on the one variable it minted *)
        apply assign_lexp_Evar_inv in Hu0 as (b & Hb & ? & ?); subst.
        assert (~ In x (st_ids st)) as Hxst.
        { cbn in Hnd. inversion Hnd as [|z zs Hzn _]; subst.
          intro Hc. apply Hzn. apply in_or_app. now right. }
        assert (In x (CALLS.new_ids st st1)) as Hxnew.
        { apply new_ids_spec. split; [|exact Hxst].
          eapply Permutation_in; [exact Hpx|now left]. }
        assert (In b (CALLS.moved_by env st st1)) as Hbmv.
        { unfold CALLS.moved_by, CALLS.sec_of. apply in_flat_map.
          exists x. split; [exact Hxnew|]. rewrite Hb. now left. }
        assert (forall c, In c (CALLS.sec_of env [x]) ->
                          In c (CALLS.moved_by env st st1)) as Hbnew.
        { intros c Hc. unfold CALLS.sec_of in Hc. cbn in Hc.
          rewrite Hb in Hc. destruct Hc as [|[]]; subst. exact Hbmv. }
        assert (forall c, In c (CALLS.sec_of env [x]) ->
                    ~ In c (bound ++ CALLS.moved_by env st1 st')) as Hsepx.
        { intros c Hc Hin. apply Hbnew in Hc.
          apply in_app_or in Hin as [Hin|Hin].
          - eapply (Hmv c); [|exact Hin].
            apply (CALLS.moved_by_prefix_local env st st1 st' Hf1). exact Hc.
          - exact (CALLS.moved_by_disjoint_local env env_inj st st1 st' c Hc Hin). }
        (** the ambient covers the clock the pass recorded *)
        assert (declared_ambients [x] [a]) as Hdecl.
        { constructor; [|constructor].
          intros ck0 Hck0.
          assert (find_clock cenv x = OK cko) as Hxck.
          { exact (Hfound1 x (ty, cko) Hxan). }
          rewrite Hxck in Hck0. inversion Hck0; subst ck0.
          assert (clockof e = [cko]) as Hcko
              by (exact (noops_lifted_clock e ty cko o
                           (normalized_lexp_numstreams e Hne) Han)).
          rewrite Hcko in Hcke. inversion Hcke; subst cke. exact Hca. }

        edestruct (lifted_defs_streams (bound ++ CALLS.moved_by env st1 st')
                     [x] [e] [t0] [a] ceh xst xstm dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2 & Hrel2).
        { constructor; [intros []|constructor]. }
        { reflexivity. }
        { exact Hsepx. }
        { exact Hdecl. }
        { constructor; [|constructor].
          eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hasc]. }
        { constructor; [|constructor]. split.
          - destruct e; try exact I. inv Hne.
          - intros tf s s' Htf. rewrite (Hpure s) in Htf. inv Htf.
            split; [reflexivity|split; [reflexivity|]].
            eapply assign_lexp_normalized_lexp_pure with (e := e); eauto. }
        { constructor; [|constructor].
          eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz]. }
        { constructor; [|constructor]. intros tf s s' Htf.
          rewrite (Hpure s) in Htf. inv Htf.
          split; [apply satisfiable_merge_r|].
          eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hz]. }
        { exact Hgenh. }

        (** the head's witness, carried over the tail's *)
        assert (satisfiable dlt2 [b] (merge a (fst t0))) as Hhead.
        { inversion Hrel2 as [|p q s0 ps qs ss Hpq _]; subst.
          now apply Hpq. }
        assert (incl (CALLS.sec_of env [x]) (CALLS.moved_by env st st'))
          as Hincx.
        { intros c Hc. apply (CALLS.moved_by_prefix_local env st st1 st' Hf1).
          now apply Hbnew. }
        exists dlt2. split; [|split; [|split; [|split]]].
        * eapply agree_off_trans.
          -- eapply agree_off_incl; [|exact Hoff1].
             apply (CALLS.moved_by_suffix_local env st st1 st' Hf0).
          -- eapply agree_off_incl; [|exact Hoff2]. exact Hincx.
        * apply listSatisfiable_app. split; [exact Hce2|].
          eapply listSatisfiable_off_scope
            with (sc := bound ++ CALLS.moved_by env st1 st')
                 (xs := CALLS.sec_of env [x]); eauto.
        * constructor.
          -- exact Hhead.
          -- eapply stream_rel_off_scope
               with (scope := bound ++ CALLS.moved_by env st1 st')
                    (moved := CALLS.sec_of env [x]);
               [| | |exact Hsepx|exact Hoff2|exact Hrel1].
             ++ eapply Forall_impl; [|exact Hambscr].
                intros q Hq. eapply st_scoped_weaken;
                  [apply incl_appl, incl_refl|exact Hq].
             ++ eapply Forall_impl; [|exact Hsc1t].
                intros q Hq. eapply st_scoped_weaken;
                  [apply incl_appl, incl_refl|exact Hq].
             ++ exact Hsc2t.
        * apply Forall_app. split.
          -- eapply Forall_impl; [|exact Hscope2].
             intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
             apply incl_app;
               [|eapply incl_tran; [exact Hincx|apply incl_appr, incl_refl]].
             apply incl_app; [apply incl_appl, incl_refl|].
             apply incl_appr, (CALLS.moved_by_suffix_local env st st1 st' Hf0).
          -- eapply Forall_impl; [|exact Hscope1].
             intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
             apply incl_app; [apply incl_appl, incl_refl|].
             apply incl_appr, (CALLS.moved_by_suffix_local env st st1 st' Hf0).
        * constructor.
          -- intros c Hc. destruct Hc as [|[]]; subst.
             apply in_or_app. right. apply Hincx.
             unfold CALLS.sec_of. cbn. rewrite Hb. now left.
          -- eapply Forall_impl; [|exact Hsc2t].
             intros q Hq. eapply st_scoped_weaken; [|exact Hq].
             apply incl_app; [apply incl_appl, incl_refl|].
             apply incl_appr, (CALLS.moved_by_suffix_local env st st1 st' Hf0).
  Qed.

  Section ExpressionContract.

    Variable vars  : list (ident * clock).
    Variable scope : list ident.

    (** The checkmark bound.  The non-call constructors never look at it; the
        call case cannot do without it, because the scoping facts about the
        source generator hold only for runs that finish before it. *)
    Variable stLo     : sec_state.
    Variable stF   : sec_state.
    Variable AN : list ident.


    (** The facts about the source generator that only the call case reads.
        They are declared here rather than pushed onto the call lemma's
        statement so that the expression induction quotes them once; the twelve
        other constructors do not mention them and are not generalised over
        them. *)

    Hypothesis sig_good :
      forall f sg, find_signature f GL = Some sg -> signature_good sg.

    Hypothesis sig_nodup :
      forall f sg, find_signature f GL = Some sg -> NoDup (signature_scope sg).

    Hypothesis sig_scoped :
      forall f sg, find_signature f GL = Some sg -> signature_scoped sg.

    Hypothesis sig_actuals_fresh :
      forall f sg inp ck rst os cns sa sb,
        find_signature f GL = Some sg ->
        Forall (caller_st env scope) inp ->
        caller_st env scope ck ->
        caller_st env scope rst ->
        Forall (caller_name env scope) os ->
        generate_constraints sg inp ck rst os sa = OK (cns, sb) ->
        call_subst_fresh sg inp ck rst os.

    Hypothesis source_types_scoped :
      CALLS.source_types_scoped_upto GL env base_ty rst_ty vars scope stLo stF.

    Hypothesis source_lexps_scoped :
      CALLS.source_lexps_scoped_upto GL env base_ty rst_ty vars scope stLo stF.

    Hypothesis source_lexps_carried_scoped :
      CALLS.source_lexps_carried_scoped_upto GL env base_ty rst_ty vars scope stLo stF.

    Hypothesis rst_ty_scoped : In rst_ty scope.

    Hypothesis clk_types_scoped :
      forall P es ck ckty,
        wc_global P ->
        Forall (wc_exp P vars) es ->
        Forall (nested_src vars AN) es ->
        (clk_src vars es ck \/
         exists x, In x (List.map fst vars) /\ find_clock cenv x = OK ck) ->
        assign_clk_type env base_ty ck = Some ckty -> st_scoped scope ckty.

    Hypothesis env_range_scoped :
      forall x b, In x (List.map fst vars) ->
                  Env.find x env = Some b -> In b scope.

    (** The clocks the argument ambients are built from have types.  Every
        declared variable has a security name; a source call's arguments are
        clocked over the declared variables ([src_exp]), so their clocks are
        typed. *)
    Hypothesis env_total :
      forall x ck, In (x, ck) vars -> exists b, Env.find x env = Some b.

    (** A nested call's output names are the node's anonymous streams, which
        the naming pass never put in the environment. *)
    Hypothesis env_anon :
      forall w b, Env.find w env = Some b -> ~ In w AN.

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
        src_exp vars AN e ->
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
        sec_le sst' stF -> sec_le stLo sst ->
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
        _ _ _ _ _ _ Htsc _ _ Hlen _ Hun Has Hgen Has' _ _ _.
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
        _ _ _ _ _ _ Htsc _ _ Hlen _ Hun Has Hgen Has' _ _ _.
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm vars AN _ _ (imm_Eunop op e a) Hsx) as Hsrc1.
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
           H2 H1 Hsrc1 Hnd Hmv Hcsc Htsc Hambsc Hcovered1 Hlen Hfound
           Hun Has Hgen Has1' Hsat Hbnd Hlow).
    Qed.

    Lemma carries_Ebinop_streams :
      forall P op e1 e2 a,
        carries_streams P e1 ->
        carries_streams P e2 ->
        carries_streams P (Ebinop op e1 e2 a).
    Proof.
      intros P op e1 e2 a IH1 IH2 is_control
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm vars AN _ _ (imm_Ebinop_l op e1 e2 a) Hsx)
        as Hs1.
      pose proof (src_exp_imm vars AN _ _ (imm_Ebinop_r op e1 e2 a) Hsx)
        as Hs2.
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
           H4 H3 Hs1 Hnd1 Hmv1
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc1 Hcar1)
           Ha1scs Hambscs
           Hcovered1 (@Coq.Init.Logic.eq_refl nat 1) Hfound1
           Hun1 Ht1 Hgen1 Hu1'
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat1 Hcar1)
           ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H5 H8 Hs2 Hnd2 Hmv2
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc2 Hcar2)
           Ha2scs Hambscs
           Hcovered2 (@Coq.Init.Logic.eq_refl nat 1) Hfound
           Hun2 Ht2 Hgen2 Hu2' Hsat2' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Forall (src_exp vars AN) es ->
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
        sec_le sst' stF -> sec_le stLo sst ->
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
          Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
          Hun Has Hgen Has' Hsat Hbnd Hlow.
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
        inversion Hsx as [|e0' es0' Hsrce Hsrces]; subst.
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
             Hwle Hwce Hsrce Hnd1 Hmv1 Hcsc1 Htsc1 Hambsc1 Hcovered1
             Hambs1len Hfound1 Hun1 Ht Hgen1 Hu Hsat1
             ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
             Hwles Hwces Hsrces Hnd2 Hmv2 Hcsc2 Htsc2 Hambsc2 Hcovered2
             Hambs2len Hfound Hunr Hr Hgen2 Hv Hsat2' Hbnd
             ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 10 with sec))
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

    (** * The call's arguments, at the ambients the call hands them

        The argument at a given slot runs on the formal's clock instantiated
        at the call's base, so the ambient that covers it is the call's own
        joined with that slot's clock actuals -- [call_arg_ambient], the same
        set the augmentation uses.  [clocks_covered_call_args] assembles those
        into the list the contract wants, and this wires it to
        [carries_list_streams_intro] so the call case can quote one lemma
        instead of redoing the plumbing.

        The length side condition is [call_arg_ambients_length] together with
        the source types having one entry per argument stream. *)
    Lemma call_args_streams :
      forall P es (ins : list (ident * clock)) bck sub bckty
             ic es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt,
        Forall (carries_streams P) es ->
        assign_clk_type env base_ty bck = Some bckty ->
        Forall2 (WellInstantiated bck sub) ins (nclocksof es) ->
        (forall nck, In nck (nclocksof es) ->
           exists ckty, assign_clk_type env base_ty (stripname nck)
                        = Some ckty) ->
        Forall (wl_exp P) es ->
        Forall (wc_exp P vars) es ->
        Forall (src_exp vars AN) es ->
        NoDup (vars_defined (List.concat eqs) ++ st_ids st) ->
        (forall x, In x (CALLS.moved_by env st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        stream_ambients_scoped scope
          (call_arg_ambients sub bckty (nclocksof es) ins) ->
        List.length ts = List.length (nclocksof es) ->
        state_clocks_found st' ->
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.concat eqs) xst = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty (List.concat es') yst
          = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        sec_le sst' stF -> sec_le stLo sst ->
        exists dlt',
          carries_result_streams scope (CALLS.moved_by env st st')
            (call_arg_ambients sub bckty (nclocksof es) ins) ts ts'' ce dlt dlt'.
    Proof.
      intros P es ins bck sub bckty ic es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt
        Hall Hbk Hwi Hdef Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      eapply (carries_list_streams_intro P es Hall ic
                (call_arg_ambients sub bckty (nclocksof es) ins));
        [exact Hwl|exact Hwc|exact Hsx|exact Hnd|exact Hmv|exact Hcsc|exact Htsc
        |exact Hambsc| | |exact Hfound|exact Hun|exact Has|exact Hgen
        |exact Has'|exact Hsat|exact Hbnd|exact Hlow].
      - (** the arguments' clocks are the instantiated formals' *)
        rewrite clocksof_nclocksof.
        exact (clocks_covered_call_args bck sub ins (nclocksof es) bckty
                 Hbk Hwi Hdef).
      - (** one ambient per argument stream *)
        rewrite (call_arg_ambients_length sub bckty (nclocksof es) ins
                   (Forall2_length _ _ _ Hwi)).
        exact (@Coq.Init.Logic.eq_sym _ _ _ Hlen).
    Qed.

    Lemma carries_Ewhen_streams :
      forall P es x b a,
        Forall (carries_streams P) es ->
        carries_streams P (Ewhen es x b a).
    Proof.
      intros P es x b [tys ck] Hall is_control
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm_forall vars AN es (Ewhen es x b (tys, ck))
                    (fun e' He' => imm_Ewhen es x b (tys, ck) e' He') Hsx)
        as Hsrces.
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
           H2 H4 Hsrces Hnd Hmv Hcsc Htes_scoped Hambsc Hcovered_es Hlen_tes
           Hfound Hmap Htes Hgen Htes'' Hsat
           ltac:(rewrite <- Hstate; exact Hbnd) Hlow)
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm_forall vars AN es1 (Emerge ckid es1 es2 (tys, cl))
                    (fun e' He' => imm_Emerge_t ckid es1 es2 (tys, cl) e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es2 (Emerge ckid es1 es2 (tys, cl))
                    (fun e' He' => imm_Emerge_f ckid es1 es2 (tys, cl) e' He') Hsx)
        as Hsrc2.
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
           H4 H5 Hsrc1 Hnd1 Hmv1 Hcsc1 Htsc1 Hon_scoped Hcovered1 Hon_len1
           Hfound1 Hun1 Htes1 Hgen1 Htes1'' Hsat1 ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H6 H9 Hsrc2 Hnd2 Hmv2 Hcsc2 Htsc2 Hon_scoped Hcovered2 Hon_len2
           Hfound Hun2 Htes2 Hgen2 Htes2'' Hsat2' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm vars AN e0 (Eite e0 es1 es2 (tys, ck))
                    (imm_Eite_c e0 es1 es2 (tys, ck)) Hsx) as Hsrc0.
      pose proof (src_exp_imm_forall vars AN es1 (Eite e0 es1 es2 (tys, ck))
                    (fun e' He' => imm_Eite_t e0 es1 es2 (tys, ck) e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es2 (Eite e0 es1 es2 (tys, ck))
                    (fun e' He' => imm_Eite_f e0 es1 es2 (tys, ck) e' He') Hsx)
        as Hsrc2.
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
           H4 H5 Hsrc0 Hnd0a Hmv0
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc0
              (CALLS.carried_single th))
           Hth_scopeds Hclock_amb_scopeds He0_covered
           (@Coq.Init.Logic.eq_refl nat 1) Hfound0
           Hun0 Ht0 Hgen0 Hth_target
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat0
              (CALLS.carried_single th))
              ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H6 H11 Hsrc1 Hnd1 Hmv1 Hcsc1 Htsc1
           Hambsc Hbranch_covered1 Hbranch_len1
           Hfound1 Hun1 Htes1 Hgen1 Htes1'' Hsat1' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H7 H12 Hsrc2 Hnd2 Hmv2 Hcsc2 Htsc2
           Hambsc Hbranch_covered2 Hbranch_len2
           Hfound Hun2 Htes2 Hgen2 Htes2'' Hsat2' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm_forall vars AN es1 (Emerge ckid es1 es2 (tys, cl))
                    (fun e' He' => imm_Emerge_t ckid es1 es2 (tys, cl) e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es2 (Emerge ckid es1 es2 (tys, cl))
                    (fun e' He' => imm_Emerge_f ckid es1 es2 (tys, cl) e' He') Hsx)
        as Hsrc2.
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
           H4 H5 Hsrc1 Hnd1 Hmv1 Hcsc1 Htsc1 Hon_scoped Hcovered1 Hon_len1
           Hfound1 Hun1 Htes1 Hgen1 Ht1y Hsat1 ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H6 H9 Hsrc2 Hnd2 Hmv2 Hcsc2 Htsc2 Hon_scoped Hcovered2 Hon_len2
           Hfound2 Hun2 Htes2 Hgen2 Ht2y Hsat2' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm vars AN e0 (Eite e0 es1 es2 (tys, ck))
                    (imm_Eite_c e0 es1 es2 (tys, ck)) Hsx) as Hsrc0.
      pose proof (src_exp_imm_forall vars AN es1 (Eite e0 es1 es2 (tys, ck))
                    (fun e' He' => imm_Eite_t e0 es1 es2 (tys, ck) e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es2 (Eite e0 es1 es2 (tys, ck))
                    (fun e' He' => imm_Eite_f e0 es1 es2 (tys, ck) e' He') Hsx)
        as Hsrc2.
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
           H4 H5 Hsrc0 Hnd0a Hmv0
           (eq_ind_r (fun cs => constraints_scoped scope cs) Hcsc0
              (CALLS.carried_single th))
           Hth_scopeds Hclock_amb_scopeds He0_covered
           (@Coq.Init.Logic.eq_refl nat 1) Hfound0
           Hun0 Ht0 Hgen0 Hth_target
           (eq_ind_r (fun cs => listSatisfiable dlt cs) Hsat0
              (CALLS.carried_single th))
              ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H6 H11 Hsrc1 Hnd1 Hmv1 Hcsc1 Htsc1
           Hambsc Hbranch_covered1 Hbranch_len1
           Hfound1 Hun1 Htes1 Hgen1 Ht1y Hsat1' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H7 H12 Hsrc2 Hnd2 Hmv2 Hcsc2 Htsc2
           Hambsc Hbranch_covered2 Hbranch_len2
           Hfound2 Hun2 Htes2 Hgen2 Ht2y Hsat2' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm_forall vars AN e0s (Efby e0s es anns)
                    (fun e' He' => imm_Efby_0 e0s es anns e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es (Efby e0s es anns)
                    (fun e' He' => imm_Efby_1 e0s es anns e' He') Hsx)
        as Hsrc2.
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
           H2 H3 Hsrc1 Hnd1 Hmv1 Hcsc0 Htsc0 Hambsc Hcov0 Hlen0
           Hfound1 Hmap0 Hts0 Hgen1 Ht0y Hsat0 ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H4 H7 Hsrc2 Hnd2 Hmv2 Hcsc1 Htsc1 Hambsc Hcov1 Hlen1
           Hfound2 Hmap1 Hus Hgen2 Huy Hsat1' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
        Hwl Hwc Hsx Hnd Hmv Hcsc Htsc Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hsat Hbnd Hlow.
      pose proof (src_exp_imm_forall vars AN e0s (Earrow e0s es anns)
                    (fun e' He' => imm_Earrow_0 e0s es anns e' He') Hsx)
        as Hsrc1.
      pose proof (src_exp_imm_forall vars AN es (Earrow e0s es anns)
                    (fun e' He' => imm_Earrow_1 e0s es anns e' He') Hsx)
        as Hsrc2.
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
           H2 H3 Hsrc1 Hnd1 Hmv1 Hcsc0 Htsc0 Hambsc Hcov0 Hlen0
           Hfound1 Hmap0 Hts0 Hgen1 Ht0y Hsat0 ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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
           H4 H7 Hsrc2 Hnd2 Hmv2 Hcsc1 Htsc1 Hambsc Hcov1 Hlen1
           Hfound2 Hmap1 Hus Hgen2 Huy Hsat1' ltac:(eauto 4 with sec)
           ltac:(eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec))
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



    (** * The call, pointwise

        The four joints are quotations: [call_args_streams] for the arguments,
        [noops_step_streams] for the no-op pass, [call_args_augmented] to turn
        the per-slot relation into the premise
        [generate_constraints_mono_sem_aug] asks for, and
        [call_results_stream_rel] to read the results back at their own
        ambients.  The reset needs nothing new: run [reset_step] at the call's
        ambient joined with the reset's clock type, and its conclusion collapses
        to what the transfer wants, because the reset's source type already
        contains that clock type. *)
    (** * The reset of a call, per stream

        The scalar [reset_step] cannot be reused.  Its ambient premise is a
        containment for *every* variable the reset's unnesting lifts, and the
        streams contract has no such premise -- by design, since that is the
        premise the pointwise relation exists to avoid.  What replaces it is
        the same pair the rest of the streams development uses: the reset
        expression has one stream, so one ambient covers it
        ([clocks_covered]), and the variable [unnest_reset] binds it to carries
        that same stream's clock, which [state_clocks_found] reads back.

        Everything else transfers from the scalar proof verbatim, because the
        reset is a one-stream expression and a one-element [stream_rel] is a
        scalar relation. *)

    Lemma reset_step_streams :
      forall (P : global) e1 r an rty eqs3 st st' a1 sst sst' ce xst xst'
             (yst : sec_state) amb dlt,
        carries_streams P e1 ->
        st_scoped scope amb ->
        clocks_covered (clockof e1) [amb] ->
        state_clocks_found st' ->
        wl_exp P e1 -> wc_exp P vars e1 -> src_exp vars AN e1 ->
        numstreams e1 = 1 ->
        unnest_reset (unnest_exp P true) (Some e1) st
          = ((Some (Evar r an), eqs3), st') ->
        Env.find r env = Some rty ->
        NoDup (vars_defined eqs3 ++ st_ids st) ->
        (forall x, In x (CALLS.moved_by env st st') -> ~ In x scope) ->
        assign_lexp_type GL env base_ty rst_ty e1 sst = OK ([a1], sst') ->
        constraints_scoped scope (carried [a1]) ->
        st_scoped scope (fst a1) ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs3 xst
          = OK (ce, xst') ->
        listSatisfiable dlt (carried [a1]) ->
        sec_le sst' stF -> sec_le stLo sst ->
        exists dlt',
          agree_off (CALLS.moved_by env st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ satisfiable dlt' [rty] (merge amb (fst a1))
          /\ In rty (scope ++ CALLS.moved_by env st st')
          /\ constraints_scoped (scope ++ CALLS.moved_by env st st') ce.
    Proof.
      intros P e1 r an rty eqs3 st st' a1 sst sst' ce xst xst' yst amb dlt
        Hcar Hambsc Hcov Hfound Hwl Hwc Hsx Hns Hun Hr Hnd Hmv Hty Hsc Hsct
        Hgen Hsat Hbnd Hlow.
      pose proof Hun as Hun0.
      destruct (unnest_exp P true e1 st) as [[es' eqs1] st1] eqn:Hk.
      pose proof Hk as Hk0.
      eapply unnest_reset_spec in Hk
        as [(v & a & Ehd & Hnorm)
           |(ty0 & ck0 & o0 & x & st2 & Hhd & Hfresh & Hnorm)];
        rewrite Hnorm in Hun0; inv Hun0.

      - (** kept: the unnested reset is already a variable *)
        assert (List.length es' = 1) as Hlen
            by (erewrite unnest_exp_length; eauto).
        destruct es' as [|e0 [|]]; simpl in Hlen; try discriminate.
        simpl in Ehd. subst e0.
        assert (assign_lexps GL env base_ty rst_ty [Evar r an] yst
                  = OK ([(([rty] : ST), [])], yst)) as Hasr.
        { apply assign_lexps_single_intro.
          simpl. unfold find_env. rewrite Hr. reflexivity. }
        assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hsts
            by (constructor; [exact Hsct|constructor]).
        assert (stream_ambients_scoped scope [amb]) as Hamb1
            by (constructor; [exact Hambsc|constructor]).
        pose proof (Hcar true [amb] [Evar r an] eqs3 st st' [a1] sst sst'
                      ce xst xst' [(([rty] : ST), [])] yst yst dlt
                      Hwl Hwc Hsx Hnd Hmv Hsc Hsts Hamb1 Hcov
                      ltac:(reflexivity) Hfound Hk0 Hty Hgen Hasr Hsat Hbnd Hlow)
          as Hres.
        destruct Hres as (dlt' & Hoff & Hce & Hrel & Hscope & Hts).
        exists dlt'. split; [exact Hoff|split; [exact Hce|split]].
        + inversion Hrel as [|p q w ps qs ws Hpq _]; subst. exact Hpq.
        + split; [|exact Hscope].
          inversion Hts as [|z zs Hz _]; subst. apply Hz. now left.

      - (** bound: one more variable, and [lifted_defs_streams] on it *)
        assert (List.length es' = 1) as Hlen
            by (erewrite unnest_exp_length; eauto).
        destruct es' as [|e0 [|]]; simpl in Hlen; try discriminate.
        simpl hd_default in *.
        assert (normalized_cexp e0) as Hne0.
        { assert (Forall normalized_cexp [e0]) as Hall
              by (eapply unnest_exp_normalized_cexp; eauto).
          now inv Hall. }
        assert (st_follows st st1) as Hf0
            by (eapply unnest_exp_st_follows; eauto).
        assert (st_follows st1 st') as Hf1
            by (eapply UNN.Fresh.fresh_ident_st_follows; eauto).
        assert (Permutation (r :: st_ids st1) (st_ids st')) as Hpx
            by (eapply UNN.Fresh.Facts.fresh_ident_vars_perm; eauto).
        assert (state_clocks_found st1) as Hfound1
            by (exact (state_clocks_found_prefix st1 st' Hf1 Hfound)).

        (** the ambient the lifted variable is read at: its own stream's,
            which is the reset expression's only stream *)
        assert (declared_ambients [r] [amb]) as Hdecl.
        { constructor; [|constructor]. intros ck Hck.
          assert (find_clock cenv r = OK ck0) as Hck0
              by (exact (Hfound r (ty0, ck0)
                           (UNN.Fresh.Facts.fresh_ident_In
                              _ _ _ _ _ Hfresh))).
          rewrite Hck0 in Hck. inversion Hck; subst ck.
          assert (LSyn.clockof e1 = [ck0]) as Hcl
              by (eapply unnest_reset_ann_clock; eauto).
          unfold clocks_covered in Hcov. rewrite Hcl in Hcov.
          inversion Hcov as [|c0 a0 cs0 as0 Hca _]; subst. exact Hca. }

        (** the emitted equations: the binding, then the reset's own *)
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (ceh & xstm & Hgenh & Hgen).
        eapply sec_bind_inv in Hgen as (cet & xstn & Hgent & Hret).
        unfold SC.ret in Hret. inv Hret.
        pose proof Hgenh as Hgenh0.
        rewrite generate_leqn_constraint_def in Hgenh0
          by (destruct e0; try exact I; inv Hne0; inv H).
        apply generate_ldef_constraint_inv in Hgenh0
          as (ck1 & ckty1 & sa & rb & stm2 & Hck1 & Hcl1 & Hte0 & Hb & Hceh).
        assert (carried [sa] = [] /\ forall s,
                   assign_lexp_type GL env base_ty rst_ty e0 s = OK ([sa], s))
          as (Hsnd & Hpure).
        { eapply assign_lexp_normalized_cexp_pure in Hte0
            as (? & _ & Hcr & Hs); eauto. }

        assert (NoDup (vars_defined eqs1 ++ st_ids st)) as Hnd1
            by (simpl in Hnd; now inv Hnd).
        edestruct (Hcar true [amb] [e0] eqs1 st st1 [a1] sst sst'
                     cet xstm xst' [sa] yst yst dlt)
          as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
        { exact Hwl. }
        { exact Hwc. }
        { exact Hsx. }
        { exact Hnd1. }
        { intros y Hy. apply Hmv.
          apply (CALLS.moved_by_prefix_local env st st1 st' Hf1). exact Hy. }
        { exact Hsc. }
        { constructor; [exact Hsct|constructor]. }
        { constructor; [exact Hambsc|constructor]. }
        { exact Hcov. }
        { reflexivity. }
        { exact Hfound1. }
        { exact Hk0. }
        { exact Hty. }
        { exact Hgent. }
        { apply assign_lexps_single_intro. apply (Hpure yst). }
        { exact Hsat. }
        { exact Hbnd. }
        { first [exact Hlow | (eapply sec_le_trans; [exact Hlow|]; eauto 6 with sec)]. }

        assert (satisfiable dlt1 (fst sa) (merge amb (fst a1))) as Hsa
            by (inversion Hrel1 as [|p q w ps qs ws Hpq _]; subst; exact Hpq).
        assert (st_scoped (scope ++ CALLS.moved_by env st st1) (fst sa))
          as Hsasc
            by (inversion Hts1 as [|z zs Hz _]; subst; exact Hz).

        (** the variable the reset was bound to *)
        assert (Permutation (vars_defined eqs1 ++ st_ids st) (st_ids st1))
          as Hp1 by (eapply unnest_exp_vars_perm; eauto).
        assert (~ In r (st_ids st1)) as Hrst.
        { simpl in Hnd. inversion Hnd as [|z zs Hzn _]; subst.
          intro Hc. apply Hzn.
          eapply Permutation_in; [symmetry; exact Hp1|exact Hc]. }
        assert (In r (new_ids st1 st')) as Hrnew.
        { apply new_ids_spec. split; [|exact Hrst].
          eapply Permutation_in; [exact Hpx|now left]. }
        assert (In rty (CALLS.moved_by env st1 st')) as Hrtymv.
        { unfold CALLS.moved_by, CALLS.sec_of. apply in_flat_map.
          exists r. split; [exact Hrnew|]. rewrite Hr. now left. }
        assert (forall c, In c (sec_of [r]) ->
                          In c (CALLS.moved_by env st1 st')) as Hbnew.
        { intros c Hc. unfold CALLS.sec_of in Hc. simpl in Hc.
          rewrite Hr in Hc. destruct Hc as [|[]]; subst. exact Hrtymv. }
        assert (forall c, In c (sec_of [r]) ->
                          ~ In c (scope ++ CALLS.moved_by env st st1))
          as Hsepx.
        { intros c Hc Hin. apply Hbnew in Hc.
          apply in_app_or in Hin as [Hin|Hin].
          - eapply (Hmv c); [|exact Hin].
            apply (CALLS.moved_by_suffix_local env st st1 st' Hf0). exact Hc.
          - exact (CALLS.moved_by_disjoint_local env env_inj st st1 st' c
                     Hin Hc). }

        edestruct (lifted_defs_streams (scope ++ CALLS.moved_by env st st1)
                     [r] [e0] [sa] [amb] ceh xst xstm dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hscope2 & Hrel2).
        { constructor; [intros []|constructor]. }
        { reflexivity. }
        { exact Hsepx. }
        { exact Hdecl. }
        { constructor; [|constructor].
          eapply st_scoped_weaken;
            [apply incl_appl, incl_refl|exact Hambsc]. }
        { constructor; [|constructor]. split.
          - destruct e0; try exact I; inv Hne0; inv H.
          - intros tf s s' Htf. rewrite (Hpure s) in Htf. inv Htf.
            split; [reflexivity|split; [reflexivity|exact Hsnd]]. }
        { constructor; [|constructor]. exact Hsasc. }
        { constructor; [|constructor]. intros tf s s' Htf.
          rewrite (Hpure s) in Htf. inv Htf.
          split; [apply satisfiable_merge_r|exact Hsasc]. }
        { assert (generate_leqns_constraints GL env base_ty rst_ty cenv
                    [([r], [e0])] xst = OK (ceh, xstm)) as Hgenh1.
          { rewrite generate_leqns_constraints_cons.
            eapply sec_bind_ok; [exact Hgenh|].
            eapply sec_bind_ok with (y := ([] : list SymTypes.constraint));
              [reflexivity|].
            unfold SC.ret. now rewrite app_nil_r. }
          exact Hgenh1. }

        assert (satisfiable dlt2 [rty] (merge amb (fst sa))) as Hhead.
        { inversion Hrel2 as [|p q w ps qs ws Hpq _]; subst. now apply Hpq. }
        assert (incl (sec_of [r]) (CALLS.moved_by env st st')) as Hincx
            by (intros c Hc;
                apply (CALLS.moved_by_suffix_local env st st1 st' Hf0);
                now apply Hbnew).

        exists dlt2. split; [|split; [|split; [|split]]].
        + eapply CALLS.agree_off_trans.
          * eapply CALLS.agree_off_incl; [|exact Hoff1].
            apply (CALLS.moved_by_prefix_local env st st1 st' Hf1).
          * eapply CALLS.agree_off_incl; [|exact Hoff2]. exact Hincx.
        + apply listSatisfiable_app. split; [exact Hce2|].
          eapply CALLS.listSatisfiable_off_scope
            with (sc := scope ++ CALLS.moved_by env st st1)
                 (xs := sec_of [r]); eauto.
        + eapply satisfiable_trans; [exact Hhead|].
          apply satisfiable_merge_intro; [apply satisfiable_merge_l|].
          eapply CALLS.satisfiable_off with (xs := sec_of [r]); eauto.
          * intros c Hc Hin. apply (Hsepx c Hin). now apply Hsasc.
          * intros c Hc Hin. apply in_merge_inv in Hc as [Hc|Hc].
            -- apply (Hsepx c Hin). apply in_or_app. left.
               now apply Hambsc.
            -- apply (Hsepx c Hin). apply in_or_app. left. now apply Hsct.
        + apply in_or_app. right. apply Hincx.
          unfold CALLS.sec_of. simpl. rewrite Hr. now left.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope2].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app;
              [|eapply incl_tran; [exact Hincx|apply incl_appr, incl_refl]].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr,
              (CALLS.moved_by_prefix_local env st st1 st' Hf1).
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr,
              (CALLS.moved_by_prefix_local env st st1 st' Hf1).
    Qed.

    Lemma carries_Eapp_streams :
      forall P ic f es er anns,
        (** the callee's own clocking is what makes the call's base clock the
            common parent of its arguments' *)
        wc_global P ->
        (** and the two program-level facts about the callee's signature that
            the augmented instantiation reads *)
        CALLS.sig_inputs_ok GL P ->
        Forall (carries_streams P) es ->
        (forall e1, er = Some e1 -> carries_streams P e1) ->
        carries_at_streams P ic (Eapp f es er anns).
    Proof.
      intros P ic f es er anns Hwcg Hsigin Halls Hallr
        ambs es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hsx Hnd Hmv Hsc Hsts Hambsc Hcovered Hlen Hfound
        Hun Has Hgen Has' Hcar Hbnd Hlow.
      pose proof Hwl as Hwl0. pose proof Hwc as Hwc0.
      assert (anns <> []) as Hanne.
      { intro Hc. subst anns. inv Hwl0;
          match goal with H : _ = List.length (n_out ?nn) |- _ =>
            pose proof (n_outgt0 nn); simpl in H; lia end. }
      assert (Forall (wl_exp P) es) as Hwles by (inv Hwl0; assumption).
      assert (Forall (wc_exp P vars) es) as Hwces by (inv Hwc0; assumption).
      assert (Forall (src_exp vars AN) es) as Hsrces
        by (eapply src_exp_imm_forall; [|exact Hsx];
            intros e' He'; exact (imm_Eapp_arg f es er anns e' He')).
      destruct (src_exp_loc vars AN _ Hsx) as (Hanon & Hargcl).
      cbn in Hargcl.
      assert (Forall (nested_src vars AN) es) as Hnsrces
        by (eapply nested_src_args; exact Hsx).

      (** the clocking data the ambients are built from *)
      assert (exists nd bck sub,
                 find_node f P = Some nd
                 /\ Forall2 (WellInstantiated bck sub)
                      (idck nd.(n_in)) (nclocksof es)
                 /\ Forall2 (WellInstantiated bck sub)
                      (idck nd.(n_out)) (List.map snd anns))
        as (nd & bck & sub & Hfn & Hwi & Hwo)
          by (inv Hwc0; repeat esplit; eauto).

      (** the two sides, taken apart *)
      pose proof Hun as Hun0.
      apply CALLS.unnest_exp_Eapp_inv in Hun
        as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er2 & eqs3 & st3 & xs
            & Hune & Hunn & Hunr & Hids & ? & ?); subst.
      pose proof Hune as Hune0.
      apply CALLS.unnest_exps_inv in Hune as (ess & eqss & Hmap & ? & ?); subst.
      pose proof Has as Has0.
      apply assign_lexp_Eapp_inv in Has
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & Hargs & Hck & Hrst & Esg & Houts & Hcs & Hts).
      apply CALLS.assign_lexps_evars in Has' as (? & Hevars); subst.

      (** the call's own ambient, and that it sits inside every result's *)
      assert (assign_clk_type env base_ty bck = Some ckty) as Hbckty.
      { assert (find_base_clock (LSyn.clocksof es) = bck) as Hfb
            by (exact (wc_exp_Eapp_base_clock P nd f es bck sub
                         Hwcg Hfn Hwi)).
        rewrite <- Hfb. exact Hck. }
      assert (clk_src vars es bck) as Hbcksrc.
      { assert (find_base_clock (LSyn.clocksof es) = bck) as Hfb'
            by (exact (wc_exp_Eapp_base_clock P nd f es bck sub
                         Hwcg Hfn Hwi)).
        rewrite <- Hfb'. apply clk_src_base. }
      assert (wc_env (idck nd.(n_in))) as Hwcin
          by (destruct (wc_find_node P f nd Hwcg Hfn) as (G' & (Wcin & _));
              exact Wcin).
      assert (Forall (fun a => incl (merge [rst_ty] ckty) a) ambs) as Hbelow.
      { eapply call_amb_below_result_ambients;
          [exact Hbckty
          |intros ck0 Hck0;
           exact (wc_Eapp_out_instck (idck nd.(n_out)) bck sub anns Hwo
                    ck0 Hck0)
          |exact Hcovered]. }

      (** the states the run passed through *)
      assert (st_follows st st1) as Hfa
          by (eapply CALLS.map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st2) as Hfb
          by (eapply unnest_noops_exps_st_follows; eauto).
      assert (st_follows st2 st3) as Hfc
          by (eapply unnest_reset_st_follows; eauto).
      assert (st_follows st3 st') as Hfd
          by (eapply idents_for_anns'_st_follows; eauto).
      assert (st_follows st st2) as Hf02 by (etransitivity; eauto).
      assert (st_follows st st3) as Hf03 by (etransitivity; eauto).
      assert (st_follows st1 st3) as Hf13 by (etransitivity; eauto).
      assert (st_follows st1 st') as Hf1' by (etransitivity; eauto).
      assert (st_follows st2 st') as Hf2' by (etransitivity; eauto).

      (** the state clocks, read back at each stage *)
      assert (state_clocks_found st3) as Hfound3
          by (exact (state_clocks_found_prefix st3 st' Hfd Hfound)).
      assert (state_clocks_found st2) as Hfound2
          by (exact (state_clocks_found_prefix st2 st3 Hfc Hfound3)).
      assert (state_clocks_found st1) as Hfound1
          by (exact (state_clocks_found_prefix st1 st2 Hfb Hfound2)).

      (** the same, on the security monad *)
      pose proof (CALLS.assign_lexp_Eapp_stages_le GL env base_ty rst_ty
                    es er anns sst sst' sg argts rstty ckty outs cs
                    sta stb stc Hargs Hrst Houts Hcs) as (Hlab & Hlbc & Hlcs).
      assert (sec_le stc stF) as Hbstc
          by exact (CALLS.sec_le_trans _ _ _ Hlcs Hbnd).
      assert (sec_le stb stF) as Hbstb
          by exact (CALLS.sec_le_trans _ _ _ Hlbc Hbstc).
      assert (sec_le sta stF) as Hbsta
          by exact (CALLS.sec_le_trans _ _ _ Hlab Hbstb).
      assert (sec_le stLo sta) as Hlsa
          by (eapply sec_le_trans; [exact Hlow|]; eapply assign_lexps_sec_le;
              exact Hargs).

      (** the emitted constraints, equation by equation *)
      rewrite generate_leqns_constraints_cons in Hgen.
      eapply sec_bind_inv in Hgen as (ce0 & xsta & Hgen0 & Hgen).
      eapply sec_bind_inv in Hgen as (cer & xstb & Hgenr & Hret).
      unfold SC.ret in Hret. inv Hret.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & cerr & xstc & Hgen1 & Hgenrr & ?); subst.
      apply generate_leqns_constraints_app in Hgenrr
        as (ce2 & ce3 & xstd & Hgen2 & Hgen3 & ?); subst.

      (** what the run defines, split between its four stages *)
      assert (vars_defined
                ((List.map fst xs, [Eapp f es2 er2 (List.map snd xs)])
                   :: (List.concat eqss ++ eqs2 ++ eqs3))
              = List.map fst xs
                ++ vars_defined (List.concat eqss ++ eqs2 ++ eqs3)) as Hvd
          by reflexivity.
      rewrite Hvd in Hnd.
      rewrite <- app_assoc in Hnd.
      assert (NoDup (vars_defined (List.concat eqss ++ eqs2 ++ eqs3)
                       ++ st_ids st)) as Hndr
          by (eapply NoDup_app_r; exact Hnd).
      assert (Permutation (vars_defined (List.concat eqss) ++ st_ids st)
                (st_ids st1)) as Hp1
          by (eapply CALLS.map_bind2_unnest_vars_perm; eauto).
      assert (Permutation (vars_defined eqs2 ++ st_ids st1) (st_ids st2))
        as Hp2 by (eapply unnest_noops_exps_vars_perm; eauto).
      assert (Permutation (vars_defined eqs3 ++ st_ids st2) (st_ids st3))
        as Hp3.
      { assert (LiftO True
                  (fun e => forall es'0 eqs'0 st0 st'0,
                       unnest_exp P true e st0 = ((es'0, eqs'0), st'0) ->
                       Permutation (vars_defined eqs'0 ++ st_ids st0)
                         (st_ids st'0)) er) as Hlift.
        { destruct er as [e1|]; simpl; [|exact I].
          intros es'0 eqs'0 st0 st'0 Hkk.
          eapply unnest_exp_vars_perm; [|exact Hkk]. inv Hwl0; assumption. }
        eapply unnest_reset_vars_perm; [exact Hlift|exact Hunr]. }
      assert (NoDup (vars_defined (List.concat eqss) ++ st_ids st)) as Hnd1
          by (eapply CALLS.NoDup_vd_app_l; exact Hndr).
      assert (NoDup (vars_defined (eqs2 ++ eqs3) ++ st_ids st1)) as Hnd23
          by (eapply CALLS.NoDup_vd_app_r; [exact Hp1|exact Hndr]).
      assert (NoDup (vars_defined eqs2 ++ st_ids st1)) as Hnd2
          by (eapply CALLS.NoDup_vd_app_l; exact Hnd23).
      assert (NoDup (vars_defined eqs3 ++ st_ids st2)) as Hnd3
          by (eapply CALLS.NoDup_vd_app_r; [exact Hp2|exact Hnd23]).

      (** the call binds at least one result, so its equation reduces *)
      assert (List.length xs = List.length anns) as Hlxs
          by (eapply idents_for_anns'_length; eauto).
      assert (exists x0 xs0, List.map fst xs = x0 :: xs0)
        as (x0 & xs0 & Exs).
      { destruct xs as [|xa xsr]; [|simpl; eauto].
        exfalso. apply Hanne. simpl in Hlxs.
        destruct anns; [reflexivity|discriminate Hlxs]. }

      (** what the emitted call generates, whichever way its reset came out *)
      pose proof Hunr as Hunr1.
      assert (exists rstty' ckt argt outt sti cs0,
                 ((er = None /\ er2 = None /\ eqs3 = [] /\ st3 = st2
                   /\ rstty' = lvar rst_ty)
                  \/ (exists e1 r ty0 ckr nm rty rstck,
                        er = Some e1
                        /\ er2 = Some (Evar r (ty0, (ckr, nm)))
                        /\ Env.find r env = Some rty
                        /\ assign_clk_type env base_ty ckr = Some rstck
                        /\ rstty' = ljoin (lvar rst_ty)
                                      (merge [rty] rstck, [])))
                 /\ assign_clk_type env base_ty
                      (find_base_clock (LSyn.clocksof es2)) = Some ckt
                 /\ assign_lexps GL env base_ty rst_ty es2 xst = OK (argt, sti)
                 /\ SC.mmap (fun x => find_env x env) (x0 :: xs0) sti
                    = OK (outt, sti)
                 /\ generate_constraints sg (List.map fst argt) ckt
                      (fst rstty') outt sti = OK (cs0, xsta)
                 /\ ce0 = cmerge cs0 (cmerge (carried argt) (snd rstty')))
        as (rstty' & ckt & argt & outt & sti & cs0
            & Hshape & Hckt & Hargt & Houtt & Hgc & Hce0).
      { rewrite Exs in Hgen0.
        apply CALLS.unnest_reset_option_shape in Hunr1
          as [(Hern & Hn2 & ? & ?)|(e1 & rv & ran & Her & Hs2)]; subst.
        - rewrite gen_leqn_Eapp in Hgen0.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & sti & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (lvar rst_ty), ckt, argt, outt, sti, cs0.
          split;
            [left; repeat split; reflexivity
            |split; [exact Hckt|split; [exact Hargt
             |split; [exact Houtt|split; [exact Hgc|exact Hce0]]]]].
        - destruct ran as (ty0 & ckr0 & nm0).
          rewrite gen_leqn_Eapp_reset in Hgen0.
          eapply sec_bind_inv in Hgen0 as (rty & s1 & Hrty & Hgen0).
          apply find_env_inv in Hrty as (Hrty & ?); subst s1.
          eapply sec_bind_inv in Hgen0 as (rstck & s2 & Hrstck & Hgen0).
          apply option_to_sec_inv in Hrstck as (Hrstck & ?); subst s2.
          apply generate_lcall_constraint_inv in Hgen0
            as (sg' & ckt & argt & outt & sti & cs0
                & Esg' & Hckt & Hargt & Houtt & Hgc & Hce0).
          rewrite Esg in Esg'. inversion Esg'; subst sg'.
          exists (ljoin (lvar rst_ty) (merge [rty] rstck, [])),
                 ckt, argt, outt, sti, cs0.
          split;
            [|split; [exact Hckt|split; [exact Hargt
              |split; [exact Houtt|split; [exact Hgc|exact Hce0]]]]].
          right. exists e1, rv, ty0, ckr0, nm0, rty, rstck.
          repeat split; auto. }

      (** what the source expression carries, taken apart *)
      assert (outs <> []) as Houtsne.
      { intro Hc. apply Hanne. apply fresh_idents_length in Houts.
        rewrite Hc in Houts. simpl in Houts.
        destruct anns; [reflexivity|discriminate Houts]. }
      assert (match outs with
              | [] => ([] : list SymTypes.constraint)
              | _ => cmerge cs (cmerge (carried argts) (snd rstty))
              end = cmerge cs (cmerge (carried argts) (snd rstty))) as Hmt
          by (destruct outs; [now elim Houtsne|reflexivity]).
      rewrite carried_uniform, Hmt in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsccs & Hscr).
      apply constraints_scoped_cmerge in Hscr as (Hscarg & Hscrst).
      apply listSatisfiable_cmerge in Hcar as (Hcarcs & Hcarr).
      apply listSatisfiable_cmerge in Hcarr as (Hcararg & Hcarrst).
      assert (Forall (fun t => st_scoped scope (fst t)) argts) as Hscargts
          by (exact (source_lexps_scoped P es argts sst sta Hwces Hlow Hargs Hbsta)).

      (** the arguments, as the pass left them *)
      assert (Forall normalized_lexp (List.concat ess)) as Hnorm1
          by (eapply CALLS.map_bind2_unnest_normalized_lexp; eauto).
      assert (List.length (List.concat ess) = List.length (annots es))
        as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (List.length (find_node_incks P f)
              = List.length (List.concat ess)) as Hlck.
      { unfold find_node_incks. rewrite Hlen1.
        inv Hwl0;
          match goal with
          | H : find_node f P = Some ?nn |- _ => rewrite H
          end; rewrite map_length;
          match goal with
          | H : List.length (annots es) = _ |- _ => now rewrite H
          end. }
      edestruct (CALLS.noops_operand_types GL env base_ty rst_ty cenv
                   (find_node_incks P f) (List.concat ess)
                   es2 eqs2 st1 st2 ce2 xstc xstd argt xst sti)
        as (argts1 & Hargts1);
        [exact Hlck|exact Hnorm1|exact Hunn|exact Hgen2|exact Hargt|].

      (** every argument stream's clock has a type, so the slot ambients exist *)
      assert (forall nck, In nck (nclocksof es) ->
                 exists ckty0,
                   assign_clk_type env base_ty (stripname nck) = Some ckty0)
        as Hdef.
      { intros nck Hnck. unfold nclocksof in Hnck.
        apply in_flat_map in Hnck as (e & He & Hne).
        rewrite Forall_forall in Hargcl.
        exact (nclockof_types_defined env base_ty vars e (Hargcl e He)
                 env_total nck Hne). }

      (** and each named argument stream carries its own security name, which
          is what makes the augmentation's actuals cover the callee's clocks *)
      assert (Forall2 (fun t nck => forall w g,
                           snd nck = Some w -> Env.find w env = Some g ->
                           In g (fst t))
                argts (nclocksof es)) as Hnamed.
      { eapply (assign_lexps_named_covered P GL env base_ty rst_ty vars es
                  Hwles Hwces); [|exact Hargs].
        intros e f0 es0 ro0 anns0 He Heq w g Hw.
        subst e.
        destruct (anon_streams_name w anns0 Hw) as (a & Ha).
        intro Hf.
        exact (env_anon w g Hf
                 (Hanon w a
                    (nested_call_name_in_anon_in f es er anns _ f0 es0 ro0
                       anns0 w a He (@Coq.Init.Logic.eq_refl _ _) Ha))). }
      assert (List.length argts = List.length (nclocksof es)) as Hlargts
          by exact (Forall2_length _ _ _ Hnamed).

      (** the slot ambients, and that they are scoped *)
      remember (call_arg_ambients sub ckty (nclocksof es) (idck nd.(n_in)))
        as ambs_arg eqn:Eambs.
      assert (stream_ambients_scoped scope ambs_arg) as Hambargsc.
      { subst ambs_arg.
        exact (call_arg_ambients_scoped_named scope sub bck ckty (nclocksof es)
                 (idck nd.(n_in)) argts rst_ty_scoped
                 (fun z Hz => clk_types_scoped P es _ ckty Hwcg Hwces Hnsrces
                                (or_introl Hbcksrc) Hbckty z Hz)
                 Hwcin Hwi Hnamed Hscargts). }
      assert (clocks_covered (LSyn.clocksof es) ambs_arg) as Hccov.
      { subst ambs_arg. rewrite clocksof_nclocksof.
        exact (clocks_covered_call_args bck sub (idck nd.(n_in))
                 (nclocksof es) ckty Hbckty Hwi Hdef). }

      (** the induction hypothesis, on the arguments *)
      edestruct (call_args_streams P es (idck nd.(n_in)) bck sub ckty
                   false ess eqss st st1 argts sst sta ce1 xsta xstc
                   argts1 xst xst dlt)
        as (dlt1 & Hoff1 & Hce1' & Hrel1 & Hscope1 & Hsca1).
      { exact Halls. }
      { exact Hbckty. }
      { exact Hwi. }
      { exact Hdef. }
      { exact Hwles. }
      { exact Hwces. }
      { exact Hsrces. }
      { exact Hnd1. }
      { intros y Hy. apply Hmv.
        apply (CALLS.moved_by_prefix_local env st st1 st' Hf1'). exact Hy. }
      { exact Hscarg. }
      { exact Hscargts. }
      { rewrite <- Eambs. exact Hambargsc. }
      { exact Hlargts. }
      { exact Hfound1. }
      { exact Hmap. }
      { exact Hargs. }
      { exact Hgen1. }
      { apply Hargts1. }
      { exact Hcararg. }
      { exact Hbsta. }
      { exact Hlow. }
      rewrite <- Eambs in Hrel1.

      (** and the no-op pass on top of it, slot by slot *)
      assert (forall y, In y (CALLS.moved_by env st1 st2) ->
                        ~ In y (scope ++ CALLS.moved_by env st st1)) as Hsep12.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (CALLS.moved_by_suffix_local env st st1 st' Hfa).
          apply (CALLS.moved_by_prefix_local env st1 st2 st' Hf2'). exact Hin.
        - exact (CALLS.moved_by_disjoint_local env env_inj st st1 st2 y
                   Hy Hin). }
      assert (LSyn.clocksof (List.concat ess) = LSyn.clocksof es) as Hcl1.
      { rewrite !clocksof_annots.
        erewrite unnest_exps_annots; [reflexivity|exact Hwles|exact Hune0]. }
      edestruct (noops_step_streams (scope ++ CALLS.moved_by env st st1)
                   ambs_arg (find_node_incks P f) (List.concat ess)
                   es2 eqs2 st1 st2 argts1 argt ce2
                   xstc xstd xst xst xst sti dlt1)
        as (dlt2 & Hoff2 & Hce2' & Hrel2 & Hscope2 & Hsca2).
      { exact Hlck. }
      { exact Hnorm1. }
      { exact Hunn. }
      { exact Hnd2. }
      { exact Hsep12. }
      { rewrite Hcl1. exact Hccov. }
      { unfold stream_ambients_scoped in Hambargsc |- *.
        eapply Forall_impl; [|exact Hambargsc]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      { exact Hfound2. }
      { apply Hargts1. }
      { exact Hargt. }
      { exact Hsca1. }
      { exact Hgen2. }

      (** the reset.  Run at the call's own ambient joined with the reset's
          clock type: that is the ambient the reset's one stream needs, and it
          collapses into what the transfer wants because the source reset type
          already contains that clock type. *)
      assert (agree_off (CALLS.moved_by env st st2) dlt dlt2) as Hoff12.
      { eapply CALLS.agree_off_trans;
          [eapply CALLS.agree_off_incl; [|exact Hoff1];
           apply (CALLS.moved_by_prefix_local env st st1 st2 Hfb)
          |eapply CALLS.agree_off_incl; [|exact Hoff2];
           apply (CALLS.moved_by_suffix_local env st st1 st2 Hfa)]. }
      assert (exists dlt3,
                 agree_off (CALLS.moved_by env st2 st3) dlt2 dlt3
                 /\ listSatisfiable dlt3 ce3
                 /\ constraints_scoped (scope ++ CALLS.moved_by env st2 st3) ce3
                 /\ satisfiable dlt3 (fst rstty')
                      (merge (merge [rst_ty] ckty) (fst rstty))
                 /\ st_scoped (scope ++ CALLS.moved_by env st st3) (fst rstty'))
        as (dlt3 & Hoff3 & Hce3' & Hscope3 & Hrelrst & Hscrst').
      { destruct Hshape
          as [(Hern & Hn2 & Heq3 & Hst3 & Hrs')
             |(e1 & rv & ty0 & ckr0 & nm0 & rty & rstck
               & Her & Hs2 & Hrty & Hrstck & Hrs')].
        - (** no reset: nothing was emitted and nothing moved *)
          subst. destruct Hrst as (Hrstty & ?); subst rstty.
          apply generate_leqns_constraints_nil in Hgen3 as (? & ?); subst.
          exists dlt2. split; [apply CALLS.agree_off_refl|].
          split; [constructor|]. split; [constructor|].
          split; [apply satisfiable_merge_r|].
          rewrite fst_lvar. intros y Hy. destruct Hy as [Hy|[]]; subst y.
          apply in_or_app. now left.
        - (** a reset: the streams reset step, on the variable it came as *)
          subst er er2 rstty'.
          destruct Hrst as (t1 & a1 & rck & stm & Hty1 & Hsg1 & Hrck & Hrstty).
          apply single_inv in Hsg1 as (? & ?); subst t1 stb.
          assert (wl_exp P e1) as Hwle1 by (inv Hwl0; assumption).
          assert (wc_exp P vars e1) as Hwce1 by (inv Hwc0; assumption).
          assert (src_exp vars AN e1) as Hsrce1
            by (eapply src_exp_imm; [apply imm_Eapp_rst|exact Hsx]).
          assert (nested_src vars AN e1) as Hnsrce1
            by (eapply nested_src_reset; exact Hsx).
          assert (numstreams e1 = 1) as Hns1 by (inv Hwl0; assumption).
          assert (st_scoped scope (fst a1)) as Hsca1'.
          { assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hf
                by (exact (source_types_scoped P e1 [a1] sta stm Hwce1 Hlsa Hty1 Hbstb)).
            now inv Hf. }
          assert (snd rstty = snd a1) as Hsndr.
          { subst rstty. rewrite !snd_ljoin, snd_lvar.
            simpl snd. now rewrite cmerge_nil, cmerge_nil2. }
          assert (LSyn.clockof e1 = [ckr0]) as Hcl
              by (eapply unnest_reset_ann_clock; eauto).
          assert (assign_clk_type env base_ty ckr0 = Some rck) as Hrck0
              by (rewrite Hcl in Hrck; simpl hd in Hrck; exact Hrck).
          assert (rstck = rck) as Hcke
              by (rewrite Hrstck in Hrck0; now inv Hrck0).

          (** the ambient the reset's single stream is read at *)
          assert (st_scoped scope (merge (merge [rst_ty] ckty) rck))
            as Hambrsc.
          { intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
            - apply in_merge_inv in Hz as [Hz|Hz].
              + destruct Hz as [Hz|[]]; subst z. exact rst_ty_scoped.
              + exact (clk_types_scoped P es _ ckty Hwcg Hwces Hnsrces (or_introl Hbcksrc) Hbckty z Hz).
            - exact (clk_types_scoped P [e1] _ rck Hwcg
                       (Forall_cons _ Hwce1 (Forall_nil _))
                       (Forall_cons _ Hnsrce1 (Forall_nil _))
                       (or_introl (clk_src_clockof vars e1 ckr0
                          ltac:(rewrite Hcl; now left))) Hrck0 z Hz). }
          assert (clocks_covered (clockof e1)
                    [merge (merge [rst_ty] ckty) rck]) as Hcovr.
          { rewrite Hcl. constructor; [|constructor].
            exists rck. split; [exact Hrck0|].
            intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
            - destruct Hz as [Hz|[]]; subst z.
              apply in_merge_left, in_merge_left. now left.
            - now apply in_merge_right. }

          edestruct (reset_step_streams P e1 rv (ty0, (ckr0, nm0)) rty eqs3
                       st2 st3 a1 sta stm ce3 xstd xst' xst
                       (merge (merge [rst_ty] ckty) rck) dlt2)
            as (dlt3 & Hoff3 & Hce3' & Hrelr & Hinr & Hscope3).
          { apply Hallr. reflexivity. }
          { exact Hambrsc. }
          { exact Hcovr. }
          { exact Hfound3. }
          { exact Hwle1. }
          { exact Hwce1. }
          { exact Hsrce1. }
          { exact Hns1. }
          { exact Hunr. }
          { exact Hrty. }
          { exact Hnd3. }
          { intros y Hy. apply Hmv.
            apply (CALLS.moved_by_suffix_local env st st2 st' Hf02).
            apply (CALLS.moved_by_prefix_local env st2 st3 st' Hfd). exact Hy. }
          { exact Hty1. }
          { rewrite carried_single, <- Hsndr. exact Hscrst. }
          { exact Hsca1'. }
          { exact Hgen3. }
          { rewrite carried_single, <- Hsndr.
            eapply CALLS.listSatisfiable_off_scope
              with (sc := scope) (xs := CALLS.moved_by env st st2);
              [exact Hscrst| |exact Hoff12|exact Hcarrst].
            intros y Hy. apply Hmv.
            apply (CALLS.moved_by_prefix_local env st st2 st' Hf2'). exact Hy. }
          { exact Hbstb. }
          { exact Hlsa. }
          exists dlt3. split; [exact Hoff3|]. split; [exact Hce3'|].
          split; [exact Hscope3|]. split.
          + subst rstty rstck. rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            apply satisfiable_merge_intro.
            * apply satisfiable_of_incl. intros z Hz.
              apply in_merge_left, in_merge_left. exact Hz.
            * apply satisfiable_merge_intro.
              -- eapply satisfiable_trans; [exact Hrelr|].
                 apply satisfiable_of_incl. intros z Hz.
                 apply in_merge_inv in Hz as [Hz|Hz].
                 ++ apply in_merge_inv in Hz as [Hz|Hz];
                      [apply in_merge_left; exact Hz
                      |apply in_merge_right, in_merge_right,
                         in_merge_right; exact Hz].
                 ++ apply in_merge_right, in_merge_right, in_merge_left.
                    exact Hz.
              -- apply satisfiable_of_incl. intros z Hz.
                 apply in_merge_right, in_merge_right, in_merge_right.
                 exact Hz.
          + rewrite !fst_ljoin, !fst_lvar. cbn [fst].
            intros y Hy. apply in_merge_inv in Hy as [Hy|Hy].
            * destruct Hy as [Hy|[]]; subst y. apply in_or_app. now left.
            * apply in_merge_inv in Hy as [Hy|Hy].
              -- destruct Hy as [Hy|[]]; subst y.
                 apply in_app_or in Hinr as [Hinr|Hinr];
                   apply in_or_app; [now left|].
                 right.
                 apply (CALLS.moved_by_suffix_local env st st2 st3 Hf02).
                 exact Hinr.
              -- apply in_or_app. left.
                 exact (clk_types_scoped P [e1] ckr0 rstck Hwcg
                          (Forall_cons _ Hwce1 (Forall_nil _))
                       (Forall_cons _ Hnsrce1 (Forall_nil _))
                          (or_introl (clk_src_clockof vars e1 ckr0
                             ltac:(rewrite Hcl; now left))) Hrstck y Hy). }

      (** the call's own ambient is scoped *)
      assert (st_scoped scope (merge [rst_ty] ckty)) as Hambcsc.
      { intros z Hz. apply in_merge_inv in Hz as [Hz|Hz].
        - destruct Hz as [Hz|[]]; subst z. exact rst_ty_scoped.
        - exact (clk_types_scoped P es _ ckty Hwcg Hwces Hnsrces (or_introl Hbcksrc) Hbckty z Hz). }

      (** the results, and the witness on them *)
      assert (Forall2 (fun x b => Env.find x env = Some b)
                (List.map fst xs) outt) as Houttf
          by (rewrite Exs; eapply CALLS.mmap_find_env_Forall2; eauto).
      assert (Permutation (List.map fst xs ++ st_ids st3) (st_ids st'))
        as Hpx by (eapply idents_for_anns'_vars_perm; eauto).
      assert (Permutation
                (vars_defined
                   ((List.map fst xs, [Eapp f es2 er2 (List.map snd xs)])
                      :: (List.concat eqss ++ eqs2 ++ eqs3)) ++ st_ids st)
                (st_ids st')) as Hpall
          by (eapply unnest_exp_vars_perm; eauto).
      rewrite Hvd, <- app_assoc in Hpall.
      assert (NoDup (st_ids st')) as Hndst'
          by (eapply Permutation_NoDup; [exact Hpall|exact Hnd]).
      assert (NoDup (List.map fst xs ++ st_ids st3)) as Hndx
          by (rewrite Hpx; exact Hndst').
      assert (NoDup (List.map fst xs)) as Hndfst
          by (eapply NoDup_app_l; exact Hndx).
      assert (NoDup outt) as Hndoutt
          by (eapply (CALLS.sec_names_NoDup env env_inj);
              [exact Hndfst|exact Houttf]).
      assert (forall b, In b outt -> In b (CALLS.moved_by env st3 st'))
        as Houttmv.
      { intros b Hb.
        assert (In b (sec_of (List.map fst xs))) as Hbs
            by (eapply CALLS.Forall2_in_sec_of; eauto).
        unfold CALLS.sec_of, CALLS.moved_by in *.
        apply in_flat_map in Hbs as (x & Hx & Hbx).
        apply in_flat_map. exists x. split; [|exact Hbx].
        apply new_ids_spec. split.
        - eapply idents_for_anns'_incl_ids; eauto.
        - eapply NoDup_app_In; eauto. }
      assert (incl outt (CALLS.moved_by env st st')) as Houttmv0
          by (intros b Hb;
              apply (CALLS.moved_by_suffix_local env st st3 st' Hf03);
              now apply Houttmv).
      assert (incl outt (CALLS.moved_by env st2 st')) as Houttmv2
          by (intros b Hb;
              apply (CALLS.moved_by_suffix_local env st2 st3 st' Hfc);
              now apply Houttmv).
      assert (forall b, In b outt -> ~ In b scope) as Houttsc
          by (intros b Hb Hc; eapply (Hmv b); [now apply Houttmv0|exact Hc]).
      assert (Forall (fun o => In o scope) outs) as Houtssc.
      { rewrite Forall_map in Hsts.
        eapply Forall_impl; [|exact Hsts].
        intros o Ho. apply Ho. now left. }
      assert (List.length outs = List.length outt) as Hlenout.
      { apply fresh_idents_length in Houts.
        apply Forall2_length in Houttf.
        rewrite Houts, <- Houttf, map_length. now symmetry. }
      edestruct (CALLS.call_outputs_witness scope (merge [rst_ty] ckty)
                   Hambcsc dlt3 outs outt)
        as (dlt4 & Hoff4 & Hpairs);
        [exact Hndoutt|exact Hlenout|exact Houttsc|exact Houtssc|].

      (** the emitted call generates just the instantiated block *)
      assert (Forall normalized_lexp es2) as Hnorm2
          by (eapply CALLS.unnest_noops_normalized; eauto).
      assert (carried argt = []) as Hcargt.
      { eapply assign_lexps_normalized_pure with (es := es2); [|exact Hargt].
        eapply Forall_impl; [|exact Hnorm2]. intros; now constructor. }
      assert (snd rstty' = []) as Hsrst'.
      { destruct Hshape
          as [(_ & _ & _ & _ & Hrs')
             |(e1 & rv & ty0 & ckr0 & nm0 & rty & rstck
               & _ & _ & _ & _ & Hrs')]; subst rstty'; [reflexivity|].
        rewrite snd_ljoin, snd_lvar. cbn [snd]. apply cmerge_nil. }
      assert (ce0 = cs0) as Hce0'
          by (now rewrite Hce0, Hcargt, Hsrst', !cmerge_nil).

      (** the clock is the same on both sides *)
      assert (Forall (fun e => numstreams e = 1) (List.concat ess)) as Hns1s
          by (eapply map_bind2_unnest_exp_numstreams; eauto).
      assert (ckt = ckty) as Hckeq.
      { assert (LSyn.clocksof es2 = LSyn.clocksof es) as Hcl2.
        { eapply CALLS.unnest_call_clocksof;
            [exact Hwles|exact Hune0|exact Hlck|exact Hns1s|exact Hunn]. }
        rewrite Hcl2, Hck in Hckt. now inv Hckt. }

      (** the witnesses, composed *)
      assert (agree_off (CALLS.moved_by env st2 st') dlt2 dlt4) as Hoff34.
      { eapply CALLS.agree_off_trans.
        - eapply CALLS.agree_off_incl; [|exact Hoff3].
          apply (CALLS.moved_by_prefix_local env st2 st3 st' Hfd).
        - eapply CALLS.agree_off_incl; [|exact Hoff4]. exact Houttmv2. }
      assert (agree_off (CALLS.moved_by env st1 st') dlt1 dlt4) as Hoff1all.
      { eapply CALLS.agree_off_trans.
        - eapply CALLS.agree_off_incl; [|exact Hoff2].
          apply (CALLS.moved_by_prefix_local env st1 st2 st' Hf2').
        - eapply CALLS.agree_off_incl; [|exact Hoff34].
          apply (CALLS.moved_by_suffix_local env st1 st2 st' Hfb). }
      assert (agree_off (CALLS.moved_by env st st') dlt dlt4) as Hoffall.
      { eapply CALLS.agree_off_trans.
        - eapply CALLS.agree_off_incl; [|exact Hoff1].
          apply (CALLS.moved_by_prefix_local env st st1 st' Hf1').
        - eapply CALLS.agree_off_incl; [|exact Hoff1all].
          apply (CALLS.moved_by_suffix_local env st st1 st' Hfa). }

      (** the argument types, at the final witness and per slot *)
      assert (forall y, In y (CALLS.moved_by env st2 st') ->
                        ~ In y (scope ++ CALLS.moved_by env st st2)) as Hsep2.
      { intros y Hin Hy. apply in_app_or in Hy as [Hy|Hy].
        - eapply (Hmv y); [|exact Hy].
          apply (CALLS.moved_by_suffix_local env st st2 st' Hf02). exact Hin.
        - exact (CALLS.moved_by_disjoint_local env env_inj st st2 st' y
                   Hy Hin). }
      assert (stream_ambients_scoped (scope ++ CALLS.moved_by env st st1)
                ambs_arg) as Hambsc1'.
      { unfold stream_ambients_scoped in Hambargsc |- *.
        eapply Forall_impl; [|exact Hambargsc]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      assert (stream_ambients_scoped (scope ++ CALLS.moved_by env st st2)
                ambs_arg) as Hambsc2'.
      { unfold stream_ambients_scoped in Hambargsc |- *.
        eapply Forall_impl; [|exact Hambargsc]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      assert (Forall (fun t =>
                 st_scoped (scope ++ CALLS.moved_by env st st1) (fst t)) argts)
        as Hsc_argts1'.
      { eapply Forall_impl; [|exact Hscargts]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      assert (Forall (fun t =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst t)) argts)
        as Hsc_argts.
      { eapply Forall_impl; [|exact Hscargts]. intros q Hq.
        eapply st_scoped_weaken; [apply incl_appl, incl_refl|exact Hq]. }
      assert (Forall (fun t =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst t))
                argts1) as Hsc_argts1.
      { eapply Forall_impl; [|exact Hsca1]. intros q Hq.
        eapply st_scoped_weaken; [|exact Hq].
        apply incl_app; [apply incl_appl, incl_refl|].
        apply incl_appr, (CALLS.moved_by_prefix_local env st st1 st2 Hfb). }
      assert (Forall (fun t =>
                 st_scoped (scope ++ CALLS.moved_by env st st2) (fst t)) argt)
        as Hsc_argt.
      { eapply Forall_impl; [|exact Hsca2]. intros q Hq.
        eapply st_scoped_weaken; [|exact Hq].
        apply incl_app.
        - apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (CALLS.moved_by_prefix_local env st st1 st2 Hfb).
        - apply incl_appr,
            (CALLS.moved_by_suffix_local env st st1 st2 Hfa). }
      assert (stream_rel dlt4 ambs_arg argts argt) as Hrelargs.
      { eapply (stream_rel_compose dlt4 ambs_arg argts argts1 argt).
        - eapply (stream_rel_off_scope
                    (scope ++ CALLS.moved_by env st st2)
                    (CALLS.moved_by env st2 st') dlt2 dlt4
                    ambs_arg argts argts1);
            [exact Hambsc2'|exact Hsc_argts|exact Hsc_argts1|exact Hsep2
            |exact Hoff34|].
          eapply (stream_rel_off_scope
                    (scope ++ CALLS.moved_by env st st1)
                    (CALLS.moved_by env st1 st2) dlt1 dlt2
                    ambs_arg argts argts1);
            [exact Hambsc1'|exact Hsc_argts1'|exact Hsca1|exact Hsep12
            |exact Hoff2|exact Hrel1].
        - eapply (stream_rel_off_scope
                    (scope ++ CALLS.moved_by env st st2)
                    (CALLS.moved_by env st2 st') dlt2 dlt4
                    ambs_arg argts1 argt);
            [exact Hambsc2'|exact Hsc_argts1|exact Hsc_argt|exact Hsep2
            |exact Hoff34|exact Hrel2]. }

      (** the reset type the source built is a source type *)
      assert (st_scoped scope (fst rstty)) as Hscrsty.
      { destruct er as [e1|].
        - destruct Hrst
            as (t1 & a1 & rck & stm & Hty1 & Hsg1 & Hrck & Hrstty).
          apply single_inv in Hsg1 as (? & ?); subst t1 stb.
          assert (wc_exp P vars e1) as Hwce1 by (inv Hwc0; assumption).
          assert (src_exp vars AN e1) as Hsrce1
            by (eapply src_exp_imm; [apply imm_Eapp_rst|exact Hsx]).
          assert (nested_src vars AN e1) as Hnsrce1
            by (eapply nested_src_reset; exact Hsx).
          subst rstty. rewrite !fst_ljoin, !fst_lvar. cbn [fst].
          intros y Hy. apply in_merge_inv in Hy as [Hy|Hy].
          + destruct Hy as [Hy|[]]; subst y. exact rst_ty_scoped.
          + apply in_merge_inv in Hy as [Hy|Hy].
            * assert (Forall (fun t => st_scoped scope (fst t)) [a1]) as Hf
                  by (exact (source_types_scoped P e1 [a1] sta stm Hwce1 Hlsa Hty1 Hbstb)).
              inv Hf. auto.
            * exact (clk_types_scoped P [e1] _ rck Hwcg
                       (Forall_cons _ Hwce1 (Forall_nil _))
                       (Forall_cons _ Hnsrce1 (Forall_nil _))
                       (or_introl (clk_src_hd_clockof vars e1)) Hrck y Hy).
        - destruct Hrst as (Hrstty & ?). subst rstty.
          rewrite fst_lvar. intros y Hy.
          destruct Hy as [Hy|[]]; subst y. exact rst_ty_scoped. }

      (** the callee's inputs are well clocked under its own interface, which
          is what makes a formal's clock variables formals *)
      assert (List.length (idck nd.(n_in)) = List.length argts) as Hlin
          by (rewrite (Forall2_length _ _ _ Hwi); now rewrite Hlargts).

      (** the actuals, as names a caller may use *)
      assert (Forall (caller_st env scope) (List.map fst argts)) as Hcs_src.
      { rewrite Forall_map. eapply Forall_impl; [|exact Hscargts].
        intros q Hq. exact (CALLS.caller_st_scoped env scope _ Hq). }
      assert (caller_st env scope ckty) as Hck_src
          by exact (CALLS.caller_st_scoped env scope _
                      (fun z Hz => clk_types_scoped P es _ ckty Hwcg Hwces Hnsrces
                                     (or_introl Hbcksrc) Hbckty z Hz)).
      assert (caller_st env scope (fst rstty)) as Hrs_src
          by exact (CALLS.caller_st_scoped env scope _ Hscrsty).
      assert (Forall (caller_name env scope) outs) as Hos_src.
      { eapply Forall_impl; [|exact Houtssc]. intros o Ho. left. exact Ho. }
      assert (Forall (caller_st env scope) (List.map fst argt)) as Hcs_tgt.
      { rewrite Forall_map. eapply Forall_impl; [|exact Hsc_argt].
        intros q Hq. exact (CALLS.caller_st_moved env scope _ _ _ Hq). }
      assert (caller_st env scope ckt) as Hckt_tgt
          by (rewrite Hckeq; exact Hck_src).
      assert (caller_st env scope (fst rstty')) as Hrs_tgt
          by exact (CALLS.caller_st_moved env scope _ _ _ Hscrst').
      assert (Forall (caller_name env scope) outt) as Hos_tgt.
      { rewrite Forall_forall. intros b Hb.
        exact (CALLS.caller_name_moved env scope st st' b (Houttmv0 b Hb)). }

      (** the signature's scope avoids both sides' actuals *)
      assert (forall y,
                 In y (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out)) ->
                 Forall (fun v => ~ In y v) (List.map fst argts)
                 /\ Forall (fun v => ~ In y v) (List.map fst argt)
                 /\ ~ In y ckty /\ ~ In y ckt
                 /\ ~ In y (fst rstty) /\ ~ In y (fst rstty')
                 /\ ~ In y outs /\ ~ In y outt) as Hfresh.
      { eapply CALLS.call_subst_fresh_pipeline;
          [eapply sig_actuals_fresh;
             [exact Esg|exact Hcs_src|exact Hck_src|exact Hrs_src
             |exact Hos_src|exact Hcs]
          |eapply sig_actuals_fresh;
             [exact Esg|exact Hcs_tgt|exact Hckt_tgt|exact Hrs_tgt
             |exact Hos_tgt|exact Hgc]]. }

      (** and so does the augmentation, which adds only clock actuals *)
      assert (Forall (fun v => forall y,
                  In y (sg.(s_in) ++ sg.(s_clk) :: sg.(s_reset) :: sg.(s_out))
                  -> ~ In y v)
                (CALLS.augment_actuals env sub (idck nd.(n_in)) argts))
        as Hfaug.
      { eapply (CALLS.augment_actuals_fresh env sub (idck nd.(n_in)) argts
                  (nclocksof es)).
        - exact (Forall2_length _ _ _ Hwi).
        - exact Hlin.
        - intros i x ck nck Hxi Hni.
          exact (proj1 (Forall2_nth_error _ (idck nd.(n_in)) (nclocksof es)
                          i (x, ck) nck Hwi Hxi Hni)).
        - intros i nck t u g Hni Hti Hu Hg.
          exact (Forall2_nth_error _ argts (nclocksof es) i t nck
                   Hnamed Hti Hni u g Hu Hg).
        - intros i x ck x' Hxi Hx'.
          assert (In (x, ck) (idck nd.(n_in))) as Hin
              by (eapply nth_error_In; exact Hxi).
          unfold wc_env in Hwcin. rewrite Forall_forall in Hwcin.
          pose proof (Hwcin (x, ck) Hin) as Hwck. cbn [snd] in Hwck.
          exact (clock_vars_wc (idck nd.(n_in)) ck Hwck x' Hx').
        - apply Forall_forall. intros v Hv y Hy.
          destruct (Hfresh y Hy) as (H1 & _).
          rewrite Forall_forall in H1. exact (H1 v Hv). }

      (** and the instantiated block, by monotonicity in the augmented
          actuals -- which is what lets each argument keep its own slot's
          ambient instead of a common one *)
      assert (listSatisfiable dlt4 cs) as Hcs4.
      { eapply CALLS.listSatisfiable_off_scope
          with (sc := scope) (xs := CALLS.moved_by env st st');
          [exact Hsccs|exact Hmv|exact Hoffall|exact Hcarcs]. }
      rewrite Eambs in Hrelargs.
      assert (listSatisfiable dlt4 cs0) as Hcs04.
      { eapply (CALLS.generate_constraints_mono_sem_aug env
                  (merge [rst_ty] ckty) dlt4 sg (idck nd.(n_in)) sub argts
                  (List.map fst argt) ckty ckt (fst rstty) (fst rstty')
                  outs outt cs cs0 stc sst' sti xsta).
        - eapply sig_good; exact Esg.
        - eapply (CALLS.sig_nodup_pipeline GL sig_nodup); exact Esg.
        - exact Hlin.
        - exact Hfresh.
        - exact Hfaug.
        - exact (call_args_augmented dlt4 sub ckty (idck nd.(n_in))
                   (nclocksof es) argts argt Hrelargs).
        - rewrite Hckeq. apply satisfiable_merge_r.
        - eapply CALLS.satisfiable_off with (xs := outt);
            [exact Hoff4| | |exact Hrelrst].
          + intros y Hy Hin.
            apply Hscrst' in Hy. apply in_app_or in Hy as [Hy|Hy].
            * eapply (Hmv y); [now apply Houttmv0|exact Hy].
            * exact (CALLS.moved_by_disjoint_local env env_inj st st3 st' y
                       Hy (Houttmv y Hin)).
          + intros y Hy Hin. apply in_merge_inv in Hy as [Hy|Hy].
            * eapply (Houttsc y Hin). now apply Hambcsc.
            * eapply (Houttsc y Hin). now apply Hscrsty.
        - exact Hpairs.
        - intros c Hc.
          eapply CALLS.call_augment_dep_concrete;
            [exact Hsigin|exact Hfn|exact Esg|exact Hwcin|exact Hwi
            |exact Hnamed|exact Hc].
        - exact Hcs.
        - exact Hgc.
        - exact Hcs4. }

      (** the results' types, on the two sides *)
      assert (Forall2 (fun b t => t = lvar b) outt ts'') as Hevars'
          by (eapply CALLS.evars_outt; eauto).
      assert (Forall2 (fun o b =>
                  satisfiable dlt4 [b] (merge (merge [rst_ty] ckty) [o]))
                outs outt) as Hpairs1.
      { eapply Forall2_impl_In; [|exact Hpairs].
        intros o b _ _ (Hp & _). exact Hp. }
      assert (List.length ambs = List.length outs) as Hlenamb
          by (rewrite Hlen, map_length; reflexivity).

      exists dlt4. split; [|split; [|split; [|split]]].
      - exact Hoffall.
      - apply listSatisfiable_app. split; [rewrite Hce0'; exact Hcs04|].
        apply listSatisfiable_app. split.
        + eapply CALLS.listSatisfiable_off_scope
            with (sc := scope ++ CALLS.moved_by env st st1)
                 (xs := CALLS.moved_by env st1 st');
            [exact Hscope1| |exact Hoff1all|exact Hce1'].
          intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
          * eapply (Hmv y); [|exact Hin].
            apply (CALLS.moved_by_suffix_local env st st1 st' Hfa). exact Hy.
          * exact (CALLS.moved_by_disjoint_local env env_inj st st1 st' y
                     Hin Hy).
        + apply listSatisfiable_app. split.
          * eapply CALLS.listSatisfiable_off_scope
              with (sc := (scope ++ CALLS.moved_by env st st1)
                            ++ CALLS.moved_by env st1 st2)
                   (xs := CALLS.moved_by env st2 st');
              [exact Hscope2| |exact Hoff34|exact Hce2'].
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- apply in_app_or in Hin as [Hin|Hin].
               ++ eapply (Hmv y); [|exact Hin].
                  apply (CALLS.moved_by_suffix_local env st st2 st' Hf02).
                  exact Hy.
               ++ exact (CALLS.moved_by_disjoint_local env env_inj st st1 st'
                           y Hin
                           (CALLS.moved_by_suffix_local env st1 st2 st' Hfb
                              y Hy)).
            -- exact (CALLS.moved_by_disjoint_local env env_inj st1 st2 st' y
                        Hin Hy).
          * eapply CALLS.listSatisfiable_off_scope
              with (sc := scope ++ CALLS.moved_by env st2 st3)
                   (xs := outt);
              [exact Hscope3| |exact Hoff4|exact Hce3'].
            intros y Hy Hin. apply in_app_or in Hin as [Hin|Hin].
            -- exact (Houttsc y Hy Hin).
            -- exact (CALLS.moved_by_disjoint_local env env_inj st2 st3 st' y
                        Hin (Houttmv y Hy)).
      - exact (call_results_stream_rel dlt4 (merge [rst_ty] ckty) ambs
                 outs outt ts''
                 (cmerge cs (cmerge (carried argts) (snd rstty)))
                 Hbelow Hpairs1 Hevars' Hlenamb).
      - apply Forall_app. split.
        + rewrite Hce0'.
          eapply generate_constraints_scoped with (sig := sg);
            [eapply sig_scoped; exact Esg| | | | |exact Hgc].
          * rewrite Forall_map. eapply Forall_impl; [|exact Hsc_argt].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (CALLS.moved_by_prefix_local env st st2 st' Hf2').
          * rewrite Hckeq. eapply st_scoped_weaken;
              [apply incl_appl, incl_refl|].
            intros y Hy. exact (clk_types_scoped P es _ ckty Hwcg Hwces Hnsrces
                                  (or_introl (clk_src_base vars es)) Hck y Hy).
          * eapply st_scoped_weaken; [|exact Hscrst'].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (CALLS.moved_by_prefix_local env st st3 st' Hfd).
          * rewrite Forall_forall. intros b Hb. apply in_or_app. right.
            now apply Houttmv0.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, (CALLS.moved_by_prefix_local env st st1 st' Hf1').
          * apply Forall_app. split.
            -- eapply Forall_impl; [|exact Hscope2].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app.
               ++ apply incl_app; [apply incl_appl, incl_refl|].
                  apply incl_appr,
                    (CALLS.moved_by_prefix_local env st st1 st' Hf1').
               ++ apply incl_appr. eapply incl_tran;
                    [apply (CALLS.moved_by_prefix_local env st1 st2 st' Hf2')
                    |apply (CALLS.moved_by_suffix_local env st st1 st' Hfa)].
            -- eapply Forall_impl; [|exact Hscope3].
               intros cc Hcc. eapply constraint_scoped_incl; [|exact Hcc].
               apply incl_app; [apply incl_appl, incl_refl|].
               apply incl_appr. eapply incl_tran;
                 [apply (CALLS.moved_by_prefix_local env st2 st3 st' Hfd)
                 |apply (CALLS.moved_by_suffix_local env st st2 st' Hf02)].
      - eapply CALLS.Forall2_right_In; [exact Hevars'|].
        intros b t Hb Heq. rewrite Heq, fst_lvar.
        intros y Hy. destruct Hy as [Hy|[]]; subst y.
        apply in_or_app. right. now apply Houttmv0.
    Qed.


    (** * The expression level, closed on the pointwise relation

        The same induction as the scalar [carries_exp], on the contract that
        gives each source stream its own clock ambient.  Only the call case
        reads the two program-level facts, and only the merge and the
        conditional split on [is_control]. *)

    Theorem carries_exp_streams :
      forall P,
        wc_global P ->
        CALLS.sig_inputs_ok GL P ->
        forall e, carries_streams P e.
    Proof.
      intros P Hwcg Hsigin e. induction e using exp_ind2; intros ic.
      - apply carries_Econst_streams.
      - apply carries_Evar_streams.
      - apply carries_Eunop_streams; assumption.
      - apply carries_Ebinop_streams; assumption.
      - apply carries_Efby_streams; assumption.
      - apply carries_Earrow_streams; assumption.
      - apply carries_Ewhen_streams; assumption.
      - destruct a as (tys & cl). destruct ic;
          [apply carries_Emerge_control_streams
          |apply carries_Emerge_lift_streams]; assumption.
      - destruct a as (tys & cl). destruct ic;
          [apply carries_Eite_control_streams
          |apply carries_Eite_lift_streams]; assumption.
      - apply carries_Eapp_streams;
          [exact Hwcg|exact Hsigin|assumption|].
        intros e1 Her. subst ro. assumption.
    Qed.

    Corollary carries_exps_streams :
      forall P,
        wc_global P ->
        CALLS.sig_inputs_ok GL P ->
        forall es, carries_list_streams P es.
    Proof.
      intros P Hwcg Hsigin es.
      apply carries_list_streams_intro.
      apply Forall_forall. intros e _.
      exact (carries_exp_streams P Hwcg Hsigin e).
    Qed.

  End ExpressionContract.

End StreamAmbients.

End SecLusUnnestingStreams.
