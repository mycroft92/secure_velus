(** Pointwise ambient infrastructure for multi-stream unnesting. *)

From Coq Require Import List.

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
    forall ckty,
      assign_clk_type env base_ty ck = Some ckty ->
      incl (merge [rst_ty] ckty) a.

  Definition clocks_covered (cks : list clock) (ambs : list ST) : Prop :=
    Forall2 clock_covered cks ambs.

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
        apply (Hclk ck Hck ckty Hcl). exact Hy. }
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
        - apply hm_ext_incl. exact (Hclk ck Hck ckty Hcl).
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

End StreamAmbients.

End SecLusUnnestingStreams.
