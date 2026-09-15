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

Module Type SECLUSUNNESTING
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
  (Import UNN     : UNNESTING Ids Op OpAux LSyn).

  Import SECMONADNotations.
  Import UNN.Fresh.Tactics.

  (** * The security side of a call expression

      The analogue of [generate_lcall_constraint_inv], one level down: what
      [assign_lexp_type] does to an [Eapp].  Every Leg U proof about a nested
      call starts here.

      The result is [length anns] types, all carrying the *same* constraint
      list -- the instantiated call block joined with whatever the arguments
      and the reset were carrying.  That shared list is what the emitted
      equation has to generate. *)

  Lemma assign_lexp_Eapp_inv :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      exists sg argts rstty ckty outs cs sta stb stc,
        assign_lexps G env base_ty rst_ty es st = OK (argts, sta)
        /\ (match er with
            | None => rstty = lvar rst_ty /\ stb = sta
            | Some e1 =>
                exists t1 a1 stm,
                  assign_lexp_type G env base_ty rst_ty e1 sta = OK (t1, stm)
                  /\ single t1 stm = OK (a1, stb)
                  /\ rstty = ljoin (lvar rst_ty) a1
            end)
        /\ assign_clk_type env base_ty (find_base_clock (LSyn.clocksof es))
           = Some ckty
        /\ find_signature f G = Some sg
        /\ fresh_idents (List.length anns) stb = OK (outs, stc)
        /\ generate_constraints sg (List.map fst argts) ckty (fst rstty) outs stc
           = OK (cs, st')
        /\ ts = List.map
                  (fun o => (([o] : ST),
                             cmerge cs (cmerge (carried argts) (snd rstty))))
                  outs.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (argts & sta & Hargs & H).
    eapply sec_bind_inv in H as (rstty & stb & Hrst & H).
    eapply sec_bind_inv in H as (ckty & stk & Hck & H).
    destruct (find_signature f G) as [sg|] eqn:Esg; [|discriminate].
    eapply sec_bind_inv in H as (outs & stc & Houts & H).
    eapply sec_bind_inv in H as (cs & std & Hcs & Hret).
    unfold ret in Hret. inv Hret.
    apply option_to_sec_inv in Hck as [Hck ?]; subst stk.
    exists sg, argts, rstty, ckty, outs, cs, sta, stb, stc.
    repeat split; auto.
    destruct er as [e1|].
    - eapply sec_bind_inv in Hrst as (t1 & stm & Ht1 & Hrst).
      eapply sec_bind_inv in Hrst as (a1 & stn & Ha1 & Hret').
      unfold ret in Hret'. inv Hret'.
      exists t1, a1, stm. auto.
    - unfold ret in Hrst. inv Hrst. auto.
  Qed.

  (** * The unnesting side of a call expression

      The mirror of the previous lemma.  [unnest_exp] on an [Eapp] unnests the
      arguments, the no-op arguments and the reset, takes one identifier per
      result annotation, returns an [Evar] for each, and emits the call as an
      equation in front of everything the sub-unnestings emitted.

      [idents_for_anns'] does not always mint: when the annotation already
      carries a name it *reuses* it.  So the correspondence with
      [fresh_idents (length anns)] is not mint-for-mint.  It does not need to
      be -- both lists have length [length anns]
      ([idents_for_anns'_length]), so the bijection is positional over the
      call's results, and whether a result's variable is new or reused only
      changes which side of the bijection was already named. *)

  Lemma unnest_exp_Eapp_inv :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists es1 eqs1 st1 es2 eqs2 st2 er' eqs3 st3 xs,
        unnest_exps G es st = ((es1, eqs1), st1)
        /\ unnest_noops_exps (find_node_incks G f) es1 st1 = ((es2, eqs2), st2)
        /\ unnest_reset (unnest_exp G true) er st2 = ((er', eqs3), st3)
        /\ idents_for_anns' anns st3 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (List.map fst xs, [Eapp f es2 er' (List.map snd xs)])
                 :: eqs1 ++ eqs2 ++ eqs3.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    unfold unnest_exps. apply bind2_spec.
    do 3 eexists. split; [eassumption|apply ret_spec].
  Qed.

  (** The two lists of results have the same length, which is what makes the
      bijection between a call's minted security names and its variables
      positional. *)

  Lemma fresh_idents_length :
    forall n outs st st',
      fresh_idents n st = OK (outs, st') ->
      List.length outs = n.
  Proof.
    induction n as [|n IH]; intros outs st st' H; simpl in H.
    - unfold ret in H. inv H. reflexivity.
    - eapply sec_bind_inv in H as (x & st1 & Hx & H).
      eapply sec_bind_inv in H as (xs & st2 & Hxs & Hret).
      unfold ret in Hret. inv Hret. simpl. f_equal. eapply IH; eauto.
  Qed.

  Lemma assign_lexp_Eapp_length :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      List.length ts = List.length anns.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & Hargs & Hrst & Hck & Esg & Houts & Hcs & Hts).
    subst ts. rewrite map_length.
    eapply fresh_idents_length; eauto.
  Qed.

  (** * Why the carried component is empty after unnesting

      The results of an unnested expression are variables, and a variable
      carries nothing: [assign_lexp_type] on an [Evar] is [lvar] of its
      security name, whose constraint component is [[]].  Everything the
      expression was carrying has become an equation.

      That is the bridge between this leg and the transcription leg, and it is
      why [to_lexps_assign_rev] could conclude the argument types come back as
      [map (fun t => (t, [])) tys] there: by the time transcription runs, both
      passes have already turned every carried constraint into an equation. *)

  Lemma assign_lexp_Evar_inv :
    forall G env base_ty rst_ty x a t st st',
      assign_lexp_type G env base_ty rst_ty (Evar x a) st = OK (t, st') ->
      exists xt,
        Env.find x env = Some xt
        /\ t = [(([xt] : ST), [])]
        /\ st' = st.
  Proof.
    intros G env base_ty rst_ty x a t st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (xt & st1 & Hx & Hret).
    apply find_env_inv in Hx as [Hx Hst]; subst st1.
    unfold ret in Hret. inv Hret.
    exists xt. repeat split; auto.
  Qed.

  Corollary unnested_call_results_carry_nothing :
    forall G env base_ty rst_ty G' is_control f es er anns es' eqs st st',
      unnest_exp G' is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      Forall (fun e' =>
                forall t sst sst',
                  assign_lexp_type G env base_ty rst_ty e' sst = OK (t, sst') ->
                  Forall (fun p => snd p = []) t)
             es'.
  Proof.
    intros G env base_ty rst_ty G' is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & _ & _ & Hes' & _).
    subst es'.
    apply Forall_map, Forall_forall. intros [id an] _ t sst sst' Ht.
    eapply assign_lexp_Evar_inv in Ht as (xt & _ & Ht & _). subst t.
    now repeat constructor.
  Qed.

  (** * Base cases

      On a constant or a variable unnesting does nothing and emits nothing,
      and the security typer returns a type carrying nothing.  Those are the
      two ends of the induction meeting trivially. *)

  Lemma unnest_exp_Econst :
    forall G is_control c st,
      unnest_exp G is_control (Econst c) st = (([Econst c], []), st).
  Proof. intros. simpl. apply ret_spec. Qed.

  Lemma unnest_exp_Evar :
    forall G is_control x a st,
      unnest_exp G is_control (Evar x a) st = (([Evar x a], []), st).
  Proof. intros. simpl. apply ret_spec. Qed.

  (** * A call carries exactly what its emitted equation generates

      Every result of a call carries the same list, so merging them all
      collapses back to that one list -- [cmerge] is idempotent.  Which means
      the call's total carried constraints are the instantiated block joined
      with what the arguments and the reset carried, and that is, term for
      term, what [generate_lcall_constraint] produces for the equation
      unnesting emits. *)

  Lemma carried_uniform :
    forall (held : list SymTypes.constraint) outs,
      carried (List.map (fun o => (([o] : ST), held)) outs)
      = match outs with [] => [] | _ => held end.
  Proof.
    intros held outs. induction outs as [|o os IH]; [reflexivity|].
    simpl in *. rewrite IH. destruct os.
    - apply cmerge_nil.
    - apply cmerge_refl.
  Qed.

  Corollary assign_lexp_Eapp_carried :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      anns <> [] ->
      exists sg (argts : list LST) (rstty : LST) (ckty : ST)
             (cs : list SymTypes.constraint),
        find_signature f G = Some sg
        /\ assign_clk_type env base_ty (find_base_clock (LSyn.clocksof es))
           = Some ckty
        /\ carried ts = cmerge cs (cmerge (carried argts) (snd rstty)).
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H Hne.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & Hargs & Hrst & Hck & Esg & Houts & Hcs & Hts).
    exists sg, argts, rstty, ckty, cs.
    split; [exact Esg|]. split; [exact Hck|].
    subst ts. rewrite carried_uniform.
    destruct outs as [|o os] eqn:Eouts.
    - exfalso. apply Hne.
      apply fresh_idents_length in Houts. simpl in Houts.
      destruct anns; [reflexivity|discriminate].
    - reflexivity.
  Qed.

  (** * Argument lists

      The induction decomposes an argument list on both sides at once, so it
      needs [carried] to distribute over the concatenation [assign_lexps]
      builds.  It does: [carried] is a [cmerge] fold, and [cmerge] is
      associative with [[]] as unit. *)

  Lemma carried_app :
    forall ts us,
      carried (ts ++ us) = cmerge (carried ts) (carried us).
  Proof.
    induction ts as [|t ts IH]; intros us; simpl.
    - now rewrite cmerge_nil2.
    - rewrite IH. now rewrite cmerge_assoc.
  Qed.

  (** So an argument list carries the merge of what its expressions carry,
      which is the shape the [Eapp] case needs of its [carried argts]. *)

  Lemma assign_lexps_carried_cons :
    forall G env base_ty rst_ty e es ts st st',
      assign_lexps G env base_ty rst_ty (e :: es) st = OK (ts, st') ->
      exists t r sta,
        assign_lexp_type G env base_ty rst_ty e st = OK (t, sta)
        /\ assign_lexps G env base_ty rst_ty es sta = OK (r, st')
        /\ ts = t ++ r
        /\ carried ts = cmerge (carried t) (carried r).
  Proof.
    intros G env base_ty rst_ty e es ts st st' H.
    rewrite assign_lexps_cons in H.
    eapply sec_bind_inv in H as (t & sta & Ht & H).
    eapply sec_bind_inv in H as (r & stb & Hr & Hret).
    unfold ret in Hret. inv Hret.
    exists t, r, sta. repeat split; auto. apply carried_app.
  Qed.

  Lemma assign_lexps_carried_nil :
    forall G env base_ty rst_ty ts st st',
      assign_lexps G env base_ty rst_ty [] st = OK (ts, st') ->
      ts = [] /\ carried ts = [] /\ st' = st.
  Proof.
    intros G env base_ty rst_ty ts st st' H.
    rewrite assign_lexps_nil in H. unfold ret in H. inv H.
    repeat split; reflexivity.
  Qed.

  (** * The delay, on the unnesting side

      [Efby] lifts exactly as [Eapp] does -- one identifier per annotation, an
      [Evar] returned for each, and one emitted equation per result.  The
      difference is what the emitted equations are: a [fby] each, rather than
      a single call.  This is also the case the initialisation leg picks up,
      since those [fby]s are what [fby_equation] then looks at. *)

  Lemma unnest_exp_Efby_inv :
    forall G is_control e0s es anns es' eqs st st',
      unnest_exp G is_control (Efby e0s es anns) st = ((es', eqs), st') ->
      exists e0s' eqs1 st1 es'' eqs2 st2 xs,
        unnest_exps G e0s st = ((e0s', eqs1), st1)
        /\ unnest_exps G es st1 = ((es'', eqs2), st2)
        /\ idents_for_anns anns st2 = (xs, st')
        /\ es' = List.map (fun '(x, ann) => Evar x ann) xs
        /\ eqs = (List.map (fun '((x, _), fby) => ([x], [fby]))
                    (combine xs (unnest_fby e0s' es'' anns)))
                 ++ eqs1 ++ eqs2.
  Proof.
    intros G is_control e0s es anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    all: unfold unnest_exps; apply bind2_spec;
         repeat esplit; eauto using ret_spec.
  Qed.

  (** * The remaining lifting cases

      [Earrow] lifts exactly as [Efby].  [Emerge] and [Eite] lift only when
      [is_control] is false; their branches are unnested at [is_control =
      true], where nothing lifts, so the induction has to run at both flags.
      [unnest_controls] is a local [let] with no global counterpart, so these
      are stated directly over [map_bind2 (unnest_exp G true)]. *)

  Lemma unnest_exp_Earrow_inv :
    forall G is_control e0s es anns es' eqs st st',
      unnest_exp G is_control (Earrow e0s es anns) st = ((es', eqs), st') ->
      exists e0s' eqs1 st1 es'' eqs2 st2 xs,
        unnest_exps G e0s st = ((e0s', eqs1), st1)
        /\ unnest_exps G es st1 = ((es'', eqs2), st2)
        /\ idents_for_anns anns st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e]) (unnest_arrow e0s' es'' anns)))
                 ++ eqs1 ++ eqs2.
  Proof.
    intros G is_control e0s es anns es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    all: unfold unnest_exps; apply bind2_spec;
         repeat esplit; eauto using ret_spec.
  Qed.

  Lemma unnest_exp_Emerge_inv :
    forall G ckid es1 es2 tys cl es' eqs st st',
      unnest_exp G false (Emerge ckid es1 es2 (tys, cl)) st = ((es', eqs), st') ->
      exists es1' eqs1 st1 es2' eqs2 st2 xs,
        map_bind2 (unnest_exp G true) es1 st = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st2)
        /\ idents_for_anns (List.map (fun ty => (ty, cl)) tys) st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e])
                       (unnest_merge ckid (List.concat es1') (List.concat es2')
                          tys cl)))
                 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G ckid es1 es2 tys cl es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Eite_inv :
    forall G e es1 es2 tys ck es' eqs st st',
      unnest_exp G false (Eite e es1 es2 (tys, ck)) st = ((es', eqs), st') ->
      exists e' eqs0 st0 es1' eqs1 st1 es2' eqs2 st2 xs,
        unnest_exp G false e st = ((e', eqs0), st0)
        /\ map_bind2 (unnest_exp G true) es1 st0 = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st2)
        /\ idents_for_anns (List.map (fun ty => (ty, ck)) tys) st2 = (xs, st')
        /\ es' = List.map (fun '(id, ann) => Evar id ann) xs
        /\ eqs = (combine (List.map (fun '(id, _) => [id]) xs)
                    (List.map (fun e => [e])
                       (unnest_ite (hd_default e') (List.concat es1')
                          (List.concat es2') tys ck)))
                 ++ eqs0 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G e es1 es2 tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
  Qed.

  (** * The reset of an unnested call is always a variable

      [unnest_reset] has two branches: it keeps the head when it is already an
      [Evar], and otherwise mints a variable and emits an equation binding it.
      Either way what comes back is a variable, which is what lets the emitted
      call equation be inverted with [generate_lcall_constraint_inv] -- the
      Lustre generator only accepts a reset that is an [Evar]. *)

  Lemma unnest_reset_shape :
    forall k er er' eqs st st',
      unnest_reset k er st = ((er', eqs), st') ->
      er' = None \/ exists v an, er' = Some (Evar v an).
  Proof.
    intros k er er' eqs st st' H.
    unnest_reset_spec.
    - right. do 2 eexists. reflexivity.
    - right. do 2 eexists. reflexivity.
    - left. reflexivity.
  Qed.

  Corollary unnest_exp_Eapp_reset_is_var :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists es2 er' xs,
        (er' = None \/ exists v an, er' = Some (Evar v an))
        /\ In (List.map fst xs, [Eapp f es2 er' (List.map snd xs)]) eqs.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & Hrst & _ & _ & Heqs).
    exists es2, er', xs. split.
    - eapply unnest_reset_shape; eauto.
    - subst eqs. now left.
  Qed.

  (** * What the call case reduces to

      Both sides instantiate the *same* callee: the source expression looks [f]
      up to build what it carries, and the equation unnesting emits looks [f]
      up to build what it generates.  So the two constraint sets have the same
      shape -- an instantiated block merged with what the arguments and the
      reset carry -- and differ only in the arguments, which the induction
      relates, and in the result names, which
      [subst_constraints_out_map] relates.

      Nothing structural is left in this case. *)

  Lemma Eapp_and_emitted_shape :
    forall GL GN env base_ty rst_ty cenv f es er anns ts sst sst'
           x xs es'' er'' anns'' ce xst xst',
      assign_lexp_type GL env base_ty rst_ty (Eapp f es er anns) sst
        = OK (ts, sst') ->
      (er'' = None \/ exists v an, er'' = Some (Evar v an)) ->
      generate_leqn_constraint GN env base_ty rst_ty cenv
        (x :: xs, [Eapp f es'' er'' anns'']) xst = OK (ce, xst') ->
      anns <> [] ->
      exists sgL sgN,
        find_signature f GL = Some sgL
        /\ find_signature f GN = Some sgN
        /\ (exists (argts : list LST) (rstty : LST) (cs : list SymTypes.constraint),
              carried ts = cmerge cs (cmerge (carried argts) (snd rstty)))
        /\ (exists (argts' : list LST) (rstty' : LST) (ckty' : ST)
                   (outs' : list ident) (cs0 : list SymTypes.constraint) sti stf,
              generate_constraints sgN (List.map fst argts') ckty' (fst rstty')
                outs' sti = OK (cs0, stf)
              /\ ce = cmerge cs0 (cmerge (carried argts') (snd rstty'))).
  Proof.
    intros GL GN env base_ty rst_ty cenv f es er anns ts sst sst'
           x xs es'' er'' anns'' ce xst xst' Hsrc Hshape Htgt Hne.
    (* the source side *)
    pose proof Hsrc as Hsrc0.
    eapply assign_lexp_Eapp_inv in Hsrc0
      as (sgL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EsgL & _ & _ & _).
    eapply assign_lexp_Eapp_carried in Hsrc
      as (sgL' & argts & rstty & ckty & cs & EsgL' & _ & Hcar); [|exact Hne].
    rewrite EsgL in EsgL'. inversion EsgL'; subst sgL'.
    (* the target side: the emitted equation, whose reset is a variable *)
    destruct Hshape as [Hnone|(v & an & Hsome)]; subst er''.
    - rewrite gen_leqn_Eapp in Htgt.
      eapply generate_lcall_constraint_inv in Htgt
        as (sgN & ckt & argt & outt & sti & cs0 & EsgN & _ & _ & _ & Hgc & Hce).
      exists sgL, sgN. repeat split; auto.
      + exists argts, rstty, cs. exact Hcar.
      + exists argt, (lvar rst_ty), ckt, outt, cs0, sti, xst'.
        split; [exact Hgc|exact Hce].
    - destruct an as [ty [ckr nm]].
      rewrite gen_leqn_Eapp_reset in Htgt.
      eapply sec_bind_inv in Htgt as (rty & sta & Hrty & Htgt).
      eapply sec_bind_inv in Htgt as (rstck & stb & Hrstck & Htgt).
      eapply generate_lcall_constraint_inv in Htgt
        as (sgN & ckt & argt & outt & sti & cs0 & EsgN & _ & _ & _ & Hgc & Hce).
      exists sgL, sgN. repeat split; auto.
      + exists argts, rstty, cs. exact Hcar.
      + exists argt, (ljoin (lvar rst_ty) (merge [rty] rstck, [])), ckt, outt,
               cs0, sti, xst'.
        split; [exact Hgc|exact Hce].
  Qed.

  (** * The cases where nothing is introduced

      [Eunop], [Ebinop] and [Ewhen] do not lift: unnesting rebuilds the
      expression and emits exactly what its sub-expressions emitted, and the
      typer carries exactly what its sub-expressions carried.  Nothing is
      minted on either side, so these cases of the induction are inherited
      rather than argued -- the renaming stays empty through them. *)

  Lemma unnest_exp_Eunop_inv :
    forall G is_control op e1 an es' eqs st st',
      unnest_exp G is_control (Eunop op e1 an) st = ((es', eqs), st') ->
      exists e1' st1,
        unnest_exp G false e1 st = ((e1', eqs), st1)
        /\ st' = st1
        /\ es' = [Eunop op (hd_default e1') an].
  Proof.
    intros G is_control op e1 an es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Ebinop_inv :
    forall G is_control op e1 e2 an es' eqs st st',
      unnest_exp G is_control (Ebinop op e1 e2 an) st = ((es', eqs), st') ->
      exists e1' eqs1 st1 e2' eqs2,
        unnest_exp G false e1 st = ((e1', eqs1), st1)
        /\ unnest_exp G false e2 st1 = ((e2', eqs2), st')
        /\ eqs = eqs1 ++ eqs2
        /\ es' = [Ebinop op (hd_default e1') (hd_default e2') an].
  Proof.
    intros G is_control op e1 e2 an es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_exp_Ewhen_inv :
    forall G is_control es ckid b tys ck es' eqs st st',
      unnest_exp G is_control (Ewhen es ckid b (tys, ck)) st
        = ((es', eqs), st') ->
      exists es1,
        unnest_exps G es st = ((es1, eqs), st')
        /\ es' = unnest_when ckid b es1 tys ck.
  Proof.
    intros G is_control es ckid b tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind.
    repeat esplit; eauto.
    unfold unnest_exps. apply bind2_spec.
    repeat esplit; eauto using ret_spec.
  Qed.

  (** And the typer's side of the same three: the unary case is literally its
      operand's, and the other two carry the merge of their operands'. *)

  Lemma assign_lexp_Eunop_inv :
    forall G env base_ty rst_ty op e1 an ts st st',
      assign_lexp_type G env base_ty rst_ty (Eunop op e1 an) st = OK (ts, st') ->
      assign_lexp_type G env base_ty rst_ty e1 st = OK (ts, st').
  Proof. intros. exact H. Qed.

  Lemma assign_lexp_Ewhen_carried :
    forall G env base_ty rst_ty es x b tys ck ts st st',
      assign_lexp_type G env base_ty rst_ty (Ewhen es x b (tys, ck)) st
        = OK (ts, st') ->
      exists us g,
        assign_lexps G env base_ty rst_ty es st = OK (us, st')
        /\ Env.find x env = Some g
        /\ ts = List.map (fun t => ljoin t (lvar g)) us.
  Proof.
    intros G env base_ty rst_ty es x b tys ck ts st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (us & sta & Hus & H).
    eapply sec_bind_inv in H as (g & stb & Hg & Hret).
    apply find_env_inv in Hg as [Hg Hst]; subst stb.
    unfold ret in Hret. inv Hret.
    exists us, g. repeat split; auto.
  Qed.

  (** * The renaming, constructed

      For a call the two sides' residual types are both lists of singletons:
      the typer gives each result the singleton of its minted name, unnesting
      gives each result an [Evar] on the variable it took.  So the renaming is
      the pairing of those two lists, and both have length [length anns].

      Nothing more is needed of it than that pairing.
      [subst_constraints_out_map] renames occurrences of the first list by the
      second *inside the left-hand sides as well as at the targets*
      ([subst_ident_constraint] rewrites [ty] and [x'] together), so putting a
      defining constraint into the set renames the type inside it too.  That is
      why the induction does not have to carry a separate claim about types:
      a type only ever appears inside a constraint, and the renaming reaches
      it there. *)

  Lemma assign_lexp_Eapp_result_types :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st
        = OK (ts, st') ->
      exists outs,
        List.length outs = List.length anns
        /\ List.map fst ts = List.map (fun o => ([o] : ST)) outs.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    eapply assign_lexp_Eapp_inv in H
      as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
          & _ & _ & _ & _ & Houts & _ & Hts).
    exists outs. split.
    - eapply fresh_idents_length; eauto.
    - subst ts. now rewrite !map_map.
  Qed.

  Lemma unnest_exp_Eapp_result_vars :
    forall G is_control f es er anns es' eqs st st',
      unnest_exp G is_control (Eapp f es er anns) st = ((es', eqs), st') ->
      exists xs,
        List.length xs = List.length anns
        /\ es' = List.map (fun '(id, an) => Evar id an) xs.
  Proof.
    intros G is_control f es er anns es' eqs st st' H.
    eapply unnest_exp_Eapp_inv in H
      as (es1 & eqs1 & st1 & es2 & eqs2 & st2 & er' & eqs3 & st3 & xs
          & _ & _ & _ & Hxs & Hes' & _).
    exists xs. split; [|exact Hes'].
    eapply idents_for_anns'_length; eauto.
  Qed.

  (** The two lists to be paired, with the pairing's defining property: they
      are the same length, so [subst_constraints_out_map] can consume them. *)

  Corollary Eapp_renaming_lists :
    forall G env base_ty rst_ty G' is_control f es er anns
           ts st st' es' eqs sst sst',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st
        = OK (ts, st') ->
      unnest_exp G' is_control (Eapp f es er anns) sst = ((es', eqs), sst') ->
      exists outs xs,
        List.map fst ts = List.map (fun o => ([o] : ST)) outs
        /\ es' = List.map (fun '(id, an) => Evar id an) xs
        /\ List.length outs = List.length (List.map fst xs).
  Proof.
    intros G env base_ty rst_ty G' is_control f es er anns
           ts st st' es' eqs sst sst' Hsrc Htgt.
    eapply assign_lexp_Eapp_result_types in Hsrc as (outs & Hlo & Hts).
    eapply unnest_exp_Eapp_result_vars in Htgt as (xs & Hlx & Hes').
    exists outs, xs. repeat split; auto.
    rewrite map_length. congruence.
  Qed.

  (** * Renaming a type

      [subst_constraints_out_map] reaches types that sit inside constraints,
      but the induction also meets a type on its own: a call's actual argument
      types are handed to [generate_constraints], which substitutes them for
      the callee's formals.  So the renaming has to apply to a bare [ST] too.

      That is not a new substitution.  [SIG.subst_ident_in_type] is the
      primitive -- the one [subst_ident_constraint] is built from -- and the
      list-wise version is its fold, shaped exactly like
      [subst_constraints_inp_map]. *)

  Fixpoint subst_idents_in_type (ty : ST) (xs vs : list ident) : ST :=
    match xs, vs with
    | x :: xs', v :: vs' =>
        subst_idents_in_type (SIG.subst_ident_in_type ty x [v]) xs' vs'
    | _, _ => ty
    end.

  Lemma subst_ident_in_type_notin :
    forall ty x v, ~ In x ty -> SIG.subst_ident_in_type ty x v = ty.
  Proof.
    intros ty x v Hnin. unfold SIG.subst_ident_in_type.
    destruct (SymTypes.my_set_mem x ty) eqn:Em; [|reflexivity].
    exfalso. apply Hnin. now apply SymTypes.my_set_mem_correct.
  Qed.

  (** What the cases that mint nothing need: a type mentioning none of the
      renamed names is left alone, so the renaming really is the identity
      through [Eunop], [Ebinop], [Ewhen] and the base cases. *)

  Lemma subst_idents_in_type_notin :
    forall xs vs ty,
      (forall x, In x xs -> ~ In x ty) ->
      subst_idents_in_type ty xs vs = ty.
  Proof.
    induction xs as [|x xs IH]; intros vs ty Hnin; simpl.
    - reflexivity.
    - destruct vs as [|v vs]; [reflexivity|].
      rewrite subst_ident_in_type_notin by (apply Hnin; now left).
      apply IH. intros y Hy. apply Hnin. now right.
  Qed.

  Corollary subst_idents_in_type_nil :
    forall ty vs, subst_idents_in_type ty [] vs = ty.
  Proof. reflexivity. Qed.

  (** * Composing renamings

      A constructor that combines sub-expressions inherits their renamings, so
      the induction has to concatenate them.  Both levels compose the way the
      folds are written -- renaming by [xs1 ++ xs2] is renaming by [xs1] and
      then by [xs2] -- and at the constraint level the composition is exactly
      the monadic sequencing the fixpoint already performs. *)

  Lemma subst_idents_in_type_app :
    forall xs1 vs1 xs2 vs2 ty,
      List.length xs1 = List.length vs1 ->
      subst_idents_in_type ty (xs1 ++ xs2) (vs1 ++ vs2)
      = subst_idents_in_type (subst_idents_in_type ty xs1 vs1) xs2 vs2.
  Proof.
    induction xs1 as [|x xs1 IH]; intros vs1 xs2 vs2 ty Hlen.
    - destruct vs1; [reflexivity|simpl in Hlen; discriminate].
    - destruct vs1 as [|v vs1]; [simpl in Hlen; discriminate|].
      simpl. apply IH. simpl in Hlen. congruence.
  Qed.

  Lemma subst_constraints_out_map_app :
    forall xs1 vs1 xs2 vs2 cs cs1 cs2 st st1 st2,
      subst_constraints_out_map cs xs1 vs1 st = OK (cs1, st1) ->
      subst_constraints_out_map cs1 xs2 vs2 st1 = OK (cs2, st2) ->
      subst_constraints_out_map cs (xs1 ++ xs2) (vs1 ++ vs2) st = OK (cs2, st2).
  Proof.
    induction xs1 as [|x xs1 IH]; intros vs1 xs2 vs2 cs cs1 cs2 st st1 st2 H1 H2.
    - destruct vs1 as [|v vs1]; simpl in H1; [|discriminate].
      unfold ret in H1. inv H1. exact H2.
    - destruct vs1 as [|v vs1]; simpl in H1; [discriminate|].
      simpl.
      destruct (SymTypes.findST cs v) eqn:Ef; [discriminate|].
      eapply sec_bind_inv in H1 as (cs' & sta & Hhd & Htl).
      eapply sec_bind_ok; [exact Hhd|].
      eapply IH; eauto.
  Qed.

  (** And the degenerate case the non-lifting constructors land in: renaming by
      nothing is the identity, at both levels. *)

  Lemma subst_constraints_out_map_nil :
    forall cs st, subst_constraints_out_map cs [] [] st = OK (cs, st).
  Proof. intros. reflexivity. Qed.

  (** * Domination

      The relation between a source type and the target type that replaces it
      is not equality and not a renaming: the target is a name the emitted
      equation constrains to sit *above* the source's type.  That is
      [SecTypes.satisfiable] -- [hm_ext dlt s0 ⊑ hm_ext dlt s1] -- so no new
      notion is needed, only its arithmetic.

      These are the steps the induction takes: a target name dominates the
      operands it was built from, and domination composes along a chain of
      sub-expressions. *)

  Lemma satisfiable_refl :
    forall dlt s, satisfiable dlt s s.
  Proof. intros dlt s. unfold satisfiable. apply Lat.order_refl, Lat.eq_refl. Qed.

  Lemma satisfiable_trans :
    forall dlt a b c,
      satisfiable dlt a b -> satisfiable dlt b c -> satisfiable dlt a c.
  Proof.
    intros dlt a b c Hab Hbc. unfold satisfiable in *.
    eapply Lat.order_trans; eauto.
  Qed.

  (** A merge dominates each of its sides, and is dominated by anything that
      dominates both -- which is how a defining constraint of the form
      [ambient ⊔ t ⊑ b] is taken apart and put back together. *)

  Lemma satisfiable_merge_l :
    forall dlt a b, satisfiable dlt a (merge a b).
  Proof.
    intros dlt a b. unfold satisfiable.
    rewrite hm_ext_merge_eq. apply Lat.join_bound1.
  Qed.

  Lemma satisfiable_merge_r :
    forall dlt a b, satisfiable dlt b (merge a b).
  Proof.
    intros dlt a b. unfold satisfiable.
    rewrite hm_ext_merge_eq. apply Lat.join_bound2.
  Qed.

  Lemma satisfiable_merge_intro :
    forall dlt a b c,
      satisfiable dlt a c -> satisfiable dlt b c -> satisfiable dlt (merge a b) c.
  Proof.
    intros dlt a b c Ha Hb. unfold satisfiable in *.
    rewrite hm_ext_merge_eq. now apply Lat.join_least_upper_bound.
  Qed.

  (** So a name constrained above a merge dominates each side of it -- the step
      that carries a source operand's type up to the variable unnesting
      created for the whole expression. *)

  Corollary satisfiable_through_merge_l :
    forall dlt a b c, satisfiable dlt (merge a b) c -> satisfiable dlt a c.
  Proof.
    intros dlt a b c H. eapply satisfiable_trans; [apply satisfiable_merge_l|exact H].
  Qed.

  Corollary satisfiable_through_merge_r :
    forall dlt a b c, satisfiable dlt (merge a b) c -> satisfiable dlt b c.
  Proof.
    intros dlt a b c H. eapply satisfiable_trans; [apply satisfiable_merge_r|exact H].
  Qed.

  (** And the form a defining constraint arrives in: [constraintSatisfiable]
      on [(lhs, [b])] is exactly domination of [b] over [lhs]. *)

  Lemma constraint_is_domination :
    forall dlt lhs b,
      constraintSatisfiable dlt (lhs, [b]) <-> satisfiable dlt lhs [b].
  Proof. intros. split; intro H; exact H. Qed.

  (** * How carried constraints propagate

      Every constructor but the call builds its result types with [ljoin],
      [ljoin_list] or [lvar], and none of those creates a constraint -- they
      merge what their operands were already carrying.  So a constructor's
      carried set is the merge of its operands' carried sets, and an
      expression carries something exactly when a call occurs inside it.

      That is the precise form of the observation that opened this leg: the
      refinement component is empty until a nested call puts something in it,
      and [to_lexps_assign_rev] saw it empty on the transcription leg because
      by then the calls had all been lifted out. *)

  Lemma carried_ljoin :
    forall a b, carried [ljoin a b] = cmerge (snd a) (snd b).
  Proof.
    intros a b. simpl. unfold ljoin. simpl. apply cmerge_nil.
  Qed.

  Lemma ljoin_list_carried :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') ->
      carried rs = cmerge (carried ts) (carried us).
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us as [|u us]; simpl in H; [|discriminate].
      unfold ret in H. inv H. reflexivity.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sta & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl. rewrite (IH _ _ _ _ Hr). unfold ljoin. simpl.
      rewrite <- !cmerge_assoc. f_equal.
      rewrite !cmerge_assoc. f_equal. apply cmerge_comm.
  Qed.

  (** A variable and a constant carry nothing, so the leaves contribute
      nothing and the whole propagation bottoms out. *)

  Lemma carried_lvar : forall d, carried [lvar d] = [].
  Proof. reflexivity. Qed.

  Lemma carried_lbot : carried [lbot] = [].
  Proof. reflexivity. Qed.


  (** * The clock environment survives the pass

      [generate_leqns_constraints] does not read the equations alone: through
      [eqn_clock_type] it looks every defined variable up in the node's
      [lnode_clock_env] to recover the clock it is defined on.  So comparing
      the two generators equation by equation is only meaningful once the two
      environments are known to answer the same way.

      Unnesting leaves [n_in] and [n_out] untouched and only *appends* to
      [n_vars].  Extension by itself would not be enough -- [Env.adds'] lets a
      later binding shadow an earlier one, so an appended name colliding with
      a declared one would silently change the answer -- but the target node
      carries its own [n_nodup], and that is exactly the statement that the
      appended names are fresh for the declared ones.  Freshness is therefore
      not assumed here; it is read off the node the pass returns. *)

  Lemma Env_find_adds'_app_notin {A : Type} :
    forall (xs ys : list (ident * A)) (m : Env.t A) x,
      ~ InMembers x ys ->
      Env.find x (Env.adds' (xs ++ ys) m) = Env.find x (Env.adds' xs m).
  Proof.
    intros * Hnin. rewrite <- Env.adds'_app. now apply Env.gsso'.
  Qed.

  (** The disjointness, stated on the shape of the pass rather than on its
      code: any node whose inputs and outputs are the source's and whose
      locals extend the source's has its extension fresh for the source. *)

  Lemma unnested_locals_fresh :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        ~ InMembers x nvars.
  Proof.
    intros n n' nvars Hin Hout Hvars x Hx.
    pose proof (n_nodup n') as Hnd.
    rewrite Hin, Hout, Hvars in Hnd.
    assert (Permutation (n_in n ++ (n_vars n ++ nvars) ++ n_out n
                           ++ anon_in_eqs (n_eqs n'))
                        ((n_in n ++ n_vars n ++ n_out n)
                           ++ nvars ++ anon_in_eqs (n_eqs n'))) as Hp.
    { repeat rewrite <- app_assoc.
      apply Permutation_app_head, Permutation_app_head, Permutation_swap. }
    rewrite Hp in Hnd.
    eapply NoDupMembers_app_InMembers in Hnd; [|exact Hx].
    intros Hn; apply Hnd, InMembers_app; auto.
  Qed.

  (** Hence the two generators read the same clocks. *)

  Lemma lnode_clock_env_extended :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        Env.find x (lnode_clock_env n') = Env.find x (lnode_clock_env n).
  Proof.
    intros n n' nvars Hin Hout Hvars x Hx.
    unfold lnode_clock_env. rewrite Hin, Hout, Hvars.
    apply Env_find_adds'_app_notin.
    eapply unnested_locals_fresh; eauto.
  Qed.

  (** What the equation level actually consumes: [find_clock], and through it
      [eqn_clock_type], cannot tell the two environments apart. *)

  Corollary find_clock_extended :
    forall n n' nvars,
      n'.(n_in)   = n.(n_in) ->
      n'.(n_out)  = n.(n_out) ->
      n'.(n_vars) = n.(n_vars) ++ nvars ->
      forall x,
        InMembers x (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
        find_clock (lnode_clock_env n') x = find_clock (lnode_clock_env n) x.
  Proof.
    intros. unfold find_clock.
    erewrite lnode_clock_env_extended; eauto.
  Qed.


  (** * The expression-level statement

      One valuation goes in, one comes out.  [dlt] satisfies what the source
      expression *carries* -- the constraints its nested calls impose on the
      fresh names the security monad minted for them.  [dlt'] satisfies what
      unnesting *emitted* -- the constraints generated for the equations the
      pass lifted out.  The two differ only off [scope]: on every security
      name the source node can see they are the same valuation, which is what
      makes this composable with the rest of the node.

      The third conjunct is the part that took the longest to get right.  It
      is not "the two sides give the expression the same type": in four of the
      five lifting cases the pass replaces a compound expression by a variable
      whose defining equation carries an ambient (the reset level joined with
      the clock the variable is defined on), so the target type is the source
      type *raised by that ambient*.  Domination in this direction --
      target below source-plus-ambient -- is exactly what the enclosing
      equation needs, because the enclosing equation sits under the same
      ambient and so absorbs it.

      [amb] is a parameter rather than a computed term: which ambient a lifted
      equation sits under is a fact about clocks, and is discharged where the
      clocks are known, not here. *)

  (** * A one-element list, and what the typer does with it

      Stated at module level rather than inside the preservation section:
      these are facts about the generator, not about the pass. *)

  Lemma assign_lexps_single :
    forall G env base_ty rst_ty e ts st st',
      assign_lexps G env base_ty rst_ty [e] st = OK (ts, st') ->
      assign_lexp_type G env base_ty rst_ty e st = OK (ts, st').
  Proof.
    intros G env base_ty rst_ty e ts st st' H.
    apply assign_lexps_carried_cons in H as (t & r & sta & Ht & Hr & Hts & _).
    apply assign_lexps_carried_nil in Hr as (Hr & _ & ?); subst.
    now rewrite app_nil_r.
  Qed.

  Lemma assign_lexps_single_intro :
    forall G env base_ty rst_ty e ts st st',
      assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
      assign_lexps G env base_ty rst_ty [e] st = OK (ts, st').
  Proof.
    intros G env base_ty rst_ty e ts st st' H.
    rewrite assign_lexps_cons.
    eapply sec_bind_ok; [exact H|].
    eapply sec_bind_ok with (y := ([] : list LST));
      [rewrite assign_lexps_nil; reflexivity|].
    unfold ret. now rewrite app_nil_r.
  Qed.

  Lemma fst_ljoin : forall a b, fst (ljoin a b) = merge (fst a) (fst b).
  Proof. reflexivity. Qed.

  Lemma fst_lvar : forall d, fst (lvar d) = [d].
  Proof. reflexivity. Qed.

  Lemma single_inv :
    forall (ts : list LST) t st st',
      single ts st = OK (t, st') -> ts = [t] /\ st' = st.
  Proof.
    intros ts t st st' H. unfold single in H.
    destruct ts as [|t0 [|]]; try discriminate.
    unfold ret in H. inv H. auto.
  Qed.

  (** * What the typer does to an already-unnested expression

      Unnesting returns normalized expressions, and a normalized expression
      contains no call.  The call case is the *only* place the security
      generator touches its state, so on the pass's output the generator is
      state-pure, and a normalized expression is given exactly one flow.

      Both facts are about what the generator does on the target side, and
      both are what let the target's types be read off in whatever order a
      constructor happens to visit its operands -- [unnest_merge] interleaves
      the two branches, where [assign_lexps] would take one branch then the
      other. *)

  Lemma carried_single : forall t, carried [t] = snd t.
  Proof. intros t. simpl. apply cmerge_nil. Qed.

  Lemma ljoin_list_pure :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') -> st' = st.
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us; simpl in H; [|discriminate].
      unfold ret in H. now inv H.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sta & Hr & Hret).
      unfold ret in Hret. inv Hret. eauto.
  Qed.

  Lemma assign_lexp_normalized_lexp_pure :
    forall G env base_ty rst_ty e,
      normalized_lexp e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        st' = st /\ List.length ts = 1 /\ carried ts = []
        /\ forall s, assign_lexp_type G env base_ty rst_ty e s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty e Hn.
    induction Hn; intros ts st st' H.
    - rewrite assign_lexp_Econst in H. unfold ret in H. inv H.
      split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
      intros s. now rewrite assign_lexp_Econst.
    - apply assign_lexp_Evar_inv in H as (b & Hb & ? & ?); subst.
      split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
      intros s. rewrite assign_lexp_Evar.
      eapply sec_bind_ok; [apply find_env_OK; exact Hb|]. reflexivity.
    - rewrite assign_lexp_Eunop in H. apply IHHn in H as (Ha & Hl & Hc & Hs).
      split; [exact Ha|split; [exact Hl|split; [exact Hc|]]].
      intros s. rewrite assign_lexp_Eunop. apply Hs.
    - rewrite assign_lexp_Ebinop in H.
      eapply sec_bind_inv in H as (t1 & sa & Ht1 & H).
      eapply sec_bind_inv in H as (t2 & sb & Ht2 & H).
      eapply sec_bind_inv in H as (a1 & sc & Ha1 & H).
      eapply sec_bind_inv in H as (a2 & sd & Ha2 & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Ha1 as (? & ?); subst.
      apply single_inv in Ha2 as (? & ?); subst.
      apply IHHn1 in Ht1 as (? & _ & Hc1 & Hs1); subst.
      apply IHHn2 in Ht2 as (? & _ & Hc2 & Hs2); subst.
      rewrite carried_single in Hc1, Hc2.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single. unfold ljoin. simpl snd.
        rewrite Hc1, Hc2. reflexivity.
      + intros s. rewrite assign_lexp_Ebinop.
        eapply sec_bind_ok; [apply Hs1|].
        eapply sec_bind_ok; [apply Hs2|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|]. reflexivity.
    - rewrite assign_lexp_Ewhen in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      apply find_env_inv in Hg as (Hgf & ?); subst.
      apply assign_lexps_single in Ht.
      apply IHHn in Ht as (? & Hlen & Hc & Hs); subst.
      destruct t as [|a [|]]; simpl in Hlen; try discriminate.
      split; [reflexivity|split; [reflexivity|split]].
      + simpl List.map. rewrite carried_single.
        rewrite carried_single in Hc.
        unfold ljoin. simpl snd. rewrite Hc. apply cmerge_nil.
      + intros s. rewrite assign_lexp_Ewhen.
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hs|].
        eapply sec_bind_ok; [apply find_env_OK; exact Hgf|]. reflexivity.
  Qed.

  Lemma assign_lexp_normalized_cexp_pure :
    forall G env base_ty rst_ty e,
      normalized_cexp e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        st' = st /\ List.length ts = 1 /\ carried ts = []
        /\ forall s, assign_lexp_type G env base_ty rst_ty e s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty e Hn.
    induction Hn as [x et ef ty cl Het IHet Hef IHef
                    | e1 et ef ty cl Hle Het IHet Hef IHef
                    | e1 Hle];
      intros ts st st' Hty.
    - rewrite assign_lexp_Emerge in Hty.
      eapply sec_bind_inv in Hty as (g & sa & Hg & Hty).
      eapply sec_bind_inv in Hty as (t & sb & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sc & Hu & Hj).
      apply find_env_inv in Hg as (Hgf & ?); subst.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      apply IHet in Ht as (? & Hlt & Hct & Hst); subst.
      apply IHef in Hu as (? & Hlu & Hcu & Hsu); subst.
      assert (st' = st) as ? by (eapply ljoin_list_pure; eauto); subst.
      destruct t as [|t0 [|]]; simpl in Hlt; try discriminate.
      destruct u as [|u0 [|]]; simpl in Hlu; try discriminate.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sd & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      rewrite carried_single in Hct, Hcu.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single.
        unfold ljoin, lvar. simpl snd. rewrite Hct, Hcu. reflexivity.
      + intros s. rewrite assign_lexp_Emerge.
        eapply sec_bind_ok; [apply find_env_OK; exact Hgf|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hst|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hsu|].
        reflexivity.
    - rewrite assign_lexp_Eite in Hty.
      eapply sec_bind_inv in Hty as (t0 & sa & Ht0 & Hty).
      eapply sec_bind_inv in Hty as (th & sb & Hth & Hty).
      eapply sec_bind_inv in Hty as (t & sc & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sd & Hu & Hj).
      apply single_inv in Hth as (? & ?); subst.
      assert (sa = st /\ List.length [th] = 1 /\ carried [th] = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s
                            = OK ([th], s))
        as (? & _ & Hcth & Hsth)
        by (eapply assign_lexp_normalized_lexp_pure with (e := e1); eauto).
      subst sa.
      rewrite carried_single in Hcth.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      apply IHet in Ht as (? & Hlt & Hct & Hst); subst.
      apply IHef in Hu as (? & Hlu & Hcu & Hsu); subst.
      assert (st' = st) as ? by (eapply ljoin_list_pure; eauto); subst.
      destruct t as [|t1 [|]]; simpl in Hlt; try discriminate.
      destruct u as [|u1 [|]]; simpl in Hlu; try discriminate.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & se & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      rewrite carried_single in Hct, Hcu.
      split; [reflexivity|split; [reflexivity|split]].
      + rewrite carried_single. unfold ljoin. simpl snd.
        rewrite Hct, Hcu, Hcth. reflexivity.
      + intros s. rewrite assign_lexp_Eite.
        eapply sec_bind_ok; [apply Hsth|].
        eapply sec_bind_ok; [unfold single, SC.ret; reflexivity|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hst|].
        eapply sec_bind_ok; [apply assign_lexps_single_intro, Hsu|].
        reflexivity.
    - eapply assign_lexp_normalized_lexp_pure; eauto.
  Qed.

  Lemma assign_lexps_normalized_pure :
    forall G env base_ty rst_ty es,
      Forall normalized_cexp es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        st' = st /\ List.length ts = List.length es /\ carried ts = []
        /\ forall s, assign_lexps G env base_ty rst_ty es s = OK (ts, s).
  Proof.
    intros G env base_ty rst_ty es Hn.
    induction Hn as [|e es He Hes IH]; intros ts st st' H.
    - apply assign_lexps_carried_nil in H as (? & Hc & ?); subst.
      split; [reflexivity|split; [reflexivity|split; [exact Hc|]]].
      intros s. now rewrite assign_lexps_nil.
    - apply assign_lexps_carried_cons in H
        as (t & r & sta & Ht & Hr & ? & Hct); subst.
      eapply assign_lexp_normalized_cexp_pure in Ht as (? & Hlt & Hc1 & Hs1);
        eauto; subst.
      apply IH in Hr as (? & Hlr & Hc2 & Hs2); subst.
      split; [reflexivity|split; [|split]].
      + rewrite app_length, Hlt, Hlr. reflexivity.
      + rewrite Hct, Hc1, Hc2. reflexivity.
      + intros s. rewrite assign_lexps_cons.
        eapply sec_bind_ok; [apply Hs1|].
        eapply sec_bind_ok; [apply Hs2|]. reflexivity.
  Qed.

  (** Under [is_control] the merge does not lift: the branches are unnested
      and the sampling is pushed inward, one [Emerge] per resulting stream,
      exactly as [Ewhen] pushes its own. *)

  Lemma unnest_exp_Emerge_control_inv :
    forall G ckid es1 es2 tys cl es' eqs st st',
      unnest_exp G true (Emerge ckid es1 es2 (tys, cl)) st = ((es', eqs), st') ->
      exists es1' eqs1 st1 es2' eqs2,
        map_bind2 (unnest_exp G true) es1 st = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st')
        /\ es' = unnest_merge ckid (List.concat es1') (List.concat es2') tys cl
        /\ eqs = List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G ckid es1 es2 tys cl es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_merge_nil :
    forall ckid es2 tys cl, unnest_merge ckid [] es2 tys cl = [].
  Proof. reflexivity. Qed.

  Lemma unnest_merge_cons :
    forall ckid e1 es1 e2 es2 ty tys cl,
      unnest_merge ckid (e1 :: es1) (e2 :: es2) (ty :: tys) cl
      = Emerge ckid [e1] [e2] ([ty], cl) :: unnest_merge ckid es1 es2 tys cl.
  Proof. reflexivity. Qed.

  (** And the typer reads it back as the same function of the branches'
      types that the source rule is of the source branches' types.  Purity is
      what makes the interleaving harmless: every sub-call starts and ends at
      the state the whole list started at. *)

  Lemma assign_lexps_unnest_merge_inv :
    forall G env base_ty rst_ty ckid cl g (es1 es2 : list exp)
           (tys : list type) ts'' st st',
      Env.find ckid env = Some g ->
      Forall normalized_cexp es1 ->
      Forall normalized_cexp es2 ->
      List.length es1 = List.length tys ->
      List.length es2 = List.length tys ->
      assign_lexps G env base_ty rst_ty (unnest_merge ckid es1 es2 tys cl) st
        = OK (ts'', st') ->
      exists ts us,
        assign_lexps G env base_ty rst_ty es1 st = OK (ts, st)
        /\ assign_lexps G env base_ty rst_ty es2 st = OK (us, st)
        /\ st' = st
        /\ ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us st
           = OK (ts'', st).
  Proof.
    intros G env base_ty rst_ty ckid cl g es1.
    induction es1 as [|e1 es1 IH];
      intros es2 tys ts'' st st' Hg Hn1 Hn2 Hl1 Hl2 Has.
    - destruct tys; simpl in Hl1; try discriminate.
      destruct es2; simpl in Hl2; try discriminate.
      rewrite unnest_merge_nil in Has.
      apply assign_lexps_carried_nil in Has as (? & _ & ?); subst.
      exists [], []. rewrite assign_lexps_nil. repeat split; reflexivity.
    - destruct tys as [|ty tys]; simpl in Hl1; try discriminate.
      destruct es2 as [|e2 es2]; simpl in Hl2; try discriminate.
      inv Hn1. inv Hn2.
      rewrite unnest_merge_cons in Has.
      apply assign_lexps_carried_cons in Has
        as (t0 & r & sta & Ht0 & Hr & ? & _); subst.
      (** the head merge *)
      rewrite assign_lexp_Emerge in Ht0.
      eapply sec_bind_inv in Ht0 as (g' & sa & Hg' & Ht0).
      eapply sec_bind_inv in Ht0 as (t & sb & Ht & Ht0).
      eapply sec_bind_inv in Ht0 as (u & sc & Hu & Hj).
      apply find_env_inv in Hg' as (Hg' & ?); subst.
      rewrite Hg in Hg'. inv Hg'.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      assert (sb = st /\ List.length t = 1 /\ carried t = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s = OK (t, s))
        as (? & Hlt & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
      subst sb.
      assert (sc = st /\ List.length u = 1 /\ carried u = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e2 s = OK (u, s))
        as (? & Hlu & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
      subst sc.
      assert (sta = st) as ? by (eapply ljoin_list_pure; eauto). subst sta.
      apply IH in Hr as (ts & us & Hts & Hus & ? & Hjr); auto; subst.
      exists (t ++ ts), (u ++ us). split; [|split; [|split]]; auto.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [exact Hts|]. reflexivity.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Hu|].
        eapply sec_bind_ok; [exact Hus|]. reflexivity.
      + destruct t as [|a [|]]; simpl in Hlt; try discriminate.
        destruct u as [|b [|]]; simpl in Hlu; try discriminate.
        simpl List.map. simpl List.app.
        eapply sec_bind_ok; [exact Hjr|].
        simpl in Hj.
        eapply sec_bind_inv in Hj as (r0 & sd & Hr0 & Hret).
        unfold ret in Hret. inv Hret.
        simpl in Hr0. unfold ret in Hr0. inv Hr0. reflexivity.
  Qed.

  Lemma unnest_exp_Eite_control_inv :
    forall G e es1 es2 tys ck es' eqs st st',
      unnest_exp G true (Eite e es1 es2 (tys, ck)) st = ((es', eqs), st') ->
      exists e' eqs0 st0 es1' eqs1 st1 es2' eqs2,
        unnest_exp G false e st = ((e', eqs0), st0)
        /\ map_bind2 (unnest_exp G true) es1 st0 = ((es1', eqs1), st1)
        /\ map_bind2 (unnest_exp G true) es2 st1 = ((es2', eqs2), st')
        /\ es' = unnest_ite (hd_default e') (List.concat es1')
                   (List.concat es2') tys ck
        /\ eqs = eqs0 ++ List.concat eqs1 ++ List.concat eqs2.
  Proof.
    intros G e es1 es2 tys ck es' eqs st st' H.
    simpl in H. repeat inv_bind. repeat esplit; eauto.
  Qed.

  Lemma unnest_ite_nil :
    forall e es2 tys ck, unnest_ite e [] es2 tys ck = [].
  Proof. reflexivity. Qed.

  Lemma unnest_ite_cons :
    forall e e1 es1 e2 es2 ty tys ck,
      unnest_ite e (e1 :: es1) (e2 :: es2) (ty :: tys) ck
      = Eite e [e1] [e2] ([ty], ck) :: unnest_ite e es1 es2 tys ck.
  Proof. reflexivity. Qed.

  (** The scrutinee is typed once per resulting stream rather than once, but
      it is normalized, so the generator gives it the same answer every time
      and never moves the state.  That is the whole difference from the merge
      inversion above. *)

  Lemma assign_lexps_unnest_ite_inv :
    forall G env base_ty rst_ty e0 ck (es1 es2 : list exp)
           (tys : list type) ts'' st st',
      normalized_lexp e0 ->
      Forall normalized_cexp es1 ->
      Forall normalized_cexp es2 ->
      List.length es1 = List.length tys ->
      List.length es2 = List.length tys ->
      assign_lexps G env base_ty rst_ty (unnest_ite e0 es1 es2 tys ck) st
        = OK (ts'', st') ->
      st' = st
      /\ exists ts us,
           assign_lexps G env base_ty rst_ty es1 st = OK (ts, st)
           /\ assign_lexps G env base_ty rst_ty es2 st = OK (us, st)
           /\ ((exists th,
                   assign_lexp_type G env base_ty rst_ty e0 st = OK ([th], st)
                   /\ ljoin_list (List.map (fun t => ljoin th t) ts) us st
                      = OK (ts'', st))
               \/ (ts = [] /\ us = [] /\ ts'' = [])).
  Proof.
    intros G env base_ty rst_ty e0 ck es1.
    induction es1 as [|e1 es1 IH];
      intros es2 tys ts'' st st' Hn0 Hn1 Hn2 Hl1 Hl2 Has.
    - destruct tys; simpl in Hl1; try discriminate.
      destruct es2; simpl in Hl2; try discriminate.
      rewrite unnest_ite_nil in Has.
      apply assign_lexps_carried_nil in Has as (? & _ & ?); subst.
      split; auto. exists [], []. rewrite assign_lexps_nil.
      split; [reflexivity|split; [reflexivity|]]. right; auto.
    - destruct tys as [|ty tys]; simpl in Hl1; try discriminate.
      destruct es2 as [|e2 es2]; simpl in Hl2; try discriminate.
      inv Hn1. inv Hn2.
      rewrite unnest_ite_cons in Has.
      apply assign_lexps_carried_cons in Has
        as (t0 & r & sta & Ht0 & Hr & ? & _); subst.
      rewrite assign_lexp_Eite in Ht0.
      eapply sec_bind_inv in Ht0 as (t0' & sa & Ht0' & Ht0).
      eapply sec_bind_inv in Ht0 as (th & sb & Hth & Ht0).
      eapply sec_bind_inv in Ht0 as (t & sc & Ht & Ht0).
      eapply sec_bind_inv in Ht0 as (u & sd & Hu & Hj).
      assert (sa = st /\ List.length t0' = 1 /\ carried t0' = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e0 s
                            = OK (t0', s))
        as (? & _ & _ & _)
        by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
      subst sa.
      apply single_inv in Hth as (? & ?); subst.
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      assert (sc = st /\ List.length t = 1 /\ carried t = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e1 s = OK (t, s))
        as (? & Hlt & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e1); eauto).
      subst sc.
      assert (sd = st /\ List.length u = 1 /\ carried u = []
              /\ forall s, assign_lexp_type G env base_ty rst_ty e2 s = OK (u, s))
        as (? & Hlu & _ & _)
        by (eapply assign_lexp_normalized_cexp_pure with (e := e2); eauto).
      subst sd.
      assert (sta = st) as ? by (eapply ljoin_list_pure; eauto). subst sta.
      apply IH in Hr as (? & ts & us & Hts & Hus & Hrest); auto. subst.
      destruct t as [|a [|]]; simpl in Hlt; try discriminate.
      destruct u as [|b [|]]; simpl in Hlu; try discriminate.
      simpl in Hj.
      eapply sec_bind_inv in Hj as (r0 & se & Hr0 & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr0. unfold ret in Hr0. inv Hr0.
      split; auto.
      exists (a :: ts), (b :: us). split; [|split].
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [exact Hts|]. reflexivity.
      + rewrite assign_lexps_cons.
        eapply sec_bind_ok; [exact Hu|].
        eapply sec_bind_ok; [exact Hus|]. reflexivity.
      + left. exists th. split; [exact Ht0'|].
        simpl List.map.
        eapply sec_bind_ok; [|reflexivity].
        destruct Hrest as [(th' & Hth' & Hjr)|(? & ? & ?)]; subst.
        * rewrite Ht0' in Hth'. inv Hth'. exact Hjr.
        * simpl. reflexivity.
  Qed.

  (** * How many flows the generator returns

      One per stream, exactly as the pass returns one expression per stream.
      Needed wherever the two sides have to be lined up positionally, and at
      the equation level to match a defined variable to its flow. *)

  Lemma ljoin_list_length :
    forall ts us rs st st',
      ljoin_list ts us st = OK (rs, st') -> List.length rs = List.length ts.
  Proof.
    induction ts as [|t ts IH]; intros us rs st st' H.
    - destruct us; simpl in H; [|discriminate].
      unfold ret in H. inv H. reflexivity.
    - destruct us as [|u us]; simpl in H; [discriminate|].
      eapply sec_bind_inv in H as (r & sa & Hr & Hret).
      unfold ret in Hret. inv Hret. simpl. f_equal. eauto.
  Qed.

  Lemma assign_lexps_length_aux :
    forall P G env base_ty rst_ty es,
      Forall (fun e => wl_exp P e -> forall ts st st',
                  assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
                  List.length ts = numstreams e) es ->
      Forall (wl_exp P) es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        List.length ts = List.length (annots es).
  Proof.
    intros P G env base_ty rst_ty es Hall.
    induction Hall as [|e es He Hes IH]; intros Hwl ts st st' H.
    - apply assign_lexps_carried_nil in H as (? & _ & ?); subst. reflexivity.
    - inv Hwl.
      apply assign_lexps_carried_cons in H as (t & r & sta & Ht & Hr & ? & _);
        subst.
      unfold annots. simpl List.flat_map. fold (annots es).
      rewrite !app_length. f_equal.
      + rewrite length_annot_numstreams. eapply He; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma assign_lexp_type_length :
    forall P G env base_ty rst_ty e,
      wl_exp P e ->
      forall ts st st',
        assign_lexp_type G env base_ty rst_ty e st = OK (ts, st') ->
        List.length ts = numstreams e.
  Proof.
    intros P G env base_ty rst_ty e.
    induction e using exp_ind2; intros Hwl ts st st' Hty; inv Hwl.
    - rewrite assign_lexp_Econst in Hty. unfold ret in Hty. now inv Hty.
    - apply assign_lexp_Evar_inv in Hty as (? & _ & ? & _); subst. reflexivity.
    - rewrite assign_lexp_Eunop in Hty.
      assert (List.length ts = numstreams e) as Hl by (eapply IHe; eauto).
      simpl. rewrite Hl. assumption.
    - rewrite assign_lexp_Ebinop in Hty.
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hty).
      eapply sec_bind_inv in Hty as (? & ? & _ & Hret).
      unfold ret in Hret. now inv Hret.
    - (** fby *)
      rewrite assign_lexp_Efby in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sb & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots e0s)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      rewrite Hl. simpl. assumption.
    - (** arrow *)
      rewrite assign_lexp_Earrow in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sb & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots e0s)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      rewrite Hl. simpl. assumption.
    - (** when *)
      rewrite assign_lexp_Ewhen in Hty.
      eapply sec_bind_inv in Hty as (t & sa & Ht & Hty).
      eapply sec_bind_inv in Hty as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      assert (List.length t = List.length (annots es)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** merge *)
      rewrite assign_lexp_Emerge in Hty.
      eapply sec_bind_inv in Hty as (g & sa & Hg & Hty).
      eapply sec_bind_inv in Hty as (t & sb & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sc & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots ets)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** ite *)
      rewrite assign_lexp_Eite in Hty.
      eapply sec_bind_inv in Hty as (t0 & sa & Ht0 & Hty).
      eapply sec_bind_inv in Hty as (th & sb & Hth & Hty).
      eapply sec_bind_inv in Hty as (t & sc & Ht & Hty).
      eapply sec_bind_inv in Hty as (u & sd & Hu & Hj).
      apply ljoin_list_length in Hj. rewrite Hj.
      assert (List.length t = List.length (annots ets)) as Hl
        by (eapply assign_lexps_length_aux; eauto).
      simpl. rewrite !map_length, Hl. assumption.
    - (** call, and call with a reset: [wl_exp] has a rule for each, and the
          generator does not distinguish them here *)
      apply assign_lexp_Eapp_inv in Hty
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & _ & _ & _ & _ & Houts & _ & ?); subst.
      apply fresh_idents_length in Houts.
      simpl. rewrite map_length. assumption.
    - apply assign_lexp_Eapp_inv in Hty
        as (sg & argts & rstty & ckty & outs & cs & sta & stb & stc
            & _ & _ & _ & _ & Houts & _ & ?); subst.
      apply fresh_idents_length in Houts.
      simpl. rewrite map_length. assumption.
  Qed.

  Corollary assign_lexps_length :
    forall P G env base_ty rst_ty es,
      Forall (wl_exp P) es ->
      forall ts st st',
        assign_lexps G env base_ty rst_ty es st = OK (ts, st') ->
        List.length ts = List.length (annots es).
  Proof.
    intros. eapply assign_lexps_length_aux; eauto.
    apply Forall_forall. intros e He Hwl.
    eapply assign_lexp_type_length; eauto.
  Qed.

  Section Preservation.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.

    (** The source node's variables, with their clocks.  Only the source
        expressions are ever checked against it. *)
    Variable vars    : list (ident * clock).

    (** The *target* node's declared clocks.  [lnode_clock_env_extended] above
        is what says using the target's here loses nothing: on every variable
        the source equations mention, the two environments answer alike. *)
    Variable cenv    : Env.t (type * clock).

    (** Every security name the *source* expression can mention: the names of
        the source node's own variables, and the names the security monad
        mints for its nested calls. *)
    Variable scope   : list ident.

    (** The ambient every equation this expression gets lifted into sits
        under.  A parameter rather than a computed term: *which* ambient a
        lifted equation sits under is a fact about clocks, and belongs where
        the clocks are known.

        The premise that ties it down is deliberately syntactic -- [amb]
        contains the reset level and the clock level of every variable the
        run's emitted equations define, as lists of names.  [hm_ext] is
        monotone under inclusion, so domination follows; and a syntactic
        premise passes to the sub-expressions for free, since their emitted
        equations are a sublist of this one's. *)
    Variable amb     : ST.

    (** A program variable's security name, as the naming pass assigned it. *)
    Definition sec_of (xs : list ident) : list ident :=
      flat_map (fun x => match Env.find x env with
                         | Some b => [b]
                         | None   => []
                         end) xs.

    (** The variables unnesting created during one run, and their security
        names.  Indexed by the *pair* of states, not fixed once for the node:
        two sibling sub-expressions run over disjoint stretches of the fresh
        state, and it is exactly that disjointness that lets one sibling's
        conclusion survive the other's witness. *)
    Definition new_ids (st st' : fresh_st (type * clock)) : list ident :=
      filter (fun x => if in_dec ident_eq_dec x (st_ids st) then false else true)
        (st_ids st').

    Definition moved_by (st st' : fresh_st (type * clock)) : list ident :=
      sec_of (new_ids st st').

    Lemma new_ids_spec :
      forall st st' x,
        In x (new_ids st st') <-> In x (st_ids st') /\ ~ In x (st_ids st).
    Proof.
      intros st st' x. unfold new_ids. rewrite filter_In.
      destruct (in_dec ident_eq_dec x (st_ids st)); split;
        (intros (?&?) || intros ?); try tauto; try discriminate; auto.
    Qed.

    (** Widening a run widens what it may have moved, in both directions:
        a prefix and a suffix of a run both move inside the whole run's set.
        This is what passes the premise down to the sub-expressions and the
        conclusions back up. *)
    Lemma new_ids_prefix :
      forall st st1 st', st_follows st1 st' ->
        incl (new_ids st st1) (new_ids st st').
    Proof.
      intros st st1 st' Hf x Hx. apply new_ids_spec in Hx as (Hx & Hn).
      apply new_ids_spec. split; auto.
      unfold st_ids in *. apply in_map_iff in Hx as ((y&a) & ? & Hin); simpl in *; subst.
      apply in_map_iff. exists (x, a). split; auto.
      eapply st_follows_incl; eauto.
    Qed.

    Lemma new_ids_suffix :
      forall st st1 st', st_follows st st1 ->
        incl (new_ids st1 st') (new_ids st st').
    Proof.
      intros st st1 st' Hf x Hx. apply new_ids_spec in Hx as (Hx & Hn).
      apply new_ids_spec. split; auto.
      intro Hin. apply Hn.
      unfold st_ids in *. apply in_map_iff in Hin as ((y&a) & ? & Hin); simpl in *; subst.
      apply in_map_iff. exists (x, a). split; auto.
      eapply st_follows_incl; eauto.
    Qed.

    Lemma sec_of_incl :
      forall xs ys, incl xs ys -> incl (sec_of xs) (sec_of ys).
    Proof.
      intros xs ys Hincl b Hb.
      unfold sec_of in *. apply in_flat_map in Hb as (x & Hx & Hb).
      apply in_flat_map. exists x. auto.
    Qed.

    Corollary moved_by_prefix :
      forall st st1 st', st_follows st1 st' ->
        incl (moved_by st st1) (moved_by st st').
    Proof. intros. apply sec_of_incl, new_ids_prefix; auto. Qed.

    Corollary moved_by_suffix :
      forall st st1 st', st_follows st st1 ->
        incl (moved_by st1 st') (moved_by st st').
    Proof. intros. apply sec_of_incl, new_ids_suffix; auto. Qed.

    (** The complement of [agree_on]: the two valuations coincide everywhere
        *outside* a set.  This, and not [agree_on], is what the induction can
        carry.  [agree_on scope] says the witness keeps the visible names
        fixed but says nothing about the rest -- and "the rest" includes the
        names the security monad minted for a *sibling* sub-expression, whose
        constraints the sibling's own hypothesis still has to be applied to.
        A witness free to move those cannot be composed with its sibling's.
        Bounding the movement instead makes composition immediate: sibling
        constraints mention [scope] only, and [moved] misses [scope]. *)
    Definition agree_off (xs : list ident) (dlt1 dlt2 : ident -> Lat.t) : Prop :=
      forall x, ~ In x xs -> dlt1 x = dlt2 x.

    Lemma agree_off_refl : forall xs dlt, agree_off xs dlt dlt.
    Proof. intros xs dlt x _. reflexivity. Qed.

    Lemma agree_off_incl :
      forall xs ys dlt dlt',
        incl xs ys -> agree_off xs dlt dlt' -> agree_off ys dlt dlt'.
    Proof. intros xs ys d d' Hincl H x Hx. apply H. auto. Qed.

    Lemma agree_off_trans :
      forall xs dlt1 dlt2 dlt3,
        agree_off xs dlt1 dlt2 -> agree_off xs dlt2 dlt3 ->
        agree_off xs dlt1 dlt3.
    Proof.
      intros xs d1 d2 d3 H12 H23 x Hx.
      rewrite H12 by exact Hx. now apply H23.
    Qed.

    (** And nothing is lost: bounded movement still gives the visible
        agreement the node level asks for. *)
    Lemma agree_off_agree_on :
      forall xs dlt dlt',
        (forall x, In x xs -> ~ In x scope) ->
        agree_off xs dlt dlt' -> agree_on scope dlt dlt'.
    Proof.
      intros xs dlt dlt' Hfresh H x Hx. apply H. intro Hm.
      eapply Hfresh; eauto.
    Qed.

    Definition carries_at (P : global) (is_control : bool) (e : exp) : Prop :=
      forall es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        wl_exp P e ->
        wc_exp P vars e ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        (forall x ck ckty,
            In x (vars_defined eqs) ->
            find_clock cenv x = OK ck ->
            assign_clk_type env base_ty ck = Some ckty ->
            incl (merge [rst_ty] ckty) amb) ->
        unnest_exp P is_control e st = ((es', eqs), st') ->
        assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv eqs xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty es' yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          (** What the emitted constraints and the target types are allowed to
              mention.  Without this the third conjunct does not survive a
              sibling's witness: the emitted set names the variables this run
              created, those are invisible to [scope], and nothing would then
              stop the sibling from moving them. *)
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    (** The two [is_control] branches of [Emerge] and [Eite] are different
        proofs -- one lifts and one does not -- so the statement is indexed by
        the flag and the expression-level property quantifies over it. *)
    Definition carries (P : global) (e : exp) : Prop :=
      forall is_control, carries_at P is_control e.

    (** Nothing was emitted, so nothing has to be satisfied. *)

    Lemma generate_leqns_constraints_cons :
      forall eq eqs,
        generate_leqns_constraints GL env base_ty rst_ty cenv (eq :: eqs)
        = (do c  <- generate_leqn_constraint GL env base_ty rst_ty cenv eq;
           do cs <- generate_leqns_constraints GL env base_ty rst_ty cenv eqs;
           SC.ret (c ++ cs)).
    Proof. reflexivity. Qed.

    Lemma generate_leqns_constraints_nil :
      forall ce xst xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv [] xst
          = OK (ce, xst') ->
        ce = [] /\ xst' = xst.
    Proof.
      intros ce xst xst' H. simpl in H. unfold ret in H. inv H. auto.
    Qed.

    (** The shape both leaves land in: the pass returned the expression
        untouched, so the two generators ran on the same term, and the
        witness is the valuation we started with. *)

    Lemma carries_unchanged :
      forall mv (ts ts'' : list LST) (ce : list constraint) dlt,
        ts'' = ts ->
        ce = [] ->
        Forall (fun t => st_scoped scope (fst t)) ts ->
        exists dlt',
          agree_off mv dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ mv) ce
          /\ Forall (fun t'' => st_scoped (scope ++ mv) (fst t'')) ts''.
    Proof.
      intros mv ts ts'' ce dlt Hts Hce Hsc; subst.
      exists dlt. split; [|split; [|split; [|split]]].
      - apply agree_off_refl.
      - constructor.
      - clear Hsc. induction ts as [|t ts IH]; [constructor|].
        constructor; [apply satisfiable_merge_r|exact IH].
      - constructor.
      - eapply Forall_impl; [|exact Hsc].
        intros t Ht. eapply st_scoped_weaken; [|exact Ht].
        apply incl_appl, incl_refl.
    Qed.

    Lemma carries_Econst : forall P c, carries P (Econst c).
    Proof.
      intros P c is_control es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst'
        dlt _ _ _ _ _ Hsc _ Hun Has Hgen Has' _.
      rewrite unnest_exp_Econst in Hun. inv Hun.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Econst in Has, Has'.
      unfold ret in Has, Has'. inv Has. inv Has'.
      eapply carries_unchanged; auto.
    Qed.

    Lemma carries_Evar : forall P x a, carries P (Evar x a).
    Proof.
      intros P x a is_control es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst'
        dlt _ _ _ _ _ Hsc _ Hun Has Hgen Has' _.
      rewrite unnest_exp_Evar in Hun. inv Hun.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      apply assign_lexps_single in Has'.
      apply assign_lexp_Evar_inv in Has as (b & Hb & ? & ?); subst.
      apply assign_lexp_Evar_inv in Has' as (b' & Hb' & ? & ?); subst.
      rewrite Hb in Hb'. inv Hb'.
      eapply carries_unchanged; auto.
    Qed.

    (** A one-stream sub-expression comes back as a one-element list, so
        [hd_default] is not losing anything -- which is why the unary and
        binary cases can hand their operand straight to the hypothesis. *)

    Lemma unnest_exp_one :
      forall P e es' eqs st st',
        wl_exp P e ->
        numstreams e = 1 ->
        unnest_exp P false e st = ((es', eqs), st') ->
        es' = [hd_default es'].
    Proof.
      intros P e es' eqs st st' Hwl Hnum Hun.
      eapply unnest_exp_length in Hun; eauto.
      rewrite Hnum in Hun.
      destruct es' as [|x [|]]; simpl in Hun; try discriminate; auto.
    Qed.

    Lemma carries_Eunop :
      forall P op e a, carries P e -> carries P (Eunop op e a).
    Proof.
      intros P op e a IH is_control es' eqs st st' ts sst sst' ce xst xst' ts''
        yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      inv Hwl. inv Hwc.
      apply unnest_exp_Eunop_inv in Hun as (e1' & st1 & Hun & ? & ?); subst.
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Eunop in Has, Has'.
      eapply IH; eauto.
      - eapply unnest_exp_one in Hun as Hone; eauto.
        rewrite Hone at 1.
        apply assign_lexps_single_intro. exact Has'.
    Qed.

    (** * Composing two sub-expressions

        A compound expression emits the concatenation of what its operands
        emitted, and the generator is a fold over the equation list, so the
        generated set splits the same way.  This is the join point of the
        induction: the operands' hypotheses each produce a witness, and these
        are the lemmas that let the second witness be applied on top of the
        first without undoing it. *)

    Lemma generate_leqns_constraints_app :
      forall eqs1 eqs2 ce xst xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv (eqs1 ++ eqs2) xst
          = OK (ce, xst') ->
        exists ce1 ce2 xst1,
          generate_leqns_constraints GL env base_ty rst_ty cenv eqs1 xst
            = OK (ce1, xst1)
          /\ generate_leqns_constraints GL env base_ty rst_ty cenv eqs2 xst1
            = OK (ce2, xst')
          /\ ce = ce1 ++ ce2.
    Proof.
      induction eqs1 as [|eq eqs1 IH]; intros eqs2 ce xst xst' H.
      - exists [], ce, xst. simpl. repeat split; auto.
      - simpl in H.
        eapply sec_bind_inv in H as (c & sta & Hc & H).
        eapply sec_bind_inv in H as (cs & stb & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        apply IH in Hcs as (ce1 & ce2 & xst1 & H1 & H2 & ?); subst.
        exists (c ++ ce1), ce2, xst1. split; [|split]; auto.
        + simpl. eapply sec_bind_ok; [exact Hc|].
          eapply sec_bind_ok; [exact H1|]. reflexivity.
        + now rewrite app_assoc.
    Qed.

    (** * What the run moved is what its equations define

        [unnest_exp_vars_perm] says the pass adds to the fresh state exactly
        the variables its emitted equations define.  With no duplicates, that
        turns the abstract [moved_by] into something concrete and checkable:
        the names this run may move are the security names of
        [vars_defined eqs] -- the same list the ambient premise quantifies
        over.

        This is also why the state-validity invariant does not have to be
        carried in Velus's own form.  All the lifting cases need of it is
        that what the run minted is new, and the permutation plus a single
        [NoDup] premise deliver exactly that, without the shrinking reusable
        set that [unnest_exp_st_valid] threads. *)

    Lemma map_bind2_unnest_vars_perm :
      forall P ic es es' eqs st st',
        Forall (wl_exp P) es ->
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        Permutation (vars_defined (List.concat eqs) ++ st_ids st) (st_ids st').
    Proof.
      intros P ic es es' eqs st st' Hwl Hmap.
      eapply map_bind2_vars_perm; eauto.
      eapply Forall_impl; [|exact Hwl].
      intros e He es'0 eqs0 st0 st0' Hun.
      eapply unnest_exp_vars_perm; eauto.
    Qed.

    Lemma NoDup_vd_app_l :
      forall (eqs1 eqs2 : list equation) (s : list ident),
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs1 ++ s).
    Proof.
      intros eqs1 eqs2 s H.
      rewrite vars_defined_app, <- app_assoc in H.
      rewrite Permutation_swap in H.
      eapply NoDup_app_r; eauto.
    Qed.

    Lemma NoDup_vd_app_r :
      forall (eqs1 eqs2 : list equation) (s s1 : list ident),
        Permutation (vars_defined eqs1 ++ s) s1 ->
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs2 ++ s1).
    Proof.
      intros eqs1 eqs2 s s1 Hperm H.
      rewrite <- Hperm.
      rewrite vars_defined_app, <- app_assoc in H.
      now rewrite Permutation_swap.
    Qed.

    Lemma NoDup_vd_drop :
      forall (eqs1 eqs2 : list equation) (s : list ident),
        NoDup (vars_defined (eqs1 ++ eqs2) ++ s) ->
        NoDup (vars_defined eqs2 ++ s).
    Proof.
      intros eqs1 eqs2 s H.
      rewrite vars_defined_app, <- app_assoc in H.
      eapply NoDup_app_r; eauto.
    Qed.

    Lemma vars_defined_in_new_ids :
      forall eqs st st' x,
        Permutation (vars_defined eqs ++ st_ids st) (st_ids st') ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        In x (vars_defined eqs) ->
        In x (new_ids st st').
    Proof.
      intros eqs st st' x Hperm Hnd Hx.
      apply new_ids_spec. split.
      - rewrite <- Hperm. apply in_or_app. now left.
      - eapply NoDup_app_In; eauto.
    Qed.

    Corollary sec_of_vars_defined_moved :
      forall eqs st st' x b,
        Permutation (vars_defined eqs ++ st_ids st) (st_ids st') ->
        NoDup (vars_defined eqs ++ st_ids st) ->
        In x (vars_defined eqs) ->
        Env.find x env = Some b ->
        In b (moved_by st st').
    Proof.
      intros eqs st st' x b Hperm Hnd Hx Hb.
      unfold moved_by, sec_of. apply in_flat_map.
      exists x. split; [eapply vars_defined_in_new_ids; eauto|].
      rewrite Hb. now left.
    Qed.

    Lemma vars_defined_incl_l :
      forall eqs1 eqs2, incl (vars_defined eqs1) (vars_defined (eqs1 ++ eqs2)).
    Proof.
      intros. rewrite vars_defined_app. apply incl_appl, incl_refl.
    Qed.

    Lemma vars_defined_incl_r :
      forall eqs1 eqs2, incl (vars_defined eqs2) (vars_defined (eqs1 ++ eqs2)).
    Proof.
      intros. rewrite vars_defined_app. apply incl_appr, incl_refl.
    Qed.

    Lemma listSatisfiable_app :
      forall dlt cs1 cs2,
        listSatisfiable dlt (cs1 ++ cs2)
        <-> listSatisfiable dlt cs1 /\ listSatisfiable dlt cs2.
    Proof. intros. unfold listSatisfiable. apply Forall_app. Qed.

    (** A type whose names the witness did not move keeps its meaning. *)

    Lemma hm_ext_off :
      forall (s : ST) xs dlt dlt',
        agree_off xs dlt dlt' ->
        (forall x, In x s -> ~ In x xs) ->
        hm_ext dlt s = hm_ext dlt' s.
    Proof.
      induction s as [|y s IH]; intros xs d d' Hoff Havoid; simpl; auto.
      rewrite (Hoff y) by (apply Havoid; now left).
      erewrite (IH xs); eauto.
      intros x Hx. apply Havoid. now right.
    Qed.

    Corollary satisfiable_off :
      forall u v xs dlt dlt',
        agree_off xs dlt dlt' ->
        (forall x, In x u -> ~ In x xs) ->
        (forall x, In x v -> ~ In x xs) ->
        satisfiable dlt u v -> satisfiable dlt' u v.
    Proof.
      intros u v xs dlt dlt' Hoff Hu Hv H. unfold satisfiable in *.
      erewrite <- (hm_ext_off u xs), <- (hm_ext_off v xs); eauto.
    Qed.

    (** The sibling transfer itself: a sub-expression's obligations mention
        only names the source can see, and a witness never moves those. *)

    Lemma listSatisfiable_off :
      forall cs xs dlt dlt',
        constraints_scoped scope cs ->
        (forall x, In x xs -> ~ In x scope) ->
        agree_off xs dlt dlt' ->
        listSatisfiable dlt cs ->
        listSatisfiable dlt' cs.
    Proof.
      intros cs xs dlt dlt' Hsc Hfresh Hoff Hsat.
      assert (agree_on scope dlt dlt') as Hagree
        by (eapply agree_off_agree_on; eauto).
      clear Hoff.
      unfold constraints_scoped, SymTypes.constraints_scoped in Hsc.
      unfold listSatisfiable in *.
      rewrite Forall_forall in Hsc, Hsat |- *.
      intros c Hin.
      eapply constraintSatisfiable_ext with (scope := scope); eauto.
      apply Hsc; exact Hin.
    Qed.

    (** And the arithmetic the joining rules need: an operand's bound still
        holds once the other operand is joined on the right. *)

    Lemma satisfiable_merge_grow_l :
      forall dlt a u v,
        satisfiable dlt a (merge u v) ->
        forall w, satisfiable dlt a (merge u (merge v w)).
    Proof.
      intros dlt a u v H w.
      eapply satisfiable_trans; [exact H|].
      apply satisfiable_merge_intro.
      - apply satisfiable_merge_l.
      - eapply satisfiable_trans; [apply satisfiable_merge_l|].
        apply satisfiable_merge_r.
    Qed.

    Lemma satisfiable_merge_grow_r :
      forall dlt a u w,
        satisfiable dlt a (merge u w) ->
        forall v, satisfiable dlt a (merge u (merge v w)).
    Proof.
      intros dlt a u w H v.
      eapply satisfiable_trans; [exact H|].
      apply satisfiable_merge_intro.
      - apply satisfiable_merge_l.
      - eapply satisfiable_trans; [apply satisfiable_merge_r|].
        apply satisfiable_merge_r.
    Qed.

    (** * Two operands, two witnesses

        The first genuine composition.  The two operands run over consecutive
        stretches of the fresh state, so the names the first witness moved are
        already in the state when the second starts, and the second therefore
        does not move them.  That is the whole argument, and it needs the
        naming pass to be injective: two distinct variables never share a
        security name, so disjoint variable sets give disjoint name sets. *)

    Hypothesis env_inj : env_injective env.

    (** The ambient names program variables only. *)
    Hypothesis amb_scoped : st_scoped scope amb.

    Lemma moved_by_disjoint :
      forall sta stb stc x,
        In x (moved_by sta stb) -> ~ In x (moved_by stb stc).
    Proof.
      intros sta stb stc x Hx Hy.
      unfold moved_by, sec_of in *.
      apply in_flat_map in Hx as (u & Hu & Hx).
      apply in_flat_map in Hy as (v & Hv & Hy).
      destruct (Env.find u env) as [bu|] eqn:Eu; simpl in Hx; [|contradiction].
      destruct (Env.find v env) as [bv|] eqn:Ev; simpl in Hy; [|contradiction].
      destruct Hx as [Hx|[]]; destruct Hy as [Hy|[]]; subst.
      assert (u = v) as ? by (eapply env_inj; eauto); subst.
      apply new_ids_spec in Hu as (Hu & _).
      apply new_ids_spec in Hv as (_ & Hv). contradiction.
    Qed.

    (** The same transfer as [listSatisfiable_off], at whatever scope the
        constraints actually have -- the emitted ones name variables the
        source never had. *)

    Lemma listSatisfiable_off_scope :
      forall cs sc xs dlt dlt',
        constraints_scoped sc cs ->
        (forall x, In x xs -> ~ In x sc) ->
        agree_off xs dlt dlt' ->
        listSatisfiable dlt cs ->
        listSatisfiable dlt' cs.
    Proof.
      intros cs sc xs dlt dlt' Hsc Hfresh Hoff Hsat.
      assert (agree_on sc dlt dlt') as Hagree
        by (intros x Hx; apply Hoff; intro Hm; eapply Hfresh; eauto).
      clear Hoff.
      unfold constraints_scoped, SymTypes.constraints_scoped in Hsc.
      unfold listSatisfiable in *.
      rewrite Forall_forall in Hsc, Hsat |- *.
      intros c Hin.
      eapply constraintSatisfiable_ext with (scope := sc); eauto.
      apply Hsc; exact Hin.
    Qed.

    Lemma constraints_scoped_cmerge :
      forall sc c1 c2,
        constraints_scoped sc (cmerge c1 c2)
        <-> constraints_scoped sc c1 /\ constraints_scoped sc c2.
    Proof.
      intros sc c1 c2.
      unfold constraints_scoped, SymTypes.constraints_scoped.
      rewrite !Forall_forall. split.
      - intros H. split; intros c Hin; apply H, cmerge_In; tauto.
      - intros (H1 & H2) c Hin. apply cmerge_In in Hin. destruct Hin; auto.
    Qed.

    Lemma st_scoped_merge :
      forall sc u v,
        st_scoped sc u -> st_scoped sc v -> st_scoped sc (merge u v).
    Proof.
      intros sc u v Hu Hv x Hx. apply in_merge_inv in Hx as [Hx|Hx]; auto.
    Qed.

    Lemma st_scoped_merge_inv :
      forall sc u v,
        st_scoped sc (merge u v) -> st_scoped sc u /\ st_scoped sc v.
    Proof.
      intros sc u v H. split; intros x Hx; apply H.
      - now apply in_merge_left.
      - now apply in_merge_right.
    Qed.

    Lemma carries_Ebinop :
      forall P op e1 e2 a,
        carries P e1 -> carries P e2 -> carries P (Ebinop op e1 e2 a).
    Proof.
      intros P op e1 e2 a IH1 IH2 is_control es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has
        Hgen Has' Hcar.
      inv Hwl. inv Hwc.
      apply unnest_exp_Ebinop_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st1) as Hf1 by (eapply unnest_exp_st_follows; eauto).
      assert (st_follows st1 st') as Hf2 by (eapply unnest_exp_st_follows; eauto).

      (** the source side: two operand types, each a single flow *)
      rewrite assign_lexp_Ebinop in Has.
      eapply sec_bind_inv in Has as (t1 & sa & Ht1 & Has).
      eapply sec_bind_inv in Has as (t2 & sb & Ht2 & Has).
      eapply sec_bind_inv in Has as (a1 & sc1 & Ha1 & Has).
      eapply sec_bind_inv in Has as (a2 & sc2 & Ha2 & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Ha1 as (? & ?); subst.
      apply single_inv in Ha2 as (? & ?); subst.

      (** the target side, the same shape on the unnested operands *)
      apply assign_lexps_single in Has'.
      rewrite assign_lexp_Ebinop in Has'.
      eapply sec_bind_inv in Has' as (u1 & ya & Hu1 & Has').
      eapply sec_bind_inv in Has' as (u2 & yb & Hu2 & Has').
      eapply sec_bind_inv in Has' as (b1 & yc & Hb1 & Has').
      eapply sec_bind_inv in Has' as (b2 & yd & Hb2 & Hret').
      unfold ret in Hret'. inv Hret'.
      apply single_inv in Hb1 as (? & ?); subst.
      apply single_inv in Hb2 as (? & ?); subst.
      eapply unnest_exp_one in Hun1 as Hone1; eauto.
      eapply unnest_exp_one in Hun2 as Hone2; eauto.

      (** the emitted set splits with the emitted equations *)
      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each operand carries, and where its names live *)
      rewrite carried_ljoin in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
      inversion Hsts as [|z zs Hsts0 Hstsr]; subst. simpl in Hsts0.
      apply st_scoped_merge_inv in Hsts0 as (Hst1 & Hst2).
      assert (carried [a1] = snd a1) as Hc1 by (simpl; apply cmerge_nil).
      assert (carried [a2] = snd a2) as Hc2 by (simpl; apply cmerge_nil).

      (** the first operand *)
      assert (Permutation (vars_defined eqs1 ++ st_ids st) (st_ids st1)) as Hp1
          by (eapply unnest_exp_vars_perm with (e := e1); eauto).
      edestruct (IH1 false f1 eqs1 st st1 [a1] sst sa ce1 xst xst1 [b1] yst ya dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
      { now rewrite Hc1. }
      { constructor; [exact Hst1|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Ht1. }
      { exact Hgen1. }
      { rewrite Hone1 at 1. apply assign_lexps_single_intro. exact Hu1. }
      { now rewrite Hc1. }

      (** the second, on top of the first: its obligations name only what the
          source can see, and the first witness left all of that alone *)
      edestruct (IH2 false f2 eqs2 st1 st' [a2] sa sb ce2 xst1 xst' [b2] ya yb dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
      { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
      { now rewrite Hc2. }
      { constructor; [exact Hst2|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Ht2. }
      { exact Hgen2. }
      { rewrite Hone2 at 1. apply assign_lexps_single_intro. exact Hu2. }
      { eapply listSatisfiable_off with (xs := moved_by st st1).
        - now rewrite Hc2.
        - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
        - exact Hoff1.
        - now rewrite Hc2. }

      inversion Hrel1 as [|p q ps qs Hr1 Hrel1r]; subst.
      inversion Hrel2 as [|p q ps qs Hr2 Hrel2r]; subst.
      inversion Hts1 as [|p ps Hb1s Hts1r]; subst.
      inversion Hts2 as [|p ps Hb2s Hts2r]; subst.

      (** the composite witness *)
      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        + eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
      - apply listSatisfiable_app. split; [|exact Hce2].
        eapply listSatisfiable_off_scope
          with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
        + exact Hscope1.
        + intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
          * eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact (moved_by_disjoint st st1 st' x Hx Hin).
        + exact Hoff2.
        + exact Hce1.
      - constructor; [|constructor]. unfold ljoin; simpl.
        apply satisfiable_merge_intro.
        + apply satisfiable_merge_grow_l.
          eapply satisfiable_off with (xs := moved_by st1 st').
          * exact Hoff2.
          * intros x Hx Hin. apply Hb1s in Hx.
            apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|now apply amb_scoped].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- eapply (Hmv x); [|now apply Hst1].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact Hr1.
        + now apply satisfiable_merge_grow_r.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
      - constructor; [|constructor]. unfold ljoin; simpl.
        apply st_scoped_merge.
        + eapply st_scoped_weaken; [|exact Hb1s].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply st_scoped_weaken; [|exact Hb2s].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Expression lists

        Every remaining constructor recurses through a list -- [unnest_exps]
        on one side, [assign_lexps] on the other -- so this is the gate.  The
        argument is the [Ebinop] argument folded: each element runs over the
        stretch of the fresh state the previous one left, so the witnesses
        chain, and each element's conclusion survives the rest because the
        rest moves elsewhere. *)

    Lemma assign_lexps_app_inv :
      forall es1 es2 ts st st',
        assign_lexps GL env base_ty rst_ty (es1 ++ es2) st = OK (ts, st') ->
        exists ts1 ts2 st1,
          assign_lexps GL env base_ty rst_ty es1 st = OK (ts1, st1)
          /\ assign_lexps GL env base_ty rst_ty es2 st1 = OK (ts2, st')
          /\ ts = ts1 ++ ts2.
    Proof.
      induction es1 as [|e es1 IH]; intros es2 ts st st' H.
      - exists [], ts, st. rewrite assign_lexps_nil. auto.
      - rewrite <- app_comm_cons, assign_lexps_cons in H.
        eapply sec_bind_inv in H as (t & sta & Ht & H).
        eapply sec_bind_inv in H as (r & stb & Hr & Hret).
        unfold ret in Hret. inv Hret.
        apply IH in Hr as (ts1 & ts2 & st1 & H1 & H2 & ?); subst.
        exists (t ++ ts1), ts2, st1. split; [|split]; auto.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [exact Ht|].
          eapply sec_bind_ok; [exact H1|]. reflexivity.
        + now rewrite app_assoc.
    Qed.

    Lemma assign_lexps_app_intro :
      forall es1 es2 ts1 ts2 st st1 st',
        assign_lexps GL env base_ty rst_ty es1 st = OK (ts1, st1) ->
        assign_lexps GL env base_ty rst_ty es2 st1 = OK (ts2, st') ->
        assign_lexps GL env base_ty rst_ty (es1 ++ es2) st
          = OK (ts1 ++ ts2, st').
    Proof.
      induction es1 as [|e es1 IH]; intros es2 ts1 ts2 st st1 st' H1 H2.
      - rewrite assign_lexps_nil in H1. unfold ret in H1. inv H1. exact H2.
      - rewrite assign_lexps_cons in H1.
        eapply sec_bind_inv in H1 as (t & sta & Ht & H1).
        eapply sec_bind_inv in H1 as (r & stb & Hr & Hret).
        unfold ret in Hret. inv Hret.
        rewrite <- app_comm_cons, assign_lexps_cons.
        eapply sec_bind_ok; [exact Ht|].
        eapply sec_bind_ok; [eapply IH; eauto|].
        unfold ret. now rewrite app_assoc.
    Qed.

    Lemma map_bind2_unnest_cons :
      forall P ic e es es' eqs st st',
        map_bind2 (unnest_exp P ic) (e :: es) st = ((es', eqs), st') ->
        exists e' eq1 st1 es'r eqsr,
          unnest_exp P ic e st = ((e', eq1), st1)
          /\ map_bind2 (unnest_exp P ic) es st1 = ((es'r, eqsr), st')
          /\ es' = e' :: es'r
          /\ eqs = eq1 :: eqsr.
    Proof.
      intros P ic e es es' eqs st st' H.
      simpl in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma map_bind2_unnest_nil :
      forall P ic es' eqs st st',
        map_bind2 (unnest_exp P ic) [] st = ((es', eqs), st') ->
        es' = [] /\ eqs = [] /\ st' = st.
    Proof.
      intros P ic es' eqs st st' H. simpl in H.
      rewrite ret_spec in H. inv H. repeat split.
    Qed.

    Lemma map_bind2_unnest_st_follows :
      forall P ic es es' eqs st st',
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        st_follows st st'.
    Proof.
      intros P ic es es' eqs st st' H.
      eapply map_bind2_st_follows; eauto.
      rewrite Forall_forall; intros; eauto.
    Qed.

    Definition carries_list (P : global) (es : list exp) : Prop :=
      forall ic es' eqs st st' ts sst sst'
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
        map_bind2 (unnest_exp P ic) es st = ((es', eqs), st') ->
        assign_lexps GL env base_ty rst_ty es sst = OK (ts, sst') ->
        generate_leqns_constraints GL env base_ty rst_ty cenv (List.concat eqs) xst
          = OK (ce, xst') ->
        assign_lexps GL env base_ty rst_ty (List.concat es') yst = OK (ts'', yst') ->
        listSatisfiable dlt (carried ts) ->
        exists dlt',
          agree_off (moved_by st st') dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''
          /\ constraints_scoped (scope ++ moved_by st st') ce
          /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t''))
               ts''.

    Lemma carries_list_intro :
      forall P es, Forall (carries P) es -> carries_list P es.
    Proof.
      intros P es Hall.
      induction Hall as [|e es IHe IHes IH];
        intros ic es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
          Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.

      - (** nothing to unnest, nothing emitted *)
        apply map_bind2_unnest_nil in Hun as (? & ? & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has'
          as (? & _ & ?); subst.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. split; [|split; [|split; [|split]]];
          solve [apply agree_off_refl | constructor].

      - (** head, then tail on top of it *)
        inv Hwl. inv Hwc.
        apply map_bind2_unnest_cons in Hun
          as (f1 & eq1 & st1 & fr & eqsr & Hun1 & Hunr & ? & ?); subst.
        assert (st_follows st st1) as Hf1 by (eapply unnest_exp_st_follows; eauto).
        assert (st_follows st1 st') as Hf2
            by (eapply map_bind2_unnest_st_follows; eauto).

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
            by (eapply unnest_exp_vars_perm with (e := e); eauto).
        edestruct (IHe ic f1 eq1 st st1 t sst sa ce1 xst xst1 u yst ya dlt)
          as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
        { assumption. }
        { assumption. }
        { eapply NoDup_vd_app_l; exact Hnd. }
        { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
        { exact Hsc1. }
        { exact Hsts1. }
        { intros y cky ckty Hy. apply Hamb.
          apply vars_defined_incl_l; exact Hy. }
        { exact Hun1. }
        { exact Ht. }
        { exact Hgen1. }
        { exact Hu. }
        { exact Hcar1. }

        edestruct (IH ic fr eqsr st1 st' r sa sst' ce2 xst1 xst' v ya yst' dlt1)
          as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
        { assumption. }
        { assumption. }
        { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
        { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
        { exact Hsc2. }
        { exact Hsts2. }
        { intros y cky ckty Hy. apply Hamb.
          apply vars_defined_incl_r; exact Hy. }
        { exact Hunr. }
        { exact Hr. }
        { exact Hgen2. }
        { exact Hv. }
        { eapply listSatisfiable_off with (xs := moved_by st st1).
          - exact Hsc2.
          - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
          - exact Hoff1.
          - exact Hcar2. }

        exists dlt2. split; [|split; [|split; [|split]]].
        + eapply agree_off_trans.
          * eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
          * eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
        + apply listSatisfiable_app. split; [|exact Hce2].
          eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
          * exact Hscope1.
          * intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * exact Hoff2.
          * exact Hce1.
        + apply Forall2_app; [|exact Hrel2].
          (** the head's bound survives the tail's witness: the head's target
              names were created before the tail started *)
          eapply Forall2_impl_In; [|exact Hrel1].
          intros p q Hp Hq Hpq.
          eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
          * intros x Hx Hin.
            eapply Forall_forall in Hts1; [|exact Hq]. apply Hts1 in Hx.
            apply in_app_or in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|exact Hx].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- exact (moved_by_disjoint st st1 st' x Hx Hin).
          * intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
            -- eapply (Hmv x); [|now apply amb_scoped].
               apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            -- eapply (Hmv x); [|].
               ++ apply (moved_by_suffix st st1 st' Hf1). exact Hin.
               ++ eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hscope1].
            intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hscope2].
            intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
        + apply Forall_app. split.
          * eapply Forall_impl; [|exact Hts1].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hts2].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Sampling

        [Ewhen] lifts nothing: unnesting pushes the sampling inward, one
        [Ewhen] per resulting stream, and the typer's rule is a map.  So the
        target types are the source's transformation applied to the operands'
        target types, and the only thing to check is that the sampling
        variable's own level rides along on both sides -- which it does, by
        the same [ljoin _ (lvar g)]. *)

    Lemma unnest_exps_inv :
      forall P es es1 eqs st st',
        unnest_exps P es st = ((es1, eqs), st') ->
        exists ess eqss,
          map_bind2 (unnest_exp P false) es st = ((ess, eqss), st')
          /\ es1 = List.concat ess
          /\ eqs = List.concat eqss.
    Proof.
      intros P es es1 eqs st st' H.
      unfold unnest_exps in H. repeat inv_bind. repeat esplit; eauto.
    Qed.

    Lemma unnest_when_nil :
      forall ckid b tys ck, unnest_when ckid b [] tys ck = [].
    Proof. reflexivity. Qed.

    Lemma unnest_when_cons :
      forall ckid b e es ty tys ck,
        unnest_when ckid b (e :: es) (ty :: tys) ck
        = Ewhen [e] ckid b ([ty], ck) :: unnest_when ckid b es tys ck.
    Proof. reflexivity. Qed.

    Lemma assign_lexps_unnest_when_inv :
      forall ckid b (tys : list type) ck g (es : list exp) ts'' st st',
        Env.find ckid env = Some g ->
        List.length es = List.length tys ->
        assign_lexps GL env base_ty rst_ty (unnest_when ckid b es tys ck) st
          = OK (ts'', st') ->
        exists ts,
          assign_lexps GL env base_ty rst_ty es st = OK (ts, st')
          /\ ts'' = List.map (fun t => ljoin t (lvar g)) ts.
    Proof.
      intros ckid b tys ck g es. revert tys.
      induction es as [|e es IH]; intros tys ts'' st st' Hg Hlen Has.
      - destruct tys; simpl in Hlen; try discriminate.
        rewrite unnest_when_nil in Has.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in Has
          as (? & _ & ?); subst.
        exists []. rewrite assign_lexps_nil. auto.
      - destruct tys as [|ty tys]; simpl in Hlen; try discriminate.
        rewrite unnest_when_cons in Has.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in Has
          as (t & r & sta & Ht & Hr & ? & _); subst.
        rewrite assign_lexp_Ewhen in Ht.
        eapply sec_bind_inv in Ht as (te & stm & Hte & Ht).
        eapply sec_bind_inv in Ht as (g' & stn & Hg' & Hret).
        unfold ret in Hret. inv Hret.
        apply find_env_inv in Hg' as (Hg' & ?); subst.
        rewrite Hg in Hg'. inv Hg'.
        apply assign_lexps_single in Hte.
        apply IH in Hr as (ts & Hts & ?); subst; auto.
        exists (te ++ ts). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [exact Hte|].
          eapply sec_bind_ok; [exact Hts|]. reflexivity.
        + now rewrite map_app.
    Qed.

    Lemma carried_cons :
      forall t ts, carried (t :: ts) = cmerge (snd t) (carried ts).
    Proof. reflexivity. Qed.

    Lemma carried_map_when :
      forall g ts,
        carried (List.map (fun t => ljoin t (lvar g)) ts) = carried ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl List.map. rewrite !carried_cons, IH.
      unfold ljoin, lvar. simpl snd. now rewrite cmerge_nil.
    Qed.

    Lemma carries_Ewhen :
      forall P es x b a, Forall (carries P) es -> carries P (Ewhen es x b a).
    Proof.
      intros P es x b [tys ck] Hall is_control es' eqs st st' ts sst sst'
        ce xst xst' ts'' yst yst' dlt Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has
        Hgen Has' Hcar.
      inv Hwl. inv Hwc.
      apply unnest_exp_Ewhen_inv in Hun as (es1 & Hunn & ?); subst.
      assert (List.length es1 = List.length tys) as Hlen
          by (erewrite unnest_exps_length; eauto).
      apply unnest_exps_inv in Hunn as (ess & eqss & Hmap & ? & ?); subst.

      (** the source: the operands' types, each sampled *)
      rewrite assign_lexp_Ewhen in Has.
      eapply sec_bind_inv in Has as (tes & sa & Htes & Has).
      eapply sec_bind_inv in Has as (g & sb & Hg & Hret).
      unfold ret in Hret. inv Hret.
      apply find_env_inv in Hg as (Hg & ?); subst.

      (** the target: the same map, over the unnested operands *)
      eapply assign_lexps_unnest_when_inv in Has' as (tes'' & Htes'' & ?);
        eauto.
      subst.

      (** the sampling variable is visible -- unless there are no streams at
          all, in which case it never appears and nothing needs it.  Its
          level is already inside the source type, and the source type is
          scoped, so this is read off the premises rather than assumed. *)
      assert (tes = [] \/ In g scope) as Hgs.
      { destruct tes as [|t0 tes0]; [now left|right].
        inversion Hsts as [|z zs Hz Hzr]; subst. simpl in Hz.
        apply Hz. apply in_merge_right. now left. }

      rewrite carried_map_when in Hsc, Hcar.
      assert (Forall (fun t => st_scoped scope (fst t)) tes) as Hstes.
      { clear - Hsts. induction tes as [|t tes IH]; constructor.
        - inversion Hsts as [|z zs Hz Hzr]; subst. simpl in Hz.
          apply st_scoped_merge_inv in Hz as (Hz & _); auto.
        - apply IH. inversion Hsts as [|z zs Hz Hzr]; subst; auto. }

      edestruct (carries_list_intro P es Hall false ess eqss st st' tes sst sa
                   ce xst xst' tes'' yst yst' dlt)
        as (dlt' & Hoff & Hce & Hrel & Hscope & Hts); eauto.

      exists dlt'. split; [|split; [|split; [|split]]]; auto.
      - (** the sampling rides along on both sides *)
        clear - Hrel.
        induction Hrel as [|t t'' tes tes'' Hr Hrest IH]; [constructor|].
        constructor; auto.
        unfold ljoin; simpl. apply satisfiable_merge_intro.
        + now apply satisfiable_merge_grow_l.
        + eapply satisfiable_trans; [apply satisfiable_merge_r|].
          apply satisfiable_merge_r.
      - (** and stays inside the same bound *)
        destruct Hgs as [?|Hgs]; subst.
        + inversion Hrel; subst. constructor.
        + clear - Hts Hgs.
          induction Hts as [|t'' tes'' Hz Hzr IH]; [constructor|].
          constructor; auto.
          unfold ljoin; simpl. apply st_scoped_merge.
          * eapply st_scoped_weaken; [|exact Hz]. apply incl_refl.
          * intros y Hy. destruct Hy as [|[]]; subst.
            apply in_or_app; now left.
    Qed.

    (** * The componentwise join, related on both sides

        [Emerge] and [Eite] both build their result with
        [ljoin_list (map (ljoin (lvar g)) _) _], on the source and on the
        target alike.  So the relation between the two sides is established
        once, by walking the two joins together, and the two constructors
        then differ only in how they get their operands. *)

    Lemma ljoin_list_rel_head :
      forall dlt h h' ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin h t) ts) us s1 = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin h' t) ts') us' s2 = OK (rs', s2') ->
        satisfiable dlt (fst h') (merge amb (fst h)) ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros dlt h h' ts. revert h h'.
      induction ts as [|t ts IH];
        intros h h' us rs ts' us' rs' s1 s1' s2 s2' Hj Hj' Hh Hts Hus.
      - inv Hts. destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj.
        inv Hus. simpl in Hj'. unfold ret in Hj'. inv Hj'. constructor.
      - inversion Hts as [|t0 t0' ts0 ts0' Ht Htsr]; subst.
        destruct us as [|u us]; simpl in Hj; [discriminate|].
        inversion Hus as [|u0 u0' us0 us0' Hu Husr]; subst.
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        simpl in Hj'.
        eapply sec_bind_inv in Hj' as (r' & sb & Hr' & Hret').
        unfold ret in Hret'. inv Hret'.
        constructor; [|eapply IH; eauto].
        rewrite !fst_ljoin.
        apply satisfiable_merge_intro; [apply satisfiable_merge_intro|].
        + (** the head -- a sampling variable, or the scrutinee's own type *)
          apply satisfiable_merge_grow_l, satisfiable_merge_grow_l. exact Hh.
        + apply satisfiable_merge_grow_l.
          eapply satisfiable_trans; [exact Ht|].
          apply satisfiable_merge_intro.
          * apply satisfiable_merge_l.
          * eapply satisfiable_trans; [apply satisfiable_merge_r|].
            apply satisfiable_merge_r.
        + now apply satisfiable_merge_grow_r.
    Qed.

    Corollary ljoin_list_rel :
      forall dlt g ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s1
          = OK (rs, s1') ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts') us' s2
          = OK (rs', s2') ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros. eapply ljoin_list_rel_head; eauto.
    Qed.

    Lemma ljoin_list_scoped_head :
      forall sc h ts us rs s s',
        st_scoped sc (fst h) ->
        ljoin_list (List.map (fun t => ljoin h t) ts) us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros sc h ts. revert h.
      induction ts as [|t ts IH]; intros h us rs s s' Hh Hj Hts Hus.
      - destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj. constructor.
      - destruct us as [|u us]; simpl in Hj; [discriminate|].
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        inversion Hts as [|z zs Hz Hzr]; subst.
        inversion Hus as [|w ws Hw Hwr]; subst.
        constructor; [|eapply IH with (h := h); eauto].
        rewrite !fst_ljoin.
        apply st_scoped_merge; [apply st_scoped_merge|]; auto.
    Qed.

    Corollary ljoin_list_scoped :
      forall sc g ts us rs s s',
        In g sc ->
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros. eapply ljoin_list_scoped_head; eauto.
      rewrite fst_lvar. intros y Hy. destruct Hy as [|[]]; subst; auto.
    Qed.

    Lemma ljoin_list_scoped_head_inv :
      forall sc h ts us rs s s',
        ljoin_list (List.map (fun t => ljoin h t) ts) us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us
        /\ (ts = [] \/ st_scoped sc (fst h)).
    Proof.
      intros sc h ts. revert h.
      induction ts as [|t ts IH]; intros h us rs s s' Hj Hrs.
      - destruct us; simpl in Hj; [|discriminate].
        unfold ret in Hj. inv Hj. auto.
      - destruct us as [|u us]; simpl in Hj; [discriminate|].
        eapply sec_bind_inv in Hj as (r & sa & Hr & Hret).
        unfold ret in Hret. inv Hret.
        inversion Hrs as [|z zs Hz Hzr]; subst.
        apply IH in Hr as (Hts & Hus & _); auto.
        rewrite !fst_ljoin in Hz.
        apply st_scoped_merge_inv in Hz as (Hz & Hu).
        apply st_scoped_merge_inv in Hz as (Hgz & Ht).
        split; [|split].
        + constructor; auto.
        + constructor; auto.
        + right; auto.
    Qed.

    Corollary ljoin_list_scoped_inv :
      forall sc g ts us rs s s',
        ljoin_list (List.map (fun t => ljoin (lvar g) t) ts) us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us
        /\ (ts = [] \/ In g sc).
    Proof.
      intros sc g ts us rs s s' Hj Hrs.
      eapply ljoin_list_scoped_head_inv in Hj as (? & ? & [?|Hg]); eauto.
      rewrite fst_lvar in Hg. repeat split; auto.
      right. apply Hg. now left.
    Qed.

    Lemma carried_map_merge_l :
      forall g ts,
        carried (List.map (fun t => ljoin (lvar g) t) ts) = carried ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl List.map. rewrite !carried_cons, IH.
      unfold ljoin, lvar. simpl snd. now rewrite cmerge_nil2.
    Qed.

    Lemma map_bind2_unnest_normalized :
      forall P es es' eqs st st',
        map_bind2 (unnest_exp P true) es st = ((es', eqs), st') ->
        Forall normalized_cexp (List.concat es').
    Proof.
      induction es as [|e es IH]; intros es' eqs st st' H.
      - apply map_bind2_unnest_nil in H as (? & ? & ?); subst. constructor.
      - apply map_bind2_unnest_cons in H
          as (e' & eq1 & st1 & es'r & eqsr & H1 & H2 & ? & ?); subst.
        simpl List.concat. apply Forall_app. split.
        + eapply unnest_exp_normalized_cexp; eauto.
        + eapply IH; eauto.
    Qed.

    (** * The merge, when it does not lift

        Under [is_control] the branches are unnested in place and the sampling
        is pushed inward.  Both sides then build the result the same way, so
        the whole case is the two branch lists composed -- as in [Ebinop] --
        followed by the join lemmas above. *)

    Lemma carries_Emerge_control :
      forall P ckid es1 es2 tys cl,
        Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P true (Emerge ckid es1 es2 (tys, cl)).
    Proof.
      intros P ckid es1 es2 tys cl Hall1 Hall2
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      inv Hwl. inv Hwc.
      apply unnest_exp_Emerge_control_inv in Hun
        as (f1 & eqs1 & st1 & f2 & eqs2 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st1) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st') as Hf2
          by (eapply map_bind2_unnest_st_follows; eauto).

      (** the source: the two branches, joined *)
      rewrite assign_lexp_Emerge in Has.
      eapply sec_bind_inv in Has as (g & sa & Hg & Has).
      eapply sec_bind_inv in Has as (tes1 & sb & Htes1 & Has).
      eapply sec_bind_inv in Has as (tes2 & sc & Htes2 & Hj).
      apply find_env_inv in Hg as (Hg & ?); subst.

      (** the target: the same join, over the unnested branches *)
      assert (Forall normalized_cexp (List.concat f1)) as Hn1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat f2)) as Hn2
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat f1) = List.length tys) as Hl1
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat f2) = List.length tys) as Hl2
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      eapply assign_lexps_unnest_merge_inv in Has'
        as (tes1'' & tes2'' & Ht1'' & Ht2'' & ? & Hj''); eauto.
      subst.

      apply generate_leqns_constraints_app in Hgen
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each branch carries, and where its names live *)
      assert (carried ts = cmerge (carried tes1) (carried tes2)) as Hct.
      { erewrite ljoin_list_carried by exact Hj.
        now rewrite carried_map_merge_l. }
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (Hsc1 & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (Hcar1 & Hcar2).
      eapply ljoin_list_scoped_inv in Hsts as (Hsts1 & Hsts2 & Hgs);
        [|exact Hj].

      assert (Permutation (vars_defined (List.concat eqs1) ++ st_ids st)
                (st_ids st1)) as Hp1
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      edestruct (carries_list_intro P es1 Hall1 true f1 eqs1 st st1 tes1 sst sb
                   ce1 xst xst1 tes1'' yst yst dlt)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv. eapply moved_by_prefix; eauto. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Htes1. }
      { exact Hgen1. }
      { exact Ht1''. }
      { exact Hcar1. }

      edestruct (carries_list_intro P es2 Hall2 true f2 eqs2 st1 st' tes2 sb sc
                   ce2 xst1 xst' tes2'' yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd]. }
      { intros x Hx. apply Hmv. eapply moved_by_suffix; eauto. }
      { exact Hsc2. }
      { exact Hsts2. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Htes2. }
      { exact Hgen2. }
      { exact Ht2''. }
      { eapply listSatisfiable_off with (xs := moved_by st st1).
        - exact Hsc2.
        - intros x Hx. apply Hmv. eapply moved_by_prefix; eauto.
        - exact Hoff1.
        - exact Hcar2. }

      (** the first branch's bound survives the second's witness *)
      assert (Forall2 (fun t t'' => satisfiable dlt2 (fst t'') (merge amb (fst t)))
                tes1 tes1'') as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
        - intros x Hx Hin.
          eapply Forall_forall in Hts1; [|exact Hq]. apply Hts1 in Hx.
          apply in_app_or in Hx as [Hx|Hx].
          + eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          + exact (moved_by_disjoint st st1 st' x Hx Hin).
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          + eapply (Hmv x); [|].
            * apply (moved_by_suffix st st1 st' Hf1). exact Hin.
            * eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1. }

      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        + eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto.
      - apply listSatisfiable_app. split; [|exact Hce2].
        eapply listSatisfiable_off_scope
          with (sc := scope ++ moved_by st st1) (xs := moved_by st1 st').
        + exact Hscope1.
        + intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
          * eapply (Hmv x); [|exact Hx].
            apply (moved_by_suffix st st1 st' Hf1). exact Hin.
          * exact (moved_by_disjoint st st1 st' x Hx Hin).
        + exact Hoff2.
        + exact Hce1.
      - eapply ljoin_list_rel; eauto.
      - apply Forall_app. split.
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_prefix; auto.
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, moved_by_suffix; auto.
      - destruct Hgs as [?|Hgs]; subst.
        + (** no streams: the sampling variable never appears *)
          inversion Hrel1; subst. simpl in Hj''.
          destruct tes2'' as [|? ?]; [|discriminate].
          unfold ret in Hj''. inv Hj''. constructor.
        + eapply ljoin_list_scoped; [|exact Hj''| |].
          * apply in_or_app; now left.
          * eapply Forall_impl; [|exact Hts1].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_prefix; auto.
          * eapply Forall_impl; [|exact Hts2].
            intros q Hq. eapply st_scoped_weaken; [|exact Hq].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, moved_by_suffix; auto.
    Qed.

    (** * Reading a sub-obligation out of a larger one

        [Emerge] joins a variable's level, which carries nothing, so its
        result carries exactly what its branches carry.  [Eite] joins the
        scrutinee's whole type, which may itself carry a nested call's
        obligations, so the result carries the scrutinee's as well.  Rather
        than compute that set, note that both are *contained* in it, which is
        all an obligation set is ever used for. *)

    Lemma constraints_scoped_sub :
      forall sc cs cs',
        (forall c, In c cs' -> In c cs) ->
        constraints_scoped sc cs -> constraints_scoped sc cs'.
    Proof.
      intros sc cs cs' Hin Hsc.
      unfold constraints_scoped, SymTypes.constraints_scoped in *.
      rewrite Forall_forall in *. auto.
    Qed.

    Lemma listSatisfiable_sub :
      forall dlt cs cs',
        (forall c, In c cs' -> In c cs) ->
        listSatisfiable dlt cs -> listSatisfiable dlt cs'.
    Proof.
      intros dlt cs cs' Hin Hsat.
      unfold listSatisfiable in *. rewrite Forall_forall in *. auto.
    Qed.

    Lemma carried_map_ljoin_mono :
      forall h ts c,
        In c (carried ts) ->
        In c (carried (List.map (fun t => ljoin h t) ts)).
    Proof.
      induction ts as [|t ts IH]; intros c Hc; [contradiction|].
      rewrite carried_cons in Hc. simpl List.map. rewrite carried_cons.
      apply cmerge_In in Hc as [Hc|Hc]; apply cmerge_In.
      - left. unfold ljoin. simpl snd. apply cmerge_In. now right.
      - right. now apply IH.
    Qed.

    Lemma carried_map_ljoin_head :
      forall h t ts c,
        In c (snd h) ->
        In c (carried (List.map (fun u => ljoin h u) (t :: ts))).
    Proof.
      intros h t ts c Hc. simpl List.map. rewrite carried_cons.
      apply cmerge_In. left. unfold ljoin. simpl snd.
      apply cmerge_In. now left.
    Qed.

    (** * The conditional, when it does not lift

        Three sub-expressions rather than two, and the first of them supplies
        the head that the other two are joined under.  So the witness is
        built in three steps, and the scrutinee's own bound has to survive
        both of the branches' witnesses -- which it does, because all three
        run over consecutive stretches of the fresh state. *)

    Lemma carries_Eite_control :
      forall P e0 es1 es2 tys ck,
        carries P e0 -> Forall (carries P) es1 -> Forall (carries P) es2 ->
        carries_at P true (Eite e0 es1 es2 (tys, ck)).
    Proof.
      intros P e0 es1 es2 tys ck IH0 Hall1 Hall2
        es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst' dlt
        Hwl Hwc Hnd Hmv Hsc Hsts Hamb Hun Has Hgen Has' Hcar.
      inv Hwl. inv Hwc.
      apply unnest_exp_Eite_control_inv in Hun
        as (f0 & eqs0 & st0 & f1 & eqs1 & st1 & f2 & eqs2
            & Hun0 & Hun1 & Hun2 & ? & ?); subst.
      assert (st_follows st st0) as Hf0
          by (eapply unnest_exp_st_follows; eauto).
      assert (st_follows st0 st1) as Hf1
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st1 st') as Hf2
          by (eapply map_bind2_unnest_st_follows; eauto).
      assert (st_follows st0 st') as Hf0' by (etransitivity; eauto).
      assert (st_follows st st1) as Hf01 by (etransitivity; eauto).
      assert (st_follows st st') as Hf012 by (etransitivity; eauto).

      (** the source: the scrutinee, then the two branches joined under it *)
      rewrite assign_lexp_Eite in Has.
      eapply sec_bind_inv in Has as (t0 & sa & Ht0 & Has).
      eapply sec_bind_inv in Has as (th & sb & Hth & Has).
      eapply sec_bind_inv in Has as (tes1 & sc & Htes1 & Has).
      eapply sec_bind_inv in Has as (tes2 & sd & Htes2 & Hj).
      apply single_inv in Hth as (? & ?); subst.

      (** the branches have at least one stream, so the scrutinee really is
          read back on the target side *)
      assert (List.length tes1 = List.length tys) as Hlt1.
      { erewrite assign_lexps_length with (es := es1); eauto. }
      assert (tes1 <> []) as Hne1.
      { intro; subst. simpl in Hlt1. lia. }

      (** the target: the same shape, over the unnested pieces *)
      assert (Forall normalized_lexp f0) as Hn0
          by (eapply unnest_exp_normalized_lexp; eauto).
      assert (f0 = [hd_default f0]) as Hone0
          by (eapply unnest_exp_one; eauto).
      assert (Forall normalized_cexp (List.concat f1)) as Hn1
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (Forall normalized_cexp (List.concat f2)) as Hn2
          by (eapply map_bind2_unnest_normalized; eauto).
      assert (List.length (List.concat f1) = List.length tys) as Hl1
          by (erewrite map_bind2_unnest_exp_length with (es := es1); eauto).
      assert (List.length (List.concat f2) = List.length tys) as Hl2
          by (erewrite map_bind2_unnest_exp_length with (es := es2); eauto).
      assert (normalized_lexp (hd_default f0)) as Hn0'
        by (rewrite Hone0 in Hn0; now inv Hn0).
      eapply assign_lexps_unnest_ite_inv in Has'
        as (? & tes1'' & tes2'' & Ht1'' & Ht2'' & Hrest);
        [|exact Hn0'|exact Hn1|exact Hn2|exact Hl1|exact Hl2].
      subst.
      assert (List.length tes1'' = List.length tys) as Hlt1''.
      { rewrite <- Hl1. eapply assign_lexps_normalized_pure; eauto. }
      destruct Hrest as [(th'' & Hth'' & Hj'')|(Hnil & _ & _)];
        [|rewrite Hnil in Hlt1''; simpl in Hlt1''; lia].

      apply generate_leqns_constraints_app in Hgen
        as (ce0 & cer & xst0 & Hgen0 & Hgenr & ?); subst.
      apply generate_leqns_constraints_app in Hgenr
        as (ce1 & ce2 & xst1 & Hgen1 & Hgen2 & ?); subst.

      (** what each piece carries, and where its names live *)
      assert (carried ts
              = cmerge (carried (List.map (fun t => ljoin th t) tes1))
                  (carried tes2)) as Hct
          by (eapply ljoin_list_carried; eauto).
      rewrite Hct in Hsc, Hcar.
      apply constraints_scoped_cmerge in Hsc as (HscM & Hsc2).
      apply listSatisfiable_cmerge in Hcar as (HcarM & Hcar2).
      assert (constraints_scoped scope (carried tes1)) as Hsc1
          by (eapply constraints_scoped_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (carried tes1)) as Hcar1
          by (eapply listSatisfiable_sub;
              [intros c Hc; apply carried_map_ljoin_mono; exact Hc|exact HcarM]).
      destruct tes1 as [|tf tes1r]; [contradiction|].
      assert (constraints_scoped scope (snd th)) as Hsc0
          by (eapply constraints_scoped_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HscM]).
      assert (listSatisfiable dlt (snd th)) as Hcar0
          by (eapply listSatisfiable_sub;
              [intros c Hc; eapply carried_map_ljoin_head; exact Hc|exact HcarM]).
      eapply ljoin_list_scoped_head_inv in Hsts as (Hsts1 & Hsts2 & Hgs);
        [|exact Hj].
      assert (st_scoped scope (fst th)) as Hst0
          by (destruct Hgs as [Hx|Hx]; [discriminate|exact Hx]).

      (** the scrutinee *)
      assert (Permutation (vars_defined eqs0 ++ st_ids st) (st_ids st0)) as Hp0
          by (eapply unnest_exp_vars_perm with (e := e0); eauto).
      assert (NoDup (vars_defined (List.concat eqs1 ++ List.concat eqs2)
                       ++ st_ids st0)) as Hnd0
          by (eapply NoDup_vd_app_r; [exact Hp0|exact Hnd]).
      assert (Permutation (vars_defined (List.concat eqs1) ++ st_ids st0)
                (st_ids st1)) as Hp1
          by (eapply map_bind2_unnest_vars_perm with (es := es1); eauto).
      edestruct (IH0 false f0 eqs0 st st0 [th] sst sa ce0 xst xst0
                   [th''] yst yst dlt)
        as (dlt0 & Hoff0 & Hce0 & Hrel0 & Hscope0 & Hts0).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd. }
      { intros x Hx. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }
      { simpl. now rewrite cmerge_nil. }
      { constructor; [exact Hst0|constructor]. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_l; exact Hy. }
      { exact Hun0. }
      { exact Ht0. }
      { exact Hgen0. }
      { rewrite Hone0 at 1. now apply assign_lexps_single_intro. }
      { simpl. now rewrite cmerge_nil. }

      (** the true branch, on top of it *)
      edestruct (carries_list_intro P es1 Hall1 true f1 eqs1 st0 st1
                   (tf :: tes1r) sa sc ce1 xst0 xst1 tes1'' yst yst dlt0)
        as (dlt1 & Hoff1 & Hce1 & Hrel1 & Hscope1 & Hts1).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_l; exact Hnd0. }
      { intros x Hx. apply Hmv.
        apply (moved_by_suffix st st0 st' Hf0).
        apply (moved_by_prefix st0 st1 st' Hf2). exact Hx. }
      { exact Hsc1. }
      { exact Hsts1. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r, vars_defined_incl_l; exact Hy. }
      { exact Hun1. }
      { exact Htes1. }
      { exact Hgen1. }
      { exact Ht1''. }
      { eapply listSatisfiable_off with (xs := moved_by st st0); eauto.
        intros x Hx. apply Hmv.
        apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }

      (** and the false branch on top of that *)
      edestruct (carries_list_intro P es2 Hall2 true f2 eqs2 st1 st' tes2 sc sd
                   ce2 xst1 xst' tes2'' yst yst dlt1)
        as (dlt2 & Hoff2 & Hce2 & Hrel2 & Hscope2 & Hts2).
      { assumption. }
      { assumption. }
      { eapply NoDup_vd_app_r; [exact Hp1|exact Hnd0]. }
      { intros x Hx. apply Hmv.
        apply (moved_by_suffix st st1 st' Hf01). exact Hx. }
      { exact Hsc2. }
      { exact Hsts2. }
      { intros y cky ckty Hy. apply Hamb.
        apply vars_defined_incl_r, vars_defined_incl_r; exact Hy. }
      { exact Hun2. }
      { exact Htes2. }
      { exact Hgen2. }
      { exact Ht2''. }
      { eapply listSatisfiable_off with (xs := moved_by st0 st1); eauto.
        - intros x Hx. apply Hmv.
          apply (moved_by_suffix st st0 st' Hf0).
          apply (moved_by_prefix st0 st1 st' Hf2). exact Hx.
        - eapply listSatisfiable_off with (xs := moved_by st st0); eauto.
          intros x Hx. apply Hmv.
          apply (moved_by_prefix st st0 st' Hf0'). exact Hx. }

      (** the later witnesses do not undo the earlier ones *)
      assert (agree_off (moved_by st0 st') dlt0 dlt2) as Hoff02.
      { eapply agree_off_trans.
        - eapply agree_off_incl; [|exact Hoff1]. apply moved_by_prefix; auto.
        - eapply agree_off_incl; [|exact Hoff2]. apply moved_by_suffix; auto. }

      assert (forall x, In x (moved_by st0 st') ->
                        ~ In x (scope ++ moved_by st st0)) as Hsep0.
      { intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
        - eapply (Hmv x); [|exact Hx].
          apply (moved_by_suffix st st0 st' Hf0). exact Hin.
        - exact (moved_by_disjoint st st0 st' x Hx Hin). }
      assert (forall x, In x (moved_by st1 st') ->
                        ~ In x (scope ++ moved_by st0 st1)) as Hsep1.
      { intros x Hin Hx. apply in_app_or in Hx as [Hx|Hx].
        - eapply (Hmv x); [|exact Hx].
          apply (moved_by_suffix st st1 st' Hf01). exact Hin.
        - exact (moved_by_disjoint st0 st1 st' x Hx Hin). }

      inversion Hrel0 as [|p q ps qs Hr0 Hrel0r]; subst.
      assert (satisfiable dlt2 (fst th'') (merge amb (fst th))) as Hr0'.
      { eapply satisfiable_off with (xs := moved_by st0 st'); eauto.
        - intros x Hx Hin. apply (Hsep0 x Hin).
          inversion Hts0 as [|z zs Hz Hzr]; subst. now apply Hz.
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st0 st' Hf0). exact Hin.
          + eapply (Hmv x); [|now apply Hst0].
            apply (moved_by_suffix st st0 st' Hf0). exact Hin. }

      assert (Forall2 (fun t t'' => satisfiable dlt2 (fst t'') (merge amb (fst t)))
                (tf :: tes1r) tes1'') as Hrel1'.
      { eapply Forall2_impl_In; [|exact Hrel1].
        intros p q Hp Hq Hpq.
        eapply satisfiable_off with (xs := moved_by st1 st'); eauto.
        - intros x Hx Hin. apply (Hsep1 x Hin).
          eapply Forall_forall in Hts1; [|exact Hq]. now apply Hts1.
        - intros x Hx Hin. apply in_merge_inv in Hx as [Hx|Hx].
          + eapply (Hmv x); [|now apply amb_scoped].
            apply (moved_by_suffix st st1 st' Hf01). exact Hin.
          + eapply (Hmv x); [|].
            * apply (moved_by_suffix st st1 st' Hf01). exact Hin.
            * eapply Forall_forall in Hsts1; [|exact Hp]. now apply Hsts1. }

      exists dlt2. split; [|split; [|split; [|split]]].
      - eapply agree_off_trans.
        + eapply agree_off_incl; [|exact Hoff0].
          apply (moved_by_prefix st st0 st' Hf0').
        + eapply agree_off_incl; [|exact Hoff02].
          apply (moved_by_suffix st st0 st' Hf0).
      - apply listSatisfiable_app. split; [|apply listSatisfiable_app; split].
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st st0) (xs := moved_by st0 st');
            eauto.
        + eapply listSatisfiable_off_scope
            with (sc := scope ++ moved_by st0 st1) (xs := moved_by st1 st');
            eauto.
        + exact Hce2.
      - eapply ljoin_list_rel_head; eauto.
      - apply Forall_app. split; [|apply Forall_app; split].
        + eapply Forall_impl; [|exact Hscope0].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st0 st' Hf0').
        + eapply Forall_impl; [|exact Hscope1].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. eapply incl_tran;
            [apply (moved_by_prefix st0 st1 st' Hf2)
            |apply (moved_by_suffix st st0 st' Hf0)].
        + eapply Forall_impl; [|exact Hscope2].
          intros c Hc. eapply constraint_scoped_incl; [|exact Hc].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st' Hf01).
      - eapply ljoin_list_scoped_head; [|exact Hj''| |].
        + inversion Hts0 as [|z zs Hz Hzr]; subst.
          eapply st_scoped_weaken; [|exact Hz].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_prefix st st0 st' Hf0').
        + eapply Forall_impl; [|exact Hts1].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr. eapply incl_tran;
            [apply (moved_by_prefix st0 st1 st' Hf2)
            |apply (moved_by_suffix st st0 st' Hf0)].
        + eapply Forall_impl; [|exact Hts2].
          intros q Hq. eapply st_scoped_weaken; [|exact Hq].
          apply incl_app; [apply incl_appl, incl_refl|].
          apply incl_appr, (moved_by_suffix st st1 st' Hf01).
    Qed.

    (** * Extending the witness on the names the pass minted

        Every lifting constructor ends the same way: [idents_for_anns] mints
        one variable per result, the pass returns an [Evar] for each, and it
        emits one equation per result binding that variable to the compound
        expression it replaced.  So the target's type for a result is a bare
        name, and what pins that name down is the emitted equation's own
        constraint.

        The witness is therefore *chosen* rather than inherited: give each
        minted name exactly the value its defining constraint demands, and the
        emitted constraints hold by construction.  Two things make that
        legitimate.  The names are minted in this run, so moving them is
        within the bound the statement allows; and nothing the values are
        computed from mentions them, since everything else was minted earlier
        or is visible. *)

    Definition upd (b : ident) (v : Lat.t) (dlt : ident -> Lat.t)
      : ident -> Lat.t :=
      fun x => if ident_eq_dec x b then v else dlt x.

    Fixpoint upds (bs : list ident) (vs : list Lat.t) (dlt : ident -> Lat.t)
      : ident -> Lat.t :=
      match bs, vs with
      | b :: bs', v :: vs' => upd b v (upds bs' vs' dlt)
      | _, _ => dlt
      end.

    Lemma upds_notin :
      forall bs vs dlt x, ~ In x bs -> upds bs vs dlt x = dlt x.
    Proof.
      induction bs as [|b bs IH]; intros vs dlt x Hx; simpl; auto.
      destruct vs as [|v vs]; auto.
      unfold upd. destruct (ident_eq_dec x b) as [?|?]; subst.
      - exfalso. apply Hx. now left.
      - apply IH. intro; apply Hx. now right.
    Qed.

    Corollary upds_agree_off :
      forall bs vs dlt, agree_off bs dlt (upds bs vs dlt).
    Proof. intros bs vs dlt x Hx. symmetry. now apply upds_notin. Qed.

    Lemma upds_nth :
      forall bs vs dlt b v,
        NoDup bs ->
        List.length bs = List.length vs ->
        In (b, v) (combine bs vs) ->
        upds bs vs dlt b = v.
    Proof.
      induction bs as [|b0 bs IH]; intros vs dlt b v Hnd Hlen Hin;
        [contradiction|].
      destruct vs as [|v0 vs]; simpl in Hlen; [discriminate|].
      inv Hnd. simpl in Hin. destruct Hin as [Heq|Hin].
      - inv Heq. simpl. unfold upd.
        destruct (ident_eq_dec b b) as [?|Hne]; [reflexivity|].
        now elim Hne.
      - simpl. unfold upd.
        destruct (ident_eq_dec b b0) as [?|Hne]; subst.
        + exfalso. apply H1. eapply in_combine_l; eauto.
        + eapply IH; eauto.
    Qed.

    (** And the values themselves: a type whose names the extension did not
        touch means the same before and after. *)

    Lemma hm_ext_upds :
      forall (s : ST) bs vs dlt,
        (forall x, In x s -> ~ In x bs) ->
        hm_ext (upds bs vs dlt) s = hm_ext dlt s.
    Proof.
      intros s bs vs dlt Havoid. symmetry.
      eapply hm_ext_off with (xs := bs); [apply upds_agree_off|].
      intros x Hx. now apply Havoid.
    Qed.

    (** * The shape every lifting constructor ends in

        The pass returns one [Evar] per result and emits one equation per
        result.  [Efby] and [Earrow] spell the emitted list differently --
        one maps over a [combine], the other combines two maps -- so both are
        first put in the same form, and everything after is shared. *)

    Lemma assign_lexps_evars :
      forall (xs : list (ident * ann)) ts'' st st',
        assign_lexps GL env base_ty rst_ty
          (List.map (fun '(x, a) => Evar x a) xs) st = OK (ts'', st') ->
        st' = st
        /\ Forall2 (fun xa t => exists b, Env.find (fst xa) env = Some b
                                          /\ t = lvar b) xs ts''.
    Proof.
      induction xs as [|[x a] xs IH]; intros ts'' st st' H.
      - simpl List.map in H.
        apply (assign_lexps_carried_nil GL env base_ty rst_ty) in H
          as (? & _ & ?); subst.
        split; auto.
      - simpl List.map in H.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        apply assign_lexp_Evar_inv in Ht as (b & Hb & ? & ?); subst.
        apply IH in Hr as (? & Hall); subst.
        split; auto. simpl List.app.
        constructor; auto. exists b. auto.
    Qed.

    Lemma emitted_defs_map_form :
      forall (xs : list (ident * ann)) (rhss : list exp),
        List.map (fun '((x, _), e) => ([x], [e])) (combine xs rhss)
        = List.map (fun '(x, e) => ([x], [e]))
            (combine (List.map fst xs) rhss).
    Proof.
      induction xs as [|[x a] xs IH]; intros rhss; [reflexivity|].
      destruct rhss as [|e rhss]; [reflexivity|].
      simpl. f_equal. apply IH.
    Qed.

    Lemma emitted_defs_combine_form :
      forall (xs : list (ident * ann)) (rhss : list exp),
        combine (List.map (fun '(id, _) => [id]) xs)
          (List.map (fun e => [e]) rhss)
        = List.map (fun '(x, e) => ([x], [e]))
            (combine (List.map fst xs) rhss).
    Proof.
      induction xs as [|[x a] xs IH]; intros rhss; [reflexivity|].
      destruct rhss as [|e rhss]; [reflexivity|].
      simpl. f_equal. apply IH.
    Qed.

    Lemma hm_ext_single :
      forall dlt b, hm_ext dlt [b] = Lat.join (dlt b) Lat.bottom.
    Proof. reflexivity. Qed.

    Lemma upd_same : forall b v dlt, upd b v dlt b = v.
    Proof.
      intros b v dlt. unfold upd.
      destruct (ident_eq_dec b b) as [?|Hne]; [reflexivity|now elim Hne].
    Qed.

    Lemma satisfiable_singleton :
      forall dlt b X,
        Lat.order (dlt b) (hm_ext dlt X) -> satisfiable dlt [b] X.
    Proof.
      intros dlt b X H. unfold satisfiable. simpl.
      apply Lat.join_least_upper_bound; auto.
    Qed.

    Lemma sec_of_cons_In :
      forall x xs b, Env.find x env = Some b -> In b (sec_of (x :: xs)).
    Proof.
      intros x xs b Hb. unfold sec_of. apply in_flat_map.
      exists x. split; [now left|]. rewrite Hb. now left.
    Qed.

    Lemma sec_of_incl_cons :
      forall x xs, incl (sec_of xs) (sec_of (x :: xs)).
    Proof.
      intros x xs b Hb. unfold sec_of in *.
      apply in_flat_map in Hb as (y & Hy & Hb).
      apply in_flat_map. exists y. split; auto. now right.
    Qed.

    Lemma sec_of_nIn :
      forall x xs b,
        ~ In x xs -> Env.find x env = Some b -> ~ In b (sec_of xs).
    Proof.
      intros x xs b Hx Hb Hin. unfold sec_of in Hin.
      apply in_flat_map in Hin as (y & Hy & Hin).
      destruct (Env.find y env) as [c|] eqn:Ey; simpl in Hin; [|contradiction].
      destruct Hin as [|[]]; subst.
      apply Hx. replace x with y; auto. symmetry. eapply env_inj; eauto.
    Qed.

    (** A defining equation of a minted variable, reduced.  The right-hand
        sides the lifting constructors emit are never calls, so the equation
        generator takes its ordinary-definition branch. *)

    Lemma generate_leqn_constraint_def :
      forall x e,
        (match e with Eapp _ _ _ _ => False | _ => True end) ->
        generate_leqn_constraint GL env base_ty rst_ty cenv ([x], [e])
        = generate_ldef_constraint GL env base_ty rst_ty cenv x e.
    Proof. intros x e He. destruct e; try reflexivity; contradiction. Qed.

    Lemma generate_ldef_constraint_inv :
      forall x e c xst xst',
        generate_ldef_constraint GL env base_ty rst_ty cenv x e xst
          = OK (c, xst') ->
        exists ck ckty tf b xst1,
          find_clock cenv x = OK ck
          /\ assign_clk_type env base_ty ck = Some ckty
          /\ assign_lexp_type GL env base_ty rst_ty e xst = OK ([tf], xst1)
          /\ Env.find x env = Some b
          /\ xst' = xst1
          /\ c = cmerge [(merge (merge [rst_ty] ckty) (fst tf), [b])] (snd tf).
    Proof.
      intros x e c xst xst' H.
      unfold generate_ldef_constraint in H.
      eapply sec_bind_inv in H as (ckty & sa & Hck & H).
      eapply sec_bind_inv in H as (ts & sb & Hts & H).
      eapply sec_bind_inv in H as (tf & sc & Htf & H).
      eapply sec_bind_inv in H as (b & sd & Hb & Hret).
      unfold ret in Hret. inv Hret.
      apply single_inv in Htf as (? & ?); subst.
      apply find_env_inv in Hb as (Hb & ?); subst.
      unfold eqn_clock_type in Hck.
      eapply sec_bind_inv in Hck as (ck & se & Hckr & Hcl).
      destruct (find_clock cenv x) as [ck'|] eqn:Ecl; [|discriminate].
      unfold res_to_sec, ret in Hckr. inv Hckr.
      apply option_to_sec_inv in Hcl as (Hcl & ?); subst.
      exists ck, ckty, tf, b, sb.
      split; [first [reflexivity|exact Ecl]|].
      split; [exact Hcl|].
      split; [exact Hts|].
      split; [exact Hb|].
      split; [reflexivity|].
      unfold lconstrain, ambient.
      rewrite !fst_ljoin, fst_lvar. simpl snd.
      now rewrite cmerge_nil2.
    Qed.

    (** * The emitted definitions of a lifting constructor

        One constraint per result, and the witness is chosen to satisfy it
        exactly.  The values are computed from types that live inside
        [bound], and the names being given values are outside [bound], so
        nothing here is self-referential. *)

    Lemma lifted_defs :
      forall bound (xs : list ident) (rhss : list exp) (srcs : list LST)
             ce xst xst' dlt,
        NoDup xs ->
        List.length xs = List.length rhss ->
        (forall b, In b (sec_of xs) -> ~ In b bound) ->
        (forall x ck ckty, In x xs ->
             find_clock cenv x = OK ck ->
             assign_clk_type env base_ty ck = Some ckty ->
             incl (merge [rst_ty] ckty) amb) ->
        st_scoped bound amb ->
        Forall (fun e => (match e with Eapp _ _ _ _ => False | _ => True end)
                         /\ forall ts s s',
                              assign_lexp_type GL env base_ty rst_ty e s
                                = OK (ts, s') ->
                              s' = s /\ List.length ts = 1 /\ carried ts = [])
          rhss ->
        Forall (fun src => st_scoped bound (fst src)) srcs ->
        Forall2 (fun e src =>
            forall tf s s',
              assign_lexp_type GL env base_ty rst_ty e s = OK ([tf], s') ->
              satisfiable dlt (fst tf) (merge amb (fst src))
              /\ st_scoped bound (fst tf)) rhss srcs ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e])) (combine xs rhss)) xst
          = OK (ce, xst') ->
        exists dlt',
          agree_off (sec_of xs) dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ constraints_scoped (bound ++ sec_of xs) ce
          /\ Forall2 (fun x src => forall b, Env.find x env = Some b ->
                          satisfiable dlt' [b] (merge amb (fst src)))
               xs srcs.
    Proof.
      intros bound xs. revert bound.
      induction xs as [|x xs IH];
        intros bound rhss srcs ce xst xst' dlt
          Hnd Hlen Hsep Hamb Hambsc Hpure Hsrcsc Hrel Hgen.
      - destruct rhss; simpl in Hlen; [|discriminate].
        inv Hrel. simpl in Hgen.
        apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
        exists dlt. split; [apply agree_off_refl|].
        split; [constructor|split; [constructor|constructor]].
      - destruct rhss as [|e rhss]; simpl in Hlen; [discriminate|].
        inversion Hrel as [|e0 src0 rhss0 srcs0 Hr Hrelr]; subst.
        inversion Hnd as [|x0 xs0 Hxn Hndr]; subst.
        inversion Hpure as [|e1 rhss1 Hhead Hpurer]; subst.
        inversion Hsrcsc as [|s0 srcs1 Hs0 Hsrcsr]; subst.
        replace (List.map (fun '(x0, e0) => ([x0], [e0]))
                   (combine (x :: xs) (e :: rhss)))
          with (([x], [e])
                :: List.map (fun '(x0, e0) => ([x0], [e0])) (combine xs rhss))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by tauto.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        destruct Hhead as (_ & Hp).
        specialize (Hp _ _ _ Htf) as (? & _ & Hcar); subst xstm.
        rewrite carried_single in Hcar. rewrite Hcar, cmerge_nil.
        specialize (Hr _ _ _ Htf) as (Hdom & Hsc).

        (** the rest of the results *)
        edestruct (IH bound rhss srcs0 cs xst xst' dlt)
          as (dlt1 & Hoff1 & Hce1 & Hscope1 & Hrel1); auto.
        { intros b' Hb'. apply Hsep. now apply sec_of_incl_cons. }
        { intros y cky ckty' Hy. apply Hamb. now right. }

        (** this result: its name gets exactly what its constraint demands *)
        assert (~ In b (sec_of xs)) as Hbx by (eapply sec_of_nIn; eauto).
        assert (~ In b bound) as Hbb by (apply Hsep; eapply sec_of_cons_In; eauto).
        assert (forall X, st_scoped bound X ->
                          hm_ext dlt1 X = hm_ext dlt X) as Hstable.
        { intros X HX. symmetry. eapply hm_ext_off with (xs := sec_of xs); eauto.
          intros y Hy Hin. eapply Hsep; [now apply sec_of_incl_cons; exact Hin|].
          now apply HX. }
        assert (st_scoped bound (merge (merge [rst_ty] ckty) (fst tf))) as Hlsc.
        { apply st_scoped_merge; auto.
          intros y Hy. apply Hambsc. eapply Hamb; eauto. now left. }
        assert (st_scoped bound (merge amb (fst src0))) as Hmsc
            by (apply st_scoped_merge; auto).
        assert (forall X, st_scoped bound X ->
                  hm_ext (upd b (hm_ext dlt1
                                   (merge (merge [rst_ty] ckty) (fst tf)))
                            dlt1) X = hm_ext dlt1 X) as Hstable'.
        { intros X HX. symmetry.
          eapply hm_ext_off with (xs := [b]).
          - intros y Hy. unfold upd.
            destruct (ident_eq_dec y b) as [?|?];
              [exfalso; apply Hy; now left|reflexivity].
          - intros y Hy Hin. destruct Hin as [|[]]; subst. now apply Hbb, HX. }
        assert (satisfiable dlt (merge (merge [rst_ty] ckty) (fst tf))
                  (merge amb (fst src0))) as Hkey.
        { apply satisfiable_merge_intro; [|exact Hdom].
          eapply Lat.order_trans;
            [apply hm_ext_incl, (Hamb x ck ckty); auto; now left|].
          apply satisfiable_merge_l. }

        exists (upd b (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf))) dlt1).
        split; [|split; [|split]].
        + (** only the minted names moved *)
          intros y Hy. rewrite (Hoff1 y); [|intro; apply Hy;
                                            now apply sec_of_incl_cons].
          unfold upd. destruct (ident_eq_dec y b) as [?|?]; [|reflexivity].
          subst. exfalso. apply Hy. eapply sec_of_cons_In; eauto.
        + (** the emitted constraints hold, by construction *)
          apply listSatisfiable_app. split.
          * constructor; [|constructor].
            unfold constraintSatisfiable, satisfiable.
            rewrite hm_ext_single, upd_same, (Hstable' _ Hlsc).
            apply Lat.join_bound1.
          * eapply listSatisfiable_off_scope
              with (sc := bound ++ sec_of xs) (xs := [b]); eauto.
            -- intros y Hy Hin. destruct Hy as [|[]]; subst.
               apply in_app_or in Hin as [Hin|Hin]; [now apply Hbb|now apply Hbx].
            -- intros y Hy. unfold upd.
               destruct (ident_eq_dec y b) as [?|?];
                 [exfalso; apply Hy; now left|reflexivity].
        + (** and stay inside the bound *)
          apply Forall_app. split.
          * constructor; [|constructor].
            intros y Hy. unfold constraint_scope in Hy. simpl in Hy.
            apply in_app_or in Hy as [Hy|Hy].
            -- apply in_or_app. left. now apply Hlsc.
            -- destruct Hy as [|[]]; subst. apply in_or_app. right.
               eapply sec_of_cons_In; eauto.
          * eapply Forall_impl; [|exact Hscope1].
            intros c0 Hc0. eapply constraint_scoped_incl; [|exact Hc0].
            apply incl_app; [apply incl_appl, incl_refl|].
            apply incl_appr, sec_of_incl_cons.
        + (** each result's name dominates the source it replaced *)
          constructor.
          * intros b' Hb'. rewrite Hb in Hb'. inv Hb'.
            apply satisfiable_singleton. rewrite upd_same.
            rewrite (Hstable' _ Hmsc), (Hstable _ Hlsc), (Hstable _ Hmsc).
            exact Hkey.
          * eapply Forall2_impl_In; [|exact Hrel1].
            intros y src Hy Hsrc Hyr b' Hb'.
            eapply satisfiable_off with (xs := [b]); eauto.
            -- intros z Hz. unfold upd.
               destruct (ident_eq_dec z b) as [?|?];
                 [exfalso; apply Hz; now left|reflexivity].
            -- intros z Hz Hin. destruct Hz as [|[]]; subst.
               destruct Hin as [|[]]; subst.
               apply Hbx. unfold sec_of. apply in_flat_map.
               exists y. split; auto. rewrite Hb'. now left.
            -- intros z Hz Hin. destruct Hin as [|[]]; subst.
               apply in_merge_inv in Hz as [Hz|Hz].
               ++ now apply Hbb, Hambsc.
               ++ apply Hbb. eapply Forall_forall in Hsrcsr; [|exact Hsrc].
                  now apply Hsrcsr.
    Qed.

    (** * The delay, and the initialised delay

        [Efby] and [Earrow] lift the same way: the operands are unnested, the
        pass builds one delay per result out of the i-th of each, mints a
        variable for it and emits its defining equation.  Both sides then
        build their result with the plain componentwise join -- no head -- so
        the join lemmas are reused at [lbot]. *)

    Lemma satisfiable_nil : forall dlt X, satisfiable dlt [] X.
    Proof. intros. unfold satisfiable. simpl. apply Lat.bottom_is_bottom. Qed.

    Lemma map_ljoin_lbot :
      forall ts, List.map (fun t => ljoin lbot t) ts = ts.
    Proof.
      induction ts as [|t ts IH]; [reflexivity|].
      simpl. rewrite IH. f_equal. unfold ljoin, lbot. simpl.
      rewrite merge_nil2, cmerge_nil2. now destruct t.
    Qed.

    Corollary ljoin_list_rel_plain :
      forall dlt ts us rs ts' us' rs' s1 s1' s2 s2',
        ljoin_list ts us s1 = OK (rs, s1') ->
        ljoin_list ts' us' s2 = OK (rs', s2') ->
        Forall2 (fun t t' => satisfiable dlt (fst t') (merge amb (fst t)))
          ts ts' ->
        Forall2 (fun u u' => satisfiable dlt (fst u') (merge amb (fst u)))
          us us' ->
        Forall2 (fun r r' => satisfiable dlt (fst r') (merge amb (fst r)))
          rs rs'.
    Proof.
      intros dlt ts us rs ts' us' rs' s1 s1' s2 s2' Hj Hj' Hts Hus.
      eapply ljoin_list_rel_head with (h := lbot) (h' := lbot);
        try rewrite map_ljoin_lbot; eauto.
    Qed.

    Corollary ljoin_list_scoped_plain :
      forall sc ts us rs s s',
        ljoin_list ts us s = OK (rs, s') ->
        Forall (fun t => st_scoped sc (fst t)) ts ->
        Forall (fun u => st_scoped sc (fst u)) us ->
        Forall (fun r => st_scoped sc (fst r)) rs.
    Proof.
      intros sc ts us rs s s' Hj Hts Hus.
      eapply ljoin_list_scoped_head with (h := lbot);
        try rewrite map_ljoin_lbot; eauto.
      intros y Hy. contradiction.
    Qed.

    Corollary ljoin_list_scoped_plain_inv :
      forall sc ts us rs s s',
        ljoin_list ts us s = OK (rs, s') ->
        Forall (fun r => st_scoped sc (fst r)) rs ->
        Forall (fun t => st_scoped sc (fst t)) ts
        /\ Forall (fun u => st_scoped sc (fst u)) us.
    Proof.
      intros sc ts us rs s s' Hj Hrs.
      rewrite <- (map_ljoin_lbot ts) in Hj.
      eapply ljoin_list_scoped_head_inv in Hj as (? & ? & _); eauto.
    Qed.

    Lemma assign_lexps_elementwise :
      forall es ts st st',
        Forall normalized_cexp es ->
        assign_lexps GL env base_ty rst_ty es st = OK (ts, st') ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es ts.
    Proof.
      induction es as [|e es IH]; intros ts st st' Hn H.
      - apply (assign_lexps_carried_nil GL env base_ty rst_ty) in H
          as (? & _ & ?); subst. constructor.
      - inv Hn.
        apply (assign_lexps_carried_cons GL env base_ty rst_ty) in H
          as (t & r & sta & Ht & Hr & ? & _); subst.
        assert (sta = st /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (t, s))
          as (? & Hlt & Hc & Hs)
          by (eapply assign_lexp_normalized_cexp_pure; eauto).
        subst sta.
        destruct t as [|a [|]]; simpl in Hlt; try discriminate.
        rewrite carried_single in Hc.
        simpl List.app. constructor; [split; [exact Hs|exact Hc]|].
        eapply IH; eauto.
    Qed.

    Lemma unnest_fby_nil :
      forall es anns, unnest_fby [] es anns = [].
    Proof. reflexivity. Qed.

    Lemma unnest_fby_cons :
      forall e0 e0s e es a anns,
        unnest_fby (e0 :: e0s) (e :: es) (a :: anns)
        = Efby [e0] [e] [a] :: unnest_fby e0s es anns.
    Proof. reflexivity. Qed.

    Lemma unnest_arrow_nil :
      forall es anns, unnest_arrow [] es anns = [].
    Proof. reflexivity. Qed.

    Lemma unnest_arrow_cons :
      forall e0 e0s e es a anns,
        unnest_arrow (e0 :: e0s) (e :: es) (a :: anns)
        = Earrow [e0] [e] [a] :: unnest_arrow e0s es anns.
    Proof. reflexivity. Qed.

    Lemma assign_lexp_fby_type :
      forall e0 e a t0 t1 tf s s',
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty (Efby [e0] [e] [a]) s
          = OK ([tf], s') ->
        tf = ljoin t0 t1.
    Proof.
      intros e0 e a t0 t1 tf s s' H0 H1 H.
      rewrite assign_lexp_Efby in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht.
      rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma assign_lexp_arrow_type :
      forall e0 e a t0 t1 tf s s',
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        assign_lexp_type GL env base_ty rst_ty (Earrow [e0] [e] [a]) s
          = OK ([tf], s') ->
        tf = ljoin t0 t1.
    Proof.
      intros e0 e a t0 t1 tf s s' H0 H1 H.
      rewrite assign_lexp_Earrow in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht.
      rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. now inv Hr.
    Qed.

    Lemma vars_defined_defs :
      forall (bs : list ident) (rhss : list exp),
        List.length bs = List.length rhss ->
        vars_defined (List.map (fun '(x, e) => ([x], [e])) (combine bs rhss))
        = bs.
    Proof.
      induction bs as [|b bs IH]; intros rhss Hlen; [reflexivity|].
      destruct rhss as [|e rhss]; simpl in Hlen; [discriminate|].
      simpl. f_equal. apply IH. congruence.
    Qed.

    Lemma assign_lexp_fby_pure :
      forall e0 e a t0 t1,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty (Efby [e0] [e] [a]) s
            = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros e0 e a t0 t1 H0 H1 Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Efby in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin. simpl snd.
      rewrite Hc0, Hc1. reflexivity.
    Qed.

    Lemma assign_lexp_arrow_pure :
      forall e0 e a t0 t1,
        (forall s, assign_lexp_type GL env base_ty rst_ty e0 s = OK ([t0], s)) ->
        (forall s, assign_lexp_type GL env base_ty rst_ty e s = OK ([t1], s)) ->
        snd t0 = [] -> snd t1 = [] ->
        forall ts s s',
          assign_lexp_type GL env base_ty rst_ty (Earrow [e0] [e] [a]) s
            = OK (ts, s') ->
          s' = s /\ List.length ts = 1 /\ carried ts = [].
    Proof.
      intros e0 e a t0 t1 H0 H1 Hc0 Hc1 ts s s' H.
      rewrite assign_lexp_Earrow in H.
      eapply sec_bind_inv in H as (t & sa & Ht & H).
      eapply sec_bind_inv in H as (u & sb & Hu & Hj).
      apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
      rewrite H0 in Ht. inv Ht. rewrite H1 in Hu. inv Hu.
      simpl in Hj. eapply sec_bind_inv in Hj as (r & sc & Hr & Hret).
      unfold ret in Hret. inv Hret.
      simpl in Hr. unfold ret in Hr. inv Hr.
      split; [reflexivity|split; [reflexivity|]].
      rewrite carried_single. unfold ljoin. simpl snd.
      rewrite Hc0, Hc1. reflexivity.
    Qed.

    (** The delays the pass builds, typed: the i-th delay's type is the i-th
        componentwise join of the operands' types, which is the same function
        of them that the source rule is of the source operands' types. *)

    Lemma unnest_fby_types :
      forall (e0s es : list exp) (anns : list ann) ts0 us s,
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) e0s ts0 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es us ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        exists rs,
          ljoin_list ts0 us s = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_fby e0s es anns) rs.
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts0 us s H0 H1 Hl0 Hl1.
      - inv H0. destruct anns; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate]. inv H1.
        exists []. split; [reflexivity|constructor].
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inversion H0 as [|p q ps qs Hp H0r]; subst.
        inversion H1 as [|p2 q2 ps2 qs2 Hp2 H1r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct IH as (rs & Hj & Hall); eauto.
        exists (ljoin q q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_fby_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_fby_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_fby_type; eauto.
    Qed.

    Lemma unnest_arrow_types :
      forall (e0s es : list exp) (anns : list ann) ts0 us s,
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) e0s ts0 ->
        Forall2 (fun e t =>
                   (forall s,
                      assign_lexp_type GL env base_ty rst_ty e s = OK ([t], s))
                   /\ snd t = []) es us ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        exists rs,
          ljoin_list ts0 us s = OK (rs, s)
          /\ Forall2 (fun e r =>
                (match e with Eapp _ _ _ _ => False | _ => True end)
                /\ (forall ts s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK (ts, s0') ->
                      s0' = s0 /\ List.length ts = 1 /\ carried ts = [])
                /\ (forall tf s0 s0',
                      assign_lexp_type GL env base_ty rst_ty e s0 = OK ([tf], s0') ->
                      tf = r))
               (unnest_arrow e0s es anns) rs.
    Proof.
      induction e0s as [|e0 e0s IH];
        intros es anns ts0 us s H0 H1 Hl0 Hl1.
      - inv H0. destruct anns; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate]. inv H1.
        exists []. split; [reflexivity|constructor].
      - destruct anns as [|a anns]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inversion H0 as [|p q ps qs Hp H0r]; subst.
        inversion H1 as [|p2 q2 ps2 qs2 Hp2 H1r]; subst.
        destruct Hp as (Hs0 & Hc0). destruct Hp2 as (Hs1 & Hc1).
        edestruct IH as (rs & Hj & Hall); eauto.
        exists (ljoin q q2 :: rs). split.
        + simpl. eapply sec_bind_ok; [exact Hj|]. reflexivity.
        + rewrite unnest_arrow_cons. constructor; auto.
          split; [exact I|split].
          * eapply assign_lexp_arrow_pure; eauto.
          * intros tf s0 s0' Htf. eapply assign_lexp_arrow_type; eauto.
    Qed.

    (** * Recovering the operands from the emitted equations

        For [Ewhen], [Emerge] and [Eite] the operands' target typings come out
        of the target typing of the whole expression, because the target
        expression list is built from the unnested operands.  For [Efby] and
        [Earrow] it is not: the target list is the minted variables, and the
        operands appear only inside the emitted equations, as the operands of
        the delays those equations bind.  So they are recovered from the
        emitted block instead. *)

    Lemma defs_operand_types_fby :
      forall (bs : list ident) (e0s es : list exp) (anns : list ann)
             ce xst xst',
        Forall normalized_lexp e0s ->
        Forall normalized_lexp es ->
        List.length bs = List.length anns ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_fby e0s es anns))) xst = OK (ce, xst') ->
        exists ts0 us,
          assign_lexps GL env base_ty rst_ty e0s xst = OK (ts0, xst)
          /\ assign_lexps GL env base_ty rst_ty es xst = OK (us, xst).
    Proof.
      induction bs as [|b bs IH];
        intros e0s es anns ce xst xst' Hn0 Hn1 Hlb Hl0 Hl1 Hgen.
      - destruct anns; simpl in Hlb; [|discriminate].
        destruct e0s; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct anns as [|a anns]; simpl in Hlb; [discriminate|].
        destruct e0s as [|e0 e0s]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_fby_cons in Hgen.
        replace (List.map (fun '(x0, e1) => ([x0], [e1]))
                   (combine (b :: bs) (Efby [e0] [e] [a] :: unnest_fby e0s es anns)))
          with (([b], [Efby [e0] [e] [a]])
                :: List.map (fun '(x0, e1) => ([x0], [e1]))
                     (combine bs (unnest_fby e0s es anns)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Efby in Htf.
        eapply sec_bind_inv in Htf as (t & sa & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sb & Hu & Hj).
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sa = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                              = OK (t, s)) as (? & _ & _ & Hs0)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
        subst sa.
        assert (sb = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (u, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        subst sb.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH e0s es anns cs xst xst') as (ts0 & us & Hts0 & Hus);
          eauto.
        exists (t ++ ts0), (u ++ us). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs0|].
          eapply sec_bind_ok; [exact Hts0|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hus|]. reflexivity.
    Qed.

    Lemma defs_operand_types_arrow :
      forall (bs : list ident) (e0s es : list exp) (anns : list ann)
             ce xst xst',
        Forall normalized_lexp e0s ->
        Forall normalized_lexp es ->
        List.length bs = List.length anns ->
        List.length e0s = List.length anns ->
        List.length es = List.length anns ->
        generate_leqns_constraints GL env base_ty rst_ty cenv
          (List.map (fun '(x, e) => ([x], [e]))
             (combine bs (unnest_arrow e0s es anns))) xst = OK (ce, xst') ->
        exists ts0 us,
          assign_lexps GL env base_ty rst_ty e0s xst = OK (ts0, xst)
          /\ assign_lexps GL env base_ty rst_ty es xst = OK (us, xst).
    Proof.
      induction bs as [|b bs IH];
        intros e0s es anns ce xst xst' Hn0 Hn1 Hlb Hl0 Hl1 Hgen.
      - destruct anns; simpl in Hlb; [|discriminate].
        destruct e0s; simpl in Hl0; [|discriminate].
        destruct es; simpl in Hl1; [|discriminate].
        exists [], []. rewrite assign_lexps_nil. auto.
      - destruct anns as [|a anns]; simpl in Hlb; [discriminate|].
        destruct e0s as [|e0 e0s]; simpl in Hl0; [discriminate|].
        destruct es as [|e es]; simpl in Hl1; [discriminate|].
        inv Hn0. inv Hn1.
        rewrite unnest_arrow_cons in Hgen.
        replace (List.map (fun '(x0, e1) => ([x0], [e1]))
                   (combine (b :: bs)
                      (Earrow [e0] [e] [a] :: unnest_arrow e0s es anns)))
          with (([b], [Earrow [e0] [e] [a]])
                :: List.map (fun '(x0, e1) => ([x0], [e1]))
                     (combine bs (unnest_arrow e0s es anns)))
          in Hgen by reflexivity.
        rewrite generate_leqns_constraints_cons in Hgen.
        eapply sec_bind_inv in Hgen as (c & xst1 & Hc & Hgen).
        eapply sec_bind_inv in Hgen as (cs & xst2 & Hcs & Hret).
        unfold ret in Hret. inv Hret.
        rewrite generate_leqn_constraint_def in Hc by exact I.
        apply generate_ldef_constraint_inv in Hc
          as (ck & ckty & tf & b' & xstm & Hck & Hcl & Htf & Hb & ? & ?); subst.
        rewrite assign_lexp_Earrow in Htf.
        eapply sec_bind_inv in Htf as (t & sa & Ht & Htf).
        eapply sec_bind_inv in Htf as (u & sb & Hu & Hj).
        apply assign_lexps_single in Ht. apply assign_lexps_single in Hu.
        assert (sa = xst /\ List.length t = 1 /\ carried t = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e0 s
                              = OK (t, s)) as (? & _ & _ & Hs0)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e0); eauto).
        subst sa.
        assert (sb = xst /\ List.length u = 1 /\ carried u = []
                /\ forall s, assign_lexp_type GL env base_ty rst_ty e s
                              = OK (u, s)) as (? & _ & _ & Hs1)
          by (eapply assign_lexp_normalized_lexp_pure with (e := e); eauto).
        subst sb.
        assert (xstm = xst) as ? by (eapply ljoin_list_pure; eauto). subst xstm.
        edestruct (IH e0s es anns cs xst xst') as (ts0 & us & Hts0 & Hus);
          eauto.
        exists (t ++ ts0), (u ++ us). split.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs0|].
          eapply sec_bind_ok; [exact Hts0|]. reflexivity.
        + rewrite assign_lexps_cons.
          eapply sec_bind_ok; [apply Hs1|].
          eapply sec_bind_ok; [exact Hus|]. reflexivity.
    Qed.

    Lemma map_bind2_unnest_normalized_lexp :
      forall P es es' eqs st st',
        map_bind2 (unnest_exp P false) es st = ((es', eqs), st') ->
        Forall normalized_lexp (List.concat es').
    Proof.
      induction es as [|e es IH]; intros es' eqs st st' H.
      - apply map_bind2_unnest_nil in H as (? & ? & ?); subst. constructor.
      - apply map_bind2_unnest_cons in H
          as (e' & eq1 & st1 & es'r & eqsr & H1 & H2 & ? & ?); subst.
        simpl List.concat. apply Forall_app. split.
        + eapply unnest_exp_normalized_lexp; eauto.
        + eapply IH; eauto.
    Qed.

    Lemma Forall2_combine_via :
      forall {A B C : Type} (P : A -> C -> Prop) (Q : B -> C -> Prop)
             (R : A -> B -> Prop) (l1 : list A) (l2 : list B) (l3 : list C),
        Forall2 P l1 l3 -> Forall2 Q l2 l3 ->
        (forall a b c, P a c -> Q b c -> R a b) ->
        Forall2 R l1 l2.
    Proof.
      intros A B C P Q R l1. revert l1.
      induction l1 as [|a l1 IH]; intros l2 l3 H1 H2 Himp.
      - inv H1. inv H2. constructor.
      - inversion H1 as [|a0 c0 l1' l3' Hac H1r]; subst.
        inversion H2 as [|b0 c1 l2' l3'' Hbc H2r]; subst.
        constructor; [eapply Himp; eauto|eapply IH; eauto].
    Qed.

  End Preservation.

End SECLUSUNNESTING.

Module SecLusUnnesting
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
  <: SECLUSUNNESTING Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.

Include SECLUSUNNESTING Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.

End SecLusUnnesting.
