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
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
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

  Section Preservation.

    Variable GL      : secglobal.
    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.

    (** The *target* node's declared clocks.  [lnode_clock_env_extended] above
        is what says using the target's here loses nothing: on every variable
        the source equations mention, the two environments answer alike. *)
    Variable cenv    : Env.t (type * clock).

    (** Every security name the *source* expression can mention: the names of
        the source node's own variables, and the names the security monad
        mints for its nested calls. *)
    Variable scope   : list ident.

    (** The ambient every equation this expression gets lifted into sits
        under. *)
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

    Definition carries (P : global) (e : exp) : Prop :=
      forall is_control es' eqs st st' ts sst sst'
             ce xst xst' ts'' yst yst' dlt,
        wl_exp P e ->
        (forall x, In x (moved_by st st') -> ~ In x scope) ->
        constraints_scoped scope (carried ts) ->
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
               ts ts''.

    (** Nothing was emitted, so nothing has to be satisfied. *)

    Lemma generate_leqns_constraints_nil :
      forall ce xst xst',
        generate_leqns_constraints GL env base_ty rst_ty cenv [] xst
          = OK (ce, xst') ->
        ce = [] /\ xst' = xst.
    Proof.
      intros ce xst xst' H. simpl in H. unfold ret in H. inv H. auto.
    Qed.

    (** A one-element expression list is typed by its element. *)

    Lemma assign_lexps_single :
      forall e ts st st',
        assign_lexps GL env base_ty rst_ty [e] st = OK (ts, st') ->
        assign_lexp_type GL env base_ty rst_ty e st = OK (ts, st').
    Proof.
      intros e ts st st' H.
      apply assign_lexps_carried_cons in H as (t & r & sta & Ht & Hr & Hts & _).
      apply assign_lexps_carried_nil in Hr as (Hr & _ & ?); subst.
      now rewrite app_nil_r.
    Qed.

    (** The shape both leaves land in: the pass returned the expression
        untouched, so the two generators ran on the same term, and the
        witness is the valuation we started with. *)

    Lemma carries_unchanged :
      forall mv (ts ts'' : list LST) (ce : list constraint) dlt,
        ts'' = ts ->
        ce = [] ->
        exists dlt',
          agree_off mv dlt dlt'
          /\ listSatisfiable dlt' ce
          /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
               ts ts''.
    Proof.
      intros mv ts ts'' ce dlt Hts Hce; subst.
      exists dlt. split; [|split].
      - apply agree_off_refl.
      - constructor.
      - induction ts as [|t ts IH]; [constructor|].
        constructor; [apply satisfiable_merge_r|exact IH].
    Qed.

    Lemma carries_Econst : forall P c, carries P (Econst c).
    Proof.
      intros P c is_control es' eqs st st' ts sst sst' ce xst xst' ts'' yst yst'
        dlt _ _ _ Hun Has Hgen Has' _.
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
        dlt _ _ _ Hun Has Hgen Has' _.
      rewrite unnest_exp_Evar in Hun. inv Hun.
      apply generate_leqns_constraints_nil in Hgen as (? & ?); subst.
      apply assign_lexps_single in Has'.
      apply assign_lexp_Evar_inv in Has as (b & Hb & ? & ?); subst.
      apply assign_lexp_Evar_inv in Has' as (b' & Hb' & ? & ?); subst.
      rewrite Hb in Hb'. inv Hb'.
      eapply carries_unchanged; auto.
    Qed.

    Lemma assign_lexps_single_intro :
      forall e ts st st',
        assign_lexp_type GL env base_ty rst_ty e st = OK (ts, st') ->
        assign_lexps GL env base_ty rst_ty [e] st = OK (ts, st').
    Proof.
      intros e ts st st' H.
      rewrite assign_lexps_cons.
      eapply sec_bind_ok; [exact H|].
      eapply sec_bind_ok with (y := ([] : list LST));
        [rewrite assign_lexps_nil; reflexivity|].
      unfold ret. now rewrite app_nil_r.
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
        yst yst' dlt Hwl Hincl Hsc Hun Has Hgen Has' Hcar.
      inv Hwl.
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
  <: SECLUSUNNESTING Ids Op OpAux Lat SecT SLT SC LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.

Include SECLUSUNNESTING Ids Op OpAux Lat SecT SLT SC LSyn CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.

End SecLusUnnesting.
