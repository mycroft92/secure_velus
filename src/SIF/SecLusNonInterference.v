(** Noninterference for Lustre, by pull-back along transcription.

    [SecNLusNonInterference.v] proves noninterference for NLustre from
    [node_security] -- the predicate that says a node's generated signature and
    raw constraints are satisfied, and that every callee is secure at the
    valuation the call site induces.  This file does the same job for Lustre
    without reproving any of it.

    [lnode_security] is the Lustre spelling of [node_security]: same shape,
    read off the Lustre generator.  [lnode_security_transcribes] turns it into
    [node_security] for the transcribed node, *at the same pair of
    valuations*.  That is what [entails] buys over [preserves_on]: transcription
    introduces no variables, so the witness never has to be adjusted, and the
    two security predicates are about one valuation rather than two related
    ones.

    The Lustre-facing statement is then [node_noninterference_outputs]
    composed with the pull-back. *)

From Coq Require Import List.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import Transcription.Tr.
From Velus Require Import Transcription.TrClocking.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecLusNLusTranslation.
From Velus Require Import SIF.SecNLusNonInterference.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLUSNONINTERFERENCE
  (Import Ids     : IDS)
  (Import Lat     : Lattice)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import SecT    : SECTYPES Lat)
  (Import LSyn    : LSYNTAX Ids Op)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CETyp          : CETYPING Ids Op CESyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Str            : INDEXEDSTREAMS Op OpAux)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (NLMem          : MEMORIES Ids Op CESyn NLSyn)
  (NLIsD          : ISDEFINED Ids Op CESyn NLSyn NLMem)
  (NLIsF          : ISFREE Ids Op CESyn NLSyn CEIsF)
  (NLCaus         : NLUSTRECAUSALITY Ids Op CESyn NLSyn CEIsF NLIsF)
  (NLClo          : NLCLOCKING Ids Op CESyn NLSyn NLOrd NLMem NLIsD CEIsF NLIsF CEClo)
  (CESem          : CESEMANTICS Ids Op OpAux CESyn Str)
  (CEProps        : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Indexed        : NLINDEXEDSEMANTICS Ids Op OpAux CESyn NLSyn Str NLOrd CESem)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import SECNL   : SECNLUSTYPING Ids Op SC CESyn NLSyn SIG NAMEGEN CEIsF CEClo
                      SECCET NLOrd NLMem NLIsD NLIsF NLClo)
  (SECNLC         : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn NLSyn Lat SecT SIG
                      SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd NLMem NLIsD
                      NLIsF NLClo SECNL)
  (SECLNG         : SECLNAMEGEN Ids Op OpAux LSyn CESyn NLSyn NAMEGEN TR)
  (LClo           : LCLOCKING Ids Op LSyn)
  (TRC            : TRCLOCKING Ids Op OpAux LSyn LClo CESyn NLSyn NLOrd NLMem
                      NLIsD CEIsF NLIsF CEClo NLClo TR)
  (Import NLNI    : SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT
                      CESyn NLSyn SIG NAMEGEN CETyp CEIsF CEClo SECCET Str
                      NLOrd NLMem NLIsD NLIsF NLCaus NLClo CESem CEProps
                      Indexed SIGPROOFS SECNL SECNLC)
  (Import SECLNL  : SECLUSNLUSTRANSLATION Ids Op OpAux SC LSyn CESyn NLSyn Lat
                      SecT STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET NLOrd
                      NLMem NLIsD NLIsF NLClo TR SECL SECNL SECNLC SECLNG LClo
                      TRC).

  Import SECMONADNotations.

  (** * Two signatures that agree on their interface induce the same call
        valuation

      [lat_valuation] reads a callee signature only through [s_in], [s_out],
      [s_clk] and [s_reset].  [Signature_entails] keeps all four aligned, so a
      call site induces literally the same valuation whichever global it read
      its callee from -- which is what lets the pull-back stay at one pair of
      valuations instead of relating two. *)

  Lemma lat_valuation_fields_agree :
    forall dlt n1 n2 inp clk rst out,
      signature_fields_agree n1 n2 ->
      SIGPROOFS.lat_valuation dlt n1 inp clk rst out
      = SIGPROOFS.lat_valuation dlt n2 inp clk rst out.
  Proof.
    intros dlt n1 n2 inp clk rst out (Hin & Hout & Hrst & Hclk).
    unfold SIGPROOFS.lat_valuation.
    rewrite Hin, Hout, Hrst, Hclk. reflexivity.
  Qed.

  (** An equation of a transcribed body comes from an equation of the source
      body.  The call clauses of [node_security] quantify over the target's
      equations, so the pull-back needs to walk back across [mmap]. *)

  Lemma to_equations_In_inv :
    forall cenv envo eqs neqs eq',
      Errors.mmap (to_equation cenv envo) eqs = OK neqs ->
      In eq' neqs ->
      exists eq, In eq eqs /\ to_equation cenv envo eq = OK eq'.
  Proof.
    intros cenv envo eqs. induction eqs as [|eq eqs IH];
      intros neqs eq' Hmap Hin; simpl in Hmap.
    - inv Hmap. inversion Hin.
    - monadInv Hmap. simpl in Hin. destruct Hin as [Heq|Hin].
      + subst. exists eq. split; [now left|exact EQ].
      + destruct (IH _ _ EQ1 Hin) as (e & He & Hte).
        exists e. split; [now right|exact Hte].
  Qed.

  (** * Security of a Lustre node

      The Lustre spelling of [SecNLusNonInterferenceSupport.node_security]:
      the node's signature is the one the global stores and the one the
      generator produces, its raw constraints are satisfied by [dlt_raw],
      its stored constraints by [dlt_sig], the two agree on the signature
      scope, and every callee is secure at the valuation its call site
      induces.

      Two things differ from the NLustre spelling, both of them the Lustre
      generator's doing rather than this predicate's.  The raw run threads a
      fresh-name state, because a nested call mints; so the eliminated names
      are the node's locals *and* whatever was minted.  And a call's argument
      types come from [assign_lexps], which returns a carried-constraint
      component alongside each type -- [map fst] is the part a callee is
      instantiated at. *)

  Section GENERATED_LNODE_SECURITY.
    Variable all_lnodes : list node.
    Variable GL : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    Inductive lnode_security
      : node -> ground_instantiation -> ground_instantiation -> Prop :=
    | SecureLNode :
        forall nd dlt_sig dlt_raw ty_env sig
               clk_id rst_id clk_type rst_type inp out locals raw st0 st_n,
          find_node nd.(n_name) all_lnodes = Some nd ->
          find_node_env nd.(n_name) envs = Some ty_env ->
          find_signature nd.(n_name) GL = Some sig ->
          generate_lnode_sig GL nd ty_env aux_names st0 = OK (sig, st_n) ->
          get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
          Env.find clk_id ty_env = Some clk_type ->
          Env.find rst_id ty_env = Some rst_type ->
          get_mappings_from_node nd.(n_in) ty_env = Some inp ->
          get_mappings_from_node nd.(n_out) ty_env = Some out ->
          get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
          generate_leqns_constraints GL ty_env clk_type rst_type
            (lnode_clock_env nd) nd.(n_eqs) st0 = OK (raw, st_n) ->
          sig = {| s_name  := nd.(n_name);
                   s_in    := inp;
                   s_out   := out;
                   s_reset := rst_type;
                   s_clk   := clk_type;
                   s_constraints :=
                     SymTypes.simplify raw (locals ++ minted st0 st_n) |} ->
          signature_satisfied dlt_sig sig ->
          agree_on (signature_scope sig) dlt_sig dlt_raw ->
          listSatisfiable dlt_raw raw ->

          (forall xs f args a callee callee_sig ckty argts outtyp sta stb,
              In (xs, [Eapp f args None a]) nd.(n_eqs) ->
              find_node f all_lnodes = Some callee ->
              find_signature f GL = Some callee_sig ->
              assign_clk_type ty_env sig.(s_clk)
                (find_base_clock (clocksof args)) = Some ckty ->
              assign_lexps GL ty_env sig.(s_clk) sig.(s_reset) args sta
                = OK (argts, stb) ->
              get_mappings xs ty_env = Some outtyp ->
              lnode_security callee
                (SIGPROOFS.lat_valuation dlt_sig callee_sig (map fst argts) ckty
                   [sig.(s_reset)] outtyp)
                (SIGPROOFS.lat_valuation dlt_raw callee_sig (map fst argts) ckty
                   [sig.(s_reset)] outtyp)) ->

          (forall xs f args r rty0 ckr nm a callee callee_sig
                  ckty rty rstck argts outtyp sta stb,
              In (xs, [Eapp f args (Some (Evar r (rty0, (ckr, nm)))) a])
                 nd.(n_eqs) ->
              find_node f all_lnodes = Some callee ->
              find_signature f GL = Some callee_sig ->
              assign_clk_type ty_env sig.(s_clk)
                (find_base_clock (clocksof args)) = Some ckty ->
              Env.find r ty_env = Some rty ->
              assign_clk_type ty_env sig.(s_clk) ckr = Some rstck ->
              assign_lexps GL ty_env sig.(s_clk) sig.(s_reset) args sta
                = OK (argts, stb) ->
              get_mappings xs ty_env = Some outtyp ->
              lnode_security callee
                (SIGPROOFS.lat_valuation dlt_sig callee_sig (map fst argts) ckty
                   (merge [sig.(s_reset)] (merge [rty] rstck)) outtyp)
                (SIGPROOFS.lat_valuation dlt_raw callee_sig (map fst argts) ckty
                   (merge [sig.(s_reset)] (merge [rty] rstck)) outtyp)) ->
          lnode_security nd dlt_sig dlt_raw.

  End GENERATED_LNODE_SECURITY.

  (** * Transporting a node's security data

      This is where the leg pays off.  [node_security] wants one pair of
      valuations; a preservation stated as [preserves_on] would only give a
      *related* pair, and the predicate would have to be weakened to say so.
      [entails] gives the same pair: the raw constraints transport under
      [dlt_raw] untouched, and the stored ones then follow for [dlt_sig]
      because the two agree on the signature scope and the stored constraints
      live in it.

      [signature_satisfied dlt_sig lsig] is not even needed as an input --
      raw satisfaction plus the agreement already imply it on either side. *)

  Lemma security_data_transports :
    forall lsig nsig rawL rawN ds dlt_sig dlt_raw,
      signature_fields_agree lsig nsig ->
      nsig.(s_constraints) = SymTypes.simplify rawN ds ->
      entails rawL rawN ->
      signature_scoped nsig ->
      agree_on (signature_scope lsig) dlt_sig dlt_raw ->
      listSatisfiable dlt_raw rawL ->
      signature_satisfied dlt_sig nsig
      /\ agree_on (signature_scope nsig) dlt_sig dlt_raw
      /\ listSatisfiable dlt_raw rawN.
  Proof.
    intros lsig nsig rawL rawN ds dlt_sig dlt_raw
           Hfields HnsigC Hent Hscoped Hagree HsatL.
    assert (Hscope : signature_scope lsig = signature_scope nsig)
      by (eapply signature_scope_agree; exact Hfields).
    assert (HsatN : listSatisfiable dlt_raw rawN)
      by (eapply entails_sat; eauto).
    assert (Hagree' : agree_on (signature_scope nsig) dlt_sig dlt_raw)
      by (rewrite <- Hscope; exact Hagree).
    repeat split; auto.
    unfold signature_satisfied, signature_constraints.
    eapply listSatisfiable_ext with (dlt1 := dlt_raw) (scope := signature_scope nsig).
    - exact Hscoped.
    - intros x Hin. symmetry. now apply Hagree'.
    - rewrite HnsigC. apply simplify_correct. exact HsatN.
  Qed.

  (** * Inverting a transcribed call

      [node_security]'s call clauses quantify over the *target*'s equations, so
      the pull-back walks back to the source equation and then to its shape.
      [to_equation] produces an [EqApp] only from an [Eapp], so the shape is
      forced. *)

  Lemma to_equation_EqApp_inv :
    forall cenv envo eq xs ck f les,
      to_equation cenv envo eq = OK (NLSyn.EqApp xs ck f les None) ->
      exists args a,
        eq = (xs, [Eapp f args None a])
        /\ Errors.mmap to_lexp args = OK les
        /\ ck = find_base_clock (clocksof args).
  Proof.
    intros cenv envo [ys es] xs ck f les Htr.
    destruct es as [|e [|e' es']]; simpl in Htr; try discriminate.
    destruct e; try (destruct ys as [|y [|]]; simpl in Htr; monadInv Htr).
    - (* Efby *)
      destruct l as [|e0 [|e0' l']]; destruct l0 as [|e1 [|e1' l0']];
        try (destruct ys as [|y [|]]; simpl in Htr; monadInv Htr).
    - (* Eapp *)
      destruct o as [er|].
      + destruct er; simpl in Htr; try monadInv Htr.
        destruct a as [ty [ckr nm]]. monadInv Htr.
      + monadInv Htr. exists l, l0. auto.
  Qed.

  Lemma to_equation_EqApp_reset_inv :
    forall cenv envo eq xs ck f les r ckr,
      to_equation cenv envo eq = OK (NLSyn.EqApp xs ck f les (Some (r, ckr))) ->
      exists args ty nm a,
        eq = (xs, [Eapp f args (Some (Evar r (ty, (ckr, nm)))) a])
        /\ Errors.mmap to_lexp args = OK les
        /\ ck = find_base_clock (clocksof args).
  Proof.
    intros cenv envo [ys es] xs ck f les r ckr Htr.
    destruct es as [|e [|e' es']]; simpl in Htr; try discriminate.
    destruct e; try (destruct ys as [|y [|]]; simpl in Htr; monadInv Htr).
    - (* Efby *)
      destruct l as [|e0 [|e0' l']]; destruct l0 as [|e1 [|e1' l0']];
        try (destruct ys as [|y [|]]; simpl in Htr; monadInv Htr).
    - (* Eapp *)
      destruct o as [er|]; [|monadInv Htr].
      destruct er; simpl in Htr; try monadInv Htr.
      destruct a as [ty [ckx nm]]. monadInv Htr.
      exists l, ty, nm, l0. auto.
  Qed.

  (** [tonodeInv] replaces the target node by the record it is built from,
      which loses the name the rest of the proof rewrites against.  This keeps
      [nd'] abstract and hands back only the fact wanted: its body is the
      source body, transcribed. *)

  Lemma to_node_eqs :
    forall nd nd' Hpn,
      to_node nd Hpn = OK nd' ->
      Errors.mmap
        (to_equation (lnode_clock_env nd)
           (fun x => if Env.mem x (Env.from_list nd.(n_out))
                     then Error (msg "output variable defined as a fby")
                     else OK tt))
        nd.(n_eqs) = OK nd'.(NLSyn.n_eqs).
  Proof.
    intros nd nd' Hpn Htn. pose proof Htn as H. tonodeInv H. exact Hmmap.
  Qed.

  (** * The pull-back

      What a node needs beyond [lnode_security] is the context
      [SecLusNLusTranslation] reads a call site in, and the NLustre generator's
      own output for the node.  Both are facts about the NLustre side, which
      the program-level preservation theorem establishes, so both are supplied
      by the caller rather than re-derived here. *)

  Definition transcribed_program_context
    (all_lnodes : list node) (P : NLSyn.global) (GL GN : secglobal)
    (envs : node_scoped_env) (aux_names : list node_aux_names) : Prop :=
    forall nd nd' Hpn ty_env clk_id rst_id clk_type rst_type,
      find_node nd.(n_name) all_lnodes = Some nd ->
      to_node nd Hpn = OK nd' ->
      find_node_env nd.(n_name) envs = Some ty_env ->
      get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
      Env.find clk_id ty_env = Some clk_type ->
      Env.find rst_id ty_env = Some rst_type ->
      exists vars scope nsig,
        NLSyn.find_node nd'.(NLSyn.n_name) P = Some nd'
        /\ call_context P vars scope ty_env clk_type rst_type GL GN
        /\ Forall (NLClo.wc_equation P vars) nd'.(NLSyn.n_eqs)
        /\ find_signature nd'.(NLSyn.n_name) GN = Some nsig
        /\ SECNL.generate_node_sig_scoped_env GN nd' envs aux_names = OK nsig
        /\ signature_scoped nsig.

  (** [transcribed_program_context] reduced to the facts the rest of the
      development already speaks in: four invariants of the NLustre global, and
      per node its naming run, its clocking, and its generated signature.

      [node_scope_fresh_in_env] is the one genuine assumption.  It is assumed
      at this level on the NLustre-to-Stc leg too --
      [generated_callers_scope_fresh] is defined in
      [SecNLusTypingCorrectness.v] and taken as a hypothesis, never proved --
      so this leg is no more assuming than that one. *)

  Lemma transcribed_program_context_intro :
    forall all_lnodes P GL GN envs aux_names,
      Signature_entails GL GN ->
      secglobal_scoped GN ->
      secglobal_good GN ->
      (forall g sg, find_signature g GN = Some sg -> NoDup (signature_scope sg)) ->
      (forall nd nd' Hpn ty_env,
          find_node nd.(n_name) all_lnodes = Some nd ->
          to_node nd Hpn = OK nd' ->
          find_node_env nd.(n_name) envs = Some ty_env ->
          exists rec stx sty nsig,
            NLSyn.find_node nd'.(NLSyn.n_name) P = Some nd'
            /\ generate_local_env_for_node nd' stx = OK ((ty_env, rec), sty)
            /\ NLClo.wc_node P nd'
            /\ SECNLC.node_scope_fresh_in_env nd' ty_env aux_names GN
            /\ find_signature nd'.(NLSyn.n_name) GN = Some nsig
            /\ SECNL.generate_node_sig_scoped_env GN nd' envs aux_names = OK nsig) ->
      transcribed_program_context all_lnodes P GL GN envs aux_names.
  Proof.
    intros all_lnodes P GL GN envs aux_names Hsig HscN HgoodN HndN Hnodes.
    intros nd nd' Hpn ty_env clk_id rst_id clk_type rst_type
           Hfnd Htn Hfenv Haux Hclk Hrst.
    destruct (Hnodes nd nd' Hpn ty_env Hfnd Htn Hfenv)
      as (rec & stx & sty & nsig & HfndP & Hlocal & Hwc & Hfresh & Hfsig & Hgen).
    pose proof (to_node_name _ _ _ Htn) as Hname.
    pose proof (generate_local_env_for_node_injective _ _ _ _ _ Hlocal) as Hinj.
    pose proof Hgen as Hgen'.
    unfold SECNL.generate_node_sig_scoped_env in Hgen'.
    rewrite <- Hname, Hfenv in Hgen'.
    edestruct SECNLC.generate_node_sig_inv as
      (clk_idN & rst_idN & clk_typeN & rst_typeN & inp & out & locals & nconst
       & stN & HauxN & HclkN & HrstN & Hinp & Hout & Hlocals & Hnconst & Hnsigdef);
      [exact Hgen'|].
    pose proof (Hfresh _ _ _ _ _ _ _ HauxN HclkN HrstN Hinp Hout Hlocals)
      as Hscopefresh.
    assert (Hcid : clk_idN = clk_id)
      by (rewrite <- Hname, Haux in HauxN; congruence).
    assert (Hrid : rst_idN = rst_id)
      by (rewrite <- Hname, Haux in HauxN; congruence).
    subst clk_idN rst_idN.
    assert (Hct : clk_typeN = clk_type) by congruence.
    assert (Hrt : rst_typeN = rst_type) by congruence.
    subst clk_typeN rst_typeN.
    pose proof Hwc as Hwc'. destruct Hwc' as (_ & _ & Hwcenv & Hwceqs).
    exists (idck (nd'.(NLSyn.n_in) ++ nd'.(NLSyn.n_vars) ++ nd'.(NLSyn.n_out))),
           (inp ++ out ++ locals ++ clk_type :: rst_type :: nil), nsig.
    split; [exact HfndP|].
    split.
    { unfold call_context.
      split; [exact Hsig|].
      split; [exact Hscopefresh|].
      split; [exact HscN|].
      split; [exact HgoodN|].
      split; [exact HndN|].
      split; [exact Hwcenv|].
      split; [eapply SECNLC.node_vars_env_scoped_from_mappings; eauto|].
      split; [exact Hinj|].
      split; [repeat (apply in_or_app; right); now left
             |repeat (apply in_or_app; right); now right; left]. }
    split; [exact Hwceqs|].
    split; [exact Hfsig|].
    split; [exact Hgen|].
    eapply SECNL.generate_node_sig_scoped; eauto.
  Qed.

  Theorem lnode_security_transcribes :
    forall all_lnodes P Hp GL GN envs aux_names,
      to_global all_lnodes Hp = OK P ->
      Signature_entails GL GN ->
      Signature_domain_incl GN GL ->
      transcribed_program_context all_lnodes P GL GN envs aux_names ->
      forall nd dlt_sig dlt_raw,
        lnode_security all_lnodes GL envs aux_names nd dlt_sig dlt_raw ->
        forall nd' Hpn,
          to_node nd Hpn = OK nd' ->
          node_security P GN envs aux_names nd' dlt_sig dlt_raw.
  Proof.
    intros all_lnodes P Hp GL GN envs aux_names Htg Hsig Hdom Hctxs
           nd0 dlt_sig0 dlt_raw0 Hsec.
    induction Hsec as
      [nd dlt_sig dlt_raw ty_env lsig clk_id rst_id clk_type rst_type
       inp out locals rawL st0 st_n
       Hfnd Hfenv Hfsig Hgen Haux Hclk Hrst Hinp Hout Hlocals Hraw
       Hsigdef Hsatsig Hagree HsatL Hcall IHcall Hrcall IHrcall].
    intros nd' Hpn Htn.
    pose proof (to_node_name _ _ _ Htn) as Hname.
    destruct (Hctxs nd nd' Hpn ty_env clk_id rst_id clk_type rst_type
                Hfnd Htn Hfenv Haux Hclk Hrst)
      as (vars & scope & nsig & HfndP & Hctx & Hwceqs & HfsigN & HgenN & HscN).
    (* the two signatures of this node *)
    destruct (Hsig _ _ Hfsig) as (nsig2 & HfsigN2 & Hnm & Hpres & _).
    rewrite Hname in HfsigN2. rewrite HfsigN in HfsigN2.
    inversion HfsigN2; subst nsig2.
    pose proof (proj1 Hpres) as Hfields.
    (* invert the NLustre node signature *)
    pose proof HgenN as HgenN'.
    unfold SECNL.generate_node_sig_scoped_env in HgenN'.
    rewrite <- Hname, Hfenv in HgenN'.
    edestruct SECNLC.generate_node_sig_inv as
      (clk_idN & rst_idN & clk_typeN & rst_typeN & inpN & outN & localsN & rawN
       & stN & HauxN & HclkN & HrstN & HinpN & HoutN & HlocalsN & HrawN
       & HnsigdefN); [exact HgenN'|].
    rewrite <- Hname, Haux in HauxN. inversion HauxN; subst clk_idN rst_idN.
    rewrite Hclk in HclkN. inversion HclkN; subst clk_typeN.
    rewrite Hrst in HrstN. inversion HrstN; subst rst_typeN.
    rewrite <- (to_node_in _ _ _ Htn), Hinp in HinpN. inversion HinpN; subst inpN.
    rewrite <- (to_node_out _ _ _ Htn), Hout in HoutN. inversion HoutN; subst outN.
    rewrite <- (to_node_vars _ _ _ Htn), Hlocals in HlocalsN.
    inversion HlocalsN; subst localsN.
    (* the raw lists entail, at the same state *)
    pose proof (to_node_eqs _ _ _ Htn) as Hmmap.
    assert (Hndeqs : Forall (fun eq => NoDup (fst eq)) nd.(n_eqs))
      by (apply NoDup_flat_map_each; exact (NoDup_vars_defined_n_eqs nd)).
    destruct (to_equations_entails P vars scope GL GN ty_env clk_type rst_type
                _ _ _ _ _ _ _ Hctx Hndeqs Hmmap Hwceqs Hraw) as (cs & Hcs & Hent).
    destruct (state_pure_generate_eqns_constraints GN ty_env clk_type rst_type
                _ st0 init_state _ _ Hcs) as [Hstn Hpure].
    rewrite HrawN in Hpure. inversion Hpure; subst cs stN.
    (* the security data transports at the same pair of valuations *)
    assert (HnsigC : nsig.(s_constraints) = SymTypes.simplify rawN locals)
      by (rewrite HnsigdefN; reflexivity).
    destruct (security_data_transports lsig nsig rawL rawN locals dlt_sig dlt_raw
                Hfields HnsigC Hent HscN Hagree HsatL)
      as (HsatSigN & HagreeN & HsatRawN).
    eapply SecureNode with
      (ty_env := ty_env) (sig := nsig)
      (clk_id := clk_id) (rst_id := rst_id)
      (clk_type := clk_type) (rst_type := rst_type)
      (inp := inp) (out := out) (locals := locals)
      (raw := rawN) (st_n := init_state);
      try eassumption.
    - rewrite <- Hname. exact Hfenv.
    - rewrite <- Hname. exact Haux.
    - rewrite <- (to_node_in _ _ _ Htn). exact Hinp.
    - rewrite <- (to_node_out _ _ _ Htn). exact Hout.
    - rewrite <- (to_node_vars _ _ _ Htn). exact Hlocals.
    - (* the simple call sites *)
      intros xs ck f exps callee callee_sig ckty inptyp outtyp st_clk st_inp
             HinEq HfindCallee HfindCalleeSig Hckty Hinptyp Houttyp.
      destruct (to_equations_In_inv _ _ _ _ _ Hmmap HinEq)
        as (eq & Hineq & Hte).
      destruct (to_equation_EqApp_inv _ _ _ _ _ _ _ Hte)
        as (args & a & Heq & Hles & Hck). subst eq ck.
      destruct (find_node_global' all_lnodes Hp P f callee Htg HfindCallee)
        as (lcallee & Hpc & HfindL & Htc).
      destruct (Hdom _ _ HfindCalleeSig) as (lcallee_sig & HfindLsig).
      destruct (Hsig _ _ HfindLsig) as (csig2 & HfindN2 & _ & Hpresc & _).
      rewrite HfindCalleeSig in HfindN2. inversion HfindN2; subst csig2.
      pose proof (proj1 Hpresc) as Hfieldsc.
      apply option_to_sec_inv in Hckty as [Hckty ?]; subst st_clk.
      eapply sec_mmap_assign_exp_Forall2 in Hinptyp as [Hst Hall]; subst st_inp.
      assert (Hlex : assign_lexps GL ty_env nsig.(s_clk) nsig.(s_reset) args
                       init_state
                     = OK (map (fun t => (t, [])) inptyp, init_state))
        by (eapply to_lexps_assign_eq; eassumption).
      destruct Hfields as (Hfin & Hfout & Hfrst & Hfclk).
      specialize (Hcall xs f args a lcallee lcallee_sig ckty
                    (map (fun t => (t, [])) inptyp) outtyp init_state init_state
                    Hineq HfindL HfindLsig
                    ltac:(rewrite Hfclk; exact Hckty)
                    ltac:(rewrite Hfclk, Hfrst; exact Hlex)
                    Houttyp).
      specialize (IHcall xs f args a lcallee lcallee_sig ckty
                    (map (fun t => (t, [])) inptyp) outtyp init_state init_state
                    Hineq HfindL HfindLsig
                    ltac:(rewrite Hfclk; exact Hckty)
                    ltac:(rewrite Hfclk, Hfrst; exact Hlex)
                    Houttyp callee Hpc Htc).
      rewrite map_map in IHcall. simpl in IHcall. rewrite map_id in IHcall.
      rewrite Hfrst in IHcall.
      erewrite (lat_valuation_fields_agree dlt_sig) in IHcall by exact Hfieldsc.
      erewrite (lat_valuation_fields_agree dlt_raw) in IHcall by exact Hfieldsc.
      exact IHcall.
    - (* the reset call sites *)
      intros xs ck f exps r ckr callee callee_sig ckty rty rstty inptyp outtyp
             st_clk st_rst st_inp HinEq HfindCallee HfindCalleeSig Hckty Hrty
             Hrstty Hinptyp Houttyp.
      destruct (to_equations_In_inv _ _ _ _ _ Hmmap HinEq)
        as (eq & Hineq & Hte).
      destruct (to_equation_EqApp_reset_inv _ _ _ _ _ _ _ _ _ Hte)
        as (args & ty0 & nm & a & Heq & Hles & Hck). subst eq ck.
      destruct (find_node_global' all_lnodes Hp P f callee Htg HfindCallee)
        as (lcallee & Hpc & HfindL & Htc).
      destruct (Hdom _ _ HfindCalleeSig) as (lcallee_sig & HfindLsig).
      destruct (Hsig _ _ HfindLsig) as (csig2 & HfindN2 & _ & Hpresc & _).
      rewrite HfindCalleeSig in HfindN2. inversion HfindN2; subst csig2.
      pose proof (proj1 Hpresc) as Hfieldsc.
      apply option_to_sec_inv in Hckty as [Hckty ?]; subst st_clk.
      apply option_to_sec_inv in Hrstty as [Hrstty ?]; subst st_rst.
      eapply sec_mmap_assign_exp_Forall2 in Hinptyp as [Hst Hall]; subst st_inp.
      assert (Hlex : assign_lexps GL ty_env nsig.(s_clk) nsig.(s_reset) args
                       init_state
                     = OK (map (fun t => (t, [])) inptyp, init_state))
        by (eapply to_lexps_assign_eq; eassumption).
      destruct Hfields as (Hfin & Hfout & Hfrst & Hfclk).
      specialize (Hrcall xs f args r ty0 ckr nm a lcallee lcallee_sig ckty
                    rty rstty (map (fun t => (t, [])) inptyp) outtyp
                    init_state init_state
                    Hineq HfindL HfindLsig
                    ltac:(rewrite Hfclk; exact Hckty)
                    Hrty
                    ltac:(rewrite Hfclk; exact Hrstty)
                    ltac:(rewrite Hfclk, Hfrst; exact Hlex)
                    Houttyp).
      specialize (IHrcall xs f args r ty0 ckr nm a lcallee lcallee_sig ckty
                    rty rstty (map (fun t => (t, [])) inptyp) outtyp
                    init_state init_state
                    Hineq HfindL HfindLsig
                    ltac:(rewrite Hfclk; exact Hckty)
                    Hrty
                    ltac:(rewrite Hfclk; exact Hrstty)
                    ltac:(rewrite Hfclk, Hfrst; exact Hlex)
                    Houttyp callee Hpc Htc).
      rewrite map_map in IHrcall. simpl in IHrcall. rewrite map_id in IHrcall.
      rewrite Hfrst in IHrcall.
      erewrite (lat_valuation_fields_agree dlt_sig) in IHrcall by exact Hfieldsc.
      erewrite (lat_valuation_fields_agree dlt_raw) in IHrcall by exact Hfieldsc.
      exact IHrcall.
  Qed.

  (** * Noninterference for a Lustre node

      The leg, end to end: a secure Lustre node transcribes to an NLustre node
      the NLustre theorem applies to, so two runs of the transcribed node that
      agree on its low inputs agree on its low outputs -- and because
      transcription keeps a node's interface, the input and output lists can be
      named on the Lustre node.

      The semantic hypotheses stay NLustre-side on purpose: they are about the
      transcribed node's runs, which is what [Transcription.Correctness]
      relates to the source node's.  Composing with that is the next leg, not
      this one. *)

  Corollary lnode_noninterference_outputs :
    forall all_lnodes P Hp GL GN envs aux_names
           nd nd' Hpn ty_env nsig dlt_sig dlt_raw t bk H H',
      to_global all_lnodes Hp = OK P ->
      Signature_entails GL GN ->
      Signature_domain_incl GN GL ->
      transcribed_program_context all_lnodes P GL GN envs aux_names ->
      to_node nd Hpn = OK nd' ->
      lnode_security all_lnodes GL envs aux_names nd dlt_sig dlt_raw ->
      generate_node_scoped_env P = OK (envs, aux_names) ->
      NLOrd.Ordered_nodes P ->
      NLClo.wc_global P ->
      SECNL.generate_all_signatures_scoped_env P envs aux_names = OK GN ->
      NLCaus.nl_global_causal P ->
      NLSyn.find_node nd'.(NLSyn.n_name) P = Some nd' ->
      find_node_env nd'.(NLSyn.n_name) envs = Some ty_env ->
      find_signature nd'.(NLSyn.n_name) GN = Some nsig ->
      Forall (Indexed.sem_equation P bk H) nd'.(NLSyn.n_eqs) ->
      Forall (Indexed.sem_equation P bk H') nd'.(NLSyn.n_eqs) ->
      history_low_eq ty_env dlt_sig t (map fst nd.(n_in)) H H' ->
      history_low_eq ty_env dlt_sig t (map fst nd.(n_out)) H H'.
  Proof.
    intros all_lnodes P Hp GL GN envs aux_names nd nd' Hpn ty_env nsig
           dlt_sig dlt_raw t bk H H'
           Htg Hsig Hdom Hctxs Htn Hsec Henvsgen Hord Hwc Hallsig Hcaus
           HfndP Hfenv Hfsig Hsem Hsem' Hlowin.
    rewrite (to_node_out _ _ _ Htn).
    rewrite (to_node_in _ _ _ Htn) in Hlowin.
    eapply node_noninterference_outputs; eauto.
    eapply lnode_security_transcribes; eauto.
  Qed.

  (** The two facts about the globals are not assumptions a caller has to
      invent.  Both are program-level theorems of [SecLusNLusTranslation.v],
      and both follow from the two drivers having been run -- which is the
      hypothesis [node_security] already carries on the NLustre side.  One
      naming pass serves both, by [to_global_lscoped_env]. *)

  Corollary lnode_noninterference_outputs_generated :
    forall all_lnodes P Hp envs aux_names GL GN st
           nd nd' Hpn ty_env nsig dlt_sig dlt_raw t bk H H',
      to_global all_lnodes Hp = OK P ->
      LClo.wc_global all_lnodes ->
      SECLNG.generate_lnode_scoped_env all_lnodes = OK (envs, aux_names) ->
      generate_all_lsignatures_scoped_env all_lnodes envs aux_names st = OK GL ->
      SECNL.generate_all_signatures_scoped_env P envs aux_names = OK GN ->
      transcribed_program_context all_lnodes P GL GN envs aux_names ->
      to_node nd Hpn = OK nd' ->
      lnode_security all_lnodes GL envs aux_names nd dlt_sig dlt_raw ->
      NLOrd.Ordered_nodes P ->
      NLClo.wc_global P ->
      NLCaus.nl_global_causal P ->
      NLSyn.find_node nd'.(NLSyn.n_name) P = Some nd' ->
      find_node_env nd'.(NLSyn.n_name) envs = Some ty_env ->
      find_signature nd'.(NLSyn.n_name) GN = Some nsig ->
      Forall (Indexed.sem_equation P bk H) nd'.(NLSyn.n_eqs) ->
      Forall (Indexed.sem_equation P bk H') nd'.(NLSyn.n_eqs) ->
      history_low_eq ty_env dlt_sig t (map fst nd.(n_in)) H H' ->
      history_low_eq ty_env dlt_sig t (map fst nd.(n_out)) H H'.
  Proof.
    intros all_lnodes P Hp envs aux_names GL GN st
           nd nd' Hpn ty_env nsig dlt_sig dlt_raw t bk H H'
           Htg Hwcl Hnames Hlsigs Hnsigs Hctxs Htn Hsec
           Hord Hwc Hcaus HfndP Hfenv Hfsig Hsem Hsem' Hlowin.
    assert (Hnames' : generate_node_scoped_env P = OK (envs, aux_names))
      by (rewrite <- (SECLNG.to_global_lscoped_env _ _ _ Htg); exact Hnames).
    eapply lnode_noninterference_outputs; eauto.
    - eapply to_global_signatures_entail; eauto.
    - eapply generate_all_signatures_domain; eauto.
  Qed.

End SECLUSNONINTERFERENCE.
