(** Every signature-satisfying valuation of a generated node is the signature-level
    valuation of a [node_security] witness.

    [node_security] is the invariant the noninterference proof consumes.  Here it is
    constructed rather than assumed: from a valuation satisfying a node's stored
    signature, [signature_satisfied_replays_raw] gives a raw valuation agreeing on the
    scope, the callee clauses are read off the instantiated constraints (a satisfied
    call block gives a satisfied callee signature, by completeness of the substitution),
    and the callee is taken at its own witness by induction on the call structure. *)

From Coq Require Import List Sorting.Permutation Lia Wf_nat PArith.BinPos Arith.PeanoNat.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterferenceClockedStep.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module SecNLusNodeSecurity
  (Import Ids    : IDS)
  (Import Lat    : Lattice)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import SecT   : SECTYPES Lat)
  (Import CESyn  : CESYNTAX Op)
  (Import SynNL  : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import Ord    : NLORDERED Ids Op CESyn SynNL)
  (Import Mem    : MEMORIES Ids Op CESyn SynNL)
  (Import IsD    : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF    : ISFREE Ids Op CESyn SynNL CEIsF)
  (NLCaus        : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF)
  (Import Clo    : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Import Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn SynNL Str Ord CESem)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN CEIsF CEClo SECCETYPING
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING Ord Mem IsD IsF Clo SECNLUSTYPING)
  (** The noninterference module is a parameter, so that [node_security] here is
      the one the later phases consume. *)
  (Import NI :
     SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN
       CETyp CEIsF CEClo SECCETYPING Str Ord Mem IsD IsF NLCaus Clo CESem
       CEProps Indexed SIGPROOFS SECNLUSTYPING SECNLUSTYPINGCORRECTNESS)
.



  (** * Regenerating a node against a larger global

      The generator reads the global only to look up the signatures of the nodes
      an equation calls.  Two globals that return the same signatures for those
      names make it produce the same constraints. *)

  Lemma generate_eqn_constraint_congr :
    forall G1 G2 env base_ty rst_ty eq st,
      (forall f, Is_node_in_eq f eq ->
                 SIG.find_signature f G1 = SIG.find_signature f G2) ->
      SECNLUSTYPING.generate_eqn_constraint G1 env base_ty rst_ty eq st
      = SECNLUSTYPING.generate_eqn_constraint G2 env base_ty rst_ty eq st.
  Proof.
    intros G1 G2 env base_ty rst_ty eq st Hlook.
    destruct eq as [x ck ce|xs ck f les r|x ck v e]; try reflexivity.
    assert (Hf : SIG.find_signature f G1 = SIG.find_signature f G2)
      by (apply Hlook; constructor).
    destruct xs as [|x0 xs0]; [reflexivity|].
    destruct r as [[rx rck]|]; cbn [SECNLUSTYPING.generate_eqn_constraint];
      rewrite Hf; reflexivity.
  Qed.

  Lemma generate_eqns_constraints_congr :
    forall G1 G2 env base_ty rst_ty eqs st,
      (forall f, Is_node_in f eqs ->
                 SIG.find_signature f G1 = SIG.find_signature f G2) ->
      SECNLUSTYPING.generate_eqns_constraints G1 env base_ty rst_ty eqs st
      = SECNLUSTYPING.generate_eqns_constraints G2 env base_ty rst_ty eqs st.
  Proof.
    intros G1 G2 env base_ty rst_ty eqs. induction eqs as [|eq eqs IH];
      intros st Hlook; [reflexivity|].
    assert (Hc : SECNLUSTYPING.generate_eqn_constraint G1 env base_ty rst_ty eq st
                 = SECNLUSTYPING.generate_eqn_constraint G2 env base_ty rst_ty eq st).
    { apply generate_eqn_constraint_congr. intros f Hf. apply Hlook. left. exact Hf. }
    cbn [SECNLUSTYPING.generate_eqns_constraints]. unfold SC.bind.
    rewrite Hc.
    destruct (SECNLUSTYPING.generate_eqn_constraint G2 env base_ty rst_ty eq st)
      as [[c st1]|e]; [|reflexivity].
    rewrite (IH st1).
    - reflexivity.
    - intros f Hf. apply Hlook. right. exact Hf.
  Qed.

  Lemma generate_node_sig_intro :
    forall G n env aux clk_id rst_id clk_type rst_type inp out locals nconst st_n,
      get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
      Env.find clk_id env = Some clk_type ->
      Env.find rst_id env = Some rst_type ->
      get_mappings_from_node n.(n_in) env = Some inp ->
      get_mappings_from_node n.(n_out) env = Some out ->
      get_mappings_from_node n.(n_vars) env = Some locals ->
      SECNLUSTYPING.generate_eqns_constraints G env clk_type rst_type n.(n_eqs)
        init_state = OK (nconst, st_n) ->
      SECNLUSTYPING.generate_node_sig G n env aux
      = OK {| s_name := n.(n_name); s_in := inp; s_out := out;
              s_reset := rst_type; s_clk := clk_type;
              s_constraints := SymTypes.simplify nconst locals |}.
  Proof.
    intros G n env aux clk_id rst_id clk_type rst_type inp out locals nconst st_n
           Haux Hclk Hrst Hinp Hout Hlocals Hcns.
    unfold SECNLUSTYPING.generate_node_sig.
    cbn [bind bind2 option_to_sec ret].
    rewrite Haux. cbn [bind bind2 option_to_sec ret].
    rewrite Hclk. cbn [bind bind2 option_to_sec ret].
    rewrite Hrst. cbn [bind bind2 option_to_sec ret].
    rewrite Hinp. cbn [bind bind2 option_to_sec ret].
    rewrite Hout. cbn [bind bind2 option_to_sec ret].
    rewrite Hlocals. cbn [bind bind2 option_to_sec ret].
    unfold bind, ret. rewrite Hcns. simpl. reflexivity.
  Qed.

  Lemma generate_node_sig_congr :
    forall G1 G2 n env aux sig,
      (forall f, Is_node_in f n.(n_eqs) ->
                 SIG.find_signature f G1 = SIG.find_signature f G2) ->
      SECNLUSTYPING.generate_node_sig G1 n env aux = OK sig ->
      SECNLUSTYPING.generate_node_sig G2 n env aux = OK sig.
  Proof.
    intros G1 G2 n env aux sig Hlook Hsig.
    destruct (SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv G1 n env aux sig Hsig)
      as (ci & ri & ct & rt & inp & out & locals & nconst & stn & Haux & Hclk
          & Hrst & Hinp & Hout & Hlocals & Hcns & Hdef).
    rewrite (generate_eqns_constraints_congr G1 G2 env ct rt n.(n_eqs)
               init_state Hlook) in Hcns.
    rewrite Hdef.
    exact (generate_node_sig_intro G2 n env aux ci ri ct rt inp out locals
             nconst stn Haux Hclk Hrst Hinp Hout Hlocals Hcns).
  Qed.

  (** * Regenerating a node against the final global *)

  Lemma find_signature_skip :
    forall L f l,
      (forall s, In s L -> s.(s_name) <> f) ->
      SIG.find_signature f (L ++ l) = SIG.find_signature f l.
  Proof.
    induction L as [|s L IH]; intros f l H; [reflexivity|].
    unfold SIG.find_signature in *. simpl.
    destruct (ident_eqb s.(s_name) f) eqn:E.
    - apply ident_eqb_eq in E. exfalso. exact (H s (or_introl Logic.eq_refl) E).
    - apply IH. intros s' Hs'. apply H. right. exact Hs'.
  Qed.

  Lemma gen_fold_app :
    forall l1 l2 acc envs aux G,
      SECNLUSTYPING.generate_all_signatures_scoped_env' acc (l1 ++ l2) envs aux
        = OK G ->
      exists acc',
        SECNLUSTYPING.generate_all_signatures_scoped_env' acc l1 envs aux = OK acc'
        /\ SECNLUSTYPING.generate_all_signatures_scoped_env' acc' l2 envs aux
           = OK G.
  Proof.
    induction l1 as [|n l1 IH]; intros l2 acc envs aux G H.
    - exists acc. split; [reflexivity|exact H].
    - simpl in H.
      destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc n envs aux)
        as [sig|] eqn:Hs; simpl in H; [|discriminate].
      destruct (IH l2 (sig :: acc) envs aux G H) as (acc' & H1 & H2).
      exists acc'. split; [simpl; rewrite Hs; simpl; exact H1|exact H2].
  Qed.

  Lemma generated_sig_name :
    forall acc n envs aux sig,
      SECNLUSTYPING.generate_node_sig_scoped_env acc n envs aux = OK sig ->
      sig.(s_name) = n.(n_name).
  Proof.
    intros acc n envs aux sig H.
    unfold SECNLUSTYPING.generate_node_sig_scoped_env in H.
    destruct (find_node_env n.(n_name) envs) as [env|]; [|discriminate].
    destruct (SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv acc n env aux sig H)
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & _ & _ & _ & _ & Hdef).
    rewrite Hdef. reflexivity.
  Qed.

  Lemma gen_fold_suffix :
    forall ns acc envs aux G,
      SECNLUSTYPING.generate_all_signatures_scoped_env' acc ns envs aux = OK G ->
      exists L,
        G = L ++ acc
        /\ forall s, In s L -> exists m, In m ns /\ s.(s_name) = m.(n_name).
  Proof.
    induction ns as [|n ns IH]; intros acc envs aux G H.
    - simpl in H. inversion H; subst. exists []. split; [reflexivity|intros s []].
    - simpl in H.
      destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc n envs aux)
        as [sig|] eqn:Hs; simpl in H; [|discriminate].
      destruct (IH (sig :: acc) envs aux G H) as (L & HG & Hn).
      exists (L ++ [sig]). split.
      + rewrite HG, <- app_assoc. reflexivity.
      + intros s Hin. apply in_app_or in Hin as [Hin|[Hin|[]]].
        * destruct (Hn s Hin) as (m & Hm & E). exists m. split; [right; exact Hm|exact E].
        * subst s. exists n. split; [left; reflexivity|].
          exact (generated_sig_name _ _ _ _ _ Hs).
  Qed.

  Lemma calls_precede_rev :
    forall all_nodes pre n post f,
      Ordered_nodes all_nodes ->
      rev all_nodes = pre ++ n :: post ->
      Is_node_in f n.(n_eqs) ->
      exists n', In n' pre /\ n'.(n_name) = f.
  Proof.
    intros all_nodes pre n post f Hord Hsplit Hin.
    assert (Hall : all_nodes = rev post ++ n :: rev pre).
    { rewrite <- (rev_involutive all_nodes), Hsplit.
      rewrite rev_app_distr. simpl. rewrite <- app_assoc. reflexivity. }
    rewrite Hall in Hord.
    apply Ordered_nodes_append in Hord.
    inversion Hord as [|nd nds Hord' Hcalls Hdist]; subst.
    destruct (Hcalls f Hin) as [_ Hex].
    apply Exists_exists in Hex as (n' & Hn' & Heq).
    exists n'. split; [apply (proj2 (in_rev _ _)) in Hn'; exact Hn'|symmetry; exact Heq].
  Qed.

  Lemma regen_full2 :
    forall all_nodes envs aux G,
      Ordered_nodes all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux
        = OK G ->
      forall n sig,
        In n all_nodes ->
        SIG.find_signature n.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux = OK sig.
  Proof.
    intros all_nodes envs aux G Hord Hgen n sig Hin Hfind.
    pose proof (Ordered_nodes_nodup_names all_nodes Hord) as Hnd.
    assert (Hinr : In n (rev all_nodes)) by (apply (proj1 (in_rev _ _)); exact Hin).
    apply in_split in Hinr as (pre & post & Hsplit).
    unfold SECNLUSTYPING.generate_all_signatures_scoped_env in Hgen.
    rewrite Hsplit in Hgen.
    destruct (gen_fold_app pre (n :: post) [] envs aux G Hgen)
      as (accn & Hpre & Hrest).
    simpl in Hrest.
    destruct (SECNLUSTYPING.generate_node_sig_scoped_env accn n envs aux)
      as [sg|] eqn:Hs; simpl in Hrest; [|discriminate].
    destruct (gen_fold_suffix post (sg :: accn) envs aux G Hrest)
      as (L & HG & Hnames).
    assert (Hndr : NoDup (map n_name (pre ++ n :: post))).
    { rewrite <- Hsplit. rewrite map_rev.
      eapply Permutation_NoDup; [apply Permutation_rev|exact Hnd]. }
    rewrite map_app in Hndr. simpl in Hndr.
    assert (Hnotpost : forall m, In m post -> m.(n_name) <> n.(n_name)).
    { intros m Hm Heq.
      apply NoDup_app_r in Hndr. inversion Hndr as [|x xs Hn _]; subst.
      apply Hn. rewrite <- Heq. apply in_map. exact Hm. }
    assert (Hskipn : forall s, In s L -> s.(s_name) <> n.(n_name)).
    { intros s Hs' Heq. destruct (Hnames s Hs') as (m & Hm & E).
      exact (Hnotpost m Hm (Logic.eq_trans (Logic.eq_sym E) Heq)). }
    pose proof (generated_sig_name _ _ _ _ _ Hs) as Hsgname.
    rewrite HG in Hfind.
    rewrite (find_signature_skip L _ _ Hskipn) in Hfind.
    unfold SIG.find_signature in Hfind. simpl in Hfind.
    rewrite Hsgname, ident_eqb_refl in Hfind.
    inversion Hfind; subst sig. clear Hfind.
    unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hs |- *.
    destruct (find_node_env n.(n_name) envs) as [env|]; [|discriminate].
    eapply generate_node_sig_congr; [|exact Hs].
    intros f Hf.
    destruct (calls_precede_rev all_nodes pre n post f Hord Hsplit Hf)
      as (n' & Hn'pre & Hn'name).
    assert (Hfws : ~ In f (n.(n_name) :: map n_name post)).
    { apply NoDup_app_In with (x := f) in Hndr; [exact Hndr|].
      rewrite <- Hn'name. apply in_map. exact Hn'pre. }
    assert (Hfn : n.(n_name) <> f)
      by (intro E; apply Hfws; left; exact E).
    assert (Hfpost : forall m, In m post -> m.(n_name) <> f).
    { intros m Hm E. apply Hfws. right. rewrite <- E. apply in_map. exact Hm. }
    rewrite HG. symmetry.
    rewrite (find_signature_skip L f (sg :: accn)).
    - unfold SIG.find_signature. simpl.
      rewrite Hsgname.
      destruct (ident_eqb n.(n_name) f) eqn:E.
      + apply ident_eqb_eq in E. contradiction.
      + reflexivity.
    - intros s Hs'. destruct (Hnames s Hs') as (m & Hm & Em).
      rewrite Em. exact (Hfpost m Hm).
  Qed.

  (** A satisfied call block makes the callee's stored signature hold at the
      valuation the call induces. *)
  Lemma sig_sat_of_call :
    forall sg inptyp ckty rstty outtyp cns st st' w,
      signature_good sg ->
      SIG.call_subst_fresh sg inptyp ckty rstty outtyp ->
      generate_constraints sg inptyp ckty rstty outtyp st = OK (cns, st') ->
      listSatisfiable w cns ->
      signature_satisfied
        (SIGPROOFS.lat_valuation w sg inptyp ckty rstty outtyp) sg.
  Proof.
    intros sg inptyp ckty rstty outtyp cns st st' w Hgood Hfresh Hgen Hsat.
    destruct (generate_constraints_lengths sg inptyp ckty rstty outtyp cns st st'
                Hgen) as [Hlin Hlout].
    assert (Hinf : Forall2 (fun x ty => ~ In x ty) sg.(s_in) inptyp)
      by (exact (call_subst_fresh_inputs_notin_pairs sg inptyp ckty rstty outtyp Hfresh Hlin)).
    destruct Hfresh as [_ [Hckf [Hrstf _]]].
    assert (Hck : ~ In sg.(s_clk) ckty).
    { intro Hin. unfold type_fresh in Hckf. rewrite Forall_forall in Hckf.
      apply (Hckf _ Hin). unfold signature_scope. apply in_or_app. right.
      apply in_or_app. right. left. reflexivity. }
    assert (Hrst : ~ In sg.(s_reset) rstty).
    { intro Hin. unfold type_fresh in Hrstf. rewrite Forall_forall in Hrstf.
      apply (Hrstf _ Hin). unfold signature_scope. apply in_or_app. right.
      apply in_or_app. right. right. left. reflexivity. }
    exact (SIGPROOFS.generate_constraints_complete_good sg inptyp ckty rstty
             outtyp cns st st' Hgood Hgen w Hsat Hinf Hck Hrst).
  Qed.

  Lemma call_fresh_of_eq :
    forall P n ty_env inp out locals clk_type rst_type
           xs ck f exps r callee_sig inptyp ckty rstty outtyp st st' st'',
      get_mappings_from_node n.(n_in) ty_env = Some inp ->
      get_mappings_from_node n.(n_out) ty_env = Some out ->
      get_mappings_from_node n.(n_vars) ty_env = Some locals ->
      Clo.wc_node P n ->
      In (EqApp xs ck f exps r) n.(n_eqs) ->
      SIG.scope_fresh (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
        callee_sig ->
      SC.mmap (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
        exps st = OK (inptyp, st') ->
      SC.option_to_sec (SECCETYPING.assign_clk_type ty_env clk_type ck) st''
        = OK (ckty, st'') ->
      SecT.st_scoped (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) rstty ->
      get_mappings xs ty_env = Some outtyp ->
      SIG.call_subst_fresh callee_sig inptyp ckty rstty outtyp.
  Proof.
    intros P n ty_env inp out locals clk_type rst_type xs ck f exps r callee_sig
           inptyp ckty rstty outtyp st st' st'' Hinp Hout Hlocals Hwcn Heqin
           Hfresh Hmm Hck Hrstsc Hmap.
    set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
    destruct Hwcn as [_ [_ [Hwcenv Hwc_eqs]]].
    assert (Hwcapp : Clo.wc_equation P
                       (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                       (EqApp xs ck f exps r)).
    { rewrite Forall_forall in Hwc_eqs. exact (Hwc_eqs _ Heqin). }
    inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                          Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
    assert (Hvars_scoped :
              SECNLUSTYPING.vars_env_scoped ty_env
                (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) caller_scope)
      by (eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
          eauto).
    assert (Hinp_scope : Forall (SecT.st_scoped caller_scope) inptyp).
    { eapply SECNLUSTYPING.mmap_assign_exp_type_scoped
        with (scope := caller_scope) (es := exps) (st := st) (st' := st');
        [|exact Hmm].
      eapply SECNLUSTYPING.wc_call_args_scoped
        with (vars := idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
             (scope := caller_scope) (sub := sub) (ck := ck) (ins := n0.(n_in));
        eauto. }
    assert (Hfree_clock_scope :
              forall z, Is_free_in_clock z ck ->
                exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
    { intros z Hz.
      destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
      { eapply SECNLUSTYPING.wc_call_clock_free_in_vars; eauto. }
      exists ty0; split; [exact Hfindz|exact Hinscope]. }
    assert (Hassign_ck : SECCETYPING.assign_clk_type ty_env clk_type ck
                         = Some ckty).
    { unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env clk_type ck) as [ckty'|]
        eqn:Hassign; simpl in Hck; try discriminate.
      inversion Hck; now subst ckty'. }
    assert (Hck_scope : SecT.st_scoped caller_scope ckty).
    { eapply (SECCETYPING.assign_clk_type_scoped ty_env clk_type caller_scope ck ckty).
      - simpl. repeat (apply in_or_app; right). simpl. now left.
      - exact Hfree_clock_scope.
      - exact Hassign_ck. }
    assert (Hout_scope : Forall (fun ty => In ty caller_scope) outtyp).
    { rewrite Forall_forall. intros ty Hty.
      pose proof (eqapp_outtyp_in_out_or_locals n ty_env out locals xs ck f exps
                    r outtyp ty Heqin Hmap Hout Hlocals Hty) as Hio.
      replace caller_scope with (inp ++ ((out ++ locals) ++ [clk_type; rst_type])).
      - apply in_or_app. right. eapply In_app_weaken_right. exact Hio.
      - unfold caller_scope. repeat rewrite <- app_assoc. reflexivity. }
    eapply SIG.call_subst_fresh_from_scope_fresh; eauto.
  Qed.

  Lemma reset_rst_scoped :
    forall P n ty_env inp out locals clk_type rst_type
           xs ck f exps r ckr rty rstck st,
      get_mappings_from_node n.(n_in) ty_env = Some inp ->
      get_mappings_from_node n.(n_out) ty_env = Some out ->
      get_mappings_from_node n.(n_vars) ty_env = Some locals ->
      Clo.wc_node P n ->
      In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
      Env.find r ty_env = Some rty ->
      SC.option_to_sec (SECCETYPING.assign_clk_type ty_env clk_type ckr) st
        = OK (rstck, st) ->
      SecT.st_scoped (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
        ([rst_type] ⊔ ([rty] ⊔ rstck)).
  Proof.
    intros P n ty_env inp out locals clk_type rst_type xs ck f exps r ckr rty
           rstck st Hinp Hout Hlocals Hwcn Heqin Hr Hrck.
    set (caller_scope := inp ++ out ++ locals ++ clk_type :: rst_type :: nil).
    destruct Hwcn as [_ [_ [Hwcenv Hwc_eqs]]].
    assert (Hwcapp : Clo.wc_equation P
                       (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                       (EqApp xs ck f exps (Some (r, ckr)))).
    { rewrite Forall_forall in Hwc_eqs. exact (Hwc_eqs _ Heqin). }
    inversion Hwcapp as [|xs0 ck0 f0 exps0 r0 n0 sub
                          Hfindwc Hwcins Hwcouts Hwcrst|]; subst.
    assert (Hvars_scoped :
              SECNLUSTYPING.vars_env_scoped ty_env
                (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) caller_scope)
      by (eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings;
          eauto).
    assert (Hinr : In (r, ckr) (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
    { eapply wc_reset_in_call_vars; eauto. }
    assert (Hr_scope : SecT.st_scoped caller_scope [rty]).
    { apply SecT.st_scoped_singleton.
      destruct (Hvars_scoped r) as (ty0 & Hfindr & Hinscope).
      - eapply In_InMembers. exact Hinr.
      - rewrite Hr in Hfindr. inversion Hfindr; subst ty0. exact Hinscope. }
    assert (Hfree_rclock_scope :
              forall z, Is_free_in_clock z ckr ->
                exists ty0, Env.find z ty_env = Some ty0 /\ In ty0 caller_scope).
    { intros z Hz.
      assert (Hwr : wc_clock (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ckr)
        by (eapply wc_env_var; eauto).
      destruct (Hvars_scoped z) as (ty0 & Hfindz & Hinscope).
      - eapply SECCETYPING.wc_clock_free_in_vars; eauto.
      - exists ty0; split; [exact Hfindz|exact Hinscope]. }
    assert (Hassign_rst : SECCETYPING.assign_clk_type ty_env clk_type ckr
                          = Some rstck).
    { unfold SC.option_to_sec in Hrck.
      destruct (SECCETYPING.assign_clk_type ty_env clk_type ckr) as [rstty'|]
        eqn:Hassign; simpl in Hrck; try discriminate.
      inversion Hrck; now subst rstty'. }
    assert (Hrst_scope : SecT.st_scoped caller_scope rstck).
    { eapply (SECCETYPING.assign_clk_type_scoped ty_env clk_type caller_scope
                ckr rstck).
      - simpl. repeat (apply in_or_app; right). simpl. now left.
      - exact Hfree_rclock_scope.
      - exact Hassign_rst. }
    eapply SecT.st_scoped_merge.
    - apply SecT.st_scoped_singleton. simpl. repeat (apply in_or_app; right).
      simpl. now right; left.
    - eapply SecT.st_scoped_merge; eauto.
  Qed.

  Lemma find_node_of_In' :
    forall (Q : global) n,
      NoDup (map n_name Q) -> In n Q -> find_node n.(n_name) Q = Some n.
  Proof.
    induction Q as [|nd Q IH]; intros n Hnd Hin; [inversion Hin|].
    simpl in Hnd. inversion Hnd as [|x xs Hnotin Hnd']; subst x xs.
    destruct Hin as [Heq|Hin].
    - subst nd. simpl. rewrite ident_eqb_refl. reflexivity.
    - simpl. destruct (ident_eqb nd.(n_name) n.(n_name)) eqn:Hname.
      + exfalso. apply ident_eqb_eq in Hname.
        apply Hnotin. rewrite Hname. now apply in_map.
      + apply IH; assumption.
  Qed.

  Lemma callee_in_pre :
    forall all_nodes pre n post f callee,
      Ordered_nodes all_nodes ->
      rev all_nodes = pre ++ n :: post ->
      Is_node_in f n.(n_eqs) ->
      find_node f all_nodes = Some callee ->
      In callee pre.
  Proof.
    intros all_nodes pre n post f callee Hord Hsplit Hin Hfind.
    destruct (calls_precede_rev all_nodes pre n post f Hord Hsplit Hin)
      as (n' & Hn'pre & Hn'name).
    pose proof (Ordered_nodes_nodup_names all_nodes Hord) as Hnd.
    assert (Hn'all : In n' all_nodes).
    { apply (proj2 (in_rev _ _)). rewrite Hsplit. apply in_or_app. left. exact Hn'pre. }
    pose proof (find_node_of_In' all_nodes n' Hnd Hn'all) as Hf'.
    rewrite Hn'name in Hf'. rewrite Hfind in Hf'. inversion Hf'; subst. exact Hn'pre.
  Qed.

  Definition exists_hyp (all_nodes : global) (G : secglobal)
    (envs : node_scoped_env) (aux : list node_aux_names) (pre : list node) : Prop :=
    forall callee callee_sig,
      In callee pre ->
      SIG.find_signature callee.(n_name) G = Some callee_sig ->
      forall d1c, signature_satisfied d1c callee_sig ->
        exists wc, SecT.agree_on (signature_scope callee_sig) d1c wc
                   /\ node_security all_nodes G envs aux callee wc wc.

  Lemma simple_call_clause :
    forall all_nodes envs aux G pre n post
           ty_env clk_id rst_id clk_type rst_type inp out locals raw st_n w,
      NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux) ->
      Ordered_nodes all_nodes -> Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux
        = OK G ->
      rev all_nodes = pre ++ n :: post ->
      find_node_env n.(n_name) envs = Some ty_env ->
      get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
      Env.find clk_id ty_env = Some clk_type ->
      Env.find rst_id ty_env = Some rst_type ->
      get_mappings_from_node n.(n_in) ty_env = Some inp ->
      get_mappings_from_node n.(n_out) ty_env = Some out ->
      get_mappings_from_node n.(n_vars) ty_env = Some locals ->
      generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state
        = OK (raw, st_n) ->
      listSatisfiable w raw ->
      exists_hyp all_nodes G envs aux pre ->
      forall xs ck f exps callee callee_sig ckty inptyp outtyp st_clk st_inp,
        In (EqApp xs ck f exps None) n.(n_eqs) ->
        find_node f all_nodes = Some callee ->
        SIG.find_signature f G = Some callee_sig ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env clk_type ck)
          SC.init_state = OK (ckty, st_clk) ->
        SC.mmap (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          exps st_clk = OK (inptyp, st_inp) ->
        get_mappings xs ty_env = Some outtyp ->
        callee_secure all_nodes G envs aux n w w callee callee_sig
          (SIGPROOFS.lat_valuation w callee_sig inptyp ckty [rst_type] outtyp)
          (SIGPROOFS.lat_valuation w callee_sig inptyp ckty [rst_type] outtyp).
  Proof.
    intros all_nodes envs aux G pre n post ty_env clk_id rst_id clk_type rst_type
           inp out locals raw st_n w Henv Hord Hwc Hgen Hsplit Hfindenv Haux Hclk
           Hrst Hinp Hout Hlocals Hraw Hsatraw IHn xs ck f exps callee callee_sig
           ckty inptyp outtyp st_clk st_inp Heqin Hfn Hfs Hck Hinp0 Hout0.
    pose proof (Ordered_nodes_nodup_names all_nodes Hord) as Hnd.
    assert (Hnin : In n all_nodes).
    { apply (proj2 (in_rev _ _)). rewrite Hsplit. apply in_or_app. right. left. reflexivity. }
    pose proof (find_node_of_In' all_nodes n Hnd Hnin) as Hfindnode.
    assert (Hwcn : Clo.wc_node all_nodes n).
    { pose proof (wc_nodes_rev all_nodes Hord Hwc) as Hall.
      rewrite Forall_forall in Hall. apply Hall. apply (proj1 (in_rev _ _)).
      exact Hnin. }
    assert (Hisnode : Is_node_in f n.(n_eqs)).
    { apply Exists_exists. exists (EqApp xs ck f exps None). split; [exact Heqin|constructor]. }
    pose proof (callee_in_pre all_nodes pre n post f callee Hord Hsplit Hisnode Hfn)
      as Hcpre.
    pose proof (proj1 (find_node_In _ _ _ Hfn)) as Hcname.
    assert (Hcallee_all : In callee all_nodes) by (exact (proj2 (find_node_In _ _ _ Hfn))).
    assert (Hfs' : SIG.find_signature callee.(n_name) G = Some callee_sig)
      by (rewrite Hcname; exact Hfs).
    pose proof (regen_full2 all_nodes envs aux G Hord Hgen callee callee_sig
                  Hcallee_all Hfs') as Hsigc.
    unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigc.
    destruct (find_node_env callee.(n_name) envs) as [env_c|] eqn:Hfindenvc;
      [|discriminate].
    fold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigc.
    assert (Hfindcallee : find_node callee.(n_name) all_nodes = Some callee)
      by (rewrite Hcname; exact Hfn).
    assert (Hsigc' : SECNLUSTYPING.generate_node_sig_scoped_env G callee envs aux
                     = OK callee_sig)
      by (unfold SECNLUSTYPING.generate_node_sig_scoped_env;
          rewrite Hfindenvc; exact Hsigc).
    assert (Hneq : n.(n_name) <> callee.(n_name)).
    { intro E. pose proof Hnd as Hnd0.
      assert (Hndr : NoDup (map n_name (pre ++ n :: post))).
      { rewrite <- Hsplit. rewrite map_rev.
        eapply Permutation_NoDup; [apply Permutation_rev|exact Hnd]. }
      rewrite map_app in Hndr. simpl in Hndr.
      apply NoDup_app_In with (x := callee.(n_name)) in Hndr.
      - apply Hndr. left. exact E.
      - apply in_map. exact Hcpre. }
    assert (Hscopefresh : SIG.scope_fresh
                            (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                            callee_sig).
    { eapply (generated_caller_scope_fresh_scoped_env all_nodes G envs aux n callee
                ty_env env_c callee_sig clk_id rst_id clk_type rst_type inp out
                locals); eauto. }
    assert (HgoodG : SIG.secglobal_good G).
    { eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env
        with (P := all_nodes).
      - exact Henv.
      - exact (wc_nodes_rev all_nodes Hord Hwc).
      - exact Hgen. }
    assert (Hgood_c : SIG.signature_good callee_sig) by (eapply HgoodG; exact Hfs).
    (* the call's block, read off the raw constraints *)
    destruct xs as [|x xs0].
    { exfalso.
      destruct Hwcn as [_ [_ [_ Hwc_eqs]]].
      rewrite Forall_forall in Hwc_eqs.
      pose proof (Hwc_eqs _ Heqin) as Hwcapp.
      inversion Hwcapp as [|xs1 ck1 f1 exps1 r1 n1 sub Hfindwc Hwcins Hwcouts Hwcrst|];
        subst.
      apply Forall2_length in Hwcouts. simpl in Hwcouts.
      pose proof (n1.(n_outgt0)) as Hgt0. lia. }
    destruct (generate_eqns_constraints_member G ty_env clk_type rst_type n.(n_eqs)
                raw init_state st_n (EqApp (x :: xs0) ck f exps None) Heqin Hraw)
      as (ceq & pre0 & post0 & steq & stceq & Hrawsplit & Hgeq).
    destruct (generate_eqapp_constraint_inv G ty_env clk_type rst_type x xs0 ck f
                exps ceq steq stceq Hgeq)
      as (nsig_c & ckty0 & inptyp0 & outtyp0 & st_clk0 & st_inp0 & Hfindsigc
          & Hck0 & Hinp0' & Hout0' & Hcallc).
    assert (Hnsig_eq : nsig_c = callee_sig) by congruence.
    subst nsig_c.
    assert (Hckeq : ckty0 = ckty).
    { pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck0)
        as H1.
      pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck)
        as H2.
      rewrite H1 in H2. inversion H2. reflexivity. }
    subst ckty0.
    assert (Hinpeq : inptyp0 = inptyp).
    { pose proof (mmap_assign_exp_type_state_irrel _ _ _ _ _ init_state Hinp0') as H1.
      pose proof (mmap_assign_exp_type_state_irrel _ _ _ _ _ init_state Hinp0) as H2.
      rewrite H1 in H2. inversion H2. reflexivity. }
    subst inptyp0.
    assert (Houteq : outtyp0 = outtyp) by congruence.
    subst outtyp0.
    assert (Hsatceq : listSatisfiable w ceq).
    { rewrite Hrawsplit in Hsatraw. exact (listSatisfiable_app_middle w pre0 ceq post0 Hsatraw). }
    assert (Hrstsc : SecT.st_scoped
                       (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                       [rst_type]).
    { apply SecT.st_scoped_singleton. repeat (apply in_or_app; right).
      simpl. right. left. reflexivity. }
    pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck)
      as Hck_init.
    assert (Hfresh : SIG.call_subst_fresh callee_sig inptyp ckty [rst_type] outtyp)
      by exact (call_fresh_of_eq all_nodes n ty_env inp out locals clk_type
                  rst_type (x :: xs0) ck f exps None callee_sig inptyp ckty
                  [rst_type] outtyp st_clk st_inp init_state Hinp Hout Hlocals
                  Hwcn Heqin Hscopefresh Hinp0 Hck_init Hrstsc Hout0).
    pose proof (sig_sat_of_call callee_sig inptyp ckty [rst_type] outtyp ceq
                  st_inp0 stceq w Hgood_c Hfresh Hcallc Hsatceq) as Hsatind.
    destruct (IHn callee callee_sig Hcpre Hfs' _ Hsatind) as (wc & Hag & Hsec).
    exact (CalleeSecure all_nodes G envs aux n w w callee callee_sig _ _ wc Hag Hsec).
  Qed.

  Lemma reset_call_clause :
    forall all_nodes envs aux G pre n post
           ty_env clk_id rst_id clk_type rst_type inp out locals raw st_n w,
      NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux) ->
      Ordered_nodes all_nodes -> Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux
        = OK G ->
      rev all_nodes = pre ++ n :: post ->
      find_node_env n.(n_name) envs = Some ty_env ->
      get_node_aux n.(n_name) aux = Some (clk_id, rst_id) ->
      Env.find clk_id ty_env = Some clk_type ->
      Env.find rst_id ty_env = Some rst_type ->
      get_mappings_from_node n.(n_in) ty_env = Some inp ->
      get_mappings_from_node n.(n_out) ty_env = Some out ->
      get_mappings_from_node n.(n_vars) ty_env = Some locals ->
      generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state
        = OK (raw, st_n) ->
      listSatisfiable w raw ->
      exists_hyp all_nodes G envs aux pre ->
      forall xs ck f exps r ckr callee callee_sig ckty rty rstty inptyp outtyp
             st_clk st_rst st_inp,
        In (EqApp xs ck f exps (Some (r, ckr))) n.(n_eqs) ->
        find_node f all_nodes = Some callee ->
        SIG.find_signature f G = Some callee_sig ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env clk_type ck)
          SC.init_state = OK (ckty, st_clk) ->
        Env.find r ty_env = Some rty ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env clk_type ckr)
          st_clk = OK (rstty, st_rst) ->
        SC.mmap (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          exps st_rst = OK (inptyp, st_inp) ->
        get_mappings xs ty_env = Some outtyp ->
        callee_secure all_nodes G envs aux n w w callee callee_sig
          (SIGPROOFS.lat_valuation w callee_sig inptyp ckty
             ([rst_type] ⊔ ([rty] ⊔ rstty)) outtyp)
          (SIGPROOFS.lat_valuation w callee_sig inptyp ckty
             ([rst_type] ⊔ ([rty] ⊔ rstty)) outtyp).
  Proof.
    intros all_nodes envs aux G pre n post ty_env clk_id rst_id clk_type rst_type
           inp out locals raw st_n w Henv Hord Hwc Hgen Hsplit Hfindenv Haux Hclk
           Hrst Hinp Hout Hlocals Hraw Hsatraw IHn xs ck f exps r ckr callee callee_sig
           ckty rty rstty inptyp outtyp st_clk st_rst st_inp Heqin Hfn Hfs Hck
           Hr Hrck Hinp0 Hout0.
    pose proof (Ordered_nodes_nodup_names all_nodes Hord) as Hnd.
    assert (Hnin : In n all_nodes).
    { apply (proj2 (in_rev _ _)). rewrite Hsplit. apply in_or_app. right. left. reflexivity. }
    pose proof (find_node_of_In' all_nodes n Hnd Hnin) as Hfindnode.
    assert (Hwcn : Clo.wc_node all_nodes n).
    { pose proof (wc_nodes_rev all_nodes Hord Hwc) as Hall.
      rewrite Forall_forall in Hall. apply Hall. apply (proj1 (in_rev _ _)).
      exact Hnin. }
    assert (Hisnode : Is_node_in f n.(n_eqs)).
    { apply Exists_exists. exists (EqApp xs ck f exps (Some (r, ckr))). split; [exact Heqin|constructor]. }
    pose proof (callee_in_pre all_nodes pre n post f callee Hord Hsplit Hisnode Hfn)
      as Hcpre.
    pose proof (proj1 (find_node_In _ _ _ Hfn)) as Hcname.
    assert (Hcallee_all : In callee all_nodes) by (exact (proj2 (find_node_In _ _ _ Hfn))).
    assert (Hfs' : SIG.find_signature callee.(n_name) G = Some callee_sig)
      by (rewrite Hcname; exact Hfs).
    pose proof (regen_full2 all_nodes envs aux G Hord Hgen callee callee_sig
                  Hcallee_all Hfs') as Hsigc.
    unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigc.
    destruct (find_node_env callee.(n_name) envs) as [env_c|] eqn:Hfindenvc;
      [|discriminate].
    fold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigc.
    assert (Hfindcallee : find_node callee.(n_name) all_nodes = Some callee)
      by (rewrite Hcname; exact Hfn).
    assert (Hsigc' : SECNLUSTYPING.generate_node_sig_scoped_env G callee envs aux
                     = OK callee_sig)
      by (unfold SECNLUSTYPING.generate_node_sig_scoped_env;
          rewrite Hfindenvc; exact Hsigc).
    assert (Hneq : n.(n_name) <> callee.(n_name)).
    { intro E. pose proof Hnd as Hnd0.
      assert (Hndr : NoDup (map n_name (pre ++ n :: post))).
      { rewrite <- Hsplit. rewrite map_rev.
        eapply Permutation_NoDup; [apply Permutation_rev|exact Hnd]. }
      rewrite map_app in Hndr. simpl in Hndr.
      apply NoDup_app_In with (x := callee.(n_name)) in Hndr.
      - apply Hndr. left. exact E.
      - apply in_map. exact Hcpre. }
    assert (Hscopefresh : SIG.scope_fresh
                            (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                            callee_sig).
    { eapply (generated_caller_scope_fresh_scoped_env all_nodes G envs aux n callee
                ty_env env_c callee_sig clk_id rst_id clk_type rst_type inp out
                locals); eauto. }
    assert (HgoodG : SIG.secglobal_good G).
    { eapply SECNLUSTYPINGCORRECTNESS.generate_all_source_signatures_good_scoped_env
        with (P := all_nodes).
      - exact Henv.
      - exact (wc_nodes_rev all_nodes Hord Hwc).
      - exact Hgen. }
    assert (Hgood_c : SIG.signature_good callee_sig) by (eapply HgoodG; exact Hfs).
    (* the call's block, read off the raw constraints *)
    destruct xs as [|x xs0].
    { exfalso.
      destruct Hwcn as [_ [_ [_ Hwc_eqs]]].
      rewrite Forall_forall in Hwc_eqs.
      pose proof (Hwc_eqs _ Heqin) as Hwcapp.
      inversion Hwcapp as [|xs1 ck1 f1 exps1 r1 n1 sub Hfindwc Hwcins Hwcouts Hwcrst|];
        subst.
      apply Forall2_length in Hwcouts. simpl in Hwcouts.
      pose proof (n1.(n_outgt0)) as Hgt0. lia. }
    destruct (generate_eqns_constraints_member G ty_env clk_type rst_type n.(n_eqs)
                raw init_state st_n (EqApp (x :: xs0) ck f exps (Some (r, ckr))) Heqin Hraw)
      as (ceq & pre0 & post0 & steq & stceq & Hrawsplit & Hgeq).
    destruct (generate_eqreset_constraint_inv G ty_env clk_type rst_type x xs0 ck f
                exps r ckr ceq steq stceq Hgeq)
      as (nsig_c & ckty0 & rty0 & rstty0 & inptyp0 & outtyp0 & st_clk0 & st_rst0
          & st_inp0 & Hfindsigc & Hck0 & Hr0 & Hrst0 & Hinp0' & Hout0' & Hcallc).
    assert (Hnsig_eq : nsig_c = callee_sig) by congruence.
    subst nsig_c.
    assert (Hckeq : ckty0 = ckty).
    { pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck0)
        as H1.
      pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck)
        as H2.
      rewrite H1 in H2. inversion H2. reflexivity. }
    subst ckty0.
    assert (Hrtyeq : rty0 = rty) by congruence.
    subst rty0.
    assert (Hrsteq : rstty0 = rstty).
    { pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hrst0)
        as H1.
      pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hrck)
        as H2.
      rewrite H1 in H2. inversion H2. reflexivity. }
    subst rstty0.
    assert (Hinpeq : inptyp0 = inptyp).
    { pose proof (mmap_assign_exp_type_state_irrel _ _ _ _ _ init_state Hinp0') as H1.
      pose proof (mmap_assign_exp_type_state_irrel _ _ _ _ _ init_state Hinp0) as H2.
      rewrite H1 in H2. inversion H2. reflexivity. }
    subst inptyp0.
    assert (Houteq : outtyp0 = outtyp) by congruence.
    subst outtyp0.
    assert (Hsatceq : listSatisfiable w ceq).
    { rewrite Hrawsplit in Hsatraw. exact (listSatisfiable_app_middle w pre0 ceq post0 Hsatraw). }
    pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hck)
      as Hck_init.
    pose proof (option_to_sec_assign_clk_state_irrel _ _ _ _ _ _ init_state Hrck)
      as Hrck_init.
    assert (Hrstsc : SecT.st_scoped
                       (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                       ([rst_type] ⊔ ([rty] ⊔ rstty)))
      by exact (reset_rst_scoped all_nodes n ty_env inp out locals clk_type
                  rst_type (x :: xs0) ck f exps r ckr rty rstty init_state Hinp
                  Hout Hlocals Hwcn Heqin Hr Hrck_init).
    assert (Hfresh : SIG.call_subst_fresh callee_sig inptyp ckty
                       ([rst_type] ⊔ ([rty] ⊔ rstty)) outtyp)
      by exact (call_fresh_of_eq all_nodes n ty_env inp out locals clk_type
                  rst_type (x :: xs0) ck f exps (Some (r, ckr)) callee_sig inptyp
                  ckty _ outtyp st_rst st_inp init_state Hinp Hout Hlocals
                  Hwcn Heqin Hscopefresh Hinp0 Hck_init Hrstsc Hout0).
    pose proof (sig_sat_of_call callee_sig inptyp ckty ([rst_type] ⊔ ([rty] ⊔ rstty)) outtyp ceq
                  st_inp0 stceq w Hgood_c Hfresh Hcallc Hsatceq) as Hsatind.
    destruct (IHn callee callee_sig Hcpre Hfs' _ Hsatind) as (wc & Hag & Hsec).
    exact (CalleeSecure all_nodes G envs aux n w w callee callee_sig _ _ wc Hag Hsec).
  Qed.

  Theorem node_security_exists_pos :
    forall all_nodes envs aux G,
      NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux) ->
      Ordered_nodes all_nodes -> Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux
        = OK G ->
      forall m pre n post,
        rev all_nodes = pre ++ n :: post -> length pre = m ->
        forall sig d1,
          SIG.find_signature n.(n_name) G = Some sig ->
          signature_satisfied d1 sig ->
          exists w, SecT.agree_on (signature_scope sig) d1 w
                    /\ node_security all_nodes G envs aux n w w.
  Proof.
    intros all_nodes envs aux G Henv Hord Hwc Hgen m.
    induction m as [m IH] using lt_wf_ind.
    intros pre n post Hsplit Hlen sig d1 Hfindsig Hsat.
    pose proof (Ordered_nodes_nodup_names all_nodes Hord) as Hnd.
    assert (Hnin : In n all_nodes).
    { apply (proj2 (in_rev _ _)). rewrite Hsplit. apply in_or_app. right. left.
      reflexivity. }
    pose proof (find_node_of_In' all_nodes n Hnd Hnin) as Hfindnode.
    assert (Hwcn : Clo.wc_node all_nodes n).
    { pose proof (wc_nodes_rev all_nodes Hord Hwc) as Hall.
      rewrite Forall_forall in Hall. apply Hall. apply (proj1 (in_rev _ _)).
      exact Hnin. }
    pose proof (regen_full2 all_nodes envs aux G Hord Hgen n sig Hnin Hfindsig)
      as Hsiggen.
    assert (Hfindenv : exists ty_env, find_node_env n.(n_name) envs = Some ty_env).
    { unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsiggen.
      destruct (find_node_env n.(n_name) envs) as [e|]; [exists e; reflexivity|discriminate]. }
    destruct Hfindenv as (ty_env & Hfindenv).
    destruct (signature_satisfied_replays_raw all_nodes G envs aux all_nodes n
                ty_env sig d1 Henv Hwcn Hfindnode Hfindenv Hsiggen Hsat)
      as (w & clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw
          & st_n & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef
          & Hagree & Hsatraw).
    exists w. split; [exact Hagree|].
    (* callees come earlier in the reversed program *)
    assert (IHn : exists_hyp all_nodes G envs aux pre).
    { intros callee callee_sig Hcpre Hfs d1c Hsatc.
      destruct (in_split _ _ Hcpre) as (p1 & p2 & Hpre).
      assert (Hs2 : rev all_nodes = p1 ++ callee :: (p2 ++ n :: post)).
      { rewrite Hsplit, Hpre. rewrite <- app_assoc. reflexivity. }
      assert (Hl : length p1 < m).
      { rewrite <- Hlen, Hpre, app_length. simpl. lia. }
      exact (IH (length p1) Hl p1 callee (p2 ++ n :: post) Hs2 Logic.eq_refl
               callee_sig d1c Hfs Hsatc). }
    subst sig.
    assert (Hsatw : signature_satisfied w {| s_name := n_name n; s_in := inp; s_out := out; s_reset := rst_type; s_clk := clk_type; s_constraints := SymTypes.simplify raw locals |}).
    { unfold signature_satisfied, signature_constraints. cbn [s_constraints].
      eapply SecT.simplify_is_correct; [exact Hsatraw|]. apply SecT.simplify_simplifyRel. reflexivity. }
    refine (SecureNode all_nodes G envs aux n w w ty_env _ clk_id rst_id clk_type
              rst_type inp out locals raw st_n Hfindnode Hfindenv Hfindsig Hsiggen
              Haux Hclk Hrst Hinp Hout Hlocals Hraw Logic.eq_refl Hsatw (fun x _ => Logic.eq_refl)
              Hsatraw _ _).
    - intros xs ck f exps callee callee_sig ckty inptyp outtyp st_clk st_inp
             Heqin Hfn Hfs Hck Hinp0 Hout0.
      eapply (simple_call_clause all_nodes envs aux G pre n post ty_env clk_id
               rst_id clk_type rst_type inp out locals raw st_n w Henv Hord Hwc
               Hgen Hsplit Hfindenv Haux Hclk Hrst Hinp Hout Hlocals Hraw Hsatraw
               IHn); eassumption.
    - intros xs ck f exps r ckr callee callee_sig ckty rty rstty inptyp outtyp
             st_clk st_rst st_inp Heqin Hfn Hfs Hck Hr Hckr Hinp0 Hout0.
      eapply (reset_call_clause all_nodes envs aux G pre n post ty_env clk_id
               rst_id clk_type rst_type inp out locals raw st_n w Henv Hord Hwc
               Hgen Hsplit Hfindenv Haux Hclk Hrst Hinp Hout Hlocals Hraw Hsatraw
               IHn); eassumption.
  Qed.

  (** ** From a source policy to a [node_security] witness

      The signature half ([Check.source_policy_realised]) turns a valuation
      satisfying the stored constraints of a source signature -- a policy on
      the node's interface -- into the statement [signatures_preserved] against the
      transcribed NLustre signature.  Together with the construction above this
      yields the witness the noninterference chain consumes, agreeing with
      the policy on the interface. *)
  Theorem policy_node_security :
    forall all_nodes envs aux G,
      NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux) ->
      Ordered_nodes all_nodes -> Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux
        = OK G ->
      forall pre n post,
        rev all_nodes = pre ++ n :: post ->
        forall sgS sgN d1,
          SIG.find_signature n.(n_name) G = Some sgN ->
          SIGPROOFS.signatures_preserved sgS sgN ->
          signature_satisfied d1 sgS ->
          exists w, SecT.agree_on (signature_scope sgS) d1 w
                    /\ node_security all_nodes G envs aux n w w.
  Proof.
    intros all_nodes envs aux G Henv Hord Hwc Hgen pre n post Hsplit sgS sgN d1
      Hfind (Hfields & Hpres) Hsat.
    destruct (Hpres d1 Hsat) as (d' & Hag1 & Hsat').
    destruct (node_security_exists_pos all_nodes envs aux G Henv Hord Hwc Hgen
                _ pre n post Hsplit Logic.eq_refl sgN d' Hfind Hsat')
      as (w & Hag2 & Hsec).
    exists w. split; [|exact Hsec].
    assert (Hscope : signature_scope sgS = signature_scope sgN).
    { unfold signature_scope. destruct Hfields as (Hi & Ho & Hr & Hc).
      rewrite Hi, Ho, Hr, Hc. reflexivity. }
    intros x Hx. rewrite (Hag1 x) by (exact Hx). apply Hag2.
    rewrite <- Hscope. exact Hx.
  Qed.

End SecNLusNodeSecurity.
