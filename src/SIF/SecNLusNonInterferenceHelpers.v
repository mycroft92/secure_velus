(* Indexed-semantics observation layer for NLustre noninterference.

   This file starts the thesis-specific noninterference development on the
   source language side.  The first step is to formalise the paper's
   [(⊑ t)-projected Stream] notion directly over the indexed semantics used by
   Vélus:

   - raw program variables are observed through a generated local security env;
   - a ground instantiation assigns lattice classes to generated security ids;
   - projection keeps exactly those raw variables whose security class is at
     most the observation level [t].

   The later semantic theorems should be stated against the relational form
   [history_low_eq], while the concrete projector [project_history_le_t] keeps a
   paper-facing version of the same notion. *)

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
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECNLUSNONINTERFERENCEHELPERS
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
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
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
     SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo
       Ord Mem IsD IsF Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecT SIG SIGPROOFS
       NAMEGEN SECCETYPING CEIsF CEClo Ord Mem IsD IsF Clo SECNLUSTYPING).

  (** Vocabulary alignment with the papers.

      The noninterference papers use:
      - [s] for a ground instantiation of symbolic security variables;
      - [ρ] for the generated constraints attached to a node signature.

      In the Coq development we standardise this as follows:
      - [dlt] is the ground instantiation used throughout [SecTypes] and
        [SIFSignature];
      - [sig.(s_constraints)] is exactly the paper's [ρ];
      - "ρ is satisfied by s" is formalised as [signature_satisfied dlt sig].

      Keeping this translation explicit avoids introducing parallel notation in
      the noninterference proof. *)

  Include SECNLUSNONINTERFERENCESUPPORT
    Ids Lat Op OpAux SC SecT CESyn SynNL SIG NAMEGEN SECCETYPING CETyp CEIsF
    CEClo Str Ord Mem IsD IsF NLCaus Clo CESem CEProps Indexed SIGPROOFS SECNLUSTYPING
    SECNLUSTYPINGCORRECTNESS.

  Section GENERATED_NODE_NONINTERFERENCE.
    Variable all_nodes : global.
    Variable G : secglobal.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.

    (** Reset control low-equality on a finite prefix.

        Relation to the paper:
        reset is not a plain NLustre source input carried in
        [map fst n.(n_in)].  In indexed semantics it appears as a Boolean
        control stream extracted by [bools_of] and consumed through [count]
        and [mask].  This definition is therefore the reset-aware analogue of
        low input equality: if the reset source variable is low, then the
        induced reset segment counters agree on the whole prefix. *)
    Definition reset_control_low_eq_upto
      (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
      (r : ident) (H H' : history) (k : nat) : Prop :=
      forall ys ys' rs rs',
        sem_var H r ys ->
        sem_var H' r ys' ->
        bools_of ys rs ->
        bools_of ys' rs' ->
        low_var ty_env dlt t r ->
        forall j, j <= k -> count rs j = count rs' j.

    (** Build reset-control equality from prefix equality of the reset source.

        Relation to the paper:
        resettable calls consume reset through the Boolean/masked semantics,
        but the causality theorem naturally provides equality first at the
        source variable level.  This lemma is the semantic bridge from low
        equality of the reset source stream to equality of reset segment
        counters on the observed prefix. *)
    Lemma reset_control_low_eq_upto_of_sem_var_eq :
      forall ty_env dlt t r H H' k,
        (low_var ty_env dlt t r ->
         forall j, j <= k -> Env.find r (H j) = Env.find r (H' j)) ->
        reset_control_low_eq_upto ty_env dlt t r H H' k.
    Proof.
      intros ty_env dlt t r H H' k Heq ys ys' rs rs'
             Hsemr Hsemr' Hbool Hbool' Hlowr j Hj.
      assert (Hys_eq : forall j0, j0 <= k -> ys j0 = ys' j0).
      {
        eapply sem_var_low_eq_upto; eauto.
      }
      assert (Hrs_eq : forall j0, j0 <= k -> rs j0 = rs' j0).
      {
        eapply bools_of_eq_upto; eauto.
      }
      exact (count_eq_upto rs rs' k Hrs_eq j Hj).
    Qed.

    (** Base-clock equality on a finite prefix.

        Relation to the paper:
        the public theorem ultimately compares two executions under the same
        ambient clock, but recursive call proofs run under derived clocks.  We
        keep that extra proof-internal alignment premise explicit at the helper
        layer so the older local step theorem can consume it directly. *)
    Definition clock_eq_upto
      (bk bk' : cstream) (k : nat) : Prop :=
      forall j, j <= k -> bk j = bk' j.

    Lemma clock_eq_upto_refl :
      forall bk k,
        clock_eq_upto bk bk k.
    Proof.
      intros bk k j Hj.
      reflexivity.
    Qed.

    (** Agreement on a symbolic scope is symmetric.

        Relation to the paper:
        replay from simplified signatures to raw constraints gives an
        agreement fact between the canonical valuation and the replayed one.
        The final noninterference corollary needs to use that agreement in
        both directions when transporting low-observation facts between the
        two valuations. *)
    Lemma agree_on_sym:
      forall scope dlt1 dlt2,
        SecT.agree_on scope dlt1 dlt2 ->
        SecT.agree_on scope dlt2 dlt1.
    Proof.
      intros scope dlt1 dlt2 Hagree x Hin.
      symmetry. exact (Hagree x Hin).
    Qed.

    (** Low observability is preserved under scope agreement.

        Relation to the paper:
        if two ground instantiations agree on the symbolic identifiers that
        classify one raw variable, then that variable has the same
        low-observability status under both instantiations.  This is the
        valuation-transport step needed after replay. *)
    Lemma low_var_agree_on_scope:
      forall ty_env t scope dlt1 dlt2 x alpha,
        Env.find x ty_env = Some alpha ->
        In alpha scope ->
        SecT.agree_on scope dlt1 dlt2 ->
        low_var ty_env dlt1 t x ->
        low_var ty_env dlt2 t x.
    Proof.
      intros ty_env t scope dlt1 dlt2 x alpha Hfind Hinscope Hagree Hlow.
      destruct Hlow as (alpha' & Hfind' & Hle).
      rewrite Hfind in Hfind'.
      inversion Hfind'. subst alpha'. clear Hfind'.
      exists alpha.
      split; [exact Hfind|].
      rewrite <- (Hagree alpha Hinscope).
      exact Hle.
    Qed.

    (** Transport low-equivalence across agreeing valuations.

        Relation to the paper:
        replay changes the valuation used to interpret symbolic security
        identifiers, but it keeps the visible signature scope unchanged.
        This lemma lifts that scope agreement from individual variables to the
        relational history observation [history_low_eq]. *)
    Lemma history_low_eq_agree_on_scope:
      forall ty_env t X scope dlt1 dlt2 H H',
        (forall x, In x X -> exists alpha, Env.find x ty_env = Some alpha /\ In alpha scope) ->
        SecT.agree_on scope dlt1 dlt2 ->
        history_low_eq ty_env dlt1 t X H H' ->
        history_low_eq ty_env dlt2 t X H H'.
    Proof.
      intros ty_env t X scope dlt1 dlt2 H H' Hscope Hagree Hlow k x Hin Hobs.
      apply Hlow; [exact Hin|].
      destruct (Hscope x Hin) as (alpha & Hfind & Hinscope).
      eapply low_var_agree_on_scope; eauto.
      eapply agree_on_sym; eauto.
    Qed.

    (** Low-equivalence weakens along observation-set inclusion.

        Relation to the paper:
        once the proof establishes agreement on a larger visible set, it may
        immediately be restricted to any smaller observed interface such as the
        node outputs. *)
    Lemma history_low_eq_weaken:
      forall ty_env dlt t X Y H H',
        (forall x, In x Y -> In x X) ->
        history_low_eq ty_env dlt t X H H' ->
        history_low_eq ty_env dlt t Y H H'.
    Proof.
      intros ty_env dlt t X Y H H' Hsub Hlow k x Hin Hobs.
      eapply Hlow; eauto.
    Qed.

    (** Replaying the stored node signature back to raw equation constraints.

        Relation to the paper:
        the paper-level node security hypothesis only stores the simplified
        node constraints [ρ].  The indexed noninterference proof for
        [vars_defined] must reason about the raw per-equation constraints
        before local variables are eliminated.  This lemma is the source-side
        bridge from the stored satisfiability fact [signature_satisfied dlt sig]
        to a completed ground instantiation that satisfies the raw
        constraints and still agrees with the original [dlt] on the visible
        signature scope.

        Concretely, the lemma states that whenever the generated scoped node
        signature [sig] is satisfied by [dlt], one can recover:

        - the exact raw equation-constraint generation data for the current
          node (clock/reset security ids, input/output/local mappings, and the
          raw constraint list [raw]); and
        - a completed valuation [dlt_raw] such that:
          [SecT.agree_on (signature_scope sig) dlt dlt_raw] and
          [SecT.listSatisfiable dlt_raw raw].

        So this lemma is precisely what lets the later proof move from the
        stored simplified signature back to the unsimplified per-equation
        constraints without losing agreement on the externally visible
        interface. *)
    Lemma signature_satisfied_replays_raw:
      forall P n ty_env sig dlt,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Clo.wc_node P n ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G n envs aux_names = OK sig ->
        signature_satisfied dlt sig ->
        exists dlt_raw clk_id rst_id clk_type rst_type inp out locals raw st_n,
          get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id)
          /\ Env.find clk_id ty_env = Some clk_type
          /\ Env.find rst_id ty_env = Some rst_type
          /\ get_mappings_from_node n.(n_in) ty_env = Some inp
          /\ get_mappings_from_node n.(n_out) ty_env = Some out
          /\ get_mappings_from_node n.(n_vars) ty_env = Some locals
          /\ generate_eqns_constraints G ty_env clk_type rst_type n.(n_eqs) init_state = OK (raw, st_n)
          /\ sig = {| s_name := n.(n_name);
                      s_in := inp;
                      s_out := out;
                      s_reset := rst_type;
                      s_clk := clk_type;
                      s_constraints := SymTypes.simplify raw locals |}
          /\ SecT.agree_on (signature_scope sig) dlt dlt_raw
          /\ SecT.listSatisfiable dlt_raw raw.
    Proof.
      intros P n ty_env sig dlt
             Henvsgen Hwc Hfindnode Hfindenv Hsigsc Hsatsig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsigsc.
      rewrite Hfindenv in Hsigsc.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv
           G n ty_env aux_names sig Hsigsc)
        as Hinv.
      destruct Hinv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & raw & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hraw & Hsigdef).
      pose proof (find_node_In _ _ _ Hfindnode) as [_ Hin].
      apply in_split in Hin as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'. clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node as
          (envs_pref & aux_pref & st_pref & local_env & rec & st_local
           & envs_cur & st_cur & Hpref & Hlocalgen & Hins & Htail);
        eauto.
      assert (Hcurfind : find_node_env n.(n_name) envs_cur = Some local_env).
      { eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto. }
      assert (Hlocalfind : find_node_env n.(n_name) envs = Some local_env).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto. }
      rewrite Hfindenv in Hlocalfind.
      inversion Hlocalfind.
      assert (Hauxhead :
                get_node_aux n.(n_name) (rec :: aux_pref) =
                Some (rec.(nclk), rec.(nrst))).
      {
        pose proof Hlocalgen as Hlocalshape.
        unfold NAMEGEN.generate_local_env_for_node in Hlocalshape.
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (clk_name & stc & Hclkgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (rst_name & str & Hrstgen & Hlocalshape).
        eapply NAMEGEN.name_bind_inv in Hlocalshape
          as (env0 & ste & Henvgen & Hret0).
        unfold NAMEGEN.NMret in Hret0.
        inversion Hret0; subst rec st_local.
        unfold get_node_aux. simpl.
        rewrite ident_eqb_refl. reflexivity.
      }
      assert (Hauxrec :
                get_node_aux n.(n_name) aux_names =
                Some (rec.(nclk), rec.(nrst))).
      { eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto. }
      rewrite Haux in Hauxrec.
      inversion Hauxrec; subst clk_id rst_id.
      assert (Hsigshape :
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}
                =
                {| s_name := n.(n_name);
                   s_in := inp;
                   s_out := out;
                   s_reset := rst_type;
                   s_clk := clk_type;
                   s_constraints := SymTypes.simplify raw locals |}).
      { reflexivity. }
      subst ty_env sig.
      pose proof
        (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_from_local_env
           G n
           {| s_name := n.(n_name);
              s_in := inp;
              s_out := out;
              s_reset := rst_type;
              s_clk := clk_type;
              s_constraints := SymTypes.simplify raw locals |}
           local_env rec aux_names st_pref st_local
           clk_type rst_type inp out locals raw st_n
           Hlocalgen Hsigsc Hclk Hrst Hinp Hout Hlocals Hraw Hsigshape)
        as Hready.
      destruct Hready as [Hwfraw Hlocalsdisj].
      edestruct (SecT.simplify_complete
                   raw locals
                   (signature_scope
                      {| s_name := n.(n_name);
                         s_in := inp;
                         s_out := out;
                         s_reset := rst_type;
                         s_clk := clk_type;
                         s_constraints := SymTypes.simplify raw locals |})
                   dlt)
        as (dlt_raw & Hagree & Hsatraw); eauto. 
        exists dlt_raw, rec.(nclk), rec.(nrst), clk_type, rst_type, inp, out, locals, raw, st_n.
        repeat split; auto.
    Qed.

    (** Restrict the NLustre causality induction to defined variables.

        Relation to the paper:
        the source causality proof naturally propagates a pointwise property
        over the whole node variable set (inputs, locals, outputs).  The
        internal noninterference theorem only needs the conclusion on
        [vars_defined n.(n_eqs)], because that is the exact set tracked by the
        generated raw constraints.  This lemma is the packaging step from the
        full node-level causality induction back down to the defined-variable
        view used in the theorem statement. *)
    Lemma nl_node_causal_ind_defined:
      forall (n : node) (P_var : ident -> Prop),
        (forall eq x,
            In eq n.(n_eqs) ->
            In x (var_defined eq) ->
            (forall y, NLCaus.nl_depends_on_eq eq x y -> P_var y) ->
            P_var x) ->
        Forall P_var (map fst n.(n_in)) ->
        NLCaus.nl_node_causal n ->
        Forall P_var (vars_defined n.(n_eqs)).
    Proof.
      intros n P_var Heqcase Hinputs Hcaus.
      pose proof
        (NLCaus.nl_node_causal_ind
           n P_var Heqcase Hinputs Hcaus)
        as Hall.
      rewrite map_app in Hall.
      apply Forall_app in Hall as [_ Hdefd].
      rewrite n.(n_defd).
      exact Hdefd.
    Qed.

    (** Turn input low-equivalence into the pointwise input property used by
        the causality induction.

        Relation to the paper:
        the base case of the node-level causality induction is agreement on
        low inputs.  The semantic hypothesis is stated relationally as
        [history_low_eq], while the induction consumes one pointwise property
        per input variable. *)
    Lemma history_low_eq_inputs_pointwise:
      forall (n : node) ty_env dlt t H H',
        history_low_eq ty_env dlt t (map fst n.(n_in)) H H' ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall k, Env.find x (H k) = Env.find x (H' k))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' Hlow.
      apply Forall_forall.
      intros x Hin Hobs k.
      eapply Hlow; eauto.
    Qed.

    (** Turn prefix input low-equivalence into the pointwise input property
        consumed by the prefix step theorem.

        Relation to the paper:
        the time-indexed node proof reasons about one finite prefix at a time.
        This is the prefix counterpart of the basic input-agreement
        initialisation. *)
    Lemma history_low_eq_upto_inputs_pointwise:
      forall (n : node) ty_env dlt t H H' k,
        history_low_eq_upto ty_env dlt t (map fst n.(n_in)) H H' k ->
        Forall
          (fun x => low_var ty_env dlt t x ->
                    forall j, j <= k -> Env.find x (H j) = Env.find x (H' j))
          (map fst n.(n_in)).
    Proof.
      intros n ty_env dlt t H H' k Hlow.
      apply Forall_forall.
      intros x Hin Hobs j Hj.
      eapply Hlow; eauto.
    Qed.

    (** Extract one equation's raw constraint block from the node-wide
        generation result.

        Relation to the paper:
        the node proof proceeds equation by equation, but the generated source
        typing stores all raw constraints in one concatenated list.  This
        lemma is the bookkeeping step that recovers the exact sublist produced
        by one equation. *)
        (*Move this to SecNLusTyping.v later after proofs are done*)
    Lemma generate_eqns_constraints_member:
      forall ty_env clk_type rst_type eqs raw st st' eq,
        In eq eqs ->
        generate_eqns_constraints G ty_env clk_type rst_type eqs st = OK (raw, st') ->
        exists ceq pre post steq stceq,
          raw = pre ++ ceq ++ post
          /\ generate_eqn_constraint G ty_env clk_type rst_type eq steq = OK (ceq, stceq).
    Proof.
      intros ty_env clk_type rst_type eqs.
      induction eqs as [|eq0 eqs IH]; intros raw st st' eq Hin Hgen.
      - inversion Hin.
      - simpl in Hgen.
        eapply sec_bind_inv in Hgen as (c0 & st1 & Hc0 & Hgen).
        eapply sec_bind_inv in Hgen as (cs0 & st2 & Hcs0 & Hret).
        unfold ret in Hret. inversion Hret; subst raw st'. clear Hret.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst eq.
          exists c0, [], cs0, st, st1.
          split; [reflexivity|exact Hc0].
        + destruct (IH cs0 st1 st2 eq Hin Hcs0)
            as (ceq & pre & post & steq & stceq & Hraw & Hgeq).
          exists ceq, (c0 ++ pre), post, steq, stceq.
          split.
          * rewrite Hraw. now rewrite app_assoc.
          * exact Hgeq.
    Qed.

    (** Recover satisfiability of one extracted raw block.

        Relation to the paper:
        once an equation's raw constraint sublist is isolated, the local
        noninterference cases only need satisfiability of that one block. *)
    Lemma listSatisfiable_app_middle:
      forall dlt pre mid post,
        SecT.listSatisfiable dlt (pre ++ mid ++ post) ->
        SecT.listSatisfiable dlt mid.
    Proof.
      intros dlt pre mid post Hsat.
      unfold SecT.listSatisfiable in *.
      repeat rewrite Forall_app in Hsat.
      destruct Hsat as [_ [Hmid _]].
      exact Hmid.
    Qed.

    (** Invert the actual-argument typing map produced at a call site.

        Relation to the paper:
        the call case needs to connect each actual expression with the
        generated symbolic type used in the instantiated callee valuation.
        This lemma extracts that pointwise correspondence from the monadic
        [mmap] returned by [generate_eqn_constraint]. *)
    Lemma mmap_assign_exp_type_inv:
      forall ty_env es tys st st',
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        st' = st
        /\ Forall2
             (fun e ty => SECCETYPING.assign_exp_type ty_env e = Some ty)
             es tys.
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' Hmap.
      - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst.
        split; [reflexivity|constructor].
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ Htl) as [Hst Htys].
        subst st2.
        unfold ret in Hret. inversion Hret; subst tys st'.
        split; [reflexivity|].
        constructor; auto.
    Qed.

    (** [option_to_sec] on clock typing is state-irrelevant.

        Relation to the paper:
        extracted raw call constraints are located at some intermediate
        monadic state inside [generate_eqns_constraints], but the underlying
        symbolic clock assignment is pure.  This helper normalises such
        premises back to an arbitrary starting state when replaying the call
        theorem. *)
    Lemma option_to_sec_assign_clk_state_irrel:
      forall ty_env base ck st st' ckty st0,
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st = OK (ckty, st') ->
        SC.option_to_sec (SECCETYPING.assign_clk_type ty_env base ck) st0 = OK (ckty, st0).
    Proof.
      intros ty_env base ck st st' ckty st0 Hck.
      unfold SC.option_to_sec in *.
      destruct (SECCETYPING.assign_clk_type ty_env base ck) as [ckty'|] eqn:Hassign;
        try discriminate.
      inversion Hck; subst.
      reflexivity.
    Qed.

    (** [mmap] of pure expression typings is state-irrelevant.

        Relation to the paper:
        actual-argument typing at a call site depends only on the expressions
        and the caller environment, not on the surrounding monadic state.
        This lets the local noninterference proof replay the extracted raw
        argument typings at the canonical initial state expected by the
        recursive call theorem. *)
    Lemma mmap_assign_exp_type_state_irrel:
      forall ty_env es tys st st' st0,
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st = OK (tys, st') ->
        SC.mmap
          (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
          es st0 = OK (tys, st0).
    Proof.
      intros ty_env es.
      induction es as [|e es IH]; intros tys st st' st0 Hmap.
      - simpl in Hmap. unfold SC.ret in Hmap. inversion Hmap; subst.
        reflexivity.
      - simpl in Hmap.
        eapply sec_bind_inv in Hmap as (ety & st1 & Hhd & Hmap).
        eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
        unfold SC.option_to_sec in Hhd.
        destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:Heq;
          try discriminate.
        inversion Hhd; subst ety st1.
        specialize (IH _ _ _ st0 Htl).
        unfold SC.ret in Hret. inversion Hret; subst tys st'.
        cbn [SC.mmap].
        cbn [SC.option_to_sec].
        rewrite Heq.
        unfold SC.bind, SC.ret.
        simpl.
        destruct
          (SC.mmap
             (fun e0 : exp => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e0))
             es st0)
          as [[tys0 st0']|err] eqn:Hm.
        + inversion IH; subst. reflexivity.
        + discriminate.
    Qed.

    (** One non-reset call input is low-equal at a chosen instant.

        Relation to the paper:
        in the [EqApp] case, the first reusable semantic step is to show that
        one low callee input variable receives the same value in both runs at a
        fixed instant. This isolates the transport from low-equal caller free
        variables, through actual-expression semantics, into the callee input
        history. *)
    Lemma eqapp_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
             k ii y ity e ety,
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls'
             k ii y ity e ety
             Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hnthv in Hnthvin.
      inversion Hnthvin; subst vin; clear Hnthvin.
      rewrite Hnthv' in Hnthvin'.
      inversion Hnthvin'; subst vin'; clear Hnthvin'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** Transport one low callee output back to the caller-defined variable.

        Relation to the paper:
        after the recursive call theorem gives low-equivalence on the callee
        outputs, the [EqApp] case still has to reconnect that fact to the
        caller-visible variable defined by the call tuple. This is the
        position-based semantic transport step for one output slot. *)
    Lemma eqapp_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    (** One low reset-call input is low-equal at a chosen instant.

        Relation to the paper:
        this is the reset-aware companion of the plain [EqApp] input transport
        step. The actual expressions are still evaluated in the caller, but
        the callee sees them through the masked reset stream. The proof
        therefore adds exactly one extra bridge: at the current reset segment,
        the masked tuple position agrees with the underlying actual-argument
        tuple position. *)
    Lemma eqapp_reset_input_var_low_eq_pointwise:
      forall ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error (map fst callee.(n_in)) ii = Some y ->
        Env.find y ty_env_c = Some ity ->
        nth_error callee_sig.(s_in) ii = Some ity ->
        nth_error inptyp ii = Some ety ->
        nth_error exps ii = Some e ->
        SECCETYPING.assign_exp_type ty_env e = Some ety ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        low_var ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp) t y ->
        (forall z, Is_free_in_exp z e -> Env.find z (H k) = Env.find z (H' k)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        Env.find y (Hc k) = Env.find y (Hc' k).
    Proof.
      intros ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             k ii y ity e ety
             Hkr Hkr' Hnthy Hfindy Hnthsig Hnthinpty Hnthe Heqexp
             Hinst_in_eq Hlowy Hfree_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'.
      assert (Hety_low : SecT.hm_ext dlt ety ⊑ t).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthinpty.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthinpty in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      specialize (Hsem_exps k).
      specialize (Hsem_exps' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H k))
           exps (ls k) ii e
           Hsem_exps Hnthe)
        as (v & Hnthv & Hsemv).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_exp_instant (bk k) (H' k))
           exps (ls' k) ii e
           Hsem_exps' Hnthe)
        as (v' & Hnthv' & Hsemv').
      assert (Hsemv_sw : sem_exp_instant (bk k) (H' k) e v).
      {
        apply
          (proj1
             (sem_exp_instant_switch_env
                (bk k) (H k) (H' k) e v Hfree_eq)).
        exact Hsemv.
      }
      assert (Hv_eq : v = v').
      {
        eapply sem_exp_instant_det; eauto.
      }
      specialize (Hsem_vars_in_c k).
      specialize (Hsem_vars_in_c' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst callee.(n_in)) (mask kr rs ls k) ii y
           Hsem_vars_in_c Hnthy)
        as (vin & Hnthvin & Hsem_y).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst callee.(n_in)) (mask kr' rs' ls' k) ii y
           Hsem_vars_in_c' Hnthy)
        as (vin' & Hnthvin' & Hsem_y').
      rewrite Hkr in Hnthvin.
      rewrite Hkr' in Hnthvin'.
      pose proof
        (nth_error_mask_count_self rs ls k ii vin Hnthvin)
        as Hnthvin0.
      pose proof
        (nth_error_mask_count_self rs' ls' k ii vin' Hnthvin')
        as Hnthvin0'.
      rewrite Hnthv in Hnthvin0.
      inversion Hnthvin0; subst vin; clear Hnthvin0.
      rewrite Hnthv' in Hnthvin0'.
      inversion Hnthvin0'; subst vin'; clear Hnthvin0'.
      unfold sem_var_instant in Hsem_y, Hsem_y'.
      rewrite Hsem_y, Hsem_y'.
      exact (f_equal (@Some value) Hv_eq).
    Qed.

    (** Transport one low reset-call output back to the caller-defined variable.

        Relation to the paper:
        this is the reset-aware output-slot transport for [EqApp]. The
        recursive theorem gives low-equivalence on the callee outputs under
        the masked run, and this lemma reconnects that masked equality to the
        caller-visible output variable at the same tuple position. *)
    Lemma eqapp_reset_output_transport_pointwise:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo,
        kr = count rs k ->
        kr' = count rs' k ->
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) (mask kr rs ys) ->
        sem_vars Hc' (map fst callee.(n_out)) (mask kr' rs' ys') ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        Env.find x (H k) = Env.find x (H' k).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' rs rs' kr kr' k i x yo
             Hkr Hkr' Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'.
      assert (Hk : k <= k) by apply le_n.
      specialize (Hlowout k Hk).
      assert (Hin_yo : In yo (map fst callee.(n_out))).
      { eapply SecT.nth_error_In_local; exact Hnthyo. }
      specialize (Hlowout yo Hin_yo Hlowyo).
      specialize (Hsem_vars_callee_out k).
      specialize (Hsem_vars_callee_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc k))
           (map fst (n_out callee)) (mask kr rs ys k) i yo
           Hsem_vars_callee_out Hnthyo)
        as (vo & Hnthvo & Hsemyo).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (Hc' k))
           (map fst (n_out callee)) (mask kr' rs' ys' k) i yo
           Hsem_vars_callee_out' Hnthyo)
        as (vo' & Hnthvo' & Hsemyo').
      rewrite Hkr in Hnthvo.
      rewrite Hkr' in Hnthvo'.
      pose proof
        (nth_error_mask_count_self rs ys k i vo Hnthvo)
        as Hnthvo0.
      pose proof
        (nth_error_mask_count_self rs' ys' k i vo' Hnthvo')
        as Hnthvo0'.
      specialize (Hsem_vars_out k).
      specialize (Hsem_vars_out' k).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H k))
           xs (ys k) i x
           Hsem_vars_out Hnthx)
        as (vx & Hnthvx & Hsemx).
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (sem_var_instant (H' k))
           xs (ys' k) i x
           Hsem_vars_out' Hnthx)
        as (vx' & Hnthvx' & Hsemx').
      rewrite Hnthvo0 in Hnthvx.
      inversion Hnthvx; subst vx; clear Hnthvx.
      rewrite Hnthvo0' in Hnthvx'.
      inversion Hnthvx'; subst vx'; clear Hnthvx'.
      unfold sem_var_instant in Hsemyo, Hsemyo', Hsemx, Hsemx'.
      rewrite Hsemx, Hsemx'.
      rewrite <- Hsemyo, <- Hsemyo'.
      exact Hlowout.
    Qed.

    (** Recover the symbolic type at one position of a [get_mappings] result.

        Relation to the paper:
        call equations define several caller variables at once.  The
        noninterference proof needs to relate one chosen caller variable [x]
        with the matching symbolic output type in [outtyp].  This lemma is the
        finite-list position bridge for that lookup. *)
    Lemma get_mappings_nth_error_inv:
      forall xs ty_env tys i x,
        get_mappings xs ty_env = Some tys ->
        nth_error xs i = Some x ->
        exists ty,
          nth_error tys i = Some ty
          /\ Env.find x ty_env = Some ty.
    Proof.
      induction xs as [|y ys IH]; intros ty_env tys i x Hmap Hnth.
      - destruct i; inversion Hnth.
      - simpl in Hmap.
        destruct (Env.find y ty_env) as [yty|] eqn:Hyfind; try discriminate.
        destruct (get_mappings ys ty_env) as [tys'|] eqn:Hys; try discriminate.
        inversion Hmap; subst tys.
        destruct i as [|i].
        + simpl in Hnth. inversion Hnth; subst x.
          exists yty. split; [reflexivity|exact Hyfind].
        + simpl in Hnth.
          specialize (IH ty_env tys' i x Hys Hnth) as (ty & Hnthty & Hfindty).
          exists ty.
          split.
          * exact Hnthty.
          * exact Hfindty.
    Qed.

    (** Successful [get_mappings] preserves list length.

        Relation to the paper:
        call proofs repeatedly move between the syntactic output tuple, its
        generated symbolic mapping, and semantic tuples.  This is the basic
        length bridge behind those position arguments. *)
    Lemma get_mappings_length:
      forall xs ty_env tys,
        get_mappings xs ty_env = Some tys ->
        List.length xs = List.length tys.
    Proof.
      induction xs as [|x xs IH]; intros ty_env tys Hmap.
      - simpl in Hmap. inversion Hmap. reflexivity.
      - simpl in Hmap.
        destruct (Env.find x ty_env) as [xty|] eqn:Hfind; try discriminate.
        destruct (get_mappings xs ty_env) as [tys'|] eqn:Htl; try discriminate.
        inversion Hmap; subst tys.
        simpl. f_equal.
        eapply IH; eauto.
    Qed.

    (** Prefix low-equivalence on plain call inputs from caller-side argument equality.

        Relation to the paper:
        recursive noninterference for a plain [EqApp] call is driven by
        low-equivalence of the callee inputs on the whole prefix considered so
        far. This lemma packages that bridge directly: if every actual
        argument is semantically equal across the two caller runs on the
        prefix, then the instantiated callee input history is low-equivalent
        on that same prefix. *)
    Lemma eqapp_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k,
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps ls ls' k
             Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthinpty & Heqexp).
      eapply
        (eqapp_input_var_low_eq_pointwise
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt rstty ckty t
           bk H H' Hc Hc' exps ls ls'
           j ii y ity e ety); eauto.
      intros z Hz.
      eapply Hfree_eqs.
      - eapply Exists_exists.
        exists e.
        split.
        + eapply nth_error_In.
          exact Hnthe.
        + exact Hz.
      - exact Hj.
    Qed.

    (** Prefix low-equivalence on reset-call inputs for one fixed reset segment.

        Relation to the paper:
        the recursive reset-call theorem is applied to one concrete reset
        segment [kr = count rs k].  This lemma packages the corresponding
        caller-to-callee input transport on the whole prefix: inside the
        active segment the mask is transparent and the proof reduces to the
        ordinary actual-expression argument equality, while outside that
        segment both masked tuples are uniformly absent. *)
    Lemma eqapp_reset_inputs_low_eq_upto:
      forall ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k,
        kr = count rs k ->
        kr' = count rs' k ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt ty)
          callee_sig.(s_in) inptyp ->
        (forall z,
            Exists (Is_free_in_exp z) exps ->
            forall j, j <= k -> Env.find z (H j) = Env.find z (H' j)) ->
        (forall j, j <= k -> count rs j = count rs' j) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt callee_sig inptyp ckty rstty outtyp)
          t (map fst callee.(n_in)) Hc Hc' k.
    Proof.
      intros ty_env ty_env_c callee callee_sig inp_c
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls' k
             Hkr Hkr' Hsig_in Hinp_c Hforinp Hinst_in_eq Hfree_eqs Hcount_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof (get_mappings_from_node_eq _ _ _ _ Hinp_c) as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthinpty & Heqexp).
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        eapply
          (eqapp_reset_input_var_low_eq_pointwise
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt rstty ckty t
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety); eauto.
        intros z Hz.
        eapply Hfree_eqs.
        + eapply Exists_exists.
          exists e.
          split.
          * eapply nth_error_In.
            exact Hnthe.
          * exact Hz.
        + exact Hj.
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq k (le_n k)) as Hcntk.
          apply Hopaque.
          rewrite Hcntj.
          rewrite Heq.
          rewrite Hkr'.
          rewrite <- Hcntk.
          symmetry.
          exact Hkr.
        }
        specialize (Hsem_vars_in_c j).
        specialize (Hsem_vars_in_c' j).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc j))
             (map fst callee.(n_in)) (mask kr rs ls j) ii y
             Hsem_vars_in_c Hnthy)
          as (vin & Hnthvin & Hsem_y).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc' j))
             (map fst callee.(n_in)) (mask kr' rs' ls' j) ii y
             Hsem_vars_in_c' Hnthy)
          as (vin' & Hnthvin' & Hsem_y').
        rewrite (mask_opaque ls kr rs j Hopaque) in Hnthvin.
        rewrite (mask_opaque ls' kr' rs' j Hopaque') in Hnthvin'.
        pose proof (nth_error_all_absent_absent _ (ls 0) _ _ Hnthvin) as Hvin.
        pose proof (nth_error_all_absent_absent _ (ls' 0) _ _ Hnthvin') as Hvin'.
        unfold sem_var_instant in Hsem_y, Hsem_y'.
        subst vin vin'.
        rewrite Hsem_y, Hsem_y'.
        reflexivity.
    Qed.

    (** Prefix low-equivalence on plain call outputs transported back to the caller.

        Relation to the paper:
        after the recursive callee theorem establishes prefix low-equivalence
        on the callee outputs, the caller proof still has to reconnect that
        prefix fact to the caller-defined output variable at the matching
        tuple position. This is the prefix-level version of that transport. *)
    Lemma eqapp_outputs_low_eq_upto:
      forall ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo,
        nth_error xs i = Some x ->
        nth_error (map fst callee.(n_out)) i = Some yo ->
        low_var ty_env_c dlt_raw_c t yo ->
        history_low_eq_upto ty_env_c dlt_raw_c t (map fst callee.(n_out)) Hc Hc' k ->
        sem_vars Hc (map fst callee.(n_out)) ys ->
        sem_vars Hc' (map fst callee.(n_out)) ys' ->
        sem_vars H xs ys ->
        sem_vars H' xs ys' ->
        forall j, j <= k -> Env.find x (H j) = Env.find x (H' j).
    Proof.
      intros ty_env_c dlt_raw_c t
             H H' Hc Hc' callee
             xs ys ys' k i x yo
             Hnthx Hnthyo Hlowyo Hlowout
             Hsem_vars_callee_out Hsem_vars_callee_out'
             Hsem_vars_out Hsem_vars_out'
             j Hj.
      eapply
        (eqapp_output_transport_pointwise
           ty_env_c dlt_raw_c t
           H H' Hc Hc' callee
           xs ys ys' j i x yo); eauto.
      eapply history_low_eq_upto_monotone; eauto.
    Qed.

    (** Symbolic types of defined caller variables come from outputs or locals.

        Relation to the paper:
        in a call equation, the generated symbolic output tuple [outtyp]
        belongs to the current node interface of defined variables.  The
        recursive call proof uses this helper to reclassify one chosen caller
        output type as coming from the current node outputs or locals, which
        is exactly the scope later shown fresh from the callee signature. *)
    Lemma defined_var_type_in_out_or_locals:
      forall n ty_env out locals x ty,
        Env.find x ty_env = Some ty ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In x (vars_defined n.(n_eqs)) ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals x ty Hfind Hout Hlocals Hdef.
      assert (Hin_vo : In x (map fst (n.(n_vars) ++ n.(n_out)))).
      {
        eapply Permutation_in; [apply n.(n_defd)|exact Hdef].
      }
      rewrite map_app, in_app_iff in Hin_vo.
      destruct Hin_vo as [Hin_local|Hin_out].
      - apply in_map_iff in Hin_local as ((xlocal, alocal) & Heq & Hin_local).
        simpl in Heq. subst xlocal.
        apply In_InMembers in Hin_local.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_local Hlocals)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. right. exact Hin'.
      - apply in_map_iff in Hin_out as ((xout, aout) & Heq & Hin_out).
        simpl in Heq. subst xout.
        apply In_InMembers in Hin_out.
        destruct (get_mappings_from_node_inmembers _ _ _ _ _ Hin_out Hout)
          as (ty' & Hfind' & Hin').
        rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. clear Hfind'.
        apply in_or_app. left. exact Hin'.
    Qed.

    (** Two distinct named nodes appear in one linear order in the program list.

        Relation to the paper:
        the call-site freshness argument only needs the source program order
        induced by the generated naming pass.  This lemma packages the pure
        list decomposition step under the standard [NoDup] node-name
        hypothesis. *)
    Lemma find_nodes_linear_order:
      forall n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node n1.(n_name) all_nodes = Some n1 ->
        find_node n2.(n_name) all_nodes = Some n2 ->
        n1.(n_name) <> n2.(n_name) ->
        (exists prefix mid suffix,
            all_nodes = prefix ++ n1 :: mid ++ n2 :: suffix)
        \/ (exists prefix mid suffix,
            all_nodes = prefix ++ n2 :: mid ++ n1 :: suffix).
    Proof.
      intros n1 n2 Hndnames Hfind1 Hfind2 Hneq.
      pose proof (find_node_In _ _ _ Hfind1) as [_ Hin1].
      pose proof (find_node_In _ _ _ Hfind2) as [_ Hin2].
      apply in_split in Hin1 as (prefix1 & suffix1 & Hall1).
      subst all_nodes.
      simpl in Hin2.
      rewrite in_app_iff in Hin2.
      simpl in Hin2.
      destruct Hin2 as [Hin2|[Heq12|Hin2]].
      - apply in_split in Hin2 as (prefix2 & suffix2 & Hprefix2).
        right.
        exists prefix2, suffix2, suffix1.
        rewrite Hprefix2. repeat rewrite <- app_assoc. reflexivity.
      - subst n2.
        exfalso. apply Hneq. reflexivity.
      - apply in_split in Hin2 as (mid & suffix2 & Hsuffix2).
        left.
        exists prefix1, mid, suffix2.
        rewrite Hsuffix2. repeat rewrite <- app_assoc. reflexivity.
    Qed.

    (** Unique lookup of one source node under unique node names.

        Relation to the paper:
        recursive call proofs extract one semantic node witness from each run.
        Under the standard source assumption that node names are unique, both
        witnesses for the same callee name must coincide.  This is the exact
        source-side canonicalisation step used before applying the recursive
        raw-output theorem. *)
    Lemma find_node_unique_nodup:
      forall f n1 n2,
        NoDup (map n_name all_nodes) ->
        find_node f all_nodes = Some n1 ->
        find_node f all_nodes = Some n2 ->
        n1 = n2.
    Proof.
      intros f n1 n2 _ Hfind1 Hfind2.
      revert f n1 n2 Hfind1 Hfind2.
      induction all_nodes as [|nd nds IH]; intros f n1 n2 Hfind1 Hfind2.
      - discriminate.
      - simpl in Hfind1, Hfind2.
        destruct (ident_eqb nd.(n_name) f) eqn:Hname.
        + inversion Hfind1; inversion Hfind2; subst; reflexivity.
        + eapply IH; eauto.
    Qed.

    (** Ordered source nodes already have unique names.

        Relation to the paper:
        the recursive source proof is naturally stated over [Ordered_nodes].
        Whenever the naming-layer helpers need explicit uniqueness of source
        node names, this lemma is the bridge back to the [NoDup] list form. *)
    Lemma Ordered_nodes_nodup_names:
      forall nodes,
        Ordered_nodes nodes ->
        NoDup (map n_name nodes).
    Proof.
      intros nodes Hord.
      induction Hord as [|nd nds Hord IH Hcalls Hfresh].
      - constructor.
      - simpl. constructor.
        + intro Hin.
          apply in_map_iff in Hin as (nd' & Heq & Hin').
          rewrite Forall_forall in Hfresh.
          specialize (Hfresh _ Hin').
          simpl in Heq.
          apply Hfresh.
          symmetry.
          exact Heq.
        + exact IH.
    Qed.

    (** Generated node interfaces have pairwise distinct visible symbolic
        identifiers.

        Relation to the paper:
        recursive call proofs instantiate input/output substitution lemmas
        from [SIFSignature], which require [NoDup] on the callee visible
        signature scope.  For generated NLustre signatures this is a pure
        naming-side fact, recovered here directly from the successful
        node-scoped environment generation. *)
    Lemma generated_sig_scope_nodup_scoped_env:
      forall n ty_env clk_id rst_id clk_type rst_type inp out,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        find_node_env n.(n_name) envs = Some ty_env ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node n.(n_in) ty_env = Some inp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        NoDup
          (SIG.signature_scope
             {| s_name := n.(n_name);
                s_in := inp;
                s_out := out;
                s_reset := rst_type;
                s_clk := clk_type;
                s_constraints := nil |}).
    Proof.
      intros n ty_env clk_id rst_id clk_type rst_type inp out
             Henvsgen Hfindnode Hfindenv Haux Hclk Hrst Hinp Hout.
      pose proof (find_node_In _ _ _ Hfindnode) as (_ & Hinnode).
      apply in_split in Hinnode as (prefix & suffix & Hall).
      subst all_nodes.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           (prefix ++ n :: suffix) (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st']|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref & aux_pref & st_pref
            & local_env & rec & st_local
            & envs_cur & st_cur
            & Hpref & Hlocal & Hins & Htail);
        eauto.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof
          (NAMEGEN.generate_node_scoped_env'_preserves_find
             _ _ _ _ _ _ _ _ _ Htail Hfind_cur)
          as Hfind_final.
        exact Hfind_final.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        pose proof
          (NAMEGEN.fresh_insert_node_env_finds_new
             _ _ _ _ _ _ Hins) as Hfind_cur.
        pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrec_name.
        assert (Haux_cur : get_node_aux n.(n_name) (rec :: aux_pref) = Some (rec.(nclk), rec.(nrst))).
        {
          unfold get_node_aux.
          simpl.
          rewrite <- Hrec_name.
          rewrite ident_eqb_refl.
          reflexivity.
        }
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
      }
      rewrite Hfindenv in Hfindlocal.
      inversion Hfindlocal; subst local_env.
      rewrite Haux in Hauxlocal.
      inversion Hauxlocal; subst clk_id rst_id.
      eapply SECNLUSTYPINGCORRECTNESS.generate_node_sig_scope_nodup_from_local_env;
        eauto.
    Qed.

    (** Fresh insertion into the node-scoped naming table does not advance
        the name-generation state.

        Relation to the paper:
        the node-scoped naming pass only uses the global state when it
        allocates fresh security identifiers inside one node-local
        environment.  Inserting that finished local env into the outer
        node-indexed table is pure bookkeeping.  The later cross-node
        separation proof relies on this to compare the numeric ranges of two
        generated node scopes precisely. *)
    Lemma fresh_insert_node_env_state:
      forall envs0 name local_env st envs' st',
        NAMEGEN.fresh_insert_node_env envs0 name local_env st = OK (envs', st') ->
        st' = st.
    Proof.
      intros envs0 name local_env st envs' st' Hins.
      unfold NAMEGEN.fresh_insert_node_env in Hins.
      destruct (Env.mem name envs0) eqn:Hmem; try discriminate.
      unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
      inversion Hins; reflexivity.
    Qed.

    (** Freshness from caller-upper versus callee-lower bounds.

        Relation to the paper:
        one direct call proof case needs the opposite orientation from the
        standard accumulator freshness theorem.  If every symbolic identifier
        in the current caller scope is strictly below some pivot [st], and
        every visible identifier in the callee signature is at least [st],
        then the two scopes are disjoint. *)
    Lemma scope_fresh_from_upper_lower_bounds:
      forall scope sig st,
        (forall ty,
            In ty scope ->
            exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive) ->
        (forall ty,
            In ty (signature_scope sig) ->
            exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive) ->
        SIG.scope_fresh scope sig.
    Proof.
      intros scope sig st Hupper Hlower ty Hinscope Hinsig.
      destruct (Hupper ty Hinscope) as (n1 & Hty1 & Hlt1).
      destruct (Hlower ty Hinsig) as (n2 & Hty2 & Hle2).
      rewrite Hty1 in Hty2.
      apply gensym_injective in Hty2 as [_ Heq]. subst n2.
      eapply Pos.lt_irrefl.
      eapply Pos.lt_le_trans; eauto.
    Qed.

    (** Every mapped call output type belongs to the current caller scope.

        Relation to the paper:
        the NLustre call proof needs the symbolic output tuple produced for a
        call equation to be recognised as part of the current caller-visible
        scope.  This is the source-side bridge from the tuple mapping
        [get_mappings xs ty_env] back to the generated raw variable scope of
        the surrounding node. *)
    Lemma eqapp_outtyp_in_out_or_locals:
      forall n ty_env out locals xs ck f exps r outtyp ty,
        In (EqApp xs ck f exps r) n.(n_eqs) ->
        get_mappings xs ty_env = Some outtyp ->
        get_mappings_from_node n.(n_out) ty_env = Some out ->
        get_mappings_from_node n.(n_vars) ty_env = Some locals ->
        In ty outtyp ->
        In ty (out ++ locals).
    Proof.
      intros n ty_env out locals xs ck f exps r outtyp ty
             Heqin Hmap Hout Hlocals Hin.
      destruct (get_mappings_In _ _ _ _ Hmap Hin) as (x & Hinx & Hfindx).
      assert (Hxdef : In x (vars_defined n.(n_eqs))).
      {
        unfold vars_defined.
        apply in_flat_map.
        exists (EqApp xs ck f exps r).
        split; [exact Heqin|exact Hinx].
      }
      eapply defined_var_type_in_out_or_locals; eauto.
    Qed.

    (** Caller scope freshness against a distinct generated callee signature.

        Relation to the paper:
        ordinary and resettable call proofs both instantiate the callee
        signature with symbolic types coming from the current caller node.
        To use the standard signature substitution lemmas, those caller-side
        identifiers must be disjoint from the visible callee signature scope.
        In the node-scoped naming discipline this follows purely from the
        relative generation order of the two nodes: two distinct node-local
        scopes live in disjoint numeric [sec] ranges. *)
    Lemma generated_caller_scope_fresh_scoped_env:
      forall caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        NoDup (map n_name all_nodes) ->
        find_node caller.(n_name) all_nodes = Some caller ->
        find_node callee.(n_name) all_nodes = Some callee ->
        caller.(n_name) <> callee.(n_name) ->
        find_node_env caller.(n_name) envs = Some caller_env ->
        find_node_env callee.(n_name) envs = Some callee_env ->
        SECNLUSTYPING.generate_node_sig_scoped_env G callee envs aux_names = OK callee_sig ->
        get_node_aux caller.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id caller_env = Some clk_type ->
        Env.find rst_id caller_env = Some rst_type ->
        get_mappings_from_node caller.(n_in) caller_env = Some inp ->
        get_mappings_from_node caller.(n_out) caller_env = Some out ->
        get_mappings_from_node caller.(n_vars) caller_env = Some locals ->
        SIG.scope_fresh
          (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
          callee_sig.
    Proof.
      intros caller callee
             caller_env callee_env callee_sig
             clk_id rst_id clk_type rst_type inp out locals
             Henvsgen Hndnames Hfindcaller Hfindcallee Hneq
             Hfindenvcaller Hfindenvcallee Hsiggencallee
             Hauxcaller Hclkcaller Hrstcaller
             Hinpcaller Houtcaller Hlocalscaller.
      pose proof
        (find_nodes_linear_order
           caller callee Hndnames Hfindcaller Hfindcallee Hneq)
        as Hord.
      unfold NAMEGEN.generate_node_scoped_env in Henvsgen.
      destruct
        (NAMEGEN.generate_node_scoped_env'
           all_nodes (Env.empty _) [] NAMEGEN.init_state)
        as [[[envs' aux'] st_final]|] eqn:Hrun;
        try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hsiggencallee.
      rewrite Hfindenvcallee in Hsiggencallee.
      destruct Hord as
          [(prefix & mid & suffix & Hall)
          |(prefix & mid & suffix & Hall)];
        subst all_nodes.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_call) as Hcall_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_call Hfind_call_cur)
            as Hfind_call_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_call Hfind_call_pref)
            as Hfind_call_after_cal.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_call_after_cal)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_call Hfind_cal_cur)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_upper :
                  forall ty,
                    In ty (inp ++ out ++ locals ++ clk_type :: rst_type :: nil) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (m < st_pref_call)%positive).
        {
          intros ty Hin.
          destruct
            (node_scope_upper_bounded_from_local_env
               caller st_pref_cal local_env_cal rec_cal st_local_cal
               clk_id rst_id clk_type rst_type inp out locals ty
               Hlocal_cal Hclkcaller Hrstcaller Hinpcaller Houtcaller Hlocalscaller Hin)
            as (m & Hm & Hlt).
          exists m. split; auto.
          eapply Pos.lt_le_trans; eauto.
          rewrite <- Hcur_cal. exact Hcall_mid_le.
        }
        assert (Hcallee_lower :
                  forall ty,
                    In ty (signature_scope callee_sig) ->
                    exists m, ty = Ids.gensym Ids.sec m /\ (st_pref_call <= m)%positive).
        {
          intros ty Hin.
          destruct
            (SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_lower_bound_from_local_env
               G callee local_env_call aux_names callee_sig
               st_pref_call rec_call st_local_call ty
               Hlocal_call Hsiggencallee Hin)
            as (m & Hm & Hlo).
          exists m. split; auto.
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|].
          eapply Pos.le_trans; [apply Pos.lt_le_incl, Pos.lt_succ_diag_r|exact Hlo].
        }
        eapply scope_fresh_from_upper_lower_bounds; eauto.
      - edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_call & aux_pref_call & st_pref_call
              & local_env_call & rec_call & st_local_call
              & envs_cur_call & st_cur_call
              & Hpref_call & Hlocal_call & Hins_call & Htail_call);
          eauto.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref_cal & aux_pref_cal & st_pref_cal
              & local_env_cal & rec_cal & st_local_cal
              & envs_cur_cal & st_cur_cal
              & Hpref_cal & Hlocal_cal & Hins_cal & Htail_cal);
          eauto.
        assert (Hcur_call : st_cur_call = st_local_call).
        { eapply fresh_insert_node_env_state; eauto. }
        assert (Hcur_cal : st_cur_cal = st_local_cal).
        { eapply fresh_insert_node_env_state; eauto. }
        pose proof
          (NAMEGEN.generate_node_scoped_env'_state_monotone
             _ _ _ _ _ _ _ Hpref_cal) as Hcal_mid_le.
        assert (Hcaller_env_local : local_env_cal = caller_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_cal) as Hfind_call_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_call_cur)
            as Hfind_call_envs.
          rewrite Hfindenvcaller in Hfind_call_envs.
          inversion Hfind_call_envs; reflexivity.
        }
        assert (Hcallee_env_local : local_env_call = callee_env).
        {
          pose proof
            (NAMEGEN.fresh_insert_node_env_finds_new
               _ _ _ _ _ _ Hins_call) as Hfind_cal_cur.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Hpref_cal Hfind_cal_cur)
            as Hfind_cal_pref.
          pose proof
            (NAMEGEN.fresh_insert_node_env_preserves_find
               _ _ _ _ _ _ _ _ Hins_cal Hfind_cal_pref)
            as Hfind_cal_after_call.
          pose proof
            (NAMEGEN.generate_node_scoped_env'_preserves_find
               _ _ _ _ _ _ _ _ _ Htail_cal Hfind_cal_after_call)
            as Hfind_cal_envs.
          rewrite Hfindenvcallee in Hfind_cal_envs.
          inversion Hfind_cal_envs; reflexivity.
        }
        subst caller_env callee_env.
        assert (Hcaller_lower :
                  SIG.scope_lower_bounded
                    (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                    st_pref_cal).
        {
          eapply SECNLUSTYPINGCORRECTNESS.node_scope_lower_bounded_from_local_env; eauto.
        }
        assert (Hcallee_upper0 :
                  SIG.signature_scope_bounded_above callee_sig st_local_call).
        {
          intros ty Hin.
          eapply SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_upper_bound_from_local_env
            with (rec := rec_call) (st := st_pref_call) (st' := st_local_call)
                 (aux_names := aux_names); eauto.
        }
        assert (Hcallee_upper :
                  SIG.signature_scope_bounded_above callee_sig st_pref_cal).
        {
          eapply SIG.signature_scope_bounded_above_monotone; eauto.
          rewrite <- Hcur_call. exact Hcal_mid_le.
        }
        eapply SIG.scope_fresh_from_bounds; eauto.
    Qed.

    (** Invert the generated raw block for one [EqDef].

        Relation to the paper:
        this exposes the exact symbolic typing data behind the simple
        combinational case, so the semantic branch can invoke the already
        proved simple-security lemmas without re-running ad hoc monadic
        analysis. *)
    Lemma generate_eqdef_constraint_inv:
      forall ty_env base_ty rst_ty x ck ce cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqDef x ck ce) st =
        OK (cns, st') ->
        exists ckty cety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ cety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_cexp_type ty_env ce = Some cety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck ce cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (cety & st2 & Hce & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in Hce.
      destruct (SECCETYPING.assign_cexp_type ty_env ce) as [cety'|] eqn:Hce';
        try discriminate.
      inversion Hce; subst cety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', cety', xty'.
      repeat split; reflexivity.
    Qed.

    (** Invert the generated raw block for one [EqFby].

        Relation to the paper:
        this is the delay-side counterpart of
        [generate_eqdef_constraint_inv].  It exposes the exact symbolic
        clock, source-expression, and target-variable types used by the raw
        typing constraint. *)
    Lemma generate_eqfby_constraint_inv:
      forall ty_env base_ty rst_ty x ck c0 e cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty (EqFby x ck c0 e) st =
        OK (cns, st') ->
        exists ckty ety xty,
          cns = [((([rst_ty] ⊔ ckty) ⊔ ety), [xty])]
          /\ SECCETYPING.assign_clk_type ty_env base_ty ck = Some ckty
          /\ SECCETYPING.assign_exp_type ty_env e = Some ety
          /\ Env.find x ty_env = Some xty.
    Proof.
      intros ty_env base_ty rst_ty x ck c0 e cns st st' Hgen.
      simpl in Hgen.
      eapply sec_bind_inv in Hgen as (ckty & st1 & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (ety & st2 & He & Hgen).
      eapply sec_bind_inv in Hgen as (xty & st3 & Hfind & Hret).
      unfold SC.option_to_sec in Hck.
      destruct (SECCETYPING.assign_clk_type ty_env base_ty ck) as [ckty'|] eqn:Hck';
        try discriminate.
      inversion Hck; subst ckty st1.
      unfold SC.option_to_sec in He.
      destruct (SECCETYPING.assign_exp_type ty_env e) as [ety'|] eqn:He';
        try discriminate.
      inversion He; subst ety st2.
      unfold find_env in Hfind.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfind'; try discriminate.
      unfold ret in Hfind. inversion Hfind; subst xty st3.
      unfold ret in Hret. inversion Hret; subst cns st'.
      exists ckty', ety', xty'.
      repeat split; reflexivity.
    Qed.

    (** Invert the generated raw block for one non-reset node call.

        Relation to the paper:
        the call case is the first point where the local NLustre proof stops
        working directly on simple expressions and must recover the full
        call-site instantiation data used to build the callee constraints. *)
    Lemma generate_eqapp_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps None) st = OK (cns, st') ->
        exists callee_sig ckty inptyp outtyp st_clk st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_clk = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty [rst_ty] outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      exists callee_sig, ckty, inptyp, (xty' :: tys'), st_clk, st_inp.
      repeat split; auto.
    Qed.

    (** Invert the generated raw block for one resettable node call.

        Relation to the paper:
        this is the reset-aware companion of
        [generate_eqapp_constraint_inv].  It exposes the reset guard typing
        and the instantiated reset type passed to the callee signature. *)
    Lemma generate_eqreset_constraint_inv:
      forall ty_env base_ty rst_ty x xs ck f exps r ckr cns st st',
        SECNLUSTYPING.generate_eqn_constraint G ty_env base_ty rst_ty
          (EqApp (x :: xs) ck f exps (Some (r, ckr))) st = OK (cns, st') ->
        exists callee_sig ckty rty rstty inptyp outtyp st_clk st_rst st_inp,
          SIG.find_signature f G = Some callee_sig
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env base_ty ck) st = OK (ckty, st_clk)
          /\ Env.find r ty_env = Some rty
          /\ SC.option_to_sec
               (SECCETYPING.assign_clk_type ty_env rst_ty ckr) st_clk =
               OK (rstty, st_rst)
          /\ SC.mmap
               (fun e => SC.option_to_sec (SECCETYPING.assign_exp_type ty_env e))
               exps st_rst = OK (inptyp, st_inp)
          /\ get_mappings (x :: xs) ty_env = Some outtyp
          /\ SIG.generate_constraints callee_sig inptyp ckty ([rty] ⊔ rstty) outtyp st_inp =
               OK (cns, st').
    Proof.
      intros ty_env base_ty rst_ty x xs ck f exps r ckr cns st st' Hgen.
      simpl in Hgen.
      destruct (SIG.find_signature f G) as [callee_sig|] eqn:Hfindsig;
        try discriminate.
      eapply sec_bind_inv in Hgen as (ckty & st_clk & Hck & Hgen).
      eapply sec_bind_inv in Hgen as (rty & st_rty & Hrty & Hgen).
      eapply sec_bind_inv in Hgen as (rstty & st_rst & Hrst & Hgen).
      eapply sec_bind_inv in Hgen as (inptyp & st_inp & Hinp & Hgen).
      eapply sec_bind_inv in Hgen as (outtyp & st_out & Hout & Hgen).
      simpl in Hout.
      eapply sec_bind_inv in Hout as (xty & st_x & Hfindx & Hout).
      eapply sec_bind_inv in Hout as (tys' & st_tl & Htl & Hret).
      unfold SC.find_env in Hfindx.
      destruct (Env.find x ty_env) as [xty'|] eqn:Hfindx'; try discriminate.
      unfold SC.ret in Hfindx. inversion Hfindx; subst xty st_x.
      specialize (mmap_find_env_inv ty_env xs tys' st_inp st_tl Htl) as [Hst_tl Hmaps_tl].
      subst st_tl.
      unfold SC.ret in Hret. inversion Hret; subst outtyp st_out.
      assert (Hmaps_out : get_mappings (x :: xs) ty_env = Some (xty' :: tys')).
      { simpl. rewrite Hfindx', Hmaps_tl. reflexivity. }
      unfold SC.find_env in Hrty.
      destruct (Env.find r ty_env) as [rty'|] eqn:Hrfind; try discriminate.
      unfold SC.ret in Hrty. inversion Hrty; subst rty st_rty.
      exists callee_sig, ckty, rty', rstty, inptyp, (xty' :: tys'), st_clk, st_rst, st_inp.
      repeat split; auto.
    Qed.

    (** Recover the interface lengths of an instantiated call block.

        Relation to the paper:
        call-site transport lemmas use positional correspondence between the
        stored signature interface and the caller actuals.  Those list-length
        equalities are already forced by [generate_constraints], and this
        lemma exposes them once so the call proof can reuse them directly. *)
    Lemma generate_constraints_lengths:
      forall sig inp clk rst out cns st st',
        SIG.generate_constraints sig inp clk rst out st = OK (cns, st') ->
        List.length sig.(s_in) = List.length inp
        /\ List.length sig.(s_out) = List.length out.
    Proof.
      intros sig inp clk rst out cns st st' Hgen.
      unfold SIG.generate_constraints in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
      eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
      eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hgen).
      split.
      - eapply SIGPROOFS.subst_constraints_inp_map_length; eauto.
      - eapply SIGPROOFS.subst_constraints_out_map_length; eauto.
    Qed.

    (** Weakening list membership across an appended suffix.

        Relation to the paper:
        this is a pure list-bookkeeping lemma used in the call proof to lift
        caller output/local scope membership into the larger generated caller
        scope that also includes clock/reset identifiers. *)
    Lemma In_app_weaken_right:
      forall (A : Type) (x : A) a b ,
        In x a ->
        In x (a ++ b).
    Proof.
      intros A x a b Hin.
      apply in_or_app.
      left.
      exact Hin.
    Qed.

    (** Output-formal lookup under instantiated valuations with only output freshness.

        Relation to the paper:
        the NLustre call proof only needs the output part of the standard
        call-substitution equality theorem.  Keeping the premise focused on
        actual output freshness avoids re-proving irrelevant input-side facts
        at each call site. *)
    Lemma inst_valuation_outputs_eq_outputs_fresh:
      forall dlt sig inp clk rst out,
        SIG.outputs_fresh (signature_scope sig) out ->
        NoDup (signature_scope sig) ->
        List.length sig.(s_out) = List.length out ->
        Forall2
          (fun x v =>
             SIGPROOFS.inst_valuation dlt sig inp clk rst out v =
             SIGPROOFS.inst_valuation dlt sig inp clk rst out x)
          sig.(s_out) out.
    Proof.
      intros dlt sig inp clk rst out Houtfresh Hndscope Hlen.
      destruct sig as [sname sin sout sreset sclk sconstraints].
      simpl in *.
      set (sigfull :=
             {| s_name := sname;
                s_in := sin;
                s_out := sout;
                s_reset := sreset;
                s_clk := sclk;
                s_constraints := sconstraints |}).
      set (ival := SIGPROOFS.inst_valuation dlt sigfull inp clk rst out).
      destruct (SIGPROOFS.sig_scope_nodup_decomp sigfull Hndscope)
        as [_ [Hnout [Hfreshin [Houtnotin _]]]].
      assert (Htail :
                Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v)
                        sout out).
      {
        eapply SIGPROOFS.upd_idents_rev_eq_on_pairs.
        - intros x Hin. unfold signature_scope. apply in_or_app. right.
          apply in_or_app. left. exact Hin.
        - exact Houtfresh.
        - exact Hnout.
        - exact Hlen.
      }
      assert (Houtsafe :
                forall x,
                  In x sout ->
                  ~ In x sin /\ ~ In x [sclk; sreset]).
      {
        intros x Hinout.
        split.
        - intro Hinin.
          rewrite Forall_forall in Hfreshin.
          specialize (Hfreshin _ Hinin).
          apply Hfreshin.
          apply in_app_iff. left. exact Hinout.
        - rewrite Forall_forall in Houtnotin.
          exact (Houtnotin _ Hinout).
      }
      assert (Hformal :
                forall x,
                  In x sout ->
                  ival x = upd_idents_rev dlt sout out x).
      {
        intros x Hinout.
        unfold ival, SIGPROOFS.inst_valuation.
        rewrite upd_types_rev_outside.
        2:{
          destruct (Houtsafe x Hinout) as [Hxin _].
          exact Hxin.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now left; symmetry.
        }
        rewrite upd_type_outside.
        2:{
          destruct (Houtsafe x Hinout) as [_ Hxclkreset].
          intro Heq. apply Hxclkreset. now right; left; symmetry.
        }
        reflexivity.
      }
      assert (Hactual :
                forall v,
                  In v out ->
                  ival v = dlt v).
      {
        intros v Hinout.
        unfold ival.
        eapply SIGPROOFS.inst_valuation_outside_sig_scope.
        unfold SIG.outputs_fresh in Houtfresh.
        rewrite Forall_forall in Houtfresh.
        exact (Houtfresh _ Hinout).
      }
      assert (HformalF : Forall (fun x => ival x = upd_idents_rev dlt sout out x) sout).
      {
        rewrite Forall_forall.
        intros x Hin.
        exact (Hformal x Hin).
      }
      assert (HactualF : Forall (fun v => ival v = dlt v) out).
      {
        rewrite Forall_forall.
        intros v Hin.
        exact (Hactual v Hin).
      }
      assert
        (Hconv :
           forall xs ys,
             Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v) xs ys ->
             Forall (fun x => ival x = upd_idents_rev dlt sout out x) xs ->
             Forall (fun v => ival v = dlt v) ys ->
             Forall2 (fun x v => ival v = ival x) xs ys).
      {
        intros xs ys Hrel.
        induction Hrel; intros Hf1 Hf2.
        - constructor.
        - inversion Hf1 as [|x' xs' Hx Hxs]; subst.
          inversion Hf2 as [|y' ys' Hy Hys]; subst.
          constructor.
          + transitivity (dlt y).
            * exact Hy.
            * rewrite Hx. symmetry. exact H.
          + eapply IHHrel; eauto.
      }
      eapply Hconv; eauto.
    Qed.

    (** Internal prefix raw-output specification for one generated node.

        Relation to the paper:
        this is a proof-internal target only.  The public theorem talks about
        whole output streams, but the proof of [EqFby] and recursive calls is
        naturally by induction on the current instant.  This internal spec
        therefore records output noninterference only up to a chosen prefix
        bound [k].  It is the exact recursive shape consumed by the local
        step theorem. *)
    Definition node_outputs_raw_spec
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
      forall k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node nd.(n_name) all_nodes = Some nd ->
        find_node_env nd.(n_name) envs = Some ty_env ->
        SIG.find_signature nd.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
        get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node nd.(n_in) ty_env = Some inp ->
        get_mappings_from_node nd.(n_out) ty_env = Some out ->
        get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := nd.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names nd dlt_sig dlt_raw ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') nd.(n_eqs) ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_out)) H H' k.

    (** Internal raw output specification with explicit clock alignment.

        Relation to the paper:
        recursive call proofs compare two executions of the callee under two
        derived clocks.  The semantic content is the same as
        [node_outputs_raw_spec], but the extra [clock_eq_upto] premise records
        the call-clock alignment explicitly instead of hiding it in the outer
        theorem. *)
    Definition node_outputs_raw_spec_clocked
      (nd : node) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
      forall k ty_env sig t bk bk' H H'
             clk_id rst_id clk_type rst_type inp out locals raw st_n,
        NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        Ordered_nodes all_nodes ->
        Clo.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G ->
        NLCaus.nl_global_causal all_nodes ->
        find_node nd.(n_name) all_nodes = Some nd ->
        find_node_env nd.(n_name) envs = Some ty_env ->
        SIG.find_signature nd.(n_name) G = Some sig ->
        SECNLUSTYPING.generate_node_sig_scoped_env G nd envs aux_names = OK sig ->
        get_node_aux nd.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id ty_env = Some clk_type ->
        Env.find rst_id ty_env = Some rst_type ->
        get_mappings_from_node nd.(n_in) ty_env = Some inp ->
        get_mappings_from_node nd.(n_out) ty_env = Some out ->
        get_mappings_from_node nd.(n_vars) ty_env = Some locals ->
        generate_eqns_constraints G ty_env clk_type rst_type nd.(n_eqs) init_state = OK (raw, st_n) ->
        sig = {| s_name := nd.(n_name);
                 s_in := inp;
                 s_out := out;
                 s_reset := rst_type;
                 s_clk := clk_type;
                 s_constraints := SymTypes.simplify raw locals |} ->
        node_security all_nodes G envs aux_names nd dlt_sig dlt_raw ->
        SecT.listSatisfiable dlt_raw raw ->
        Forall (Indexed.sem_equation all_nodes bk H) nd.(n_eqs) ->
        Forall (Indexed.sem_equation all_nodes bk' H') nd.(n_eqs) ->
        clock_eq_upto bk bk' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_in)) H H' k ->
        history_low_eq_upto ty_env dlt_raw t (map fst nd.(n_out)) H H' k.

    Lemma succ_eqapp_nonreset_inputs_low_eq_upto:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps x k
             inp_c inptyp outtyp ckty rstty callee_sig ls ls',
        Clo.wc_node P n ->
        In (EqApp (xh :: xt) ck callee.(n_name) exps None) n.(n_eqs) ->
        In x (xh :: xt) ->
        (forall y,
            NLCaus.nl_depends_on_eq
              (EqApp (xh :: xt) ck callee.(n_name) exps None) x y ->
            low_var ty_env dlt_raw obs y ->
            Env.find y (H (S k)) = Env.find y (H' (S k))) ->
        history_low_eq_upto ty_env dlt_raw obs (map fst (n_in n)) H H' (S k) ->
        history_low_eq_upto ty_env dlt_raw obs (vars_defined (n_eqs n)) H H' k ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt_raw ty)
          callee_sig.(s_in) inptyp ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) ls ->
        sem_vars Hc' (map fst callee.(n_in)) ls' ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps x k
             inp_c inptyp outtyp ckty rstty callee_sig ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev
             Hsig_in Hinp_c Hforinp Hinst_in_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthety & Heqexp).
      assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ obs).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt_raw ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthety.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthety in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      assert (Hfree_eq :
                forall z,
                  Is_free_in_exp z e ->
                  Env.find z (H j) = Env.find z (H' j)).
      {
        intros z Hz.
        assert (Hlowz : low_var ty_env dlt_raw obs z).
        {
          refine
            (exp_type_low
               ty_env dlt_raw obs e ety z _ _ _).
          - exact Heqexp.
          - exact Hety_low.
          - exact Hz.
        }
        assert (Hzs : Exists (Is_free_in_exp z) exps).
        {
          eapply Exists_exists.
          exists e.
          split; [eapply nth_error_In; exact Hnthe|exact Hz].
        }
        destruct
          (free_exp_in_inputs_or_defined
             P n (xh :: xt) ck callee.(n_name) exps None z
             Hwcnode Heqin Hzs)
          as [Hin_z|Hdef_z].
        - eapply Hlowin; eauto.
        - destruct (Nat.eq_dec j (S k)) as [Heqj|Hneqj].
          + subst j.
            assert (Hdep_xz :
                      NLCaus.nl_depends_on_eq
                        (EqApp (xh :: xt) ck callee.(n_name) exps None) x z).
            {
              split; [exact Hxdef|].
              eapply nth_error_free_in_aexps; eauto.
            }
            exact (Hdeps z Hdep_xz Hlowz).
          + eapply Hprev; eauto. lia.
      }
      eapply
        (eqapp_input_var_low_eq_pointwise
           ty_env ty_env_c callee callee_sig
           inptyp outtyp dlt_raw rstty ckty obs
           bk H H' Hc Hc' exps ls ls'
           j ii y ity e ety); eauto.
    Qed.

    (** Successor-step transport of reset-call inputs from caller equality.

        Relation to the paper:
        this is the reset-aware analogue of
        [succ_eqapp_nonreset_inputs_low_eq_upto].  The recursive callee run
        is taken on one masked reset segment, so the proof must additionally
        split on whether a past instant still belongs to that active segment
        or lies in an opaque, fully absent prefix. *)
    Lemma succ_eqapp_reset_inputs_low_eq_upto:
      forall P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps r ckr x k
             inp_c inptyp outtyp ckty rstty callee_sig
             rs rs' kr kr' ls ls',
        Clo.wc_node P n ->
        In (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) n.(n_eqs) ->
        In x (xh :: xt) ->
        (forall y,
            NLCaus.nl_depends_on_eq
              (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x y ->
            low_var ty_env dlt_raw obs y ->
            Env.find y (H (S k)) = Env.find y (H' (S k))) ->
        history_low_eq_upto ty_env dlt_raw obs (map fst (n_in n)) H H' (S k) ->
        history_low_eq_upto ty_env dlt_raw obs (vars_defined (n_eqs n)) H H' k ->
        callee_sig.(s_in) = inp_c ->
        get_mappings_from_node callee.(n_in) ty_env_c = Some inp_c ->
        Forall2
          (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
          exps inptyp ->
        Forall2
          (fun x0 ty =>
             SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
             SecT.hm_ext dlt_raw ty)
          callee_sig.(s_in) inptyp ->
        kr = count rs (S k) ->
        kr' = count rs' (S k) ->
        (forall j, j <= S k -> count rs j = count rs' j) ->
        sem_exps bk H exps ls ->
        sem_exps bk H' exps ls' ->
        sem_vars Hc (map fst callee.(n_in)) (mask kr rs ls) ->
        sem_vars Hc' (map fst callee.(n_in)) (mask kr' rs' ls') ->
        history_low_eq_upto ty_env_c
          (SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp)
          obs (map fst callee.(n_in)) Hc Hc' (S k).
    Proof.
      intros P n ty_env ty_env_c dlt_raw obs
             H H' Hc Hc' bk
             xh xt ck callee exps r ckr x k
             inp_c inptyp outtyp ckty rstty callee_sig
             rs rs' kr kr' ls ls'
             Hwcnode Heqin Hxdef Hdeps Hlowin Hprev
             Hsig_in Hinp_c Hforinp Hinst_in_eq
             Hkr Hkr' Hcount_eq
             Hsem_exps Hsem_exps' Hsem_vars_in_c Hsem_vars_in_c'
             j Hj y Hiny Hlowy.
      pose proof
        (get_mappings_from_node_eq _ _ _ _ Hinp_c)
        as Hinp_c_eq.
      destruct (SecT.In_nth_error_ex _ _ _ Hiny) as [ii Hnthy].
      destruct
        (get_mappings_nth_error_inv
           (map fst callee.(n_in)) ty_env_c inp_c ii y Hinp_c_eq Hnthy)
        as (ity & Hnthity & Hfindy).
      assert (Hnthsig : nth_error callee_sig.(s_in) ii = Some ity).
      { rewrite Hsig_in. exact Hnthity. }
      assert (Hii_exps : ii < List.length exps).
      {
        assert (Hii_inp : ii < List.length inp_c).
        {
          apply nth_error_Some.
          rewrite Hnthity.
          discriminate.
        }
        assert (Hlen_inp : List.length inp_c = List.length inptyp).
        {
          rewrite <- Hsig_in.
          eapply Forall2_length; eauto.
        }
        assert (Hlen_exps : List.length inptyp = List.length exps).
        {
          symmetry.
          eapply Forall2_length; eauto.
        }
        rewrite <- Hlen_exps.
        rewrite <- Hlen_inp.
        exact Hii_inp.
      }
      destruct (nth_error exps ii) as [e|] eqn:Hnthe.
      2:{
        apply nth_error_None in Hnthe.
        lia.
      }
      destruct
        (SecT.Forall2_nth_error_inv
           _ _
           (fun e0 ty => SECCETYPING.assign_exp_type ty_env e0 = Some ty)
           exps inptyp ii e
           Hforinp Hnthe)
        as (ety & Hnthety & Heqexp).
      assert (Hety_low : SecT.hm_ext dlt_raw ety ⊑ obs).
      {
        destruct Hlowy as (alpha & Hfindalpha & Halpha_low).
        rewrite Hfindy in Hfindalpha.
        inversion Hfindalpha; subst alpha; clear Hfindalpha.
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (fun x0 ty =>
                SIGPROOFS.inst_valuation dlt_raw callee_sig inptyp ckty rstty outtyp x0 =
                SecT.hm_ext dlt_raw ty)
             callee_sig.(s_in) inptyp ii ity
             Hinst_in_eq Hnthsig)
          as (ety' & Hnthety' & Hinsteq).
        change (nth_error inptyp ii = Some ety) in Hnthety.
        change (nth_error inptyp ii = Some ety') in Hnthety'.
        rewrite Hnthety in Hnthety'.
        inversion Hnthety'; subst ety'; clear Hnthety'.
        rewrite <- Hinsteq.
        exact Halpha_low.
      }
      assert (Hfree_eq :
                forall z,
                  Is_free_in_exp z e ->
                  Env.find z (H j) = Env.find z (H' j)).
      {
        intros z Hz.
        assert (Hlowz : low_var ty_env dlt_raw obs z).
        {
          refine
            (exp_type_low
               ty_env dlt_raw obs e ety z _ _ _).
          - exact Heqexp.
          - exact Hety_low.
          - exact Hz.
        }
        assert (Hzs : Exists (Is_free_in_exp z) exps).
        {
          eapply Exists_exists.
          exists e.
          split; [eapply nth_error_In; exact Hnthe|exact Hz].
        }
        destruct
          (free_exp_in_inputs_or_defined
             P n (xh :: xt) ck callee.(n_name) exps (Some (r, ckr)) z
             Hwcnode Heqin Hzs)
          as [Hin_z|Hdef_z].
        - eapply Hlowin; eauto.
        - destruct (Nat.eq_dec j (S k)) as [Heqj|Hneqj].
          + subst j.
            assert (Hdep_xz :
                      NLCaus.nl_depends_on_eq
                        (EqApp (xh :: xt) ck callee.(n_name) exps (Some (r, ckr))) x z).
            {
              split; [exact Hxdef|].
              left.
              eapply nth_error_free_in_aexps; eauto.
            }
            exact (Hdeps z Hdep_xz Hlowz).
          + eapply Hprev; eauto. lia.
      }
      destruct (Nat.eq_dec (count rs j) kr) as [Hactive|Hopaque].
      - assert (Hactive' : count rs' j = kr').
        {
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq (S k) (le_n (S k))) as Hcntk.
          rewrite Hkr in Hactive.
          rewrite Hkr'.
          rewrite <- Hcntk.
          rewrite <- Hcntj.
          exact Hactive.
        }
        eapply
          (eqapp_reset_input_var_low_eq_pointwise
             ty_env ty_env_c callee callee_sig
             inptyp outtyp dlt_raw rstty ckty obs
             bk H H' Hc Hc' exps rs rs' kr kr' ls ls'
             j ii y ity e ety); eauto.
      - assert (Hopaque' : count rs' j <> kr').
        {
          intro Heq.
          specialize (Hcount_eq j Hj) as Hcntj.
          specialize (Hcount_eq (S k) (le_n (S k))) as Hcntk.
          apply Hopaque.
          rewrite Hcntj.
          rewrite Heq.
          rewrite Hkr'.
          rewrite <- Hcntk.
          symmetry.
          exact Hkr.
        }
        specialize (Hsem_vars_in_c j).
        specialize (Hsem_vars_in_c' j).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc j))
             (map fst callee.(n_in)) (mask kr rs ls j) ii y
             Hsem_vars_in_c Hnthy)
          as (vin & Hnthvin & Hsem_y).
        destruct
          (SecT.Forall2_nth_error_inv
             _ _
             (sem_var_instant (Hc' j))
             (map fst callee.(n_in)) (mask kr' rs' ls' j) ii y
             Hsem_vars_in_c' Hnthy)
          as (vin' & Hnthvin' & Hsem_y').
        rewrite (mask_opaque ls kr rs j Hopaque) in Hnthvin.
        rewrite (mask_opaque ls' kr' rs' j Hopaque') in Hnthvin'.
        pose proof (nth_error_all_absent_absent _ (ls 0) _ _ Hnthvin) as Hvin.
        pose proof (nth_error_all_absent_absent _ (ls' 0) _ _ Hnthvin') as Hvin'.
        unfold sem_var_instant in Hsem_y, Hsem_y'.
        subst vin vin'.
        rewrite Hsem_y, Hsem_y'.
        reflexivity.
    Qed.


    (** Internal raw output theorem.

        Relation to the paper:
        this is not part of the public statement of noninterference.  It is
        the proof-internal theorem that should be derived from the paired
        [node_security] predicate and then used to recover the canonical
        output theorem. *)
  End GENERATED_NODE_NONINTERFERENCE.

End SECNLUSNONINTERFERENCEHELPERS.
