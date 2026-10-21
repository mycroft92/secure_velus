(** Executable export of generated Lustre security signatures and constraints.

    The Lustre counterpart of [SecNLusConstraintExport.v], and the first place
    the Lustre-side stack is applied to the concrete Velus modules rather than
    kept behind module parameters.  That is what makes it a check as well as an
    export: [SECLNAMEGEN], [SECLTYPING] and -- in [Check] below --
    [SECLUSNLUSTRANSLATION] are instantiated at [Instantiator]'s real Lustre,
    CoreExpr, NLustre and Transcription modules.

    [Check] is a functor over the lattice because the repository fixes no
    concrete one: [Lattice] is genuinely a parameter of the security semantics.
    Everything else in it is concrete. *)

From Velus Require Import Common.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecLusNLusTranslation.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SecLusUnnesting.
From Velus Require Import SIF.SecNamingTotality.
From Velus Require Import SIF.SecLNamingTotality.
From Velus Require Import SIF.SecLusNormalization.

From Coq Require Import String List.
From compcert Require Import common.Errors.

Import ListNotations.

Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module Import OpAux := Interface.OpAux.
Module CE := Instantiator.CE.
Module L := Instantiator.L.
Module NL := Instantiator.NL.
Module TR := Instantiator.TR.

Module SC := SecMonad Ids.
Module SIG := Signature Ids SC.

Module ConcreteNameGen <: NAMEGEN Ids Op CE.Syn NL.Syn.
Include NAMEGEN Ids Op CE.Syn NL.Syn.
End ConcreteNameGen.

Module ConcreteSecCETyping <: SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo.
Include SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo.
End ConcreteSecCETyping.

Module ConcreteSecLNameGen :=
  SecLNameGen Ids Op OpAux L.Syn CE.Syn NL.Syn ConcreteNameGen TR.Tr.

Module ConcreteSecLTyping :=
  SecLTyping Ids Op OpAux SC L.Syn CE.Syn NL.Syn SIG ConcreteNameGen
    CE.IsF CE.Clo ConcreteSecCETyping TR.Tr.

(** * The dump

    Same record as the NLustre export, so the two can be diffed node by node
    on a transcribed program -- which is what [Signature_entails] is about. *)

Record lnode_constraint_dump := mkLNodeConstraintDump {
  ldump_name : ident;
  ldump_clk : ident;
  ldump_rst : ident;
  ldump_inputs : list (ident * ident);
  ldump_outputs : list (ident * ident);
  ldump_locals : list (ident * ident);
  ldump_raw_constraints : list SymTypes.constraint;
  ldump_constraints : list SymTypes.constraint
}.

Definition sif_lconstraint_dump := list lnode_constraint_dump.

Fixpoint zip_idents (xs ys : list ident) : list (ident * ident) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: zip_idents xs' ys'
  | _, _ => []
  end.

Definition build_lnode_constraint_dump
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  (n : L.Syn.node)
  : res lnode_constraint_dump :=
  match find_node_env n.(L.Syn.n_name) envs with
  | None => Error (MSG "Missing generated local security environment for node "
                    :: CTX n.(L.Syn.n_name) :: nil)
  | Some env =>
      match get_node_aux n.(L.Syn.n_name) aux_names with
      | None => Error (MSG "Missing generated clock/reset names for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
      | Some (clk_id, rst_id) =>
          match get_mappings_from_node n.(L.Syn.n_in) env,
                get_mappings_from_node n.(L.Syn.n_out) env,
                get_mappings_from_node n.(L.Syn.n_vars) env,
                SIG.find_signature n.(L.Syn.n_name) G
          with
          | Some inp_ids, Some out_ids, Some local_ids, Some sig =>
              match ConcreteSecLTyping.generate_leqns_constraints
                      G env sig.(SIG.s_clk) sig.(SIG.s_reset)
                      (ConcreteSecLTyping.lnode_clock_env n)
                      n.(L.Syn.n_eqs) SC.init_state with
              | Error e => Error e
              | OK (raw_constraints, _) =>
                  OK {| ldump_name := n.(L.Syn.n_name);
                        ldump_clk := sig.(SIG.s_clk);
                        ldump_rst := sig.(SIG.s_reset);
                        ldump_inputs := zip_idents (map fst n.(L.Syn.n_in)) inp_ids;
                        ldump_outputs := zip_idents (map fst n.(L.Syn.n_out)) out_ids;
                        ldump_locals := zip_idents (map fst n.(L.Syn.n_vars)) local_ids;
                        ldump_raw_constraints := raw_constraints;
                        ldump_constraints := sig.(SIG.s_constraints) |}
              end
          | None, _, _, _ =>
              Error (MSG "Missing generated input mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, None, _, _ =>
              Error (MSG "Missing generated output mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, _, None, _ =>
              Error (MSG "Missing generated local mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, _, _, None =>
              Error (MSG "Missing generated security signature for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          end
      end
  end.

Fixpoint build_lconstraint_dump
  (nodes : list L.Syn.node)
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  : res sif_lconstraint_dump :=
  match nodes with
  | [] => OK []
  | n :: nodes' =>
      match build_lnode_constraint_dump envs aux_names G n with
      | Error e => Error e
      | OK d =>
          match build_lconstraint_dump nodes' envs aux_names G with
          | Error e => Error e
          | OK ds => OK (d :: ds)
          end
      end
  end.

(** The accumulator grows front-to-back while [Ordered_nodes] places a callee
    after its caller, so the driver generates over [rev nodes] -- exactly as
    the NLustre one does, which is what lets the two dumps be compared. *)

Definition generate_lustre_constraint_dump
  (nodes : list L.Syn.node)
  : res sif_lconstraint_dump :=
  let ordered_nodes := rev nodes in
  match ConcreteSecLNameGen.generate_lnode_scoped_env_st ordered_nodes with
  | Error e => Error e
  | OK (envs, aux_names, st) =>
      match ConcreteSecLTyping.generate_all_lsignatures_scoped_env
              ordered_nodes envs aux_names st with
      | Error e => Error e
      | OK G => build_lconstraint_dump ordered_nodes envs aux_names G
      end
  end.

(** * The leg, at the concrete modules

    Nothing here is used by the export; it exists so that the parameter list of
    [SECLUSNLUSTRANSLATION] is checked against the real Velus modules rather
    than only against itself. *)

Module Check (Lat : Lattice).

  Module SecT := SecTypes.SecTypes Lat.
  Module SLT := SecLusTypesFun Lat SecT.
  Module STEP := SecMonadStep Ids SC.

  Module SIGPROOFS <: SIGNATURE_PROOFS Ids SC SIG Lat SecT.
  Include SIGNATURE_PROOFS Ids SC SIG Lat SecT.
  End SIGPROOFS.

  Module SECNLUSTYPING :=
    SecNLusTyping Ids Op SC CE.Syn NL.Syn SIG ConcreteNameGen
      CE.IsF CE.Clo ConcreteSecCETyping NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo.

  Module SECNLC :=
    SecNLusTypingCorrectness Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
      ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping
      NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo SECNLUSTYPING.

  Module Leg :=
    SecLusNLusTranslation Ids Op OpAux SC L.Syn CE.Syn NL.Syn Lat SecT STEP
      SIG SIGPROOFS ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping
      NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo TR.Tr ConcreteSecLTyping
      SECNLUSTYPING SECNLC ConcreteSecLNameGen L.Clo L.Ord TR.Clocking.

  (** And the unnesting leg, at the same concrete modules. *)
  Module LegU :=
    SecLusUnnesting Ids Op OpAux Lat SecT SLT SC L.Syn L.Clo CE.Syn NL.Syn STEP SIG
      SIGPROOFS ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping TR.Tr
      ConcreteSecLTyping L.Norm.Norm.Unnesting.

  (** And the normalization legs: unnesting, then [fby] normalisation, as one
      program-level lockstep. *)
  Module SECNT := SecNamingTotality Ids Op CE.Syn NL.Syn NL.Mem NL.IsD NL.Ord
                    ConcreteNameGen.
  Module SECLNT :=
    SecLNamingTotality Ids Op OpAux L.Syn CE.Syn NL.Syn NL.Mem NL.IsD NL.Ord
      ConcreteNameGen TR.Tr ConcreteSecLNameGen SECNT L.Ord.
  Module LegN :=
    SecLusNormalization Ids Op OpAux Lat SecT SLT SC L.Syn L.Clo CE.Syn NL.Syn
      NL.Mem NL.IsD NL.Ord STEP SIG SIGPROOFS ConcreteNameGen CE.IsF CE.Clo
      ConcreteSecCETyping TR.Tr ConcreteSecLTyping L.Cau L.Typ L.Norm.Norm
      ConcreteSecLNameGen SECNT L.Ord SECLNT.

  (** The signature side of the composition.  The two Lustre-to-Lustre legs
      give [sigs_preserved] from the source global to the transcribed one; the
      translation leg gives [Signature_entails] from there to NLustre.  The
      source signature's call clause is then read off the composed
      [signatures_preserved], so what it needs is only the node-local facts
      about the source (good, duplicate-free scope) and about the NLustre
      signature (scoped). *)
  Lemma source_signature_entails :
    forall GS GT GN,
      LegU.sigs_preserved GS GT ->
      Leg.Signature_entails GT GN ->
      (forall f sg, SIG.find_signature f GS = Some sg ->
          SIG.signature_good sg /\ NoDup (SIG.signature_scope sg)) ->
      (forall f sg, SIG.find_signature f GN = Some sg -> SIG.signature_scoped sg) ->
      Leg.Signature_entails GS GN.
  Proof.
    intros GS GT GN Hsp Hent Hsrc Hsc f n1 Hf.
    destruct (Hsp f n1 Hf) as (t & Hft & Hname1 & Hp1).
    destruct (Hent f t Hft) as (n2 & Hfn & Hn2 & Hp2 & _).
    destruct (Hsrc f n1 Hf) as [Hgood Hnd].
    exists n2. split; [exact Hfn|].
    assert (Hpres : SIGPROOFS.signatures_preserved n1 n2)
      by (eapply LegU.signatures_preserved_trans; eauto).
    unfold Leg.Signature_head_entails. split; [|split; [exact Hpres|]].
    - congruence.
    - eapply Leg.Signature_call_entails_from_preserved; eauto.
  Qed.

  (** The whole signature half: the source program's security signatures,
      generated against the naming of its normalised form, are entailed by the
      NLustre signatures of the transcription of that form.  The two
      Lustre-to-Lustre legs are [LegN.normalization_signatures_preserved];
      nothing is assumed beyond the program's typing and clocking (the former
      source guard is a theorem of well-clockedness).  The closure of generated callee signatures under the
      declared clocks is proved ([LegN.sig_inputs_step]). *)
  Module U := L.Norm.Norm.Unnesting.
  Module NFm := L.Norm.Norm.NormFby.

  Lemma Ordered_nodes_nodup_names_nl :
    forall (Q : NL.Syn.global),
      NL.Ord.Ordered_nodes Q -> NoDup (map NL.Syn.n_name Q).
  Proof.
    intros Q Hord. induction Hord as [|nd nds Hord IH Hcalls Hfresh];
      [constructor|]. simpl. constructor.
    - intro Hin. apply in_map_iff in Hin as (nd' & Heq & Hin').
      rewrite Forall_forall in Hfresh.
      exact (Hfresh _ Hin' (eq_sym Heq)).
    - exact IH.
  Qed.

  Lemma find_node_of_In_nl :
    forall (Q : NL.Syn.global) n,
      NoDup (map NL.Syn.n_name Q) -> In n Q ->
      NL.Syn.find_node n.(NL.Syn.n_name) Q = Some n.
  Proof.
    induction Q as [|nd Q IH]; intros n Hnd Hin; [inversion Hin|].
    simpl in Hnd. inversion Hnd as [|x xs Hnotin Hnd']; subst x xs.
    destruct Hin as [Heq|Hin].
    - subst nd. simpl. rewrite ident_eqb_refl. reflexivity.
    - simpl. destruct (ident_eqb nd.(NL.Syn.n_name) n.(NL.Syn.n_name)) eqn:Hname.
      + exfalso. apply ident_eqb_eq in Hname.
        apply Hnotin. rewrite Hname. now apply in_map.
      + apply IH; assumption.
  Qed.

  Theorem source_signatures_entail_nlustre :
    forall (G : L.Syn.global) (Hwl : L.Syn.wl_global G)
           (Hpr : Forall (fun n => L.Syn.n_prefixes n = U.elab_prefs) G)
           (Hunt : U.unnested_global (U.unnest_global G Hwl Hpr))
           (Hpref1 : Forall (fun n => L.Syn.n_prefixes n = NFm.norm1_prefs)
                       (U.unnest_global G Hwl Hpr)),
      L.Clo.wc_global G -> L.Typ.wt_global G ->
      forall envs aux stN st GS GT GM P Hp GN,
        ConcreteSecLNameGen.generate_lnode_scoped_env_st
          (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1))
          = OK (envs, aux, stN) ->
        LegN.sec_le stN st ->
        L.Ord.Ordered_nodes
          (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1) ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env (rev G) envs aux
          st = OK GS ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env
          (rev (U.unnest_global G Hwl Hpr)) envs aux st = OK GT ->
        ConcreteSecLTyping.generate_all_lsignatures_scoped_env
          (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1))
          envs aux st = OK GM ->
        TR.Tr.to_global
          (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1) Hp
          = OK P ->
        ConcreteNameGen.generate_node_scoped_env (rev P) = OK (envs, aux) ->
        NL.Ord.Ordered_nodes P ->
        NL.Clo.wc_global P ->
        SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK GN ->
        Leg.Signature_entails GS GN.
  Proof.
    intros G Hwl Hpr Hunt Hpref1 Hwc Hwt envs aux stN st GS GT GM P
      Hp GN Hnaming Hle Hord HgS HgT HgM Htr Hnames HordP Hwcp HgN.
    destruct (LegN.normalization_signatures_preserved G Hwl Hpr Hunt Hpref1
                Hwc Hwt envs aux stN st GS GT GM Hnaming Hle HgS HgT
                HgM) as (_ & Hsp).
    assert (Hnotself :
              Forall (fun m => ~ L.Ord.Is_node_in m.(L.Syn.n_name)
                                  m.(L.Syn.n_eqs))
                (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt
                        Hpref1))).
    { pose proof (Leg.Ordered_nodes_not_self _ Hord) as Hns.
      rewrite Forall_forall in Hns |- *. intros x Hx.
      apply in_rev in Hx. exact (Hns x Hx). }
    assert (Hwcrev : Forall (NL.Clo.wc_node P) (rev P)).
    { pose proof (Ordered_nodes_nodup_names_nl P HordP) as Hnd.
      apply Forall_forall. intros n Hin. apply in_rev in Hin.
      eapply NL.Clo.wc_find_node'; [exact HordP|exact Hwcp|].
      apply (find_node_of_In_nl P n Hnd Hin). }
    destruct (Leg.generate_all_signatures_entails_scoped_inv P _ (rev P) envs aux st
                GM GN
                (Leg.transcribed_rev _ _ (Leg.to_global_transcribed _ _ _ Htr))
                Hnotself Hnames Hwcrev HgM HgN)
      as (Hent & Hsc & _ & _).
    eapply source_signature_entails;
      [exact (fun f sg1 Hf => Hsp f sg1 Hf)|exact Hent
      |exact (LegN.source_signatures_good G Hwl Hpr Hunt Hpref1 Hwc Hwt
                envs aux stN st GS Hnaming Hle HgS)
      |exact Hsc].
  Qed.

  (** What the signature half says about a security policy.  A valuation that
      satisfies a source signature's stored constraints -- a policy on the
      source node's interface and its call interface -- extends, agreeing on
      the signature's scope, to a valuation satisfying the stored constraints
      of the transcribed NLustre signature of the same node.  Noninterference
      of the compiled program is then stated against the extension, whose
      interface levels are the policy's. *)
  Corollary source_policy_realised :
    forall GS GN,
      Leg.Signature_entails GS GN ->
      forall f sgS,
        SIG.find_signature f GS = Some sgS ->
        exists sgN,
          SIG.find_signature f GN = Some sgN
          /\ SIGPROOFS.signatures_preserved sgS sgN.
  Proof.
    intros GS GN Hent f sgS Hf.
    destruct (Hent f sgS Hf) as (sgN & HfN & _ & Hpres & _).
    exact (ex_intro _ sgN (conj HfN Hpres)).
  Qed.

End Check.
