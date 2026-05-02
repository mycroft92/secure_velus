(* Target-side observation scaffold for STC.

   This file mirrors only the observation-layer part of the initial NLustre
   setup, and is intentionally not the main proof path for the thesis.

   Current design decision:

   - we do not currently need an intrinsic STC noninterference theorem over
     arbitrary STC runs;
   - the required target-side result is weaker: noninterference for STC
     behaviors that arise from translating NLustre behaviors;
   - that weaker result should eventually be stated as a semantic corollary in
     [SecNLusStcTranslation.v], by combining:
       + source-side NLustre noninterference,
       + indexed-to-memory NLustre bridging,
       + NLustre-to-STC semantic preservation, and
       + source/target signature preservation.

   This file therefore just isolates the STC-side observation vocabulary that
   may still be useful for packaging that later corollary.  The first goal is
   to isolate the pieces that are already clear on the STC side:

   - the shared low-observation layer still uses the source-generated
     [NameInterface] environment keyed by the translated system name;
   - the target-side causality/scheduling interface lives in
     [SIF.StcCausality];
   - the eventual theorem will need to keep semantic environments [R] separate
     from STC memories [S/I/S'] and from the generated typing environment.

   The final intrinsic STC semantic theorem is intentionally deferred, because
   it is not required for the weaker translated-behavior result. *)

From Coq Require Import List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEProperties.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import Stc.StcClockingSemantics.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import SIF.StcCausality.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECSTCNONINTERFERENCE
  (Import Ids    : IDS)
  (Import Lat    : Lattice)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import SecT   : SECTYPES Lat)
  (Import CESyn  : CESYNTAX Op)
  (Import SynNL  : NLSYNTAX Ids Op CESyn)
  (Import SynStc : STCSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING : SECCETYPING Ids Op CESyn)
  (Import CETyp  : CETYPING Ids Op CESyn)
  (Import CEIsF  : CEISFREE Ids Op CESyn)
  (Import CEClo  : CECLOCKING Ids Op CESyn)
  (Import Last   : STCISLAST Ids Op CESyn SynStc)
  (Import Var    : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def    : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst   : STCISSYSTEM Ids Op CESyn SynStc)
  (Import Ord    : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsF    : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import Clo    : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Import Str    : INDEXEDSTREAMS Op OpAux)
  (Import CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (Import CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Import Sem    : STCSEMANTICS Ids Op OpAux CESyn SynStc Syst Ord Str CESem)
  (Import CloSem : STCCLOCKINGSEMANTICS Ids Op OpAux CESyn SynStc Str Last Var Def Syst Ord CESem Sem CEClo Clo)
  (Import WellDef : STCWELLDEFINED Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF)
  (StcCaus       : STCCAUSALITY Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF WellDef)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc SIG NAMEGEN SECCETYPING
       CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING).

  (** Vocabulary alignment with the papers and the existing SIF files.

      As on the NLustre side:
      - paper [s] = Coq [dlt];
      - paper [ρ] = Coq [sig.(s_constraints)];
      - "ρ is satisfied by s" = [signature_satisfied dlt sig].

      The STC development reuses the same convention so the later translation
      theorem can compare source and target security arguments without a second
      notation layer. *)
  Definition ground_instantiation : Type := ident -> Lat.t.

  Definition signature_constraints (sig : signature) : list constraint :=
    sig.(s_constraints).

  Definition signature_satisfied
    (dlt : ground_instantiation) (sig : signature) : Prop :=
    SecT.listSatisfiable dlt (signature_constraints sig).

  (** The target-side naming discipline still comes from the source-generated
      [NameInterface] table.  STC systems reuse the local security environment
      keyed by their translated system name; they do not generate a second
      target-only typing environment. *)
  Section GENERATED_LOW_OBSERVATION.
    Variable src_nodes : SynNL.global.
    Variable envs : node_scoped_env.
    Variable aux_names : list node_aux_names.
    Variable sys : system.
    Variable ty_env : local_sec_env.
    Variable dlt : ground_instantiation.
    Variable t : Lat.t.

    Hypothesis Henvsgen :
      NAMEGEN.generate_node_scoped_env src_nodes = OK (envs, aux_names).
    Hypothesis Hfindenv :
      find_node_env sys.(s_name) envs = Some ty_env.

    (** One raw STC variable is observable at level [t] when the generated
        security identifier attached to it by the source naming layer is below
        [t] under the chosen ground instantiation.

        Relation to the paper:
        this is the target-side counterpart of membership in [X⊑t], with the
        important caveat that [Γ] is still generated on the source side and
        then looked up by translated system name. *)
    Definition low_var (x : ident) : Prop :=
      exists α, Env.find x ty_env = Some α /\ dlt α ⊑ t.

    Definition low_var_dec (x : ident) : {low_var x} + {~ low_var x}.
    Proof.
      unfold low_var.
      destruct (Env.find x ty_env) as [α|] eqn:Hfind.
      - destruct (Lat.order_dec (dlt α) t) as [Hle|Hnle].
        + left. now exists α.
        + right. intros (α' & Hfind' & Hle').
          inv Hfind'. contradiction.
      - right. intros (α & Hfind' & _).
        discriminate Hfind'.
    Defined.

    Definition low_var_b (x : ident) : bool :=
      if low_var_dec x then true else false.

    (** Boolean reflection of low observability.

        Relation to the paper:
        this is the decidable target-side form of the judgment [x ∈ X⊑t]. *)
    Lemma low_var_b_spec:
      forall x,
        low_var_b x = true <-> low_var x.
    Proof.
      intros x.
      unfold low_var_b.
      destruct (low_var_dec x); split; intro H; auto; discriminate.
    Qed.

    (** Finite-list representative of the paper's low-observation set.

        Relation to the paper:
        STC observations are still filtered through [X⊑t]; the only difference
        is that the later semantic theorem will talk about system transitions
        rather than pure node histories. *)
    Definition vars_le_t (X : list ident) : list ident :=
      filter low_var_b X.

    (** Membership characterization for the finite low-observation set.

        Relation to the paper:
        this is the list-based reformulation of [x ∈ X⊑t]. *)
    Lemma vars_le_t_spec:
      forall X x,
        In x (vars_le_t X) <-> In x X /\ low_var x.
    Proof.
      intros X x.
      unfold vars_le_t.
      rewrite filter_In.
      rewrite low_var_b_spec.
      tauto.
    Qed.

    Definition project_env_on (xs : list ident) (R : env) : env :=
      fold_right
        (fun x acc =>
           match Env.find x R with
           | Some v => Env.add x v acc
           | None => acc
           end)
        (Env.empty _)
        xs.

    (** Paper-style low projection on one STC semantic snapshot.

        Relation to the paper:
        this is the target-side environment analogue of [H|X⊑t], specialised
        to a single instant environment [R]. *)
    Definition project_env_le_t (X : list ident) (R : env) : env :=
      project_env_on (vars_le_t X) R.

    (** Relational low-equivalence on one STC semantic environment.

        Relation to the paper:
        the later STC theorem should use this relational view rather than the
        concrete projection, exactly as on the NLustre side. *)
    Definition env_low_eq (X : list ident) (R R' : env) : Prop :=
      forall x,
        In x X ->
        low_var x ->
        Env.find x R = Env.find x R'.
  End GENERATED_LOW_OBSERVATION.

  Section SYSTEM_THEOREM_SHAPE.
    Variable sys : system.

    (** Basic STC variable sets for the future theorem statements.

        The target proof will need both the broad internal set tracked by the
        typing generator and the narrower user-visible set. *)
    Definition system_inputs : list ident :=
      map fst sys.(s_in).

    Definition system_outputs : list ident :=
      map fst sys.(s_out).

    Definition system_lasts : list ident :=
      map fst sys.(s_lasts).

    Definition system_defined : list ident :=
      Def.defined sys.(s_tcs).

    (** Candidate public visible set for the first STC theorem packaging.

        Relation to the paper:
        STC makes memory cells explicit as [s_lasts], so the target-side
        visible set must decide whether the theorem first exposes only outputs
        or outputs together with the current values of lasts. *)
    Definition system_visible : list ident :=
      system_outputs ++ system_lasts.
  End SYSTEM_THEOREM_SHAPE.

  (** Proof-architecture note.

      This file is currently limited to observation vocabulary and theorem
      shape bookkeeping.

      Why no intrinsic STC theorem here for now:

      - the weaker theorem actually needed by the thesis is a translated-
        behavior corollary, not a property of arbitrary STC runs;
      - [NLustreToStc.Correctness.correctness_loop] already transports source
        runs to STC loops;
      - [SecNLusStcTranslation.generated_program_signatures_preserved_global]
        already aligns the relevant source/target signatures;
      - so the main semantic work should stay source-side until the NLustre
        noninterference theorem is finished.

      If a stronger target-native theorem later becomes necessary, the most
      likely internal statement is still over [system_defined], because:

      - [SECSTCTYPING.generate_trconstrs_constraints_targets] reasons over
        [Def.defined sys.(s_tcs)];
      - [SECSTCTYPING.system_var_defined_in_tcs] and
        [SECSTCTYPING.system_last_defined_in_tcs] already connect visible
        outputs/lasts back into that internal set;
      - [TcNext] splits current observation from next-state update, so the
        semantic proof would need one careful current-step theorem before
        packaging a cleaner visible corollary. *)
End SECSTCNONINTERFERENCE.

Module SecStcNonInterference
  (Ids    : IDS)
  (Lat    : Lattice)
  (Op     : OPERATORS)
  (OpAux  : OPERATORS_AUX Op)
  (SC     : SECMONAD Ids)
  (SecT   : SECTYPES Lat)
  (CESyn  : CESYNTAX Op)
  (SynNL  : NLSYNTAX Ids Op CESyn)
  (SynStc : STCSYNTAX Ids Op CESyn)
  (SIG    : SIGNATURE Ids SC)
  (NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (SECCETYPING : SECCETYPING Ids Op CESyn)
  (CETyp  : CETYPING Ids Op CESyn)
  (CEIsF  : CEISFREE Ids Op CESyn)
  (CEClo  : CECLOCKING Ids Op CESyn)
  (Last   : STCISLAST Ids Op CESyn SynStc)
  (Var    : STCISVARIABLE Ids Op CESyn SynStc)
  (Def    : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Syst   : STCISSYSTEM Ids Op CESyn SynStc)
  (Ord    : STCORDERED Ids Op CESyn SynStc Syst)
  (IsF    : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Clo    : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst Ord CEClo)
  (Str    : INDEXEDSTREAMS Op OpAux)
  (CESem  : CESEMANTICS Ids Op OpAux CESyn Str)
  (CEProps : CEPROPERTIES Ids Op OpAux CESyn Str CESem CETyp CEIsF)
  (Sem    : STCSEMANTICS Ids Op OpAux CESyn SynStc Syst Ord Str CESem)
  (CloSem : STCCLOCKINGSEMANTICS Ids Op OpAux CESyn SynStc Str Last Var Def Syst Ord CESem Sem CEClo Clo)
  (WellDef : STCWELLDEFINED Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF)
  (StcCaus : STCCAUSALITY Ids Op CESyn SynStc Syst Ord Var Last Def CEIsF IsF WellDef)
  (SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (SECSTCTYPING :
     SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst Ord IsF Clo)
  (SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc SIG NAMEGEN SECCETYPING
       CEIsF CEClo Last Var Def Syst Ord IsF Clo SECSTCTYPING)
  <: SECSTCNONINTERFERENCE
       Ids Lat Op OpAux SC SecT CESyn SynNL SynStc SIG NAMEGEN SECCETYPING
       CETyp CEIsF CEClo Last Var Def Syst Ord IsF Clo Str CESem CEProps Sem
       CloSem WellDef StcCaus SIGPROOFS SECSTCTYPING SECSTCTYPINGCORRECTNESS.
  Include SECSTCNONINTERFERENCE
            Ids Lat Op OpAux SC SecT CESyn SynNL SynStc SIG NAMEGEN
            SECCETYPING CETyp CEIsF CEClo Last Var Def Syst Ord IsF Clo Str
            CESem CEProps Sem CloSem WellDef StcCaus SIGPROOFS SECSTCTYPING
            SECSTCTYPINGCORRECTNESS.
End SecStcNonInterference.
