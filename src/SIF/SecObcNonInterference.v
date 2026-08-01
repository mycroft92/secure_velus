(** Noninterference for Obc behaviors that come from translated secure
    NLustre nodes.

    Like [SecStcNonInterference.v], this is a *transport*, not a fresh
    noninterference proof: the imperative semantics is never attacked
    directly.  A behaviour of a translated class is exhibited together
    with the Stc behaviour behind it -- which is what
    [StcToObc.Correctness.correctness_loop_call] produces -- and the Stc
    theorem is run on that.  The only real work is moving
    low-equivalence between the two stream representations: Stc speaks
    [value] streams, Obc speaks [option val] streams, related by
    [eq_if_present] on the way in and by [value_to_option] on the way
    out. *)

From Coq Require Import List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindToIndexed.
From Velus Require Import CoreExpr.
From Velus Require Import NLustre.
From Velus Require Import Stc.
From Velus Require Import Stc.StcSchedule.
From Velus Require Import Obc.
From Velus Require NLustreToStc.Translation.
From Velus Require NLustreToStc.Correctness.
From Velus Require StcToObc.Translation.
From Velus Require StcToObc.Correctness.
From Velus Require Import StcToObc.StcMemoryCorres.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.NLustreCausality.
From Velus Require Import SIF.SecNLusNonInterferenceSupport.
From Velus Require Import SIF.SecNLusNonInterference.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import SIF.SecNLusStcTranslation.
From Velus Require Import SIF.SecObcTyping.
From Velus Require Import SIF.SecObcTypingCorrectness.
From Velus Require Import SIF.SecStcObcTranslation.
From Velus Require Import SIF.SecNLusStcObcEnv.
From Velus Require Import SIF.SecStcNonInterference.
From Velus Require Import Clocks.
From compcert Require Import common.Errors.

Module Type SECOBCNONINTERFERENCE
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import CStr  : COINDSTREAMS Op OpAux)
  (Import Str   : INDEXEDSTREAMS Op OpAux)
  (Import CIStr : COINDTOINDEXED Op OpAux CStr Str)
  (Import SC    : SECMONAD Ids)
  (Import SecT  : SECTYPES Lat)
  (Import CE    : COREEXPR Ids Op OpAux Str)
  (Import NL    : NLUSTRE Ids Op OpAux CStr Str CIStr CE)
  (Import Stc   : STC Ids Op OpAux Str CE)
  (Import TransNL : NLustreToStc.Translation.TRANSLATION
                      Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (NLStcCorr : NLustreToStc.Correctness.CORRECTNESS
                 Ids Op OpAux CStr Str CIStr CE NL Stc TransNL)
  (Import SIG          : SIGNATURE Ids SC)
  (Import SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN      : NAMEGEN Ids Op CE.Syn NL.Syn)
  (Import SECCETYPING  : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (NLCaus              : NLUSTRECAUSALITY Ids Op CE.Syn NL.Syn CE.IsF NL.IsF)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CE.Syn NL.Syn SIG NAMEGEN CE.IsF CE.Clo
       SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
       NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo
       SECNLUSTYPING)
  (NLusSupport :
     SECNLUSNONINTERFERENCESUPPORT Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG
       NAMEGEN CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD
       NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (NLusNI :
     SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG NAMEGEN
       CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD NL.IsF
       NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (NLusStcBridge :
     SECNLUSSTCTRANSLATION Ids Lat Op SC SecT CE.Syn NL.Syn Stc.Syn NL.Mem
       TransNL SIG SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord
       NL.IsD NL.IsF NL.Clo SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Stc.Last
       Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING
       SECSTCTYPINGCORRECTNESS)
  (StcNI :
     SECSTCNONINTERFERENCE Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       TransNL NLStcCorr SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI SECSTCTYPING
       SECSTCTYPINGCORRECTNESS NLusStcBridge)
  (** The Obc side proper: syntax, semantics and the translation's own
      correctness theorem, exactly as [NLCorrectness] wires them. *)
  (Import Obc   : OBC Ids Op OpAux)
  (Import TransObc : StcToObc.Translation.TRANSLATION
                       Ids Op OpAux CE.Syn Stc.Syn Obc.Syn)
  (Import Corres : STCMEMORYCORRES Ids Op CE.Syn Stc.Syn Stc.Last)
  (StcObcCorr : StcToObc.Correctness.CORRECTNESS
                  Ids Op OpAux Str CE Stc Obc TransObc Corres)
  (** Velus's own scheduler: the Obc code the compiler emits comes from
      the *scheduled* Stc program, which is the only one [Well_defined]
      can hold of. *)
  (ExtSch : EXT_STCSCHEDULER Ids Op CE.Syn Stc.Syn)
  (Sched : STCSCHEDULE Ids Op OpAux Str CE Stc.Syn Stc.Syst Stc.Ord Stc.Sem
             Stc.Typ Stc.Var Stc.Last Stc.Def Stc.Clo Stc.Free Stc.Wdef ExtSch)
  (** The Stc-to-Obc signature bridge, so that a class's security witness
      can name the Obc signature the way [system_security] names the Stc
      one.  Taken as a parameter, not re-derived. *)
  (SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC Obc.Syn SIG)
  (SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC Obc.Syn Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (StcObcBridge :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CE.Syn Stc.Syn Obc.Syn Lat SecT SIG
       SIGPROOFS CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def Stc.Syst
       Stc.Ord Stc.Free Stc.Clo SECSTCTYPING NL.Syn NAMEGEN Stc.Wdef
       SECSTCTYPINGCORRECTNESS TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS)
  (** The chain layer, which is where the environment facts and the
      scheduling step are discharged. *)
  (ChainEnv :
     SECNLUSSTCOBCENV Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       ExtSch Sched Obc.Syn TransNL TransObc SIG SIGPROOFS NAMEGEN
       SECCETYPING SECSTCTYPING SECSTCTYPINGCORRECTNESS SECOBCTYPING
       SECOBCTYPINGCORRECTNESS StcObcBridge).

  Definition ground_instantiation : Type := NLusSupport.ground_instantiation.

  (** ** Low-equivalence on Obc streams

      Obc's [loop_call] carries [option val] streams: [None] where the
      dataflow value was absent.  This is the [option]-valued reading of
      [StcNI.tuple_stream_low_eq] -- two runs agree on every low
      position at which both are present.  Absence is not itself
      constrained, exactly as in the Stc statement, where an [absent]
      slot carries no [nth_error] witness either. *)

  Definition obc_stream_low_eq
    (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
    (xs : list ident) (ins ins' : nat -> list (option val)) : Prop :=
    forall k i x v v',
      nth_error xs i = Some x ->
      NLusSupport.low_var ty_env dlt t x ->
      nth_error (ins k) i = Some (Some v) ->
      nth_error (ins' k) i = Some (Some v') ->
      v = v'.

  (** Two runs agreeing on which of their *low* inputs are present.

      This is not a new demand on the program.  At NLustre and Stc the
      streams carry [value], so [env_low_eq]'s [Env.find x R = Env.find x
      R'] and [tuple_stream_low_eq]'s [v = v'] already force low
      positions to agree on presence -- the requirement is inside the
      low-equivalence relation there, not beside it.  Obc streams carry
      [option val] and [eq_if_present] discards absence entirely, so the
      same content can no longer be carried by the relation and has to be
      written down separately.  It is guarded by [low_var] for exactly
      that reason: anything more would be stronger than what the layers
      above already assume. *)

  Definition same_low_presence
    (ty_env : local_sec_env) (dlt : ground_instantiation) (t : Lat.t)
    (xs : list ident) (xss xss' : stream (list value)) : Prop :=
    forall k i x,
      nth_error xs i = Some x ->
      NLusSupport.low_var ty_env dlt t x ->
      (nth_error (xss k) i = Some absent
       <-> nth_error (xss' k) i = Some absent).

  (** ** What an Obc behaviour of a translated class is

      The dataflow behaviour behind it, plus the two stream
      correspondences [correctness_loop_call] establishes: inputs agree
      wherever the dataflow value is present, outputs are the dataflow
      outputs read through [value_to_option].  [xss]/[yss] stay explicit,
      exactly as in [StcNI.translated_system_behavior] -- the clock
      premise of the Stc theorem is stated over them, so they cannot be
      hidden here. *)

  Definition translated_class_behavior
    (all_nodes : NL.Syn.global) (sys : Stc.Syn.system)
    (xss yss : stream (list value)) (ins outs : nat -> list (option val))
    : Prop :=
    StcNI.translated_system_behavior all_nodes sys xss yss
    /\ (forall n, Forall2 StcObcCorr.eq_if_present (xss n) (ins n))
    /\ (forall n, outs n = List.map StcObcCorr.value_to_option (yss n))
    /\ exists me0,
        Obc.Sem.loop_call
          (TransObc.translate (Sched.schedule (TransNL.translate all_nodes)))
          (Stc.Syn.s_name sys) step ins outs 0 me0.

  (** And it is exactly what the compiler's own correctness theorem
      produces.  Nothing here is new: the scheduler carries the Stc
      behaviour over to the program [Well_defined] can hold of, and
      [correctness_loop_call] does the rest. *)

  Lemma translated_class_behavior_from_system:
    forall all_nodes sys xss yss ins,
      Stc.Wdef.Well_defined (Sched.schedule (TransNL.translate all_nodes)) ->
      Stc.Clo.wc_program (Sched.schedule (TransNL.translate all_nodes)) ->
      StcNI.translated_system_behavior all_nodes sys xss yss ->
      (forall n, Forall2 StcObcCorr.eq_if_present (xss n) (ins n)) ->
      (forall n, List.Exists (fun v => v <> absent) (xss n)) ->
      translated_class_behavior all_nodes sys xss yss ins
        (fun n => List.map StcObcCorr.value_to_option (yss n)).
  Proof.
    intros all_nodes sys xss yss ins Hwd Hwc Hbeh Hins Hclk.
    pose proof Hbeh as Hbeh0.
    destruct Hbeh0 as (M & Hmsem & Hinit & Hloop).
    split; [exact Hbeh|].
    split; [exact Hins|].
    split; [intro n; reflexivity|].
    destruct (StcObcCorr.correctness_loop_call
                (Sched.schedule (TransNL.translate all_nodes))
                (Stc.Syn.s_name sys) xss yss ins (M 0)
                Hwd Hwc
                (Sched.scheduler_initial_state _ _ _ Hinit)
                (Sched.scheduler_loop _ _ _ _ _ _ Hloop)
                Hins Hclk)
      as (me0 & _ & Hloopcall & _).
    exists me0. exact Hloopcall.
  Qed.

  (** The output side of the correspondence is exact -- [outs] is the
      pointwise image of [yss] -- so low-equivalence crosses it in both
      directions.  This is the direction the theorem below needs. *)

  Lemma obc_stream_low_eq_of_tuple_stream_low_eq:
    forall ty_env dlt t xs yss yss' outs outs',
      (forall n, outs n = List.map StcObcCorr.value_to_option (yss n)) ->
      (forall n, outs' n = List.map StcObcCorr.value_to_option (yss' n)) ->
      StcNI.tuple_stream_low_eq ty_env dlt t xs yss yss' ->
      obc_stream_low_eq ty_env dlt t xs outs outs'.
  Proof.
    intros ty_env dlt t xs yss yss' outs outs' Houts Houts' Hlow
           k i x v v' Hnthx Hlowx Hnth Hnth'.
    rewrite Houts in Hnth. rewrite Houts' in Hnth'.
    destruct (nth_error (yss k) i) as [w|] eqn:Hw.
    2:{ assert (Hnone : nth_error
                          (List.map StcObcCorr.value_to_option (yss k)) i = None).
        { apply nth_error_None. rewrite map_length. now apply nth_error_None. }
        rewrite Hnone in Hnth. discriminate. }
    destruct (nth_error (yss' k) i) as [w'|] eqn:Hw'.
    2:{ assert (Hnone : nth_error
                          (List.map StcObcCorr.value_to_option (yss' k)) i = None).
        { apply nth_error_None. rewrite map_length. now apply nth_error_None. }
        rewrite Hnone in Hnth'. discriminate. }
    rewrite (map_nth_error _ _ _ Hw) in Hnth.
    rewrite (map_nth_error _ _ _ Hw') in Hnth'.
    inversion Hnth; clear Hnth.
    inversion Hnth'; clear Hnth'.
    assert (Heq : w = w') by (eapply Hlow; eauto).
    subst w'. congruence.
  Qed.

  (** The input side is not exact: [eq_if_present absent o] holds for
      *every* [o], so an Obc input slot whose dataflow value is absent
      carries no information at all.  Obc-level agreement therefore
      recovers the dataflow-level one only for two runs that agree on
      which inputs are present -- which is a hypothesis about the pair of
      runs, of the same nature as the [eq_str] one the Stc theorem
      already carries, and is stated as such rather than derived. *)

  Lemma tuple_stream_low_eq_of_obc_stream_low_eq:
    forall ty_env dlt t xs xss xss' ins ins',
      (forall n, Forall2 StcObcCorr.eq_if_present (xss n) (ins n)) ->
      (forall n, Forall2 StcObcCorr.eq_if_present (xss' n) (ins' n)) ->
      same_low_presence ty_env dlt t xs xss xss' ->
      obc_stream_low_eq ty_env dlt t xs ins ins' ->
      StcNI.tuple_stream_low_eq ty_env dlt t xs xss xss'.
  Proof.
    intros ty_env dlt t xs xss xss' ins ins' Hins Hins' Habs Hlow
           k i x v v' Hnthx Hlowx Hnth Hnth'.
    destruct v as [|c]; destruct v' as [|c'].
    - reflexivity.
    - apply (Habs k i x Hnthx Hlowx) in Hnth.
      rewrite Hnth in Hnth'. discriminate.
    - apply (Habs k i x Hnthx Hlowx) in Hnth'.
      rewrite Hnth in Hnth'. discriminate.
    - destruct (SecT.Forall2_nth_error_inv
                  _ _ StcObcCorr.eq_if_present (xss k) (ins k) i
                  (present c) (Hins k) Hnth) as (o & Hnto & Ho).
      destruct (SecT.Forall2_nth_error_inv
                  _ _ StcObcCorr.eq_if_present (xss' k) (ins' k) i
                  (present c') (Hins' k) Hnth') as (o' & Hnto' & Ho').
      inversion Ho; subst o.
      inversion Ho'; subst o'.
      f_equal. eapply Hlow; eauto.
  Qed.

  (** ** The Obc-facing theorem

      Same shape as [StcNI.translated_system_noninterference_outputs],
      with the conclusion moved onto the Obc output streams.  The input
      hypothesis stays at the dataflow level: [eq_if_present] says
      nothing at all about an Obc slot whose dataflow value is absent,
      so Obc-level agreement on the inputs is strictly weaker than
      [tuple_stream_low_eq] and cannot replace it without also assuming
      the two runs agree on which inputs are present. *)

  Theorem translated_class_noninterference_outputs:
    forall all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs',
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
        = OK Gsrc ->
      NLCaus.nl_global_causal all_nodes ->
      find_node_env (Stc.Syn.s_name sys) envs = Some ty_env ->
      StcNI.system_security all_nodes Gsrc Gstc envs aux_names sys
        dlt_sig dlt_raw ->
      translated_class_behavior all_nodes sys xss yss ins outs ->
      translated_class_behavior all_nodes sys xss' yss' ins' outs' ->
      eq_str (clock_of xss) (clock_of xss') ->
      StcNI.tuple_stream_low_eq ty_env dlt_sig t
        (List.map fst (Stc.Syn.s_in sys)) xss xss' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst (Stc.Syn.s_out sys)) outs outs'.
  Proof.
    intros all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs'
           Henvsgen Hord Hwc Hallsrc Hcaus Hfindenv
           Hsyssec Hbeh Hbeh' Hclock_eq Hlowin.
    destruct Hbeh as (Hstc & _ & Houts & _).
    destruct Hbeh' as (Hstc' & _ & Houts' & _).
    eapply obc_stream_low_eq_of_tuple_stream_low_eq;
      [exact Houts|exact Houts'|].
    eapply StcNI.translated_system_noninterference_outputs;
      [exact Henvsgen|exact Hord|exact Hwc|exact Hallsrc|exact Hcaus
      |exact Hfindenv|exact Hsyssec|exact Hstc|exact Hstc'
      |exact Hclock_eq|exact Hlowin].
  Qed.

  (** The same statement with both sides phrased over Obc streams, for a
      caller who can supply the presence agreement. *)

  Corollary translated_class_noninterference_outputs_obc:
    forall all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs',
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
        = OK Gsrc ->
      NLCaus.nl_global_causal all_nodes ->
      find_node_env (Stc.Syn.s_name sys) envs = Some ty_env ->
      StcNI.system_security all_nodes Gsrc Gstc envs aux_names sys
        dlt_sig dlt_raw ->
      translated_class_behavior all_nodes sys xss yss ins outs ->
      translated_class_behavior all_nodes sys xss' yss' ins' outs' ->
      eq_str (clock_of xss) (clock_of xss') ->
      same_low_presence ty_env dlt_sig t
        (List.map fst (Stc.Syn.s_in sys)) xss xss' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst (Stc.Syn.s_in sys)) ins ins' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst (Stc.Syn.s_out sys)) outs outs'.
  Proof.
    intros all_nodes Gsrc Gstc envs aux_names sys ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs'
           Henvsgen Hord Hwc Hallsrc Hcaus Hfindenv
           Hsyssec Hbeh Hbeh' Hclock_eq Habs Hlowin.
    pose proof Hbeh as Hbeh0. pose proof Hbeh' as Hbeh0'.
    destruct Hbeh0 as (_ & Hins & _ & _).
    destruct Hbeh0' as (_ & Hins' & _ & _).
    eapply translated_class_noninterference_outputs;
      [exact Henvsgen|exact Hord|exact Hwc|exact Hallsrc|exact Hcaus
      |exact Hfindenv|exact Hsyssec|exact Hbeh|exact Hbeh'|exact Hclock_eq|].
    eapply tuple_stream_low_eq_of_obc_stream_low_eq;
      [exact Hins|exact Hins'|exact Habs|exact Hlowin].
  Qed.

  (** ** Reading the statement off the Obc class

      The theorem above is indexed by the Stc system's interface.  That
      interface is literally the translated class's [step] method's,
      [translate_system] taking [m_in := idty s_in] and [m_out := idty
      s_out] and [schedule_system] copying both, so the conclusion can be
      stated over the class the compiler actually emits without assuming
      anything new. *)

  Lemma translated_class_step_method:
    forall sys,
      Obc.Syn.find_method step
        (TransObc.translate_system (Sched.schedule_system sys)).(Obc.Syn.c_methods)
      = Some (TransObc.step_method (Sched.schedule_system sys)).
  Proof.
    intro sys. apply TransObc.exists_step_method.
  Qed.

  Lemma translated_class_step_interface:
    forall sys stepm,
      Obc.Syn.find_method step
        (TransObc.translate_system (Sched.schedule_system sys)).(Obc.Syn.c_methods)
      = Some stepm ->
      List.map fst stepm.(Obc.Syn.m_in) = List.map fst (Stc.Syn.s_in sys)
      /\ List.map fst stepm.(Obc.Syn.m_out) = List.map fst (Stc.Syn.s_out sys).
  Proof.
    intros sys stepm Hfind.
    rewrite translated_class_step_method in Hfind.
    inversion Hfind; subst stepm.
    split; simpl; apply map_fst_idty.
  Qed.

  (** The Obc-facing statement proper: both stream hypotheses and the
      conclusion are indexed by the emitted class's [step] method. *)

  Corollary translated_class_noninterference_outputs_step:
    forall all_nodes Gsrc Gstc envs aux_names sys cls stepm ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs',
      cls = TransObc.translate_system (Sched.schedule_system sys) ->
      Obc.Syn.find_method step cls.(Obc.Syn.c_methods) = Some stepm ->
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
        = OK Gsrc ->
      NLCaus.nl_global_causal all_nodes ->
      find_node_env (Stc.Syn.s_name sys) envs = Some ty_env ->
      StcNI.system_security all_nodes Gsrc Gstc envs aux_names sys
        dlt_sig dlt_raw ->
      translated_class_behavior all_nodes sys xss yss ins outs ->
      translated_class_behavior all_nodes sys xss' yss' ins' outs' ->
      eq_str (clock_of xss) (clock_of xss') ->
      same_low_presence ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_in)) xss xss' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_in)) ins ins' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_out)) outs outs'.
  Proof.
    intros all_nodes Gsrc Gstc envs aux_names sys cls stepm ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs'
           Hcls Hstepm Henvsgen Hord Hwc Hallsrc Hcaus Hfindenv
           Hsyssec Hbeh Hbeh' Hclock_eq Habs Hlowin.
    subst cls.
    destruct (translated_class_step_interface sys stepm Hstepm) as (Hin & Hout).
    rewrite Hout. rewrite Hin in Hlowin. unfold same_low_presence in Habs.
    rewrite Hin in Habs.
    eapply translated_class_noninterference_outputs_obc;
      [exact Henvsgen|exact Hord|exact Hwc|exact Hallsrc|exact Hcaus
      |exact Hfindenv|exact Hsyssec|exact Hbeh|exact Hbeh'|exact Hclock_eq
      |exact Habs|exact Hlowin].
  Qed.

  (** ** The class-level security witness

      The mirror of [StcNI.system_security], one layer down.  Where that
      one exhibits the NLustre node behind a system together with the
      NLustre-to-Stc head consistency, this one exhibits the system
      behind a class together with the two facts the rest of the chain
      supplies: the scheduling step -- signature preservation from the
      unscheduled accumulator [Gstc] to the scheduled one [Gstcs], which
      is what [generated_signatures_preserved_by_scheduling] produces --
      and the Stc-to-Obc head consistency out of [Gstcs] into [Gobc].

      It is indexed by the system rather than by the class because a
      class does not determine its system: [schedule_tcs] is not
      injective, so two differently-ordered bodies can translate to the
      same class.  Every lookup is nevertheless the class's own, the
      translation preserving names. *)

  Definition class_security
    (all_nodes : NL.Syn.global) (Gsrc Gstc Gstcs Gobc : secglobal)
    (envs : node_scoped_env) (aux_names : list node_aux_names)
    (sys : Stc.Syn.system) (dlt_sig dlt_raw : ground_instantiation) : Prop :=
    exists ssig ssigs osig,
      StcNI.system_security all_nodes Gsrc Gstc envs aux_names sys
        dlt_sig dlt_raw
      /\ SIG.find_signature (Stc.Syn.s_name sys) Gstc = Some ssig
      /\ SIG.find_signature (Stc.Syn.s_name sys) Gstcs = Some ssigs
      /\ signatures_preserved ssig ssigs
      /\ SIG.find_signature (Stc.Syn.s_name sys) Gobc = Some osig
      /\ StcObcBridge.Signature_head_consistent_obc ssigs osig.

  (** And it is exactly what the chain produces.  Every step is a
      theorem proved elsewhere: the Stc witness by
      [StcNI.system_security_from_node_security], the scheduling step by
      [ChainEnv.generated_signatures_preserved_by_scheduling], and the
      last leg by [ChainEnv.generated_program_signatures_preserved_obc_scheduled].
      Nothing is reproved here. *)

  Lemma class_security_from_node_security:
    forall all_nodes Gsrc Gstc Gstcs Gobc envs aux_names n dlt_sig dlt_raw,
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Clo.wc_global all_nodes ->
      Stc.Clo.wc_program (TransNL.translate all_nodes) ->
      Stc.Wdef.Well_scheduled (Sched.schedule (TransNL.translate all_nodes)) ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
        = OK Gsrc ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (TransNL.translate all_nodes) envs aux_names = OK Gstc ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (Sched.schedule (TransNL.translate all_nodes)) envs aux_names = OK Gstcs ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env
        (TransObc.translate (Sched.schedule (TransNL.translate all_nodes)))
        envs aux_names = OK Gobc ->
      find_node n.(NL.Syn.n_name) all_nodes = Some n ->
      NLusNI.node_security all_nodes Gsrc envs aux_names n dlt_sig dlt_raw ->
      class_security all_nodes Gsrc Gstc Gstcs Gobc envs aux_names
        (TransNL.translate_node n) dlt_sig dlt_raw.
  Proof.
    intros all_nodes Gsrc Gstc Gstcs Gobc envs aux_names n dlt_sig dlt_raw
           Henvsgen Hwcnl Hwcstc Hsch Hallsrc Hallstc Hallstcs Hallobc
           Hfindnode Hsec.
    assert (Hsys : StcNI.system_security all_nodes Gsrc Gstc envs aux_names
                     (TransNL.translate_node n) dlt_sig dlt_raw)
      by (eapply StcNI.system_security_from_node_security;
          [exact Henvsgen|exact Hwcnl|exact Hallsrc|exact Hallstc
          |exact Hfindnode|exact Hsec]).
    pose proof Hsys as Hsys0.
    destruct Hsys0 as (n0 & nsig & ssig & _ & _ & _ & Hfindstc & _ & _).
    (* the scheduling step *)
    assert (Hpres : sig_env_preserved Gstc Gstcs).
    { eapply ChainEnv.generated_signatures_preserved_by_scheduling;
        [exact Henvsgen|apply ChainEnv.translate_names|exact Hwcstc|exact Hsch
        |exact Hallstc|exact Hallstcs]. }
    destruct (Hpres _ _ Hfindstc)
      as (ssigs & Hfindstcs & Hpresss & _ & _ & _).
    (* the Stc-to-Obc leg *)
    destruct (ChainEnv.generated_program_signatures_preserved_obc_scheduled
                all_nodes envs aux_names Gstcs Gobc
                Henvsgen (Sched.scheduler_wc_program _ Hwcstc) Hsch
                Hallstcs Hallobc
                (Stc.Syn.s_name (TransNL.translate_node n)) ssigs Hfindstcs)
      as (osig & Hfindobc & Hhead).
    exists ssig, ssigs, osig.
    split; [exact Hsys|].
    split; [exact Hfindstc|].
    split; [exact Hfindstcs|].
    split; [exact Hpresss|].
    split; [exact Hfindobc|exact Hhead].
  Qed.

  Lemma class_security_system:
    forall all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys dlt_sig dlt_raw,
      class_security all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys
        dlt_sig dlt_raw ->
      StcNI.system_security all_nodes Gsrc Gstc envs aux_names sys
        dlt_sig dlt_raw.
  Proof.
    intros all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys dlt_sig dlt_raw
           (ssig & ssigs & osig & Hsys & _).
    exact Hsys.
  Qed.

  (** ** The final Obc theorem

      Same content as [translated_class_noninterference_outputs_step],
      stated against the class-level witness. *)

  Theorem class_noninterference_outputs:
    forall all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys cls stepm ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs',
      cls = TransObc.translate_system (Sched.schedule_system sys) ->
      Obc.Syn.find_method step cls.(Obc.Syn.c_methods) = Some stepm ->
      NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      NL.Ord.Ordered_nodes all_nodes ->
      NL.Clo.wc_global all_nodes ->
      SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
        = OK Gsrc ->
      NLCaus.nl_global_causal all_nodes ->
      find_node_env (Stc.Syn.s_name sys) envs = Some ty_env ->
      class_security all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys
        dlt_sig dlt_raw ->
      translated_class_behavior all_nodes sys xss yss ins outs ->
      translated_class_behavior all_nodes sys xss' yss' ins' outs' ->
      eq_str (clock_of xss) (clock_of xss') ->
      same_low_presence ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_in)) xss xss' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_in)) ins ins' ->
      obc_stream_low_eq ty_env dlt_sig t
        (List.map fst stepm.(Obc.Syn.m_out)) outs outs'.
  Proof.
    intros all_nodes Gsrc Gstc Gstcs Gobc envs aux_names sys cls stepm ty_env
           dlt_sig dlt_raw t xss xss' yss yss' ins ins' outs outs'
           Hcls Hstepm Henvsgen Hord Hwc Hallsrc Hcaus Hfindenv
           Hclssec Hbeh Hbeh' Hclock_eq Habs Hlowin.
    eapply translated_class_noninterference_outputs_step;
      [exact Hcls|exact Hstepm|exact Henvsgen|exact Hord|exact Hwc|exact Hallsrc
      |exact Hcaus|exact Hfindenv
      |eapply class_security_system; exact Hclssec
      |exact Hbeh|exact Hbeh'|exact Hclock_eq|exact Habs|exact Hlowin].
  Qed.

End SECOBCNONINTERFERENCE.

Module SecObcNonInterference
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import CStr  : COINDSTREAMS Op OpAux)
  (Import Str   : INDEXEDSTREAMS Op OpAux)
  (Import CIStr : COINDTOINDEXED Op OpAux CStr Str)
  (Import SC    : SECMONAD Ids)
  (Import SecT  : SECTYPES Lat)
  (Import CE    : COREEXPR Ids Op OpAux Str)
  (Import NL    : NLUSTRE Ids Op OpAux CStr Str CIStr CE)
  (Import Stc   : STC Ids Op OpAux Str CE)
  (Import TransNL : NLustreToStc.Translation.TRANSLATION
                      Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (NLStcCorr : NLustreToStc.Correctness.CORRECTNESS
                 Ids Op OpAux CStr Str CIStr CE NL Stc TransNL)
  (Import SIG          : SIGNATURE Ids SC)
  (Import SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN      : NAMEGEN Ids Op CE.Syn NL.Syn)
  (Import SECCETYPING  : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (NLCaus              : NLUSTRECAUSALITY Ids Op CE.Syn NL.Syn CE.IsF NL.IsF)
  (Import SECNLUSTYPING :
     SECNLUSTYPING Ids Op SC CE.Syn NL.Syn SIG NAMEGEN CE.IsF CE.Clo
       SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo)
  (Import SECNLUSTYPINGCORRECTNESS :
     SECNLUSTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
       NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo
       SECNLUSTYPING)
  (NLusSupport :
     SECNLUSNONINTERFERENCESUPPORT Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG
       NAMEGEN CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD
       NL.IsF NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (NLusNI :
     SECNLUSNONINTERFERENCE Ids Lat Op OpAux SC SecT CE.Syn NL.Syn SIG NAMEGEN
       CE.Typ CE.IsF CE.Clo SECCETYPING Str NL.Ord NL.Mem NL.IsD NL.IsF
       NLCaus NL.Clo CE.Sem CE.Props NL.Sem SIGPROOFS SECNLUSTYPING
       SECNLUSTYPINGCORRECTNESS)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (NLusStcBridge :
     SECNLUSSTCTRANSLATION Ids Lat Op SC SecT CE.Syn NL.Syn Stc.Syn NL.Mem
       TransNL SIG SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING NL.Ord
       NL.IsD NL.IsF NL.Clo SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Stc.Last
       Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING
       SECSTCTYPINGCORRECTNESS)
  (StcNI :
     SECSTCNONINTERFERENCE Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       TransNL NLStcCorr SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI SECSTCTYPING
       SECSTCTYPINGCORRECTNESS NLusStcBridge)
  (** The Obc side proper: syntax, semantics and the translation's own
      correctness theorem, exactly as [NLCorrectness] wires them. *)
  (Import Obc   : OBC Ids Op OpAux)
  (Import TransObc : StcToObc.Translation.TRANSLATION
                       Ids Op OpAux CE.Syn Stc.Syn Obc.Syn)
  (Import Corres : STCMEMORYCORRES Ids Op CE.Syn Stc.Syn Stc.Last)
  (StcObcCorr : StcToObc.Correctness.CORRECTNESS
                  Ids Op OpAux Str CE Stc Obc TransObc Corres)
  (** Velus's own scheduler: the Obc code the compiler emits comes from
      the *scheduled* Stc program, which is the only one [Well_defined]
      can hold of. *)
  (ExtSch : EXT_STCSCHEDULER Ids Op CE.Syn Stc.Syn)
  (Sched : STCSCHEDULE Ids Op OpAux Str CE Stc.Syn Stc.Syst Stc.Ord Stc.Sem
             Stc.Typ Stc.Var Stc.Last Stc.Def Stc.Clo Stc.Free Stc.Wdef ExtSch)
  (** The Stc-to-Obc signature bridge, so that a class's security witness
      can name the Obc signature the way [system_security] names the Stc
      one.  Taken as a parameter, not re-derived. *)
  (SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC Obc.Syn SIG)
  (SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC Obc.Syn Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (StcObcBridge :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CE.Syn Stc.Syn Obc.Syn Lat SecT SIG
       SIGPROOFS CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def Stc.Syst
       Stc.Ord Stc.Free Stc.Clo SECSTCTYPING NL.Syn NAMEGEN Stc.Wdef
       SECSTCTYPINGCORRECTNESS TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS)
  (** The chain layer, which is where the environment facts and the
      scheduling step are discharged. *)
  (ChainEnv :
     SECNLUSSTCOBCENV Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc
       ExtSch Sched Obc.Syn TransNL TransObc SIG SIGPROOFS NAMEGEN
       SECCETYPING SECSTCTYPING SECSTCTYPINGCORRECTNESS SECOBCTYPING
       SECOBCTYPINGCORRECTNESS StcObcBridge)
  <: SECOBCNONINTERFERENCE
       Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc TransNL
       NLStcCorr SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
       SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI
       SECSTCTYPING SECSTCTYPINGCORRECTNESS NLusStcBridge StcNI Obc
       TransObc Corres StcObcCorr ExtSch Sched SECOBCTYPING
       SECOBCTYPINGCORRECTNESS StcObcBridge ChainEnv.
  Include SECOBCNONINTERFERENCE
            Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc TransNL
            NLStcCorr SIG SIGPROOFS NAMEGEN SECCETYPING NLCaus
            SECNLUSTYPING SECNLUSTYPINGCORRECTNESS NLusSupport NLusNI
            SECSTCTYPING SECSTCTYPINGCORRECTNESS NLusStcBridge StcNI Obc
            TransObc Corres StcObcCorr ExtSch Sched SECOBCTYPING
            SECOBCTYPINGCORRECTNESS StcObcBridge ChainEnv.
End SecObcNonInterference.
