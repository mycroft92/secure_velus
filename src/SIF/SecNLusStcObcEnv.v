(** Environment threading for the NLustre-Stc-Obc chain.

    The security naming pass runs once, over NLustre nodes.  Every layer
    below it then needs the same handful of facts about the environments
    that pass produced -- which environment belongs to which system or
    class, that its names are freshly minted, and where they sit
    relative to the names generated before and after.

    Each layer states its theorems against those facts rather than
    against the naming run, so that no layer has to mention the syntax
    of the layer above it.  This module is where the facts are actually
    discharged: it sees the whole chain, so it can connect
    [generate_node_scoped_env] on NLustre nodes to the Stc systems --
    scheduled or not -- and the Obc classes those nodes give rise to.
    It threads proofs and does nothing else: no new typing rule, no new
    signature notion, and no property of the compiler's own passes that
    those passes do not already prove. *)

From Coq Require Import List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindToIndexed.
From Velus Require Import CoreExpr.
From Velus Require Import NLustre.
From Velus Require Import Stc.
From Velus Require Import Stc.StcSchedule.
From Velus Require Import Obc.ObcSyntax.
From Velus Require NLustreToStc.Translation.
From Velus Require StcToObc.Translation.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import SIF.SecObcTyping.
From Velus Require Import SIF.SecObcTypingCorrectness.
From Velus Require Import SIF.SecStcObcTranslation.

From compcert Require Import common.Errors.

Module Type SECNLUSSTCOBCENV
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
  (** Velus's own scheduler, exactly as the [STC] bundle declares it.
      Only its name-preservation lemma is used here. *)
  (ExtSch : EXT_STCSCHEDULER Ids Op CE.Syn Stc.Syn)
  (Sched : STCSCHEDULE Ids Op OpAux Str CE Stc.Syn Stc.Syst Stc.Ord Stc.Sem
             Stc.Typ Stc.Var Stc.Last Stc.Def Stc.Clo Stc.Free Stc.Wdef ExtSch)
  (** Only Obc's syntax: nothing here needs its semantics or typing. *)
  (Import SynObc : OBCSYNTAX Ids Op OpAux)
  (TransNL  : NLustreToStc.Translation.TRANSLATION Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (TransObc : StcToObc.Translation.TRANSLATION Ids Op OpAux CE.Syn Stc.Syn SynObc)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CE.Syn NL.Syn)
  (Import SECCETYPING : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (StcObcBridge :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CE.Syn Stc.Syn SynObc Lat SecT SIG
       SIGPROOFS CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def Stc.Syst
       Stc.Ord Stc.Free Stc.Clo SECSTCTYPING NL.Syn NAMEGEN Stc.Wdef
       SECSTCTYPINGCORRECTNESS TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS).

  (** ** Building a system's windowed environment

      One node of the scoped naming run contributes one system's
      environment together with the state window its names occupy. *)

  Lemma scoped_envs_windowed_step:
    forall envs s n st env rec st' systems,
      find_node_env s.(Stc.Syn.s_name) envs = Some env ->
      generate_local_env_for_node n st = OK ((env, rec), st') ->
      scoped_envs_windowed envs st' systems ->
      scoped_envs_windowed envs st (s :: systems).
  Proof.
    intros envs s n st env rec st' systems Hfind Hlocal Htail.
    econstructor;
      [exact Hfind
      |eapply env_naming_props_from_local_env; eauto
      |eapply env_sec_window_from_local_env; eauto
      |exact Htail].
  Qed.

  (** The whole run, walked once.  This is the only place the NLustre
      node list is put side by side with a list of Stc systems. *)

  Lemma scoped_envs_windowed_from_scoped_env':
    forall prefix nodes systems envs aux_names envs_pref aux_pref st,
      generate_node_scoped_env' prefix (Env.empty _) nil init_state
        = OK ((envs_pref, aux_pref), st) ->
      generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name)) nodes systems ->
      scoped_envs_windowed envs st systems.
  Proof.
    intros prefix nodes.
    revert prefix.
    induction nodes as [|n nodes IH];
      intros prefix systems envs aux_names envs_pref aux_pref st
             Hprefgen Henvsgen Hnames.
    - inversion Hnames; subst systems. constructor.
    - inversion Hnames as [|n' s ns systems' Hname Hnames']; subst n' ns systems.
      pose proof Henvsgen as Henvsgen_full.
      unfold generate_node_scoped_env in Henvsgen_full.
      destruct (generate_node_scoped_env' (prefix ++ n :: nodes)
                  (Env.empty _) nil init_state)
        as [[[envs_full aux_full] st_full]|] eqn:Hrun; try discriminate.
      inversion Henvsgen_full; subst envs_full aux_full; clear Henvsgen_full.
      edestruct generate_node_scoped_env'_split_node
        as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
            & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
        eauto.
      rewrite Hprefgen in Hpref.
      inversion Hpref; subst envs_pref' aux_pref' st_pref.
      assert (Hcur : st_cur = st_local).
      { unfold fresh_insert_node_env in Hins.
        destruct (Env.mem n.(NL.Syn.n_name) envs_pref) eqn:Hmem; try discriminate.
        unfold insert_node_env, NMret in Hins.
        inversion Hins. reflexivity. }
      subst st_cur.
      assert (Hfindlocal :
                find_node_env s.(Stc.Syn.s_name) envs = Some local_env).
      { rewrite Hname.
        eapply generate_node_scoped_env'_preserves_find; eauto.
        eapply fresh_insert_node_env_finds_new; eauto. }
      eapply scoped_envs_windowed_step; [exact Hfindlocal|exact Hlocal|].
      (* step the prefix by one node and recurse *)
      assert (Hstep :
                generate_node_scoped_env' (n :: nil) envs_pref aux_pref st
                = OK ((envs_cur, rec :: aux_pref), st_local)).
      { simpl. unfold NMbind2. rewrite Hlocal. simpl.
        unfold NMbind. rewrite Hins. simpl. reflexivity. }
      assert (Hprefgen' :
                generate_node_scoped_env' (prefix ++ n :: nil)
                  (Env.empty _) nil init_state
                = OK ((envs_cur, rec :: aux_pref), st_local))
        by (eapply generate_node_scoped_env'_app; eauto).
      assert (Henvsgen' :
                generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes)
                = OK (envs, aux_names)).
      { assert (Heqlist : (prefix ++ n :: nil) ++ nodes = prefix ++ n :: nodes).
        { clear - prefix n nodes.
          induction prefix as [|a prefix IHprefix]; simpl;
            [reflexivity|now f_equal]. }
        rewrite Heqlist. exact Henvsgen. }
      eapply IH; eauto.
  Qed.

  Lemma scoped_envs_windowed_from_scoped_env:
    forall all_nodes systems envs aux_names,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name)) all_nodes systems ->
      scoped_envs_windowed envs init_state systems.
  Proof.
    intros all_nodes systems envs aux_names Hgen Hnames.
    eapply scoped_envs_windowed_from_scoped_env'
      with (prefix := nil) (envs_pref := Env.empty _) (aux_pref := nil);
      [reflexivity|exact Hgen|exact Hnames].
  Qed.

  (** ** Discharging the alignment along the chain

      [translate_node] copies the node's name, and [schedule_system]
      keeps every field but [s_tcs] -- the latter is Velus's own
      [Scheduler.schedule_system_name], used here rather than restated.
      So the alignment every layer below was assuming holds both before
      and after scheduling. *)

  Lemma translate_names:
    forall nodes,
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name))
              nodes (TransNL.translate nodes).
  Proof.
    induction nodes as [|n nodes IH]; simpl; constructor; auto.
  Qed.

  Lemma schedule_names:
    forall nodes systems,
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name)) nodes systems ->
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name))
              nodes (Sched.schedule systems).
  Proof.
    intros nodes systems Hnames.
    induction Hnames as [|n s nodes' systems' Hname Hnames' IH].
    - constructor.
    - simpl. constructor; [|exact IH].
      first [now rewrite Sched.schedule_system_name | exact Hname].
  Qed.

  Corollary scheduled_translate_names:
    forall nodes,
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name))
              nodes (Sched.schedule (TransNL.translate nodes)).
  Proof.
    intro nodes. apply schedule_names, translate_names.
  Qed.

  (** ** The chain-level statement

      Stated for any Stc program whose systems carry the source nodes'
      names.  That matters: the compiler does not hand
      [translate all_nodes] to the Obc pass, it hands over
      [schedule (translate all_nodes)] (see [NLCorrectness.nl_to_cl]),
      and [Well_scheduled] holds only after that pass.  The corollary
      below instantiates it at the program the compiler reaches. *)

  Theorem generated_program_signatures_preserved_obc_chain:
    forall all_nodes systems envs aux_names G1 G2,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      Forall2 (fun n s => s.(Stc.Syn.s_name) = n.(NL.Syn.n_name)) all_nodes systems ->
      Stc.Clo.wc_program systems ->
      Stc.Wdef.Well_scheduled systems ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env systems envs aux_names
        = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env
        (TransObc.translate systems) envs aux_names = OK G2 ->
      forall f stcsig,
        SIG.find_signature f G1 = Some stcsig ->
        exists obcsig,
          SIG.find_signature f G2 = Some obcsig
          /\ StcObcBridge.Signature_head_consistent_obc stcsig obcsig.
  Proof.
    intros all_nodes systems envs aux_names G1 G2 Hgen Hnames Hwc Hsch Hstc Hobc.
    eapply StcObcBridge.generated_program_signatures_preserved_obc_global;
      [eapply scoped_envs_windowed_from_scoped_env; [exact Hgen|exact Hnames]
      |eapply aux_naming_props_from_scoped_env; exact Hgen
      |exact Hwc|exact Hsch|exact Hstc|exact Hobc].
  Qed.

  (** The instance the compiler actually reaches. *)

  Corollary generated_program_signatures_preserved_obc_scheduled:
    forall all_nodes envs aux_names G1 G2,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      Stc.Clo.wc_program (Sched.schedule (TransNL.translate all_nodes)) ->
      Stc.Wdef.Well_scheduled
        (Sched.schedule (TransNL.translate all_nodes)) ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (Sched.schedule (TransNL.translate all_nodes)) envs aux_names
        = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env
        (TransObc.translate
           (Sched.schedule (TransNL.translate all_nodes)))
        envs aux_names = OK G2 ->
      forall f stcsig,
        SIG.find_signature f G1 = Some stcsig ->
        exists obcsig,
          SIG.find_signature f G2 = Some obcsig
          /\ StcObcBridge.Signature_head_consistent_obc stcsig obcsig.
  Proof.
    intros all_nodes envs aux_names G1 G2 Hgen Hwc Hsch Hstc Hobc.
    eapply generated_program_signatures_preserved_obc_chain;
      [exact Hgen|apply scheduled_translate_names
      |exact Hwc|exact Hsch|exact Hstc|exact Hobc].
  Qed.

End SECNLUSSTCOBCENV.

Module SecNLusStcObcEnv
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
  (** Velus's own scheduler, exactly as the [STC] bundle declares it.
      Only its name-preservation lemma is used here. *)
  (ExtSch : EXT_STCSCHEDULER Ids Op CE.Syn Stc.Syn)
  (Sched : STCSCHEDULE Ids Op OpAux Str CE Stc.Syn Stc.Syst Stc.Ord Stc.Sem
             Stc.Typ Stc.Var Stc.Last Stc.Def Stc.Clo Stc.Free Stc.Wdef ExtSch)
  (Import SynObc : OBCSYNTAX Ids Op OpAux)
  (TransNL  : NLustreToStc.Translation.TRANSLATION Ids Op CE.Syn NL.Syn Stc.Syn NL.Mem)
  (TransObc : StcToObc.Translation.TRANSLATION Ids Op OpAux CE.Syn Stc.Syn SynObc)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CE.Syn NL.Syn)
  (Import SECCETYPING : SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo)
  (Import SECSTCTYPING :
     SECSTCTYPING Ids Op SC CE.Syn Stc.Syn SIG CE.IsF CE.Clo SECCETYPING
       Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CE.Syn NL.Syn Stc.Syn Lat SecT SIG
       SIGPROOFS NAMEGEN CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def
       Stc.Syst Stc.Ord Stc.Free Stc.Clo Stc.Wdef SECSTCTYPING)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (StcObcBridge :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CE.Syn Stc.Syn SynObc Lat SecT SIG
       SIGPROOFS CE.IsF CE.Clo SECCETYPING Stc.Last Stc.Var Stc.Def Stc.Syst
       Stc.Ord Stc.Free Stc.Clo SECSTCTYPING NL.Syn NAMEGEN Stc.Wdef
       SECSTCTYPINGCORRECTNESS TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS)
  <: SECNLUSSTCOBCENV Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc ExtSch Sched SynObc
       TransNL TransObc SIG SIGPROOFS NAMEGEN SECCETYPING SECSTCTYPING
       SECSTCTYPINGCORRECTNESS SECOBCTYPING SECOBCTYPINGCORRECTNESS
       StcObcBridge.

Include SECNLUSSTCOBCENV Ids Lat Op OpAux CStr Str CIStr SC SecT CE NL Stc ExtSch Sched
  SynObc TransNL TransObc SIG SIGPROOFS NAMEGEN SECCETYPING SECSTCTYPING
  SECSTCTYPINGCORRECTNESS SECOBCTYPING SECOBCTYPINGCORRECTNESS StcObcBridge.

End SecNLusStcObcEnv.
