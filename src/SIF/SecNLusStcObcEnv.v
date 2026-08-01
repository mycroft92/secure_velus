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
    [generate_node_scoped_env] on NLustre nodes to the Stc systems and
    Obc classes those nodes translate to.  It threads proofs and does
    nothing else -- no new typing rule, no new signature notion. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import Obc.ObcSyntax.
From Velus Require NLustreToStc.Translation.
From Velus Require StcToObc.Translation.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
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

From Coq Require Import List.
Import List.ListNotations.
From compcert Require Import common.Errors.

Module Type SECNLUSSTCOBCENV
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Op)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SynObc: OBCSYNTAX Ids Op OpAux)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import LastStc  : STCISLAST Ids Op CESyn SynStc)
  (Import VarStc   : STCISVARIABLE Ids Op CESyn SynStc)
  (Import DefStc   : STCISDEFINED Ids Op CESyn SynStc VarStc LastStc)
  (Import SystStc  : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc   : STCORDERED Ids Op CESyn SynStc SystStc)
  (Import IsFStc   : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc   : STCCLOCKING Ids Op CESyn SynStc LastStc VarStc DefStc
                       SystStc OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG CEIsF CEClo
                           SECCETYPING LastStc VarStc DefStc SystStc OrdStc
                           IsFStc CloStc)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import WD    : STCWELLDEFINED Ids Op CESyn SynStc SystStc OrdStc VarStc
                    LastStc DefStc CEIsF IsFStc)
  (Import SECSTCTYPINGCORRECTNESS :
     SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecT SIG SIGPROOFS
       NAMEGEN CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc
       IsFStc CloStc WD SECSTCTYPING)
  (TransObc : StcToObc.Translation.TRANSLATION Ids Op OpAux CESyn SynStc SynObc)
  (Import SECOBCTYPING : SECOBCTYPING Ids Op OpAux SC SynObc SIG)
  (Import SECOBCTYPINGCORRECTNESS :
     SECOBCTYPINGCORRECTNESS Ids Op OpAux SC SynObc Lat SecT SIG SIGPROOFS
       SECOBCTYPING)
  (Import SECSTCOBCTRANSLATION :
     SECSTCOBCTRANSLATION Ids Op OpAux SC CESyn SynStc SynObc Lat SecT SIG
       SIGPROOFS CEIsF CEClo SECCETYPING LastStc VarStc DefStc SystStc OrdStc
       IsFStc CloStc SECSTCTYPING SynNL NAMEGEN WD SECSTCTYPINGCORRECTNESS
       TransObc SECOBCTYPING SECOBCTYPINGCORRECTNESS)
  (Import Mem : MEMORIES Ids Op CESyn SynNL)
  (TransNL : NLustreToStc.Translation.TRANSLATION Ids Op CESyn SynNL SynStc Mem).

  (** ** Building a system's windowed environment

      One node of the scoped naming run contributes one system's
      environment together with the state window its names occupy. *)

  Lemma scoped_envs_windowed_step:
    forall envs s n st env rec st' systems,
      find_node_env s.(SynStc.s_name) envs = Some env ->
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
      node list is put side by side with the Stc system list. *)

  Lemma scoped_envs_windowed_from_scoped_env':
    forall prefix nodes systems envs aux_names envs_pref aux_pref st,
      generate_node_scoped_env' prefix (Env.empty _) nil init_state
        = OK ((envs_pref, aux_pref), st) ->
      generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
      Forall2 (fun n s => s.(SynStc.s_name) = n.(n_name)) nodes systems ->
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
        destruct (Env.mem n.(n_name) envs_pref) eqn:Hmem; try discriminate.
        unfold insert_node_env, NMret in Hins.
        inversion Hins. reflexivity. }
      subst st_cur.
      assert (Hfindlocal : find_node_env s.(SynStc.s_name) envs = Some local_env).
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
      Forall2 (fun n s => s.(SynStc.s_name) = n.(n_name)) all_nodes systems ->
      scoped_envs_windowed envs init_state systems.
  Proof.
    intros all_nodes systems envs aux_names Hgen Hnames.
    eapply scoped_envs_windowed_from_scoped_env'
      with (prefix := nil) (envs_pref := Env.empty _) (aux_pref := nil);
      [reflexivity|exact Hgen|exact Hnames].
  Qed.

  (** ** Discharging the alignment

      [translate_node] copies the node's name, so the two lists line up
      by construction.  This is the fact every layer below was assuming. *)

  Lemma translate_names:
    forall nodes,
      Forall2 (fun n s => s.(SynStc.s_name) = n.(n_name))
              nodes (TransNL.translate nodes).
  Proof.
    induction nodes as [|n nodes IH]; simpl; constructor; auto.
  Qed.

  Corollary scoped_envs_windowed_translate:
    forall all_nodes envs aux_names,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      scoped_envs_windowed envs init_state (TransNL.translate all_nodes).
  Proof.
    intros all_nodes envs aux_names Hgen.
    eapply scoped_envs_windowed_from_scoped_env;
      [exact Hgen|apply translate_names].
  Qed.

  (** ** The chain-level statement

      The Stc-to-Obc lookup theorem with its environment hypotheses
      discharged: everything is now expressed in terms of the one naming
      run over the source program. *)

  Theorem generated_program_signatures_preserved_obc_chain:
    forall all_nodes envs aux_names G1 G2,
      generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
      CloStc.wc_program (TransNL.translate all_nodes) ->
      WD.Well_scheduled (TransNL.translate all_nodes) ->
      SECSTCTYPING.generate_all_sys_signatures_scoped_env
        (TransNL.translate all_nodes) envs aux_names = OK G1 ->
      SECOBCTYPING.generate_all_class_signatures_scoped_env
        (TransObc.translate (TransNL.translate all_nodes)) envs aux_names = OK G2 ->
      forall f stcsig,
        SIG.find_signature f G1 = Some stcsig ->
        exists obcsig,
          SIG.find_signature f G2 = Some obcsig
          /\ Signature_head_consistent_obc stcsig obcsig.
  Proof.
    intros all_nodes envs aux_names G1 G2 Hgen Hwc Hsch Hstc Hobc.
    eapply generated_program_signatures_preserved_obc_global;
      [eapply scoped_envs_windowed_translate; exact Hgen
      |eapply aux_naming_props_from_scoped_env; exact Hgen
      |exact Hwc|exact Hsch|exact Hstc|exact Hobc].
  Qed.

End SECNLUSSTCOBCENV.
