(*** Main translation related theorems.
   - For translationof equation
   - Signature preservation at node level *)
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import SIF_fresh.SecCETyping.
From Velus Require Import SIF_fresh.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF_fresh.SecNLusTyping.
From Velus Require Import SIF_fresh.SecSTCTyping.
From Velus Require Import NLustreToStc.Translation.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Module Type SECNLUSSTCTRANSLATION 
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Import Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (Import SIG          : SIGNATURE   Ids SC)
  (Import SECCETYPING  : SECCETYPING Ids Op CESyn)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING).

  Section SECCEPRES.

  End SECCEPRES.
  Check generate_eqn_constraint. 
  Check generate_trconstrs_constraints.
  (** Thoughts:
    - Need secglobal to be properly setup with goodness constraint
    - Need rst_env with goodness constraints
  *)
  Section SECEQNPRES.

    (* Type preservation for each equation -> trconstr *)
    (** G1 G2 are needed, how does the inductive argument work here?*)
    (** Do I need to bring in nodes and systems as well? Or is it just signatures? *)
    (*  forall G eq tcs bk H M Is vars insts,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      NL.Clo.wc_equation G vars eq ->
      CE.Sem.sem_clocked_vars bk H vars ->
      translate_eqn_nodup_subs eq tcs ->
      (forall n, state_closed_insts (translate G) insts (Is n)) ->
      (forall n, forall x, find_val x (Is n) = None) ->
      msem_equation G bk H M eq ->
      sem_trconstrs_n (translate G) bk H M Is (next M) tcs ->
      exists Is',
        sem_trconstrs_n (translate G) bk H M Is' (next M) (translate_eqn eq ++ tcs)
        /\ (forall n, state_closed_insts (translate G) (gather_inst_eq eq ++ insts) (Is' n))
       /\ forall n x, find_val x (Is' n) = None. *)

    Theorem eqn_preservation: forall (e:equation) (trs: list trconstr), translate_eqn e = trs 
      -> forall (G1 G2: secglobal)
              (env: Env.t ident) 
              (base_ty rst_ty: ident)
              (nconst sconst: list constraint),
          generate_eqn_constraint G1 env base_ty rst_ty e = nconst
      ->  generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs = sconst. 

  End SECEQNPRES. 



End SECNLUSSTCTRANSLATION.


Module SecNLusStcTranslation 
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SynStc: STCSYNTAX Ids Op CESyn)
  (Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (SIG          : SIGNATURE   Ids SC)
  (SECCETYPING  : SECCETYPING Ids Op CESyn)
  (SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING)
  (SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING) <: SECNLUSSTCTRANSLATION Ids Op SC CESyn SynNL SynStc Mem Translation SIG SECCETYPING SECNLUSTYPING SECSTCTYPING.

  Include SECNLUSSTCTRANSLATION Ids Op SC CESyn SynNL SynStc Mem Translation SIG SECCETYPING SECNLUSTYPING SECSTCTYPING.
End SecNLusStcTranslation.

