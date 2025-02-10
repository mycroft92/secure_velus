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
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Module Type SECNLUSSTCTRANSLATION 
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import SecTypes : SECTYPES Lat)
  (Import CESyn    : CESYNTAX      Op)
  (Import SynNL    : NLSYNTAX  Ids Op CESyn)
  (Import SynStc   : STCSYNTAX Ids Op CESyn)
  (Import Mem      : MEMORIES  Ids Op CESyn SynNL)
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
(* Check (generate_eqn_constraint _ _ _ _ _) _.
Check res. *)
    (* Type preservation for each equation -> trconstr *)
    (** G1 G2 are needed? how does the inductive argument work here?*)
    (** Do I need to bring in nodes and systems as well? Or is it just signatures? *)
    (* I don't need more than one G right?, I can say equivalence at node-system level?*)
    (* Lemma eqn_trconstr_consitent: forall (e:equation) (trs: list trconstr), translate_eqn e = trs
      -> forall (G: secglobal) 
                (env rst_env: Env.t ident)
                (base_ty rst_ty: ident),
          (match generate_eqn_constraint G env base_ty rst_ty e init_state with
          | OK _ => True
          | Error _ => 
            (match generate_trconstrs_constraints G env rst_env base_ty rst_ty trs init_state with 
              | OK _ => False
              | Error _ => True
            end)
          end).
      Proof.
        Admitted. *)

    Theorem eqn_preserv: forall (e: equation) (trs: list trconstr), translate_eqn e = trs 
      -> forall (G: secglobal) 
                (env rst_env: Env.t ident)
                (base_ty rst_ty: ident)
                (nconst sconst: list constraint)
                (init_state: sec_state),
      (*Need to express that these generation two monads start in the same state*)
         match generate_eqn_constraint G env base_ty rst_ty e init_state with
         | OK (nconst ,_) => 
            (match generate_trconstrs_constraints G env rst_env base_ty rst_ty trs init_state with
            | OK (sconst, _) => forall (dlt: ident -> Lat.t), listSatisfiable dlt nconst -> listSatisfiable dlt sconst
            | Error _ => False end)
          | Error _ => True
          end.
      Proof.
        intros. induction e; simpl in H; subst.
        - simpl.
       

        Admitted.
      (* Qed. *)


  End SECEQNPRES. 

  Section NODESYSPRES.
    Theorem node_preserv: forall (n : node) (s: system), translate_node n = s 
      -> forall (G: secglobal) (nsig: signature), 
            generate_node_signature G n = OK nsig 
      -> forall (ssig: signature),
            generate_system_signature G s = OK ssig
      (*Interface types are the same*)
      -> forall (dlt: ident -> Lat.t), listSatisfiable dlt (nsig.(s_constraints))
      -> listSatisfiable dlt (ssig.(s_constraints)).
      (* (match generate_node_signature G n with 
       | OK nsig => forall (ssig: signature), 
          (match generate_system_signature G s with
           | OK ssig =>  forall (dlt: ident -> Lat.t), listSatisfiable dlt (nsig.(s_constraints))
                    -> listSatisfiable dlt (ssig.(s_constraints))
           | Error _ => False
           end)
       | Error _ => True
       end). *)
    Proof.
      Admitted.


  End NODESYSPRES.



End SECNLUSSTCTRANSLATION.


Module SecNLusStcTranslation 
  (Ids   : IDS)
  (Lat   : Lattice)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (SecTypes : SECTYPES Lat)
  (CESyn : CESYNTAX Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SynStc: STCSYNTAX Ids Op CESyn)
  (Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (SIG          : SIGNATURE   Ids SC)
  (SECCETYPING  : SECCETYPING Ids Op CESyn)
  (SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG SECCETYPING)
  (SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING) <: SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG SECCETYPING SECNLUSTYPING SECSTCTYPING.

  Include SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG SECCETYPING SECNLUSTYPING SECSTCTYPING.
End SecNLusStcTranslation.

