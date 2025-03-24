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
Locate find_env .
Print error.
Ltac monadInv :=
    simpl in *;
    unfold error in *;
    match goal with
    | H: OK _ = OK _ |- _ =>
      inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
      discriminate
    | H: ret _ _ = _ |- _ =>
      unfold ret in H
    | H: bind ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.


    Lemma find_env_consistent: forall x env st1 st2 st3 st4 xty xty2, 
      find_env x env st1 = OK (xty, st2) ->
      find_env x env st3 = OK (xty2, st4) -> xty = xty2.
    Proof.
      intros. unfold find_env in *.
      destruct (Env.find x env) eqn:findx1; inversion H; inversion H0.
      now subst.
    Qed.
Locate Env.
(* Need to say that find_env i env on same state gives same ident*)
    Definition Signature_consistent (G1 G2: secglobal) : Prop :=
      forall f n1 n2, find_signature f G1 = Some n1 -> (find_signature f G2 = Some n2) /\ n1.(s_in) = n2.(s_in) /\ n2.(s_out) = n2.(s_out) /\ (forall dlt, listSatisfiable dlt n1.(s_constraints) -> listSatisfiable dlt n2.(s_constraints)).

    Theorem eqn_preserv: 
    (* The signature consistency should make it easier in node-sec level preservation*)
    forall (G1 G2: secglobal), Signature_consistent G1 G2 ->
    forall (e: equation) (trs: list trconstr), translate_eqn e = trs ->
    forall (env rst_env: Env.t ident)
           (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state st1 st2: sec_state),
           (generate_eqn_constraint G1 env base_ty rst_ty e init_state) = OK (nconst, st1) ->
           (generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state) = OK (sconst, st2) ->
        forall (dlt: ident -> Lat.t), listSatisfiable dlt nconst -> listSatisfiable dlt sconst.
    Proof.
      induction e; intros; 
       repeat monadInv.
       (*cexp case*)
       1:{eapply find_env_consistent in Hbind0; eauto. subst. unfold option_to_sec in *. destruct (assign_clk_type env base_ty c) eqn:clkty; destruct (assign_cexp_type env c0) eqn:cexpty;repeat monadInv;  now subst. }
       (* fby case*)
       2:{ eapply find_env_consistent in Hbind0; eauto. subst. unfold option_to_sec in *. destruct (assign_clk_type env base_ty c) eqn:clkty; destruct (assign_exp_type env e) eqn:cexpty;repeat monadInv;  now subst. }
      
      - simpl in H. destruct o eqn:rsto. destruct l; subst; simpl in H1.
        * repeat monadInv. now unfold listSatisfiable. 
        * destruct p. unfold generate_trconstrs_constraints in H1. repeat monadInv.  (*Need some auxiliary result here for call preservation?*)  
        *


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
        intros. induction e as [x ck cexp| xs ck f es [[rst rck]|] | x ck c0 exp ]; simpl in H; subst; simpl;
        destruct (assign_clk_type env base_ty ck) eqn:ck_typ_eqn; simpl.
        - destruct (assign_cexp_type env cexp) eqn:cexp_typ_eqn; subst;simpl.
          * destruct (SECNLUSTYPING.find_env x env) eqn:find_x_eqn; simpl.
       

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

