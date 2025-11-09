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

    Lemma find_env_consistent: forall x env st1 st2 st3 st4 xty xty2, 
      find_env x env st1 = OK (xty, st2) ->
      find_env x env st3 = OK (xty2, st4) -> xty = xty2.
    Proof.
      intros. unfold find_env in *.
      destruct (Env.find x env) eqn:findx1; inversion H; inversion H0.
      now subst.
    Qed.

(* Need to say that find_env i env on same state gives same ident, add clocks as well here*)
    Definition Signature_consistent (G1 G2: secglobal) : Prop :=
      forall f n1 n2, SECNLUSTYPING.find_signature f G1 = Some n1 -> (SECSTCTYPING.find_signature f G2 = Some n2) /\ n1.(s_in) = n2.(s_in) /\ n2.(s_out) = n2.(s_out) /\ n1.(s_reset) = n2.(s_reset) /\ n1.(s_clk) = n2.(s_clk) /\ (forall dlt, listSatisfiable dlt n1.(s_constraints) -> listSatisfiable dlt n2.(s_constraints)).
    Hint Unfold Signature_consistent.
    
    Ltac myMonadInv :=
      simpl in *;
      try (unfold error in *);
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

    Theorem eqn_preserv: 
    (* The signature consistency should make it easier in node-sec level preservation*)
    (* 1. Signatures consistency on inp, out, clk, rst.*)
    (* 2. The inits need to be "aligned", it is not necessary that they match because stc's fresh names are different from nlus's *)
    forall (G1 G2: secglobal), Signature_consistent G1 G2 ->
    forall (e: equation) (trs: list trconstr), translate_eqn e = trs ->
    forall (env rst_env: Env.t ident)
           (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
           (generate_eqn_constraint G1 env base_ty rst_ty e init_state1) = OK (nconst, st1) ->
           (generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2) = OK (sconst, st2) ->
        forall (dlt: ident -> Lat.t), listSatisfiable dlt nconst -> listSatisfiable dlt sconst.
    Proof.
      induction e; intros; 
       repeat myMonadInv.
       (*cexp case*)
       1:{eapply find_env_consistent in Hbind0; eauto. subst. unfold option_to_sec in *. destruct (assign_clk_type env base_ty c) eqn:clkty; destruct (assign_cexp_type env c0) eqn:cexpty;repeat myMonadInv;  now subst. }
       (* fby case*)
       2:{ eapply find_env_consistent in Hbind0; eauto. subst. unfold option_to_sec in *. destruct (assign_clk_type env base_ty c) eqn:clkty; destruct (assign_exp_type env e) eqn:cexpty;repeat myMonadInv;  now subst. }
      
      - simpl in H. destruct o eqn:rsto. destruct l; subst; simpl in H1.
        * repeat myMonadInv. now unfold listSatisfiable. 
        * destruct p. unfold translate_eqn in H2. unfold generate_trconstrs_constraints in H1. repeat myMonadInv.    
        * unfold translate_eqn in H0. destruct l eqn:Hl; subst trs; simpl in H2.
          +  inversion H2. now unfold listSatisfiable.
          +  repeat myMonadInv. unfold listSatisfiable. rewrite Forall_app. split; auto. unfold Signature_consistent in H.
          destruct (SECNLUSTYPING.find_signature i G1) eqn:HNLnodefind; destruct (SECSTCTYPING.find_signature i G2) eqn:HSTCsysfind; repeat myMonadInv.
          
          (*Need some auxiliary result here for call preservation with substitution?*)

    Admitted.

    Lemma eqns_preserv: forall (G1 G2: secglobal), Signature_consistent G1 G2 ->
    forall (es: list equation) (trs: list trconstr), translate_eqns es = trs ->
    forall (env rst_env: Env.t ident)
           (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
           (generate_eqns_constraints G1 env base_ty rst_ty es init_state1) = OK (nconst, st1) ->
           (generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2) = OK (sconst, st2) ->
        forall (dlt: ident -> Lat.t), listSatisfiable dlt nconst -> listSatisfiable dlt sconst.
    Proof.
      induction es; intros. 
      - repeat myMonadInv. unfold listSatisfiable. auto.
      - unfold translate_eqns in H0. simpl in H0,H1,H2. repeat myMonadInv. 

      eapply generate_tr_constraints_inv in H2. destruct H2 as (aeqncons & st' & eseqncons & [Hgen_a [Hgen_es Hscons]]). rewrite Hscons. unfold listSatisfiable. apply Forall_app in H3.  
      apply Forall_app. destruct H3 as [HNLa HNLind]. split. 
      * eapply (eqn_preserv G1 G2 H a (translate_eqn a) _ env rst_env base_ty rst_ty x aeqncons _ _); eauto. 
      * eapply IHes; eauto.
      Unshelve. eauto. (*obvious goal coming from translate_eqn a*)
    Qed.
      
  (* Should I split trs into multiple parts and then have results on generate_trconstrs_constraints .... (trs++trs') .. = generate_trconstrs_constraints .... trs .. ++ generate_trconstrs_constraints .... trs' ..??*)



  End SECEQNPRES. 

  Section NODESYSPRES.

   Ltac myMonadInv :=
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
    | H: bind ?x ?f ?st = OK ?p |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK ?p|- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.

  Ltac matchMonadInv :=
    
    match goal with
    | H: (match ?x with
          | OK _ => _ 
          | Error _ => _ end) = OK _ |- _ => 
      let H1 := fresh "Hmat" in
       destruct x eqn:H1; repeat myMonadInv
  
    | H: (match ?x with
          | OK _ => _ 
          | Error _ => _ end) = Error _ |- _ => 
      let H1 := fresh "Hmat" in
       destruct x eqn:H1; repeat myMonadInv
    (* | H: context [match ?x with
          | OK _ => _ 
          | Error _ => _ end] |- _ => 
      let H1 := fresh "Hmat" in
       destruct x eqn:H1; repeat monadInv *)
    end.    

    Locate monadInv.
    Theorem node_preserv: forall (n : node) (s: system), translate_node n = s 
      -> forall (G1 G2: secglobal), Signature_consistent G1 G2 
      -> forall (nsig: signature), 
            generate_node_signature G1 n = OK nsig 
      -> forall (ssig: signature),
            generate_system_signature G2 s = OK ssig
      (*Interface types are the same*)
      -> forall (dlt: ident -> Lat.t), listSatisfiable dlt (nsig.(s_constraints))
      -> listSatisfiable dlt (ssig.(s_constraints)).
    Proof.
       unfold Signature_consistent. intros. unfold translate_node in H. unfold generate_node_signature in H1. unfold generate_system_signature in H2. repeat matchMonadInv.
      
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

