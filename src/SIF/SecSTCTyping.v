
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.

Module Type SECSTCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).
  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x'
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  Section RESETHANDLER.
  (** This section collects STC reset statements and assigns one fresh
      reset-instance type variable to each translated reset call. *)
  Fixpoint collect_reset_stmts' (trl: list trconstr) (acc: list trconstr) : list trconstr :=
    match trl with
    | [] => acc
    | tr::trl' => 
      (match tr with
        | TcReset _ _ _ => collect_reset_stmts' trl' (acc ++ [tr])
        | _             => collect_reset_stmts' trl' acc
        end)
    end.

  Definition collect_reset_stmts trl := collect_reset_stmts' trl [].

  (* Reset-instance type variables are STC-specific auxiliaries.
     Keep them in their own namespace so they never clash with the
     shared NLustre/STC interface/local type variables. *)
  Definition fresh_reset_ident : Sec ident :=
    fun n =>
      let id := Ids.gensym Ids.sec_reset n in
      OK (id, Pos.succ n).

  Definition fresh_reset_insert (k: ident) (env: Env.t ident): Sec (Env.t ident * ident) :=
    if Env.mem k env then
      error (MSG "Key declared more than once " :: [CTX k])
    else
      do v <- fresh_reset_ident;
      do e <- insert_env k v env;
      ret (e, v).

  (* Insert one reset-instance type variable for a translated [TcReset]. *)
  Definition assign_reset_type (tr: trconstr) (env: Env.t ident) : Sec (Env.t ident * ident) :=
    match tr with
    | TcReset x ck f => fresh_reset_insert x env
    | _ => error (msg "Not a reset statement! ")
    end. 

  Fixpoint generate_reset_env' (trl: list trconstr) (env: Env.t ident) (acc: list ident): Sec (Env.t ident * list ident) :=
    match trl with
    | [] => ret (env, acc)
    | t :: trl => 
       (match t with
        | TcReset _ _ _ => 
             do (env',i)   <- assign_reset_type  t env; 
             generate_reset_env' trl env' (acc++[i])
        | _  => generate_reset_env' trl env acc
        end)
     end.
  
  Definition generate_reset_env trl : Sec (Env.t ident * list ident) := generate_reset_env' trl (Env.empty _) [].
  End RESETHANDLER.

  (** STC translated-constraint typing in the shared naming environment plus
      the STC-only reset-instance environment. *)
  Section SECTRCONSTRTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable reset_env: Env.t ident.
    Variable base_ty: ident.
    Variable rst_ty : ident.

    Definition generate_trconstr_constraint (e: trconstr): Sec (list constraint) := 
      match e with
      | TcDef x ck cexp  =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | TcNext x  ck exp       =>         
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | TcCall _ [] _ _ _ _ => ret []
      | TcCall _ xs ck false f exps => 
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)

      | TcCall x0 xs ck true f exps => 
         (match find_signature f G with
          | Some n =>
              do ckty     <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp   <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp   <- mmap (fun x => find_env x env) xs;
              do rst_inst <- find_env x0 reset_env;
            generate_constraints n inptyp ckty [rst_inst] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | TcReset x rck f =>
          do rckty    <- option_to_sec (assign_clk_type env base_ty rck); (* κ''*)
          do rst_inst <- find_env x reset_env; (* κ⁰ in paper*)
          ret [([rst_ty]  ⊔ rckty, [rst_inst])]
      end.

  Fixpoint generate_trconstrs_constraints (es: list trconstr) : Sec (list constraint) :=
    match es with
    | []     => ret []
    | e::es' => 
        do c  <- generate_trconstr_constraint e;
        do cs <- generate_trconstrs_constraints es';
        ret (c++cs)
    end.

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

  
  Lemma generate_tr_constraints_inv: forall (es1 es2: list trconstr)  st sconst st2,
  generate_trconstrs_constraints (es1 ++ es2) st = OK (sconst, st2) -> exists sconst1 st1 sconst2,  generate_trconstrs_constraints es1 st = OK (sconst1, st1) /\ generate_trconstrs_constraints es2 st1 = OK (sconst2, st2) /\ sconst = sconst1++sconst2.
  Proof.
    induction es1.
    - intros. simpl in H.  repeat eexists . eauto.
    - intros. simpl in H. repeat monadInv. eapply IHes1 in Hbind1. destruct Hbind1 as (es1const & es1state & es2const & [indArg1 [indArg2 Hx1]]). exists (x++es1const). exists es1state. exists es2const. split.
    2: split; auto; rewrite <- app_assoc; now subst. 
    unfold bind. destruct (generate_trconstr_constraint a st) as [(x' & x0')|] eqn:Hgen1;  inversion Hbind;
    destruct (generate_trconstrs_constraints es1 x0) eqn:Hgen2; inversion indArg1; subst; unfold ret; try congruence.
  Qed.

    


  End SECTRCONSTRTYPING.


  Section SECSYSTYPING.
    Variable G: secglobal.

    (* Legacy self-contained system-signature generation. *)
    Definition generate_system_signature (n: system): res signature :=
      match  (do (env_in,  inp)    <- insert_vars (List.map fst (n.(SynStc.s_in))) (Env.empty _);
              do (env_out, out)    <- insert_vars (List.map fst n.(SynStc.s_out)) env_in;
              do (env, locals)     <- insert_vars (List.map fst n.(SynStc.s_vars)) env_out;
              do ck_id             <- fresh_ident;
              do rst_id            <- fresh_ident;
              do (reset_env, rids) <- generate_reset_env n.(SynStc.s_tcs);
              do constraints'      <- generate_trconstrs_constraints G env reset_env ck_id rst_id (n.(SynStc.s_tcs));
              ret (SynStc.s_name n, inp, out, rst_id, ck_id, simplify constraints' (locals ++ rids))) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints),_) => 
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.   

    (* Environment-driven system-signature generation used in the translation
       preservation proofs. The main STC-specific addition is the separate
       reset-instance environment threaded through [generate_reset_env]. *)
    Definition generate_sys_signature (n: system) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(SynStc.s_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(SynStc.s_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(SynStc.s_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(SynStc.s_vars)) env);
              do (reset_env, rids) <- generate_reset_env n.(SynStc.s_tcs);
              do constraints' <- generate_trconstrs_constraints G env reset_env clk_type rst_type (n.(SynStc.s_tcs));
              ret (inp, out, rst_type, clk_type, simplify constraints' (locals ++ rids), env)) init_state with
      | Error e => Error e
      | OK ((inp, out, rst_id, ck_id, constraints, env),_) => 
          OK {| s_name  := SynStc.s_name n;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.  
  End SECSYSTYPING.

  Section SECPROGRAMTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_sys_signatures' (acc: list signature) (sys_list: program) (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_sys_signature acc n env aux_names;
        generate_all_sys_signatures' (sig::acc) ns env aux_names
      end.
    Definition generate_all_sys_signatures (sys_list: program) (env: Env.t ident) (aux_names: list node_aux_names): res (list signature) :=
      generate_all_sys_signatures' [] sys_list env aux_names.


    Fixpoint generate_signatures' (acc: list signature) (sys_list: program): res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_system_signature acc n;
        generate_signatures' (sig::acc) ns
      end.

    Definition generate_signatures (sys_list: program) := generate_signatures' [] sys_list.

  End SECPROGRAMTYPING.
End SECSTCTYPING.

Module SecSTCTyping  
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX Op)
  (SynStc: STCSYNTAX Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING.

Include SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING.


End SecSTCTyping.
