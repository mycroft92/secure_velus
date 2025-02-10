
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

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECSTCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).
  (* Check wst_exp. *)

  (* expressions are already done in CETyping*)
  (* sec typing expressions : mapping -> expression -> sec type *)

  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  Section RESETHANDLER.
  (***
    This section collects all reset statements and assigns reset variables for their calls.
  *)
  Fixpoint collect_reset_stmts' (trl: list trconstr) (acc: list trconstr) : list trconstr :=
    match trl with
    | [] => acc
    | tr::trl' => 
      (match tr with
        | TcReset _ _ _ => collect_reset_stmts' trl' (acc ++ [tr])
        | _             => collect_reset_stmts' trl' acc
        end)
    end.

  Definition collect_reset_stmts trl := collect_reset_stmts' trl []. (* first part of gather_reset function in paper*)

  (* Inserts a new reset type for reset function call into environment env. Returns the environemnt and list of reset types generated*)
  Definition assign_reset_type (tr: trconstr) (env: Env.t ident) : Sec (Env.t ident * ident) :=
    match tr with
    | TcReset x ck f => fresh_insert x env 
    | _ => error (msg "Not a reset statement! ")
    end. 

  (* TcReset i r f *)
  Fixpoint generate_reset_env' (trl: list trconstr) (env: Env.t ident) (acc: list ident): Sec (Env.t ident * list ident) :=
    (* let trl' := collect_reset_stmts trl in *)
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

  (* sec typing equations   : mapping -> equation -> constraints  *)
  Section SECTRCONSTRTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable reset_env: Env.t ident. (* context of resets*)
    Variable base_ty: ident.
    Variable rst_ty : ident.
    Print trconstr.
    (* We need a context of resets*)
    Definition generate_trconstr_constraint (e: trconstr): Sec (list constraint) := 
      match e with
      | TcDef x ck cexp  =>
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | TcNext x  ck exp       => 
          do expty <- option_to_sec (assign_exp_type  env exp);
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
          (* TcCall needs some throat clearing in args to compute *)
      | TcCall _ xs ck false f exps => 
         (match find_signature f G with
          | Some n => (*error (msg "unimplemented") *)
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)

      | TcCall x0 xs ck true f exps => 
         (match find_signature f G with
          | Some n => (*error (msg "unimplemented")*) 
              do inptyp   <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do ckty     <- option_to_sec (assign_clk_type env base_ty ck);
              do outtyp   <- mmap (fun x => find_env x env) xs;
              do rst_inst <- find_env x0 reset_env;
            generate_constraints n inptyp ckty [rst_inst] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | TcReset x rck f => (*error (msg "Unimplemented")*)
          do rckty    <- option_to_sec (assign_clk_type env base_ty rck); (* κ''*)
          do rst_inst <- find_env x reset_env; (* κ⁰ in paper*)
          (*Naming of types to be consistent*)
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


  End SECTRCONSTRTYPING.

  (* sec typing nodes *) 
  Section SECSYSTYPING.
    Variable G: secglobal.
    (* Variable env: Env.t ident.  *)
    (* Variable base_ty: ident.
    Variable rst_ty : ident. *)
    (* Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in   : list ident; (*ordered list of input security types*)
    n_out  : list ident; (*ordered list of output security types*)

    n_reset: ident; (* We generate the name for the reset type and its corresponding value*)
    n_clk  : ident; (* In a generated signature, this will always be named sec_clk*)(*The base clock is always empty list*)
    (* We already have that Gamma \rel forall inp. inp, because the clock rules give us this directly. No need to have an additional \Gamma = GLB (inputs) *)
    constraints : list constraint; (*constraints*)
    }. *)
    (* For each node
      * inputs : G, env 
      * create new Env with inputs type vars, clock_ty, reset_ty, output type vars, localvars
      * run simplify on localvars types*)
    (* Fixpoint generate_node_signature (n: node) : Sec signature := *)
      
      (*Check List.map.
    Check insert_vars.
    Print signature.
    Print system.
    Check SynStc.s_name.
    (*Check n_name.*)
    Check generate_trconstrs_constraints.
         Check generate_reset_env. *)
    (* This should just return signature, not in a monad*)
    Definition generate_system_signature (n: system): res signature :=
      match  (do (env_in,  inp)    <- insert_vars (List.map fst (n.(SynStc.s_in))) (Env.empty _);
              do (env_out, out)    <- insert_vars (List.map fst n.(SynStc.s_out)) env_in;
              do (env, locals)     <- insert_vars (List.map fst n.(SynStc.s_vars)) env_out;
              do ck_id             <- fresh_ident;
              do rst_id            <- fresh_ident;
              do (reset_env, rids) <- generate_reset_env n.(SynStc.s_tcs); (* reset_env *) 
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

  End SECSYSTYPING.

  Section SECPROGRAMTYPING.
    Open Scope error_monad_scope.
    Fixpoint generate_signatures' (acc: list signature) (sys_list: program): res (list signature) :=
      match sys_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_system_signature acc n;
        generate_signatures' (acc++[sig]) ns
      end.

    Definition generate_signatures (sys_list: program) := generate_signatures' [] sys_list.

  End SECPROGRAMTYPING.
  (**
   * 1. New name generation scheme
   *   a. Check elab->fresh monad usage
   * 2. Sets up mapping from idents -> idents
   * 3. Typing rules
   * 4. Do we assume that signatures are part of node records or are they seperate records?
   **) 
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
