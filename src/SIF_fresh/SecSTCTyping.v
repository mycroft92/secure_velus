
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import Stc.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF_fresh.SecCETyping.
From Velus Require Import SIF_fresh.SecContext.
From Velus Require Import SIF.SIFSignature.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECSTCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import OpAux : OPERATORS_AUX   Op)
  (Import Str   : INDEXEDSTREAMS Op OpAux)
  (Import CE    : COREEXPR Ids   Op OpAux Str)
  (Import STC   : STC      Ids Op OpAux Str CE)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CE.Syn).
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
          ret [([rst_ty]  ⊔ rckty, [rst_inst])]
      end.

  Fixpoint generate_eqns_constraints (es: list equation) : Sec (list constraint) :=
    match es with
    | []     => ret []
    | e::es' => 
        do c  <- generate_eqn_constraint e;
        do cs <- generate_eqns_constraints es';
        ret (c++cs)
    end.


  End SECTRCONSTRTYPING.

Check generate_eqns_constraints.
  (* sec typing nodes *) 
  Section SECNODETYPING.
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
      
    Print node.
    Check List.map.
    Check insert_vars.
    Check n_name.
    Check generate_eqns_constraints.
    (* This should just return signature, not in a monad*)
    Definition generate_node_signature (n: node): res signature :=
      match  (do (env_in,  inp)  <- insert_vars (List.map fst (n.(n_in))) (Env.empty _);
              do (env_out, out)  <- insert_vars (List.map fst n.(n_out)) env_in;
              do (env, locals)   <- insert_vars (List.map fst n.(n_vars)) env_out;
              do ck_id           <- fresh_ident;
              do rst_id          <- fresh_ident;
              do constraints'    <- generate_eqns_constraints G env ck_id rst_id (n.(n_eqs));
              ret (n_name n, inp, out, rst_id, ck_id, simplify constraints' locals)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints),_) => 
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.   

  End SECNODETYPING.

  Section SECGLOBALTYPING.
    Open Scope error_monad_scope.
    Fixpoint generate_signatures' (acc: list signature) (node_list: global): res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_signature acc n;
        generate_signatures' (acc++[sig]) ns
      end.

    Definition generate_signatures (node_list: global) := generate_signatures' [] node_list.

  End SECGLOBALTYPING.
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
(OpAux : OPERATORS_AUX   Op)
(CStr  : COINDSTREAMS    Op OpAux)
(IStr  : INDEXEDSTREAMS  Op OpAux)
(CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
(CE    : COREEXPR    Ids Op OpAux      IStr)
(NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
(SIG   : SIGNATURE   Ids SC)
(SECCETYPING: SECCETYPING Ids Op CE.Syn) <: SECSTCTYPING Ids Op SC OpAux CStr IStr CIStr CE NL SIG SECCETYPING.

Include SECSTCTYPING Ids Op SC OpAux CStr IStr CIStr CE NL SIG SECCETYPING.


End SecSTCTyping.
