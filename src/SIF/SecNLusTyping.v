
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
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

  (** NLustre equation typing in the shared naming environment. *)
  Section SECEQNTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable base_ty: ident.
    Variable rst_ty : ident.
    Definition generate_eqn_constraint (e: equation): Sec (list constraint) := 
      match e with
      | EqDef x ck cexp  =>
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | EqFby x  ck _ exp       => 
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do expty <- option_to_sec (assign_exp_type  env exp);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | EqApp [] _ _ _ _ => ret [] 
      | EqApp xs ck f exps None => 
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | EqApp xs ck f exps (Some (r,ckr)) =>
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do rty    <- find_env r env;
              do rstty  <- option_to_sec (assign_clk_type env rst_ty ckr);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty ([rty] ⊔ rstty) outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      end.

  Fixpoint generate_eqns_constraints (es: list equation) : Sec (list constraint) :=
    match es with
    | []     => ret []
    | e::es' => 
        do c  <- generate_eqn_constraint e;
        do cs <- generate_eqns_constraints es';
        ret (c++cs)
    end.


  End SECEQNTYPING.
 
  Section SECNODETYPING.
    Variable G: secglobal.

    (* Legacy self-contained signature generation, kept for comparison with the
       newer environment-driven formulation below. *)
    Definition generate_node_signature (n: node): res signature :=
      match  (do (env_in,  inp)  <- insert_vars (List.map fst (n.(n_in))) (Env.empty _);
              do (env_out, out)  <- insert_vars (List.map fst n.(n_out)) env_in;
              do ck_id           <- fresh_ident;
              do rst_id          <- fresh_ident;
              do (env, locals)   <- insert_vars (List.map fst n.(n_vars)) env_out;
              do constraints'    <- generate_eqns_constraints G env ck_id rst_id (n.(n_eqs));
              ret (n_name n, inp, out, rst_id, ck_id, simplify constraints' locals, env_out)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints, _),_) => 
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.   

      (* Environment-driven signature generation used by the translation
         preservation development. The shared [env] and [aux_names] fix the
         interface/local security identifiers ahead of time. *)
      Definition generate_node_sig (n: node) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match  (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(n_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(n_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(n_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(n_vars)) env);
            
              do constraints'    <- generate_eqns_constraints G env clk_type rst_type (n.(n_eqs));
              ret (n_name n, inp, out, rst_type, clk_type, simplify constraints' locals, env)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints, _),_) => 
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

    Fixpoint generate_all_signatures' (acc: list signature) (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_sig acc n env aux_names;
        generate_all_signatures' (sig::acc) ns env aux_names
      end.
    Definition generate_all_signatures (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names): res (list signature) :=
      generate_all_signatures' [] node_list env aux_names.

    Fixpoint generate_signatures' (acc: list signature) (node_list: global): res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_signature acc n;
        generate_signatures' (sig::acc) ns
      end.

    Definition generate_signatures (node_list: global) := generate_signatures' [] node_list.

  End SECGLOBALTYPING.

End SECNLUSTYPING.

Module SecNLusTyping  
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.

Include SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.


End SecNLusTyping.
