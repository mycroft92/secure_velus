
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
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import Names : NAMEGEN Ids Op  CESyn SynNL)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).

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

  (* sec typing equations   : mapping -> equation -> constraints  *)
  Section SECEQNTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable base_ty: ident.
    Variable rst_ty : ident.
    (*Perhaps need to transpose from base_ty and rst_ty to their original names?*)

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
          | Some n => (*error (msg "unimplemented") *)
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      (*1. find the signature
        2. compute the types of input expressions, clock and reset
        3. find the types of output expressions 
        4. substitute the types to generate fresh constraints*)
      | EqApp xs ck f exps (Some (r,ckr)) => error (msg "unimplemented")
         (* (match find_signature f G with
          | Some n => 
              (*error (msg "unimplemented")*)
              (*I will add this once the proof goes through for no reset part*)
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do rty    <- find_env r env;
              do rstty  <- option_to_sec (assign_clk_type env rst_ty ckr);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty ([rty] ⊔ rstty) outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end) *)
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
    (* Standardize the names. Keep Glossary.*)
    (*** This function changes in the sense that there is no name creation anymore*)
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

      Definition generate_node_sig (n: node) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match  (do (ck_id, rst_id) <- get_node_aux n aux_name;
            
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

      (*How will type preservation here look like?*)
      (*a. If env generated is same for inputs, ouputs, clock and reset, then the constraints produced after simplify are equisatisfiable?
          - Requires generate_node_signature to take an environment that fixes inputs, outputs etc.. (except local vars)
        b. Assume that env holds same ident when starting in same state? This might give us the exact equivalence of constraints*)

  End SECNODETYPING.

  Section SECGLOBALTYPING.
    Open Scope error_monad_scope.
    Fixpoint generate_signatures' (acc: list signature) (node_list: global): res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_signature acc n;
        generate_signatures' (sig::acc) ns
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

  (*Security of node calls*)
  (* Lemma security_node_calls_1: forall (G: secglobal) f n dlt, find_signature f G = Some n ->
    listSatisfiable dlt (n.(s_constraints)) -> *)
    (* substitution on s_constraints with NEW names, can also be satisfiable under same dlt or different dlt' 
     a \leq b
      d \sqcup c/a , e/b
      - The U \rel U', (o' \rel o) are assumptions (chec statement in paper)
      - dlt*
    ?*)

End SECNLUSTYPING.

Module SecNLusTyping  
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (Names : NAMEGEN Ids Op  CESyn SynNL)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECNLUSTYPING Ids Op SC CESyn SynNL SIG Names SECCETYPING.

Include SECNLUSTYPING Ids Op SC CESyn SynNL SIG Names SECCETYPING.


End SecNLusTyping.
