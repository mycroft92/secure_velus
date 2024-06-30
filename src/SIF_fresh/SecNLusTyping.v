
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import NLustre.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF_fresh.SecCETyping.
From Velus Require Import SIF_fresh.SecContext.
From Velus Require Import SIF.SIFSignature.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.
(*Definition msg_missing_ident (id : ident) : errmsg := MSG "Identifier: '" :: CTX id :: msg "' not found in context.".  *)

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import OpAux : OPERATORS_AUX   Op)
  (Import CStr  : COINDSTREAMS    Op OpAux)
  (Import IStr  : INDEXEDSTREAMS  Op OpAux)
  (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
  (Import CE    : COREEXPR    Ids Op OpAux      IStr)
  (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CE.Syn).
  (* Check wst_exp. *)

  (* expressions are already done in CETyping*)
  (* sec typing expressions : mapping -> expression -> sec type *)

  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(n_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  (* sec typing equations   : mapping -> equation -> constraints  *)
  Section SECEEQNTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable base_ty: ident.
    Variable rst_ty : ident.


    Definition generate_eqn_constraint (e: equation): Sec (list constraint) := 
      match e with
      | EqDef x ck cexp  =>
          do expty <- option_to_sec (assign_cexp_type env cexp);
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | EqFby x  ck _ exp       => 
          do expty <- option_to_sec (assign_exp_type  env exp);
          do ckty  <- option_to_sec (assign_clk_type  env base_ty ck);
          do xty   <- find_env x env;
          ret [(ckty ⊔ expty, [xty])]
      | EqApp xs ck f exps None => 
         (match find_signature f G with
          | Some n => (*error (msg "unimplemented") *)
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      (*1. find the signature
        2. compute the types of input expressions, clock and reset
        3. find the types of output expressions 
        4. substitute the types to generate fresh constraints*)
      | EqApp xs ck f exps (Some (r,ckr)) => 
         (match find_signature f G with
          | Some n => error (msg "unimplemented")
              (*I will add this once the proof goes through for no reset part*)
              (* 
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do rty    <- find_env r env;
              do rstty  <- option_to_sec (assign_clk_type env rst_ty ckr);
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty ([rty] ⊔ rstty) outtyp *)
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


  End SECEEQNTYPING.

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
    (* This should just return signature, not in a monad*)
    (* Definition generate_node_signature (n: node): res signature :=
      do (env_in,  inp)  <- insert_vars (List.map fst n.(n_in)) (Env.empty _);
      do (env_out, out)  <- insert_vars (List.map fst n.(n_out)) env_in;
      do (env, locals) <- insert_vars (List.map fst n.(n_vars)) env_out;
      do ck_id   <- fresh_ident;
      do rst_id  <- fresh_ident;
      do constraints' <- generate_eqns_constraints G env ck_id rst_id (n.(n_eqs)); *)

    

   

  End SECNODETYPING.

  Section SECGLOBALTYPING.

  End SECGLOBALTYPING.
  (**
   * 1. New name generation scheme
   *   a. Check elab->fresh monad usage
   * 2. Sets up mapping from idents -> idents
   * 3. Typing rules
   * 4. Do we assume that signatures are part of node records or are they seperate records?
   **) 
End SECNLUSTYPING.

Module SecNLusTyping  
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
(SECCETYPING: SECCETYPING Ids Op CE.Syn) <: SECNLUSTYPING Op SC OpAux CStr IStr CIStr CE NL SECCETYPING.

Include SECNLUSTYPING Op SC OpAux CStr IStr CIStr CE NL SECCETYPING.


End SecNLusTyping.
