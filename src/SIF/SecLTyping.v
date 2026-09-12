(** Symbolic security typing for unrestricted Lustre.

    The \nlustre generator of [SecNLusTyping.v] gives an expression a single
    symbolic type.  Lustre needs two things more.  An expression denotes a
    *list* of flows, so a type is a list; and a node call may appear inside an
    expression, where there is no equation on which to hang the callee's
    instantiated constraints, so a type carries them itself.  Both are
    supplied by [LusTypes.v]: the type of one flow is an [LST], a symbolic
    type paired with the obligations it carries.

    The rules are those of ICTAC 2021 Figures 6--8, with three additions that
    the mechanised syntax forces and that neither that paper nor the
    \nlustre/\stc one covers: the ambient reset level is threaded throughout,
    a call may carry a reset expression, and [Earrow] is typed.

    Each case is written against the corresponding case of
    [Transcription/Tr.v], so that on the normalized fragment this generator
    and the \nlustre one emit *equal* constraints rather than merely
    satisfiability-preserving ones. *)

From Coq Require Import List.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLTYPING
  (Import Ids    : IDS)
  (Import Op     : OPERATORS)
  (Import OpAux  : OPERATORS_AUX Op)
  (Import SC     : SECMONAD Ids)
  (Import LSyn   : LSYNTAX  Ids Op)
  (CESyn         : CESYNTAX     Op)
  (NLSyn         : NLSYNTAX Ids Op CESyn)
  (Import SIG    : SIGNATURE  Ids SC)
  (CEIsF         : CEISFREE Ids Op CESyn)
  (CEClo         : CECLOCKING Ids Op CESyn)
  (Import SECCET : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR     : TR Ids Op OpAux LSyn CESyn NLSyn).

  Import SECMONADNotations.

  (** Minting one identifier per output flow of a nested call.  These are the
      only identifiers this generator creates.  They live in the ordinary
      [sec] namespace, so the node-level entry point must start the monad at
      the naming pass's final state; see [docs/SecLTyping.md]. *)

  Fixpoint fresh_idents (n : nat) : Sec (list ident) :=
    match n with
    | O => ret []
    | S n' => do x <- SC.fresh_ident;
              do xs <- fresh_idents n';
              ret (x :: xs)
    end.

  Section SECLEXPTYPING.

    Variable G       : secglobal.            (* callee signatures *)
    Variable env     : Env.t ident.          (* program variable -> security name *)
    Variable base_ty : ident.                (* the node's base clock *)
    Variable rst_ty  : ident.                (* the node's ambient reset level *)

    Definition single (ts : list LST) : Sec LST :=
      match ts with
      | [t] => ret t
      | _   => error (msg "security typing: expected a single flow")
      end.

    (** Componentwise join, as every rule of ICTAC Figure 7 is componentwise.
        A length mismatch is a malformed program, not a silent truncation. *)
    Fixpoint ljoin_list (ts us : list LST) : Sec (list LST) :=
      match ts, us with
      | [], [] => ret []
      | t :: ts', u :: us' =>
          do r <- ljoin_list ts' us';
          ret (ljoin t u :: r)
      | _, _ => error (msg "security typing: flow list length mismatch")
      end.

    (** Everything a list of flow types is carrying, collected. *)
    Definition carried (ts : list LST) : list constraint :=
      fold_right (fun t acc => cmerge (snd t) acc) [] ts.

    Fixpoint assign_lexp_type (e : exp) {struct e} : Sec (list LST) :=
      let assign_lexps :=
        fix go (es : list exp) : Sec (list LST) :=
          match es with
          | [] => ret []
          | e' :: es' => do t <- assign_lexp_type e';
                         do r <- go es';
                         ret (t ++ r)
          end in
      match e with
      | Econst _ => ret [lbot]

      | Evar x _ =>
          do a <- find_env x env;
          ret [lvar a]

      | Eunop _ e1 _ =>
          assign_lexp_type e1

      | Ebinop _ e1 e2 _ =>
          do t1 <- assign_lexp_type e1;
          do t2 <- assign_lexp_type e2;
          do a1 <- single t1;
          do a2 <- single t2;
          ret [ljoin a1 a2]

      | Ewhen es x _ _ =>
          do ts <- assign_lexps es;
          do g  <- find_env x env;
          ret (map (fun t => ljoin t (lvar g)) ts)

      | Emerge x ets efs _ =>
          do g  <- find_env x env;
          do ts <- assign_lexps ets;
          do us <- assign_lexps efs;
          do r  <- ljoin_list ts us;
          ret (map (fun t => ljoin t (lvar g)) r)

      | Eite e0 ets efs _ =>
          do t0 <- assign_lexp_type e0;
          do th <- single t0;
          do ts <- assign_lexps ets;
          do us <- assign_lexps efs;
          do r  <- ljoin_list ts us;
          ret (map (fun t => ljoin t th) r)

      | Efby e0s es _ =>
          do ts <- assign_lexps e0s;
          do us <- assign_lexps es;
          ljoin_list ts us

      | Earrow e0s es _ =>
          do ts <- assign_lexps e0s;
          do us <- assign_lexps es;
          ljoin_list ts us

      (** The call case.  The callee's stored signature is instantiated with
          the actual argument types, the call's base clock and the reset level
          reaching it; the outputs are fresh, one per result flow, because a
          nested call has no declared variable whose name it could borrow.
          Each result flow is typed by its own fresh name, refined by the
          instantiated constraints together with everything the arguments and
          the reset expression were themselves carrying.  That is
          [beta{|rho'|}] of rule (LTncall), composed with the join rule of
          Figure 5. *)
      | Eapp f es er anns =>
          do argts <- assign_lexps es;
          do rstty <- (match er with
                       | None => ret (lvar rst_ty)
                       | Some e1 =>
                           do t1 <- assign_lexp_type e1;
                           do a1 <- single t1;
                           ret (ljoin (lvar rst_ty) a1)
                       end);
          do ckty <- option_to_sec
                       (assign_clk_type env base_ty
                          (find_base_clock (LSyn.clocksof es)));
          match find_signature f G with
          | None => error (MSG "Signature not found for: " :: [CTX f])
          | Some sg =>
              do outs <- fresh_idents (List.length anns);
              do cs   <- generate_constraints sg (map fst argts) ckty
                                              (fst rstty) outs;
              let held := cmerge cs (cmerge (carried argts) (snd rstty)) in
              ret (map (fun o => (([o] : ST), held)) outs)
          end
      end.

    Definition assign_lexps (es : list exp) : Sec (list LST) :=
      (fix go (es : list exp) : Sec (list LST) :=
         match es with
         | [] => ret []
         | e' :: es' => do t <- assign_lexp_type e';
                        do r <- go es';
                        ret (t ++ r)
         end) es.

  End SECLEXPTYPING.

End SECLTYPING.
