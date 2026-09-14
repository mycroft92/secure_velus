(** Leg U: unnesting preserves generated constraints.

    This is the pass the refinement types were built for.  [unnest_exp] on a
    nested call mints one variable per result with [idents_for_anns'], returns
    an [Evar] for each, and emits the call as its own equation.
    [assign_lexp_type] on the same expression mints one security name per
    result with [fresh_idents], returns a variable-shaped type for each, and
    *carries* that equation's constraints.

    So the theorem is that the carried constraints are the constraints of the
    equations unnesting emits, and the minted security names are the variables
    unnesting adds.  Nothing in the transcription leg states this, and nothing
    in it can: [to_lexp] rejects [Eapp], so by then there are no nested calls
    left and the carried component is empty everywhere.

    The two allocators cannot produce the same names -- unnesting mints
    [gensym norm1 _] and the security monad [gensym sec _] -- so the two sides
    are related by a bijection rather than by equality.  Both mint one name per
    annotation in the same order, so within a node the bijection is positional,
    and [preserves_on] absorbs it: the witness valuation is free to differ off
    the visible scope, which is exactly where the renamed names live. *)

From Coq Require Import List.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLUSUNNESTING
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX Ids Op)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import UNN     : UNNESTING Ids Op OpAux LSyn).

  Import SECMONADNotations.

  (** * The security side of a call expression

      The analogue of [generate_lcall_constraint_inv], one level down: what
      [assign_lexp_type] does to an [Eapp].  Every Leg U proof about a nested
      call starts here.

      The result is [length anns] types, all carrying the *same* constraint
      list -- the instantiated call block joined with whatever the arguments
      and the reset were carrying.  That shared list is what the emitted
      equation has to generate. *)

  Lemma assign_lexp_Eapp_inv :
    forall G env base_ty rst_ty f es er anns ts st st',
      assign_lexp_type G env base_ty rst_ty (Eapp f es er anns) st = OK (ts, st') ->
      exists sg argts rstty ckty outs cs sta stb stc,
        assign_lexps G env base_ty rst_ty es st = OK (argts, sta)
        /\ (match er with
            | None => rstty = lvar rst_ty /\ stb = sta
            | Some e1 =>
                exists t1 a1 stm,
                  assign_lexp_type G env base_ty rst_ty e1 sta = OK (t1, stm)
                  /\ single t1 stm = OK (a1, stb)
                  /\ rstty = ljoin (lvar rst_ty) a1
            end)
        /\ assign_clk_type env base_ty (find_base_clock (LSyn.clocksof es))
           = Some ckty
        /\ find_signature f G = Some sg
        /\ fresh_idents (List.length anns) stb = OK (outs, stc)
        /\ generate_constraints sg (List.map fst argts) ckty (fst rstty) outs stc
           = OK (cs, st')
        /\ ts = List.map
                  (fun o => (([o] : ST),
                             cmerge cs (cmerge (carried argts) (snd rstty))))
                  outs.
  Proof.
    intros G env base_ty rst_ty f es er anns ts st st' H.
    simpl in H.
    eapply sec_bind_inv in H as (argts & sta & Hargs & H).
    eapply sec_bind_inv in H as (rstty & stb & Hrst & H).
    eapply sec_bind_inv in H as (ckty & stk & Hck & H).
    destruct (find_signature f G) as [sg|] eqn:Esg; [|discriminate].
    eapply sec_bind_inv in H as (outs & stc & Houts & H).
    eapply sec_bind_inv in H as (cs & std & Hcs & Hret).
    unfold ret in Hret. inv Hret.
    apply option_to_sec_inv in Hck as [Hck ?]; subst stk.
    exists sg, argts, rstty, ckty, outs, cs, sta, stb, stc.
    repeat split; auto.
    destruct er as [e1|].
    - eapply sec_bind_inv in Hrst as (t1 & stm & Ht1 & Hrst).
      eapply sec_bind_inv in Hrst as (a1 & stn & Ha1 & Hret').
      unfold ret in Hret'. inv Hret'.
      exists t1, a1, stm. auto.
    - unfold ret in Hrst. inv Hrst. auto.
  Qed.

End SECLUSUNNESTING.
