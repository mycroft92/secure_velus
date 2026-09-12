(** Leg A: transcription preserves generated constraints exactly.

    Of the three passes between Lustre and NLustre, transcription is the one
    that introduces no variables and preserves a node's interface
    definitionally.  So on the normalized fragment the two constraint
    generators do not merely preserve satisfiability -- they agree.  That is
    what this file proves, and it is the reason the Lustre leg can be stated
    as an equality where the NLustre-to-Stc leg needs [preserves_on].

    The expression-level halves live in [SecLTyping.v], next to the generator
    they are about.  What is here is the equation level and above, which needs
    both generators in scope. *)

From Coq Require Import List.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.

Module Type SECLUSNLUSTRANSLATION
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX  Ids Op)
  (CESyn          : CESYNTAX     Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import SIG     : SIGNATURE  Ids SC)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (NLOrd          : NLORDERED Ids Op CESyn NLSyn)
  (NLMem          : MEMORIES Ids Op CESyn NLSyn)
  (NLIsD          : ISDEFINED Ids Op CESyn NLSyn NLMem)
  (NLIsF          : ISFREE Ids Op CESyn NLSyn CEIsF)
  (NLClo          : NLCLOCKING Ids Op CESyn NLSyn NLOrd NLMem NLIsD CEIsF NLIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import SECNL   : SECNLUSTYPING Ids Op SC CESyn NLSyn SIG NAMEGEN CEIsF CEClo
                      SECCET NLOrd NLMem NLIsD NLIsF NLClo).

  Import SECMONADNotations.

  Lemma res_to_sec_OK : forall {A : Type} (a : A) st,
      res_to_sec (OK a) st = OK (a, st).
  Proof. reflexivity. Qed.

  (** A monad law the call case needs: it binds the instantiated block only to
      merge an empty set of carried obligations into it. *)
  Lemma bind_ret_id : forall {A : Type} (m : Sec A) st,
      (do a <- m; ret a) st = m st.
  Proof.
    intros A m st. unfold bind, ret.
    destruct (m st) as [[a st']|e]; reflexivity.
  Qed.

  (** * What remains: the equation level and above

      The expression-level halves of this leg are proved, in [SecLTyping.v]:
      [to_lexp_assign_eq], [to_cexp_assign_eq] and [to_lexps_assign_eq]. The
      generators have been aligned case for case with [to_equation] -- bind
      order, the monadic output lookup, the join association in merge and ite,
      and the empty-result call case -- so that the remaining steps are
      computations rather than reconciliations.

      The statement to prove is

<<
      Theorem to_equation_constraint_eq :
        forall G env base_ty rst_ty cenv envo eq eq' cs st st',
          to_equation cenv envo eq = OK eq' ->
          generate_eqn_constraint G env base_ty rst_ty eq' st = OK (cs, st') ->
          generate_leqn_constraint G env base_ty rst_ty cenv eq st = OK (cs, st').
>>

      running NLustre-to-Lustre, *not* as an equality of the two [Sec]
      computations. Equality is false where generation fails: the two
      generators report different messages, so they agree only on success.
      And this is the direction that is both provable from the expression
      lemmas and sufficient:
      [SecNLusTypingTotality.source_signature_generation_total] says the
      NLustre generator succeeds on any ordered, well-clocked program, and
      transcription supplies both (`TrOrdered.ord_l_nl`,
      `TrClocking.wc_transcription`). So on a program that transcribes the
      NLustre side always succeeds, this theorem hands the Lustre side the
      same constraints, and the two sets are then equal -- which is what
      preservation needs in either direction.

      The proof splits into the four shapes of [to_equation]. The seven forms
      that transcribe to [EqDef] share one script, [Efby] is that script with
      [to_lexp_assign_eq] in place of [to_cexp_assign_eq], and the two call
      shapes use [to_lexps_assign_eq] with [carried_plain], [map_fst_plain]
      and [bind_ret_id].

      One practical warning for whoever writes it. A blanket [simpl] cannot be
      used: it unfolds [SymTypes.merge] into its raw inner [fix] on one side
      of the goal only, after which [reflexivity] cannot close a goal whose
      two sides are otherwise identical. Reduce with [cbn [fst snd]] and the
      per-constant unfolding lemmas instead -- the same discipline
      [norm_cs_cons] and the [assign_lexp_*] equations already impose. *)

End SECLUSNLUSTRANSLATION.
