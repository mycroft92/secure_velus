(** Leg I: putting [fby]s into normalized form preserves generated constraints.

    This is the leg the two-operand [fby] rule exists for.  [fby_equation]
    rewrites only at the *top* of an equation -- it never descends into a
    subexpression -- so unlike unnesting there is no expression induction here
    at all: the operands [e0] and [e] are carried over verbatim, and what has
    to be shown is an entailment between a handful of constraint shapes.

    Two of the four shapes leave the equation alone.  The other two replace
    one delayed definition by an [ite] over a fresh initialisation flag
    together with a delayed definition of a fresh variable, and it is exactly
    there that typing *both* operands of an [fby] pays: the source constraint
    already mentions the initial value's type, which is what the [ite]'s first
    branch needs, and the fresh variables are locals, so the witness valuation
    is free to give them the levels the new equations ask for.

    Everything above the equation level is shared with Leg U: [call_weakens],
    [generate_leqns_constraints_entails_G], [preserves_on_simplify] and the
    program-level lockstep [generate_all_lsignatures_weakens'] say nothing
    about which pass is being run. *)

From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Lia.
From Coq Require Import String.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Unnesting.
From Velus Require Import Lustre.Normalization.NormFby.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SymLusTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecLTyping.

From compcert Require Import common.Errors.

Import List.ListNotations.
From Velus Require Import SIF.SecLusUnnestingNodes.

Module SecLusNormFby
  (Import Ids     : IDS)
  (Import Op      : OPERATORS)
  (Import OpAux   : OPERATORS_AUX Op)
  (Import Lat     : Lattice)
  (Import SecT    : SECTYPES Lat)
  (Import SLT     : SECLUSTYPES Lat SecT)
  (Import SC      : SECMONAD Ids)
  (Import LSyn    : LSYNTAX Ids Op)
  (Import LClo    : LCLOCKING Ids Op LSyn)
  (CESyn          : CESYNTAX Op)
  (NLSyn          : NLSYNTAX Ids Op CESyn)
  (Import STEP    : SECMONADSTEP Ids SC)
  (Import SIG     : SIGNATURE Ids SC)
  (SIGPROOFS      : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn NLSyn)
  (CEIsF          : CEISFREE Ids Op CESyn)
  (CEClo          : CECLOCKING Ids Op CESyn)
  (Import SECCET  : SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import TR      : TR Ids Op OpAux LSyn CESyn NLSyn)
  (Import SECL    : SECLTYPING Ids Op OpAux SC LSyn CESyn NLSyn SIG NAMEGEN
                      CEIsF CEClo SECCET TR)
  (Import UNN     : UNNESTING Ids Op OpAux LSyn)
  (Import NF      : NORMFBY Ids Op OpAux LSyn UNN)
.

Module NODES := SecLusUnnestingNodes Ids Op OpAux Lat SecT SLT SC LSyn LClo CESyn NLSyn STEP SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCET TR SECL UNN.
Include NODES.

Import SECMONADNotations.

  (** * The node lists the two drivers walk

      As on Leg U, and for the same reason: the drivers generate over
      [rev nodes], so the relation is a [Forall2], which reverses where a
      [normfby_global] run does not.  The pass's arguments are part of the
      relation because [normfby_node]'s result mentions them. *)

  Definition normfbyed_nodes (ns nt : list node) : Prop :=
    Forall2 (fun n m =>
               exists Q c (Hunt : unnested_node Q n)
                        (Hpref : n_prefixes n = norm1_prefs),
                 m = normfby_node Q c n Hunt Hpref) ns nt.

  Lemma normfby_global_normfbyed_nodes :
    forall G Hunt Hprefs, normfbyed_nodes G (normfby_global G Hunt Hprefs).
  Proof.
    induction G as [|n G IH]; intros Hunt Hprefs; simpl.
    - constructor.
    - constructor; [|apply IH].
      eexists. eexists. eexists. eexists. reflexivity.
  Qed.

  Lemma normfbyed_nodes_rev :
    forall ns nt, normfbyed_nodes ns nt -> normfbyed_nodes (rev ns) (rev nt).
  Proof.
    unfold normfbyed_nodes. induction 1; simpl; [constructor|].
    apply Forall2_app_both; [assumption|constructor; [assumption|constructor]].
  Qed.

  Section NormFbyNode.

    Variable env     : Env.t ident.
    Variable base_ty : ident.
    Variable rst_ty  : ident.
    Variable scope   : list ident.

    (** * What the pass does to a node's record

        The same three facts as [unnest_node_fields], and they hold for the
        same reason: the pass copies the interface and extends [n_vars] on the
        right with the variables its run created. *)
    Lemma normfby_node_fields :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs),
        (normfby_node Q c n Hunt Hpref).(n_eqs)
          = fst (fby_equations
                   (PS.union c (ps_from_list (List.map fst (n_out n))))
                   n.(n_eqs) init_st)
        /\ (normfby_node Q c n Hunt Hpref).(n_vars)
             = n.(n_vars)
                 ++ idty (st_anns
                            (snd (fby_equations
                                    (PS.union c
                                       (ps_from_list (List.map fst (n_out n))))
                                    n.(n_eqs) init_st)))
        /\ (normfby_node Q c n Hunt Hpref).(n_in) = n.(n_in)
        /\ (normfby_node Q c n Hunt Hpref).(n_out) = n.(n_out)
        /\ (normfby_node Q c n Hunt Hpref).(n_name) = n.(n_name).
    Proof.
      intros Q c n Hunt Hpref. unfold normfby_node.
      repeat split; reflexivity.
    Qed.

    (** * Five of a signature's six fields are equal on the nose

        [generate_lnode_sig] reads the interface fields off [n_name], [n_in],
        [n_out] and the one naming environment, all four of which the pass
        copies.  So only [s_constraints] can differ -- which is exactly what
        [preserves_on] speaks about. *)
    Corollary normfby_node_sig_interface :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs)
             (G G' : secglobal) (aux : list node_aux_names)
             st0 st0' sg st1 sg' st1',
        generate_lnode_sig G n env aux st0 = OK (sg, st1) ->
        generate_lnode_sig G' (normfby_node Q c n Hunt Hpref) env aux st0'
          = OK (sg', st1') ->
        s_name sg' = s_name sg
        /\ s_in sg' = s_in sg
        /\ s_out sg' = s_out sg
        /\ s_clk sg' = s_clk sg
        /\ s_reset sg' = s_reset sg.
    Proof.
      intros Q c n Hunt Hpref G G' aux st0 st0' sg st1 sg' st1' H H'.
      apply (lnode_sig_inv env) in H
        as (c1 & r1 & ct1 & rt1 & i1 & o1 & l1 & cs1
            & Ha1 & Hc1 & Hr1 & Hi1 & Ho1 & _ & _ & ?); subst sg.
      apply (lnode_sig_inv env) in H'
        as (c2 & r2 & ct2 & rt2 & i2 & o2 & l2 & cs2
            & Ha2 & Hc2 & Hr2 & Hi2 & Ho2 & _ & _ & ?); subst sg'.
      cbn [n_name n_in n_out normfby_node] in Ha2, Hi2, Ho2.
      rewrite Ha1 in Ha2. inversion Ha2; subst c2 r2.
      rewrite Hc1 in Hc2. inversion Hc2; subst ct2.
      rewrite Hr1 in Hr2. inversion Hr2; subst rt2.
      rewrite Hi1 in Hi2. inversion Hi2; subst i2.
      rewrite Ho1 in Ho2. inversion Ho2; subst o2.
      cbn [s_name s_in s_out s_clk s_reset].
      repeat split; reflexivity.
    Qed.

    (** * The clock environments agree where the generator looks

        [find_clock_node_ext_defd] takes no account of which pass extended the
        variables, so this is a quotation. *)
    Corollary generate_leqns_normfby_node_cenv :
      forall Q c (n : node) (Hunt : unnested_node Q n)
             (Hpref : n_prefixes n = norm1_prefs) (G : secglobal) s,
        generate_leqns_constraints G env base_ty rst_ty
          (lnode_clock_env (normfby_node Q c n Hunt Hpref)) n.(n_eqs) s
        = generate_leqns_constraints G env base_ty rst_ty
            (lnode_clock_env n) n.(n_eqs) s.
    Proof.
      intros Q c n Hunt Hpref G s.
      apply EQ.generate_leqns_constraints_cenv_ext.
      intros x Hx.
      destruct (normfby_node_fields Q c n Hunt Hpref) as (_ & Hv & Hi & Ho & _).
      exact (find_clock_node_ext_defd n (normfby_node Q c n Hunt Hpref) _ x
               Hi Ho Hv Hx).
    Qed.

  End NormFbyNode.

End SecLusNormFby.
