(** Causality facts for NLustre nodes, dependency graphs, and variable-order induction. *)

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.

From Velus Require Import Common.
From Velus Require Import AcyGraph.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.

Module Type NLUSTRECAUSALITY
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX Op)
       (Import SynNL : NLSYNTAX Ids Op CESyn)
       (Import CEIsF : CEISFREE Ids Op CESyn)
       (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF).

  Definition nl_depends_on_eq (eq : equation) (x y : ident) : Prop :=
    match eq with
    | EqDef z ck ce =>
        x = z /\ Is_free_in_caexp y ck ce
    | EqApp xs ck _ es None =>
        In x xs /\ Is_free_in_aexps y ck es
    | EqApp xs ck _ es (Some (r, ckr)) =>
        In x xs /\ (Is_free_in_aexps y ck es \/ y = r \/ Is_free_in_clock y ckr)
    | EqFby z ck _ _ =>
        x = z /\ Is_free_in_clock y ck
    end.

  Definition nl_depends_on (eqs : list equation) (x y : ident) : Prop :=
    Exists (fun eq => nl_depends_on_eq eq x y) eqs.

  Definition nl_graph_of_eqs {v a}
    (vars : list (ident * clock)) (eqs : list equation) (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g) (PSP.of_list (map fst vars))
    /\ (forall x y, nl_depends_on eqs x y -> is_arc g y x).

  Definition nl_graph_of_node {v a} (n : node) (g : AcyGraph v a) : Prop :=
    nl_graph_of_eqs (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) n.(n_eqs) g.

  Definition nl_node_causal (n : node) : Prop :=
    exists {v a} (g : AcyGraph v a), nl_graph_of_node n g.

  Definition nl_global_causal (G : global) : Prop :=
    Forall nl_node_causal G.

  Lemma nl_global_causal_find:
    forall G n,
      nl_global_causal G ->
      find_node n.(n_name) G = Some n ->
      nl_node_causal n.
  Proof.
    intros G n Hcaus Hfind.
    eapply Forall_forall; eauto.
    eapply find_node_In; eauto.
  Qed.

  Lemma nl_TopoOrder_inv {v a} :
    forall (g : AcyGraph v a) eqs x xs,
      (forall x y, nl_depends_on eqs x y -> is_arc g y x) ->
      TopoOrder g (x :: xs) ->
      In x (vars_defined eqs) ->
      exists eq,
        In eq eqs
        /\ In x (var_defined eq)
        /\ (forall y, nl_depends_on_eq eq x y -> In y xs).
  Proof.
    intros g eqs x xs Hdep Hpref Hin.
    inversion_clear Hpref as [|? ? (? & ? & Hafter) ?].
    unfold vars_defined in Hin.
    apply in_flat_map in Hin as [eq [Heqin Hvar]].
    exists eq. repeat split; auto.
    intros y Hy.
    apply Hafter.
    left.
    apply Hdep.
    eapply Exists_exists. exists eq. split; eauto.
  Qed.

  Section NL_CAUSAL_IND.
    Variable n : node.
    Variable P_var : ident -> Prop.

    Hypothesis EqCase :
      forall eq x,
        In eq n.(n_eqs) ->
        In x (var_defined eq) ->
        (forall y, nl_depends_on_eq eq x y -> P_var y) ->
        P_var x.

    Hypothesis Inputs :
      Forall P_var (map fst n.(n_in)).

    Lemma nl_causal_ind {v a} :
      forall (g : AcyGraph v a),
        nl_graph_of_node n g ->
        Forall P_var (PS.elements (vertices g)).
    Proof.
      intros g [Hv Ha].
      specialize (has_TopoOrder g) as (xs' & Heq & Hpre).
      rewrite Heq, <- PS_For_all_Forall, <- ps_from_list_ps_of_list, PS_For_all_Forall'.
      assert (incl xs' (map fst n.(n_in) ++ vars_defined n.(n_eqs))) as Hincl.
      { intros x Hin.
        rewrite Hv in Heq.
        repeat rewrite <- ps_from_list_ps_of_list in Heq.
        rewrite <- ps_from_list_In in *.
        rewrite <- Heq, map_fst_idck, map_app in Hin.
        rewrite n.(n_defd).
        exact Hin.
      }
      clear Heq.
      induction xs' as [|x xs IH]; auto.
      apply incl_cons' in Hincl as [Hin Htail].
      assert (Forall P_var xs) as Hxs by (inversion Hpre; auto).
      constructor.
      - apply in_app_or in Hin as [Hin_in|Hin_def].
        + eapply Forall_forall.
          * exact Inputs.
          * exact Hin_in.
        + eapply nl_TopoOrder_inv in Hpre; eauto.
          destruct Hpre as (eq & Heqin & Hvar & Hdeps).
          eapply EqCase; eauto.
          intros y Hy.
          eapply Forall_forall; eauto.
      - exact Hxs.
      Qed.

    Corollary nl_node_causal_ind :
      nl_node_causal n ->
      Forall P_var (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))).
    Proof.
      intros (v & a & g & Hgraph).
      assert (Hvars := nl_causal_ind g Hgraph).
      destruct Hgraph as (Hv & _).
      rewrite <- PS_For_all_Forall in Hvars.
      rewrite <- PS_For_all_Forall', ps_from_list_ps_of_list, <- map_fst_idck, <- Hv; auto.
    Qed.
  End NL_CAUSAL_IND.
End NLUSTRECAUSALITY.

Module NLustreCausality
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX Op)
       (SynNL : NLSYNTAX Ids Op CESyn)
       (CEIsF : CEISFREE Ids Op CESyn)
       (IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
       <: NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF.
  Include NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF.
End NLustreCausality.
