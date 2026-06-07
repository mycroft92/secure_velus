(** Causality facts for NLustre nodes, dependency graphs, and variable-order induction. *)

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import String.
From Coq Require Import Lia.

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

From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Environment.
From Velus Require Import Transcription.Tr.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

Module Type NLUSTRECAUSALITYBRIDGE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (L            : LSYNTAX Ids Op)
       (Import CESyn : CESYNTAX Op)
       (Import SynNL : NLSYNTAX Ids Op CESyn)
       (Import CEIsF : CEISFREE Ids Op CESyn)
       (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
       (Import LC    : LCLOCKING Ids Op L)
       (Import LCA   : LCAUSALITY Ids Op L)
       (Import TR    : TR Ids Op OpAux L CESyn SynNL)
       (Import NLCaus : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF).

  Definition node_envo (n : L.node) : Env.t (type * clock) :=
    Env.from_list n.(L.n_out).

  Definition node_env (n : L.node) : Env.t (type * clock) :=
    Env.adds' n.(L.n_vars) (Env.adds' n.(L.n_in) (node_envo n)).

  Definition node_not_out (n : L.node) : ident -> res unit :=
    fun x =>
      if Env.mem x (node_envo n)
      then Error (msg "output variable defined as a fby")
      else OK tt.

  Lemma In_nth_error_ex {A} :
    forall (x : A) xs,
      In x xs ->
      exists k, nth_error xs k = Some x.
  Proof.
    induction xs as [|y xs IH]; [contradiction|]; intros [<-|Hin].
    - exists 0; auto.
    - destruct (IH Hin) as (k & Hk); exists (S k); auto.
  Qed.

  Lemma Forall2_in_left_ex :
    forall {A B} (P : A -> B -> Prop) xs ys x,
      Forall2 P xs ys ->
      In x xs ->
      exists y, In y ys /\ P x y.
  Proof.
    intros A B P xs ys x Hfor; induction Hfor; intros Hin; [contradiction|].
    destruct Hin as [<-|Hin].
    - exists y; split; [now left | exact H].
    - destruct (IHHfor Hin) as (y' & Hin' & HP); exists y'; split; [now right | exact HP].
  Qed.

  Lemma Forall2_in_right_ex :
    forall {A B} (P : A -> B -> Prop) xs ys y,
      Forall2 P xs ys ->
      In y ys ->
      exists x, In x xs /\ P x y.
  Proof.
    intros A B P xs ys y Hfor; induction Hfor; intros Hin; [contradiction|].
    destruct Hin as [<-|Hin].
    - exists x; split; [now left | exact H].
    - destruct (IHHfor Hin) as (x' & Hin' & HP); exists x'; split; [now right | exact HP].
  Qed.

  Lemma source_arc_of_singleton {v a} :
    forall vars eqs eq (g : AcyGraph v a) x y,
      In eq eqs ->
      (forall x y, LCA.depends_on_ck vars eqs x y -> is_arc g y x) ->
      LCA.depends_on_ck vars [eq] x y ->
      is_arc g y x.
  Proof.
    intros vars eqs eq g x y Heqin Harcs Hdep.
    apply Harcs.
    destruct Hdep as [Hdep|(ck & Hinx & Hfree)].
    - left. inversion Hdep; subst; clear Hdep.
      + eapply Exists_exists. exists eq. split; eauto.
      + inversion H0.
    - right; eauto.
  Qed.

  Lemma mmap_in_exists :
    forall {A B} (f : A -> res B) xs ys (P : A -> Prop) y,
      mmap f xs = OK ys ->
      Forall P xs ->
      In y ys ->
      exists x, In x xs /\ f x = OK y /\ P x.
  Proof.
    intros A B f xs.
    induction xs as [|x xs IH]; intros ys P y Hmap Hfor Hin; simpl in Hmap.
    - inversion Hmap; subst; contradiction.
    - inversion Hfor as [|? ? HPx HPxs]; subst; monadInv Hmap.
      destruct Hin as [<-|Hin].
      + exists x; repeat split; [now left | exact EQ | exact HPx].
      + destruct (IH _ _ _ EQ1 HPxs Hin) as (x' & Hin' & Hfx' & HPx').
        exists x'; repeat split; [now right | exact Hfx' | exact HPx'].
  Qed.

  Lemma find_base_clock_of_wi :
    forall G f n es bck sub,
      LC.wc_global G ->
      L.find_node f G = Some n ->
      Forall2 (LC.WellInstantiated bck sub) (idck n.(L.n_in)) (L.nclocksof es) ->
      find_base_clock (L.clocksof es) = bck.
  Proof.
    intros G f n es bck sub HwcG Hfind Hwi.
    eapply LC.wc_find_node in HwcG as (G' & Hwcnode); eauto.
    destruct Hwcnode as (Hwenv & _).
    apply find_base_clock_bck.
    - rewrite L.clocksof_nclocksof.
      eapply LC.WellInstantiated_bck; eauto.
      unfold idck. rewrite map_length. exact (L.n_ingt0 n).
    - apply LC.WellInstantiated_parent in Hwi.
      apply Forall_forall.
      intros ck Hin.
      rewrite L.clocksof_nclocksof in Hin.
      apply in_map_iff in Hin as (nck & Hck & Hinnck). subst ck.
      rewrite Forall_forall in Hwi.
      specialize (Hwi nck Hinnck).
      exact Hwi.
  Qed.

  Lemma app_output_clock_dep :
    forall vars (xs : list ident) (anns : list L.ann) callee bck sub x y,
      In x xs ->
      Forall2 (fun x ck => In (x, ck) vars) xs (map stripname (map snd anns)) ->
      Forall2 (LC.WellInstantiated bck sub) (idck callee.(L.n_out)) (map snd anns) ->
      Is_free_in_clock y bck ->
      exists xck,
        In (x, xck) vars
        /\ Is_free_in_clock y xck.
  Proof.
    intros vars xs anns callee bck sub x y Hinx Hclocks Houts Hfree.
    destruct (Forall2_in_left_ex _ _ _ _ Hclocks Hinx) as (xck & Hinck & Hxvars).
    apply in_map_iff in Hinck as (nc & Hck & Hinnc). subst xck.
    destruct (Forall2_in_right_ex _ _ _ _ Houts Hinnc) as (? & ? & Hwi).
    unfold LC.WellInstantiated in Hwi.
    destruct Hwi as (_ & Hinst).
    exists (fst nc). split; auto.
    eapply instck_free_bck; eauto.
  Qed.

  Lemma to_lexp_numstreams :
    forall e le,
      to_lexp e = OK le ->
      L.numstreams e = 1.
  Proof.
    intros e le Hto.
    destruct e as [c|x ann|op e ann|op e1 e2 ann|e0s es anns
                  |e0s es anns|es x b ann|x ets efs ann|e ets efs ann|f es ro anns];
      simpl in Hto; try discriminate; auto.
    - destruct es; try discriminate.
      destruct es; try discriminate.
      destruct ann as [tys nck]. destruct tys; try discriminate.
      destruct tys; try discriminate.
      destruct (to_lexp e) eqn:Hsub; try discriminate.
      inversion Hto; reflexivity.
  Qed.

  Lemma to_lexp_free :
    forall e le id,
      to_lexp e = OK le ->
      CEIsF.Is_free_in_exp id le ->
      LCA.Is_free_left id 0 e.
  Proof.
    induction e using L.exp_ind2; intros le id Hto Hfree; simpl in Hto; try discriminate.
    - now inversion Hto; subst; inversion Hfree.
    - destruct a as [xty xck]. simpl in Hto.
      inversion Hto; subst.
      inversion Hfree; subst.
      apply LCA.IFLvar.
    - destruct a as [ty ck]. simpl in Hto.
      destruct (to_lexp e) eqn:Hsub; try discriminate.
      inversion Hto; subst.
      inversion Hfree; subst.
      apply LCA.IFLunop.
      eapply IHe; eauto.
    - destruct a as [ty ck]. simpl in Hto.
      destruct (to_lexp e1) eqn:Hsub1; try discriminate.
      destruct (to_lexp e2) eqn:Hsub2; try discriminate.
      inversion Hto; subst.
      inversion Hfree; subst.
      apply LCA.IFLbinop. destruct H1 as [H1|H1].
      + left. eapply IHe1; eauto.
      + right. eapply IHe2; eauto.
    - destruct es as [|e0 es']; try discriminate.
      inversion H as [|? ? IH0 Hfor]; subst.
      destruct es' as [|e1 es'']; try discriminate.
      inversion Hfor.
      destruct a as [tys nck]. destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_lexp e0) eqn:Hsub; try discriminate.
      inversion Hto; subst.
      inversion Hfree; subst.
      + apply LCA.IFLwhen. right.
        apply LCA.IFLLnow.
        * rewrite (to_lexp_numstreams _ _ Hsub). simpl. lia.
        * eauto.
      + apply LCA.IFLwhen. left. split; simpl; auto; lia.
  Qed.

  Lemma mmap_to_lexp_free :
    forall es les x,
      mmap to_lexp es = OK les ->
      Exists (CEIsF.Is_free_in_exp x) les ->
      Exists (fun e => LCA.Is_free_left x 0 e) es.
  Proof.
    induction es as [|e es IH]; intros les x Hmap Hfree; simpl in Hmap.
    - inversion Hmap; subst; inversion Hfree.
    - monadInv Hmap; inversion Hfree; [left; eauto using to_lexp_free | right; eauto].
  Qed.

  Lemma to_cexp_eexp_free :
    forall e le id,
      to_lexp e = OK le ->
      CEIsF.Is_free_in_cexp id (Eexp le) ->
      LCA.Is_free_left id 0 e.
  Proof.
    intros e le id Hto Hfree; inversion Hfree; subst; eauto using to_lexp_free.
  Qed.

  Lemma to_cexp_numstreams :
    forall e ce,
      to_cexp e = OK ce ->
      L.numstreams e = 1.
  Proof.
    intros e ce Hto.
    destruct e as [c|x ann|op e ann|op e1 e2 ann|e0s es anns
                  |e0s es anns|es x b ann|x ets efs ann|e ets efs ann|f es ro anns];
      simpl in Hto; try discriminate; auto.
    - destruct es as [|e0 es']; try discriminate.
      destruct es'; try discriminate.
      destruct ann as [tys nck].
      destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_lexp e0) eqn:Hsub; try discriminate.
      inversion Hto; reflexivity.
    - destruct ann as [tys nck].
      destruct ets as [|et ets']; try discriminate.
      destruct ets'; try discriminate.
      destruct efs as [|ef efs']; try discriminate.
      destruct efs'; try discriminate.
      destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_cexp et) eqn:Ht; try discriminate.
      destruct (to_cexp ef) eqn:Hf; try discriminate.
      inversion Hto; reflexivity.
    - destruct ann as [tys nck].
      destruct ets as [|et ets']; try discriminate.
      destruct ets'; try discriminate.
      destruct efs as [|ef efs']; try discriminate.
      destruct efs'; try discriminate.
      destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_lexp e) eqn:Hb; try discriminate.
      destruct (to_cexp et) eqn:Ht; try discriminate.
      destruct (to_cexp ef) eqn:Hf; try discriminate.
      inversion Hto; reflexivity.
  Qed.

  Lemma to_cexp_free :
    forall e ce id,
      to_cexp e = OK ce ->
      CEIsF.Is_free_in_cexp id ce ->
      LCA.Is_free_left id 0 e.
  Proof.
    induction e using L.exp_ind2; intros ce id Hto Hfree; simpl in Hto; try discriminate.
    - inversion Hto; subst.
      eapply to_cexp_eexp_free.
      + reflexivity.
      + exact Hfree.
    - destruct a as [ty ck]. simpl in Hto.
      inversion Hto; subst.
      eapply to_cexp_eexp_free.
      + reflexivity.
      + exact Hfree.
    - destruct a as [ty ck]. simpl in Hto.
      destruct (to_lexp e) eqn:Hsub; try discriminate.
      inversion Hto; subst.
      eapply to_cexp_eexp_free; eauto.
      simpl. now rewrite Hsub.
    - destruct a as [ty ck]. simpl in Hto.
      destruct (to_lexp e1) eqn:Hsub1; try discriminate.
      destruct (to_lexp e2) eqn:Hsub2; try discriminate.
      inversion Hto; subst.
      eapply to_cexp_eexp_free; eauto.
      simpl. now rewrite Hsub1, Hsub2.
    - destruct es as [|e0 es']; try discriminate.
      destruct es'; try discriminate.
      destruct a as [tys nck]. destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_lexp e0) eqn:Hsub; try discriminate.
      inversion Hto; subst.
      eapply to_cexp_eexp_free; eauto.
      simpl. now rewrite Hsub.
    - destruct ets as [|et ets']; try discriminate.
      inversion H as [|? ? IHet Hets]; subst.
      destruct ets'; try discriminate.
      destruct efs as [|ef efs']; try discriminate.
      inversion H0 as [|? ? IHef Hefs]; subst.
      destruct efs'; try discriminate.
      destruct a as [tys nck]. destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_cexp et) eqn:Ht; try discriminate.
      destruct (to_cexp ef) eqn:Hf; try discriminate.
      inversion Hto; subst.
      inversion Hfree; subst.
      + apply LCA.IFLmerge. left. split; simpl; auto; lia.
      + apply LCA.IFLmerge. right. left.
        apply LCA.IFLLnow.
        * rewrite (to_cexp_numstreams _ _ Ht). simpl. lia.
        * eauto.
      + apply LCA.IFLmerge. right. right.
        apply LCA.IFLLnow.
        * rewrite (to_cexp_numstreams _ _ Hf). simpl. lia.
        * eauto.
    - destruct ets as [|et ets']; try discriminate.
      inversion H as [|? ? IHet Hets]; subst.
      destruct ets'; try discriminate.
      destruct efs as [|ef efs']; try discriminate.
      inversion H0 as [|? ? IHef Hefs]; subst.
      destruct efs'; try discriminate.
      destruct a as [tys nck]. destruct tys as [|ty tys']; try discriminate.
      destruct tys'; try discriminate.
      destruct (to_lexp e) eqn:Hb; try discriminate.
      destruct (to_cexp et) eqn:Ht; try discriminate.
      destruct (to_cexp ef) eqn:Hf; try discriminate.
      inversion Hto; subst.
      inversion Hfree; subst.
      + apply LCA.IFLite. left. split.
        * simpl. lia.
        * eapply to_lexp_free; eauto.
      + apply LCA.IFLite. right. left.
        apply LCA.IFLLnow.
        * rewrite (to_cexp_numstreams _ _ Ht). simpl. lia.
        * eauto.
      + apply LCA.IFLite. right. right.
        apply LCA.IFLLnow.
        * rewrite (to_cexp_numstreams _ _ Hf). simpl. lia.
        * eauto.
  Qed.

  Lemma depends_on_singleton :
    forall xs es x y k,
      nth_error xs k = Some x ->
      LCA.Is_free_left_list y k es ->
      LCA.depends_on [(xs, es)] x y.
  Proof.
    intros xs es x y k Hnth Hfree; constructor; eauto.
  Qed.

  Lemma node_env_clock_in :
    forall n x ck,
      find_clock (node_env n) x = OK ck ->
      In (x, ck) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)).
  Proof.
    intros n x ck Hfind; eapply envs_eq_find'; eauto using envs_eq_node.
  Qed.

  Lemma is_arc_trans {v a} :
    forall (g : AcyGraph v a) x y,
      is_arc g x y ->
      is_trans_arc g x y.
  Proof. intros g x y Harc; now left. Qed.

  Lemma source_defined_in_node_vars :
    forall n x,
      In x (L.vars_defined n.(L.n_eqs)) ->
      In x (map fst (L.n_in n ++ L.n_vars n ++ L.n_out n)).
  Proof.
    intros n x Hin; rewrite map_app, in_app_iff; right.
    eapply Permutation_in; [exact (L.n_defd n) | exact Hin].
  Qed.

  Lemma eqdef_depends_trans {v a} :
    forall n xs e x ck ce y (g : AcyGraph v a),
      In (xs, [e]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      find_clock (node_env n) x = OK ck ->
      to_cexp e = OK ce ->
      xs = [x] ->
      Is_free_in_caexp y ck ce ->
      is_trans_arc g y x.
  Proof.
    intros n xs e x ck ce y g Heqin Harc Hfind Hto Hxs Hfree.
    subst xs.
    inversion Hfree; subst.
    - apply is_arc_trans.
      eapply source_arc_of_singleton; eauto.
      left.
      eapply depends_on_singleton with (k:=0).
      + reflexivity.
      + apply LCA.IFLLnow.
        * rewrite (to_cexp_numstreams _ _ Hto). simpl. lia.
        * eapply to_cexp_free; eauto.
    - apply is_arc_trans.
      apply Harc.
      right. exists ck. split.
      + apply node_env_clock_in. exact Hfind.
      + assumption.
  Qed.

  Lemma eqfby_depends_trans {v a} :
    forall n xs e0 e1 anns x ck y (g : AcyGraph v a),
      In (xs, [L.Efby [e0] [e1] anns]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      find_clock (node_env n) x = OK ck ->
      xs = [x] ->
      Is_free_in_clock y ck ->
      is_trans_arc g y x.
  Proof.
    intros n xs e0 e1 anns x ck y g Heqin Harc Hfind -> Hfree.
    apply is_arc_trans, Harc; right; exists ck; auto using node_env_clock_in.
  Qed.

  Lemma eqapp_args_trans_none {v a} :
    forall n xs f es anns x y k les (g : AcyGraph v a),
      In (xs, [L.Eapp f es None anns]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      mmap to_lexp es = OK les ->
      nth_error xs k = Some x ->
      k < Datatypes.length anns ->
      Exists (CEIsF.Is_free_in_exp y) les ->
      is_trans_arc g y x.
  Proof.
    intros n xs f es anns x y k les g Heqin Harc Hmap Hnth Hk Hfree.
    apply is_arc_trans.
    eapply source_arc_of_singleton; eauto.
    left.
    eapply depends_on_singleton; eauto.
    apply LCA.IFLLnow.
    - simpl. exact Hk.
    - apply LCA.IFLapp.
      + exact Hk.
      + exists 0.
        eapply mmap_to_lexp_free; eauto.
  Qed.

  Lemma eqapp_args_trans_reset {v a} :
    forall n xs f es r anns x y k les (g : AcyGraph v a),
      In (xs, [L.Eapp f es (Some r) anns]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      mmap to_lexp es = OK les ->
      nth_error xs k = Some x ->
      k < Datatypes.length anns ->
      Exists (CEIsF.Is_free_in_exp y) les ->
      is_trans_arc g y x.
  Proof.
    intros n xs f es r anns x y k les g Heqin Harc Hmap Hnth Hk Hfree.
    apply is_arc_trans.
    eapply source_arc_of_singleton; eauto.
    left.
    eapply depends_on_singleton; eauto.
    apply LCA.IFLLnow.
    - simpl. exact Hk.
    - apply LCA.IFLreset.
      + exact Hk.
      + left. exists 0.
        eapply mmap_to_lexp_free; eauto.
  Qed.

  Lemma eqapp_base_clock_trans {v a} :
    forall n xs (anns : list L.ann) (callee : L.node) bck (sub : ident_map) x y
      (g : AcyGraph v a),
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      In x xs ->
      Forall2 (fun x ck => In (x, ck) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)))
              xs (map stripname (map snd anns)) ->
      Forall2 (LC.WellInstantiated bck sub) (idck callee.(L.n_out)) (map snd anns) ->
      Is_free_in_clock y bck ->
      is_trans_arc g y x.
  Proof.
    intros n xs anns callee bck sub x y g Harc Hinx Hclocks Houts Hfree.
    destruct (app_output_clock_dep
                (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                xs anns callee bck sub x y Hinx Hclocks Houts Hfree)
      as (xck & Hinxck & Hfreeck).
    apply is_arc_trans.
    apply Harc.
    right. exists xck. split; auto.
  Qed.

  Lemma eqapp_reset_clock_trans {v a} :
    forall n xs f es r ty ckr name anns x y k (g : AcyGraph v a),
      In (xs, [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      nth_error xs k = Some x ->
      k < Datatypes.length anns ->
      In (r, ckr) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      Is_free_in_clock y ckr ->
      is_trans_arc g y x.
  Proof.
    intros n xs f es r ty ckr name anns x y k g Heqin Harc Hnth Hk Hinr Hfree.
    assert (Hyr : is_arc g y r).
    { apply Harc.
      right. exists ckr. split; auto.
    }
    assert (Hrx : is_arc g r x).
    { eapply source_arc_of_singleton
        with (vars := idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
             (eqs := n.(L.n_eqs))
             (eq := (xs, [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns])).
      - exact Heqin.
      - exact Harc.
      - left.
        eapply depends_on_singleton
          with (xs := xs)
               (es := [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns])
               (x := x)
               (y := r)
               (k := k).
        + exact Hnth.
        + apply LCA.IFLLnow.
          * simpl. exact Hk.
          * apply LCA.IFLreset.
            -- exact Hk.
            -- right. apply LCA.IFLvar.
    }
    unfold is_trans_arc, is_arc in *.
    eapply has_arc_trans; eauto.
  Qed.

  Lemma eqapp_reset_var_trans {v a} :
    forall n xs f es r ty ckr name anns x k (g : AcyGraph v a),
      In (xs, [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns]) n.(L.n_eqs) ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      nth_error xs k = Some x ->
      k < Datatypes.length anns ->
      is_trans_arc g r x.
  Proof.
    intros n xs f es r ty ckr name anns x k g Heqin Harc Hnth Hk.
    apply is_arc_trans.
    eapply source_arc_of_singleton
      with (vars := idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
           (eqs := n.(L.n_eqs))
           (eq := (xs, [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns])).
    - exact Heqin.
    - exact Harc.
    - left.
      eapply depends_on_singleton
        with (xs := xs)
             (es := [L.Eapp f es (Some (L.Evar r (ty, (ckr, name)))) anns])
             (x := x)
             (y := r)
             (k := k).
      + exact Hnth.
      + apply LCA.IFLLnow.
        * simpl. exact Hk.
        * apply LCA.IFLreset.
          -- exact Hk.
          -- right. apply LCA.IFLvar.
  Qed.

  Lemma nth_error_lt_anns :
    forall xs (anns : list L.ann) x k,
      Forall2 (fun x nc => LiftO True (eq x) (snd nc)) xs (map snd anns) ->
      nth_error xs k = Some x ->
      k < Datatypes.length anns.
  Proof.
    intros xs anns x k Hfor Hnth.
    apply Forall2_length in Hfor.
    rewrite map_length in Hfor.
    assert (Hk : k < Datatypes.length xs).
    { apply nth_error_Some.
      rewrite Hnth.
      discriminate.
    }
    rewrite Hfor in Hk.
    exact Hk.
  Qed.

  Lemma map_stripname_map_snd_clock_of_nclock :
    forall (anns : list L.ann),
      map stripname (map snd anns) = map L.clock_of_nclock anns.
  Proof. intros anns; unfold L.clock_of_nclock; now rewrite map_map. Qed.

  Lemma lhscks_clock_of_nclock :
    forall n xs (anns : list L.ann),
      Forall2
        (fun x ck => In (x, ck) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)))
        xs (map L.clock_of_nclock anns) ->
      Forall2
        (fun x ck => In (x, ck) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)))
        xs (map stripname (map snd anns)).
  Proof.
    intros n xs anns Hlhscks; now rewrite map_stripname_map_snd_clock_of_nclock.
  Qed.

  Lemma to_equation_depends_trans {v a} :
    forall G n eq eq' (g : AcyGraph v a) x y,
      LC.wc_global G ->
      In eq n.(L.n_eqs) ->
      LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) eq ->
      (forall x y,
          LCA.depends_on_ck (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))
                            n.(L.n_eqs) x y ->
          is_arc g y x) ->
      to_equation (node_env n) (node_not_out n) eq = OK eq' ->
      NLCaus.nl_depends_on_eq eq' x y ->
      is_trans_arc g y x.
  Proof.
    intros G n [xs es] eq' g x y HwcG Heqin HwcEq Harc Htoeq Hdep.
    destruct HwcEq as (HwcEs & Hlhsncks & Hlhscks).
    destruct es as [|e es']; try discriminate.
    destruct es'; try discriminate.
    simpl in Htoeq.
    destruct e as [c|z ann|op e ann|op e1 e2 ann|e0s es0 anns
                  |e0s es0 anns|es0 z b ann|z ets efs ann|econd ets efs ann|f es0 ro anns];
      simpl in Htoeq.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Econst c)); eauto; reflexivity.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Evar z ann)); eauto; reflexivity.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Eunop op e ann)); eauto; reflexivity.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Ebinop op e1 e2 ann)); eauto; reflexivity.
    - destruct e0s as [|einit e0s'].
      { destruct xs as [|xbad xs']; simpl in Htoeq; try discriminate.
        destruct xs'; simpl in Htoeq; try discriminate.
        monadInv Htoeq.
      }
      destruct e0s' as [|einit' e0s''].
      2:{ destruct xs as [|xbad xs']; simpl in Htoeq; try discriminate.
          destruct xs'; simpl in Htoeq; try discriminate.
          monadInv Htoeq.
      }
      destruct es0 as [|enext es1].
      { destruct xs as [|xbad xs']; simpl in Htoeq; try discriminate.
        destruct xs'; simpl in Htoeq; try discriminate.
        monadInv Htoeq.
      }
      destruct es1 as [|enext' es1'].
      2:{ destruct xs as [|xbad xs']; simpl in Htoeq; try discriminate.
          destruct xs'; simpl in Htoeq; try discriminate.
          monadInv Htoeq.
      }
      destruct xs as [|x0 xs'].
      { simpl in Htoeq. discriminate. }
      destruct xs' as [|x1 xs''].
      2:{ simpl in Htoeq. discriminate. }
      simpl in Htoeq.
      monadInv Htoeq.
      simpl in Hdep.
      destruct Hdep as [Hx Hfree]. subst x.
      eapply (eqfby_depends_trans n [x0] einit enext anns); eauto; reflexivity.
    - destruct xs as [|? [|]]; simpl in Htoeq; try discriminate; monadInv Htoeq.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Ewhen es0 z b ann)); eauto; reflexivity.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Emerge z ets efs ann)); eauto; reflexivity.
    - destruct xs as [|x0 [|]]; try discriminate; monadInv Htoeq;
      destruct Hdep as [-> ?]; eapply (eqdef_depends_trans n [x0] (L.Eite econd ets efs ann)); eauto; reflexivity.
    - destruct ro as [r|].
      + destruct r as [rc|r annr|rop re annr|rop re1 re2 annr
                      |re0s res0 ranns|re0s res0 ranns|res0 rz rb rann
                      |rz rets refs rann|rcond rets refs rann|rf resr rro ranns];
          try discriminate.
        destruct annr as [ty [ckr name]].
        simpl in Htoeq.
        destruct (mmap to_lexp es0) as [les|err] eqn:Hmap; try discriminate.
        inversion Htoeq; subst.
        inversion HwcEs as [|? ? Happ Hnil]; subst; clear HwcEs Hnil.
        inversion_clear Happ
          as [| | | | | | | | | | |?????? bck sub HwcArgs Hfindcallee HwiIn HwiOut Hwr Hckr].
        simpl in Hlhsncks, Hlhscks.
        rewrite app_nil_r in Hlhsncks, Hlhscks.
        destruct Hdep as [Hinx [Hfreeargs|[Hyreset|Hclockr]]].
        * inversion Hfreeargs; subst.
          -- destruct (In_nth_error_ex _ _ Hinx) as (k & Hnth).
             pose proof (nth_error_lt_anns _ _ _ _ Hlhsncks Hnth) as Hk.
             eapply eqapp_args_trans_reset; eauto.
          -- pose proof (find_base_clock_of_wi G f n0 es0 bck sub HwcG Hfindcallee HwiIn) as Hbase.
             rewrite Hbase in H.
             eapply (eqapp_base_clock_trans n xs anns n0 bck sub x y g);
               [ exact Harc
               | exact Hinx
               | eapply lhscks_clock_of_nclock; exact Hlhscks
               | exact HwiOut
               | exact H ].
        * subst y.
          destruct (In_nth_error_ex _ _ Hinx) as (k & Hnth).
          pose proof (nth_error_lt_anns _ _ _ _ Hlhsncks Hnth) as Hk.
          eapply (eqapp_reset_var_trans n xs f es0 r ty ckr name anns x k g);
            [ exact Heqin
            | exact Harc
            | exact Hnth
            | exact Hk ].
        * destruct (In_nth_error_ex _ _ Hinx) as (k & Hnth).
          pose proof (nth_error_lt_anns _ _ _ _ Hlhsncks Hnth) as Hk.
          inversion Hwr; subst; clear Hwr;
            eapply (eqapp_reset_clock_trans n xs f es0 r ty ckr _ anns x y k g);
              eauto.
      + destruct (mmap to_lexp es0) as [les|err] eqn:Hmap; try discriminate.
        inversion Htoeq; subst.
        inversion HwcEs as [|? ? Happ Hnil]; subst; clear HwcEs Hnil.
        inversion_clear Happ
          as [| | | | | | | | | | ???? bck sub HwcArgs Hfindcallee HwiIn HwiOut |].
        simpl in Hlhsncks, Hlhscks.
        rewrite app_nil_r in Hlhsncks, Hlhscks.
        destruct Hdep as [Hinx Hfree].
        inversion Hfree; subst.
        * destruct (In_nth_error_ex _ _ Hinx) as (k & Hnth).
          pose proof (nth_error_lt_anns _ _ _ _ Hlhsncks Hnth) as Hk.
          eapply eqapp_args_trans_none; eauto.
        * pose proof (find_base_clock_of_wi G f n0 es0 bck sub HwcG Hfindcallee HwiIn) as Hbase.
          rewrite Hbase in H.
          eapply (eqapp_base_clock_trans n xs anns n0 bck sub x y g);
            [ exact Harc
            | exact Hinx
            | eapply lhscks_clock_of_nclock; exact Hlhscks
            | exact HwiOut
            | exact H ].
  Qed.

  Lemma complete_order_graph :
    forall xs,
      NoDup xs ->
      exists v a (g : AcyGraph v a),
        PS.Equal (vertices g) (PSP.of_list xs)
        /\ ForallTail (fun x xs => forall y, In y xs -> is_arc g y x) xs.
  Proof.
    induction xs as [|x xs IH]; intro Hnd.
    - exists PS.empty, empty_arc_set, AGempty.
      split.
      + intros y. split; intro Hy.
        * destruct (not_In_empty _ Hy).
        * rewrite ps_of_list_In in Hy. contradiction.
      + constructor.
    - apply NoDup_cons_iff in Hnd as [Hnin Hnd].
      destruct (IH Hnd) as (v & a & g & Hv & Htail).
      assert (AcyGraph (PS.add x v) (add_after (PSP.of_list xs) x a)) as g'.
      { eapply add_after_AcyGraph'; eauto.
        - intro Hin. apply Hnin. rewrite Hv in Hin. rewrite ps_of_list_In in Hin. exact Hin.
        - intro Hin. apply Hnin. rewrite ps_of_list_In in Hin. exact Hin.
        - rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
          rewrite Forall_forall.
          intros y Hy.
          rewrite Hv, ps_of_list_In.
          exact Hy.
      }
      exists (PS.add x v), (add_after (PSP.of_list xs) x a), g'.
      split.
      + intros y. split; intro Hy.
        * apply PS.add_spec in Hy as [Hy|Hy].
          -- subst. rewrite ps_of_list_In. now left.
          -- rewrite Hv, ps_of_list_In in Hy.
             rewrite ps_of_list_In. now right.
        * rewrite ps_of_list_In in Hy.
          apply PS.add_spec.
          destruct Hy as [Hy|Hy].
          -- left. symmetry. exact Hy.
          -- right. rewrite Hv, ps_of_list_In. exact Hy.
      + constructor.
        * intros y Hy.
          apply add_after_has_arc2.
          rewrite ps_of_list_In; auto.
        * eapply ForallTail_impl.
          2: exact Htail.
          intros z zs Hz y Hy.
          eapply add_after_has_arc1.
          eapply Hz; eauto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Bridge theorems: Lustre causality transfers to NLustre causality   *)
  (* ------------------------------------------------------------------ *)

  (** x is always the defined variable in an NLustre equation that depends. *)
  Lemma nl_depends_on_eq_var_defined :
    forall eq x y,
      NLCaus.nl_depends_on_eq eq x y ->
      In x (var_defined eq).
  Proof.
    intros eq x y Hdep.
    destruct eq as [z ck ce | xs ck f es ro | z ck v0 ck0]; simpl in Hdep |- *.
    - destruct Hdep as [Hx _]. subst. now left.
    - destruct ro as [[r ckr]|]; destruct Hdep as [Hinx _]; exact Hinx.
    - destruct Hdep as [Hx _]. subst. now left.
  Qed.

  (** Extract the mmap proof from a successful to_node call. *)
  Lemma to_node_eqs :
    forall n n' Hpref,
      to_node n Hpref = OK n' ->
      mmap (to_equation (node_env n) (node_not_out n)) n.(L.n_eqs) = OK n'.(n_eqs).
  Proof.
    intros n n' Hpref Htr.
    unfold to_node in Htr.
    destruct (mmap_to_equation
                (Env.adds' (L.n_vars n) (Env.adds' (L.n_in n) (Env.from_list (L.n_out n))))
                (fun x : Env.key =>
                   if Env.mem x (Env.from_list (L.n_out n))
                   then Error (msg "output variable defined as a fby")
                   else OK tt) n)
      as [[neqs Hmmap]|err]; [|discriminate].
    inv Htr. unfold node_env, node_envo, node_not_out. exact Hmmap.
  Qed.

  (** If a Lustre node is causal, its translated NLustre node is causal. *)
  Lemma to_node_causal :
    forall G n n' Hpref,
      LC.wc_global G ->
      LC.wc_node G n ->
      to_node n Hpref = OK n' ->
      LCA.node_causal n ->
      NLCaus.nl_node_causal n'.
  Proof.
    intros G n n' Hpref HwcG HwcN Htr Hcaus.
    (* Unpack the source causal graph. *)
    destruct Hcaus as (v & a & g_src & Hgraph_src).
    destruct Hgraph_src as [Hv_src Harc_src].
    (* Obtain a topological order for the source graph. *)
    destruct (has_TopoOrder g_src) as (xs & Heq_xs & Htopo).
    (* Build a complete linear-order NLustre graph over the same vertex set. *)
    destruct (complete_order_graph xs (TopoOrder_NoDup g_src xs Htopo))
      as (v' & a' & g' & Hv' & Htail').
    (* Extract the equation mmap and wc_equation facts. *)
    assert (Hmmap : mmap (to_equation (node_env n) (node_not_out n)) n.(L.n_eqs) = OK n'.(n_eqs))
      by exact (to_node_eqs n n' Hpref Htr).
    destruct HwcN as (_ & _ & _ & HwcEqs).
    (* Record that in/vars/out are preserved by translation. *)
    assert (Hin_eq  : L.n_in   n = n'.(n_in))   by exact (to_node_in   n n' Hpref Htr).
    assert (Hvars_eq: L.n_vars n = n'.(n_vars))  by exact (to_node_vars n n' Hpref Htr).
    assert (Hout_eq : L.n_out  n = n'.(n_out))   by exact (to_node_out  n n' Hpref Htr).
    (* Exhibit the NLustre graph. *)
    exists v', a', g'.
    unfold NLCaus.nl_graph_of_node, NLCaus.nl_graph_of_eqs.
    split.
    - (* Vertices of g' equal the NLustre node variable set. *)
      rewrite <- Hin_eq, <- Hvars_eq, <- Hout_eq.
      transitivity (PSP.of_list xs).
      + exact Hv'.
      + transitivity (vertices g_src).
        * symmetry. exact Heq_xs.
        * exact Hv_src.
    - (* Every NLustre dependency yields an arc in g'. *)
      intros x y Hdep.
      unfold NLCaus.nl_depends_on in Hdep.
      apply Exists_exists in Hdep as [eq' [Heq'in Hdep']].
      (* Recover the source equation corresponding to eq'. *)
      destruct (mmap_in_exists
                  (to_equation (node_env n) (node_not_out n))
                  n.(L.n_eqs) n'.(n_eqs)
                  (LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)))
                  eq' Hmmap HwcEqs Heq'in)
        as (eq & Heqin & Heqto & Hwceq).
      (* Lift the NLustre dependency to a transitive arc in g_src. *)
      assert (Htrans : is_trans_arc g_src y x).
      { eapply to_equation_depends_trans; eauto. }
      (* Show x ∈ xs using the vertex-set equalities. *)
      assert (Hinx : In x xs).
      { assert (Hxvar : In x (var_defined eq'))
          by exact (nl_depends_on_eq_var_defined eq' x y Hdep').
        apply ok_fst_defined in Heqto.
        rewrite <- Heqto in Hxvar.
        assert (Hvd : In x (L.vars_defined n.(L.n_eqs))).
        { unfold L.vars_defined. apply in_flat_map. exists eq. split; auto. }
        apply source_defined_in_node_vars in Hvd.
        rewrite <- ps_of_list_In.
        rewrite <- Heq_xs.
        rewrite Hv_src.
        rewrite ps_of_list_In, map_fst_idck.
        exact Hvd. }
      (* Split xs at x to apply the ForallTail properties. *)
      apply in_split in Hinx as (xs1 & xs2 & Hxsplit). subst xs.
      (* y lands in xs2 by the TopoOrder invariant. *)
      assert (Hy_in : In y xs2).
      { destruct (ForallTail_middle _ x xs1 xs2 Htopo) as (_ & _ & Ha).
        exact (Ha y Htrans). }
      (* An arc g' y x exists by the complete-order-graph invariant. *)
      exact (ForallTail_middle _ x xs1 xs2 Htail' y Hy_in).
  Qed.

  (** If a Lustre global is causal, its translated NLustre global is causal. *)
  Theorem to_global_causal :
    forall G P Hprefs,
      LC.wc_global G ->
      to_global G Hprefs = OK P ->
      Forall LCA.node_causal G ->
      NLCaus.nl_global_causal P.
  Proof.
    unfold NLCaus.nl_global_causal.
    induction G as [|n Gtl IH]; intros P Hprefs HwcG Htrans Hcaus.
    - inv Htrans. constructor.
    - monadInv Htrans.
      inversion Hcaus as [|? ? Hcaus_n Hcaus_tl]; subst.
      inversion HwcG as [|? ? Hwctl HwcN]; subst.
      constructor.
      + eapply to_node_causal; eauto.
      + eapply IH; [exact Hwctl | exact EQ1 | exact Hcaus_tl].
  Qed.

End NLUSTRECAUSALITYBRIDGE.

Module NLustreCausalityBridge
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (L     : LSYNTAX Ids Op)
       (CESyn : CESYNTAX Op)
       (SynNL : NLSYNTAX Ids Op CESyn)
       (CEIsF : CEISFREE Ids Op CESyn)
       (IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
       (LC    : LCLOCKING Ids Op L)
       (LCA   : LCAUSALITY Ids Op L)
       (TR    : TR Ids Op OpAux L CESyn SynNL)
       (NLCaus : NLUSTRECAUSALITY Ids Op CESyn SynNL CEIsF IsF)
       <: NLUSTRECAUSALITYBRIDGE Ids Op OpAux L CESyn SynNL CEIsF IsF LC LCA TR NLCaus.
  Include NLUSTRECAUSALITYBRIDGE Ids Op OpAux L CESyn SynNL CEIsF IsF LC LCA TR NLCaus.
End NLustreCausalityBridge.
