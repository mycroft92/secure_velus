(** Security signatures, call instantiation, and global signature invariants. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Export SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Coq   Require Import List Sorting.Permutation.
From Coq Require Import String.
From compcert Require Import common.Errors.
Import List.ListNotations.

Module Type SIGNATURE
  (Import Ids : IDS)
  (Import SC  : SECMONAD Ids).
Import SECMONADNotations.

Record signature := mkSig {
    s_name : ident;
    s_in   : list ident;
    s_out  : list ident;
    s_reset: ident;
    s_clk  : ident;
    s_constraints : list constraint
}.
Definition secglobal := list signature.

Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

Section Type_Substitutions.

  Local Definition subst_ident_in_type (ty: ST) (x: ident) (v: ST): ST :=
    match (my_set_mem x ty) with
    | false =>  ty
    | true  => (st_remove x ty) ⊔ (st_remove x v)
    end.

  Definition subst_inp_ident_in_constraint (c: constraint) (x: ident) (v: ST): Sec constraint :=
    match c with
    | (ty, [x']) =>
      if ident_eqb x x' then
        error (MSG "Something wrong with fresh_gen, ident is regenerated in an inner sig. " :: [CTX x])
      else ret (subst_ident_in_type ty x v, [x'])
    | _ => error (msg "malformed constraint")
    end.

  Definition subst_ident_in_constraints (cs: list constraint) (x: ident) (v: ST)
   : Sec (list constraint) :=
   mmap (fun c => subst_inp_ident_in_constraint c x v) cs.

  Fixpoint subst_constraints_inp_map (cs: list constraint) (xs: list ident) (vs: list ST): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs =>
      do cs' <- subst_ident_in_constraints cs x v;
      subst_constraints_inp_map cs' xs vs
    | _, _ => error (msg "Malformed replace map")
    end.

  Definition subst_ident_constraint (c: constraint) (x v: ident): Sec constraint :=
    if ident_eqb x v then error (msg "Illegal same ident substitution") else
    (match c with
    | (ty, [x']) =>
       if ident_eqb x x' then
        ret (subst_ident_in_type ty x [v], [v])
       else ret (subst_ident_in_type ty x [v], [x'])
    | _  => error (msg "Malformed constraint")
    end).

  Definition subst_ident_constraints (cs: list constraint) (x v: ident): Sec (list constraint) :=
    mmap (fun c => subst_ident_constraint c x v) cs.

  Fixpoint subst_constraints_out_map (cs: list constraint) (xs: list ident) (vs: list ident): Sec (list constraint) :=
    match xs,vs with
    | [], [] => ret cs
    | x::xs, v::vs =>
      match findST cs v with
      | Some _ =>
          error (MSG "Output substitution captures an existing RHS identifier: " :: [CTX v])
      | None =>
          do cs' <- subst_ident_constraints cs x v;
          subst_constraints_out_map cs' xs vs
      end
    | _, _ => error (msg "Malformed replace map")
    end.

  Definition generate_constraints (sig: signature)
    (inp: list ST)
    (clk: ST)
    (res: ST)
    (out: list ident): Sec (list constraint) :=
    do inp_subst_constraints <- subst_constraints_inp_map sig.(s_constraints) sig.(s_in) inp;
    do clk_subst_constraints <- subst_ident_in_constraints inp_subst_constraints sig.(s_clk) clk;
    do res_subst_constraints <- subst_ident_in_constraints clk_subst_constraints sig.(s_reset) res;
    do out_subst_constraints <- subst_constraints_out_map res_subst_constraints sig.(s_out) out;
    mmap (fun x =>
            do st <- option_to_sec (findST out_subst_constraints x);
            ret (st, [x])) out.

  Definition signature_good (sig: signature) : Prop :=
    wf_constraints sig.(s_constraints)
    /\ Permutation (map snd sig.(s_constraints))
                   (map (fun ty => [ty]) sig.(s_out)).

  Definition secglobal_good (G: secglobal) : Prop :=
    forall f sig,
      find_signature f G = Some sig ->
      signature_good sig.

  Lemma secglobal_good_nil:
    secglobal_good [].
  Proof.
    intros f sig Hfind.
    simpl in Hfind. discriminate.
  Qed.

  Lemma secglobal_good_cons:
    forall sig G,
      signature_good sig ->
      secglobal_good G ->
      secglobal_good (sig :: G).
  Proof.
    intros sig G Hsig Hglob f sig' Hfind.
    simpl in Hfind.
    destruct (ident_eqb sig.(s_name) f) eqn:Hname.
    - inversion Hfind; subst sig'. exact Hsig.
    - eapply Hglob; eauto.
  Qed.

  Definition call_constraints_shape (G: secglobal) : Prop :=
    forall f sig inptyp ckty rstty outtyp cns st st',
      find_signature f G = Some sig ->
      NoDup outtyp ->
      generate_constraints sig inptyp ckty rstty outtyp st = OK (cns, st') ->
      wf_constraints cns
      /\ map snd cns = map (fun ty => [ty]) outtyp.

  Definition signature_scope (sig: signature) : list ident :=
    sig.(s_in) ++ sig.(s_out) ++ [sig.(s_clk); sig.(s_reset)].

  Definition signature_scoped (sig: signature) : Prop :=
    constraints_scoped (signature_scope sig) sig.(s_constraints).

  Definition signature_scope_sec (sig: signature) : Prop :=
    forall ty, In ty (signature_scope sig) -> exists n, ty = Ids.gensym Ids.sec n.

  Definition secglobal_scope_sec (G: secglobal) : Prop :=
    forall f sig,
      find_signature f G = Some sig ->
      signature_scope_sec sig.

  Lemma sec_reset_not_in_signature_scope:
    forall sig rst_inst,
      signature_scope_sec sig ->
      (exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
      ~ In rst_inst (signature_scope sig).
  Proof.
    intros sig rst_inst Hsec (nreset & Hrsteq) Hin.
    specialize (Hsec _ Hin) as (nsec & Hseceq).
    rewrite Hrsteq in Hseceq.
    apply gensym_injective in Hseceq as [Hpref _].
    symmetry in Hpref.
    exact (Ids.sec_neq_sec_reset Hpref).
  Qed.

  Lemma secglobal_scope_sec_nil:
    secglobal_scope_sec [].
  Proof.
    intros f sig Hfind.
    simpl in Hfind. discriminate.
  Qed.

  Lemma secglobal_scope_sec_cons:
    forall sig G,
      signature_scope_sec sig ->
      secglobal_scope_sec G ->
      secglobal_scope_sec (sig :: G).
  Proof.
    intros sig G Hsig Hglob f sig' Hfind.
    simpl in Hfind.
    destruct (ident_eqb sig.(s_name) f) eqn:Hname.
    - inversion Hfind; subst sig'. exact Hsig.
    - eapply Hglob; eauto.
  Qed.

  Definition signature_fields_agree (n1 n2: signature) : Prop :=
    n1.(s_in) = n2.(s_in)
    /\ n1.(s_out) = n2.(s_out)
    /\ n1.(s_reset) = n2.(s_reset)
    /\ n1.(s_clk) = n2.(s_clk).

  Definition type_fresh (scope: list ident) (st: ST) : Prop :=
    Forall (fun x => ~ In x scope) st.

  Definition types_fresh (scope: list ident) (sts: list ST) : Prop :=
    Forall (type_fresh scope) sts.

  Definition outputs_fresh (scope: list ident) (outs: list ident) : Prop :=
    Forall (fun x => ~ In x scope) outs.

  Definition call_subst_fresh
    (sig: signature) (inptyp: list ST) (ckty rstty: ST) (outtyp: list ident) : Prop :=
    types_fresh (signature_scope sig) inptyp
    /\ type_fresh (signature_scope sig) ckty
    /\ type_fresh (signature_scope sig) rstty
    /\ outputs_fresh (signature_scope sig) outtyp.

  Definition call_actuals_scoped
    (scope: list ident) (inptyp: list ST) (ckty: ST) (outtyp: list ident) : Prop :=
    Forall (st_scoped scope) inptyp
    /\ st_scoped scope ckty
    /\ Forall (fun x => In x scope) outtyp.

  Definition call_subst_scoped
    (scope: list ident) (inptyp: list ST) (ckty rstty: ST) (outtyp: list ident) : Prop :=
    call_actuals_scoped scope inptyp ckty outtyp
    /\ st_scoped scope rstty.

  Definition scope_fresh (scope: list ident) (sig: signature) : Prop :=
    forall x, In x scope -> ~ In x (signature_scope sig).

  Definition secglobal_scope_fresh (scope: list ident) (G: secglobal) : Prop :=
    forall f sig,
      find_signature f G = Some sig ->
      scope_fresh scope sig.

  Definition scope_lower_bounded (scope: list ident) (st: ident) : Prop :=
    forall ty,
      In ty scope ->
      exists n, ty = Ids.gensym Ids.sec n /\ (st <= n)%positive.

  Definition signature_scope_bounded_above (sig: signature) (st: ident) : Prop :=
    forall ty,
      In ty (signature_scope sig) ->
      exists n, ty = Ids.gensym Ids.sec n /\ (n < st)%positive.

  Definition secglobal_scope_bounded_above (G: secglobal) (st: ident) : Prop :=
    forall f sig,
      find_signature f G = Some sig ->
      signature_scope_bounded_above sig st.

  Lemma secglobal_scope_bounded_above_nil:
    forall st, secglobal_scope_bounded_above nil st.
  Proof.
    intros st f sig Hfind.
    simpl in Hfind. discriminate.
  Qed.

  Lemma secglobal_scope_bounded_above_cons:
    forall st sig G,
      signature_scope_bounded_above sig st ->
      secglobal_scope_bounded_above G st ->
      secglobal_scope_bounded_above (sig :: G) st.
  Proof.
    intros st sig G Hsig HG f sig' Hfind.
    simpl in Hfind.
    destruct (ident_eqb sig.(s_name) f) eqn:Hname.
    - inversion Hfind; subst. exact Hsig.
    - eapply HG; eauto.
  Qed.

  Lemma scope_fresh_from_bounds:
    forall scope sig st,
      scope_lower_bounded scope st ->
      signature_scope_bounded_above sig st ->
      scope_fresh scope sig.
  Proof.
    intros scope sig st Hlo Hhi ty Hinscope Hinsig.
    destruct (Hlo ty Hinscope) as (nlo & Hloeq & Hlole).
    destruct (Hhi ty Hinsig) as (nhi & Hhieq & Hhilt).
    rewrite Hloeq in Hhieq.
    apply gensym_injective in Hhieq as [_ Hidx].
    subst nhi.
    assert (Hcontra : (nlo < nlo)%positive)
      by (eapply Pos.lt_le_trans; [exact Hhilt | exact Hlole]).
    exfalso.
    exact (Pos.lt_irrefl _ Hcontra).
  Qed.

  Lemma signature_scope_bounded_above_monotone:
    forall sig st st',
      signature_scope_bounded_above sig st ->
      (st <= st')%positive ->
      signature_scope_bounded_above sig st'.
  Proof.
    intros sig st st' Hbound Hle ty Hin.
    destruct (Hbound ty Hin) as (n & Hn & Hlt).
    exists n. split; auto.
    eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma secglobal_scope_bounded_above_monotone:
    forall G st st',
      secglobal_scope_bounded_above G st ->
      (st <= st')%positive ->
      secglobal_scope_bounded_above G st'.
  Proof.
    intros G st st' Hbound Hle f sig Hfind.
    eapply signature_scope_bounded_above_monotone; eauto.
  Qed.

  Lemma signature_fields_agree_scope_eq:
    forall n1 n2,
      signature_fields_agree n1 n2 ->
      signature_scope n1 = signature_scope n2.
  Proof.
    intros n1 n2 [Hin [Hout [Hrst Hclk]]].
    unfold signature_scope.
    now rewrite Hin, Hout, Hclk, Hrst.
  Qed.

  Lemma scope_fresh_fields_agree:
    forall scope n1 n2,
      signature_fields_agree n1 n2 ->
      scope_fresh scope n1 ->
      scope_fresh scope n2.
  Proof.
    intros scope n1 n2 Hagree Hfresh x Hin.
    rewrite <- (signature_fields_agree_scope_eq _ _ Hagree).
    eauto.
  Qed.

  Lemma signature_scope_sec_fields_agree:
    forall n1 n2,
      signature_fields_agree n1 n2 ->
      signature_scope_sec n1 ->
      signature_scope_sec n2.
  Proof.
    intros n1 n2 Hagree Hsec ty Hin.
    destruct Hagree as [Hin' [Hout' [Hrst' Hclk']]].
    unfold signature_scope in *.
    rewrite <- Hin', <- Hout', <- Hclk', <- Hrst' in Hin.
    eauto.
  Qed.

  Lemma scope_fresh_notin_sig_scope:
    forall scope sig x,
      scope_fresh scope sig ->
      In x (signature_scope sig) ->
      ~ In x scope.
  Proof.
    intros scope sig x Hfresh Hsig Hscope.
    exact (Hfresh x Hscope Hsig).
  Qed.

  Lemma scope_fresh_notin_inputs:
    forall scope sig,
      scope_fresh scope sig ->
      Forall (fun x => ~ In x scope) sig.(s_in).
  Proof.
    intros scope sig Hfresh.
    rewrite Forall_forall.
    intros x Hin.
    eapply scope_fresh_notin_sig_scope; eauto.
    unfold signature_scope. apply in_or_app. now left.
  Qed.

  Lemma scope_fresh_notin_outputs:
    forall scope sig,
      scope_fresh scope sig ->
      Forall (fun x => ~ In x scope) sig.(s_out).
  Proof.
    intros scope sig Hfresh.
    rewrite Forall_forall.
    intros x Hin.
    eapply scope_fresh_notin_sig_scope; eauto.
    unfold signature_scope. apply in_or_app. right. apply in_or_app. left. exact Hin.
  Qed.

  Lemma scope_fresh_notin_clk:
    forall scope sig,
      scope_fresh scope sig ->
      ~ In sig.(s_clk) scope.
  Proof.
    intros scope sig Hfresh.
    eapply scope_fresh_notin_sig_scope; eauto.
    unfold signature_scope. apply in_or_app. right. apply in_or_app. right. simpl. left. reflexivity.
  Qed.

  Lemma scope_fresh_notin_reset:
    forall scope sig,
      scope_fresh scope sig ->
      ~ In sig.(s_reset) scope.
  Proof.
    intros scope sig Hfresh.
    eapply scope_fresh_notin_sig_scope; eauto.
    unfold signature_scope. apply in_or_app. right. apply in_or_app. right. simpl. right. left. reflexivity.
  Qed.

  Lemma type_fresh_from_scope_fresh:
    forall scope sig ty,
      scope_fresh scope sig ->
      st_scoped scope ty ->
      type_fresh (signature_scope sig) ty.
  Proof.
    intros scope sig ty Hfresh Hsc.
    unfold type_fresh.
    rewrite Forall_forall.
    intros x Hin Hsig.
    eapply Hfresh; eauto.
  Qed.

  Lemma types_fresh_from_scope_fresh:
    forall scope sig tys,
      scope_fresh scope sig ->
      Forall (st_scoped scope) tys ->
      types_fresh (signature_scope sig) tys.
  Proof.
    intros scope sig tys Hfresh Htys.
    induction Htys as [|ty tys Hty Htys IH]; constructor; auto.
    eapply type_fresh_from_scope_fresh; eauto.
  Qed.

  Lemma outputs_fresh_from_scope_fresh:
    forall scope sig outs,
      scope_fresh scope sig ->
      Forall (fun x => In x scope) outs ->
      outputs_fresh (signature_scope sig) outs.
  Proof.
    intros scope sig outs Hfresh Houts.
    induction Houts as [|x outs Hin Houts IH]; constructor; auto.
  Qed.

  Lemma call_subst_fresh_from_scope_fresh:
    forall scope sig inptyp ckty rstty outtyp,
      scope_fresh scope sig ->
      Forall (st_scoped scope) inptyp ->
      st_scoped scope ckty ->
      st_scoped scope rstty ->
      Forall (fun x => In x scope) outtyp ->
      call_subst_fresh sig inptyp ckty rstty outtyp.
  Proof.
    intros scope sig inptyp ckty rstty outtyp
           Hfresh Hinp Hclk Hrst Hout.
    repeat split.
    - eapply types_fresh_from_scope_fresh; eauto.
    - eapply type_fresh_from_scope_fresh; eauto.
    - eapply type_fresh_from_scope_fresh; eauto.
    - eapply outputs_fresh_from_scope_fresh; eauto.
  Qed.

  Lemma call_subst_fresh_reset_from_scope_fresh:
    forall scope sig inptyp ckty rst_inst outtyp,
      scope_fresh scope sig ->
      signature_scope_sec sig ->
      Forall (st_scoped scope) inptyp ->
      st_scoped scope ckty ->
      (exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
      Forall (fun x => In x scope) outtyp ->
      call_subst_fresh sig inptyp ckty (rst_inst :: nil) outtyp.
  Proof.
    intros scope sig inptyp ckty rst_inst outtyp
           Hfresh Hsigsec Hinp Hclk Hrstinst Hout.
    repeat split.
    - eapply types_fresh_from_scope_fresh; eauto.
    - eapply type_fresh_from_scope_fresh; eauto.
    - unfold type_fresh. rewrite Forall_forall.
      intros x Hin Hsig.
      simpl in Hin. destruct Hin as [Heq|[]]. subst x.
      eapply sec_reset_not_in_signature_scope; eauto.
    - eapply outputs_fresh_from_scope_fresh; eauto.
  Qed.

  Definition secglobal_scoped (G: secglobal) : Prop :=
    forall f sig,
      find_signature f G = Some sig ->
      signature_scoped sig.

  Lemma secglobal_scoped_nil:
    secglobal_scoped [].
  Proof.
    intros f sig Hfind.
    simpl in Hfind. discriminate.
  Qed.

  Lemma secglobal_scoped_cons:
    forall sig G,
      signature_scoped sig ->
      secglobal_scoped G ->
      secglobal_scoped (sig :: G).
  Proof.
    intros sig G Hsig Hglob f sig' Hfind.
    simpl in Hfind.
    destruct (ident_eqb sig.(s_name) f) eqn:Hname.
    - inversion Hfind; subst sig'. exact Hsig.
    - eapply Hglob; eauto.
  Qed.

  Definition subst_rhs_ident (x v: ident) (rhs: ST) : ST :=
    match rhs with
    | [y] => if ident_eqb x y then [v] else [y]
    | _ => rhs
    end.

  Lemma subst_ident_in_constraint_rhs:
    forall c x ty c' st st',
      subst_inp_ident_in_constraint c x ty st = OK (c', st') ->
      snd c' = snd c.
  Proof.
    intros [lhs rhs] x ty c' st st' Hsub.
    unfold subst_inp_ident_in_constraint in Hsub.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    destruct (ident_eqb x r) eqn:Hxr; try discriminate.
    unfold ret in Hsub. inversion Hsub; subst c' st'. reflexivity.
  Qed.

  Lemma subst_ident_in_constraints_rhs:
    forall cs x ty cs' st st',
      subst_ident_in_constraints cs x ty st = OK (cs', st') ->
      map snd cs' = map snd cs.
  Proof.
    induction cs as [|c cs IH]; intros x ty cs' st st' Hsub.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. reflexivity.
    - simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'.
      simpl. rewrite (subst_ident_in_constraint_rhs _ _ _ _ _ _ Hhd).
      rewrite (IH _ _ _ _ _ Htl). reflexivity.
  Qed.

  Lemma subst_ident_constraint_rhs:
    forall c x v c' st st',
      subst_ident_constraint c x v st = OK (c', st') ->
      snd c' = subst_rhs_ident x v (snd c).
  Proof.
    intros [lhs rhs] x v c' st st' Hsub.
    unfold subst_ident_constraint in Hsub.
    destruct (ident_eqb x v) eqn:Hxv; try discriminate.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    destruct (ident_eqb x r) eqn:Hxr.
    - unfold ret in Hsub. inversion Hsub; subst c' st'. simpl. rewrite Hxr. reflexivity.
    - unfold ret in Hsub. inversion Hsub; subst c' st'. simpl. rewrite Hxr. reflexivity.
  Qed.

  Lemma subst_ident_constraints_rhs:
    forall cs x v cs' st st',
      subst_ident_constraints cs x v st = OK (cs', st') ->
      map snd cs' = map (subst_rhs_ident x v) (map snd cs).
  Proof.
    induction cs as [|c cs IH]; intros x v cs' st st' Hsub.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. reflexivity.
    - simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'.
      simpl. rewrite (subst_ident_constraint_rhs _ _ _ _ _ _ Hhd).
      rewrite (IH _ _ _ _ _ Htl). reflexivity.
  Qed.

  Lemma nodup_singleton_map:
    forall (xs : list ident),
      NoDup xs ->
      NoDup (map (fun ty => [ty]) xs).
  Proof.
    intros xs Hnd.
    induction Hnd as [|x xs Hnin Hnd IH]; simpl.
    - constructor.
    - constructor.
      + intro Hin.
        apply in_map_iff in Hin as (y & Hy & Hiny).
        inversion Hy; subst. contradiction.
      + exact IH.
  Qed.

  Lemma reorder_constraints_shape:
    forall src outs cns st st',
      NoDup outs ->
      mmap
        (fun x : ident =>
           do st0 <- option_to_sec (findST src x);
           ret (st0, [x])) outs st = OK (cns, st') ->
      map snd cns = map (fun ty => [ty]) outs
      /\ wf_constraints cns.
  Proof.
    intros src outs.
    induction outs as [|x outs IH]; intros cns st st' Hnd Hmap.
    - simpl in Hmap.
      unfold ret in Hmap. inversion Hmap; subst.
      split; [reflexivity|].
      unfold wf_constraints. split; constructor.
    - simpl in Hmap.
      apply NoDup_cons' in Hnd as [Hnin Hndtail].
      eapply sec_bind_inv in Hmap as (cx & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (cxs & st2 & Htl & Hret).
      unfold option_to_sec in Hhd.
      destruct (findST src x) as [lhs|] eqn:Hfind; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst cx st1.
      unfold ret in Hret. inversion Hret; subst cns st'.
      specialize (IH _ _ _ Hndtail Htl) as [Hsnd Hwf].
      split.
      + simpl. rewrite Hsnd. reflexivity.
      + unfold wf_constraints in *.
        destruct Hwf as [Hndwf Hfortail].
        split.
        * simpl. constructor.
          -- intro Hin.
             assert (Hin' : In [x] (map (fun ty => [ty]) outs)).
             { rewrite <- Hsnd. exact Hin. }
             apply in_map_iff in Hin' as (y & Hy & Hiny).
             inversion Hy; subst.
             apply Hnin. exact Hiny.
          -- exact Hndwf.
        * constructor; [simpl; reflexivity|exact Hfortail].
  Qed.

  (** This fixes the shape of instantiated call constraints.  Source and target call proofs use it to reason about one visible constraint block per caller output. *)
  Theorem generate_constraints_shape:
    forall sig inp clk rst out cns st st',
      NoDup out ->
      generate_constraints sig inp clk rst out st = OK (cns, st') ->
      wf_constraints cns
      /\ map snd cns = map (fun ty => [ty]) out.
  Proof.
    intros sig inp clk rst out cns st st' Hnd Hgen.
    unfold generate_constraints in Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & Hinpsub & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & Hclksub & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & Hrstsub & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & Houtsub & Hreorder).
    destruct (reorder_constraints_shape c4 out cns st4 st' Hnd Hreorder) as [Hsnd Hwf].
    split; [exact Hwf|exact Hsnd].
  Qed.

  Lemma lookup_output_constraint_scoped:
    forall scope src x c st st',
      constraints_scoped scope src ->
      In x scope ->
      (do st0 <- option_to_sec (findST src x);
       ret (st0, [x])) st = OK (c, st') ->
      constraint_scoped scope c.
  Proof.
    intros scope src x c st st' Hsc Hinx Hlookup.
    simpl in Hlookup.
    unfold option_to_sec in Hlookup.
    destruct (findST src x) as [lhs|] eqn:Hfind; try discriminate.
    unfold ret in Hlookup. inversion Hlookup; subst c st'.
    intros y Hin.
    unfold constraint_scope in Hin. simpl in Hin.
    apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - apply find_correct in Hfind.
      unfold constraints_scoped in Hsc.
      rewrite Forall_forall in Hsc.
      eapply constraint_scoped_lhs with (rhs := [x]).
      + eapply Hsc. exact Hfind.
      + exact Hin.
    - simpl in Hin. destruct Hin as [Heq|[]]. subst y. exact Hinx.
  Qed.

  Lemma reorder_constraints_scoped:
    forall scope src outs cns st st',
      constraints_scoped scope src ->
      Forall (fun x => In x scope) outs ->
      mmap
        (fun x : ident =>
           do st0 <- option_to_sec (findST src x);
           ret (st0, [x])) outs st = OK (cns, st') ->
      constraints_scoped scope cns.
  Proof.
    induction outs as [|x outs IH]; intros cns st st' Hsc Houts Hmap.
    - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. constructor.
    - inversion Houts as [|x' outs' Hx Houts']; subst x' outs'.
      simpl in Hmap.
      eapply sec_bind_inv in Hmap as (cx & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (cxs & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      constructor.
      + eapply lookup_output_constraint_scoped; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma subst_ident_in_type_scoped_app:
    forall pre post x ty v,
      st_scoped (pre ++ x :: post) ty ->
      st_scoped (pre ++ post) v ->
      st_scoped (pre ++ post) (subst_ident_in_type ty x v).
  Proof.
    intros pre post x ty v Hty Hv.
    unfold subst_ident_in_type.
    destruct (my_set_mem x ty) eqn:Hmem.
    - eapply st_scoped_merge.
      + eapply st_scoped_remove_app; eauto.
      + eapply st_scoped_remove_app.
        eapply st_scoped_weaken with (scope1 := pre ++ post).
        * intros y Hin.
          apply in_app_iff in Hin.
          apply in_app_iff.
          destruct Hin as [Hin|Hin].
          -- now left.
          -- right. simpl. now right.
        * exact Hv.
    - apply st_scoped_drop_absent_app with (x := x).
      + intro Hin.
        apply my_set_mem_correct in Hin.
        rewrite Hin in Hmem. discriminate.
      + exact Hty.
  Qed.

  Lemma subst_inp_ident_in_constraint_scoped:
    forall scope c x v c' st st',
      constraint_scoped (x :: scope) c ->
      st_scoped scope v ->
      subst_inp_ident_in_constraint c x v st = OK (c', st') ->
      constraint_scoped scope c'.
  Proof.
    intros scope [lhs rhs] x v c' st st' Hsc Hv Hsub.
    unfold subst_inp_ident_in_constraint in Hsub.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    destruct (ident_eqb x r) eqn:Hxr; try discriminate.
    unfold ret in Hsub. inversion Hsub; subst c' st'; clear Hsub.
    intros y Hin.
    unfold constraint_scope in Hin. rewrite in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - assert (Hlhs : st_scoped ([] ++ x :: scope) lhs).
      { intros z Hz.
        eapply constraint_scoped_lhs with (rhs := [r]).
        - exact Hsc.
        - exact Hz. }
      pose proof (subst_ident_in_type_scoped_app [] scope x lhs v Hlhs Hv) as Hlhs'.
      exact (Hlhs' y Hin).
    - simpl in Hin. destruct Hin as [Heq|[]]. subst y.
      apply ident_eqb_neq in Hxr.
      pose proof (constraint_scoped_rhs (x :: scope) lhs [r] r Hsc (or_introl eq_refl)) as Hrsc.
      simpl in Hrsc. destruct Hrsc as [Heq|Hin']; [contradiction|exact Hin'].
  Qed.

  Lemma subst_ident_constraint_scoped:
    forall scope c x v c' st st',
      constraint_scoped (x :: scope) c ->
      In v scope ->
      subst_ident_constraint c x v st = OK (c', st') ->
      constraint_scoped scope c'.
  Proof.
    intros scope [lhs rhs] x v c' st st' Hsc Hv Hsub.
    unfold subst_ident_constraint in Hsub.
    destruct (ident_eqb x v) eqn:Hxv; try discriminate.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    destruct (ident_eqb x r) eqn:Hxr.
    - unfold ret in Hsub. inversion Hsub; subst c' st'; clear Hsub.
      intros y Hin.
      unfold constraint_scope in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + assert (Hlhs : st_scoped ([] ++ x :: scope) lhs).
        { intros z Hz.
          eapply constraint_scoped_lhs with (rhs := [r]).
          - exact Hsc.
          - exact Hz. }
        pose proof (subst_ident_in_type_scoped_app [] scope x lhs [v] Hlhs
                     (st_scoped_singleton scope v Hv)) as Hlhs'.
        exact (Hlhs' y Hin).
      + simpl in Hin. destruct Hin as [Heq|[]]. subst y. exact Hv.
    - unfold ret in Hsub. inversion Hsub; subst c' st'; clear Hsub.
      intros y Hin.
      unfold constraint_scope in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + assert (Hlhs : st_scoped ([] ++ x :: scope) lhs).
        { intros z Hz.
          eapply constraint_scoped_lhs with (rhs := [r]).
          - exact Hsc.
          - exact Hz. }
        pose proof (subst_ident_in_type_scoped_app [] scope x lhs [v] Hlhs
                     (st_scoped_singleton scope v Hv)) as Hlhs'.
        exact (Hlhs' y Hin).
      + simpl in Hin. destruct Hin as [Heq|[]]. subst y.
        apply ident_eqb_neq in Hxr.
        pose proof (constraint_scoped_rhs (x :: scope) lhs [r] r Hsc (or_introl eq_refl)) as Hrsc.
        simpl in Hrsc. destruct Hrsc as [Heq|Hin']; [contradiction|exact Hin'].
  Qed.

  Lemma subst_ident_constraints_scoped:
    forall scope cs x v cs' st st',
      constraints_scoped (x :: scope) cs ->
      In v scope ->
      subst_ident_constraints cs x v st = OK (cs', st') ->
      constraints_scoped scope cs'.
  Proof.
    induction cs as [|c cs IH]; intros x v cs' st st' Hsc Hv Hsub.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
    - inversion Hsc as [|c0 cs0 Hc Hcs]; subst c0 cs0.
      simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'; clear Hret.
      constructor.
      + eapply subst_ident_constraint_scoped; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma subst_ident_in_constraints_scoped:
    forall scope cs x v cs' st st',
      constraints_scoped (x :: scope) cs ->
      st_scoped scope v ->
      subst_ident_in_constraints cs x v st = OK (cs', st') ->
      constraints_scoped scope cs'.
  Proof.
    induction cs as [|c cs IH]; intros x v cs' st st' Hsc Hv Hsub.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
    - inversion Hsc as [|c0 cs0 Hc Hcs]; subst c0 cs0.
      simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'; clear Hret.
      constructor.
      + eapply subst_inp_ident_in_constraint_scoped; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma subst_constraints_inp_map_scoped:
    forall xs vs rest scope cs cs' st st',
      constraints_scoped (xs ++ rest ++ scope) cs ->
      Forall (st_scoped scope) vs ->
      subst_constraints_inp_map cs xs vs st = OK (cs', st') ->
      constraints_scoped (rest ++ scope) cs'.
  Proof.
    induction xs as [|x xs IH]; intros vs rest scope cs cs' st st' Hsc Hvs Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hsc.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      inversion Hvs as [|v0 vs0 Hv Hvs']; subst v0 vs0.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      eapply IH with (st := st1); eauto.
      eapply subst_ident_in_constraints_scoped; eauto.
      eapply st_scoped_weaken; eauto.
      intros y Hin. repeat rewrite in_app_iff. now right; right.
  Qed.

  Lemma subst_constraints_out_map_scoped:
    forall xs vs scope cs cs' st st',
      constraints_scoped (xs ++ scope) cs ->
      Forall (fun x => In x scope) vs ->
      subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      constraints_scoped scope cs'.
  Proof.
    induction xs as [|x xs IH]; intros vs scope cs cs' st st' Hsc Hvs Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      simpl in Hsc.
      unfold ret in Hsub. inversion Hsub; subst. exact Hsc.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      inversion Hvs as [|v0 vs0 Hv Hvs']; subst v0 vs0.
      destruct (findST cs v) as [stx|] eqn:Hfind; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      assert (Hv' : In v (xs ++ scope)).
      { apply in_or_app. right. exact Hv. }
      pose proof (subst_ident_constraints_scoped (xs ++ scope) cs x v cs1 st st1 Hsc Hv' Hhd) as Hsc1.
      eapply IH with (vs := vs) (cs := cs1) (st := st1) in Htl; eauto.
  Qed.

  (** This shows that instantiated call constraints stay inside the caller-visible scope.  Both signature generators reuse it when they build call constraints from stored signatures. *)
  Theorem generate_constraints_scoped:
    forall sig scope inp clk rst out cns st st',
      signature_scoped sig ->
      Forall (st_scoped scope) inp ->
      st_scoped scope clk ->
      st_scoped scope rst ->
      Forall (fun x => In x scope) out ->
      generate_constraints sig inp clk rst out st = OK (cns, st') ->
      constraints_scoped scope cns.
  Proof.
    intros sig scope inp clk rst out cns st st'
           Hscoped Hinp Hclk Hrst Hout Hgen.
    unfold generate_constraints in Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & Hinpsub & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & Hclksub & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & Hrstsub & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & Houtsub & Hreorder).
    assert (Hsig0 :
              constraints_scoped
                (s_in sig ++ (s_out sig ++ [s_clk sig; s_reset sig]) ++ scope)
                sig.(s_constraints)).
    { eapply constraints_scoped_weaken; [|exact Hscoped].
      intros x Hin.
      unfold signature_scope in Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      - apply in_or_app. now left.
      - apply in_or_app. right. apply in_or_app. now left. }
    assert (Hc1 :
              constraints_scoped
                ((s_out sig ++ [s_clk sig; s_reset sig]) ++ scope) c1).
    { eapply (subst_constraints_inp_map_scoped
                (s_in sig) inp (s_out sig ++ [s_clk sig; s_reset sig])
                scope (s_constraints sig) c1 st st1).
      - exact Hsig0.
      - exact Hinp.
      - exact Hinpsub. }
    assert (Hc1' :
              constraints_scoped
                (s_clk sig :: (s_out sig ++ [s_reset sig] ++ scope)) c1).
    { eapply constraints_scoped_weaken; [|exact Hc1].
      intros x Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      - rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + simpl. right. apply in_or_app. now left.
        + simpl in Hin. destruct Hin as [Heq|[Heq|[]]]; subst.
          * now left.
          * right. apply in_or_app. right. simpl. now left.
      - right. apply in_or_app. right. simpl. now right. }
    assert (Hclk' : st_scoped (s_out sig ++ [s_reset sig] ++ scope) clk).
    { eapply st_scoped_weaken; [|exact Hclk].
      intros x Hin.
      apply in_or_app. right.
      apply in_or_app. right.
      exact Hin. }
    assert (Hc2 :
              constraints_scoped
                (s_out sig ++ [s_reset sig] ++ scope) c2).
    { eapply (subst_ident_in_constraints_scoped
                (s_out sig ++ [s_reset sig] ++ scope)
                c1 (s_clk sig) clk c2 st1 st2).
      - exact Hc1'.
      - exact Hclk'.
      - exact Hclksub. }
    assert (Hc2' :
              constraints_scoped
                (s_reset sig :: (s_out sig ++ scope)) c2).
    { eapply constraints_scoped_weaken; [|exact Hc2].
      intros x Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      - simpl. right. apply in_or_app. now left.
      - simpl in Hin. destruct Hin as [Heq|Hin].
        + subst. now left.
        + right. apply in_or_app. now right. }
    assert (Hrst' : st_scoped (s_out sig ++ scope) rst).
    { eapply st_scoped_weaken; [|exact Hrst].
      intros x Hin.
      apply in_or_app. now right. }
    assert (Hc3 : constraints_scoped (s_out sig ++ scope) c3).
    { eapply (subst_ident_in_constraints_scoped
                (s_out sig ++ scope)
                c2 (s_reset sig) rst c3 st2 st3).
      - exact Hc2'.
      - exact Hrst'.
      - exact Hrstsub. }
    assert (Hc4 : constraints_scoped scope c4).
    { eapply (subst_constraints_out_map_scoped
                (s_out sig) out scope c3 c4 st3 st4).
      - exact Hc3.
      - exact Hout.
      - exact Houtsub. }
    eapply reorder_constraints_scoped; eauto.
  Qed.

End Type_Substitutions.

End SIGNATURE.

Module Signature
    (Ids : IDS)
    (SC : SECMONAD Ids) <: SIGNATURE Ids SC.
Include SIGNATURE Ids SC.
End Signature.

Module Type SIGNATURE_PROOFS (Import Ids: IDS)
  (Import SC: SECMONAD Ids)
  (Import SIG: SIGNATURE Ids SC)
  (Import Lat: Lattice)
  (Import SecTypes: SECTYPES Lat).
  Import MergeFacts.
  Local Notation sig_scope := signature_scope.
  Lemma st_remove_correct: forall dlt ty x, hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty.
  Proof.
    induction ty; intros.
    - now unfold SymTypes.st_remove.
    - unfold  SymTypes.st_remove. simpl.
      destruct (ident_eq_dec x a) eqn:Hxa.
      + subst x. assert (hm_ext dlt (remove ident_eq_dec a ty) ⊑ hm_ext dlt ty) as H1. { auto. }
      assert (hm_ext dlt ty ⊑ join (dlt a) (hm_ext dlt ty)) as H2. { apply join_bound2. }
      now eapply order_trans.
      + simpl. auto.
  Qed.

  Lemma subst_ident_in_type_correct1:
      forall dlt x st ty, hm_ext dlt st ⊑ dlt x
      -> hm_ext dlt (SIG.subst_ident_in_type ty x st) ⊑ hm_ext dlt ty.
  Proof.
    induction ty; intros; unfold SIG.subst_ident_in_type; unfold SymTypes.my_set_mem; auto.
    destruct (ident_eqb a x) eqn:Hax.
    - unfold SymTypes.st_remove.
      apply ident_eqb_eq in Hax; subst. simpl.
      destruct (ident_eq_dec x x) eqn:Hxx; auto.
      * fold SymTypes.st_remove. apply (hm_ext_distributive dlt (SymTypes.st_remove x st) (SymTypes.st_remove x ty) (join (dlt x) (hm_ext dlt ty))).
        + assert (hm_ext dlt (SymTypes.st_remove x st) ⊑ hm_ext dlt st) as Hez. {  apply st_remove_correct. }
       apply Lat.order_trans with (y:=hm_ext dlt st); auto.
       apply Lat.order_trans with (y:=dlt x); auto.
        + assert (hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty) as Hez. {  apply st_remove_correct. }
      apply Lat.order_trans with (y:=hm_ext dlt ty); auto.
      * congruence.
    - fold SymTypes.my_set_mem. apply ident_eqb_neq in Hax. simpl. destruct (ident_eq_dec x a) eqn:Hxa; try congruence.
    unfold SIG.subst_ident_in_type in IHty. apply IHty in H as Hih.
    destruct (SymTypes.my_set_mem x ty) eqn:Hmem; auto.
    apply (hm_ext_distributive dlt (SymTypes.st_remove x st) (a :: SymTypes.st_remove x ty)
             (join (dlt a) (hm_ext dlt ty))).
    + assert (hm_ext dlt (SymTypes.st_remove x st) ⊑ hm_ext dlt st) as Hrmst. { apply st_remove_correct. }
      apply order_trans with (y:=hm_ext dlt st); [exact Hrmst|].
      apply order_trans with (y:=dlt x); [exact H|].
      apply SymTypes.my_set_mem_correct in Hmem.
      apply order_trans with (y:=hm_ext dlt ty).
      * apply hm_ext_list_in1. exact Hmem.
      * apply join_bound2.
    + simpl. apply join_least_upper_bound.
      * apply join_bound1.
      * assert (hm_ext dlt (SymTypes.st_remove x ty) ⊑ hm_ext dlt ty) as Hrmty. { apply st_remove_correct. }
        apply order_trans with (y:=hm_ext dlt ty); [exact Hrmty|].
        apply join_bound2.
  Qed.

    Lemma sig_scope_in_raw_scope:
      forall sig locals x,
        In x (sig_scope sig) ->
        In x (sig.(s_in) ++ sig.(s_out) ++ locals ++ sig.(s_clk) :: sig.(s_reset) :: nil).
    Proof.
      intros sig locals x Hin.
      unfold sig_scope in Hin.
      repeat rewrite in_app_iff in *.
      destruct Hin as [Hin|[Hin|Hin]].
      - now left.
      - right. left. exact Hin.
      - destruct Hin as [Hinclk|[Hinrst|[]]].
        + right. right. right. left. exact Hinclk.
        + right. right. right. right. left. exact Hinrst.
    Qed.

  Lemma subst_inp_ident_in_constraint_correct:
    forall (c: constraint) (x: ident) (v: ST) c' st st', subst_inp_ident_in_constraint c x v st = OK (c' , st') ->
    forall dlt, constraintSatisfiable dlt c ->
    hm_ext dlt v ⊑ dlt x ->constraintSatisfiable dlt c'.
  Proof.
    intros. unfold subst_inp_ident_in_constraint in H. destruct c eqn:Hc. destruct s0 eqn:Hs0; try (now inversion H). destruct s1 eqn:Hs1; try (now inversion H). destruct (ident_eqb x i) eqn:Hxi; try (now inversion H). unfold ret in H; inversion H.
    unfold constraintSatisfiable in *. unfold satisfiable in *.
    apply order_trans with (y:=hm_ext dlt s). eapply subst_ident_in_type_correct1; eauto. easy.
  Qed.

  Ltac monadInv :=
    simpl in *;
    unfold error in *;
    match goal with
    | H: ident_eqb _ _ = true |- _ => rewrite ident_eqb_eq in H; subst
    | H: OK _ = OK _ |- _ =>
      inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
      discriminate
    | H: ret _ _ = _ |- _ =>
      unfold ret in H
    | H: bind ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.

  Ltac matchMonadInv :=
    match goal with
    | H: (match ?x with
          | OK _ => _
          | Error _ => _ end) |- _ =>
      let H1 := fresh "Hmat" in
      destruct x eqn:H1; monadInv
    end.

  Lemma subst_ident_in_constraints_correct:
    forall (cs: list constraint) (x: ident) (v: ST) cs' st st', subst_ident_in_constraints cs x v st = OK (cs' , st') ->
      forall dlt, listSatisfiable dlt cs -> hm_ext dlt v ⊑ dlt x -> listSatisfiable dlt cs'.
  Proof.
    induction cs; intros.
    - simpl in H. unfold ret in H. inversion H; now subst.
    - repeat monadInv. unfold listSatisfiable in *. inversion H0. apply Forall_cons.
      + apply (subst_inp_ident_in_constraint_correct a x v x0 st x1); auto.
      + now apply (IHcs x v x2 x1 st').
  Qed.

  Definition inp_replace_cond dlt (x: ident) (v: ST): Prop := hm_ext dlt v ⊑ dlt x.

  Lemma  subst_constraints_inp_map_correct:
    forall  (xs: list ident) (cs: list constraint) (vs: list ST) cs' st st',
      subst_constraints_inp_map cs xs vs st = OK (cs',st') ->
        forall dlt, listSatisfiable dlt cs -> Forall2 (inp_replace_cond dlt) xs vs
        -> listSatisfiable dlt cs'.
  Proof.
    induction xs as [| x xs]; intros.
    - simpl in H; destruct vs eqn:E; inversion H; now subst.
    - simpl in H. destruct vs eqn:E; inversion H.
      *  monadInv. inversion  H1. unfold inp_replace_cond in H5.
        apply (IHxs x0 l cs' x1 st'); auto.
        eapply subst_ident_in_constraints_correct; eauto.
  Qed.

  Lemma hm_ext_upd_type_subst_le_l:
    forall dlt x st ty,
      ~ In x st ->
      hm_ext (upd_type dlt x st) ty ⊑ hm_ext dlt (SIG.subst_ident_in_type ty x st).
  Proof.
    intros dlt x st ty Hfresh.
    apply hm_ext_bound_from_members.
    intros y Hy.
    destruct (ident_eq_dec y x) as [Heq|Hneq].
    - subst y.
      unfold upd_type. rewrite ident_eqb_refl.
      unfold SIG.subst_ident_in_type.
      destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
      + assert (Hmemst : SymTypes.my_set_mem x st = false).
        {
          destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
          exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
        }
        assert (Heqst : SymTypes.st_remove x st = st).
        { apply SymTypes.sym_st_remove_notin. exact Hmemst. }
        rewrite Heqst.
        change (hm_ext dlt st ⊑ hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st)).
        eapply order_trans.
        * apply hm_ext_concat_r.
        * apply order_refl, eq_refl.
      + exfalso.
        apply (proj2 (SymTypes.my_set_mem_correct x ty)) in Hy.
        rewrite Hmem in Hy. discriminate.
    - rewrite upd_type_outside by (intro Heq; apply Hneq; symmetry; exact Heq).
      unfold SIG.subst_ident_in_type.
      destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
      + assert (Hmemst : SymTypes.my_set_mem x st = false).
        {
          destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
          exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
        }
        assert (Heqst : SymTypes.st_remove x st = st).
        { apply SymTypes.sym_st_remove_notin. exact Hmemst. }
        rewrite Heqst.
        change (dlt y ⊑ hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st)).
        assert (Hinrm : In y (SymTypes.st_remove x ty)).
        { eapply SymTypes.sym_st_remove_preserves_other_in; eauto. }
        eapply order_trans.
        * eapply hm_ext_list_in1. exact Hinrm.
        * apply hm_ext_concat_l.
      + eapply hm_ext_list_in1. exact Hy.
  Qed.

  Lemma hm_ext_upd_type_subst_le_r:
    forall dlt x st ty,
      ~ In x st ->
      hm_ext dlt (SIG.subst_ident_in_type ty x st) ⊑ hm_ext (upd_type dlt x st) ty.
  Proof.
    intros dlt x st ty Hfresh.
    unfold SIG.subst_ident_in_type.
    destruct (SymTypes.my_set_mem x ty) eqn:Hmem; simpl.
    - assert (Hmemst : SymTypes.my_set_mem x st = false).
      {
        destruct (SymTypes.my_set_mem x st) eqn:Hmemst; auto.
        exfalso. apply Hfresh. apply SymTypes.my_set_mem_correct. exact Hmemst.
      }
      assert (Heqst : SymTypes.st_remove x st = st).
      { apply SymTypes.sym_st_remove_notin. exact Hmemst. }
      rewrite Heqst.
      change (hm_ext dlt ((SymTypes.st_remove x ty) ⊔ st) ⊑ hm_ext (upd_type dlt x st) ty).
      apply hm_ext_bound_from_members.
      intros y Hin.
      destruct (in_merge_inv _ _ _ Hin) as [Hinrm|Hinst].
      + destruct (st_remove_in_inv _ _ _ Hinrm) as [Hinty Hneq].
        assert (Hxny : x <> y).
        { intro Heq. apply Hneq. symmetry. exact Heq. }
        assert (Heqout : eq (dlt y) (upd_type dlt x st y)).
        {
          apply (proj2 (eq_no_red _ _)).
          symmetry. apply upd_type_outside. exact Hxny.
        }
        eapply order_trans.
        * apply order_refl.
          exact Heqout.
        * eapply hm_ext_list_in1. exact Hinty.
      + assert (Hinty : In x ty).
        { apply SymTypes.my_set_mem_correct. exact Hmem. }
        assert (Heqx : eq (hm_ext dlt st) (upd_type dlt x st x)).
        {
          apply (proj2 (eq_no_red _ _)).
          unfold upd_type. rewrite ident_eqb_refl. reflexivity.
        }
        eapply order_trans.
        * eapply hm_ext_list_in1. exact Hinst.
        * eapply order_trans.
          -- apply order_refl. exact Heqx.
          -- eapply hm_ext_list_in1. exact Hinty.
    - apply hm_ext_bound_from_members.
      intros y Hin.
      assert (Hneq : y <> x).
      { intro Heq. subst y.
        apply SymTypes.my_set_mem_correct in Hin.
        rewrite Hin in Hmem. discriminate.
      }
      assert (Hxny : x <> y).
      { intro Heq. apply Hneq. symmetry. exact Heq. }
      assert (Heqout : eq (dlt y) (upd_type dlt x st y)).
      {
        apply (proj2 (eq_no_red _ _)).
        symmetry. apply upd_type_outside. exact Hxny.
      }
      eapply order_trans.
      + apply order_refl.
        exact Heqout.
      + eapply hm_ext_list_in1. exact Hin.
  Qed.

  Lemma hm_ext_upd_type_subst:
    forall dlt x st ty,
      ~ In x st ->
      hm_ext (upd_type dlt x st) ty = hm_ext dlt (SIG.subst_ident_in_type ty x st).
  Proof.
    intros dlt x st ty Hfresh.
    apply eq_no_red.
    apply order_antisym.
    - apply hm_ext_upd_type_subst_le_l; exact Hfresh.
    - apply hm_ext_upd_type_subst_le_r; exact Hfresh.
  Qed.

  Lemma hm_ext_upd_ident_subst:
    forall dlt x v ty,
      x <> v ->
      hm_ext (upd_ident dlt x v) ty = hm_ext dlt (SIG.subst_ident_in_type ty x [v]).
  Proof.
    intros dlt x v ty Hneq.
    rewrite (hm_ext_agree_on_st (upd_ident dlt x v) (upd_type dlt x [v]) ty).
    - apply hm_ext_upd_type_subst.
      simpl. intros [Heq|[]]. subst v. contradiction.
    - intros y Hin.
      apply upd_ident_eq_upd_type_singleton; exact Hneq.
  Qed.

  Definition lat_valuation
    (dlt: ident -> Lat.t) (sig: signature)
    (inp: list ST) (clk rst: ST) (out: list ident)
    : ident -> Lat.t :=
    upd_types_rev
      (upd_type
         (upd_type
            (upd_idents_rev dlt sig.(s_out) out)
            sig.(s_reset) rst)
         sig.(s_clk) clk)
      sig.(s_in) inp.

  Lemma lat_valuation_agree_on_scope:
    forall dlt sig scope inp clk rst out,
      scope_fresh scope sig ->
      agree_on scope dlt (lat_valuation dlt sig inp clk rst out).
  Proof.
    intros dlt sig scope inp clk rst out Hfresh.
    unfold lat_valuation.
    eapply agree_on_trans.
    - eapply upd_idents_rev_agree_on.
      eapply scope_fresh_notin_outputs; eauto.
    - eapply agree_on_trans.
      + eapply upd_type_agree_on.
        eapply scope_fresh_notin_reset; eauto.
      + eapply agree_on_trans.
        * eapply upd_type_agree_on.
          eapply scope_fresh_notin_clk; eauto.
        * eapply upd_types_rev_agree_on.
          eapply scope_fresh_notin_inputs; eauto.
  Qed.

  Lemma overlay_scope_agree_on_sig_scope:
    forall scope sig dlt_scope dlt_base,
      scope_fresh scope sig ->
      agree_on (sig_scope sig) dlt_base (overlay_scope scope dlt_scope dlt_base).
  Proof.
    intros scope sig dlt_scope dlt_base Hfresh x Hin.
    symmetry.
    apply overlay_scope_agree_outside.
    intro Hscope.
    exact (Hfresh x Hscope Hin).
  Qed.

  Lemma subst_constraints_inp_map_length:
    forall cs xs vs cs' st st',
      SIG.subst_constraints_inp_map cs xs vs st = OK (cs', st') ->
      List.length xs = List.length vs.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      reflexivity.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      simpl. f_equal. eapply IH. exact Htl.
  Qed.

  Lemma subst_constraints_out_map_length:
    forall cs xs vs cs' st st',
      SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      List.length xs = List.length vs.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub.
    - destruct vs as [|v vs]; cbn [SIG.subst_constraints_out_map] in Hsub; try discriminate.
      reflexivity.
    - destruct vs as [|v vs]; cbn [SIG.subst_constraints_out_map] in Hsub; try discriminate.
      revert Hsub.
      destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; cbn [SIG.subst_constraints_out_map] in Hsub; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      simpl. f_equal. eapply IH. exact Htl.
  Qed.

  Lemma upd_idents_rev_eq_on_pairs:
    forall dlt xs vs scope,
      incl xs scope ->
      outputs_fresh scope vs ->
      NoDup xs ->
      List.length xs = List.length vs ->
      Forall2 (fun x v => upd_idents_rev dlt xs vs x = dlt v) xs vs.
  Proof.
    induction xs as [|x xs IH]; intros vs scope Hincl Hfresh Hnd Hlen.
    - destruct vs as [|v vs]; simpl in Hlen; try discriminate.
      constructor.
    - destruct vs as [|v vs]; simpl in Hlen; try discriminate.
      inversion Hfresh as [|v' vs' Hv Hfresh']; subst v' vs'.
      inversion Hnd as [|x' xs' Hxnotin Hnd']; subst x' xs'.
      inversion Hlen; subst.
      constructor.
      + simpl. unfold upd_ident. rewrite ident_eqb_refl.
        rewrite upd_idents_rev_outside.
        * reflexivity.
        * intro Hin. apply Hv. apply Hincl. now right.
      + specialize (IH vs scope
                       (fun y Hy => Hincl y (or_intror Hy))
                       Hfresh' Hnd' H0) as Htail.
        eapply SecTypes.Forall2_upd_ident_outside_base; eauto.
  Qed.

  Lemma upd_types_rev_eq_on_pairs:
    forall dlt xs tys scope,
      incl xs scope ->
      types_fresh scope tys ->
      NoDup xs ->
      List.length xs = List.length tys ->
      Forall2 (fun x ty => upd_types_rev dlt xs tys x = hm_ext dlt ty) xs tys.
  Proof.
    induction xs as [|x xs IH]; intros tys scope Hincl Hfresh Hnd Hlen.
    - destruct tys as [|ty tys]; simpl in Hlen; try discriminate.
      constructor.
    - destruct tys as [|ty tys]; simpl in Hlen; try discriminate.
      inversion Hfresh as [|ty' tys' Hty Hfresh']; subst ty' tys'.
      inversion Hnd as [|x' xs' Hxnotin Hnd']; subst x' xs'.
      inversion Hlen; subst.
      constructor.
      + simpl. unfold upd_type. rewrite ident_eqb_refl.
        assert (Hfreshxs : Forall (fun z => ~ In z ty) xs).
        {
          rewrite Forall_forall.
          intros z Hz Hzin.
          unfold type_fresh in Hty.
          rewrite Forall_forall in Hty.
          specialize (Hty _ Hzin).
          apply Hty. apply Hincl. now right.
        }
        pose proof (upd_types_rev_agree_on dlt ty xs tys Hfreshxs) as Hagree.
        apply hm_ext_agree_on_st in Hagree.
        symmetry. exact Hagree.
      + specialize (IH tys scope
                       (fun y Hy => Hincl y (or_intror Hy))
                       Hfresh' Hnd' H0) as Htail.
        eapply SecTypes.Forall2_upd_type_outside_base; eauto.
  Qed.

  Lemma sig_scope_nodup_decomp:
    forall sig,
      NoDup (sig_scope sig) ->
      NoDup sig.(s_in)
      /\ NoDup sig.(s_out)
      /\ Forall (fun x => ~ In x (sig.(s_out) ++ [sig.(s_clk); sig.(s_reset)])) sig.(s_in)
      /\ Forall (fun x => ~ In x [sig.(s_clk); sig.(s_reset)]) sig.(s_out)
      /\ sig.(s_clk) <> sig.(s_reset).
  Proof.
    intros sig Hnd.
    unfold sig_scope in Hnd.
    apply NoDup_app'_iff in Hnd as [Hnin [Hnoutclk Hfreshin]].
    apply NoDup_app'_iff in Hnoutclk as [Hnout [Hclkreset Hfreshout]].
    apply NoDup_cons_iff in Hclkreset as [Hclkneq Hrstnil].
    simpl in Hclkneq.
    split; [exact Hnin|].
    split; [exact Hnout|].
    split; [exact Hfreshin|].
    split.
    - exact Hfreshout.
    - intro Heq. apply Hclkneq. now left.
  Qed.

  Lemma type_fresh_notin_sig_scope:
    forall sig ty x,
      type_fresh (sig_scope sig) ty ->
      In x (sig_scope sig) ->
      ~ In x ty.
  Proof.
    intros sig ty x Hfresh Hin.
    unfold type_fresh in Hfresh.
    rewrite Forall_forall in Hfresh.
    intro Hxty.
    eapply Hfresh; eauto.
  Qed.

  Lemma hm_ext_after_output_updates_on_fresh_type:
    forall dlt sig out ty,
      type_fresh (sig_scope sig) ty ->
      hm_ext (upd_idents_rev dlt sig.(s_out) out) ty = hm_ext dlt ty.
  Proof.
    intros dlt sig out ty Hfresh.
    assert (Hagree :
              agree_on ty dlt (upd_idents_rev dlt sig.(s_out) out)).
    {
      eapply upd_idents_rev_agree_on.
      rewrite Forall_forall.
      intros x Hinout.
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. left. exact Hinout.
    }
    symmetry. eapply hm_ext_agree_on_st; eauto.
  Qed.

  Lemma hm_ext_after_output_reset_updates_on_fresh_type:
    forall dlt sig out rst ty,
      type_fresh (sig_scope sig) ty ->
      hm_ext
        (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst) ty =
      hm_ext dlt ty.
  Proof.
    intros dlt sig out rst ty Hfresh.
    assert (Hrstfresh : ~ In sig.(s_reset) ty).
    {
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. right.
      simpl. right. left. reflexivity.
    }
    rewrite <- (hm_ext_after_output_updates_on_fresh_type dlt sig out ty Hfresh).
    symmetry.
    eapply hm_ext_agree_on_st.
    intros x Hin.
    unfold upd_type.
    destruct (ident_eqb x sig.(s_reset)) eqn:Heq; auto.
    apply ident_eqb_eq in Heq. subst x. contradiction.
  Qed.

  Lemma hm_ext_after_output_reset_clk_updates_on_fresh_type:
    forall dlt sig out clk rst ty,
      type_fresh (sig_scope sig) ty ->
      hm_ext
        (upd_type
           (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst)
           sig.(s_clk) clk) ty =
      hm_ext dlt ty.
  Proof.
    intros dlt sig out clk rst ty Hfresh.
    assert (Hclkfresh : ~ In sig.(s_clk) ty).
    {
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. right.
      simpl. left. reflexivity.
    }
    rewrite <- (hm_ext_after_output_reset_updates_on_fresh_type dlt sig out rst ty Hfresh).
    symmetry.
    eapply hm_ext_agree_on_st.
    intros x Hin.
    unfold upd_type.
    destruct (ident_eqb x sig.(s_clk)) eqn:Heq; auto.
    apply ident_eqb_eq in Heq. subst x. contradiction.
  Qed.

  Lemma lat_valuation_outside_sig_scope:
    forall dlt sig inp clk rst out y,
      ~ In y (sig_scope sig) ->
      lat_valuation dlt sig inp clk rst out y = dlt y.
  Proof.
    intros dlt sig inp clk rst out y Hnout.
    unfold lat_valuation.
    rewrite upd_types_rev_outside.
    2:{
      intro Hin.
      apply Hnout.
      unfold sig_scope. apply in_or_app. left. exact Hin.
    }
    rewrite upd_type_outside.
    2:{
      intro Heq. subst y.
      apply Hnout.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. right.
      simpl. left. reflexivity.
    }
    rewrite upd_type_outside.
    2:{
      intro Heq. subst y.
      apply Hnout.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. right.
      simpl. right. left. reflexivity.
    }
    rewrite upd_idents_rev_outside.
    - reflexivity.
    - intro Hin.
      apply Hnout.
      unfold sig_scope. apply in_or_app. right. apply in_or_app. left. exact Hin.
  Qed.

  Lemma hm_ext_lat_valuation_on_fresh_type:
    forall dlt sig inp clk rst out ty,
      type_fresh (sig_scope sig) ty ->
      hm_ext (lat_valuation dlt sig inp clk rst out) ty = hm_ext dlt ty.
  Proof.
    intros dlt sig inp clk rst out ty Hfresh.
    unfold lat_valuation.
    assert (Hagree :
              agree_on ty
                (upd_type
                   (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst)
                   sig.(s_clk) clk)
                (upd_types_rev
                   (upd_type
                      (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst)
                      sig.(s_clk) clk)
                   sig.(s_in) inp)).
    {
      eapply upd_types_rev_agree_on.
      rewrite Forall_forall.
      intros x Hin.
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. left. exact Hin.
    }
    rewrite <- (hm_ext_agree_on_st _ _ _ Hagree).
    eapply hm_ext_after_output_reset_clk_updates_on_fresh_type; eauto.
  Qed.

  Lemma lat_valuation_outputs_eq:
    forall dlt sig inp clk rst out,
      call_subst_fresh sig inp clk rst out ->
      NoDup (sig_scope sig) ->
      List.length sig.(s_out) = List.length out ->
      Forall2
        (fun x v =>
           lat_valuation dlt sig inp clk rst out v =
           lat_valuation dlt sig inp clk rst out x)
        sig.(s_out) out.
  Proof.
    intros dlt sig inp clk rst out Hfresh Hndscope Hlen.
    destruct sig as [sname sin sout sreset sclk sconstraints].
    simpl in *.
    destruct Hfresh as [_ [_ [_ Houtfresh]]].
    set (sigfull :=
           {| s_name := sname;
              s_in := sin;
              s_out := sout;
              s_reset := sreset;
              s_clk := sclk;
              s_constraints := sconstraints |}).
    set (ival := lat_valuation dlt sigfull inp clk rst out).
    destruct (sig_scope_nodup_decomp sigfull Hndscope)
      as [_ [Hnout [Hfreshin [Houtnotin _]]]].
    assert (Htail :
              Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v)
                      sout out).
    {
      eapply upd_idents_rev_eq_on_pairs.
      - intros x Hin. unfold sig_scope. apply in_or_app. right.
        apply in_or_app. left. exact Hin.
      - exact Houtfresh.
      - exact Hnout.
      - exact Hlen.
    }
    assert (Houtsafe :
              forall x,
                In x sout ->
                ~ In x sin /\ ~ In x [sclk; sreset]).
    {
      intros x Hinout.
      split.
      - intro Hinin.
        rewrite Forall_forall in Hfreshin.
        specialize (Hfreshin _ Hinin).
        apply Hfreshin.
        apply in_app_iff. left. exact Hinout.
      - rewrite Forall_forall in Houtnotin.
        exact (Houtnotin _ Hinout).
    }
    assert (Hformal :
              forall x,
                In x sout ->
                ival x = upd_idents_rev dlt sout out x).
    {
      intros x Hinout.
      unfold ival, lat_valuation.
      rewrite upd_types_rev_outside.
      2:{
        destruct (Houtsafe x Hinout) as [Hxin _].
        exact Hxin.
      }
      rewrite upd_type_outside.
      2:{
        destruct (Houtsafe x Hinout) as [_ Hxclkreset].
        intro Heq. apply Hxclkreset. now left; symmetry.
      }
      rewrite upd_type_outside.
      2:{
        destruct (Houtsafe x Hinout) as [_ Hxclkreset].
        intro Heq. apply Hxclkreset. now right; left; symmetry.
      }
      reflexivity.
    }
    assert (Hactual :
              forall v,
                In v out ->
                ival v = dlt v).
    {
      intros v Hinout.
      unfold ival.
      eapply lat_valuation_outside_sig_scope.
      unfold outputs_fresh in Houtfresh.
      rewrite Forall_forall in Houtfresh.
      exact (Houtfresh _ Hinout).
    }
    assert (HformalF : Forall (fun x => ival x = upd_idents_rev dlt sout out x) sout).
    {
      rewrite Forall_forall.
      intros x Hin.
      exact (Hformal x Hin).
    }
    assert (HactualF : Forall (fun v => ival v = dlt v) out).
    {
      rewrite Forall_forall.
      intros v Hin.
      exact (Hactual v Hin).
    }
    assert
      (Hconv :
         forall xs ys,
           Forall2 (fun x v => upd_idents_rev dlt sout out x = dlt v) xs ys ->
           Forall (fun x => ival x = upd_idents_rev dlt sout out x) xs ->
           Forall (fun v => ival v = dlt v) ys ->
           Forall2 (fun x v => ival v = ival x) xs ys).
    {
      intros xs ys Hrel.
      induction Hrel; intros Hf1 Hf2.
      - constructor.
      - inversion Hf1 as [|x' xs' Hx Hxs]; subst.
        inversion Hf2 as [|y' ys' Hy Hys]; subst.
        constructor.
        + transitivity (dlt y).
          * exact Hy.
          * rewrite Hx. symmetry. exact H.
        + eapply IHHrel; eauto.
    }
    eapply Hconv; eauto.
  Qed.

  Lemma lat_valuation_inputs_eq:
    forall dlt sig inp clk rst out,
      call_subst_fresh sig inp clk rst out ->
      NoDup (sig_scope sig) ->
      List.length sig.(s_in) = List.length inp ->
      Forall2
        (fun x ty =>
           lat_valuation dlt sig inp clk rst out x = hm_ext dlt ty)
        sig.(s_in) inp.
  Proof.
    intros dlt [sname sin sout sreset sclk sconstraints] inp clk rst out
           Hfresh Hndscope Hlen.
    simpl in *.
    destruct Hfresh as [Hinfresh [_ [_ _]]].
    assert (Hndin : NoDup sin).
    {
      destruct (sig_scope_nodup_decomp
                  {| s_name := sname;
                     s_in := sin;
                     s_out := sout;
                     s_reset := sreset;
                     s_clk := sclk;
                     s_constraints := sconstraints |} Hndscope)
        as [Hndin [_ [_ [_ _]]]].
      exact Hndin.
    }
    revert inp Hinfresh Hlen.
    induction sin as [|x xs IH]; intros inp Hinfresh Hlen.
    - destruct inp as [|ty tys]; simpl in Hlen; try discriminate.
      constructor.
    - destruct inp as [|ty tys]; simpl in Hlen; try discriminate.
      inversion Hlen; subst.
      inversion Hinfresh as [|ty' tys' Hty Hfresh']; subst ty' tys'.
      constructor.
      + assert (Heq :
                  upd_types_rev
                    (upd_type
                       (upd_type (upd_idents_rev dlt sout out) sreset rst)
                         sclk clk) (x :: xs) (ty :: tys) x =
                  hm_ext
                    (upd_type
                       (upd_type (upd_idents_rev dlt sout out) sreset rst)
                         sclk clk) ty).
        {
          assert (Hpair :
                    Forall2
                      (fun x0 ty0 =>
                         upd_types_rev
                           (upd_type
                              (upd_type (upd_idents_rev dlt sout out) sreset rst)
                                sclk clk) (x :: xs) (ty :: tys) x0 =
                         hm_ext
                           (upd_type
                              (upd_type (upd_idents_rev dlt sout out) sreset rst)
                                sclk clk) ty0)
                      (x :: xs) (ty :: tys)).
          {
            eapply upd_types_rev_eq_on_pairs
              with (scope := x :: xs ++ sout ++ [sclk; sreset]).
            - intros y Hin.
              simpl.
              destruct Hin as [Heq|Hin].
              + now left.
              + right. apply in_or_app. left. exact Hin.
            - constructor; [exact Hty|exact Hfresh'].
            - exact Hndin.
            - exact Hlen.
          }
          inversion Hpair as [|x0 ty0 xs0 tys0 Hhd Htl]; subst.
          exact Hhd.
        }
        set (base :=
               upd_type
                 (upd_type (upd_idents_rev dlt sout out) sreset rst)
                 sclk clk).
        unfold lat_valuation.
        simpl.
        unfold upd_type.
        rewrite ident_eqb_refl.
        assert (Hfreshxs : Forall (fun z => ~ In z ty) xs).
        {
          rewrite Forall_forall.
          intros z Hz Hzin.
          unfold type_fresh in Hty.
          rewrite Forall_forall in Hty.
          eapply Hty; eauto.
          unfold sig_scope.
          apply in_or_app. left.
          now right.
        }
        pose proof (upd_types_rev_agree_on base ty xs tys Hfreshxs) as Hagree.
        transitivity (hm_ext base ty).
        { symmetry. eapply hm_ext_agree_on_st. exact Hagree. }
        {
          exact
            (hm_ext_after_output_reset_clk_updates_on_fresh_type
               dlt
               {| s_name := sname;
                  s_in := x :: xs;
                  s_out := sout;
                  s_reset := sreset;
                  s_clk := sclk;
                  s_constraints := sconstraints |}
               out clk rst ty Hty).
        }
      + set (base :=
               upd_type
                 (upd_type (upd_idents_rev dlt sout out) sreset rst)
                 sclk clk).
        assert (Hndscope_tail :
                  NoDup
                    (sig_scope
                       {| s_name := sname;
                          s_in := xs;
                          s_out := sout;
                          s_reset := sreset;
                          s_clk := sclk;
                          s_constraints := sconstraints |})).
        {
          unfold sig_scope in Hndscope |- *.
          simpl in Hndscope |- *.
          now inversion Hndscope.
        }
        assert (Hfresh_tail :
                  types_fresh
                    (sig_scope
                       {| s_name := sname;
                          s_in := xs;
                          s_out := sout;
                          s_reset := sreset;
                          s_clk := sclk;
                          s_constraints := sconstraints |}) tys).
        {
          unfold types_fresh in Hfresh' |- *.
          rewrite Forall_forall in Hfresh' |- *.
          intros ty0 Hty0.
          specialize (Hfresh' _ Hty0).
          unfold type_fresh in Hfresh' |- *.
          rewrite Forall_forall in Hfresh' |- *.
          intros y Hy Hin.
          apply (Hfresh' y Hy).
          unfold sig_scope in Hin |- *.
          simpl in Hin |- *.
          now right.
        }
        specialize
          (IH Hndscope_tail
              ltac:(inversion Hndin; assumption)
              tys Hfresh_tail H0) as Htail.
        cbn [lat_valuation] in Htail |- *.
        change
          (Forall2
             (fun x0 ty0 =>
                upd_type (upd_types_rev base xs tys) x ty x0 =
                hm_ext dlt ty0) xs tys).
        eapply SecTypes.Forall2_upd_type_outside_base.
        * inversion Hndin; assumption.
        * exact Htail.
  Qed.

  Lemma lat_valuation_clk_eq:
    forall dlt sig inp clk rst out,
      call_subst_fresh sig inp clk rst out ->
      NoDup (sig_scope sig) ->
      lat_valuation dlt sig inp clk rst out sig.(s_clk) = hm_ext dlt clk.
  Proof.
    intros dlt sig inp clk rst out Hfresh Hndscope.
    destruct Hfresh as [_ [Hclkfresh [_ _]]].
    destruct (sig_scope_nodup_decomp sig Hndscope)
      as [_ [_ [Hfreshin [_ _]]]].
    assert (Hclknotin : ~ In sig.(s_clk) sig.(s_in)).
    {
      intro Hin.
      rewrite Forall_forall in Hfreshin.
      specialize (Hfreshin _ Hin).
      apply Hfreshin.
      apply in_or_app. right.
      simpl. now left.
    }
    unfold lat_valuation.
    rewrite upd_types_rev_outside by exact Hclknotin.
    unfold upd_type.
    rewrite ident_eqb_refl.
    eapply hm_ext_after_output_reset_updates_on_fresh_type; eauto.
  Qed.

  Lemma lat_valuation_reset_eq:
    forall dlt sig inp clk rst out,
      call_subst_fresh sig inp clk rst out ->
      NoDup (sig_scope sig) ->
      lat_valuation dlt sig inp clk rst out sig.(s_reset) = hm_ext dlt rst.
  Proof.
    intros dlt sig inp clk rst out Hfresh Hndscope.
    destruct Hfresh as [_ [_ [Hrstfresh _]]].
    destruct (sig_scope_nodup_decomp sig Hndscope)
      as [_ [_ [Hfreshin [_ Hclkneqrst]]]].
    assert (Hrstnotin : ~ In sig.(s_reset) sig.(s_in)).
    {
      intro Hin.
      rewrite Forall_forall in Hfreshin.
      specialize (Hfreshin _ Hin).
      apply Hfreshin.
      apply in_or_app. right.
      simpl. now right; left.
    }
    unfold lat_valuation.
    rewrite upd_types_rev_outside by exact Hrstnotin.
    rewrite upd_type_outside.
    2:{
      intro Heq.
      apply Hclkneqrst.
      exact Heq.
    }
    unfold upd_type.
    rewrite ident_eqb_refl.
    eapply hm_ext_after_output_updates_on_fresh_type; eauto.
  Qed.

  Lemma call_subst_fresh_inputs_notin_pairs:
    forall sig inp clk rst out,
      call_subst_fresh sig inp clk rst out ->
      List.length sig.(s_in) = List.length inp ->
      Forall2 (fun x ty => ~ In x ty) sig.(s_in) inp.
  Proof.
    intros [sname sin sout sreset sclk sconstraints] inp clk rst out Hfresh Hlen.
    simpl in *.
    destruct Hfresh as [Hinfresh [_ [_ _]]].
    revert inp Hinfresh Hlen.
    induction sin as [|x xs IH]; intros inp Hinfresh Hlen.
    - destruct inp as [|ty tys]; simpl in Hlen; try discriminate.
      constructor.
    - destruct inp as [|ty tys]; simpl in Hlen; try discriminate.
      inversion Hlen; subst.
      inversion Hinfresh as [|ty' tys' Hty Hfresh']; subst ty' tys'.
      assert (Hfresh_tail :
                types_fresh
                  (sig_scope
                     {| s_name := sname;
                        s_in := xs;
                        s_out := sout;
                        s_reset := sreset;
                        s_clk := sclk;
                        s_constraints := sconstraints |}) tys).
      {
        unfold types_fresh in Hfresh' |- *.
        rewrite Forall_forall in Hfresh' |- *.
        intros ty0 Hty0.
        specialize (Hfresh' _ Hty0).
        unfold type_fresh in Hfresh' |- *.
        rewrite Forall_forall in Hfresh' |- *.
        intros y Hy Hin.
        apply (Hfresh' y Hy).
        unfold sig_scope in Hin |- *.
        simpl in Hin |- *.
        now right.
      }
      constructor.
      + intros Hin.
        unfold type_fresh in Hty.
        rewrite Forall_forall in Hty.
        eapply Hty; eauto.
        unfold sig_scope. simpl. now left.
      + eapply IH; eauto.
  Qed.

  Lemma lat_valuation_same_sig_agree_on_sig_scope:
    forall sig scope dlt dlt' inp clk rst out,
      NoDup (sig_scope sig) ->
      scope_fresh scope sig ->
      call_subst_scoped scope inp clk rst out ->
      call_subst_fresh sig inp clk rst out ->
      agree_on scope dlt dlt' ->
      List.length sig.(s_in) = List.length inp ->
      List.length sig.(s_out) = List.length out ->
      agree_on (sig_scope sig)
               (lat_valuation dlt sig inp clk rst out)
               (lat_valuation dlt' sig inp clk rst out).
  Proof.
    intros sig scope dlt dlt' inp clk rst out
           Hndscope Hscopefresh Hscoped Hfresh HagreeScope HlenIn HlenOut
           x Hin.
    destruct Hscoped as [[HinpScope [HckScope HoutScope]] HrstScope].
    assert (HinstScope :
              agree_on scope dlt (lat_valuation dlt sig inp clk rst out)).
    { eapply lat_valuation_agree_on_scope; eauto. }
    assert (HinstScope' :
              agree_on scope dlt' (lat_valuation dlt' sig inp clk rst out)).
    { eapply lat_valuation_agree_on_scope; eauto. }
    unfold sig_scope in Hin.
    apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - pose proof (lat_valuation_inputs_eq dlt sig inp clk rst out Hfresh Hndscope HlenIn)
        as HsrcInputs.
      pose proof (lat_valuation_inputs_eq dlt' sig inp clk rst out Hfresh Hndscope HlenIn)
        as HtgtInputs.
      destruct (SecTypes.In_nth_error_ex _ _ _ Hin) as [n Hnth].
      destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HsrcInputs Hnth)
        as [ty [Hnthty HsrcEq]].
      destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HtgtInputs Hnth)
        as [ty' [Hnthty' HtgtEq]].
      rewrite Hnthty in Hnthty'. inversion Hnthty'. subst ty'. clear Hnthty'.
      rewrite HsrcEq, HtgtEq.
      eapply hm_ext_agree_on_scoped_type; eauto.
      rewrite Forall_forall in HinpScope.
      eapply HinpScope.
      eapply SecTypes.nth_error_In_local. exact Hnthty.
    - apply in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + pose proof (lat_valuation_outputs_eq dlt sig inp clk rst out Hfresh Hndscope HlenOut)
          as HsrcOuts.
        pose proof (lat_valuation_outputs_eq dlt' sig inp clk rst out Hfresh Hndscope HlenOut)
          as HtgtOuts.
        destruct (SecTypes.In_nth_error_ex _ _ _ Hin) as [n Hnth].
        destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HsrcOuts Hnth)
          as [v [Hnthv HsrcEq]].
        destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HtgtOuts Hnth)
          as [v' [Hnthv' HtgtEq]].
        rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. clear Hnthv'.
        rewrite <- HsrcEq, <- HtgtEq.
        transitivity (dlt v).
        * symmetry. eapply HinstScope.
          rewrite Forall_forall in HoutScope.
          eapply HoutScope.
          eapply SecTypes.nth_error_In_local. exact Hnthv.
        * transitivity (dlt' v).
          -- eapply HagreeScope.
             rewrite Forall_forall in HoutScope.
             eapply HoutScope.
             eapply SecTypes.nth_error_In_local. exact Hnthv.
          -- eapply HinstScope'.
             rewrite Forall_forall in HoutScope.
             eapply HoutScope.
             eapply SecTypes.nth_error_In_local. exact Hnthv.
      + simpl in Hin.
        destruct Hin as [Heq|[Heq|[]]]; subst x.
        * rewrite (lat_valuation_clk_eq dlt sig inp clk rst out Hfresh Hndscope).
          rewrite (lat_valuation_clk_eq dlt' sig inp clk rst out Hfresh Hndscope).
          eapply hm_ext_agree_on_scoped_type; eauto.
        * rewrite (lat_valuation_reset_eq dlt sig inp clk rst out Hfresh Hndscope).
          rewrite (lat_valuation_reset_eq dlt' sig inp clk rst out Hfresh Hndscope).
          eapply hm_ext_agree_on_scoped_type; eauto.
  Qed.

  Lemma lat_valuation_fields_agree_eq:
    forall dlt nsig ssig inp clk rst out x,
      signature_fields_agree nsig ssig ->
      lat_valuation dlt nsig inp clk rst out x =
      lat_valuation dlt ssig inp clk rst out x.
  Proof.
    intros dlt nsig ssig inp clk rst out x Hfields.
    destruct Hfields as [HinEq [HoutEq [HrstEq HclkEq]]].
    unfold lat_valuation.
    simpl.
    now rewrite HinEq, HoutEq, HrstEq, HclkEq.
  Qed.

  Lemma lat_valuation_fields_agree_on_sig_scope:
    forall nsig ssig scope dlt dlt' inp clk rst out,
      signature_fields_agree nsig ssig ->
      NoDup (sig_scope nsig) ->
      scope_fresh scope nsig ->
      call_subst_scoped scope inp clk rst out ->
      call_subst_fresh nsig inp clk rst out ->
      agree_on scope dlt dlt' ->
      List.length nsig.(s_in) = List.length inp ->
      List.length nsig.(s_out) = List.length out ->
      agree_on (sig_scope ssig)
               (lat_valuation dlt nsig inp clk rst out)
               (lat_valuation dlt' ssig inp clk rst out).
  Proof.
    intros nsig ssig scope dlt dlt' inp clk rst out
           Hfields Hndscope Hscopefresh Hscoped Hfresh Hagree HlenIn HlenOut.
    pose proof
      (lat_valuation_same_sig_agree_on_sig_scope
         nsig scope dlt dlt' inp clk rst out
         Hndscope Hscopefresh Hscoped Hfresh Hagree HlenIn HlenOut)
      as Hsame.
    unfold agree_on in Hsame |- *.
    intros x Hin.
    rewrite <- (signature_fields_agree_scope_eq _ _ Hfields) in Hin.
    rewrite <- (lat_valuation_fields_agree_eq dlt' nsig ssig inp clk rst out x Hfields).
    exact (Hsame x Hin).
  Qed.

  Lemma lat_valuation_fields_agree_on_sig_scope_reset:
    forall nsig ssig scope dlt dlt' inp clk srcrst rst_inst out,
      signature_fields_agree nsig ssig ->
      NoDup (sig_scope nsig) ->
      scope_fresh scope nsig ->
      call_actuals_scoped scope inp clk out ->
      st_scoped scope srcrst ->
      call_subst_fresh nsig inp clk srcrst out ->
      call_subst_fresh ssig inp clk (rst_inst :: nil) out ->
      ~ In rst_inst scope ->
      agree_on scope dlt dlt' ->
      dlt' rst_inst = hm_ext dlt srcrst ->
      List.length nsig.(s_in) = List.length inp ->
      List.length nsig.(s_out) = List.length out ->
      agree_on (sig_scope ssig)
               (lat_valuation dlt nsig inp clk srcrst out)
               (lat_valuation dlt' ssig inp clk (rst_inst :: nil) out).
  Proof.
    intros nsig ssig scope dlt dlt' inp clk srcrst rst_inst out
           Hfields Hndscope Hscopefresh Hscoped Hsrcrstscope
           Hfresh_nsig Hfresh_ssig Hrstinst_outside HagreeScope Hrstinst_eq
           HlenIn HlenOut x Hin.
    destruct Hscoped as [HinpScope [HckScope HoutScope]].
    destruct Hfields as [HinEq [HoutEq [HrstEq HclkEq]]].
    assert (HinstScope :
              agree_on scope dlt (lat_valuation dlt nsig inp clk srcrst out)).
    { eapply lat_valuation_agree_on_scope; eauto. }
    assert (Hndscope_ssig : NoDup (sig_scope ssig)).
    { rewrite <- (signature_fields_agree_scope_eq _ _ (conj HinEq (conj HoutEq (conj HrstEq HclkEq)))). exact Hndscope. }
    unfold sig_scope in Hin.
    apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - pose proof (lat_valuation_inputs_eq dlt nsig inp clk srcrst out Hfresh_nsig Hndscope HlenIn)
        as HsrcInputs.
      pose proof (lat_valuation_inputs_eq dlt' ssig inp clk (rst_inst :: nil) out Hfresh_ssig Hndscope_ssig)
        as HtgtInputs0.
      assert (HlenIn_ssig : List.length ssig.(s_in) = List.length inp).
      { now rewrite <- HinEq. }
      specialize (HtgtInputs0 HlenIn_ssig) as HtgtInputs.
      assert (Hinsrc : In x nsig.(s_in)).
      { now rewrite HinEq. }
      destruct (SecTypes.In_nth_error_ex _ _ _ Hinsrc) as [n Hnth].
      destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HsrcInputs Hnth)
        as [ty [Hnthty HsrcEq]].
      rewrite HinEq in Hnth.
      destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HtgtInputs Hnth)
        as [ty' [Hnthty' HtgtEq]].
      rewrite Hnthty in Hnthty'. inversion Hnthty'. subst ty'. clear Hnthty'.
      rewrite HsrcEq, HtgtEq.
      eapply hm_ext_agree_on_scoped_type; eauto.
      rewrite Forall_forall in HinpScope.
      eapply HinpScope.
      eapply SecTypes.nth_error_In_local. exact Hnthty.
    - apply in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      + pose proof (lat_valuation_outputs_eq dlt nsig inp clk srcrst out Hfresh_nsig Hndscope HlenOut)
          as HsrcOuts.
        pose proof (lat_valuation_outputs_eq dlt' ssig inp clk (rst_inst :: nil) out Hfresh_ssig Hndscope_ssig)
          as HtgtOuts0.
        assert (HlenOut_ssig : List.length ssig.(s_out) = List.length out).
        { now rewrite <- HoutEq. }
        specialize (HtgtOuts0 HlenOut_ssig) as HtgtOuts.
        assert (Houtsrc : In x nsig.(s_out)).
        { now rewrite HoutEq. }
        destruct (SecTypes.In_nth_error_ex _ _ _ Houtsrc) as [n Hnth].
        destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HsrcOuts Hnth)
          as [v [Hnthv HsrcEq]].
        rewrite HoutEq in Hnth.
        destruct (SecTypes.Forall2_nth_error_inv _ _ _ _ _ _ _ HtgtOuts Hnth)
          as [v' [Hnthv' HtgtEq]].
        rewrite Hnthv in Hnthv'. inversion Hnthv'. subst v'. clear Hnthv'.
        rewrite <- HsrcEq, <- HtgtEq.
        transitivity (dlt v).
        * symmetry. eapply HinstScope.
          rewrite Forall_forall in HoutScope.
          eapply HoutScope.
          eapply SecTypes.nth_error_In_local. exact Hnthv.
        * transitivity (dlt' v).
          -- eapply HagreeScope.
             rewrite Forall_forall in HoutScope.
             eapply HoutScope.
             eapply SecTypes.nth_error_In_local. exact Hnthv.
          -- symmetry.
             eapply lat_valuation_outside_sig_scope.
             destruct Hfresh_ssig as [_ [_ [_ Houtfresh_ssig]]].
             unfold outputs_fresh in Houtfresh_ssig.
             rewrite Forall_forall in Houtfresh_ssig.
             eapply Houtfresh_ssig.
             eapply SecTypes.nth_error_In_local. exact Hnthv.
      + simpl in Hin.
        destruct Hin as [Heq|[Heq|[]]]; subst x.
        * replace (lat_valuation dlt nsig inp clk srcrst out (s_clk ssig))
            with (lat_valuation dlt nsig inp clk srcrst out (s_clk nsig))
            by now rewrite HclkEq.
          rewrite (lat_valuation_clk_eq dlt nsig inp clk srcrst out Hfresh_nsig Hndscope).
          rewrite (lat_valuation_clk_eq dlt' ssig inp clk (rst_inst :: nil) out Hfresh_ssig Hndscope_ssig).
          eapply hm_ext_agree_on_scoped_type; eauto.
        * replace (lat_valuation dlt nsig inp clk srcrst out (s_reset ssig))
            with (lat_valuation dlt nsig inp clk srcrst out (s_reset nsig))
            by now rewrite HrstEq.
          rewrite (lat_valuation_reset_eq dlt nsig inp clk srcrst out Hfresh_nsig Hndscope).
          rewrite (lat_valuation_reset_eq dlt' ssig inp clk (rst_inst :: nil) out Hfresh_ssig Hndscope_ssig).
          simpl.
          rewrite <- join_bottom_eq1.
          symmetry.
          exact Hrstinst_eq.
  Qed.

  Lemma subst_ident_constraint_complete_out:
    forall c x v c' st st',
      SIG.subst_ident_constraint c x v st = OK (c', st') ->
      forall dlt,
        constraintSatisfiable dlt c' ->
        constraintSatisfiable (upd_ident dlt x v) c.
  Proof.
    intros [lhs rhs] x v c' st st' Hsub dlt Hsat.
    unfold SIG.subst_ident_constraint in Hsub.
    destruct (ident_eqb x v) eqn:Hxv; try discriminate.
    apply ident_eqb_neq in Hxv as Hneq.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    unfold ret in Hsub.
    destruct (ident_eqb x r) eqn:Hxr; inversion Hsub; subst c' st'; clear Hsub.
    - apply ident_eqb_eq in Hxr. subst r.
      unfold constraintSatisfiable, satisfiable in *.
      simpl in Hsat.
      rewrite <- hm_ext_upd_ident_subst in Hsat by exact Hneq.
      simpl.
      unfold upd_ident.
      rewrite ident_eqb_refl.
      exact Hsat.
    - apply ident_eqb_neq in Hxr.
      unfold constraintSatisfiable, satisfiable in *.
      simpl in Hsat.
      rewrite <- hm_ext_upd_ident_subst in Hsat by exact Hneq.
      simpl.
      rewrite upd_ident_outside by exact Hxr.
      exact Hsat.
  Qed.

  Lemma subst_ident_constraints_complete_out:
    forall cs x v cs' st st',
      SIG.subst_ident_constraints cs x v st = OK (cs', st') ->
      forall dlt,
        listSatisfiable dlt cs' ->
        listSatisfiable (upd_ident dlt x v) cs.
  Proof.
    induction cs as [|c cs IH]; intros x v cs' st st' Hsub dlt Hsat.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
    - simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'.
      inversion Hsat; subst.
      constructor.
      + eapply subst_ident_constraint_complete_out; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma subst_inp_ident_in_constraint_complete:
    forall c x ty c' st st',
      ~ In x ty ->
      SIG.subst_inp_ident_in_constraint c x ty st = OK (c', st') ->
      forall dlt,
        constraintSatisfiable dlt c' ->
        constraintSatisfiable (upd_type dlt x ty) c.
  Proof.
    intros [lhs rhs] x ty c' st st' Hfresh Hsub dlt Hsat.
    unfold SIG.subst_inp_ident_in_constraint in Hsub.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    destruct (ident_eqb x r) eqn:Hxr; try discriminate.
    unfold ret in Hsub. inversion Hsub; subst c' st'; clear Hsub.
    apply ident_eqb_neq in Hxr.
    unfold constraintSatisfiable, satisfiable in *.
    simpl in Hsat.
    rewrite <- hm_ext_upd_type_subst in Hsat by exact Hfresh.
    simpl.
    rewrite upd_type_outside by exact Hxr.
    exact Hsat.
  Qed.

  Lemma subst_ident_in_constraints_complete:
    forall cs x ty cs' st st',
      ~ In x ty ->
      SIG.subst_ident_in_constraints cs x ty st = OK (cs', st') ->
      forall dlt,
        listSatisfiable dlt cs' ->
        listSatisfiable (upd_type dlt x ty) cs.
  Proof.
    induction cs as [|c cs IH]; intros x ty cs' st st' Hfresh Hsub dlt Hsat.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
    - simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'.
      inversion Hsat; subst.
      constructor.
      + eapply subst_inp_ident_in_constraint_complete; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma wf_constraints_rhs_unique:
    forall cs lhs1 lhs2 x,
      wf_constraints cs ->
      In (lhs1, [x]) cs ->
      In (lhs2, [x]) cs ->
      lhs1 = lhs2.
  Proof.
    induction cs as [|[lhs rhs] cs IH]; intros lhs1 lhs2 x Hwf Hin1 Hin2.
    - contradiction.
    - unfold wf_constraints in Hwf.
      destruct Hwf as [Hnd Hall].
      simpl in Hin1, Hin2.
      destruct Hin1 as [Hin1|Hin1]; destruct Hin2 as [Hin2|Hin2].
      + inversion Hin1; inversion Hin2; subst; congruence.
      + inversion Hin1; subst lhs rhs.
        inversion Hnd as [|? ? Hnotin _]; subst.
        exfalso. apply Hnotin.
        apply in_map_iff.
        exists (lhs2, [x]). split; [reflexivity|exact Hin2].
      + inversion Hin2; subst lhs rhs.
        inversion Hnd as [|? ? Hnotin _]; subst.
        exfalso. apply Hnotin.
        apply in_map_iff.
        exists (lhs1, [x]). split; [reflexivity|exact Hin1].
      + eapply IH.
        * eapply wf_constraints_no_nil.
          exact (conj Hnd Hall).
        * exact Hin1.
        * exact Hin2.
  Qed.

  Lemma findST_wf_exact:
    forall cs lhs x,
      wf_constraints cs ->
      In (lhs, [x]) cs ->
      findST cs x = Some lhs.
  Proof.
    intros cs lhs x Hwf Hin.
    assert (Hinrhs : In [x] (map snd cs)).
    { apply in_map_iff. exists (lhs, [x]). split; [reflexivity|exact Hin]. }
    destruct (findST_of_rhs_in _ _ Hinrhs) as [lhs' Hfind].
    pose proof (find_correct _ _ _ Hfind) as Hinfind.
    assert (lhs' = lhs).
    { eapply wf_constraints_rhs_unique; eauto. }
    subst lhs'. exact Hfind.
  Qed.

  Lemma reorder_constraints_member:
    forall src outs cns st st' x lhs,
      SC.mmap
        (fun y : ident =>
           SC.bind (option_to_sec (findST src y))
                   (fun st0 => SC.ret (st0, [y]))) outs st = OK (cns, st') ->
      In x outs ->
      findST src x = Some lhs ->
      In (lhs, [x]) cns.
  Proof.
    induction outs as [|y outs IH]; intros cns st st' x lhs Hmap Hin Hfind.
    - contradiction.
    - simpl in Hmap.
      eapply sec_bind_inv in Hmap as (cy & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (cys & st2 & Htl & Hret).
      unfold option_to_sec in Hhd.
      destruct (findST src y) as [lhsy|] eqn:Hfindy; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst cy st1.
      unfold ret in Hret. inversion Hret; subst cns st'.
      simpl in Hin.
      destruct Hin as [Heq|Hin].
      + subst x.
        rewrite Hfind in Hfindy. inversion Hfindy; subst lhsy.
        simpl. now left.
      + simpl. right. eapply IH; eauto.
  Qed.

  Lemma reorder_constraints_correct:
    forall src outs cns st st' dlt,
      SC.mmap
        (fun x : ident =>
           SC.bind (option_to_sec (findST src x))
                   (fun st0 => SC.ret (st0, [x]))) outs st = OK (cns, st') ->
      listSatisfiable dlt src ->
      listSatisfiable dlt cns.
  Proof.
    induction outs as [|x outs IH]; intros cns st st' dlt Hmap Hsat.
    - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. constructor.
    - simpl in Hmap.
      eapply sec_bind_inv in Hmap as (cx & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (cxs & st2 & Htl & Hret).
      unfold option_to_sec in Hhd.
      destruct (findST src x) as [lhs|] eqn:Hfind; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst cx st1.
      unfold ret in Hret. inversion Hret; subst cns st'.
      constructor.
      + unfold listSatisfiable in Hsat.
        rewrite Forall_forall in Hsat.
        specialize (Hsat _ (find_correct _ _ _ Hfind)).
        exact Hsat.
      + eapply IH; eauto.
  Qed.

  Lemma reorder_constraints_complete:
    forall src outs cns st st' dlt,
      wf_constraints src ->
      Permutation (map snd src) (map (fun x => [x]) outs) ->
      SC.mmap
        (fun x : ident =>
           SC.bind (option_to_sec (findST src x))
                   (fun st0 => SC.ret (st0, [x]))) outs st = OK (cns, st') ->
      listSatisfiable dlt cns ->
      listSatisfiable dlt src.
  Proof.
    intros src outs cns st st' dlt Hwf Hperm Hmap Hsat.
    unfold listSatisfiable.
    rewrite Forall_forall.
    intros [lhs rhs] Hin.
    destruct (wf_constraints_shape _ _ _ Hwf Hin) as [x Hrhs].
    subst rhs.
    assert (Hinrhs : In [x] (map snd src)).
    { apply in_map_iff. exists (lhs, [x]). split; [reflexivity|exact Hin]. }
    assert (Hinouts : In x outs).
    {
      assert (Hinouts' : In [x] (map (fun y => [y]) outs)).
      { eapply Permutation_in; [exact Hperm|exact Hinrhs]. }
      apply in_map_iff in Hinouts' as (y & Hy & Hiny).
      inversion Hy; subst y. exact Hiny.
    }
    assert (Hfind : findST src x = Some lhs).
    { eapply findST_wf_exact; eauto. }
    unfold listSatisfiable in Hsat.
    rewrite Forall_forall in Hsat.
    specialize (Hsat _ (reorder_constraints_member _ _ _ _ _ _ _ Hmap Hinouts Hfind)).
    exact Hsat.
  Qed.

  Lemma subst_ident_constraint_correct_out:
    forall c x v c' st st',
      SIG.subst_ident_constraint c x v st = OK (c', st') ->
      forall dlt,
        dlt v = dlt x ->
        constraintSatisfiable dlt c ->
        constraintSatisfiable dlt c'.
  Proof.
    intros [lhs rhs] x v c' st st' Hsub dlt Hveq Hsat.
    unfold SIG.subst_ident_constraint in Hsub.
    destruct (ident_eqb x v) eqn:Hxv; try discriminate.
    apply ident_eqb_neq in Hxv as Hneq.
    destruct rhs as [|r rhs']; try discriminate.
    destruct rhs' as [|r' rhs'']; try discriminate.
    unfold ret in Hsub.
    destruct (ident_eqb x r) eqn:Hxr; inversion Hsub; subst c' st'; clear Hsub.
    - apply ident_eqb_eq in Hxr. subst r.
      unfold constraintSatisfiable, satisfiable in *.
      simpl in Hsat |- *.
      rewrite <- (hm_ext_upd_ident_subst dlt x v lhs Hneq).
      rewrite (hm_ext_agree_on_st (upd_ident dlt x v) dlt lhs).
      + rewrite Hveq. exact Hsat.
      + intros y Hy.
        unfold upd_ident.
        destruct (ident_eqb y x) eqn:Hyx; auto.
        apply ident_eqb_eq in Hyx. subst y.
        exact Hveq.
    - unfold constraintSatisfiable, satisfiable in *.
      simpl in Hsat |- *.
      rewrite <- (hm_ext_upd_ident_subst dlt x v lhs Hneq).
      rewrite (hm_ext_agree_on_st (upd_ident dlt x v) dlt lhs).
      + exact Hsat.
      + intros y Hy.
        unfold upd_ident.
        destruct (ident_eqb y x) eqn:Hyx; auto.
        apply ident_eqb_eq in Hyx. subst y.
        exact Hveq.
  Qed.

  Lemma subst_ident_constraints_correct_out:
    forall cs x v cs' st st',
      SIG.subst_ident_constraints cs x v st = OK (cs', st') ->
      forall dlt,
        dlt v = dlt x ->
        listSatisfiable dlt cs ->
        listSatisfiable dlt cs'.
  Proof.
    induction cs as [|c cs IH]; intros x v cs' st st' Hsub dlt Hveq Hsat.
    - simpl in Hsub. unfold ret in Hsub. inversion Hsub; subst. constructor.
    - simpl in Hsub.
      eapply sec_bind_inv in Hsub as (c1 & st1 & Hhd & Hsub).
      eapply sec_bind_inv in Hsub as (cs1 & st2 & Htl & Hret).
      unfold ret in Hret. inversion Hret; subst cs' st'.
      inversion Hsat; subst.
      constructor.
      + eapply subst_ident_constraint_correct_out; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma subst_constraints_out_map_correct:
    forall cs xs vs cs' st st',
      SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      forall dlt,
        listSatisfiable dlt cs ->
        Forall2 (fun x v => dlt v = dlt x) xs vs ->
        listSatisfiable dlt cs'.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub dlt Hsat Hrel.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      inversion Hrel as [|x' v' xs' vs' Heq Hrel']; subst x' v' xs' vs'.
      simpl in Hsub.
      revert Hsub.
      destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; simpl in Hsub.
      + discriminate.
      + eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
        eapply IH with (cs := cs1) (dlt := dlt) in Htl; eauto.
        eapply subst_ident_constraints_correct_out; eauto.
  Qed.

  (** This is the main correctness theorem for signature instantiation.  It shows that substituting caller inputs, clock, reset, and outputs into a stored signature produces constraints whose satisfiability matches the intended caller-side interpretation.  The translation bridge and the noninterference proofs use this theorem instead of unfolding instantiation by hand. *)
  Theorem generate_constraints_correct_inst:
    forall sig inp clk rst out cns st st' dlt,
      NoDup (sig_scope sig) ->
      call_subst_fresh sig inp clk rst out ->
      generate_constraints sig inp clk rst out st = OK (cns, st') ->
      listSatisfiable (lat_valuation dlt sig inp clk rst out) sig.(s_constraints) ->
      listSatisfiable (lat_valuation dlt sig inp clk rst out) cns.
  Proof.
    intros sig inp clk rst out cns st st' dlt Hndscope Hfresh Hgen Hsat0.
    destruct Hfresh as [Hinfresh [Hclkfresh [Hrstfresh Houtfresh]]].
    unfold generate_constraints in Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hreorder).
    pose proof (subst_constraints_inp_map_length _ _ _ _ _ _ HinpSub) as HlenIn.
    pose proof (subst_constraints_out_map_length _ _ _ _ _ _ HoutSub) as HlenOut.
    set (ival := lat_valuation dlt sig inp clk rst out).
    assert (Hfresh_all : call_subst_fresh sig inp clk rst out).
    { repeat split; assumption. }
    pose proof (lat_valuation_inputs_eq dlt sig inp clk rst out Hfresh_all Hndscope HlenIn)
      as Hinputs_eq.
    assert (Hinput_cond :
              forall x ty,
                lat_valuation dlt sig inp clk rst out x = hm_ext dlt ty ->
                type_fresh (sig_scope sig) ty ->
                inp_replace_cond ival x ty).
    {
      intros x ty Heq Hty.
      unfold inp_replace_cond, ival.
      rewrite (hm_ext_lat_valuation_on_fresh_type dlt sig inp clk rst out ty Hty).
      rewrite Heq.
      exact (order_refl _ _ (eq_refl (hm_ext dlt ty))).
    }
    assert (Hrep_in : Forall2 (inp_replace_cond ival) sig.(s_in) inp).
    {
      assert (Hmap :
                forall xs ys,
                  Forall2
                    (fun x ty =>
                       lat_valuation dlt sig inp clk rst out x = hm_ext dlt ty)
                    xs ys ->
                  types_fresh (sig_scope sig) ys ->
                  Forall2 (inp_replace_cond ival) xs ys).
      {
        intros xs ys Hrel.
        induction Hrel; intro Hfreshys.
        - constructor.
        - inversion Hfreshys as [|ty ys' Hty Htys]; subst.
          constructor.
          + eapply Hinput_cond; eauto.
          + eapply IHHrel; exact Htys.
      }
      eapply Hmap; eauto.
    }
    assert (Hsat1 : listSatisfiable ival c1).
    {
      eapply subst_constraints_inp_map_correct with (dlt := ival).
      - exact HinpSub.
      - exact Hsat0.
      - exact Hrep_in.
    }
    assert (Hsat2 : listSatisfiable ival c2).
    {
      pose proof (lat_valuation_clk_eq dlt sig inp clk rst out Hfresh_all Hndscope)
        as HclkEq.
      pose proof (hm_ext_lat_valuation_on_fresh_type dlt sig inp clk rst out clk Hclkfresh)
        as HclkFreshEq.
      eapply subst_ident_in_constraints_correct.
      - exact HclkSub.
      - exact Hsat1.
      - unfold ival.
        rewrite HclkFreshEq.
        rewrite HclkEq.
        exact (order_refl _ _ (eq_refl _)).
    }
    assert (Hsat3 : listSatisfiable ival c3).
    {
      pose proof (lat_valuation_reset_eq dlt sig inp clk rst out Hfresh_all Hndscope)
        as HrstEq.
      pose proof (hm_ext_lat_valuation_on_fresh_type dlt sig inp clk rst out rst Hrstfresh)
        as HrstFreshEq.
      eapply subst_ident_in_constraints_correct.
      - exact HrstSub.
      - exact Hsat2.
      - unfold ival.
        rewrite HrstFreshEq.
        rewrite HrstEq.
        exact (order_refl _ _ (eq_refl _)).
    }
    assert (Hsat4 : listSatisfiable ival c4).
    {
      eapply subst_constraints_out_map_correct.
      - exact HoutSub.
      - exact Hsat3.
      - eapply lat_valuation_outputs_eq.
        * exact Hfresh_all.
        * exact Hndscope.
        * exact HlenOut.
    }
    eapply reorder_constraints_correct; eauto.
  Qed.

  Lemma subst_constraints_inp_map_rhs:
    forall cs xs tys cs' st st',
      SIG.subst_constraints_inp_map cs xs tys st = OK (cs', st') ->
      map snd cs' = map snd cs.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs tys cs' st st' Hsub.
    - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. reflexivity.
    - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      rewrite (IH _ _ _ _ _ Htl).
      exact (SIG.subst_ident_in_constraints_rhs _ _ _ _ _ _ Hhd).
  Qed.

  Lemma subst_constraints_out_map_complete:
    forall cs xs vs cs' st st',
      SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      forall dlt,
        listSatisfiable dlt cs' ->
        listSatisfiable (upd_idents_rev dlt xs vs) cs.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs vs cs' st st' Hsub dlt Hsat.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      simpl in Hsub.
      revert Hsub.
      destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; simpl in Hsub.
      + discriminate.
      + eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
        pose proof (IH cs1 vs cs' st1 st' Htl dlt Hsat) as Hmid.
        change (listSatisfiable (upd_ident (upd_idents_rev dlt xs vs) x v) cs).
        eapply subst_ident_constraints_complete_out; eauto.
  Qed.

  Lemma subst_constraints_inp_map_complete:
    forall cs xs tys cs' st st',
      Forall2 (fun x ty => ~ In x ty) xs tys ->
      SIG.subst_constraints_inp_map cs xs tys st = OK (cs', st') ->
      forall dlt,
        listSatisfiable dlt cs' ->
        listSatisfiable (upd_types_rev dlt xs tys) cs.
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs tys cs' st st' Hfresh Hsub dlt Hsat.
    - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. exact Hsat.
    - destruct tys as [|ty tys]; simpl in Hsub; try discriminate.
      inversion Hfresh as [|x' ty' xs' tys' Hxy Hfresh']; subst x' ty' xs' tys'.
      eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
      pose proof (IH cs1 tys cs' st1 st' Hfresh' Htl dlt Hsat) as Hmid.
      change (listSatisfiable (upd_type (upd_types_rev dlt xs tys) x ty) cs).
      eapply subst_ident_in_constraints_complete; eauto.
  Qed.

  Lemma findST_none_notin_rhs:
    forall cs x,
      findST cs x = None ->
      ~ In [x] (map snd cs).
  Proof.
    intros cs x Hfind Hin.
    destruct (findST_of_rhs_in _ _ Hin) as (st & Hsome).
    rewrite Hfind in Hsome. discriminate.
  Qed.

  Lemma wf_constraints_of_singleton_perm:
    forall cs outs,
      NoDup outs ->
      Permutation (map snd cs) (map (fun y => [y]) outs) ->
      wf_constraints cs.
  Proof.
    intros cs outs Hnd Hperm.
    split.
    - eapply Permutation_NoDup.
      + apply Permutation_sym. exact Hperm.
      + eapply SIG.nodup_singleton_map. exact Hnd.
    - rewrite Forall_forall.
      intros [lhs rhs] Hin.
      assert (Hinrhs : In rhs (map snd cs)).
      { apply in_map_iff. exists (lhs, rhs). split; [reflexivity|exact Hin]. }
      eapply Permutation_in in Hinrhs; [|exact Hperm].
      apply in_map_iff in Hinrhs as (x & Heq & _).
      inversion Heq. reflexivity.
  Qed.

  Lemma subst_rhs_ident_singletons_cons:
    forall x v tail,
      ~ In x tail ->
      map (SIG.subst_rhs_ident x v) (map (fun y => [y]) (x :: tail)) =
      map (fun y => [y]) (v :: tail).
  Proof.
    intros x v tail Hnotin.
    simpl. rewrite ident_eqb_refl.
    f_equal.
    induction tail as [|a tail IH]; simpl; auto.
    assert (Hneq : x <> a).
    { intro Heq. subst a. apply Hnotin. left. reflexivity. }
    rewrite (proj2 (ident_eqb_neq x a) Hneq).
    f_equal.
    apply IH.
    intro Hin. apply Hnotin. right. exact Hin.
  Qed.

  Lemma subst_ident_constraints_shape_out_step:
    forall cs x v tail cs' st st',
      wf_constraints cs ->
      Permutation (map snd cs) (map (fun y => [y]) (x :: tail)) ->
      findST cs v = None ->
      SIG.subst_ident_constraints cs x v st = OK (cs', st') ->
      wf_constraints cs'
      /\ Permutation (map snd cs') (map (fun y => [y]) (v :: tail)).
  Proof.
    intros cs x v tail cs' st st' Hwf Hperm Hfind Hsub.
    pose proof (SIG.subst_ident_constraints_rhs _ _ _ _ _ _ Hsub) as Hrhs.
    assert (Hnd_cs : NoDup (map snd cs)).
    { exact (proj1 Hwf). }
    assert (Hnd_xtail_map : NoDup (map (fun y => [y]) (x :: tail))).
    { eapply Permutation_NoDup; [exact Hperm|exact Hnd_cs]. }
    assert (Hnd_xtail : NoDup (x :: tail)).
    { eapply NoDup_map_inv with (f := fun y => [y]). exact Hnd_xtail_map. }
    assert (Hxnotin : ~ In x tail).
    { apply NoDup_cons_iff in Hnd_xtail. exact (proj1 Hnd_xtail). }
    assert (Hvnotin_xtail : ~ In v (x :: tail)).
    {
      intro Hin.
      apply (findST_none_notin_rhs _ _ Hfind).
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - apply in_map_iff. exists v. split; [reflexivity|exact Hin].
    }
    assert (Hperm_map :
              Permutation (map (SIG.subst_rhs_ident x v) (map snd cs))
                          (map (SIG.subst_rhs_ident x v)
                               (map (fun y => [y]) (x :: tail)))).
    { eapply Permutation_map. exact Hperm. }
    replace (map (SIG.subst_rhs_ident x v) (map snd cs)) with (map snd cs') in Hperm_map
      by (symmetry; exact Hrhs).
    rewrite (subst_rhs_ident_singletons_cons x v tail Hxnotin) in Hperm_map.
    split.
    - eapply wf_constraints_of_singleton_perm.
      + apply NoDup_cons_iff. split.
        * intro Hin. apply Hvnotin_xtail. right. exact Hin.
        * apply NoDup_cons_iff in Hnd_xtail. exact (proj2 Hnd_xtail).
      + exact Hperm_map.
    - exact Hperm_map.
  Qed.

  Lemma singleton_map_perm_middle:
    forall (xs : list ident) (v : ident) (acc : list ident),
      Permutation (map (fun y => [y]) (v :: xs ++ acc))
                  (map (fun y => [y]) (xs ++ v :: acc)).
  Proof.
    intros xs v acc.
    simpl.
    rewrite !map_app.
    simpl.
    apply Permutation_middle.
  Qed.

  Lemma subst_constraints_out_map_shape_acc:
    forall cs xs vs acc cs' st st',
      wf_constraints cs ->
      Permutation (map snd cs) (map (fun y => [y]) (xs ++ acc)) ->
      SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      wf_constraints cs'
      /\ Permutation (map snd cs') (map (fun y => [y]) (vs ++ acc)).
  Proof.
    intros cs xs.
    revert cs.
    induction xs as [|x xs IH]; intros cs vs acc cs' st st' Hwf Hperm Hsub.
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      unfold ret in Hsub. inversion Hsub; subst. split; [exact Hwf|exact Hperm].
    - destruct vs as [|v vs]; simpl in Hsub; try discriminate.
      simpl in Hperm.
      revert Hsub.
      destruct (SymTypes.findST cs v) eqn:Hfind; intro Hsub; simpl in Hsub.
      + discriminate.
      + eapply sec_bind_inv in Hsub as (cs1 & st1 & Hhd & Htl).
        destruct (subst_ident_constraints_shape_out_step
                    cs x v (xs ++ acc) cs1 st st1 Hwf Hperm Hfind Hhd)
          as [Hwf1 Hperm1].
        assert (Hperm1' :
                  Permutation (map snd cs1)
                              (map (fun y => [y]) (xs ++ v :: acc))).
        {
          eapply Permutation_trans; [exact Hperm1|].
          apply singleton_map_perm_middle.
        }
        destruct (IH cs1 vs (v :: acc) cs' st1 st' Hwf1 Hperm1' Htl)
          as [Hwf2 Hperm2].
        split; [exact Hwf2|].
        eapply Permutation_trans; [exact Hperm2|].
        apply Permutation_sym.
        apply singleton_map_perm_middle.
  Qed.

  Corollary subst_constraints_out_map_shape:
    forall cs xs vs cs' st st',
      wf_constraints cs ->
      Permutation (map snd cs) (map (fun y => [y]) xs) ->
      SIG.subst_constraints_out_map cs xs vs st = OK (cs', st') ->
      wf_constraints cs'
      /\ Permutation (map snd cs') (map (fun y => [y]) vs).
  Proof.
    intros cs xs vs cs' st st' Hwf Hperm Hsub.
    assert (Hperm_nil :
              Permutation (map snd cs) (map (fun y => [y]) (xs ++ nil))).
    { rewrite app_nil_r. exact Hperm. }
    destruct (subst_constraints_out_map_shape_acc
                cs xs vs nil cs' st st' Hwf Hperm_nil Hsub)
      as [Hwf' Hperm'].
    rewrite app_nil_r in Hperm'.
    split.
    - exact Hwf'.
    - exact Hperm'.
  Qed.

  Lemma signature_good_outputs_nodup:
    forall sig,
      signature_good sig ->
      NoDup sig.(s_out).
  Proof.
    intros sig [Hwf Hperm].
    assert (Hnd_map : NoDup (map (fun y => [y]) sig.(s_out))).
    { eapply Permutation_NoDup; [exact Hperm|exact (proj1 Hwf)]. }
    eapply NoDup_map_inv with (f := fun y => [y]).
    exact Hnd_map.
  Qed.

  Theorem generate_constraints_complete_good:
    forall sig inp clk rst out cns st st',
      signature_good sig ->
      generate_constraints sig inp clk rst out st = OK (cns, st') ->
      forall dlt,
        listSatisfiable dlt cns ->
        Forall2 (fun x ty => ~ In x ty) sig.(s_in) inp ->
        ~ In sig.(s_clk) clk ->
        ~ In sig.(s_reset) rst ->
        listSatisfiable
          (upd_types_rev
             (upd_type
                (upd_type
                   (upd_idents_rev dlt sig.(s_out) out)
                   sig.(s_reset) rst)
                sig.(s_clk) clk)
             sig.(s_in) inp)
          sig.(s_constraints).
  Proof.
    intros sig inp clk rst out cns st st' Hgood Hgen dlt Hsat Hinfresh Hclkfresh Hrstfresh.
    destruct Hgood as [Hwf0 Hperm0].
    assert (Hndout0 : NoDup sig.(s_out)).
    { eapply signature_good_outputs_nodup. exact (conj Hwf0 Hperm0). }
    unfold generate_constraints in Hgen.
    eapply sec_bind_inv in Hgen as (c1 & st1 & HinpSub & Hgen).
    eapply sec_bind_inv in Hgen as (c2 & st2 & HclkSub & Hgen).
    eapply sec_bind_inv in Hgen as (c3 & st3 & HrstSub & Hgen).
    eapply sec_bind_inv in Hgen as (c4 & st4 & HoutSub & Hreorder).
    pose proof (subst_constraints_inp_map_rhs _ _ _ _ _ _ HinpSub) as Hrhs1.
    pose proof (SIG.subst_ident_in_constraints_rhs _ _ _ _ _ _ HclkSub) as Hrhs2.
    pose proof (SIG.subst_ident_in_constraints_rhs _ _ _ _ _ _ HrstSub) as Hrhs3.
    assert (Hperm1 : Permutation (map snd c1) (map (fun y => [y]) sig.(s_out))).
    { rewrite Hrhs1. exact Hperm0. }
    assert (Hwf1 : wf_constraints c1).
    { eapply wf_constraints_of_singleton_perm; eauto. }
    assert (Hperm2 : Permutation (map snd c2) (map (fun y => [y]) sig.(s_out))).
    { rewrite Hrhs2, Hrhs1. exact Hperm0. }
    assert (Hwf2 : wf_constraints c2).
    { eapply wf_constraints_of_singleton_perm; eauto. }
    assert (Hperm3 : Permutation (map snd c3) (map (fun y => [y]) sig.(s_out))).
    { rewrite Hrhs3, Hrhs2, Hrhs1. exact Hperm0. }
    assert (Hwf3 : wf_constraints c3).
    { eapply wf_constraints_of_singleton_perm; eauto. }
    destruct (subst_constraints_out_map_shape _ _ _ _ _ _ Hwf3 Hperm3 HoutSub)
      as [Hwf4 Hperm4].
    assert (Hsat4 : listSatisfiable dlt c4).
    { eapply reorder_constraints_complete; eauto. }
    assert (Hsat3 : listSatisfiable (upd_idents_rev dlt sig.(s_out) out) c3).
    { eapply subst_constraints_out_map_complete; eauto. }
    assert (Hsat2 :
              listSatisfiable
                (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst) c2).
    { eapply subst_ident_in_constraints_complete; eauto. }
    assert (Hsat1 :
              listSatisfiable
                (upd_type
                   (upd_type (upd_idents_rev dlt sig.(s_out) out) sig.(s_reset) rst)
                   sig.(s_clk) clk) c1).
    { eapply subst_ident_in_constraints_complete; eauto. }
    eapply subst_constraints_inp_map_complete; eauto.
  Qed.

  (** * Monotonicity of [generate_constraints] in its input actuals

      Weakening the actual input types weakens the generated constraints:
      the targets are unchanged and every source shrinks.  Together with
      [constraints_src_le_satisfaction] this transfers satisfaction from
      the stronger instantiation to the weaker one, which is what the
      Stc-to-Obc bridge needs (the compiled arguments drop the [when]
      guards that the source-level arguments carry). *)

  Lemma st_remove_mono:
    forall d a b,
      (forall z, In z a -> In z b) ->
      forall z, In z (SymTypes.st_remove d a) -> In z (SymTypes.st_remove d b).
  Proof.
    intros d a b Hab z Hz.
    apply SymTypes.st_remove_in_inv in Hz as [Hin Hne].
    apply SymTypes.st_remove_preserves_other_in; auto.
  Qed.

  Lemma subst_ident_in_type_mono:
    forall ty1 ty2 x v1 v2,
      (forall z, In z ty2 -> In z ty1) ->
      (forall z, In z v2 -> In z v1) ->
      forall z,
        In z (SIG.subst_ident_in_type ty2 x v2) ->
        In z (SIG.subst_ident_in_type ty1 x v1).
  Proof.
    intros ty1 ty2 x v1 v2 Hty Hv z Hz.
    unfold SIG.subst_ident_in_type in *.
    destruct (SymTypes.my_set_mem x ty2) eqn:M2.
    - (* x occurs in the smaller source, hence in the bigger one too *)
      assert (M1 : SymTypes.my_set_mem x ty1 = true).
      { apply SymTypes.my_set_mem_correct.
        apply Hty. apply SymTypes.my_set_mem_correct. exact M2. }
      rewrite M1.
      apply SymTypes.in_merge_inv in Hz.
      destruct Hz as [Hz|Hz].
      + apply SymTypes.in_merge_left. eapply st_remove_mono; eauto.
      + apply SymTypes.in_merge_right. eapply st_remove_mono; eauto.
    - (* x does not occur in the smaller source: it is returned unchanged *)
      destruct (SymTypes.my_set_mem x ty1) eqn:M1.
      + apply SymTypes.in_merge_left.
        apply SymTypes.st_remove_preserves_other_in.
        * intro Heq. subst z.
          assert (SymTypes.my_set_mem x ty2 = true)
            by (apply SymTypes.my_set_mem_correct; exact Hz).
          congruence.
        * apply Hty, Hz.
      + apply Hty, Hz.
  Qed.

  Lemma subst_inp_ident_in_constraint_mono:
    forall c1 c2 x v1 v2 d1 d2 sa sa' sb sb',
      snd c1 = snd c2 ->
      (forall z, In z (fst c2) -> In z (fst c1)) ->
      (forall z, In z v2 -> In z v1) ->
      subst_inp_ident_in_constraint c1 x v1 sa = OK (d1, sa') ->
      subst_inp_ident_in_constraint c2 x v2 sb = OK (d2, sb') ->
      snd d1 = snd d2 /\ (forall z, In z (fst d2) -> In z (fst d1)).
  Proof.
    intros [l1 r1] [l2 r2] x v1 v2 d1 d2 sa sa' sb sb' Hr Hl Hv H1 H2.
    simpl in Hr, Hl. subst r2.
    unfold subst_inp_ident_in_constraint in H1, H2.
    destruct r1 as [|y ys]; try discriminate.
    destruct ys as [|y' ys']; try discriminate.
    destruct (ident_eqb x y) eqn:Hxy; try discriminate.
    unfold ret in H1, H2.
    inversion H1; inversion H2; subst.
    split; [reflexivity|].
    simpl. intros z Hz.
    eapply subst_ident_in_type_mono; eauto.
  Qed.

  Lemma subst_ident_in_constraints_mono:
    forall cs1 cs2 x v1 v2 d1 d2 sa sa' sb sb',
      constraints_src_le cs1 cs2 ->
      (forall z, In z v2 -> In z v1) ->
      subst_ident_in_constraints cs1 x v1 sa = OK (d1, sa') ->
      subst_ident_in_constraints cs2 x v2 sb = OK (d2, sb') ->
      constraints_src_le d1 d2.
  Proof.
    unfold subst_ident_in_constraints.
    intros cs1 cs2 x v1 v2 d1 d2 sa sa' sb sb' Hle Hv.
    revert d1 d2 sa sa' sb sb'.
    induction Hle as [|c1 c2 cs1 cs2 Hc Hle IH];
      intros d1 d2 sa sa' sb sb' H1 H2.
    - simpl in H1, H2. unfold ret in H1, H2.
      inversion H1; inversion H2; subst. constructor.
    - simpl in H1, H2.
      eapply sec_bind_inv in H1 as (e1 & s1 & He1 & H1).
      eapply sec_bind_inv in H1 as (t1 & s1' & Ht1 & R1).
      unfold ret in R1. inversion R1; subst d1 sa'.
      eapply sec_bind_inv in H2 as (e2 & s2 & He2 & H2).
      eapply sec_bind_inv in H2 as (t2 & s2' & Ht2 & R2).
      unfold ret in R2. inversion R2; subst d2 sb'.
      destruct Hc as [Hcr Hcl].
      constructor.
      + eapply subst_inp_ident_in_constraint_mono; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma constraints_src_le_refl:
    forall cs, constraints_src_le cs cs.
  Proof.
    induction cs as [|c cs IH].
    - constructor.
    - constructor; [split; [reflexivity|auto]|exact IH].
  Qed.

  Lemma subst_constraints_inp_map_mono:
    forall xs vs1 vs2 cs1 cs2 d1 d2 sa sa' sb sb',
      constraints_src_le cs1 cs2 ->
      Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) vs1 vs2 ->
      subst_constraints_inp_map cs1 xs vs1 sa = OK (d1, sa') ->
      subst_constraints_inp_map cs2 xs vs2 sb = OK (d2, sb') ->
      constraints_src_le d1 d2.
  Proof.
    induction xs as [|x xs IH];
      intros vs1 vs2 cs1 cs2 d1 d2 sa sa' sb sb' Hle Hvs H1 H2.
    - destruct vs1; destruct vs2; simpl in H1, H2; try discriminate.
      unfold ret in H1, H2. inversion H1; inversion H2; subst. exact Hle.
    - destruct vs1 as [|v1 vs1']; destruct vs2 as [|v2 vs2'];
        simpl in H1, H2; try discriminate.
      inversion Hvs as [|? ? ? ? Hv Hvs']; subst.
      eapply sec_bind_inv in H1 as (c1' & s1 & Hs1 & H1).
      eapply sec_bind_inv in H2 as (c2' & s2 & Hs2 & H2).
      eapply IH; [|exact Hvs'|exact H1|exact H2].
      eapply subst_ident_in_constraints_mono; eauto.
  Qed.

  Lemma subst_ident_constraint_mono:
    forall c1 c2 x v d1 d2 sa sa' sb sb',
      snd c1 = snd c2 ->
      (forall z, In z (fst c2) -> In z (fst c1)) ->
      subst_ident_constraint c1 x v sa = OK (d1, sa') ->
      subst_ident_constraint c2 x v sb = OK (d2, sb') ->
      snd d1 = snd d2 /\ (forall z, In z (fst d2) -> In z (fst d1)).
  Proof.
    intros [l1 r1] [l2 r2] x v d1 d2 sa sa' sb sb' Hr Hl H1 H2.
    simpl in Hr, Hl. subst r2.
    unfold subst_ident_constraint in H1, H2.
    destruct (ident_eqb x v) eqn:Hxv; try discriminate.
    destruct r1 as [|y ys]; try discriminate.
    destruct ys as [|y' ys']; try discriminate.
    destruct (ident_eqb x y) eqn:Hxy;
      unfold ret in H1, H2; inversion H1; inversion H2; subst;
      (split; [reflexivity|]);
      simpl; intros z Hz;
      eapply subst_ident_in_type_mono; eauto.
  Qed.

  Lemma subst_ident_constraints_mono:
    forall cs1 cs2 x v d1 d2 sa sa' sb sb',
      constraints_src_le cs1 cs2 ->
      subst_ident_constraints cs1 x v sa = OK (d1, sa') ->
      subst_ident_constraints cs2 x v sb = OK (d2, sb') ->
      constraints_src_le d1 d2.
  Proof.
    unfold subst_ident_constraints.
    intros cs1 cs2 x v d1 d2 sa sa' sb sb' Hle.
    revert d1 d2 sa sa' sb sb'.
    induction Hle as [|c1 c2 cs1 cs2 Hc Hle IH];
      intros d1 d2 sa sa' sb sb' H1 H2.
    - simpl in H1, H2. unfold ret in H1, H2.
      inversion H1; inversion H2; subst. constructor.
    - simpl in H1, H2.
      eapply sec_bind_inv in H1 as (e1 & s1 & He1 & H1).
      eapply sec_bind_inv in H1 as (t1 & s1' & Ht1 & R1).
      unfold ret in R1. inversion R1; subst d1 sa'.
      eapply sec_bind_inv in H2 as (e2 & s2 & He2 & H2).
      eapply sec_bind_inv in H2 as (t2 & s2' & Ht2 & R2).
      unfold ret in R2. inversion R2; subst d2 sb'.
      destruct Hc as [Hcr Hcl].
      constructor.
      + eapply subst_ident_constraint_mono; eauto.
      + eapply IH; eauto.
  Qed.

  Lemma constraints_src_le_findST:
    forall cs1 cs2 d s1 s2,
      constraints_src_le cs1 cs2 ->
      SymTypes.findST cs1 d = Some s1 ->
      SymTypes.findST cs2 d = Some s2 ->
      forall z, In z s2 -> In z s1.
  Proof.
    intros cs1 cs2 d s1 s2 Hle.
    revert s1 s2.
    induction Hle as [|[l1 r1] [l2 r2] cs1 cs2 [Hr Hl] Hle IH];
      intros s1 s2 H1 H2.
    - simpl in H1. discriminate.
    - simpl in Hr, Hl. subst r2.
      simpl in H1, H2.
      destruct r1 as [|y ys].
      + eapply IH; eauto.
      + destruct ys as [|y' ys'].
        * destruct (ident_eqb y d) eqn:Hyd.
          -- inversion H1; inversion H2; subst. exact Hl.
          -- eapply IH; eauto.
        * eapply IH; eauto.
  Qed.

  Lemma subst_constraints_out_map_mono:
    forall xs vs cs1 cs2 d1 d2 sa sa' sb sb',
      constraints_src_le cs1 cs2 ->
      subst_constraints_out_map cs1 xs vs sa = OK (d1, sa') ->
      subst_constraints_out_map cs2 xs vs sb = OK (d2, sb') ->
      constraints_src_le d1 d2.
  Proof.
    induction xs as [|x xs IH];
      intros vs cs1 cs2 d1 d2 sa sa' sb sb' Hle H1 H2.
    - destruct vs; simpl in H1, H2; try discriminate.
      unfold ret in H1, H2. inversion H1; inversion H2; subst. exact Hle.
    - destruct vs as [|v vs']; simpl in H1, H2; try discriminate.
      destruct (SymTypes.findST cs1 v) eqn:F1; try discriminate.
      destruct (SymTypes.findST cs2 v) eqn:F2; try discriminate.
      eapply sec_bind_inv in H1 as (c1' & s1 & Hs1 & H1).
      eapply sec_bind_inv in H2 as (c2' & s2 & Hs2 & H2).
      eapply IH; [|exact H1|exact H2].
      eapply subst_ident_constraints_mono; eauto.
  Qed.

  Lemma generate_constraints_mono_inp:
    forall sig inp1 inp2 clk rst out cns1 cns2 sa sa' sb sb',
      Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) inp1 inp2 ->
      generate_constraints sig inp1 clk rst out sa = OK (cns1, sa') ->
      generate_constraints sig inp2 clk rst out sb = OK (cns2, sb') ->
      constraints_src_le cns1 cns2.
  Proof.
    intros sig inp1 inp2 clk rst out cns1 cns2 sa sa' sb sb' Hinp H1 H2.
    unfold generate_constraints in H1, H2.
    eapply sec_bind_inv in H1 as (a1 & s1 & Ha1 & H1).
    eapply sec_bind_inv in H1 as (b1 & t1 & Hb1 & H1).
    eapply sec_bind_inv in H1 as (c1 & u1 & Hc1 & H1).
    eapply sec_bind_inv in H1 as (e1 & w1 & He1 & H1).
    eapply sec_bind_inv in H2 as (a2 & s2 & Ha2 & H2).
    eapply sec_bind_inv in H2 as (b2 & t2 & Hb2 & H2).
    eapply sec_bind_inv in H2 as (c2 & u2 & Hc2 & H2).
    eapply sec_bind_inv in H2 as (e2 & w2 & He2 & H2).
    assert (Hle1 : constraints_src_le a1 a2).
    { eapply subst_constraints_inp_map_mono;
        [apply constraints_src_le_refl|exact Hinp|exact Ha1|exact Ha2]. }
    assert (Hle2 : constraints_src_le b1 b2).
    { eapply subst_ident_in_constraints_mono; [exact Hle1| |exact Hb1|exact Hb2]. auto. }
    assert (Hle3 : constraints_src_le c1 c2).
    { eapply subst_ident_in_constraints_mono; [exact Hle2| |exact Hc1|exact Hc2]. auto. }
    assert (Hle4 : constraints_src_le e1 e2).
    { eapply subst_constraints_out_map_mono; [exact Hle3|exact He1|exact He2]. }
    (* the final lookup pass: same outputs, ordered sources *)
    clear - Hle4 H1 H2.
    revert cns1 cns2 w1 sa' w2 sb' H1 H2.
    induction out as [|y ys IH]; intros cns1 cns2 w1 sa' w2 sb' H1 H2.
    - simpl in H1, H2. unfold ret in H1, H2.
      inversion H1; inversion H2; subst. constructor.
    - simpl in H1, H2.
      eapply sec_bind_inv in H1 as (h1 & p1 & Hh1 & H1).
      eapply sec_bind_inv in H1 as (q1 & p1' & Hq1 & R1).
      unfold ret in R1. inversion R1; subst cns1 sa'.
      eapply sec_bind_inv in H2 as (h2 & p2 & Hh2 & H2).
      eapply sec_bind_inv in H2 as (q2 & p2' & Hq2 & R2).
      unfold ret in R2. inversion R2; subst cns2 sb'.
      eapply sec_bind_inv in Hh1 as (g1 & k1 & Hg1 & Hr1).
      unfold ret in Hr1. inversion Hr1; subst h1 p1.
      eapply sec_bind_inv in Hh2 as (g2 & k2 & Hg2 & Hr2).
      unfold ret in Hr2. inversion Hr2; subst h2 p2.
      unfold option_to_sec in Hg1, Hg2.
      destruct (SymTypes.findST e1 y) as [f1|] eqn:F1; try discriminate.
      destruct (SymTypes.findST e2 y) as [f2|] eqn:F2; try discriminate.
      unfold ret in Hg1, Hg2. inversion Hg1; inversion Hg2; subst g1 g2 k1 k2.
      constructor.
      + simpl. split; [reflexivity|].
        intros z Hz. eapply constraints_src_le_findST; eauto.
      + eapply IH; eauto.
  Qed.

  (** * Signature preservation and call preservation

      Generic over signatures (no NLustre or STC syntax), hoisted here
      from the NLustre-to-Stc bridge so that every translation layer can
      use them. *)

  Definition signatures_preserved (n1 n2: signature) : Prop :=
    signature_fields_agree n1 n2
    /\ preserves_on (sig_scope n1) n1.(s_constraints) n2.(s_constraints).

  Theorem signatures_preserved_reset_underlying_calls_from_good:
    forall nsig ssig,
      signature_good nsig ->
      NoDup (sig_scope nsig) ->
      signature_scoped ssig ->
      signatures_preserved nsig ssig ->
      forall scope inptyp ckty srcrst outtyp rst_inst
             nconst sconst st_init1 st_init2 st1 st2,
        scope_fresh scope nsig ->
        call_subst_scoped scope inptyp ckty srcrst outtyp ->
        ~ In rst_inst scope ->
        call_subst_fresh nsig inptyp ckty srcrst outtyp ->
        call_subst_fresh ssig inptyp ckty (rst_inst :: nil) outtyp ->
        generate_constraints nsig inptyp ckty srcrst outtyp st_init1 = OK (nconst, st1) ->
        generate_constraints ssig inptyp ckty (rst_inst :: nil) outtyp st_init2 = OK (sconst, st2) ->
        preserves_on scope nconst ((srcrst, (rst_inst :: nil)) :: sconst).
    Proof.
    intros nsig ssig Hgood Hndscope Hssigscoped [Hfields Hpres]
           scope inptyp ckty srcrst outtyp rst_inst
           nconst sconst st_init1 st_init2 st1 st2
           Hscopefresh Hcallscoped Hrstinst_outside
           Hfresh_nsig Hfresh_ssig Hgen_nsig Hgen_ssig.
    unfold preserves_on.
    intros dlt Hsat_nconst.
    destruct Hcallscoped as [Hactualscoped Hsrcrstscope].
    pose proof Hgen_nsig as Hgen_nsig_len.
    unfold generate_constraints in Hgen_nsig_len.
    eapply sec_bind_inv in Hgen_nsig_len as (c1 & st1' & HinpSub & Hgen_nsig_len).
    eapply sec_bind_inv in Hgen_nsig_len as (c2 & st2' & HclkSub & Hgen_nsig_len).
    eapply sec_bind_inv in Hgen_nsig_len as (c3 & st3' & HrstSub & Hgen_nsig_len).
    eapply sec_bind_inv in Hgen_nsig_len as (c4 & st4' & HoutSub & Hreorder).
    pose proof (subst_constraints_inp_map_length _ _ _ _ _ _ HinpSub) as HlenIn.
    pose proof (subst_constraints_out_map_length _ _ _ _ _ _ HoutSub) as HlenOut.
    assert (Hinfresh_pairs :
              Forall2 (fun x ty => ~ In x ty) nsig.(s_in) inptyp).
    {
      eapply call_subst_fresh_inputs_notin_pairs; eauto.
    }
    destruct Hfresh_nsig as [Hinfresh [Hclkfresh [Hrstfresh Houtfresh]]].
    assert (Hfresh_nsig_all : call_subst_fresh nsig inptyp ckty srcrst outtyp).
    { repeat split; assumption. }
    assert (Hclknotin : ~ In nsig.(s_clk) ckty).
    {
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. right.
      apply in_or_app. right. simpl. now left.
    }
    assert (Hrstnotin : ~ In nsig.(s_reset) srcrst).
    {
      eapply type_fresh_notin_sig_scope; eauto.
      unfold sig_scope. apply in_or_app. right.
      apply in_or_app. right. simpl. now right; left.
    }
    pose proof
      (generate_constraints_complete_good
         nsig inptyp ckty srcrst outtyp nconst st_init1 st1
         Hgood Hgen_nsig dlt Hsat_nconst
         Hinfresh_pairs Hclknotin Hrstnotin)
      as Hsat_nsig.
    destruct (Hpres _ Hsat_nsig)
      as (dlt_mid & Hagree_mid & Hsat_ssig).
    set (dlt_ov := overlay_scope scope dlt dlt_mid).
    set (dlt_rst := overlay_scope [rst_inst] (fun _ => hm_ext dlt srcrst) dlt_ov).
    assert (Hscopefresh_ssig : scope_fresh scope ssig).
    { eapply scope_fresh_fields_agree; eauto. }
    assert (Hndscope_ssig : NoDup (sig_scope ssig)).
    { rewrite <- (signature_fields_agree_scope_eq _ _ Hfields). exact Hndscope. }
    assert (Hagree_rst_scope : agree_on scope dlt dlt_rst).
    {
      intros x Hin.
      unfold dlt_rst, dlt_ov, overlay_scope.
      destruct (in_dec ident_eq_dec x [rst_inst]) as [Hinrst|Hninrst].
      - simpl in Hinrst. destruct Hinrst as [Heq|[]]. subst x.
        exfalso. exact (Hrstinst_outside Hin).
      - destruct (in_dec ident_eq_dec x scope) as [Hin'|Hnin']; [reflexivity|contradiction].
    }
    assert (Hrstinst_eq :
              dlt_rst rst_inst = hm_ext dlt srcrst).
    {
      unfold dlt_rst, overlay_scope.
      destruct (in_dec ident_eq_dec rst_inst [rst_inst]) as [Hin|Hnin].
      - reflexivity.
      - exfalso. apply Hnin. simpl. now left.
    }
    assert (Hinst_agree :
              agree_on (sig_scope ssig)
                       (lat_valuation dlt nsig inptyp ckty srcrst outtyp)
                       (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
    {
      eapply lat_valuation_fields_agree_on_sig_scope_reset; eauto.
    }
    assert (Hmid_src :
              agree_on (sig_scope ssig)
                       dlt_mid
                       (lat_valuation dlt nsig inptyp ckty srcrst outtyp)).
    {
      intros x Hin.
      symmetry.
      pose proof (signature_fields_agree_scope_eq _ _ Hfields) as Hscopeeq.
      rewrite <- Hscopeeq in Hin.
      eapply Hagree_mid; exact Hin.
    }
    assert (Hmid_tgt_inst :
              agree_on (sig_scope ssig)
                       dlt_mid
                       (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
    {
      eapply agree_on_trans; eauto.
    }
    assert (Hsat_ssig_inst :
              listSatisfiable
                (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                ssig.(s_constraints)).
    {
      eapply listSatisfiable_ext; eauto.
    }
    assert (Hsat_sconst :
              listSatisfiable
                (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                sconst).
    {
      eapply generate_constraints_correct_inst; eauto.
    }
    assert (Hrstfresh_ssig : type_fresh (sig_scope ssig) [rst_inst]).
    {
      destruct Hfresh_ssig as [_ [_ [Hrstfresh0 _]]].
      exact Hrstfresh0.
    }
    assert (Hrstinst_notin_sig : ~ In rst_inst (sig_scope ssig)).
    {
      inversion Hrstfresh_ssig as [|? ? Hrstinst_notin' _]; subst.
      exact Hrstinst_notin'.
    }
    assert (Hagree_scope_final :
              agree_on scope dlt
                       (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
    {
      eapply agree_on_trans.
      + exact Hagree_rst_scope.
      + eapply lat_valuation_agree_on_scope; eauto.
    }
    assert (Hagree_scope_final_sym :
              agree_on scope
                (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                dlt).
    {
      intros x Hin.
      symmetry.
      apply Hagree_scope_final.
      exact Hin.
    }
    assert (Hsat_reset :
              constraintSatisfiable
                (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                (srcrst, [rst_inst])).
    {
      unfold constraintSatisfiable, satisfiable.
      rewrite (hm_ext_agree_on_scoped_type
                 scope srcrst
                 (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                 dlt
                 Hsrcrstscope
                 Hagree_scope_final_sym).
      simpl.
      rewrite lat_valuation_outside_sig_scope by exact Hrstinst_notin_sig.
      rewrite Hrstinst_eq.
      apply join_bound1.
    }
    exists (lat_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp).
    split.
    - intros x Hin.
      transitivity (dlt_rst x).
      + exact (Hagree_rst_scope x Hin).
      + symmetry.
        apply lat_valuation_outside_sig_scope.
        exact (Hscopefresh_ssig x Hin).
    - constructor; [exact Hsat_reset|exact Hsat_sconst].
    Qed.



End SIGNATURE_PROOFS.
