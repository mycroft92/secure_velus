(** Security signatures and their call-time instantiation. *)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 
From Velus Require Import SIF.SecTypes. 
From Velus Require Export SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Coq   Require Import List Sorting.Permutation.
From Coq Require Import String. (* for errors *)
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

(* Lookup by node/system name inside a security-signature environment. *)
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
        error (MSG "Something wrong with fresh_gen, ident is regenerated in an inner node. " :: [CTX x])
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
  
  (* Instantiate a signature by substituting the caller's input/clock/reset
     security types and output identifiers into the stored constraints. *)
  (** The caller-facing reshaping at the end is the key interface contract used
      by the typing developments.  Stored signature constraints may be kept in
      any internal order, but a successful call instantiation rebuilds the
      concrete constraint list in the caller's output order.  This lets the
      NLustre/STC typing proofs consume the same per-call shape fact without
      carrying a separate [call_constraints_shape] assumption. *)
  Definition generate_constraints (node: signature) 
    (inp: list ST) 
    (clk: ST) 
    (res: ST) 
    (out: list ident): Sec (list constraint) :=
    do inp_subst_constraints <- subst_constraints_inp_map node.(s_constraints) node.(s_in) inp;
    do clk_subst_constraints <- subst_ident_in_constraints inp_subst_constraints node.(s_clk) clk;
    do res_subst_constraints <- subst_ident_in_constraints clk_subst_constraints node.(s_reset) res;
    do out_subst_constraints <- subst_constraints_out_map res_subst_constraints node.(s_out) out;
    mmap (fun x =>
            do st <- option_to_sec (findST out_subst_constraints x);
            ret (st, [x])) out.

  (** Stored-signature target shape.

      A generated signature is allowed to keep its constraints in any order,
      but every stored constraint must still be well formed and target exactly
      the signature outputs up to permutation.  The call-instantiation layer
      later turns this into the concrete per-call shape fact consumed by the
      NLustre and STC typing developments.  Relative to the paper, this is the
      signature-level invariant that replaces the older external
      [call_constraints_shape] premise. *)
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

  (** Legacy call-shape interface.

      This predicate is being phased out in favour of the more structural
      [signature_good] / [secglobal_good] invariants above.  It is kept only
      while the downstream typing and translation modules are migrated. *)
  Definition call_constraints_shape (G: secglobal) : Prop :=
    forall f sig inptyp ckty rstty outtyp cns st st',
      find_signature f G = Some sig ->
      NoDup outtyp ->
      generate_constraints sig inptyp ckty rstty outtyp st = OK (cns, st') ->
      wf_constraints cns
      /\ map snd cns = map (fun ty => [ty]) outtyp.

  (* Generic scope notions for symbolic types/constraints live in [SecTypes].
     This file only adds the signature-specific wrapper. *)
  Definition signature_scope (sig: signature) : list ident :=
    sig.(s_in) ++ sig.(s_out) ++ [sig.(s_clk); sig.(s_reset)].

  Definition signature_scoped (sig: signature) : Prop :=
    constraints_scoped (signature_scope sig) sig.(s_constraints).

  (* Some later call-preservation arguments need the stronger fact that every
     visible signature identifier lies in the ordinary [sec] namespace.  This
     is a generic property of signatures, while the generated-source/target
     proofs that establish it live in the corresponding correctness modules. *)
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

  (* Signature-interface agreement and call-instantiation freshness live at the
     signature layer.  They are reused by the later NLustre/STC bridge, but do
     not depend on any translation-specific theorem shape. *)
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

  (* Every stored signature in the global environment only mentions its own
     visible interface variables. This is the reusable global invariant
     consumed by the NLustre and STC typing developments. *)
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
    rewrite merge_comm2. assert (hm_ext dlt ([a] ⊔ (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st)) ⊑ join (hm_ext dlt [a]) (hm_ext dlt (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st))) as Htrans. { apply hm_ext_distributive2. }
    apply order_trans with (y:=join (hm_ext dlt [a])
               (hm_ext dlt (SymTypes.st_remove x ty ⊔ SymTypes.st_remove x st))); auto.
    simpl. rewrite <- join_bottom_eq1.  apply join_least_upper_bound; auto. eapply order_trans; eauto.
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

End SIGNATURE_PROOFS.
