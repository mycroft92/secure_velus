
From Velus Require Import Common.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.

From Coq Require Import String. (*Required for Errors *)
From compcert Require Import common.Errors.


Import List.ListNotations.

Module Type SECNLUSTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX      Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SIG   : SIGNATURE   Ids SC)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn).

  Import SECMONADNotations.
  
  Local Definition find_signature (f : ident) : secglobal -> option signature :=
    List.find (fun n=> ident_eqb n.(s_name) f).

  Definition find_env (x: ident) (env: Env.t ident): Sec ident :=
    match Env.find x env with
    | Some x' => ret x'
    | None    => error (MSG "Cannot find identifier in env: " :: [CTX x])
    end.

  (** NLustre equation typing in the shared naming environment. *)
  Section SECEQNTYPING.
    Variable G: secglobal.
    Variable env: Env.t ident. 
    Variable base_ty: ident.
    Variable rst_ty : ident.
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
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;              
              do outtyp <- mmap (fun x => find_env x env) xs;
            generate_constraints n inptyp ckty [rst_ty] outtyp
          | None   => error (MSG "Signature not found for: ":: [CTX f])
          end)
      | EqApp xs ck f exps (Some (r,ckr)) =>
         (match find_signature f G with
          | Some n =>
              do ckty   <- option_to_sec (assign_clk_type env base_ty ck);
              do rty    <- find_env r env;
              do rstty  <- option_to_sec (assign_clk_type env rst_ty ckr);
              do inptyp <- mmap (fun x => option_to_sec (assign_exp_type env x)) exps;
              do outtyp <- mmap (fun x => find_env x env) xs;
              generate_constraints n inptyp ckty ([rty] ⊔ rstty) outtyp
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

  (** Structural well-formedness of raw NLustre constraints.

      This is the source-side fact needed later by
      [SecTypes.simplify_complete].  The theorem is stated in two layers:

      - a shape theorem for one equation, saying that its generated
        constraints are indexed exactly by the mapped variables it defines;
      - a list theorem that lifts the result to a whole equation list using
        [NoDup (vars_defined eqs)] from the NLustre syntax layer.

      The [EqApp] case is isolated behind a call-instantiation hypothesis.
      That separation is intentional: the NLustre argument itself only needs
      the standard “variables are defined at most once” property, while the
      call case depends on separate metatheory for [generate_constraints]. *)

  Definition call_constraints_shape : Prop :=
    forall f sig inptyp ckty rstty outtyp cns st st',
      find_signature f G = Some sig ->
      NoDup outtyp ->
      generate_constraints sig inptyp ckty rstty outtyp st = OK (cns, st') ->
      wf_constraints cns
      /\ map snd cns = map (fun ty => [ty]) outtyp.

  Definition env_injective : Prop :=
    forall x y tx ty,
      Env.find x env = Some tx ->
      Env.find y env = Some ty ->
      tx = ty ->
      x = y.

  Ltac secInv :=
    simpl in *;
    unfold error in *;
    match goal with
    | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
        discriminate
    | H: ret _ _ = _ |- _ =>
        unfold ret in H
    | H: bind ?x ?f ?st = OK (?res, ?st') |- _ =>
        eapply sec_bind_inv in H as [? [? [? ?]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
        eapply sec_bind2_inv in H as [? [? [? [? ?]]]]
    end; simpl in *.

  Lemma get_mappings_app:
    forall xs ys txs tys,
      get_mappings xs env = Some txs ->
      get_mappings ys env = Some tys ->
      get_mappings (xs ++ ys) env = Some (txs ++ tys).
  Proof.
    induction xs as [|x xs IH]; intros ys txs tys Hxs Hys.
    - simpl in Hxs. inversion Hxs; subst. exact Hys.
    - simpl in Hxs.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [txs'|] eqn:Htail; try discriminate.
      inversion Hxs; subst txs.
      simpl. rewrite Hfind.
      rewrite (IH ys txs' tys Htail Hys).
      reflexivity.
  Qed.

  Lemma get_mappings_nodup:
    forall xs tys,
      NoDup xs ->
      env_injective ->
      get_mappings xs env = Some tys ->
      NoDup tys.
  Proof.
    induction xs as [|x xs IH]; intros tys Hnd Hinj Hmap.
    - simpl in Hmap. inversion Hmap. constructor.
    - simpl in Hmap.
      destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      destruct (get_mappings xs env) as [tys'|] eqn:Htail; try discriminate.
      inversion Hmap; subst tys.
      apply NoDup_cons.
      + intro Hin.
        apply NoDup_cons_iff in Hnd as [Hnin _].
        apply in_map_iff in Hin as ([|ty] & Heq & Hin'); inversion Heq; subst ty.
        clear Heq.
        assert (exists y, In y xs /\ Env.find y env = Some xty).
        {
          clear IH.
          induction xs as [|y ys IHys].
          - inversion Hin'.
          - simpl in Htail.
            destruct (Env.find y env) as [yty|] eqn:Hyfind; try discriminate.
            destruct (get_mappings ys env) as [tys''|] eqn:Hys; try discriminate.
            inversion Htail; subst tys'.
            simpl in Hin'.
            destruct Hin' as [Heq|Hin''].
            + inversion Heq; subst yty. exists y. split; [left; reflexivity|exact Hyfind].
            + specialize (IHys Hys Hin'') as (z & Hinz & Hzfind).
              exists z. split; [right; exact Hinz|exact Hzfind].
        }
        destruct H as (y & Hiny & Hyfind).
        assert (x = y) by (eapply Hinj; eauto).
        subst y. contradiction.
      + apply IH.
        * now apply NoDup_cons_iff in Hnd.
        * exact Hinj.
        * exact Htail.
  Qed.

  Lemma mmap_find_env_inv:
    forall xs tys st st',
      mmap (fun x => find_env x env) xs st = OK (tys, st') ->
      st' = st /\ get_mappings xs env = Some tys.
  Proof.
    induction xs as [|x xs IH]; intros tys st st' Hmap.
    - simpl in Hmap. unfold ret in Hmap. inversion Hmap; subst. split; auto.
    - simpl in Hmap.
      eapply sec_bind_inv in Hmap as (xty & st1 & Hhd & Hmap).
      eapply sec_bind_inv in Hmap as (tys' & st2 & Htl & Hret).
      unfold find_env in Hhd.
      destruct (Env.find x env) as [xty'|] eqn:Hfind; try discriminate.
      unfold ret in Hhd. inversion Hhd; subst xty st1.
      specialize (IH _ _ _ Htl) as [Hst Hmaps].
      subst st2.
      unfold ret in Hret. inversion Hret; subst tys st'.
      split; auto.
      simpl. rewrite Hfind, Hmaps. reflexivity.
  Qed.

  Lemma generate_eqn_constraint_shape:
    forall eq cns st st',
      call_constraints_shape ->
      env_injective ->
      NoDup (var_defined eq) ->
      generate_eqn_constraint eq st = OK (cns, st') ->
      exists tys,
        get_mappings (var_defined eq) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    intros eq cns st st' Hcall Hinj Hnd Hgen.
    destruct eq as [x ck ce|xs ck f exps r|x ck c0 exp].
    - simpl in Hgen. repeat secInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold option_to_sec in H2. destruct (assign_cexp_type env ce); try discriminate.
      unfold find_env in H4. destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      unfold ret in H4. inversion H4; subst.
      unfold ret in H5. inversion H5; subst cns st'.
      exists [xty]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
    - destruct r as [[rx rck]|].
      + simpl in Hgen. repeat secInv.
        unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
        unfold find_env in H2. destruct (Env.find rx env) as [rty|] eqn:Hrfind; try discriminate.
        unfold ret in H2. inversion H2; subst.
        unfold option_to_sec in H4. destruct (assign_clk_type env rst_ty rck); try discriminate.
        assert (Houts : st6 = st5 /\ get_mappings xs env = Some x3).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st6.
        eapply Hcall in H8; eauto.
        * destruct H8 as [Hwf Hsnd].
          exists x3. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
      + simpl in Hgen. repeat secInv.
        unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
        assert (Houts : st4 = st3 /\ get_mappings xs env = Some x1).
        { eapply mmap_find_env_inv; eauto. }
        destruct Houts as [Hstouts Hmapouts]. subst st4.
        eapply Hcall in H6; eauto.
        * destruct H6 as [Hwf Hsnd].
          exists x1. split; [exact Hmapouts|].
          split; [exact Hsnd|exact Hwf].
        * eapply get_mappings_nodup; eauto.
    - simpl in Hgen. repeat secInv.
      unfold option_to_sec in H0. destruct (assign_clk_type env base_ty ck); try discriminate.
      unfold option_to_sec in H2. destruct (assign_exp_type env exp); try discriminate.
      unfold find_env in H4. destruct (Env.find x env) as [xty|] eqn:Hfind; try discriminate.
      unfold ret in H4. inversion H4; subst.
      unfold ret in H5. inversion H5; subst cns st'.
      exists [xty]. split.
      + simpl. rewrite Hfind. reflexivity.
      + split; [reflexivity|].
        unfold wf_constraints. split.
        * constructor; [intro Hin; inversion Hin|constructor].
        * constructor; [simpl; reflexivity|constructor].
  Qed.

  Theorem generate_eqns_constraints_shape:
    forall eqs cns st st',
      call_constraints_shape ->
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      exists tys,
        get_mappings (vars_defined eqs) env = Some tys
        /\ map snd cns = map (fun ty => [ty]) tys
        /\ wf_constraints cns.
  Proof.
    induction eqs as [|eq eqs IH]; intros cns st st' Hcall Hinj Hnd Hgen.
    - simpl in Hgen. unfold ret in Hgen. inversion Hgen; subst.
      exists []. split; [reflexivity|].
      split; [reflexivity|].
      unfold wf_constraints. split; constructor.
    - simpl in Hgen.
      eapply sec_bind_inv in Hgen as (c1 & st1 & Heq & Hgen).
      eapply sec_bind_inv in Hgen as (c2 & st2 & Heqs & Hret).
      unfold ret in Hret. inversion Hret; subst cns st'.
      assert (Hndsplit : NoDup (var_defined eq ++ vars_defined eqs)).
      { simpl in Hnd. exact Hnd. }
      apply NoDup_app'_iff in Hndsplit as [Hnd1 [Hnd2 Hdisj]].
      edestruct generate_eqn_constraint_shape as (tys1 & Hmap1 & Hsnd1 & Hwf1); eauto.
      edestruct IH as (tys2 & Hmap2 & Hsnd2 & Hwf2); eauto.
      exists (tys1 ++ tys2). split.
      + simpl. eapply get_mappings_app; eauto.
      + split.
        * rewrite map_app, Hsnd1, Hsnd2. reflexivity.
        * unfold wf_constraints in *.
          destruct Hwf1 as [Hndc1 Hfor1].
          destruct Hwf2 as [Hndc2 Hfor2].
          split.
          -- rewrite map_app, Hsnd1, Hsnd2.
             eapply get_mappings_nodup; eauto.
             simpl. exact Hnd.
          -- rewrite Forall_app. split; auto.
  Qed.

  Corollary generate_eqns_constraints_wf:
    forall eqs cns st st',
      call_constraints_shape ->
      env_injective ->
      NoDup (vars_defined eqs) ->
      generate_eqns_constraints eqs st = OK (cns, st') ->
      wf_constraints cns.
  Proof.
    intros eqs cns st st' Hcall Hinj Hnd Hgen.
    edestruct generate_eqns_constraints_shape as (? & ? & ? & Hwf); eauto.
  Qed.


  End SECEQNTYPING.
 
  Section SECNODETYPING.
    Variable G: secglobal.

    (** Node-level raw well-formedness.

        This is the NLustre well-formedness fact used later by the translation
        proof.  The crucial source-side premise is not an ad hoc SIF property:
        it is the standard NLustre invariant [NoDup_var_defined_n_eqs], which
        follows from the node record field [n_defd].  In other words, once the
        call-instantiation layer is known to preserve the shape of callee
        constraints, the enclosing node contributes exactly the expected
        “every variable is defined once” argument from the paper. *)
    Corollary generate_node_eqns_constraints_wf:
      forall n env base_ty rst_ty raw st st',
        call_constraints_shape G env base_ty rst_ty ->
        env_injective env ->
        generate_eqns_constraints G env base_ty rst_ty n.(n_eqs) st = OK (raw, st') ->
        wf_constraints raw.
    Proof.
      intros n env base_ty rst_ty raw st st' Hcall Hinj Hraw.
      eapply generate_eqns_constraints_wf; eauto.
      apply NoDup_var_defined_n_eqs.
    Qed.

    (* Legacy self-contained signature generation, kept for comparison with the
       newer environment-driven formulation below. *)
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

      (* Environment-driven signature generation used by the translation
         preservation development. The shared [env] and [aux_names] fix the
         interface/local security identifiers ahead of time. *)
      Definition generate_node_sig (n: node) (env: Env.t ident) (aux_names: list node_aux_names) : res signature :=
      match  (do (clk_id, rst_id) <- option_to_sec (get_node_aux (n.(n_name)) aux_names);
              do clk_type <- option_to_sec (Env.find clk_id env);
              do rst_type <- option_to_sec (Env.find rst_id env);
              do inp <- option_to_sec (get_mappings_from_node (n.(n_in)) env);
              do out <- option_to_sec (get_mappings_from_node (n.(n_out)) env);
              do locals <- option_to_sec (get_mappings_from_node (n.(n_vars)) env);
            
              do constraints'    <- generate_eqns_constraints G env clk_type rst_type (n.(n_eqs));
              ret (n_name n, inp, out, rst_type, clk_type, simplify constraints' locals, env)) init_state with
      | Error e => Error e
      | OK ((name, inp, out, rst_id, ck_id, constraints, _),_) => 
          OK {| s_name  := name;
                s_in    := inp;
                s_out   := out;
                s_reset := rst_id;
                s_clk   := ck_id;
                s_constraints := constraints|}
      end.  

  End SECNODETYPING.

  Section SECGLOBALTYPING.
    Open Scope error_monad_scope.

    Fixpoint generate_all_signatures' (acc: list signature) (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names) : res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_sig acc n env aux_names;
        generate_all_signatures' (sig::acc) ns env aux_names
      end.
    Definition generate_all_signatures (node_list: global) (env: Env.t ident) (aux_names: list node_aux_names): res (list signature) :=
      generate_all_signatures' [] node_list env aux_names.

    Fixpoint generate_signatures' (acc: list signature) (node_list: global): res (list signature) :=
      match node_list with
      | [] => OK acc
      | n::ns => 
        do sig <- generate_node_signature acc n;
        generate_signatures' (sig::acc) ns
      end.

    Definition generate_signatures (node_list: global) := generate_signatures' [] node_list.

  End SECGLOBALTYPING.

End SECNLUSTYPING.

Module SecNLusTyping  
  (Ids   : IDS)
  (Op    : OPERATORS)
  (SC    : SECMONAD Ids)
  (CESyn : CESYNTAX      Op)
  (SynNL : NLSYNTAX  Ids Op CESyn)
  (SIG   : SIGNATURE   Ids SC)
  (SECCETYPING: SECCETYPING Ids Op CESyn) <: SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.

Include SECNLUSTYPING Ids Op SC CESyn SynNL SIG  SECCETYPING.


End SecNLusTyping.
