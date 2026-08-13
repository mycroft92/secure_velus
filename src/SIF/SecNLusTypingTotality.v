(** Totality of the NLustre security signature generator.

    [SecNamingTotality.v] discharges the naming pass; this file
    discharges the generator that runs on its output, which is the other
    half of the root hypothesis every SIF layer carries.

    The shape of the argument is the one the Stc and Obc legs already
    use for *relative* totality ([generate_sys_signature_ok_from_wc],
    [generate_class_signature_ok_from_wc]), except that there is no
    previous phase to read the lookups off.  They come instead from
    well-clocking:

    - a clock, an expression or a control expression mentions only
      declared variables ([wc_clock_free_in_vars] and friends), and the
      naming environment binds every declared variable, so the three
      [assign_*_type] walks return [Some];
    - the variables an equation defines are declared, so [find_env]
      answers;
    - a call names a node of the program, whose signature the induction
      has already generated and put in the accumulator.

    The last point is why the generator is run on a list in which a
    callee precedes its caller -- [rev] of an [Ordered_nodes] program,
    exactly as [SecNLusConstraintExport] does. *)

From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecNamingTotality.

From compcert Require Import common.Errors.

Open Scope list_scope.

Module Type SECNLUSTYPINGTOTALITY
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX Ids Op CESyn)
  (Import Lat   : Lattice)
  (Import SecT  : SECTYPES Lat)
  (Import SIG   : SIGNATURE Ids SC)
  (Import SIGPROOFS : SIGNATURE_PROOFS Ids SC SIG Lat SecT)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import CEIsF : CEISFREE Ids Op CESyn)
  (Import CEClo : CECLOCKING Ids Op CESyn)
  (Import SECCETYPING: SECCETYPING Ids Op CESyn CEIsF CEClo)
  (Import Ord   : NLORDERED Ids Op CESyn SynNL)
  (Import Mem   : MEMORIES Ids Op CESyn SynNL)
  (Import IsD   : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsF   : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import Clo   : NLCLOCKING Ids Op CESyn SynNL Ord Mem IsD CEIsF IsF CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN
                           CEIsF CEClo SECCETYPING Ord Mem IsD IsF Clo)
  (Import NAMETOT : SECNAMINGTOTALITY Ids Op CESyn SynNL Mem IsD Ord NAMEGEN)
  (Import SECNLUSTYPINGCORRECTNESS : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn
     SynNL Lat SecT SIG SIGPROOFS NAMEGEN CEIsF CEClo SECCETYPING Ord Mem IsD
     IsF Clo SECNLUSTYPING).

  Import SECMONADNotations.

  (** * The three [assign_*_type] walks

      Each is a straight structural recursion whose only partiality is
      an [Env.find] on a free variable.  Bind every free variable and it
      returns. *)

  Section ASSIGNTOTALITY.

    Variable env: Env.t ident.
    Variable base_ty: ident.

    Lemma assign_clk_type_total:
      forall ck,
        (forall x, Is_free_in_clock x ck ->
                   exists ty, Env.find x env = Some ty) ->
        exists ckty, SECCETYPING.assign_clk_type env base_ty ck = Some ckty.
    Proof.
      induction ck as [|ck IH x b]; intro Hfree.
      - exists [base_ty]. reflexivity.
      - destruct IH as (ckty & Hck).
        { intros y Hy. apply Hfree. now constructor. }
        destruct (Hfree x) as (xty & Hx); [now constructor|].
        exists (ckty ⊔ [xty]). simpl. now rewrite Hck, Hx.
    Qed.

    Lemma assign_exp_type_total:
      forall e,
        (forall x, Is_free_in_exp x e ->
                   exists ty, Env.find x env = Some ty) ->
        exists ety, SECCETYPING.assign_exp_type env e = Some ety.
    Proof.
      induction e as [c|x t|e IH x b|op e IH t|op e1 IH1 e2 IH2 t];
        intro Hfree.
      - exists []. reflexivity.
      - destruct (Hfree x) as (xty & Hx); [now constructor|].
        exists [xty]. simpl. now rewrite Hx.
      - destruct IH as (ety & He).
        { intros y Hy. apply Hfree. now apply FreeEwhen1. }
        destruct (Hfree x) as (xty & Hx); [now apply FreeEwhen2|].
        exists (ety ⊔ [xty]). simpl. now rewrite He, Hx.
      - apply IH. intros y Hy. apply Hfree. now constructor.
      - destruct IH1 as (e1ty & He1).
        { intros y Hy. apply Hfree. apply FreeEbinop. now left. }
        destruct IH2 as (e2ty & He2).
        { intros y Hy. apply Hfree. apply FreeEbinop. now right. }
        exists (e1ty ⊔ e2ty). simpl. now rewrite He1, He2.
    Qed.

    Lemma assign_cexp_type_total:
      forall ce,
        (forall x, Is_free_in_cexp x ce ->
                   exists ty, Env.find x env = Some ty) ->
        exists cty, SECCETYPING.assign_cexp_type env ce = Some cty.
    Proof.
      induction ce as [x ce1 IH1 ce2 IH2|e ce1 IH1 ce2 IH2|e]; intro Hfree.
      - destruct (Hfree x) as (xty & Hx); [now apply FreeEmerge_cond|].
        destruct IH1 as (c1 & H1).
        { intros y Hy. apply Hfree. now apply FreeEmerge_true. }
        destruct IH2 as (c2 & H2).
        { intros y Hy. apply Hfree. now apply FreeEmerge_false. }
        exists ([xty] ⊔ c1 ⊔ c2). simpl. now rewrite Hx, H1, H2.
      - destruct (assign_exp_type_total e) as (ety & He).
        { intros y Hy. apply Hfree. now apply FreeEite_cond. }
        destruct IH1 as (c1 & H1).
        { intros y Hy. apply Hfree. now apply FreeEite_true. }
        destruct IH2 as (c2 & H2).
        { intros y Hy. apply Hfree. now apply FreeEite_false. }
        exists (ety ⊔ c1 ⊔ c2). simpl. now rewrite He, H1, H2.
      - apply assign_exp_type_total.
        intros y Hy. apply Hfree. now constructor.
    Qed.

  End ASSIGNTOTALITY.

  (** * One equation

      The generator's remaining partiality is [find_env] on the
      variables an equation defines, the [mmap]s over a call's actuals,
      and the callee lookup.  The first two are settled by the same
      binding hypothesis as above; the callee data is a hypothesis here
      and is discharged by the program induction. *)

  Section EQNTOTALITY.

    Variable G: SIG.secglobal.
    Variable env: Env.t ident.
    Variable base_ty rst_ty: ident.

    (** Every variable the node declares is bound.  This is what
        [SecNamingTotality.generate_local_env_for_node_binds] supplies. *)

    Definition vars_bound {A: Type} (vars: list (ident * A)) : Prop :=
      forall x, InMembers x vars -> exists ty, Env.find x env = Some ty.

    Lemma mmap_find_env_ok:
      forall xs tys st,
        get_mappings xs env = Some tys ->
        mmap (fun x => SC.find_env x env) xs st = OK (tys, st).
    Proof.
      induction xs as [|x xs IH]; intros tys st Hmaps.
      - simpl in Hmaps. inversion Hmaps; subst. reflexivity.
      - simpl in Hmaps.
        destruct (Env.find x env) as [xty|] eqn:Hx; simpl in Hmaps;
          try discriminate.
        destruct (get_mappings xs env) as [tys'|] eqn:Htys; simpl in Hmaps;
          try discriminate.
        inversion Hmaps; subst tys.
        cbn [mmap].
        eapply SC.sec_bind_ok;
          [unfold SC.find_env; rewrite Hx; reflexivity|].
        eapply SC.sec_bind_ok; [apply IH; reflexivity|reflexivity].
    Qed.

    Lemma mmap_assign_exp_type_ok:
      forall es st,
        Forall (fun e => forall x, Is_free_in_exp x e ->
                                   exists ty, Env.find x env = Some ty) es ->
        exists tys, mmap (fun e => SC.option_to_sec
                                     (SECCETYPING.assign_exp_type env e)) es st
                    = OK (tys, st).
    Proof.
      induction es as [|e es IH]; intros st Hall.
      - exists []. reflexivity.
      - inversion Hall as [|e' es' He Hes]; subst e' es'.
        destruct (assign_exp_type_total env e He) as (ety & Hety).
        destruct (IH st Hes) as (tys & Htys).
        exists (ety :: tys).
        cbn [mmap].
        eapply SC.sec_bind_ok;
          [unfold SC.option_to_sec; rewrite Hety; reflexivity|].
        eapply SC.sec_bind_ok; [exact Htys|reflexivity].
    Qed.

    (** [SecNLusNonInterferenceHelpers.v] proves the same fact, but it is
        three files further down the build; keeping a local copy is
        cheaper than reordering the development for one list lemma. *)

    Lemma get_mappings_length_eq:
      forall xs tys,
        get_mappings xs env = Some tys ->
        List.length xs = List.length tys.
    Proof.
      induction xs as [|x xs IH]; intros tys Hmap.
      - simpl in Hmap. inversion Hmap. reflexivity.
      - simpl in Hmap.
        destruct (Env.find x env) as [xty|] eqn:Hfind; simpl in Hmap;
          try discriminate.
        destruct (get_mappings xs env) as [tys'|] eqn:Htys; simpl in Hmap;
          try discriminate.
        inversion Hmap; subst tys. simpl. f_equal.
        apply IH. reflexivity.
    Qed.

    (** The two [Forall2]s of a well-clocked call, read as boundedness of
        the actuals and of the results.  The scoped counterparts in
        [SecNLusTyping.v] are relative to an environment and a scope;
        these are the plain binding versions totality needs. *)

    Lemma wc_call_args_bound:
      forall vars sub ck (ins: list (ident * (type * clock))) (es: list exp),
        vars_bound vars ->
        Forall2 (fun '(x, (_, xck)) le =>
                   SameVar (sub x) le
                   /\ exists lck, wc_exp vars le lck /\ instck ck sub xck = Some lck)
                ins es ->
        Forall (fun e => forall x, Is_free_in_exp x e ->
                                   exists ty, Env.find x env = Some ty) es.
    Proof.
      intros vars sub ck ins es Hbound Hfor.
      induction Hfor as [|[y [yt yck]] le ins' es' Hhead Hall IH]; constructor.
      - intros z Hz. apply Hbound.
        destruct Hhead as (_ & lck & Hexp & _).
        eapply wc_exp_free_in_vars; eauto.
      - exact IH.
    Qed.

    Lemma wc_call_outs_bound:
      forall vars sub ck (outs: list (ident * (type * clock))) (xs: list ident),
        vars_bound vars ->
        Forall2 (fun '(y, (_, yck)) x =>
                   sub y = Some x
                   /\ exists xck, In (x, xck) vars /\ instck ck sub yck = Some xck)
                outs xs ->
        forall x, In x xs -> exists ty, Env.find x env = Some ty.
    Proof.
      intros vars sub ck outs xs Hbound Hfor.
      induction Hfor as [|[y [yt yck]] x1 outs' xs' Hhead Hall IH]; intros z Hz.
      - inversion Hz.
      - destruct Hz as [Heq|Hz]; [subst z|now apply IH].
        apply Hbound. destruct Hhead as (_ & xck & Hin & _).
        eapply In_InMembers; exact Hin.
    Qed.

    (** The data a call needs from its callee's already-generated
        signature.  Every conjunct is one hypothesis of
        [generate_constraints_ok_from_good]. *)

    Definition call_data (P: global) (vars: list (ident * clock))
                         (f: ident) (les: list exp) (xs: list ident) : Prop :=
      exists sig,
        SIG.find_signature f G = Some sig
        /\ SIGPROOFS.signature_targets_out sig
        /\ NoDup (SIG.signature_scope sig)
        /\ List.length sig.(SIG.s_in) = List.length les
        /\ List.length sig.(SIG.s_out) = List.length xs
        /\ (forall outtyp,
               get_mappings xs env = Some outtyp ->
               NoDup outtyp /\ SIG.outputs_fresh (SIG.signature_scope sig) outtyp).

    Theorem generate_eqn_constraint_ok:
      forall P vars eq st,
        wc_env vars ->
        wc_equation P vars eq ->
        vars_bound vars ->
        (forall xs ck f les r,
            eq = EqApp xs ck f les r -> xs <> [] -> call_data P vars f les xs) ->
        exists cns st',
          SECNLUSTYPING.generate_eqn_constraint G env base_ty rst_ty eq st
          = OK (cns, st').
    Proof.
      intros P vars eq st Hwcenv Hwc Hbound Hcalls.
      destruct eq as [x ck ce|xs ck f les r|x ck c0 e].
      - (* EqDef *)
        inversion Hwc as [x' ck' ce' Hx Hce| |]; subst.
        destruct (assign_clk_type_total env base_ty ck) as (ckty & Hck).
        { intros z Hz. apply Hbound.
          eapply wc_clock_free_in_vars; [|exact Hz].
          eapply wc_env_var; eauto. }
        destruct (assign_cexp_type_total env ce) as (cty & Hcty).
        { intros z Hz. apply Hbound. eapply wc_cexp_free_in_vars; eauto. }
        destruct (Hbound x) as (xty & Hxty); [eapply In_InMembers; exact Hx|].
        do 2 eexists. cbn [SECNLUSTYPING.generate_eqn_constraint].
        eapply SC.sec_bind_ok;
          [unfold SC.option_to_sec; rewrite Hck; reflexivity|].
        eapply SC.sec_bind_ok;
          [unfold SC.option_to_sec; rewrite Hcty; reflexivity|].
        eapply SC.sec_bind_ok;
          [unfold SC.find_env; rewrite Hxty; reflexivity|reflexivity].
      - (* EqApp *)
        inversion Hwc as [|xs' ck' f' les' r' n sub Hfindnode Hinputs Houtputs Hreset|];
          subst.
        assert (Hckb : forall x, Is_free_in_clock x ck ->
                                 exists ty, Env.find x env = Some ty).
        { intros z Hz. apply Hbound.
          eapply wc_call_clock_free_in_vars; eauto. }
        assert (Hargs : Forall (fun e => forall x, Is_free_in_exp x e ->
                                                   exists ty, Env.find x env = Some ty)
                               les)
          by (eapply wc_call_args_bound; eauto).
        destruct xs as [|x0 xs0].
        + do 2 eexists. reflexivity.
        + assert (Hxs : (x0 :: xs0) <> []) by discriminate.
          destruct (Hcalls (x0 :: xs0) ck f les r Logic.eq_refl Hxs)
            as (sig & Hfsig & Htgt & Hndsc & Hlenin & Hlenout & Hout).
          destruct (assign_clk_type_total env base_ty ck) as (ckty & Hck);
            [exact Hckb|].
          destruct (mmap_assign_exp_type_ok les st) as (inptyp & Hinp);
            [exact Hargs|].
          assert (Houtsb : forall x, In x (x0 :: xs0) ->
                                     exists ty, Env.find x env = Some ty)
            by (eapply wc_call_outs_bound; eauto).
          assert (Houts : exists outtyp,
                     get_mappings (x0 :: xs0) env = Some outtyp).
          { apply get_mappings_Some_iff, Forall_forall. exact Houtsb. }
          destruct Houts as (outtyp & Houttyp).
          destruct (Hout outtyp Houttyp) as (Hndout & Hfresh).
          assert (Hleni : List.length sig.(SIG.s_in) = List.length inptyp).
          { rewrite Hlenin. symmetry. eapply mmap_length; exact Hinp. }
          assert (Hleno : List.length sig.(SIG.s_out) = List.length outtyp).
          { rewrite Hlenout.
            eapply get_mappings_length_eq; exact Houttyp. }
          destruct r as [[rx rck]|].
          * (* reset call *)
            assert (Hrin : In (rx, rck) vars) by (apply Hreset; reflexivity).
            destruct (Hbound rx) as (rty & Hrty);
              [eapply In_InMembers; exact Hrin|].
            destruct (assign_clk_type_total env base_ty rck) as (rstty & Hrstty).
            { intros z Hz. apply Hbound.
              eapply wc_clock_free_in_vars; [|exact Hz].
              eapply wc_env_var; eauto. }
            destruct (SIGPROOFS.generate_constraints_ok_from_good
                        sig inptyp ckty ([rst_ty] ⊔ ([rty] ⊔ rstty)) outtyp st
                        Htgt Hndsc Hleni Hleno Hfresh Hndout)
              as (cns & Hgc).
            do 2 eexists. cbn [SECNLUSTYPING.generate_eqn_constraint].
            rewrite Hfsig.
            eapply SC.sec_bind_ok;
              [unfold SC.option_to_sec; rewrite Hck; reflexivity|].
            eapply SC.sec_bind_ok;
              [unfold SC.find_env; rewrite Hrty; reflexivity|].
            eapply SC.sec_bind_ok;
              [unfold SC.option_to_sec; rewrite Hrstty; reflexivity|].
            eapply SC.sec_bind_ok; [exact Hinp|].
            eapply SC.sec_bind_ok;
              [exact (mmap_find_env_ok _ _ st Houttyp)|exact Hgc].
          * (* ordinary call *)
            destruct (SIGPROOFS.generate_constraints_ok_from_good
                        sig inptyp ckty [rst_ty] outtyp st
                        Htgt Hndsc Hleni Hleno Hfresh Hndout)
              as (cns & Hgc).
            do 2 eexists. cbn [SECNLUSTYPING.generate_eqn_constraint].
            rewrite Hfsig.
            eapply SC.sec_bind_ok;
              [unfold SC.option_to_sec; rewrite Hck; reflexivity|].
            eapply SC.sec_bind_ok; [exact Hinp|].
            eapply SC.sec_bind_ok;
              [exact (mmap_find_env_ok _ _ st Houttyp)|exact Hgc].
      - (* EqFby *)
        inversion Hwc as [| |x' ck' v le Hx Hle]; subst.
        destruct (assign_clk_type_total env base_ty ck) as (ckty & Hck).
        { intros z Hz. apply Hbound.
          eapply wc_clock_free_in_vars; [|exact Hz].
          eapply wc_env_var; eauto. }
        destruct (assign_exp_type_total env e) as (ety & Hety).
        { intros z Hz. apply Hbound. eapply wc_exp_free_in_vars; eauto. }
        destruct (Hbound x) as (xty & Hxty); [eapply In_InMembers; exact Hx|].
        do 2 eexists. cbn [SECNLUSTYPING.generate_eqn_constraint].
        eapply SC.sec_bind_ok;
          [unfold SC.option_to_sec; rewrite Hck; reflexivity|].
        eapply SC.sec_bind_ok;
          [unfold SC.option_to_sec; rewrite Hety; reflexivity|].
        eapply SC.sec_bind_ok;
          [unfold SC.find_env; rewrite Hxty; reflexivity|reflexivity].
    Qed.

    (** A body generates when each of its equations does. *)

    Theorem generate_eqns_constraints_ok:
      forall P vars eqs st,
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        vars_bound vars ->
        (forall eq xs ck f les r,
            In eq eqs -> eq = EqApp xs ck f les r -> xs <> [] ->
            call_data P vars f les xs) ->
        exists cns st',
          SECNLUSTYPING.generate_eqns_constraints G env base_ty rst_ty eqs st
          = OK (cns, st').
    Proof.
      induction eqs as [|eq eqs IH]; intros st Hwcenv Hwc Hbound Hcalls.
      - do 2 eexists. reflexivity.
      - inversion Hwc as [|eq' eqs' Heq Heqs]; subst eq' eqs'.
        destruct (generate_eqn_constraint_ok P vars eq st Hwcenv Heq Hbound)
          as (cns & st1 & Hgen).
        { intros xs ck f les r Hshape Hxs.
          eapply Hcalls; [now left|exact Hshape|exact Hxs]. }
        destruct (IH st1 Hwcenv Heqs Hbound) as (cns' & st2 & Hrec).
        { intros eq' xs ck f les r Hin Hshape Hxs.
          eapply Hcalls; [now right; exact Hin|exact Hshape|exact Hxs]. }
        exists (cns ++ cns'), st2.
        cbn [SECNLUSTYPING.generate_eqns_constraints].
        eapply SC.sec_bind_ok; [exact Hgen|].
        eapply SC.sec_bind_ok; [exact Hrec|reflexivity].
    Qed.

  End EQNTOTALITY.

  (** * One node

      The per-equation call hypothesis is now discharged from facts
      about the *accumulated* signatures: each callee's signature was
      generated by an earlier step, so it is good and its scope is
      bounded below the window this node's names occupy.  That bound is
      what makes the caller's outputs fresh for the callee's scope --
      the one obligation of [generate_constraints_ok_from_good] that
      does not follow from the callee's own well-formedness. *)

  Section NODETOTALITY.

    (** A call's results are among the variables the body defines, and a
        body defines each variable once.  ([SecNLusStcTranslation.v]
        proves the same two facts, but four files further down.) *)

    Lemma eqapp_outputs_in_vars:
      forall n xs ck f les r x,
        In (EqApp xs ck f les r) n.(n_eqs) ->
        In x xs ->
        In x (map fst (n.(n_vars) ++ n.(n_out))).
    Proof.
      intros n xs ck f les r x Hin Hx.
      rewrite <- n.(n_defd).
      unfold vars_defined. apply in_flat_map.
      exists (EqApp xs ck f les r). split; [exact Hin|exact Hx].
    Qed.

    Lemma vars_defined_app:
      forall l1 l2,
        vars_defined (l1 ++ l2) = vars_defined l1 ++ vars_defined l2.
    Proof.
      induction l1 as [|eq l1 IH]; intro l2; simpl.
      - reflexivity.
      - unfold vars_defined in *. simpl. rewrite IH. apply app_assoc.
    Qed.

    Lemma eqapp_outputs_nodup:
      forall n xs ck f les r,
        In (EqApp xs ck f les r) n.(n_eqs) ->
        NoDup xs.
    Proof.
      intros n xs ck f les r Hin.
      pose proof (node_vars_defined_NoDup n) as Hnd.
      apply in_split in Hin as (l1 & l2 & Heq).
      rewrite Heq, vars_defined_app in Hnd.
      apply NoDup_app_r in Hnd.
      cbn [vars_defined flat_map var_defined] in Hnd.
      eapply NoDup_app_l; exact Hnd.
    Qed.

    (** The node's own names all lie in the scope
        [node_scope_fresh_in_env] talks about, so a call's output types
        inherit its freshness. *)

    Lemma call_outputs_fresh:
      forall n env aux_names G xs ck f les r outtyp
             clk_id rst_id clk_type rst_type inp out locals,
        SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n env aux_names G ->
        get_node_aux n.(n_name) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node n.(n_in) env = Some inp ->
        get_mappings_from_node n.(n_out) env = Some out ->
        get_mappings_from_node n.(n_vars) env = Some locals ->
        In (EqApp xs ck f les r) n.(n_eqs) ->
        get_mappings xs env = Some outtyp ->
        forall sig,
          SIG.find_signature f G = Some sig ->
          SIG.outputs_fresh (SIG.signature_scope sig) outtyp.
    Proof.
      intros n env aux_names G xs ck f les r outtyp
             clk_id rst_id clk_type rst_type inp out locals
             Hfresh Haux Hclk Hrst Hinp Hout Hlocals Hin Houttyp sig Hfindsig.
      specialize (Hfresh clk_id rst_id clk_type rst_type inp out locals
                    Haux Hclk Hrst Hinp Hout Hlocals f sig Hfindsig).
      unfold SIG.outputs_fresh. apply Forall_forall.
      intros ty Hty.
      (* [ty] is the type of a variable the call defines *)
      destruct (get_mappings_In _ _ _ _ Houttyp Hty) as (x & Hx & Hfindx).
      assert (Hinvar : In x (map fst (n.(n_vars) ++ n.(n_out))))
        by (eapply eqapp_outputs_in_vars; eauto).
      rewrite map_app in Hinvar.
      apply in_app_iff in Hinvar as [Hinvar|Hinvar].
      - (* a local *)
        apply get_mappings_from_node_eq in Hlocals.
        destruct (get_mappings_in _ _ _ _ Hinvar Hlocals) as (ty' & Hty' & Hinty').
        rewrite Hfindx in Hty'. inversion Hty'; subst ty'.
        eapply Hfresh.
        apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; now left.
      - (* an output *)
        apply get_mappings_from_node_eq in Hout.
        destruct (get_mappings_in _ _ _ _ Hinvar Hout) as (ty' & Hty' & Hinty').
        rewrite Hfindx in Hty'. inversion Hty'; subst ty'.
        eapply Hfresh.
        apply in_or_app; right. apply in_or_app; now left.
    Qed.

    (** The per-node theorem.  Everything the generator looks up is now
        accounted for: the interface through the naming run, the
        equations through well-clocking, and the callees through the
        accumulator. *)

    Theorem generate_node_sig_ok:
      forall P G n env rec aux_names st st',
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst)) ->
        wc_node P n ->
        SIG.secglobal_scope_bounded_above G st ->
        (forall f, Is_node_in f n.(n_eqs) ->
           exists sig n',
             SIG.find_signature f G = Some sig
             /\ SIG.signature_good sig
             /\ NoDup (SIG.signature_scope sig)
             /\ find_node f P = Some n'
             /\ List.length sig.(SIG.s_in) = List.length n'.(n_in)
             /\ List.length sig.(SIG.s_out) = List.length n'.(n_out)) ->
        exists sig, SECNLUSTYPING.generate_node_sig G n env aux_names = OK sig.
    Proof.
      intros P G n env rec aux_names st st'
             Hlocal Haux Hwc Hbound Hcalls.
      destruct (generate_local_env_for_node_covers _ _ _ _ _ Hlocal)
        as ((clk_type & Hclk) & (rst_type & Hrst)
            & (inp & Hinp) & (locals & Hlocals) & (out & Hout)).
      assert (Henvinj : SECNLUSTYPING.env_injective env)
        by (eapply generate_local_env_for_node_injective; eauto).
      assert (Hfresh : node_scope_fresh_in_env n env aux_names G)
        by (eapply node_scope_fresh_in_env_from_bounds; eauto).
      destruct Hwc as (_ & _ & Hwcenv & Hwceqs).
      (* the node's declared variables are all bound *)
      assert (Hbnd : vars_bound env
                       (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))).
      { intros x Hx.
        apply InMembers_idck, fst_InMembers in Hx.
        eapply generate_local_env_for_node_binds; [exact Hlocal|].
        right. right. exact Hx. }
      (* and every call has its callee's data *)
      assert (Hcd : forall eq xs ck f les r,
                 In eq n.(n_eqs) -> eq = EqApp xs ck f les r -> xs <> [] ->
                 call_data G env P
                   (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) f les xs).
      { intros eq xs ck f les r Hin Hshape Hxs. subst eq.
        destruct (Hcalls f) as (sig & n' & Hfsig & Hgood & Hndsc
                                & Hfnode & Hlenin & Hlenout).
        { unfold Is_node_in. apply Exists_exists.
          exists (EqApp xs ck f les r). split; [exact Hin|constructor]. }
        rewrite Forall_forall in Hwceqs.
        pose proof (Hwceqs _ Hin) as Hwceq.
        inversion Hwceq as [|xs' ck' f' les' r' n0 sub Hfn0 Hins Houts Hr|];
          subst.
        rewrite Hfnode in Hfn0. inversion Hfn0; subst n0.
        exists sig.
        split; [exact Hfsig|].
        split; [apply SIGPROOFS.signature_good_targets_out, Hgood|].
        split; [exact Hndsc|].
        split; [rewrite Hlenin; eapply Forall2_length; exact Hins|].
        split; [rewrite Hlenout; eapply Forall2_length; exact Houts|].
        intros otys Hotys.
        split.
        - eapply SECNLUSTYPING.get_mappings_nodup;
            [eapply eqapp_outputs_nodup; exact Hin|exact Henvinj|exact Hotys].
        - eapply call_outputs_fresh with (n := n) (les := les) (r := r);
            eauto. }
      destruct (generate_eqns_constraints_ok G env clk_type rst_type
                  P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                  n.(n_eqs) init_state Hwcenv Hwceqs Hbnd Hcd)
        as (cns & st_n & Hcns).
      eexists.
      unfold SECNLUSTYPING.generate_node_sig.
      cbn [bind bind2 option_to_sec ret].
      rewrite Haux. cbn [bind bind2 option_to_sec ret].
      rewrite Hclk. cbn [bind bind2 option_to_sec ret].
      rewrite Hrst. cbn [bind bind2 option_to_sec ret].
      rewrite Hinp. cbn [bind bind2 option_to_sec ret].
      rewrite Hout. cbn [bind bind2 option_to_sec ret].
      rewrite Hlocals. cbn [bind bind2 option_to_sec ret].
      unfold bind, ret. rewrite Hcns. simpl. reflexivity.
    Qed.

  End NODETOTALITY.

  (** * The whole program

      The generator walks a list in which a callee precedes its caller
      and pushes each fresh signature onto the accumulator, so when a
      node is reached, the signatures of every node before it are
      available.  [Ordered_nodes] orders a program the other way -- a
      callee comes *after* its caller -- which is exactly why the driver
      reverses the list before generating
      ([SecNLusConstraintExport.generate_nlustre_constraint_dump]). *)

  Section PROGRAMTOTALITY.

    (** A node of a duplicate-free program is what [find_node] finds
        under its own name. *)

    Lemma In_find_node:
      forall (G: global) n,
        NoDup (map n_name G) ->
        In n G ->
        find_node n.(n_name) G = Some n.
    Proof.
      induction G as [|nd G IH]; intros n Hnd Hin; [inversion Hin|].
      simpl in Hnd. inversion Hnd as [|x xs Hnotin Hnd']; subst x xs.
      destruct Hin as [Heq|Hin].
      - subst nd. simpl. rewrite ident_eqb_refl. reflexivity.
      - simpl.
        destruct (ident_eqb nd.(n_name) n.(n_name)) eqn:Hname.
        + exfalso. apply ident_eqb_eq in Hname.
          apply Hnotin. rewrite Hname. now apply in_map.
        + apply IH; assumption.
    Qed.

    (** Every node a body calls is named further along the program. *)

    Lemma Ordered_nodes_calls_later:
      forall prefix nd suffix f,
        Ordered_nodes (prefix ++ nd :: suffix) ->
        Is_node_in f nd.(n_eqs) ->
        Exists (fun n' => f = n'.(n_name)) suffix.
    Proof.
      intros prefix nd suffix f Hord Hin.
      apply Ordered_nodes_append in Hord.
      inversion Hord as [|nd' nds Hord' Hcalls Hdist]; subst nd' nds.
      apply Hcalls, Hin.
    Qed.

    (** Read on the reversed list, "further along" becomes "already
        seen": a callee is named by one of the nodes the generator has
        processed. *)

    Lemma rev_calls_precede:
      forall all_nodes prefix n suffix f,
        Ordered_nodes all_nodes ->
        rev all_nodes = prefix ++ n :: suffix ->
        Is_node_in f n.(n_eqs) ->
        exists n', In n' prefix /\ n'.(n_name) = f.
    Proof.
      intros all_nodes prefix n suffix f Hord Hsplit Hin.
      assert (Hall : all_nodes = rev suffix ++ n :: rev prefix).
      { rewrite <- (rev_involutive all_nodes), Hsplit.
        rewrite rev_app_distr. simpl. rewrite <- app_assoc. reflexivity. }
      rewrite Hall in Hord.
      pose proof (Ordered_nodes_calls_later _ _ _ _ Hord Hin) as Hex.
      apply Exists_exists in Hex as (n' & Hn' & Heq).
      exists n'. split; [apply in_rev in Hn'; exact Hn'|now symmetry].
    Qed.

    (** The induction's invariant on the accumulator: every node already
        walked has a signature in it, well formed and with the arity of
        its node.  That is exactly the data a call site needs. *)

    Definition acc_covers (acc: SIG.secglobal) (ns: list node) : Prop :=
      forall n', In n' ns ->
        exists sig,
          SIG.find_signature n'.(n_name) acc = Some sig
          /\ SIG.signature_good sig
          /\ NoDup (SIG.signature_scope sig)
          /\ List.length sig.(SIG.s_in) = List.length n'.(n_in)
          /\ List.length sig.(SIG.s_out) = List.length n'.(n_out).

    Lemma get_mappings_from_node_length:
      forall {A: Type} (xs: list (ident * A)) env tys,
        get_mappings_from_node xs env = Some tys ->
        List.length xs = List.length tys.
    Proof.
      induction xs as [|[x a] xs IH]; intros env tys Hmap.
      - simpl in Hmap. inversion Hmap. reflexivity.
      - simpl in Hmap.
        destruct (Env.find x env) as [ty|] eqn:Hx; simpl in Hmap;
          try discriminate.
        destruct (get_mappings_from_node xs env) as [tys'|] eqn:Htys;
          simpl in Hmap; try discriminate.
        inversion Hmap; subst tys. simpl. f_equal.
        eapply IH; exact Htys.
    Qed.

    (** The walk.  [prefix] is what has been generated, [nodes] what is
        left; the naming run is split at the same point, so the state
        [st] bounds every name the accumulator mentions and every name
        the next node will mint lies above it. *)

    Theorem generate_all_signatures_scoped_env'_ok:
      forall P nodes prefix acc envs aux_names envs_pref aux_pref st,
        generate_node_scoped_env' prefix (Env.empty _) nil init_state
          = OK ((envs_pref, aux_pref), st) ->
        generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
        Forall (wc_node P) nodes ->
        NoDup (map n_name P) ->
        NoDup (map n_name (prefix ++ nodes)) ->
        (forall n, In n (prefix ++ nodes) -> In n P) ->
        (forall pre n suf,
            prefix ++ nodes = pre ++ n :: suf ->
            forall f, Is_node_in f n.(n_eqs) ->
                      exists n', In n' pre /\ n'.(n_name) = f) ->
        acc_covers acc prefix ->
        SIG.secglobal_scoped acc ->
        SIG.secglobal_scope_bounded_above acc st ->
        exists G,
          SECNLUSTYPING.generate_all_signatures_scoped_env' acc nodes envs
            aux_names = OK G.
    Proof.
      intros P nodes. induction nodes as [|n nodes IH];
        intros prefix acc envs aux_names envs_pref aux_pref st
               Hprefgen Henvsgen Hwc Hndp Hnd Hinp Hcp Hcov Hsc Hbound.
      - eexists. reflexivity.
      - inversion Hwc as [|n' ns Hwcn Hwctl]; subst n' ns.
        pose proof Henvsgen as Hfull.
        unfold generate_node_scoped_env in Hfull.
        destruct (generate_node_scoped_env' (prefix ++ n :: nodes)
                    (Env.empty _) nil init_state)
          as [[[envs_full aux_full] st_full]|] eqn:Hrun; try discriminate.
        inversion Hfull; subst envs_full aux_full; clear Hfull.
        edestruct generate_node_scoped_env'_split_node
          as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
              & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
          [exact Hrun|].
        rewrite Hprefgen in Hpref.
        inversion Hpref; subst envs_pref' aux_pref' st_pref.
        assert (Hcureq : st_cur = st_local).
        { unfold fresh_insert_node_env in Hins.
          destruct (Env.mem n.(n_name) envs_pref) eqn:Hmem; try discriminate.
          unfold insert_node_env, NMret in Hins. now inversion Hins. }
        subst st_cur.
        pose proof (generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
        assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
        { eapply generate_node_scoped_env'_preserves_find; [exact Htail|].
          eapply fresh_insert_node_env_finds_new; exact Hins. }
        assert (Hauxlocal : get_node_aux n.(n_name) aux_names
                            = Some (rec.(nclk), rec.(nrst))).
        { eapply generate_node_scoped_env'_preserves_get_node_aux;
            [exact Htail| |eapply fresh_insert_node_env_finds_new; exact Hins].
          unfold get_node_aux. simpl.
          rewrite <- Hrecname, ident_eqb_refl. reflexivity. }
        assert (Henvinj : SECNLUSTYPING.env_injective local_env)
          by (eapply generate_local_env_for_node_injective; eauto).
        assert (Hcalls : forall f, Is_node_in f n.(n_eqs) ->
                   exists sig n',
                     SIG.find_signature f acc = Some sig
                     /\ SIG.signature_good sig
                     /\ NoDup (SIG.signature_scope sig)
                     /\ find_node f P = Some n'
                     /\ List.length sig.(SIG.s_in) = List.length n'.(n_in)
                     /\ List.length sig.(SIG.s_out) = List.length n'.(n_out)).
        { intros f Hnodein.
          destruct (Hcp prefix n nodes Logic.eq_refl f Hnodein)
            as (n' & Hn'in & Hn'name).
          destruct (Hcov n' Hn'in)
            as (sig & Hfsig & Hgood & Hndsc & Hleni & Hleno).
          exists sig, n'. rewrite <- Hn'name.
          split; [exact Hfsig|].
          split; [exact Hgood|].
          split; [exact Hndsc|].
          split; [apply In_find_node;
                  [exact Hndp|apply Hinp, in_or_app; now left]|].
          split; [exact Hleni|exact Hleno]. }
        destruct (generate_node_sig_ok P acc n local_env rec aux_names st st_local
                    Hlocal Hauxlocal Hwcn Hbound Hcalls) as (sig & Hsig).
        edestruct generate_node_sig_inv
          as (clk_id & rst_id & clk_type & rst_type & inp & out & locals
              & nconst & st_n & Haux' & Hclk & Hrst & Hinp' & Hout' & Hloc'
              & Hraw & Hsigdef); [exact Hsig|].
        rewrite Hauxlocal in Haux'. inversion Haux'; subst clk_id rst_id.
        assert (Hgood : SIG.signature_good sig).
        { rewrite Hsigdef.
          eapply generate_node_sig_good_from_local_env; eauto. }
        assert (Hndsc : NoDup (SIG.signature_scope sig)).
        { rewrite Hsigdef.
          eapply (generate_node_sig_scope_nodup_from_local_env
                    n local_env rec st st_local clk_type rst_type inp out);
            eauto. }
        assert (Hsigsc : SIG.signature_scoped sig)
          by (eapply SECNLUSTYPING.generate_node_sig_scoped; eauto).
        assert (Hname : sig.(SIG.s_name) = n.(n_name))
          by (rewrite Hsigdef; reflexivity).
        assert (Hleni : List.length sig.(SIG.s_in) = List.length n.(n_in)).
        { rewrite Hsigdef. simpl. symmetry.
          eapply get_mappings_from_node_length; exact Hinp'. }
        assert (Hleno : List.length sig.(SIG.s_out) = List.length n.(n_out)).
        { rewrite Hsigdef. simpl. symmetry.
          eapply get_mappings_from_node_length; exact Hout'. }
        assert (Hle : (st <= st_local)%positive)
          by (eapply generate_local_env_for_node_state_monotone; eauto).
        assert (Hbound' : SIG.secglobal_scope_bounded_above (sig :: acc) st_local).
        { eapply SIG.secglobal_scope_bounded_above_cons.
          - intros ty Hty.
            eapply generated_node_sig_scope_upper_bound_from_local_env;
              [exact Hlocal|exact Hsig|exact Hty].
          - eapply SIG.secglobal_scope_bounded_above_monotone; eauto. }
        assert (Hnotin : ~ In n.(n_name) (map n_name prefix)).
        { rewrite map_app in Hnd. simpl in Hnd.
          intro Hmem. eapply NoDup_app_In in Hnd; [|exact Hmem].
          apply Hnd. now left. }
        assert (Hcov' : acc_covers (sig :: acc) (prefix ++ [n])).
        { intros n'' Hn''.
          apply in_app_iff in Hn'' as [Hn''|Hn''].
          - destruct (Hcov n'' Hn'')
              as (sig'' & Hf'' & Hg'' & Hnd'' & Hli'' & Hlo'').
            exists sig''.
            split.
            { unfold SIG.find_signature. simpl.
              destruct (ident_eqb sig.(SIG.s_name) n''.(n_name)) eqn:Heq.
              - exfalso. apply ident_eqb_eq in Heq.
                apply Hnotin. rewrite Hname in Heq. rewrite Heq.
                now apply in_map.
              - exact Hf''. }
            split; [exact Hg''|].
            split; [exact Hnd''|].
            split; [exact Hli''|exact Hlo''].
          - destruct Hn'' as [Heq|[]]. subst n''.
            exists sig.
            split.
            { unfold SIG.find_signature. simpl.
              rewrite Hname, ident_eqb_refl. reflexivity. }
            split; [exact Hgood|].
            split; [exact Hndsc|].
            split; [exact Hleni|exact Hleno]. }
        assert (Hstep : SECNLUSTYPING.generate_node_sig_scoped_env acc n envs
                          aux_names = OK sig).
        { unfold SECNLUSTYPING.generate_node_sig_scoped_env.
          rewrite Hfindlocal. exact Hsig. }
        edestruct (IH (prefix ++ [n]) (sig :: acc) envs aux_names
                     envs_cur (rec :: aux_pref) st_local)
          as (G & HG).
        + eapply generate_node_scoped_env'_app; [exact Hprefgen|].
          cbn [generate_node_scoped_env'].
          eapply NMbind2_ok; [exact Hlocal|].
          eapply NMbind_ok; [exact Hins|].
          eapply NMbind2_ok; [reflexivity|reflexivity].
        + rewrite <- app_assoc. exact Henvsgen.
        + exact Hwctl.
        + exact Hndp.
        + rewrite <- app_assoc. exact Hnd.
        + rewrite <- app_assoc. exact Hinp.
        + rewrite <- app_assoc. exact Hcp.
        + exact Hcov'.
        + eapply SIG.secglobal_scoped_cons; eauto.
        + exact Hbound'.
        + exists G. simpl. rewrite Hstep. exact HG.
    Qed.

    (** A well-clocked ordered program is well-clocked node by node
        against the *whole* program, which is the form the walk wants.
        [wc_global] only relates each node to the tail below it. *)

    Lemma wc_global_Forall_wc_node:
      forall G, Ordered_nodes G -> wc_global G -> Forall (wc_node G) G.
    Proof.
      intros G Hord Hwc. apply Forall_forall. intros n Hin.
      eapply wc_find_node'; [exact Hord|exact Hwc|].
      apply In_find_node;
        [eapply Ordered_nodes_NoDup_names; exact Hord|exact Hin].
    Qed.

    (** The generator succeeds on the list the driver hands it. *)

    Corollary generate_all_signatures_scoped_env_ok:
      forall all_nodes envs aux_names,
        Ordered_nodes all_nodes ->
        wc_global all_nodes ->
        generate_node_scoped_env (rev all_nodes) = OK (envs, aux_names) ->
        exists G,
          SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs
            aux_names = OK G.
    Proof.
      intros all_nodes envs aux_names Hord Hwc Hnaming.
      assert (Hnd : NoDup (map n_name all_nodes))
        by (eapply Ordered_nodes_NoDup_names; exact Hord).
      pose proof (wc_global_Forall_wc_node all_nodes Hord Hwc) as Hall.
      unfold SECNLUSTYPING.generate_all_signatures_scoped_env.
      eapply (generate_all_signatures_scoped_env'_ok all_nodes (rev all_nodes)
                nil nil envs aux_names (Env.empty _) nil init_state).
      - reflexivity.
      - simpl. exact Hnaming.
      - apply Forall_forall. intros n Hin.
        rewrite Forall_forall in Hall. apply Hall.
        apply in_rev. exact Hin.
      - exact Hnd.
      - simpl. rewrite map_rev.
        eapply Permutation_NoDup; [apply Permutation_rev|exact Hnd].
      - simpl. intros n Hin. apply in_rev. exact Hin.
      - simpl. intros pre n suf Hsplit f Hf.
        eapply rev_calls_precede; eauto.
      - intros n' [].
      - apply SIG.secglobal_scoped_nil.
      - apply SIG.secglobal_scope_bounded_above_nil.
    Qed.

    (** ** The root hypothesis, discharged

        Both halves together: an ordered, well-clocked source program has
        a naming run, and the NLustre signature generator succeeds on it.
        This is the hypothesis every SIF layer's top-level theorem
        carries, and the head of the totality chain in
        [SecObcNonInterference.generate_all_signatures_chain_ok]. *)

    Theorem source_signature_generation_total:
      forall all_nodes,
        Ordered_nodes all_nodes ->
        wc_global all_nodes ->
        exists envs aux_names G,
          generate_node_scoped_env (rev all_nodes) = OK (envs, aux_names)
          /\ SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes)
               envs aux_names = OK G.
    Proof.
      intros all_nodes Hord Hwc.
      destruct (generate_node_scoped_env_ok_rev all_nodes Hord)
        as (envs & aux_names & Hnaming).
      destruct (generate_all_signatures_scoped_env_ok all_nodes envs aux_names
                  Hord Hwc Hnaming) as (G & HG).
      exists envs, aux_names, G. split; assumption.
    Qed.

  End PROGRAMTOTALITY.

End SECNLUSTYPINGTOTALITY.
