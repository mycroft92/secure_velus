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
  (Import NAMETOT : SECNAMINGTOTALITY Ids Op CESyn SynNL Mem IsD Ord NAMEGEN).

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

End SECNLUSTYPINGTOTALITY.
