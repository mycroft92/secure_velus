(*** Translation preservation from NLustre typing constraints to STC typing constraints.

     This file proves a deliberately weak preservation statement.

     - We do not require the NLustre and STC lattice mappings to coincide everywhere.
     - We only require agreement on a chosen list of shared variables.
     - STC is allowed to introduce additional auxiliary variables, in particular
       reset-instance variables created during the STC translation.

     The proof is organised in three layers:

     1. [eqn_preserv]: one NLustre equation versus the STC constraints produced
        by [translate_eqn].
     2. [eqns_preserv_scoped]: extension to a list of equations through the
        scoped concatenation argument.
     3. [node_preserv_scoped]: instantiation of the list-level theorem for a
        translated
        node/system pair, with the scope chosen to be the interface variables,
        locals, clock type, and reset type. *)
From Coq Require Import List.
Import List.ListNotations.
From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import SecLattice.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import SIF.SymTypes.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcClocking.
From Velus Require Import NLustre.Memories.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecSTCTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecStcTypingCorrectness.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecTypes.
From Velus Require Import Clocks.

From Coq Require Import String. (*Required for Errors *)
From Coq Require Import Program.Equality.
From Coq Require Import Permutation.
From compcert Require Import common.Errors.

Module Type SECNLUSSTCTRANSLATION
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import SecTypes : SECTYPES Lat)
  (Import CESyn    : CESYNTAX      Op)
  (Import SynNL    : NLSYNTAX  Ids Op CESyn)
  (Import SynStc   : STCSYNTAX Ids Op CESyn)
  (Import Mem      : MEMORIES  Ids Op CESyn SynNL)
  (Import Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (Import SIG          : SIGNATURE   Ids SC)
  (Import SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecTypes)
  (Import NAMEGEN : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING  : SECCETYPING Ids Op CESyn)
  (Import CEIsF        : CEISFREE Ids Op CESyn)
  (Import CEClo        : CECLOCKING Ids Op CESyn)
  (Import OrdNL        : NLORDERED Ids Op CESyn SynNL)
  (Import IsD          : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsFNL        : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import CloNL        : NLCLOCKING Ids Op CESyn SynNL OrdNL Mem IsD CEIsF IsFNL CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
  (Import SECNLUSTYPINGCORRECTNESS
      : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecTypes SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL SECNLUSTYPING)
  (Import Last         : STCISLAST Ids Op CESyn SynStc)
  (Import Var          : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def          : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst         : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc       : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsFStc       : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc       : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc)
  (Import SECSTCTYPINGCORRECTNESS
      : SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecTypes SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING).
  (** In this section we relate the constraint generator for one NLustre
      equation with the constraint generator for the STC constraints obtained
      by translation. *)
  Section SECEQNPRES.

    (** Generic lattice-mapping agreement now lives in [SecTypes].  This file keeps
        only the weak preservation relation built on top of that shared notion. *)

    (** Signature-interface freshness and call-instantiation side conditions
        now live in [SIFSignature].  We keep the local shorthand [sig_scope]
        only to avoid rewriting the later translation proofs. *)
    Local Notation sig_scope := signature_scope.
    Definition signatures_preserved (n1 n2: signature) : Prop :=
      signature_fields_agree n1 n2
      /\ preserves_on (sig_scope n1) n1.(s_constraints) n2.(s_constraints).

    (** [Signature_call_preserves n1 n2] packages the two call-specific
        obligations used by [eqn_preserv]:

        - ordinary calls instantiate the callee signatures with the caller's
          argument/output types;
        - resettable calls do the same, while allowing STC to prepend one fresh
          reset-instance constraint outside the shared scope. *)
    Definition Signature_call_preserves (n1 n2: signature) : Prop :=
      (forall scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2,
          scope_fresh scope n1 ->
          call_subst_scoped scope inptyp ckty rstty outtyp ->
          call_subst_fresh n1 inptyp ckty rstty outtyp ->
          call_subst_fresh n2 inptyp ckty rstty outtyp ->
          generate_constraints n1 inptyp ckty rstty outtyp st_init1 = OK (nconst, st1) ->
          generate_constraints n2 inptyp ckty rstty outtyp st_init2 = OK (sconst, st2) ->
          preserves_on scope nconst sconst)
      /\ (forall scope inptyp ckty srcrst outtyp reset_lhs rst_inst nconst sconst st_init1 st_init2 st1 st2,
            scope_fresh scope n1 ->
            call_subst_scoped scope inptyp ckty srcrst outtyp ->
            reset_lhs = srcrst ->
            ~ In rst_inst scope ->
            call_subst_fresh n1 inptyp ckty srcrst outtyp ->
            call_subst_fresh n2 inptyp ckty (rst_inst :: nil) outtyp ->
            generate_constraints n1 inptyp ckty srcrst outtyp st_init1 = OK (nconst, st1) ->
            generate_constraints n2 inptyp ckty (rst_inst :: nil) outtyp st_init2 = OK (sconst, st2) ->
            preserves_on scope nconst ((reset_lhs, (rst_inst :: nil)) :: sconst)).

    (** [Signature_head_consistent n1 n2] is the local compatibility predicate
        for one NLustre/STC signature pair. [Signature_consistent] below is just
        the pointwise lifting of this predicate over global signature lists. *)
    Definition Signature_head_consistent (n1 n2: signature) : Prop :=
      n1.(s_name) = n2.(s_name)
      /\ signature_fields_agree n1 n2
      /\ Signature_call_preserves n1 n2.

    (** [Signature_consistent G1 G2] is the abstract compatibility assumption
        relating a source global signature environment and a target one.

        For each callee signature found on the NLustre side, it provides:

        - a matching STC signature with the same interface fields;
        - preservation for ordinary calls;
        - preservation for resettable calls, where STC is allowed to prepend one
          extra reset-instance constraint using a fresh identifier outside the
          chosen shared scope.

        This is the point where the present mechanisation intentionally differs
        from a literal "same signature" theorem from the paper: the statement
        explicitly tolerates STC-only auxiliaries. *)
    Definition Signature_consistent (G1 G2: secglobal) : Prop :=
      forall f n1,
        SIG.find_signature f G1 = Some n1 ->
        exists n2,
          SIG.find_signature f G2 = Some n2
          /\ Signature_head_consistent n1 n2.
    Hint Unfold Signature_call_preserves Signature_head_consistent Signature_consistent.

    (** Reset-call keys in source equations.

        These helpers isolate the only source-defined variables that create
        private STC auxiliaries during translation: the leading output of a
        resettable [EqApp].  They are used later to relate source equation-list
        structure to the reset-instance environment generated on the STC side. *)
    Definition reset_call_var (e: equation) : option ident :=
      match e with
      | EqApp (x :: _) _ _ _ (Some _) => Some x
      | _ => None
      end.

    Fixpoint reset_call_vars (eqs: list equation) : list ident :=
      match eqs with
      | nil => nil
      | e :: eqs' =>
          match reset_call_var e with
          | Some x => x :: reset_call_vars eqs'
          | None => reset_call_vars eqs'
          end
      end.

    Lemma reset_call_vars_in_vars_defined:
      forall eqs x,
        In x (reset_call_vars eqs) ->
        In x (vars_defined eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      { inversion Hin. }
      destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp]; simpl in *.
      { right. exact (IH _ Hin). }
      {
        destruct xs as [|x0 xs']; simpl in *.
        { exact (IH _ Hin). }
        destruct orst as [[r ckr]|]; simpl in *.
        { destruct Hin as [Heq|Hin].
          - subst x. simpl. now left.
          - simpl. right. apply in_app_iff. right. exact (IH _ Hin). }
        { right. apply in_app_iff. right. exact (IH _ Hin). }
      }
      { right. exact (IH _ Hin). }
    Qed.

    Lemma reset_call_vars_nodup:
      forall eqs,
        NoDup (vars_defined eqs) ->
        NoDup (reset_call_vars eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros Hnd.
      - constructor.
      - destruct eq as [y ck ce|xs ck f exps orst|y ck c0 exp]; simpl in *.
        + apply NoDup_cons_iff in Hnd as [_ Htail].
          exact (IH Htail).
        + destruct xs as [|x0 xs']; simpl in *.
          * exact (IH Hnd).
          * destruct orst as [[r ckr]|]; simpl in *.
            -- apply NoDup_cons.
               ++ intro Hin.
                  apply (reset_call_vars_in_vars_defined eqs) in Hin.
                  apply NoDup_cons_iff in Hnd as [Hnin _].
                  apply Hnin.
                  apply in_app_iff. right. exact Hin.
               ++ apply IH.
                  apply NoDup_cons_iff in Hnd as [_ Htail].
                  eapply NoDup_app_r. exact Htail.
            -- apply IH.
               apply NoDup_cons_iff in Hnd as [_ Htail].
               eapply NoDup_app_r. exact Htail.
        + apply NoDup_cons_iff in Hnd as [_ Htail].
          exact (IH Htail).
    Qed.

    Lemma reset_call_var_translate_eqn:
      forall eq x,
        reset_call_var eq = Some x ->
        exists ck f,
          In (TcReset x ck f) (translate_eqn eq).
    Proof.
      intros [y ck ce|xs ck f exps orst|y ck c0 exp] x Hreset;
        simpl in Hreset; try discriminate.
      destruct xs as [|x0 xs]; try discriminate.
      destruct orst as [[r ckr]|]; try discriminate.
      inversion Hreset; subst x.
      exists (Con ckr r true), f.
      simpl. now left.
    Qed.

    Lemma reset_call_vars_translate_eqns:
      forall eqs x,
        In x (reset_call_vars eqs) ->
        exists ck f,
          In (TcReset x ck f) (translate_eqns eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      - inversion Hin.
      - simpl in Hin.
        destruct (reset_call_var eq) as [x0|] eqn:Hreset.
        + destruct Hin as [Heq|Hin].
          * subst x.
            destruct (reset_call_var_translate_eqn _ _ Hreset) as (ck & f & Hin').
            exists ck, f.
            unfold translate_eqns. simpl. now apply in_or_app; left.
          * destruct (IH _ Hin) as (ck & f & Hin').
            exists ck, f.
            unfold translate_eqns. simpl. now apply in_or_app; right.
        + destruct (IH _ Hin) as (ck & f & Hin').
          exists ck, f.
          unfold translate_eqns. simpl. now apply in_or_app; right.
    Qed.

    (** Concrete reset-instance extras used by translated equation blocks.

        A resettable NLustre call introduces exactly one STC-only auxiliary
        identifier, obtained by looking up the call's leading output in the
        reset-instance environment built for the translated system.  The list
        version mirrors [reset_call_vars] and will later be used to track the
        private variables threaded through the scoped concatenation proof. *)
    Definition eqn_reset_extras (rst_env: Env.t ident) (eq: equation)
      : option (list ident) :=
      match reset_call_var eq with
      | Some x =>
          match Env.find x rst_env with
          | Some ty => Some (ty :: nil)
          | None => None
          end
      | None => Some nil
      end.

    Fixpoint eqns_reset_extras (rst_env: Env.t ident) (eqs: list equation)
      : option (list ident) :=
      match eqs with
      | nil => Some nil
      | eq :: eqs' =>
          match eqn_reset_extras rst_env eq, eqns_reset_extras rst_env eqs' with
          | Some tys1, Some tys2 => Some (tys1 ++ tys2)
          | _, _ => None
          end
      end.

    Lemma get_mappings_In_here:
      forall xs env tys ty,
        get_mappings xs env = Some tys ->
        In ty tys ->
        exists x, In x xs /\ Env.find x env = Some ty.
    Proof.
      induction xs as [|x xs IH]; intros env tys ty Hmap Hin.
      - simpl in Hmap. inversion Hmap; subst. inversion Hin.
      - simpl in Hmap.
        destruct (Env.find x env) as [xty|] eqn:Hfind.
        2: discriminate.
        destruct (get_mappings xs env) as [tys'|] eqn:Hmaps.
        2: discriminate.
        inversion Hmap; subst tys.
        simpl in Hin.
        destruct Hin as [Heq|Hin].
        + subst ty. exists x. split; [left; reflexivity|exact Hfind].
        + specialize (IH env tys' ty Hmaps Hin) as (x' & Hin' & Hfind').
          exists x'. split; [right; exact Hin'|exact Hfind'].
    Qed.

    Lemma eqns_reset_extras_eq_get_mappings:
      forall eqs rst_env,
        eqns_reset_extras rst_env eqs = get_mappings (reset_call_vars eqs) rst_env.
    Proof.
      induction eqs as [|eq eqs IH]; intros rst_env; simpl.
      - reflexivity.
      - destruct (reset_call_var eq) as [x|] eqn:Hreset.
        + unfold eqn_reset_extras. rewrite Hreset. simpl.
          destruct (Env.find x rst_env) as [ty|] eqn:Hfind; simpl.
          * rewrite IH.
            destruct (get_mappings (reset_call_vars eqs) rst_env) as [tys|] eqn:Htail;
              reflexivity.
          * reflexivity.
        + unfold eqn_reset_extras. rewrite Hreset. simpl.
          rewrite IH.
          destruct (get_mappings (reset_call_vars eqs) rst_env) as [tys|] eqn:Htail;
            reflexivity.
    Qed.

    Lemma eqns_reset_extras_complete:
      forall rst_env eqs tys x ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In x (reset_call_vars eqs) ->
        Env.find x rst_env = Some ty ->
        In ty tys.
    Proof.
      intros rst_env eqs tys x ty Hextras Hin Hfind.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      destruct (get_mappings_in _ _ _ _ Hin Hextras) as (ty' & Hfind' & Hin').
      rewrite Hfind in Hfind'. inversion Hfind'. subst ty'. exact Hin'.
    Qed.

    Lemma eqns_reset_extras_In:
      forall rst_env eqs tys ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In ty tys ->
        exists x,
          In x (reset_call_vars eqs)
          /\ Env.find x rst_env = Some ty.
    Proof.
      intros rst_env eqs tys ty Hextras Hin.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      eapply get_mappings_In_here; eauto.
    Qed.

    Lemma eqns_reset_extras_nodup:
      forall rst_env eqs tys,
        NoDup (reset_call_vars eqs) ->
        SECSTCTYPING.env_injective rst_env ->
        eqns_reset_extras rst_env eqs = Some tys ->
        NoDup tys.
    Proof.
      intros rst_env eqs tys Hnd Hinj Hextras.
      rewrite eqns_reset_extras_eq_get_mappings in Hextras.
      eapply SECSTCTYPING.get_mappings_nodup; eauto.
    Qed.

    Lemma eqns_reset_extras_fresh:
      forall rst_env eqs tys scope,
        eqns_reset_extras rst_env eqs = Some tys ->
        (forall x rst_inst st1 st2,
            find_env x rst_env st1 = OK (rst_inst, st2) ->
            ~ In rst_inst scope) ->
        forall ty, In ty tys -> ~ In ty scope.
    Proof.
      intros rst_env eqs tys scope Hextras Hfresh ty Hin HinScope.
      destruct (eqns_reset_extras_In _ _ _ _ Hextras Hin) as (x & Hinx & Hfind).
      eapply (Hfresh x ty init_state init_state).
      - eapply SC.find_env_of_Env_find; eauto.
      - exact HinScope.
    Qed.

    Lemma get_mappings_exists:
      forall xs env,
        (forall x, In x xs -> exists ty, Env.find x env = Some ty) ->
        exists tys, get_mappings xs env = Some tys.
    Proof.
      induction xs as [|x xs IH]; intros env Hfind.
      - exists nil. reflexivity.
      - destruct (Hfind x) as [ty Hxty]; [left; reflexivity|].
        destruct (IH env) as [tys Htys].
        + intros y Hy. apply Hfind. right. exact Hy.
        + exists (ty :: tys). simpl. rewrite Hxty, Htys. reflexivity.
    Qed.

    Lemma eqns_reset_extras_exists:
      forall rst_env eqs,
        (forall x, In x (reset_call_vars eqs) -> exists ty, Env.find x rst_env = Some ty) ->
        exists tys, eqns_reset_extras rst_env eqs = Some tys.
    Proof.
      intros rst_env eqs Hfind.
      rewrite eqns_reset_extras_eq_get_mappings.
      eapply get_mappings_exists; eauto.
    Qed.

    Lemma trconstrs_reset_keys_translate_eqn:
      forall eq x,
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqn eq)) ->
        reset_call_var eq = Some x.
    Proof.
      intros [y ck ce|xs ck f exps orst|y ck c0 exp] x Hin;
        simpl in *; try contradiction.
      destruct xs as [|x0 xs']; simpl in *; try contradiction.
      destruct orst as [[r ckr]|]; simpl in *; try contradiction.
      intuition congruence.
    Qed.

    Lemma trconstrs_reset_keys_translate_eqns:
      forall eqs x,
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        In x (reset_call_vars eqs).
    Proof.
      induction eqs as [|eq eqs IH]; intros x Hin.
      - inversion Hin.
      - unfold translate_eqns in Hin. simpl in Hin.
        change
          (In x
             (SECSTCTYPING.trconstrs_reset_keys
                (translate_eqn eq ++ translate_eqns eqs))) in Hin.
        rewrite SECSTCTYPINGCORRECTNESS.trconstrs_reset_keys_app in Hin.
        apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        + destruct (reset_call_var eq) as [x0|] eqn:Hreset; simpl.
          * pose proof (trconstrs_reset_keys_translate_eqn _ _ Hin) as Heq.
            rewrite Heq. simpl. auto.
          * pose proof (trconstrs_reset_keys_translate_eqn _ _ Hin) as Heq.
            congruence.
        + destruct (reset_call_var eq) as [x0|] eqn:Hreset; simpl.
          * rewrite Hreset. simpl. exact (or_intror (IH _ Hin)).
          * rewrite Hreset. simpl. exact (IH _ Hin).
    Qed.

    (** Bridging translated reset keys to the concrete mapped extras.

        The scoped concatenation proof later needs exactly this fact: whenever
        the STC constraints generated from [translate_eqns eqs] consult the
        reset-instance environment on some source identifier [x], the returned
        security variable belongs to the private-extra list reconstructed by
        [eqns_reset_extras rst_env eqs]. *)
    Lemma translated_reset_key_in_extras:
      forall rst_env eqs tys x ty,
        eqns_reset_extras rst_env eqs = Some tys ->
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        Env.find x rst_env = Some ty ->
        In ty tys.
    Proof.
      intros rst_env eqs tys x ty Hextras Hin Hfind.
      eapply eqns_reset_extras_complete; eauto.
      eapply trconstrs_reset_keys_translate_eqns; eauto.
    Qed.

    Lemma translated_reset_key_fresh:
      forall rst_env eqs tys scope x ty st1 st2,
        eqns_reset_extras rst_env eqs = Some tys ->
        (forall y rst_inst st3 st4,
            find_env y rst_env st3 = OK (rst_inst, st4) ->
            ~ In rst_inst scope) ->
        In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
        find_env x rst_env st1 = OK (ty, st2) ->
        In ty tys /\ ~ In ty scope.
    Proof.
      intros rst_env eqs tys scope x ty st1 st2 Hextras Hfresh Hin Hfind.
      split.
      - unfold find_env in Hfind.
        destruct (Env.find x rst_env) as [ty'|] eqn:Henv; try discriminate.
        inversion Hfind; subst ty' st2.
        eapply translated_reset_key_in_extras; eauto.
      - eapply Hfresh; eauto.
    Qed.

    (** Local clocking preservation for translated equations and nodes.

        These are the lightweight translation-clocking lemmas needed by the
        scoped concatenation proof.  They deliberately avoid pulling the full
        [NL2StcClocking] functor into the SIF proof: all we need here is that a
        well-clocked NLustre fragment translates to STC constraints and systems
        that are accepted by the STC clocking judgement under the corresponding
        translated environments. *)
    Lemma gather_eqs_n_vars_wc_local:
      forall n G,
        Forall (wc_equation G (idck (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
        Permutation (idck (fst (gather_eqs (n_eqs n))))
                    (idck
                       (fst
                          (partition
                             (fun x : ident * (type * clock) =>
                                PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                             (n_vars n)))).
    Proof.
      intros * WC.
      rewrite fst_partition_filter.
      apply NoDup_Permutation.
      - apply NoDupMembers_NoDup, NoDupMembers_idck, fst_NoDupMembers.
        rewrite fst_fst_gather_eqs_var_defined.
        pose proof (NoDup_var_defined_n_eqs n) as Hnodup;
          rewrite <-is_filtered_vars_defined in Hnodup.
        rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
        rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
        auto.
      - apply NoDupMembers_NoDup, fst_NoDupMembers.
        rewrite map_fst_idck, filter_mem_fst.
        apply nodup_filter.
        pose proof (n.(n_nodup)) as Hnodup.
        apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
        now apply fst_NoDupMembers.
      - intros (x, ck).
        setoid_rewrite ps_from_list_gather_eqs_memories.
        assert (forall x, In x (vars_defined (filter is_fby (n_eqs n))) ->
                     InMembers x (n_vars n)) as Spec
            by (intro; rewrite <-fst_partition_memories_var_defined, fst_partition_filter,
                       filter_mem_fst, filter_In, fst_InMembers; intuition).
        pose proof (filter_fst_idck (n_vars n)
                                    (fun x => PS.mem x (Mem.memories (n_eqs n)))) as E;
          setoid_rewrite E; clear E.
        setoid_rewrite filter_In.
        setoid_rewrite <-PSE.MP.Dec.F.mem_iff.
        unfold Mem.memories, gather_eqs in *.
        generalize (@nil (ident * ident)).
        induction (n_eqs n) as [|[]]; inversion_clear WC as [|?? WCeq]; simpl; intros; auto.
        + split; try contradiction.
          setoid_rewrite PSE.MP.Dec.F.empty_iff; intuition.
        + cases.
        + inversion_clear WCeq as [| |???? Hinc].
          rewrite In_fold_left_memory_eq, PSE.MP.Dec.F.add_iff, PSE.MP.Dec.F.empty_iff.
          split.
          * intros * Hin.
            unfold idck in Hin.
            apply in_map_iff in Hin as ((x', (c', ck')) & E & Hin); simpl in *; inv E.
            apply In_fst_fold_left_gather_eq in Hin as [Hin|Hin].
            -- inversion_clear Hin as [E|]; try contradiction; inv E.
               intuition.
               assert (InMembers x (n_vars n)) by auto.
               pose proof (n_nodup n) as Hnodup.
               rewrite fst_NoDupMembers, 2 map_app, NoDup_swap, <- 2 map_app, <-fst_NoDupMembers in Hnodup.
               eapply NoDupMembers_app_InMembers, NotInMembers_app in Hnodup as (? & ?); eauto.
               rewrite 2 idck_app, 2 in_app in Hinc; destruct Hinc as [Hinc|[|Hinc]]; auto;
                 apply In_InMembers in Hinc; rewrite InMembers_idck in Hinc; contradiction.
            -- assert (In (x, ck) (idck (fst (fold_left gather_eq l ((@nil (ident * (const * clock))), l0)))))
                 as Hin' by (apply in_map_iff; eexists; intuition; eauto; simpl; auto).
               apply IHl in Hin'; intuition.
          * intros * (Hin & [MemIn|MemIn]).
            -- assert (In (x, ck) (idck (fst (fold_left gather_eq l ((@nil (ident * (const * clock))), l0))))) as Hin'
                   by (apply IHl; auto; intros * Hin';
                       apply Spec; simpl; auto).
               unfold idck in Hin'; apply in_map_iff in Hin' as ((x', (c', ck')) & E & Hin'); simpl in *; inv E.
               apply in_map_iff; exists (x, (c', ck)); simpl.
               rewrite In_fst_fold_left_gather_eq; intuition.
            -- destruct MemIn as [E|]; try contradiction; inv E.
               apply in_map_iff; exists (x, (c0, c)); simpl.
               rewrite In_fst_fold_left_gather_eq; intuition.
               f_equal.
               assert (In (x, ck) (idck (n_in n ++ n_vars n ++ n_out n)))
                 by (rewrite 2 idck_app, 2 in_app; auto).
               eapply NoDupMembers_det; eauto.
               apply NoDupMembers_idck, n_nodup.
    Qed.

    Lemma wc_trconstrs_permutation_local:
      forall P vars vars' trs,
        Permutation vars vars' ->
        Forall (wc_trconstr P vars) trs ->
        Forall (wc_trconstr P vars') trs.
    Proof.
      intros * E WC.
      eapply Forall_impl with (2 := WC); eauto.
      setoid_rewrite E; auto.
    Qed.

    Lemma translate_eqn_wc_local:
      forall P vars eq,
        wc_env vars ->
        wc_equation P vars eq ->
        Forall (wc_trconstr (translate P) vars) (translate_eqn eq).
    Proof.
      intros P vars eq Henv Hwc.
      destruct eq as [x ck ce|xs ck f les orst|x ck c0 e].
      - inversion_clear Hwc. simpl.
        constructor.
        + constructor; auto.
        + constructor.
      - inversion_clear Hwc. simpl.
        destruct xs as [|x0 xs']; simpl; auto.
        apply find_node_translate in H as (? & ? & ? & ?); subst.
        destruct orst as [[r ckr]|].
        + constructor.
          * econstructor.
            { constructor.
              - apply wc_env_var with (x := r).
                + exact Henv.
                + eapply H2; reflexivity.
              - eapply H2; reflexivity. }
          * constructor.
            { econstructor; eauto. }
            { constructor. }
        + constructor.
          * econstructor; eauto.
          * constructor.
      - inversion_clear Hwc. simpl.
        constructor.
        + constructor; auto.
        + constructor.
    Qed.

    Lemma translate_eqns_wc_local:
      forall P vars eqs,
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        Forall (wc_trconstr (translate P) vars) (translate_eqns eqs).
    Proof.
      intros P vars eqs Henv Hwc.
      induction Hwc as [|eq eqs Hwc_eq Hwc_eqs IH]; simpl.
      - constructor.
      - apply Forall_app; split.
        + eapply translate_eqn_wc_local; eauto.
        + exact IH.
    Qed.

    Lemma translate_node_wc_local:
      forall G n,
        wc_node G n ->
        wc_system (translate G) (translate_node n).
    Proof.
      intros G n Hwc.
      destruct Hwc as (Henv_in & Henv_out & Henv_vars & Heqs).
      assert (E :
                Permutation
                  (idck (n_in n ++
                         snd
                           (partition
                              (fun x : ident * (type * clock) =>
                                 PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                              (n_vars n)) ++
                         n_out n) ++ idck (fst (gather_eqs (n_eqs n))))
                  (idck (n_in n ++ n_vars n ++ n_out n))).
      {
        repeat rewrite idck_app.
        rewrite Permutation_app_comm, Permutation_swap, gather_eqs_n_vars_wc_local,
          <-2 idck_app, app_assoc, <-permutation_partition, idck_app; eauto.
      }
      repeat split; simpl; auto.
      - now rewrite E.
      - apply Permutation_sym in E.
        eapply wc_trconstrs_permutation_local with (vars := idck (n_in n ++ n_vars n ++ n_out n)); eauto.
        clear - Heqs Henv_vars.
        induction Heqs as [|eq eqs Hwc_eq Hwc_eqs IH]; simpl.
        + constructor.
        + apply Forall_app; split.
          * eapply translate_eqn_wc_local; eauto.
          * exact IH.
    Qed.

    Lemma translate_wc_local:
      forall G,
        wc_global G ->
        wc_program (translate G).
    Proof.
      intros G Hwc.
      induction Hwc; simpl; auto.
      constructor; auto.
      eapply translate_node_wc_local; eauto.
    Qed.

    (** Scopedness of translated STC constraints from key lookups.

        This is the direct translation-layer wrapper around
        [SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys].  It keeps
        the NLustre-side hypotheses close by: well-clocked source equations
        produce well-clocked translated trconstrs under the same local variable
        environment. *)
    Lemma translated_eqns_constraints_scoped_on_keys:
      forall P (G2 : secglobal) vars scope eqs (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        (forall x ty st0 st1,
            In x (SECSTCTYPING.trconstrs_reset_keys (translate_eqns eqs)) ->
            find_env x rst_env st0 = OK (ty, st1) ->
            In ty scope) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns eqs) st
          = OK (cns, st') ->
        constraints_scoped scope cns.
    Proof.
      intros P G2 vars scope eqs env rst_env base_ty rst_ty cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hreset Hgen.
      eapply (SECSTCTYPING.generate_trconstrs_constraints_scoped_on_keys
                G2 env rst_env base_ty rst_ty
                (translate P) vars scope (translate_eqns eqs) cns st st'); eauto using translate_eqns_wc_local.
    Qed.

    (** Concrete scopedness corollary using [eqns_reset_extras].

        Once the private reset-instance names for an equation list have been
        reconstructed as [extras], every translated reset lookup lands inside
        that list.  The generated STC constraints are therefore scoped to the
        shared scope extended with exactly those extras. *)
    Lemma translated_eqns_constraints_scoped:
      forall P (G2 : secglobal) vars scope eqs (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) extras cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) eqs ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env eqs = Some extras ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns eqs) st
          = OK (cns, st') ->
        constraints_scoped (scope ++ extras) cns.
    Proof.
      intros P G2 vars scope eqs env rst_env base_ty rst_ty extras cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hextras Hgen.
      eapply (translated_eqns_constraints_scoped_on_keys
                P G2 vars (scope ++ extras) eqs env rst_env base_ty rst_ty cns st st').
      - exact Hscoped.
      - exact Henv.
      - exact Hwc.
      - intros x Hx.
        destruct (Hvars x Hx) as (ty & Hfind & Hscope).
        exists ty. split; [exact Hfind|].
        apply in_or_app. left. exact Hscope.
      - apply in_or_app. left. exact Hbase.
      - apply in_or_app. left. exact Hrst.
      - intros x ty st0 st1 Hin Hfind.
        apply in_app_iff. right.
        unfold find_env in Hfind.
        destruct (Env.find x rst_env) as [ty'|] eqn:Henvfind; try discriminate.
        inversion Hfind; subst ty' st1.
        eapply translated_reset_key_in_extras; eauto.
      - exact Hgen.
    Qed.

    (** Single-equation scopedness corollary.

        This is the one-step target scopedness fact used in the new scoped
        equation-list preservation proof: the translated STC block for one
        NLustre equation only mentions the shared scope plus the equation's own
        reset-instance extra (if any). *)
    Lemma translated_eqn_constraints_scoped:
      forall P (G2 : secglobal) vars scope e (env rst_env : Env.t ident)
             (base_ty rst_ty : ident) extras cns st st',
        secglobal_scoped G2 ->
        wc_env vars ->
        wc_equation P vars e ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqn_reset_extras rst_env e = Some extras ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqn e) st
          = OK (cns, st') ->
        constraints_scoped (scope ++ extras) cns.
    Proof.
      intros P G2 vars scope e env rst_env base_ty rst_ty extras cns st st'
             Hscoped Henv Hwc Hvars Hbase Hrst Hextra Hgen.
      destruct e; simpl in Hextra |- *; try discriminate.
      - eapply (translated_eqns_constraints_scoped
                  P G2 vars scope (EqDef i c c0 :: nil) env rst_env
                  base_ty rst_ty extras cns st st').
        + exact Hscoped.
        + exact Henv.
        + constructor; [exact Hwc|constructor].
        + exact Hvars.
        + exact Hbase.
        + exact Hrst.
        + simpl in Hextra. inversion Hextra; subst extras. reflexivity.
        + simpl. exact Hgen.
      - destruct l as [|x xs]; simpl in Hextra |- *.
        + inversion Hextra; subst extras.
          simpl in Hgen. inversion Hgen; subst cns st'.
          constructor.
        + eapply (translated_eqns_constraints_scoped
                    P G2 vars scope (EqApp (x :: xs) c i l0 o :: nil) env rst_env
                    base_ty rst_ty extras cns st st').
          * exact Hscoped.
          * exact Henv.
          * constructor; [exact Hwc|constructor].
          * exact Hvars.
          * exact Hbase.
          * exact Hrst.
          * simpl. rewrite Hextra, app_nil_r. reflexivity.
          * simpl. rewrite app_nil_r. exact Hgen.
      - eapply (translated_eqns_constraints_scoped
                  P G2 vars scope (EqFby i c c0 e :: nil) env rst_env
                  base_ty rst_ty extras cns st st').
        + exact Hscoped.
        + exact Henv.
        + constructor; [exact Hwc|constructor].
        + exact Hvars.
        + exact Hbase.
        + exact Hrst.
        + simpl in Hextra. inversion Hextra; subst extras. reflexivity.
        + simpl. exact Hgen.
    Qed.

    (** Small inversion tactic for the state/error monad used by the typing
        functions. *)
    Ltac myMonadInv :=
      simpl in *;
      try (unfold error in *);
      match goal with
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


    (** Single-equation preservation.

        The interesting cases are calls:

        - an ordinary call is discharged by the ordinary-call component of
          [Signature_consistent];
        - a resettable call is discharged by the reset-call component of
          [Signature_consistent], after aligning the fresh reset-instance name
          introduced on the STC side and recording that it lies outside the
          shared scope. *)
    Theorem eqn_preserv:
      forall scope P vars (G1 G2: secglobal)
             (e: equation) (trs: list trconstr)
             (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
           (nconst sconst: list constraint)
           (init_state1 init_state2 st1 st2: sec_state),
      Signature_consistent G1 G2 ->
      SIG.secglobal_scope_fresh scope G1 ->
      secglobal_scope_sec G2 ->
      wc_env vars ->
      wc_equation P vars e ->
      SECNLUSTYPING.vars_env_scoped env vars scope ->
      In base_ty scope ->
      In rst_ty scope ->
      translate_eqn e = trs ->
      (forall x rst_inst st1' st2',
          find_env x rst_env st1' = OK (rst_inst, st2') ->
          exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
      (forall x rst_inst st1' st2',
          find_env x rst_env st1' = OK (rst_inst, st2') ->
          ~ In rst_inst scope) ->
      generate_eqn_constraint G1 env base_ty rst_ty e init_state1 = OK (nconst, st1) ->
      generate_trconstrs_constraints G2 env rst_env base_ty rst_ty trs init_state2 = OK (sconst, st2) ->
      preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 e trs env rst_env base_ty rst_ty nconst sconst
             init_state1 init_state2 st1 st2
             Hsig Hscopefresh Hglobsec Henv Hwc Hvars Hbase Hrst Htr Hrstgen Hfresh Hnl Hstc.
      destruct e as [x ck cexp|xs ck f exps orst|x ck c0 exp].
      - simpl in Htr. subst trs. simpl in Hnl, Hstc.
        repeat myMonadInv.
        assert (Hck: x0 = x1).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hexp: x7 = x3).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hxty: x9 = x5).
        { eapply SC.find_env_consistent; eauto. }
        subst.
        unfold preserves_on. intros dlt Hsat.
        exists dlt. split.
        + apply agree_on_refl.
        + exact Hsat.
      - destruct xs as [|x xs].
        + simpl in Htr. subst trs. simpl in Hnl, Hstc.
          repeat myMonadInv.
          apply preserves_on_nil.
        + destruct orst as [[r ckr]|].
          * simpl in Htr. subst trs. simpl in Hnl, Hstc.
            inversion Hwc as [x' ck' ce' Hx Hce
                             |xs' ck' f' exps' r' n' sub Hfindnode Hinputs Houtputs Hreset
                             |x' ck' v le Hx Hle]; subst.
            destruct (SIG.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [_ Hresetcall]]]]].
            pose proof (Hscopefresh f snl Hfindnl) as Hsnlfresh.
            pose proof (scope_fresh_fields_agree scope snl sstc Hfields Hsnlfresh) as Hsstcfresh.
            pose proof (Hglobsec f sstc Hfindstc) as Hsstcsec.
            rewrite Hfindstc in Hstc.
            eapply sec_bind_inv in Hnl as (ckty_nl & st_ck_nl & Hck_nl & Hnl).
            eapply sec_bind_inv in Hnl as (rty_nl & st_r_nl & Hr_nl & Hnl).
            eapply sec_bind_inv in Hnl as (rstty_nl & st_rst_nl & Hrst_nl & Hnl).
            eapply sec_bind_inv in Hnl as (inptyp_nl & st_inp_nl & Hinp_nl & Hnl).
            eapply sec_bind_inv in Hnl as (outtyp_nl & st_out_nl & Hout_nl & Hcall_nl).
            eapply sec_bind_inv in Hstc as (reset_cns & st_mid & Hreset_blk & Hstc).
            eapply sec_bind_inv in Hstc as (call_cns & st_call2 & Hcall_blk & Hret_concat).
            unfold ret in Hret_concat. inversion Hret_concat; subst sconst st2.
            simpl in Hreset_blk.
              eapply sec_bind_inv in Hreset_blk as (rty_stc & st_r_stc & Hr_reset_stc & Hreset_blk).
              eapply sec_bind_inv in Hreset_blk as (rstty_stc & st_rstty_stc & Hrstty_reset_stc & Hreset_blk).
              eapply sec_bind_inv in Hreset_blk as (rst_inst_reset & st_rstinst_reset & Hrstinst_reset & Hret_reset).
              unfold ret in Hret_reset. inversion Hret_reset; subst reset_cns st_mid.
            simpl in Hcall_blk.
            eapply sec_bind_inv in Hcall_blk as (c_call & st_call1 & Hc_call & Hcall_blk).
            eapply sec_bind_inv in Hcall_blk as (c_nil_call & st_call3 & Hnil_call & Hret_call_blk).
            unfold ret in Hret_call_blk. inversion Hret_call_blk; subst call_cns st_call2.
            unfold ret in Hnil_call. inversion Hnil_call; subst c_nil_call st_call3.
            simpl in Hc_call.
            eapply sec_bind_inv in Hc_call as (ckty_stc & st_ck_stc & Hck_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (inptyp_stc & st_inp_stc & Hinp_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (outtyp_stc & st_out_stc & Hout_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (rst_inst_call & st_rstinst_call & Hrstinst_call & Hcall_stc).
            eapply sec_bind_inv in Hout_nl as (outhd_nl & st_outhd_nl & Houthd_nl & Hout_nl).
            eapply sec_bind_inv in Hout_nl as (outtl_nl & st_outtl_nl & Houttl_nl & Hret_out_nl).
            unfold ret in Hret_out_nl. inversion Hret_out_nl; subst outtyp_nl st_out_nl.
            eapply sec_bind_inv in Hout_stc as (outhd_stc & st_outhd_stc & Houthd_stc & Hout_stc).
            eapply sec_bind_inv in Hout_stc as (outtl_stc & st_outtl_stc & Houttl_stc & Hret_out_stc).
            unfold ret in Hret_out_stc. inversion Hret_out_stc; subst outtyp_stc st_out_stc.
            assert (Hck : ckty_nl = ckty_stc).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp : inptyp_nl = inptyp_stc).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthd : outhd_nl = outhd_stc).
            { eapply SC.find_env_consistent; eauto. }
            assert (Houttl : outtl_nl = outtl_stc).
            {
              eapply (@mmap_consistent ident ident
                        (fun x => SC.find_env x env)
                        (fun x => SC.find_env x env) xs); eauto.
              intros. eapply SC.find_env_consistent; eauto.
            }
              assert (Hrstinst : rst_inst_call = rst_inst_reset).
              { eapply SC.find_env_consistent; eauto. }
              assert (Hrty_reset : rty_nl = rty_stc).
              { eapply SC.find_env_consistent; eauto. }
              assert (Hrstty_reset : rstty_nl = rstty_stc).
              { eapply option_to_sec_consistent; eauto. }
              assert (Hckopt : assign_clk_type env base_ty ck = Some ckty_nl).
            { unfold option_to_sec in Hck_nl.
              destruct (assign_clk_type env base_ty ck) eqn:Hckopt; try discriminate.
              inversion Hck_nl; subst. reflexivity. }
            assert (Hrstopt : assign_clk_type env rst_ty ckr = Some rstty_nl).
            { unfold option_to_sec in Hrst_nl.
              destruct (assign_clk_type env rst_ty ckr) eqn:Hrstopt; try discriminate.
              inversion Hrst_nl; subst. reflexivity. }
            assert (Hckscope : st_scoped scope ckty_nl).
            { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := base_ty) (ck := ck); eauto.
              intros z Hz.
              destruct (Hvars z) as (ty & Hfind & Hscopez); eauto using SECNLUSTYPING.wc_call_clock_free_in_vars. }
            assert (Hrstscope : st_scoped scope ((rty_nl :: nil) ⊔ rstty_nl)).
            { assert (Hinr : In (r, ckr) vars).
              { eapply Hreset. reflexivity. }
              assert (Hwc_ckr : wc_clock vars ckr).
              { eapply wc_env_var; eauto. }
              eapply st_scoped_merge.
              { apply st_scoped_singleton.
                destruct (Hvars r (In_InMembers r ckr vars Hinr)) as (ty & Hfind & Hscope_r).
                unfold SC.find_env in Hr_nl.
                rewrite Hfind in Hr_nl. inversion Hr_nl; subst. exact Hscope_r. }
              { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := rst_ty) (ck := ckr); eauto.
                intros z Hz.
                destruct (Hvars z) as (ty & Hfind & Hscopez).
                { eapply SECNLUSTYPING.wc_clock_free_in_vars; eauto. }
                exists ty. split; assumption. } }
            assert (HinpScope : Forall (st_scoped scope) inptyp_nl).
            { eapply SECNLUSTYPING.mmap_assign_exp_type_scoped.
              - eapply SECNLUSTYPING.wc_call_args_scoped; eauto.
              - exact Hinp_nl. }
            assert (HoutScope : Forall (fun x => In x scope) (outhd_nl :: outtl_nl)).
            { constructor.
              - assert (HxIn : In x (x :: xs)) by (left; reflexivity).
                destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                            Hvars Houtputs x HxIn)
                  as [ty [Hfind Hinscope]].
                unfold SC.find_env in Houthd_nl.
                rewrite Hfind in Houthd_nl. inversion Houthd_nl; subst. exact Hinscope.
              - eapply (SC.mmap_find_env_scoped env).
                + intros y Hy.
                  destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                              Hvars Houtputs y (or_intror Hy)) as [ty [Hfind Hscopey]].
                  exists ty. split.
                  * exact Hfind.
                  * exact Hscopey.
                + exact Houttl_nl. }
            assert (Hfresh_nl :
                      call_subst_fresh snl inptyp_nl ckty_nl ((rty_nl :: nil) ⊔ rstty_nl) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
            subst ckty_stc inptyp_stc outhd_stc outtl_stc rst_inst_call.
            assert (Hrstinst_gensym : exists n, rst_inst_reset = Ids.gensym Ids.sec_reset n).
              { exact (Hrstgen x rst_inst_reset st_rstty_stc st_rstinst_reset Hrstinst_reset). }
            assert (Hfresh_stc :
                      call_subst_fresh sstc inptyp_nl ckty_nl (rst_inst_reset :: nil) (outhd_nl :: outtl_nl)).
              { exact (call_subst_fresh_reset_from_scope_fresh
                         scope sstc inptyp_nl ckty_nl rst_inst_reset (outhd_nl :: outtl_nl)
                         Hsstcfresh Hsstcsec HinpScope Hckscope Hrstinst_gensym HoutScope). }
              assert (Hnin : ~ In rst_inst_reset scope).
              { exact (Hfresh x rst_inst_reset st_rstty_stc st_rstinst_reset Hrstinst_reset). }
              set (srcrst_call :=
                                  ((fix merge' (c2 : SymTypes.ST) : SymTypes.ST :=
                                      match c2 with
                         | nil => rty_nl :: nil
                         | y :: ys =>
                             match (rty_nl ?= y)%positive with
                             | Eq =>
                                 rty_nl
                                 :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) ys
                             | Lt =>
                                 rty_nl
                                 :: (fix merge'0 (c0 : SymTypes.ST) : SymTypes.ST := c0) c2
                             | Gt => y :: merge' ys
                             end
                         end) rstty_nl)).
              assert (Hsrcrstscope_call : st_scoped scope srcrst_call).
              { unfold srcrst_call. change (st_scoped scope ((rty_nl :: nil) ⊔ rstty_nl)). exact Hrstscope. }
              change
                (generate_constraints snl inptyp_nl ckty_nl srcrst_call
                   (outhd_nl :: outtl_nl) st_outtl_nl = OK (nconst, st1))
                in Hcall_nl.
              repeat rewrite app_nil_r.
              cbn [app].
              subst rty_stc rstty_stc.
              eexact (Hresetcall scope inptyp_nl ckty_nl srcrst_call
                                  (outhd_nl :: outtl_nl)
                                  srcrst_call
                                  rst_inst_reset
                                  nconst c_call st_outtl_nl st_rstinst_call st1 st_call1
                                  Hsnlfresh
                                  (conj (conj HinpScope (conj Hckscope HoutScope)) Hsrcrstscope_call)
                                  ltac:(reflexivity)
                                  Hnin Hfresh_nl Hfresh_stc Hcall_nl Hcall_stc).
          * simpl in Htr. subst trs. simpl in Hnl, Hstc.
            inversion Hwc as [x' ck' ce' Hx Hce
                             |xs' ck' f' exps' r' n' sub Hfindnode Hinputs Houtputs Hreset
                             |x' ck' v le Hx Hle]; subst.
            destruct (SIG.find_signature f G1) as [snl|] eqn:Hfindnl.
            2: discriminate.
            unfold Signature_consistent, Signature_head_consistent, Signature_call_preserves in Hsig.
            destruct (Hsig f snl Hfindnl) as
              [sstc [Hfindstc [_ [Hfields [Hsimplecall _]]]]].
            pose proof (Hscopefresh f snl Hfindnl) as Hsnlfresh.
            pose proof (scope_fresh_fields_agree scope snl sstc Hfields Hsnlfresh) as Hsstcfresh.
            rewrite Hfindstc in Hstc.
            eapply sec_bind_inv in Hnl as (ckty_nl & st_ck_nl & Hck_nl & Hnl).
            eapply sec_bind_inv in Hnl as (inptyp_nl & st_inp_nl & Hinp_nl & Hnl).
            eapply sec_bind_inv in Hnl as (outtyp_nl & st_out_nl & Hout_nl & Hcall_nl).
            simpl in Hstc.
            eapply sec_bind_inv in Hstc as (c_call & st_call1 & Hc_call & Hstc).
            eapply sec_bind_inv in Hstc as (c_nil_call & st_call2 & Hnil_call & Hret_call_blk).
            unfold ret in Hret_call_blk. inversion Hret_call_blk; subst sconst st2.
            unfold ret in Hnil_call. inversion Hnil_call; subst c_nil_call st_call2.
            simpl in Hc_call.
            eapply sec_bind_inv in Hc_call as (ckty_stc & st_ck_stc & Hck_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (inptyp_stc & st_inp_stc & Hinp_stc & Hc_call).
            eapply sec_bind_inv in Hc_call as (outtyp_stc & st_out_stc & Hout_stc & Hcall_stc).
            eapply sec_bind_inv in Hout_nl as (outhd_nl & st_outhd_nl & Houthd_nl & Hout_nl).
            eapply sec_bind_inv in Hout_nl as (outtl_nl & st_outtl_nl & Houttl_nl & Hret_out_nl).
            unfold ret in Hret_out_nl. inversion Hret_out_nl; subst outtyp_nl st_out_nl.
            eapply sec_bind_inv in Hout_stc as (outhd_stc & st_outhd_stc & Houthd_stc & Hout_stc).
            eapply sec_bind_inv in Hout_stc as (outtl_stc & st_outtl_stc & Houttl_stc & Hret_out_stc).
            unfold ret in Hret_out_stc. inversion Hret_out_stc; subst outtyp_stc st_out_stc.
            assert (Hck : ckty_nl = ckty_stc).
            { eapply option_to_sec_consistent; eauto. }
            assert (Hinptyp : inptyp_nl = inptyp_stc).
            { eapply mmap_option_to_sec_consistent; eauto. }
            assert (Houthd : outhd_nl = outhd_stc).
            { eapply SC.find_env_consistent; eauto. }
            assert (Houttl : outtl_nl = outtl_stc).
            {
              eapply (@mmap_consistent ident ident
                        (fun x => SC.find_env x env)
                        (fun x => SC.find_env x env) xs); eauto.
              intros. eapply SC.find_env_consistent; eauto.
            }
            assert (Hckopt : assign_clk_type env base_ty ck = Some ckty_nl).
            { unfold option_to_sec in Hck_nl.
              destruct (assign_clk_type env base_ty ck) eqn:Hckopt; try discriminate.
              inversion Hck_nl; subst. reflexivity. }
            assert (Hckscope : st_scoped scope ckty_nl).
            { eapply SECNLUSTYPING.assign_clk_type_scoped with (base := base_ty) (ck := ck); eauto.
              intros z Hz.
              destruct (Hvars z) as (ty & Hfind & Hscopez); eauto using SECNLUSTYPING.wc_call_clock_free_in_vars. }
            assert (Hrstsingle : st_scoped scope (rst_ty :: nil)).
            { apply st_scoped_singleton; exact Hrst. }
            assert (HinpScope : Forall (st_scoped scope) inptyp_nl).
            { eapply SECNLUSTYPING.mmap_assign_exp_type_scoped.
              - eapply SECNLUSTYPING.wc_call_args_scoped; eauto.
              - exact Hinp_nl. }
            assert (HoutScope : Forall (fun x => In x scope) (outhd_nl :: outtl_nl)).
            { constructor.
              - assert (HxIn : In x (x :: xs)) by (left; reflexivity).
                destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                            Hvars Houtputs x HxIn)
                  as [ty [Hfind Hinscope]].
                unfold SC.find_env in Houthd_nl.
                rewrite Hfind in Houthd_nl. inversion Houthd_nl; subst. exact Hinscope.
              - eapply (SC.mmap_find_env_scoped env).
                + intros y Hy.
                  destruct (SECNLUSTYPING.wc_call_outs_scoped env vars scope sub ck (n_out n') (x :: xs)
                              Hvars Houtputs y (or_intror Hy)) as [ty [Hfind Hscopey]].
                  exists ty. split.
                  * exact Hfind.
                  * exact Hscopey.
                + exact Houttl_nl. }
            assert (Hfresh_nl :
                      call_subst_fresh snl inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
            subst ckty_stc inptyp_stc outhd_stc outtl_stc.
            assert (Hfresh_stc :
                      call_subst_fresh sstc inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)).
            { eapply call_subst_fresh_from_scope_fresh; eauto. }
              repeat rewrite app_nil_r.
              cbn [app].
              eexact (Hsimplecall scope inptyp_nl ckty_nl (rst_ty :: nil) (outhd_nl :: outtl_nl)
                                   nconst c_call st_outtl_nl st_outtl_stc st1 st_call1
                                   Hsnlfresh
                                   (conj (conj HinpScope (conj Hckscope HoutScope)) Hrstsingle)
                                   Hfresh_nl Hfresh_stc Hcall_nl Hcall_stc).
      - simpl in Htr. subst trs. simpl in Hnl, Hstc.
        repeat myMonadInv.
        assert (Hck: x0 = x1).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hexp: x7 = x3).
        { eapply option_to_sec_consistent; eauto. }
        assert (Hxty: x9 = x5).
        { eapply SC.find_env_consistent; eauto. }
        subst.
        unfold preserves_on. intros dlt Hsat.
        exists dlt. split.
        + apply agree_on_refl.
        + exact Hsat.
    Qed.

    Lemma eqns_preserv_scoped_nil:
      forall scope P vars (G1 G2: secglobal)
             extras (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
             (nconst sconst: list constraint)
             (init_state1 init_state2 st1 st2: sec_state),
        Signature_consistent G1 G2 ->
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) nil ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env nil = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1' st2',
            find_env x rst_env st1' = OK (rst_inst, st2') ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env base_ty rst_ty nil init_state1 = OK (nconst, st1) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns nil) init_state2
          = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 extras env rst_env base_ty rst_ty nconst sconst
             init_state1 init_state2 st1 st2
             Hsig Hscoped Henv Hwc Hvars Hbase Hrst Hextras Hnd Hfresh Hnl Hstc.
      dependent destruction Hwc.
      simpl in Hextras, Hnl, Hstc.
      inversion Hextras; subst.
      unfold ret in Hnl, Hstc.
      destruct nconst as [|cn nconst']; try discriminate.
      destruct sconst as [|cs sconst']; try discriminate.
      inversion Hnl; inversion Hstc; subst.
      exact (preserves_on_nil scope).
    Qed.

    (** Scoped equation-list preservation.

        In addition to one-step preservation, this theorem tracks the concrete
        STC-only reset-instance extras produced by the translation and
        composes head/tail blocks with [preserves_on_concat_scoped]. *)
    Lemma eqns_preserv_scoped:
      forall scope P vars (G1 G2: secglobal) (es: list equation) extras
             (env rst_env: Env.t ident)
             (base_ty rst_ty: ident)
             (nconst sconst: list constraint)
             (init_state1 init_state2 st1 st2: sec_state),
        Signature_consistent G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        wc_env vars ->
        Forall (wc_equation P vars) es ->
        SECSTCTYPING.vars_env_scoped env vars scope ->
        In base_ty scope ->
        In rst_ty scope ->
        eqns_reset_extras rst_env es = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1' st2',
            find_env x rst_env st1' = OK (rst_inst, st2') ->
            exists n, rst_inst = Ids.gensym Ids.sec_reset n) ->
        (forall x rst_inst st1' st2',
            find_env x rst_env st1' = OK (rst_inst, st2') ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env base_ty rst_ty es init_state1 = OK (nconst, st1) ->
        generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqns es) init_state2
          = OK (sconst, st2) ->
        preserves_on scope nconst sconst.
    Proof.
      intros scope P vars G1 G2 es.
      induction es as [|e es IH]; intros extras env rst_env base_ty rst_ty nconst sconst
                                      init_state1 init_state2 st1 st2
                                      Hsig Hscopefresh Hglobsec Hscoped Henv Hwc Hvars Hbase Hrst
                                      Hextras Hnd Hrstgen Hfresh Hnl Hstc.
      - eapply (eqns_preserv_scoped_nil
                  scope P vars G1 G2 extras env rst_env base_ty rst_ty
                  nconst sconst init_state1 init_state2 st1 st2);eauto.

      - inversion Hwc as [|eq eqs Hwc_e Hwc_es]; subst eq eqs.
        simpl in Hextras.
        destruct (eqn_reset_extras rst_env e) as [extras1|] eqn:Hextra1;
          try discriminate.
        destruct (eqns_reset_extras rst_env es) as [extras2|] eqn:Hextra2;
          try discriminate.
        inversion Hextras; subst extras.
        simpl in Hnl.
        repeat myMonadInv.
        eapply generate_tr_constraints_inv in Hstc.
        destruct Hstc as (sconst1 & st_mid & sconst2 & [Hstc1 [Hstc2 Hsconst]]).
        rewrite Hsconst.
        eapply preserves_on_concat_scoped with (extras1 := extras1) (extras2 := extras2).
        + exact Hnd.
        + intros ty0 Hin.
          eapply (eqns_reset_extras_fresh
                    rst_env (e :: es) (extras1 ++ extras2) scope).
          * simpl. rewrite Hextra1, Hextra2. reflexivity.
          * exact Hfresh.
          * exact Hin.
        + eapply (translated_eqn_constraints_scoped
                    P G2 vars scope e env rst_env base_ty rst_ty
                    extras1 sconst1 init_state2 st_mid); eauto.

        + eapply (translated_eqns_constraints_scoped
                    P G2 vars scope es env rst_env base_ty rst_ty
                    extras2 sconst2 st_mid st2); eauto.
        + match goal with
          | Hnl1 : generate_eqn_constraint G1 env base_ty rst_ty e init_state1 = OK (_, _),
            Hstc1' : generate_trconstrs_constraints G2 env rst_env base_ty rst_ty (translate_eqn e) init_state2 = OK (_, _) |- _ =>
              eapply (eqn_preserv scope P vars G1 G2 e (translate_eqn e) env rst_env base_ty rst_ty
                                  _ _ init_state1 init_state2 _ _)
          end; eauto.
        + eapply (IH extras2 env rst_env base_ty rst_ty x1 sconst2
                     x0 st_mid st1 st2); eauto using NoDup_app_r.
    Qed.

  End SECEQNPRES.

  (** The node/system part of the development is organised in five layers:

      1. [node_preserv_scoped] is the core theorem. It works for one
         already-aligned
         node/system pair and assumes the relevant environment lookups plus the
         freshness of STC reset-instance variables.
      2. The freshness and inversion lemmas below are used only to discharge
         those assumptions when the environments and signatures come from the
         generators in [NameInterface], [SecNLusTyping], and [SecSTCTyping].
      3. [generated_node_preserv_scoped] packages that discharge for generated
         signatures, and [found_system_preserv_scoped_global] is the
         lookup-based global corollary obtained from [find_system_translate].
      4. The bridge layer reconstructs per-node
         [Signature_head_consistent] from two explicit lattice-mapping ingredients:
         simplification completeness for generated signatures, and call-time
         preservation derived from [signatures_preserved].
      5. [Signature_consistent_cons] and the generated-signature induction then
         lift that local compatibility relation to entire generated signature
         lists.
      6. [generated_node_preserv_global] and
         [generated_program_preserv_global] use that global consistency result
         to remove the explicit [Signature_consistent] premise from the final
         node/system theorems. *)
  Section NODESYSPRES.
    Local Notation sig_scope := signature_scope.

    (** The lemmas in this block are only used to discharge the freshness side
        conditions of the generated-node theorems. They establish that ordinary
        security variables come from the [sec] namespace, while reset-instance
        variables come from the disjoint [sec_reset] namespace. *)
    Ltac myNameInv :=
      simpl in *;
      match goal with
      | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
      | H: Error _ = OK _ |- _ =>
        discriminate
      | H: NMret _ _ = _ |- _ =>
        unfold NMret in H
      | H: NMbind ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply name_bind_inv in H as [? [? [H1 H2]]]
      | H: NMbind2 ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply name_bind2_inv in H as [? [? [? [H1 H2]]]]
      end; simpl in *.

    Ltac mySecInv :=
      simpl in *;
      match goal with
      | H: OK _ = OK _ |- _ =>
        inversion H; clear H; try subst
      | H: Error _ = OK _ |- _ =>
        discriminate
      | H: ret _ _ = _ |- _ =>
        unfold ret in H
      | H: bind ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply sec_bind_inv in H as [? [? [H1 H2]]]
      | H: bind2 ?x ?f ?st = OK ?res |- _ =>
        let H1 := fresh "Hbind" in
        let H2 := fresh "Hbind" in
        eapply sec_bind2_inv in H as [? [? [? [H1 H2]]]]
      end; simpl in *.

    Lemma fresh_insert_preserves_find:
      forall env k st env' st' x ty,
        fresh_insert env k st = OK (env', st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros env k st env' st' x ty Hins Hfind.
      unfold fresh_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply name_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_ident_gen in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, NMret in Hins0. inversion Hins0; subst e st2.
      unfold NMret in Hret. inversion Hret; subst env' st'.
      assert (Hxk : x <> k).
      { intro Heq. subst x.
        assert (Env.mem k env = true).
        { apply Env.mem_1. unfold Env.In. eexists; exact Hfind. }
        congruence. }
      now rewrite Env.gso.
    Qed.

    Lemma generate_new_names_for_node_preserves_find:
      forall n env st env' aux st' x ty,
        generate_new_names_for_node n env st = OK ((env', aux), st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      intros n env st env' aux st' x ty Hgen Hfind.
      unfold generate_new_names_for_node in Hgen.
      eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
      eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
      eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hret).
      unfold NMret in Hret. inversion Hret; subst env' aux st'.
      eapply NAMEGEN.fresh_map_list_preserves_find; eauto.
    Qed.

    Lemma generate_node_env'_preserves_find:
      forall ns env acc st env' aux st' x ty,
        generate_node_env' ns env acc st = OK ((env', aux), st') ->
        Env.find x env = Some ty ->
        Env.find x env' = Some ty.
    Proof.
      induction ns as [|n ns IH]; intros env acc st env' aux st' x ty Hgen Hfind.
      - simpl in Hgen. inversion Hgen; subst. exact Hfind.
      - simpl in Hgen.
        eapply name_bind2_inv in Hgen as (env1 & r & st1 & Hstep & Hgen).
        eapply name_bind2_inv in Hgen as (env2 & rs & st2 & Hrec & Hret).
        unfold NMret in Hret. inversion Hret; subst env' aux st'.
        eapply IH; eauto.
        eapply generate_new_names_for_node_preserves_find; eauto.
    Qed.

    Lemma fresh_insert_sec_range:
      forall env k st env' st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec n) ->
        fresh_insert env k st = OK (env', st') ->
        Env.find x env' = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n.
    Proof.
      intros env k st env' st' x ty Henv Hins Hfind.
      unfold fresh_insert in Hins.
      destruct (Env.mem k env) eqn:Hmem; try discriminate.
      eapply name_bind_inv in Hins as (v & st1 & Hfresh & Hins).
      eapply name_bind_inv in Hins as (e & st2 & Hins0 & Hret).
      unfold fresh_ident_gen in Hfresh.
      inversion Hfresh; subst v st1.
      unfold insert_env, NMret in Hins0.
      inversion Hins0; subst e st2.
      unfold NMret in Hret. inversion Hret. subst env' st'.
      destruct (Pos.eq_dec x k) as [Heq|Hneq].
      - subst. rewrite Env.gss in Hfind. inversion Hfind. subst.
        eexists; reflexivity.
      - rewrite Env.gso in Hfind; eauto.
    Qed.

    Lemma fresh_map_list_sec_range:
      forall ks env st env' st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists n, ty' = Ids.gensym Ids.sec n) ->
        fresh_map_list ks env st = OK (env', st') ->
        Env.find x env' = Some ty ->
        exists n, ty = Ids.gensym Ids.sec n.
    Proof.
      induction ks as [|k ks IH]; intros env st env' st' x ty Henv Hmap Hfind.
      - simpl in Hmap. inversion Hmap; subst. eauto.
      - simpl in Hmap.
        repeat myNameInv.
        eapply IH; [|eauto|eauto].
        intros y ty' Hy.
        eapply fresh_insert_sec_range; eauto.
    Qed.

    Lemma generate_new_names_for_node_sec_range:
      forall n env st env' aux st' x ty,
        (forall y ty', Env.find y env = Some ty' -> exists m, ty' = Ids.gensym Ids.sec m) ->
        generate_new_names_for_node n env st = OK ((env', aux), st') ->
        Env.find x env' = Some ty ->
        exists m, ty = Ids.gensym Ids.sec m.
    Proof.
      intros n env st env' aux st' x ty Henv Hgen Hfind.
      unfold generate_new_names_for_node in Hgen.
      eapply name_bind_inv in Hgen as (clk_name & st1 & Hclk & Hgen).
      eapply name_bind_inv in Hgen as (rst_name & st2 & Hrst & Hgen).
      eapply name_bind_inv in Hgen as (env0 & st3 & Hmap & Hret).
      unfold fresh_ident_gen in Hclk. inversion Hclk; subst clk_name st1.
      unfold fresh_ident_gen in Hrst. inversion Hrst; subst rst_name st2.
      unfold NMret in Hret. inversion Hret. subst env' aux st'.
      eapply fresh_map_list_sec_range; eauto.
    Qed.

    Lemma generated_reset_env_maps_reset_calls:
      forall eqs reset_env rids st' x,
        generate_reset_env (translate_eqns eqs) init_state = OK ((reset_env, rids), st') ->
        In x (reset_call_vars eqs) ->
        exists ty, Env.find x reset_env = Some ty.
    Proof.
      intros eqs reset_env rids st' x Hgen Hin.
      destruct (reset_call_vars_translate_eqns _ _ Hin) as (ck & f & Hinreset).
      eapply SECSTCTYPINGCORRECTNESS.generate_reset_env_has_reset_stmt; eauto.
    Qed.

    Lemma generated_eqns_reset_extras:
      forall eqs reset_env rids st',
        NoDup (vars_defined eqs) ->
        generate_reset_env (translate_eqns eqs) init_state = OK ((reset_env, rids), st') ->
        exists tys,
          eqns_reset_extras reset_env eqs = Some tys
          /\ NoDup tys.
    Proof.
      intros eqs reset_env rids st' Hnodup Hgen.
      destruct (eqns_reset_extras_exists reset_env eqs) as [tys Hextras].
      {
        intros x Hin.
        eapply generated_reset_env_maps_reset_calls; eauto.
      }
      exists tys. split; [exact Hextras|].
      eapply eqns_reset_extras_nodup; eauto.
      - eapply reset_call_vars_nodup; eauto.
      - intros x y tx ty Hfindx Hfindy Heq.
        eapply SECSTCTYPINGCORRECTNESS.generate_reset_env_injective; eauto.
    Qed.

    (** Scoped node theorem.

        This theorem packages [eqns_preserv_scoped] at node level, so it keeps
        the concrete structural side conditions that justify scoped
        concatenation:

        - local NLustre clocking for the node equations;
        - scoped target signatures in [G2];
        - the exact reset-instance extras produced by the translated STC side.
     *)
    Theorem node_preserv_scoped:
      forall P (n : node) (s: system) scope
             (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             clk_id rst_id clk_type rst_type
             inp out locals
             reset_env rids extras
             nconst sconst
             st_reset st_n st_s,
        translate_node n = s ->
        Signature_consistent G1 G2 ->
        SIG.secglobal_scope_fresh scope G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        get_node_aux (n.(n_name)) aux_names = Some (clk_id, rst_id) ->
        Env.find clk_id env = Some clk_type ->
        Env.find rst_id env = Some rst_type ->
        get_mappings_from_node (n.(n_in)) env = Some inp ->
        get_mappings_from_node (n.(n_out)) env = Some out ->
        get_mappings_from_node (n.(n_vars)) env = Some locals ->
        scope = inp ++ out ++ locals ++ (clk_type :: rst_type :: nil) ->
        generate_reset_env s.(SynStc.s_tcs) init_state = OK ((reset_env, rids), st_reset) ->
        eqns_reset_extras reset_env n.(n_eqs) = Some extras ->
        NoDup extras ->
        (forall x rst_inst st1 st2,
            find_env x reset_env st1 = OK (rst_inst, st2) ->
            ~ In rst_inst scope) ->
        generate_eqns_constraints G1 env clk_type rst_type n.(n_eqs) init_state = OK (nconst, st_n) ->
        generate_trconstrs_constraints G2 env reset_env clk_type rst_type s.(SynStc.s_tcs) st_reset = OK (sconst, st_s) ->
        preserves_on scope nconst sconst.
    Proof.
      intros P n s scope G1 G2 env aux_names clk_id rst_id clk_type rst_type
             inp out locals reset_env rids extras nconst sconst st_reset st_n st_s
             Htr Hsig Hscopefresh Hglobsec Hscoped Hwc Haux Hclk Hrst Hinp Hout Hlocals Hscope
             Hresetenv Hextras Hnd Hfresh Hnl Hstc.
      subst scope.
      subst s. simpl in Hresetenv, Hstc.
      destruct Hwc as [_ [_ [Hwcenv Hwc]]].
      eapply (eqns_preserv_scoped
                (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                P (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out)))
                G1 G2 n.(n_eqs) extras env reset_env clk_type rst_type
                nconst sconst init_state st_reset st_n st_s).
      - exact Hsig.
      - exact Hscopefresh.
      - exact Hglobsec.
      - exact Hscoped.
      - exact Hwcenv.
      - exact Hwc.
      - eapply SECNLUSTYPINGCORRECTNESS.node_vars_env_scoped_from_mappings; eauto.
      - repeat rewrite in_app_iff. right. right. right. left. reflexivity.
      - repeat rewrite in_app_iff. right. right. right. right. left. reflexivity.
      - exact Hextras.
      - exact Hnd.
      - intros x0 rst_inst st1 st2 Hfind.
        unfold find_env in Hfind.
        destruct (Env.find x0 reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
        inversion Hfind; subst rst_inst st2.
        eapply generate_reset_env_range; eauto.
      - exact Hfresh.
      - exact Hnl.
      - exact Hstc.
    Qed.

    (** The next two inversion lemmas package the operational content of the
        generated NLustre/STC signatures. They let the node/system theorem talk
        directly in terms of the underlying constraint generators, rather than
        repeatedly unfolding the large monadic definitions. *)

    (** Visible-field provenance for generated STC signatures.

        This is the target-local counterpart of
        [SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_key].  Visible identifiers of a generated STC
        signature come from the shared environment image of the system's
        inputs/outputs and the per-node clock/reset keys, never from STC-only
        hidden state. *)
    (** Namespace corollaries for generated visible signatures.

        Together with the naming-layer fact that every shared-environment value
        produced by [generate_node_env] lies in the [sec] namespace, the two
        provenance lemmas above imply that every visible identifier stored in a
        generated source/target signature also lies in that same namespace. *)
    (** Target-local namespace fact under one node-local env generation.

        This remains in the translation layer because it is phrased over the
        translated current node [translate_node n], not an arbitrary STC
        system. *)
    Lemma generated_sys_signature_scope_sec_from_local_env:
      forall G n env aux_names rec st st' sig,
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        SECSTCTYPING.generate_sys_signature G (translate_node n) env aux_names = OK sig ->
        signature_scope_sec sig.
    Proof.
      intros G n env aux_names rec st st' sig Hlocal Hsig ty Hin.
      destruct (SECSTCTYPINGCORRECTNESS.generated_sys_signature_scope_key _ _ _ _ _ _ Hsig Hin)
        as (_ & _ & x & _ & _ & Hfind).
      eapply NAMEGEN.generate_local_env_for_node_sec_range in Hfind; eauto.
    Qed.

    (** Target-local namespace fact under one node-local env generation.

        This is the node-scoped counterpart of
        [generated_sys_signature_scope_sec]: once the current node's local
        security env has been generated, every visible identifier in the
        resulting STC signature lies in the [sec] namespace. *)
    (** Scoped generated-node theorem.

        This is the generated counterpart of [node_preserv_scoped].  It
        exposes the concrete local prerequisites used by the scoped
        concatenation proof:

        - local source clocking for [n];
        - scoped target signatures in [G2].

        This theorem is the generated bridge from node-level scoped
        preservation to the later global corollaries. *)
    Theorem generated_node_preserv_scoped:
      forall P all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros P all_nodes n G1 G2 env aux_names nsig ssig
             Hsig Hscopefreshenv Hglobsec Hscoped Hwc Henvgen Hnsig Hssig.
      edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & nlocals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hnlocals & Hnconst & Hnsigdef); eauto.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Haux in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      rewrite Hnsigdef in *.
      rewrite Hssigdef in *.
      pose proof (Hscopefreshenv
                    clk_id rst_id clk_type rst_type inp out nlocals
                    Haux Hclk Hrst Hinp Hout Hnlocals)
        as Hscopefresh.
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
      exists nlocals, slocals, slasts, rids, nconst, sconst.
      split.
      - repeat split; reflexivity.
      - split; [reflexivity|].
        split; [reflexivity|].
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfind Hin.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfind; clear Hfind; subst.
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (scope := inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)
               (G1 := G1) (G2 := G2)
               (s := translate_node n)
               (env := env) (reset_env := reset_env)
               (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (clk_type := clk_type) (rst_type := rst_type)
               (inp := inp) (out := out) (locals := nlocals)
               (rids := rids) (extras := extras)
               (nconst := nconst) (sconst := sconst);
          eauto.
    Qed.

    (** Node-scoped generated-node theorem.

        This is the same local generated bridge as
        [generated_node_preserv_scoped], but phrased over the new
        node-scoped naming layer.  The proof projects the current node's local
        env from the outer node-indexed table and reuses the raw node theorem
        on that recovered local env. *)
    Theorem generated_node_preserv_scoped_scoped_env:
      forall P all_nodes (n : node) (G1 G2: secglobal)
             (envs: node_scoped_env) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        (forall env,
            find_node_env n.(n_name) envs = Some env ->
            SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n env aux_names G1) ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        SECNLUSTYPING.generate_node_sig_scoped_env G1 n envs aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature_scoped_env G2 (translate_node n) envs aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros P all_nodes n G1 G2 envs aux_names nsig ssig
             Hsig Hfreshenv Hglobsec Hscoped Hwc Henvsgen Hfindnode Hnsig Hssig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
      destruct (find_node_env n.(n_name) envs) as [env|] eqn:Hfindenv; try discriminate.
      simpl in Hssig.
      rewrite Hfindenv in Hssig.
      edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & nlocals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hnlocals & Hnconst & Hnsigdef); eauto.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Haux in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      rewrite Hnsigdef in *.
      rewrite Hssigdef in *.
      assert (Hsameenv : Some env = Some env) by reflexivity.
      specialize (Hfreshenv env Hsameenv).
      pose proof (find_node_In _ _ _ Hfindnode) as [_ Hinall].
      apply in_split in Hinall as (prefix & suffix & Hall).
      subst all_nodes.
      edestruct NAMEGEN.generate_node_scoped_env_find_current
        as (local_env & rec & st_pref & st_local & Hlocalgen & Hlocalfind);
        eauto.
      rewrite Hfindenv in Hlocalfind. inversion Hlocalfind. subst local_env.
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
      exists nlocals, slocals, slasts, rids, nconst, sconst.
      split.
      - repeat split; reflexivity.
      - split; [reflexivity|].
        split; [reflexivity|].
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfind Hin.
          unfold find_env in Hfind.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfind; clear Hfind; subst.
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          repeat rewrite in_app_iff in Hin.
          destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hinp Hin)
              as (xinp & ainp & _ & Hfindinp).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xinp rst_inst
                         Hlocalgen Hfindinp) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hout Hin)
              as (xout & aout & _ & Hfindout).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xout rst_inst
                         Hlocalgen Hfindout) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - destruct (get_mappings_from_node_In _ _ _ _ _ Hnlocals Hin)
              as (xlocal & alocal & _ & Hfindlocal).
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local xlocal rst_inst
                         Hlocalgen Hfindlocal) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - subst rst_inst.
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local clk_id clk_type
                         Hlocalgen Hclk) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
          - subst rst_inst.
            edestruct (NAMEGEN.generate_local_env_for_node_sec_range
                         n st_pref env rec st_local rst_id rst_type
                         Hlocalgen Hrst) as (nsec & Hscopeeq).
            rewrite Hrsteq in Hscopeeq.
            apply gensym_injective in Hscopeeq as [Hpref _].
            symmetry in Hpref.
            exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (scope := inp ++ out ++ nlocals ++ clk_type :: rst_type :: nil)
               (G1 := G1) (G2 := G2)
               (s := translate_node n)
               (env := env) (reset_env := reset_env)
               (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (clk_type := clk_type) (rst_type := rst_type)
               (inp := inp) (out := out) (locals := nlocals)
               (rids := rids) (extras := extras)
               (nconst := nconst) (sconst := sconst);
          eauto.
    Qed.

    (** Generated-node corollary under standard source-side well-formedness.

        This packages [generated_node_preserv_scoped] with the standard
        NLustre ordering/clocking facts needed to recover the local [wc_node]
        hypothesis. *)
    Corollary generated_node_preserv_scoped_global:
      forall all_nodes (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        SECNLUSTYPINGCORRECTNESS.generated_callers_scope_fresh all_nodes env aux_names G1 ->
        CloNL.wc_global all_nodes ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        find_node n.(n_name) all_nodes = Some n ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes n G1 G2 env aux_names nsig ssig
             Hsig Hfreshgen Hwcg Hglobsec Hscoped Henvgen Hfind Hnsig Hssig.
      edestruct (CloNL.wc_find_node all_nodes n.(n_name) n Hwcg Hfind)
        as (G'' & G' & _ & Hwc).
      eapply generated_node_preserv_scoped with (P := G'); eauto.
    Qed.

    (** Lookup corollary.

        This is the lookup-based version of
        [generated_node_preserv_scoped_global]. *)
    Corollary found_system_preserv_scoped_global:
      forall all_nodes f n s prog' (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        SECNLUSTYPINGCORRECTNESS.generated_callers_scope_fresh all_nodes env aux_names G1 ->
        CloNL.wc_global all_nodes ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        find_node f all_nodes = Some n ->
        SynStc.find_system f (translate all_nodes) = Some (s, prog') ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 s env aux_names = OK ssig ->
        exists nlocals slocals slasts rids nconst sconst,
          signature_fields_agree nsig ssig
          /\ nsig.(s_constraints) = SymTypes.simplify nconst nlocals
          /\ ssig.(s_constraints) = SymTypes.simplify sconst (SECSTCTYPING.hidden_sys_vars slocals slasts rids)
          /\ preserves_on (nsig.(s_in) ++ nsig.(s_out) ++ nlocals ++ nsig.(s_clk) :: nsig.(s_reset) :: nil)
                          nconst sconst.
    Proof.
      intros all_nodes f n s prog' G1 G2 env aux_names nsig ssig
             Hsig Hfreshgen Hwcg Hglobsec Hscoped Henvgen Hfind Hsys Hnsig Hssig.
      eapply find_system_translate in Hsys as (n' & Hfind' & Htr).
      rewrite Hfind in Hfind'. inversion Hfind'. subst n'. subst s.
      pose proof (find_node_name _ _ _ Hfind) as Hname.
      subst f.
      eapply generated_node_preserv_scoped_global; eauto.
    Qed.


    (** Simplify bridge for generated signatures.

        This theorem combines the generated node preservation result with the
        source-side simplify completeness theorem and the target-side simplify
        soundness theorem. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_scoped:
      forall all_nodes P (n : node) (G1 G2: secglobal)
             (env: Env.t ident) (aux_names: list node_aux_names)
             (nsig ssig: signature),
        Signature_consistent G1 G2 ->
        SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        CloNL.wc_node P n ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready env aux_names ->
        signatures_preserved nsig ssig.
    Proof.
      intros all_nodes P n G1 G2 env aux_names nsig ssig
             Hcons Hscopefreshenv Hglobsec Hscoped Henvgen Hwc Hnsig Hssig Hready.
      edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Haux in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      destruct (Hready G1 n nsig
                  clk_id rst_id clk_type rst_type inp out locals nconst st_n
                  Hnsig Haux Hclk Hrst Hinp Hout Hlocals Hnconst Hnsigdef)
        as [Hwf Hdisj].
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
      assert (Hrawpres :
                preserves_on
                  (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                  nconst sconst).
      {
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfindrst Hin.
          unfold find_env in Hfindrst.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfindrst; clear Hfindrst; subst.
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          edestruct SECNLUSTYPINGCORRECTNESS.node_scope_sec_range as (nsec & Hscopeeq); eauto.
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (s := translate_node n)
               (G1 := G1) (G2 := G2)
               (env := env) (aux_names := aux_names)
               (clk_id := clk_id) (rst_id := rst_id)
               (inp := inp) (out := out) (locals := locals)
               (reset_env := reset_env) (rids := rids) (extras := extras)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s).
        - reflexivity.
        - exact Hcons.
        - eapply Hscopefreshenv; eauto.
        - exact Hglobsec.
        - exact Hscoped.
        - exact Hwc.
        - exact Haux.
        - exact Hclk.
        - exact Hrst.
        - exact Hinp.
        - exact Hout.
        - exact Hlocals.
        - reflexivity.
        - exact Hresetenv.
        - exact Hextras.
        - exact Hnd.
        - exact Hfresh.
        - exact Hnconst.
        - exact Hsconst.
      }
      subst nsig ssig.
      unfold signatures_preserved.
      split.
      - repeat split; reflexivity.
      - unfold preserves_on.
        intros dlt Hsat.
        destruct (SecTypes.simplify_complete
                    nconst locals
                    (inp ++ out ++ clk_type :: rst_type :: nil)
                    dlt
                    Hwf
                    Hdisj
                    Hsat)
          as (dlt_raw & Hagree & Hsat_raw).
        destruct (Hrawpres dlt_raw Hsat_raw) as (dlt_stc & Hagree_stc & Hsat_stc).
        exists dlt_stc. split.
        + intros x Hin.
          pose proof (SIGPROOFS.sig_scope_in_raw_scope
                        {| s_name := n.(n_name);
                           s_in := inp;
                           s_out := out;
                           s_reset := rst_type;
                           s_clk := clk_type;
                           s_constraints := SymTypes.simplify nconst locals |}
                        locals x Hin) as Hinraw.
          transitivity (dlt_raw x).
          * apply Hagree. exact Hin.
          * apply Hagree_stc.
            exact Hinraw.
        + eapply simplify_is_correct.
          * exact Hsat_stc.
          * eapply simplify_simplifyRel. reflexivity.
    Qed.

    (** Local simplify bridge under one node-scoped env generation.

        This is the node-scoped counterpart of
        [generated_signatures_preserved_from_simplify_bridge_scoped].  It
        avoids the old flat generated-env prerequisite and instead reasons from
        the one caller node's locally generated security env. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_local_env:
      forall P G1 G2 n env aux_names rec st st' nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n env aux_names G1 ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        generate_local_env_for_node n st = OK ((env, rec), st') ->
        get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst)) ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        signatures_preserved nsig ssig.
    Proof.
      intros P G1 G2 n env aux_names rec st st' nsig ssig
             Hcons Hscopefreshenv Hglobsec Hscoped Hwc Hlocal Hauxrec Hnsig Hssig.
      edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts
           & Hresetenv & Hsconst & Hssigdef); eauto.
      simpl in Haux', Hinp', Hout', Hslocals, Hslasts, Hresetenv, Hsconst, Hssigdef.
      rewrite Hauxrec in Haux. inversion Haux. subst clk_id rst_id.
      rewrite Hauxrec in Haux'. inversion Haux'. subst clk_id' rst_id'.
      rewrite Hclk in Hclk'. inversion Hclk'. subst clk_type'.
      rewrite Hrst in Hrst'. inversion Hrst'. subst rst_type'.
      rewrite Hinp in Hinp'. inversion Hinp'. subst inp'.
      rewrite Hout in Hout'. inversion Hout'. subst out'.
      pose proof (Hscopefreshenv
                    rec.(nclk) rec.(nrst) clk_type rst_type inp out locals
                    Hauxrec Hclk Hrst Hinp Hout Hlocals)
        as Hscopefresh.
      destruct (generated_eqns_reset_extras _ _ _ _ (NoDup_var_defined_n_eqs n) Hresetenv)
        as [extras [Hextras Hnd]].
      assert (Hrawpres :
                preserves_on
                  (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)
                  nconst sconst).
      {
        assert (Hfresh:
                  forall x rst_inst st1 st2,
                    find_env x reset_env st1 = OK (rst_inst, st2) ->
                    ~ In rst_inst (inp ++ out ++ locals ++ clk_type :: rst_type :: nil)).
        {
          intros x rst_inst st1 st2 Hfindrst Hin.
          unfold find_env in Hfindrst.
          destruct (Env.find x reset_env) as [rst_inst'|] eqn:Hrstfind; try discriminate.
          inversion Hfindrst; clear Hfindrst; subst.
          edestruct generate_reset_env_range as (nrst_idx & Hrsteq); eauto.
          destruct
            (SECNLUSTYPINGCORRECTNESS.local_node_scope_sec_range
               n st env rec st'
               rec.(nclk) rec.(nrst) clk_type rst_type inp out locals rst_inst
               Hlocal Hclk Hrst Hinp Hout Hlocals Hin)
            as (nsec & Hscopeeq).
          rewrite Hrsteq in Hscopeeq.
          apply gensym_injective in Hscopeeq as [Hpref _].
          symmetry in Hpref.
          exact (Ids.sec_neq_sec_reset Hpref).
        }
        eapply node_preserv_scoped
          with (P := P)
               (s := translate_node n)
               (G1 := G1) (G2 := G2)
               (env := env) (aux_names := aux_names)
               (clk_id := rec.(nclk)) (rst_id := rec.(nrst))
               (inp := inp) (out := out) (locals := locals)
               (reset_env := reset_env) (rids := rids)
               (nconst := nconst) (sconst := sconst)
               (st_reset := st_reset) (st_n := st_n) (st_s := st_s); eauto.
      }
      rewrite Hnsigdef, Hssigdef.
      unfold signatures_preserved.
      split.
      - repeat split; reflexivity.
      - assert (Hnsig_local :
                  SECNLUSTYPING.generate_node_sig G1 n env aux_names =
                  OK
                    {| s_name := n.(n_name);
                       s_in := inp;
                       s_out := out;
                       s_reset := rst_type;
                       s_clk := clk_type;
                       s_constraints := SymTypes.simplify nconst locals |}).
        {
          rewrite <- Hnsigdef.
          exact Hnsig.
        }
        assert (Hclk_local : Env.find rec.(nclk) env = Some clk_type) by exact Hclk.
        assert (Hrst_local : Env.find rec.(nrst) env = Some rst_type) by exact Hrst.
        destruct (SECNLUSTYPINGCORRECTNESS.generated_node_simplify_ready_from_local_env
                    G1 n
                    {| s_name := n.(n_name);
                       s_in := inp;
                       s_out := out;
                       s_reset := rst_type;
                       s_clk := clk_type;
                       s_constraints := SymTypes.simplify nconst locals |}
                    env rec aux_names st st' clk_type rst_type inp out locals nconst st_n
                    Hlocal Hnsig_local Hclk_local Hrst_local Hinp Hout Hlocals Hnconst
                    ltac:(reflexivity))
          as [Hwf Hdisj].
        intros dlt Hsat.
        destruct (SecTypes.simplify_complete
                    nconst locals
                    (inp ++ out ++ clk_type :: rst_type :: nil)
                    dlt
                    Hwf
                    Hdisj
                    Hsat)
          as (dlt_raw & Hagree & Hsat_raw).
        destruct (Hrawpres dlt_raw Hsat_raw) as (dlt_stc & Hagree_stc & Hsat_stc).
        exists dlt_stc. split.
        + intros x Hin.
          pose proof (SIGPROOFS.sig_scope_in_raw_scope
                        {| s_name := n.(n_name);
                           s_in := inp;
                           s_out := out;
                           s_reset := rst_type;
                           s_clk := clk_type;
                           s_constraints := SymTypes.simplify nconst locals |}
                        locals x Hin) as Hinraw.
          transitivity (dlt_raw x).
          * apply Hagree. exact Hin.
          * apply Hagree_stc. exact Hinraw.
        + eapply simplify_is_correct.
          * exact Hsat_stc.
          * eapply simplify_simplifyRel. reflexivity.
    Qed.

    (** Scoped-env head-step simplify bridge.

        This is the generated-prefix counterpart of
        [generated_signatures_preserved_from_simplify_bridge_local_env].  The
        source accumulator carries only the structural bound that all already
        generated visible identifiers lie below the current naming state [st].
        The current caller node is then recovered from the node-scoped env run,
        and [SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env_from_bounds] turns that bound into the
        exact local call-freshness fact consumed by the bridge. *)
    Theorem generated_signatures_preserved_from_simplify_bridge_scoped_env:
      forall prefix P G1 G2 n envs aux_names
             envs_pref aux_pref st nsig ssig,
        NAMEGEN.generate_node_scoped_env' prefix (Env.empty _) nil NAMEGEN.init_state
          = OK ((envs_pref, aux_pref), st) ->
        generate_node_scoped_env (prefix ++ n :: P) = OK (envs, aux_names) ->
        Signature_consistent G1 G2 ->
        SIG.secglobal_scope_bounded_above G1 st ->
        secglobal_scope_sec G2 ->
        secglobal_scoped G2 ->
        CloNL.wc_node P n ->
        SECNLUSTYPING.generate_node_sig_scoped_env G1 n envs aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature_scoped_env G2 (translate_node n) envs aux_names = OK ssig ->
        signatures_preserved nsig ssig.
    Proof.
      intros prefix P G1 G2 n envs aux_names
             envs_pref aux_pref st nsig ssig
             Hprefgen Henvsgen Hcons Hbound Hglobsec Hscoped Hwc Hnsig Hssig.
      unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
      unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
      destruct (find_node_env n.(n_name) envs) as [env|] eqn:Hfindenv; try discriminate.
      assert (Hfindenv_sys : find_node_env (translate_node n).(SynStc.s_name) envs = Some env).
      { simpl. exact Hfindenv. }
      rewrite Hfindenv_sys in Hssig.
      unfold generate_node_scoped_env in Henvsgen.
      destruct (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: P) (Env.empty _) nil NAMEGEN.init_state)
        as [[[envs' aux'] st']|] eqn:Hrun; try discriminate.
      inversion Henvsgen; subst envs' aux'; clear Henvsgen.
      edestruct NAMEGEN.generate_node_scoped_env'_split_node
        as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
            & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
        eauto.
      rewrite Hprefgen in Hpref. inversion Hpref; subst envs_pref' aux_pref' st_pref.
      assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
        eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
      {
        eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
        - pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
          unfold get_node_aux. simpl. rewrite <- Hrecname, ident_eqb_refl. reflexivity.
        - eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
      }
      rewrite Hfindenv in Hfindlocal. inversion Hfindlocal. subst local_env.
      eapply generated_signatures_preserved_from_simplify_bridge_local_env
        with (P := P) (rec := rec) (st := st) (st' := st_local); eauto.
      eapply SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env_from_bounds; eauto.
    Qed.

      Theorem signatures_preserved_simple_calls_from_good:
        forall nsig ssig,
          signature_good nsig ->
          NoDup (sig_scope nsig) ->
          signature_scoped ssig ->
          signatures_preserved nsig ssig ->
          forall scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2,
            scope_fresh scope nsig ->
            call_subst_scoped scope inptyp ckty rstty outtyp ->
            call_subst_fresh nsig inptyp ckty rstty outtyp ->
            call_subst_fresh ssig inptyp ckty rstty outtyp ->
            generate_constraints nsig inptyp ckty rstty outtyp st_init1 = OK (nconst, st1) ->
            generate_constraints ssig inptyp ckty rstty outtyp st_init2 = OK (sconst, st2) ->
            preserves_on scope nconst sconst.
      Proof.
        intros nsig ssig Hgood Hndscope Hssigscoped [Hfields Hpres]
               scope inptyp ckty rstty outtyp nconst sconst st_init1 st_init2 st1 st2
               Hscopefresh Hcallscoped Hfresh_nsig Hfresh_ssig Hgen_nsig Hgen_ssig.
        unfold preserves_on.
        intros dlt Hsat_nconst.
        pose proof Hgen_nsig as Hgen_nsig_len.
        unfold generate_constraints in Hgen_nsig_len.
        eapply sec_bind_inv in Hgen_nsig_len as (c1 & st1' & HinpSub & Hgen_nsig_len).
        eapply sec_bind_inv in Hgen_nsig_len as (c2 & st2' & HclkSub & Hgen_nsig_len).
        eapply sec_bind_inv in Hgen_nsig_len as (c3 & st3' & HrstSub & Hgen_nsig_len).
        eapply sec_bind_inv in Hgen_nsig_len as (c4 & st4' & HoutSub & Hreorder).
        pose proof (SIGPROOFS.subst_constraints_inp_map_length _ _ _ _ _ _ HinpSub) as HlenIn.
        pose proof (SIGPROOFS.subst_constraints_out_map_length _ _ _ _ _ _ HoutSub) as HlenOut.
        assert (Hinfresh_pairs :
                  Forall2 (fun x ty => ~ In x ty) nsig.(s_in) inptyp).
        {
          eapply SIGPROOFS.call_subst_fresh_inputs_notin_pairs; eauto.
        }
        destruct Hfresh_nsig as [Hinfresh [Hclkfresh [Hrstfresh Houtfresh]]].
        assert (Hfresh_nsig_all : call_subst_fresh nsig inptyp ckty rstty outtyp).
        { repeat split; assumption. }
        assert (Hclknotin : ~ In nsig.(s_clk) ckty).
        {
          eapply SIGPROOFS.type_fresh_notin_sig_scope; eauto.
          unfold sig_scope. apply in_or_app. right.
          apply in_or_app. right. simpl. now left.
        }
        assert (Hrstnotin : ~ In nsig.(s_reset) rstty).
        {
          eapply SIGPROOFS.type_fresh_notin_sig_scope; eauto.
          unfold sig_scope. apply in_or_app. right.
          apply in_or_app. right. simpl. now right; left.
        }
        pose proof
          (SIGPROOFS.generate_constraints_complete_good
             nsig inptyp ckty rstty outtyp nconst st_init1 st1
             Hgood Hgen_nsig dlt Hsat_nconst
             Hinfresh_pairs Hclknotin Hrstnotin)
          as Hsat_nsig.
        destruct (Hpres _ Hsat_nsig)
          as (dlt_mid & Hagree_mid & Hsat_ssig).
        set (dlt_ov := overlay_scope scope dlt dlt_mid).
        assert (Hscopefresh_ssig : scope_fresh scope ssig).
        { eapply scope_fresh_fields_agree; eauto. }
        assert (Hndscope_ssig : NoDup (sig_scope ssig)).
        { rewrite <- (signature_fields_agree_scope_eq _ _ Hfields). exact Hndscope. }
        assert (Hinst_agree :
                  agree_on (sig_scope ssig)
                           (SIGPROOFS.inst_valuation dlt nsig inptyp ckty rstty outtyp)
                           (SIGPROOFS.inst_valuation dlt_ov ssig inptyp ckty rstty outtyp)).
        {
          eapply SIGPROOFS.inst_valuation_fields_agree_on_sig_scope.
          - exact Hfields.
          - exact Hndscope.
          - exact Hscopefresh.
          - exact Hcallscoped.
          - exact Hfresh_nsig_all.
          - apply overlay_scope_agree_on.
          - exact HlenIn.
          - exact HlenOut.
        }
        assert (Hmid_src :
                  agree_on (sig_scope ssig)
                           dlt_mid
                           (SIGPROOFS.inst_valuation dlt nsig inptyp ckty rstty outtyp)).
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
                           (SIGPROOFS.inst_valuation dlt_ov ssig inptyp ckty rstty outtyp)).
        {
          eapply agree_on_trans; eauto.
        }
        assert (Hsat_ssig_inst :
                  listSatisfiable
                    (SIGPROOFS.inst_valuation dlt_ov ssig inptyp ckty rstty outtyp)
                    ssig.(s_constraints)).
        {
          eapply listSatisfiable_ext; eauto.
        }
        assert (Hsat_sconst :
                  listSatisfiable
                    (SIGPROOFS.inst_valuation dlt_ov ssig inptyp ckty rstty outtyp)
                    sconst).
        {
          eapply SIGPROOFS.generate_constraints_correct_inst; eauto.
        }
        exists (SIGPROOFS.inst_valuation dlt_ov ssig inptyp ckty rstty outtyp).
        split.
        - eapply agree_on_trans.
          + apply overlay_scope_agree_on.
          + eapply SIGPROOFS.inst_valuation_agree_on_scope; eauto.
        - exact Hsat_sconst.
      Qed.

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
        pose proof (SIGPROOFS.subst_constraints_inp_map_length _ _ _ _ _ _ HinpSub) as HlenIn.
        pose proof (SIGPROOFS.subst_constraints_out_map_length _ _ _ _ _ _ HoutSub) as HlenOut.
        assert (Hinfresh_pairs :
                  Forall2 (fun x ty => ~ In x ty) nsig.(s_in) inptyp).
        {
          eapply SIGPROOFS.call_subst_fresh_inputs_notin_pairs; eauto.
        }
        destruct Hfresh_nsig as [Hinfresh [Hclkfresh [Hrstfresh Houtfresh]]].
        assert (Hfresh_nsig_all : call_subst_fresh nsig inptyp ckty srcrst outtyp).
        { repeat split; assumption. }
        assert (Hclknotin : ~ In nsig.(s_clk) ckty).
        {
          eapply SIGPROOFS.type_fresh_notin_sig_scope; eauto.
          unfold sig_scope. apply in_or_app. right.
          apply in_or_app. right. simpl. now left.
        }
        assert (Hrstnotin : ~ In nsig.(s_reset) srcrst).
        {
          eapply SIGPROOFS.type_fresh_notin_sig_scope; eauto.
          unfold sig_scope. apply in_or_app. right.
          apply in_or_app. right. simpl. now right; left.
        }
        pose proof
          (SIGPROOFS.generate_constraints_complete_good
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
                           (SIGPROOFS.inst_valuation dlt nsig inptyp ckty srcrst outtyp)
                           (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
        {
          eapply SIGPROOFS.inst_valuation_fields_agree_on_sig_scope_reset; eauto.
        }
        assert (Hmid_src :
                  agree_on (sig_scope ssig)
                           dlt_mid
                           (SIGPROOFS.inst_valuation dlt nsig inptyp ckty srcrst outtyp)).
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
                           (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
        {
          eapply agree_on_trans; eauto.
        }
        assert (Hsat_ssig_inst :
                  listSatisfiable
                    (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                    ssig.(s_constraints)).
        {
          eapply listSatisfiable_ext; eauto.
        }
        assert (Hsat_sconst :
                  listSatisfiable
                    (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                    sconst).
        {
          eapply SIGPROOFS.generate_constraints_correct_inst; eauto.
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
                           (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)).
        {
          eapply agree_on_trans.
          + exact Hagree_rst_scope.
          + eapply SIGPROOFS.inst_valuation_agree_on_scope; eauto.
        }
        assert (Hagree_scope_final_sym :
                  agree_on scope
                    (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                    dlt).
        {
          intros x Hin.
          symmetry.
          apply Hagree_scope_final.
          exact Hin.
        }
        assert (Hsat_reset :
                  constraintSatisfiable
                    (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                    (srcrst, [rst_inst])).
        {
          unfold constraintSatisfiable, satisfiable.
          rewrite (hm_ext_agree_on_scoped_type
                     scope srcrst
                     (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp)
                     dlt
                     Hsrcrstscope
                     Hagree_scope_final_sym).
          simpl.
          rewrite SIGPROOFS.inst_valuation_outside_sig_scope by exact Hrstinst_notin_sig.
          rewrite Hrstinst_eq.
          apply join_bound1.
        }
        exists (SIGPROOFS.inst_valuation dlt_rst ssig inptyp ckty (rst_inst :: nil) outtyp).
        split.
        - intros x Hin.
          transitivity (dlt_rst x).
          + exact (Hagree_rst_scope x Hin).
          + symmetry.
            apply SIGPROOFS.inst_valuation_outside_sig_scope.
            exact (Hscopefresh_ssig x Hin).
        - constructor; [exact Hsat_reset|exact Hsat_sconst].
      Qed.

      Theorem signatures_preserved_reset_calls_from_good:
        forall nsig ssig,
          signature_good nsig ->
          NoDup (sig_scope nsig) ->
          signature_scoped nsig ->
          signature_scoped ssig ->
          signatures_preserved nsig ssig ->
          forall scope inptyp ckty srcrst outtyp reset_lhs rst_inst
                 nconst sconst st_init1 st_init2 st1 st2,
            scope_fresh scope nsig ->
            call_subst_scoped scope inptyp ckty srcrst outtyp ->
            reset_lhs = srcrst ->
            ~ In rst_inst scope ->
            call_subst_fresh nsig inptyp ckty srcrst outtyp ->
            call_subst_fresh ssig inptyp ckty (rst_inst :: nil) outtyp ->
            generate_constraints nsig inptyp ckty srcrst outtyp st_init1 = OK (nconst, st1) ->
            generate_constraints ssig inptyp ckty (rst_inst :: nil) outtyp st_init2 = OK (sconst, st2) ->
            preserves_on scope nconst ((reset_lhs, (rst_inst :: nil)) :: sconst).
      Proof.
        intros nsig ssig Hgood Hndscope Hnsigscoped Hssigscoped Hpres
               scope inptyp ckty srcrst outtyp reset_lhs rst_inst
               nconst sconst st_init1 st_init2 st1 st2
               Hscopefresh Hcallscoped Hlhs Hnin Hfresh_nsig Hfresh_ssig Hgen_nsig Hgen_ssig.
        subst reset_lhs.
        eexact
          (signatures_preserved_reset_underlying_calls_from_good
             nsig ssig Hgood Hndscope Hssigscoped Hpres
             scope inptyp ckty srcrst outtyp rst_inst
             nconst sconst st_init1 st_init2 st1 st2
             Hscopefresh Hcallscoped Hnin Hfresh_nsig Hfresh_ssig
             Hgen_nsig Hgen_ssig).
      Qed.

      (** The remaining gap to a fully proved signature-step theorem is not in
        the global induction; it is in the lattice-mapping bridge from generated raw
        node/system constraints to the simplified modular signatures used at
        call sites.

        The two obligations below isolate that gap exactly:

        - [signatures_preserved] must be derivable for generated signatures,
          typically from [generated_node_preserv_scoped] plus a completeness result
          for [SymTypes.simplify];
        - [Signature_call_preserves] must follow from
          [signatures_preserved], via a lattice-mapping correctness theorem for
          [generate_constraints] under consistent fresh-name instantiations.

        Once these two bridge lemmas are available, the abstract
        [generated_signature_step_consistent] hypothesis used by the global
        theorems is no longer needed. *)

    (** Abstract per-generated-node bridge.

        This packages the one-step compatibility obligation needed by the later
        list-of-signatures induction: if a node and its translated system are
        generated from already consistent accumulators, then the fresh source
        and target signatures are themselves [Signature_head_consistent]. *)
    Definition generated_signature_step_consistent
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall acc1 acc2 n nsig ssig,
        Signature_consistent acc1 acc2 ->
        SECNLUSTYPING.generate_node_sig acc1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names = OK ssig ->
        Signature_head_consistent nsig ssig.

    Lemma generated_signature_name_agree:
      forall G1 G2 n env aux_names nsig ssig,
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        nsig.(s_name) = ssig.(s_name).
    Proof.
      intros G1 G2 n env aux_names nsig ssig Hnsig Hssig.
      edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
          (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
           & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef); eauto.
      edestruct SECSTCTYPINGCORRECTNESS.generate_sys_signature_inv as
          (clk_id' & rst_id' & clk_type' & rst_type' & inp' & out' & slocals & slasts
           & reset_env & rids & st_reset & sconst & st_s
           & Haux' & Hclk' & Hrst' & Hinp' & Hout' & Hslocals & Hslasts & Hresetenv & Hsconst & Hssigdef); eauto.
      rewrite Hnsigdef, Hssigdef. reflexivity.
    Qed.

    Theorem generated_signature_step_consistent_from_bridges:
      forall all_nodes env aux_names,
        generate_node_env all_nodes = OK (env, aux_names) ->
        (forall G1 G2 n nsig ssig,
            Signature_consistent G1 G2 ->
            SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
            SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
            signatures_preserved nsig ssig) ->
        (forall G1 G2 n nsig ssig,
            SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
            SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
            signatures_preserved nsig ssig ->
            Signature_call_preserves nsig ssig) ->
        generated_signature_step_consistent env aux_names.
    Proof.
      intros all_nodes env aux_names Henvgen Hsigpres Hcall.
      unfold generated_signature_step_consistent.
      intros G1 G2 n nsig ssig Hcons Hnsig Hssig.
      split.
      - eapply generated_signature_name_agree; eauto.
      - destruct (Hsigpres G1 G2 n nsig ssig Hcons Hnsig Hssig) as [Hfields Hpres].
        split; [exact Hfields|].
        eapply Hcall; eauto.
    Qed.

    (** Concrete bridge premises.

        The abstract step theorem above only needs generated-signature
        preservation plus the internal call-instantiation bridges proved above.
        The final public theorem stack below no longer assumes either
        [signatures_preserved_calls] or [signatures_preserved_reset_calls]. *)
    Definition generated_signatures_preserved
      (env: Env.t ident) (aux_names: list node_aux_names) : Prop :=
      forall G1 G2 n nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        signatures_preserved nsig ssig.

    (** Global-signature extension.

        Once the new NLustre/STC signatures for one processed node are known to
        satisfy [Signature_head_consistent], adding them to already-consistent
        accumulators preserves global [Signature_consistent]. This is the basic
        step needed for the induction over [generate_all_signatures'] and
        [generate_all_sys_signatures']. *)
    Lemma Signature_consistent_nil:
      Signature_consistent nil nil.
    Proof.
      intros f n1 Hfind.
      simpl in Hfind. discriminate.
    Qed.

    Theorem Signature_consistent_cons:
      forall G1 G2 nsig ssig,
        Signature_consistent G1 G2 ->
        Signature_head_consistent nsig ssig ->
        Signature_consistent (nsig :: G1) (ssig :: G2).
    Proof.
      intros G1 G2 nsig ssig Hcons Hhead f n1 Hfind.
      simpl in Hfind.
      destruct (ident_eqb nsig.(s_name) f) eqn:Hname.
      - destruct Hhead as [Hsgname Hhead].
        apply ident_eqb_eq in Hname. inversion Hfind; subst n1.
        exists ssig. simpl. rewrite <- Hsgname, Hname, ident_eqb_refl.
        split; [reflexivity|].
        split; [exact Hsgname|exact Hhead].
      - apply ident_eqb_neq in Hname.
        destruct Hhead as [Hsgname Hhead].
        specialize (Hcons f n1 Hfind) as (n2 & Hfind2 & Hhead2).
        assert (Hssigname : ssig.(s_name) <> f).
        { rewrite <- Hsgname. exact Hname. }
        assert (Hneqb : ident_eqb ssig.(s_name) f = false).
        { apply ident_eqb_neq. exact Hssigname. }
        exists n2. simpl. rewrite Hneqb. auto.
    Qed.

    Corollary generate_all_translated_system_signatures_scoped:
      forall all_nodes env aux_names G,
        CloStc.wc_program (translate all_nodes) ->
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G ->
        secglobal_scoped G.
    Proof.
      intros all_nodes env aux_names G Hwc Henvgen Hgen.
      eapply SECSTCTYPING.generate_all_sys_signatures_scoped; eauto.
      eapply NAMEGEN.generate_node_env_injective; eauto.
    Qed.

    Corollary generate_all_translated_system_signatures_scope_sec:
      forall all_nodes env aux_names G,
        generate_node_env all_nodes = OK (env, aux_names) ->
        SECSTCTYPING.generate_all_sys_signatures (translate all_nodes) env aux_names = OK G ->
        secglobal_scope_sec G.
    Proof.
      intros all_nodes env aux_names G Henvgen.
      unfold SECSTCTYPING.generate_all_sys_signatures.
      assert (Haccsec:
                forall todo acc G',
                  secglobal_scope_sec acc ->
                  SECSTCTYPING.generate_all_sys_signatures' acc (translate todo) env aux_names = OK G' ->
                  secglobal_scope_sec G').
      {
        intros todo.
        induction todo as [|n todo IHtodo]; intros acc G' Haccsec Hgen'.
        - simpl in Hgen'. inversion Hgen'; subst. exact Haccsec.
        - simpl in Hgen'.
          destruct (SECSTCTYPING.generate_sys_signature acc (translate_node n) env aux_names) as [sig'|e] eqn:Hsig';
            simpl in Hgen'; try discriminate.
          destruct (SECSTCTYPING.generate_all_sys_signatures' (sig' :: acc) (translate todo) env aux_names) as [G''|e] eqn:Htl';
            simpl in Hgen'; try discriminate.
          inversion Hgen'; subst. eapply IHtodo.
          + eapply secglobal_scope_sec_cons; eauto.
            eapply SECSTCTYPINGCORRECTNESS.generated_sys_signature_scope_sec; eauto.
          + exact Htl'.
      }
      intro Hgen.
      eapply Haccsec; eauto.
      apply secglobal_scope_sec_nil.
    Qed.

    (** This is the generated-signature form of [Signature_consistent_cons].
        The generation equalities make the statement line up with the
        accumulator step of the global generators: once one generated
        source/target pair satisfies [Signature_head_consistent], the global
        invariant extends immediately. *)
    Theorem generated_signature_consistent_step:
      forall G1 G2 n env aux_names nsig ssig,
        Signature_consistent G1 G2 ->
        SECNLUSTYPING.generate_node_sig G1 n env aux_names = OK nsig ->
        SECSTCTYPING.generate_sys_signature G2 (translate_node n) env aux_names = OK ssig ->
        Signature_head_consistent nsig ssig ->
        Signature_consistent (nsig :: G1) (ssig :: G2).
    Proof.
      intros. eapply Signature_consistent_cons; eauto.
    Qed.

    (** Per-step compatibility hypothesis used by the global generators.

        This isolates the one-node bridge from the accumulator induction:
        if one freshly generated node/system signature pair satisfies
        [Signature_head_consistent], then the list induction lifts that fact to
        the whole generated global signature lists. *)
    Theorem generate_all_signatures_consistent'_abstract:
      forall nodes acc1 acc2 env aux_names G1 G2,
        Signature_consistent acc1 acc2 ->
        generated_signature_step_consistent env aux_names ->
        SECNLUSTYPING.generate_all_signatures' acc1 nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures' acc2 (translate nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      induction nodes as [|n nodes IH]; intros acc1 acc2 env aux_names G1 G2
                                            Hcons Hstep Hnl Hstc.
      - simpl in Hnl, Hstc. inversion Hnl; inversion Hstc; subst. exact Hcons.
      - simpl in Hnl, Hstc.
        destruct (SECNLUSTYPING.generate_node_sig acc1 n env aux_names) as [nsig|] eqn:Hnsig;
          try discriminate.
        destruct (SECSTCTYPING.generate_sys_signature acc2 (translate_node n) env aux_names) as [ssig|] eqn:Hssig;
          simpl in Hnl, Hstc; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures' (nsig :: acc1) nodes env aux_names) as [G1'|] eqn:Hnl';
          simpl in Hnl; try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures' (ssig :: acc2) (translate nodes) env aux_names) as [G2'|] eqn:Hstc';
          simpl in Hstc; try discriminate.
        inversion Hnl; subst; clear Hnl.
        inversion Hstc; subst; clear Hstc.
        eapply IH with (acc1 := nsig :: acc1) (acc2 := ssig :: acc2); eauto.
        + eapply generated_signature_consistent_step; eauto.
    Qed.

    Corollary generate_all_signatures_consistent_abstract:
      forall nodes env aux_names G1 G2,
        generated_signature_step_consistent env aux_names ->
        SECNLUSTYPING.generate_all_signatures nodes env aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures (translate nodes) env aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros nodes env aux_names G1 G2 Hstep Hnl Hstc.
      unfold SECNLUSTYPING.generate_all_signatures in Hnl.
      unfold SECSTCTYPING.generate_all_sys_signatures in Hstc.
      eapply generate_all_signatures_consistent'_abstract
        with (acc1 := @nil signature) (acc2 := @nil signature); eauto.
      apply Signature_consistent_nil.
    Qed.

    (** Concrete global-signature theorem.

        This proof performs the accumulator induction directly and uses the
        scoped simplify bridge for the current head node, together with the
        current scopedness and call-preservation hypotheses. *)
    Theorem generate_all_signatures_consistent_scoped':
      forall prefix nodes acc1 acc2 envs aux_names
             envs_pref aux_pref st G1 G2,
        NAMEGEN.generate_node_scoped_env' prefix (Env.empty _) nil NAMEGEN.init_state
          = OK ((envs_pref, aux_pref), st) ->
        generate_node_scoped_env (prefix ++ nodes) = OK (envs, aux_names) ->
        CloNL.wc_global nodes ->
        Signature_consistent acc1 acc2 ->
        secglobal_scoped acc1 ->
        secglobal_scoped acc2 ->
        secglobal_scope_sec acc2 ->
        SIG.secglobal_scope_bounded_above acc1 st ->
        SECNLUSTYPING.generate_all_signatures_scoped_env' acc1 nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env' acc2 (translate nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2 /\ secglobal_scoped G2 /\ secglobal_scope_sec G2.
    Proof.
      intros prefix nodes.
      revert prefix.
      induction nodes as [|n nodes IH];
        intros prefix acc1 acc2 envs aux_names envs_pref aux_pref st G1 G2
               Hprefgen Henvsgen Hwc Hcons Hacc1scoped Hacc2scoped
               Hacc2sec Hbound Hnl Hstc.
      - simpl in Hnl, Hstc. inversion Hnl; inversion Hstc; subst.
        repeat split; assumption.
      - inversion Hwc as [|n' ns Hwc_tail Hwc_head]; subst n' ns.
        simpl in Hnl, Hstc.
        destruct (SECNLUSTYPING.generate_node_sig_scoped_env acc1 n envs aux_names)
          as [nsig|] eqn:Hnsig; try discriminate.
        destruct (SECSTCTYPING.generate_sys_signature_scoped_env acc2 (translate_node n) envs aux_names)
          as [ssig|] eqn:Hssig; simpl in Hnl, Hstc; try discriminate.
        destruct (SECNLUSTYPING.generate_all_signatures_scoped_env' (nsig :: acc1) nodes envs aux_names)
          as [G1'|] eqn:Hnl'; simpl in Hnl; try discriminate.
        destruct (SECSTCTYPING.generate_all_sys_signatures_scoped_env' (ssig :: acc2) (translate nodes) envs aux_names)
          as [G2'|] eqn:Hstc'; simpl in Hstc; try discriminate.
        inversion Hnl; subst G1'. clear Hnl.
        inversion Hstc; subst G2'. clear Hstc.
        pose proof Henvsgen as Henvsgen_full.
        unfold generate_node_scoped_env in Henvsgen_full.
        destruct (NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nodes) (Env.empty _) nil NAMEGEN.init_state)
          as [[[envs_full aux_full] st_full]|] eqn:Hrun; try discriminate.
        inversion Henvsgen_full; subst envs_full aux_full; clear Henvsgen_full.
        edestruct NAMEGEN.generate_node_scoped_env'_split_node
          as (envs_pref' & aux_pref' & st_pref & local_env & rec & st_local
              & envs_cur & st_cur & Hpref & Hlocal & Hins & Htail);
          eauto.
        rewrite Hprefgen in Hpref. inversion Hpref; subst envs_pref' aux_pref' st_pref.
        assert (Hcur : st_cur = st_local).
        {
          unfold NAMEGEN.fresh_insert_node_env in Hins.
          destruct (Env.mem n.(n_name) envs_pref) eqn:Hmem; try discriminate.
          unfold NAMEGEN.insert_node_env, NAMEGEN.NMret in Hins.
          inversion Hins. reflexivity.
        }
        subst st_cur.
        assert (Hfindlocal : find_node_env n.(n_name) envs = Some local_env).
        {
          eapply NAMEGEN.generate_node_scoped_env'_preserves_find; eauto.
          eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
        }
        assert (Hauxlocal : get_node_aux n.(n_name) aux_names = Some (rec.(nclk), rec.(nrst))).
        {
          eapply NAMEGEN.generate_node_scoped_env'_preserves_get_node_aux; eauto.
          - pose proof (NAMEGEN.generate_local_env_for_node_name _ _ _ _ _ Hlocal) as Hrecname.
            unfold get_node_aux. simpl. rewrite <- Hrecname, ident_eqb_refl. reflexivity.
          - eapply NAMEGEN.fresh_insert_node_env_finds_new; eauto.
        }
        unfold SECNLUSTYPING.generate_node_sig_scoped_env in Hnsig.
        rewrite Hfindlocal in Hnsig.
        unfold SECSTCTYPING.generate_sys_signature_scoped_env in Hssig.
        assert (Hfindlocal_sys :
                  find_node_env (translate_node n).(SynStc.s_name) envs = Some local_env).
        { simpl. exact Hfindlocal. }
        rewrite Hfindlocal_sys in Hssig.
        assert (Henvinj : SECNLUSTYPING.env_injective local_env).
        { eapply NAMEGEN.generate_local_env_for_node_injective; eauto. }
        assert (Hnsigscoped : signature_scoped nsig).
        {
          eapply SECNLUSTYPING.generate_node_sig_scoped with (P := nodes).
          - exact Hacc1scoped.
          - exact Henvinj.
          - exact Hwc_head.
          - exact Hnsig.
        }
          assert (Hssigscoped : signature_scoped ssig).
          {
            eapply SECSTCTYPING.generate_sys_signature_scoped with (P := translate nodes).
            - exact Hacc2scoped.
            - exact Henvinj.
            - eapply translate_node_wc_local; eauto.
            - exact Hssig.
          }
          edestruct SECNLUSTYPINGCORRECTNESS.generate_node_sig_inv as
              (clk_id & rst_id & clk_type & rst_type & inp & out & locals & nconst & st_n
               & Haux & Hclk & Hrst & Hinp & Hout & Hlocals & Hnconst & Hnsigdef);
            eauto.
          assert (Hscopefresh : SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env n local_env aux_names acc1).
          {
            eapply SECNLUSTYPINGCORRECTNESS.node_scope_fresh_in_env_from_bounds; eauto.
          }
          assert (Hpres : signatures_preserved nsig ssig).
          {
            eapply generated_signatures_preserved_from_simplify_bridge_local_env
              with (P := nodes) (env := local_env) (aux_names := aux_names)
                   (rec := rec) (st := st) (st' := st_local); eauto.
          }
          assert (Hclkid : clk_id = rec.(nclk)).
          {
            rewrite Hauxlocal in Haux.
            inversion Haux. reflexivity.
          }
          assert (Hrstid : rst_id = rec.(nrst)).
          {
            rewrite Hauxlocal in Haux.
            inversion Haux. reflexivity.
          }
          assert (Hnsiggood : signature_good nsig).
          {
            rewrite Hnsigdef.
            eapply SECNLUSTYPINGCORRECTNESS.generate_node_sig_good_from_local_env
              with (P := nodes) (rec := rec) (st := st) (st' := st_local)
                   (clk_type := clk_type) (rst_type := rst_type)
                   (inp := inp) (out := out) (locals := locals)
                   (raw := nconst) (st_n := st_n).
            - exact Hlocal.
            - exact Hauxlocal.
            - exact Hacc1scoped.
            - exact Hwc_head.
            - rewrite <- Hclkid. exact Hclk.
            - rewrite <- Hrstid. exact Hrst.
            - exact Hinp.
            - exact Hout.
            - exact Hlocals.
            - exact Hnconst.
          }
          assert (Hndscope_nsig : NoDup (sig_scope nsig)).
          {
            rewrite Hnsigdef.
            eapply SECNLUSTYPINGCORRECTNESS.generate_node_sig_scope_nodup_from_local_env
              with (rec := rec) (st := st) (st' := st_local)
                   (clk_type := clk_type) (rst_type := rst_type)
                   (inp := inp) (out := out).
            - exact Hlocal.
            - rewrite <- Hclkid. exact Hclk.
            - rewrite <- Hrstid. exact Hrst.
            - exact Hinp.
            - exact Hout.
          }
        assert (Hhead : Signature_head_consistent nsig ssig).
          {
            split.
            - eapply generated_signature_name_agree; eauto.
            - destruct Hpres as [Hfields Hprescall].
              split; [exact Hfields|].
              split.
                + eapply signatures_preserved_simple_calls_from_good.
                  * exact Hnsiggood.
                  * exact Hndscope_nsig.
                  * exact Hssigscoped.
                  * exact (conj Hfields Hprescall).
              + eapply signatures_preserved_reset_calls_from_good.
                * exact Hnsiggood.
                * exact Hndscope_nsig.
                * exact Hnsigscoped.
                * exact Hssigscoped.
                * exact (conj Hfields Hprescall).
          }
        assert (Hcons' : Signature_consistent (nsig :: acc1) (ssig :: acc2)).
        { eapply Signature_consistent_cons; eauto. }
        assert (Hacc1scoped' : secglobal_scoped (nsig :: acc1)).
        { eapply secglobal_scoped_cons; eauto. }
        assert (Hacc2scoped' : secglobal_scoped (ssig :: acc2)).
        { eapply secglobal_scoped_cons; eauto. }
        assert (Hacc2sec' : secglobal_scope_sec (ssig :: acc2)).
        {
          eapply secglobal_scope_sec_cons; eauto.
          eapply generated_sys_signature_scope_sec_from_local_env
            with (rec := rec) (st := st) (st' := st_local) (aux_names := aux_names); eauto.
        }
        assert (Hnsigbound : SIG.signature_scope_bounded_above nsig st_local).
        {
          intros ty Hin.
          eapply SECNLUSTYPINGCORRECTNESS.generated_node_sig_scope_upper_bound_from_local_env
            with (rec := rec) (st := st) (st' := st_local) (aux_names := aux_names); eauto.
        }
        assert (Hle : (st <= st_local)%positive).
        { eapply NAMEGEN.generate_local_env_for_node_state_monotone; eauto. }
        assert (Hbound' : SIG.secglobal_scope_bounded_above (nsig :: acc1) st_local).
        {
          eapply SIG.secglobal_scope_bounded_above_cons; eauto.
          eapply SIG.secglobal_scope_bounded_above_monotone; eauto.
        }
        assert (Hstep :
                  NAMEGEN.generate_node_scoped_env' (n :: nil) envs_pref aux_pref st =
                  OK ((envs_cur, rec :: aux_pref), st_local)).
        {
          simpl.
          unfold NMbind2.
          rewrite Hlocal.
          simpl.
          unfold NMbind.
          rewrite Hins.
          simpl.
          reflexivity.
        }
        assert (Hprefgen' :
                  NAMEGEN.generate_node_scoped_env' (prefix ++ n :: nil) (Env.empty _) nil NAMEGEN.init_state =
                  OK ((envs_cur, rec :: aux_pref), st_local)).
        {
          eapply NAMEGEN.generate_node_scoped_env'_app; eauto.
        }
          assert (Henvsgen' : generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes) = OK (envs, aux_names)).
          {
            assert (Heqlist : (prefix ++ n :: nil) ++ nodes = prefix ++ n :: nodes).
            {
              clear - prefix n nodes.
              induction prefix as [|a prefix IHprefix]; simpl.
              - reflexivity.
              - now f_equal.
            }
            assert (Heqprefix :
                      generate_node_scoped_env ((prefix ++ n :: nil) ++ nodes) =
                      generate_node_scoped_env (prefix ++ n :: nodes)).
            {
              now rewrite Heqlist.
            }
            rewrite Heqprefix.
            simpl.
            exact Henvsgen.
          }
        eapply IH with (prefix := prefix ++ n :: nil)
                        (acc1 := nsig :: acc1) (acc2 := ssig :: acc2)
                        (envs := envs) (aux_names := aux_names)
                        (envs_pref := envs_cur) (aux_pref := rec :: aux_pref)
                        (st := st_local); eauto.
    Qed.

    Corollary generate_all_signatures_consistent_scoped:
      forall all_nodes envs aux_names G1 G2,
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2 /\ secglobal_scoped G2 /\ secglobal_scope_sec G2.
      Proof.
        intros all_nodes envs aux_names G1 G2
               Henvsgen Hwc Hallnl Hallstc.
        unfold SECNLUSTYPING.generate_all_signatures_scoped_env in Hallnl.
        unfold SECSTCTYPING.generate_all_sys_signatures_scoped_env in Hallstc.
        eapply generate_all_signatures_consistent_scoped'
          with (prefix := nil) (acc1 := nil) (acc2 := nil)
               (envs := envs) (aux_names := aux_names)
               (envs_pref := Env.empty _) (aux_pref := nil)
               (st := NAMEGEN.init_state) (G1 := G1) (G2 := G2).
        - reflexivity.
        - exact Henvsgen.
        - exact Hwc.
        - apply Signature_consistent_nil.
        - apply secglobal_scoped_nil.
        - apply secglobal_scoped_nil.
        - apply secglobal_scope_sec_nil.
        - apply SIG.secglobal_scope_bounded_above_nil.
        - exact Hallnl.
        - exact Hallstc.
      Qed.

    Corollary generate_all_signatures_consistent:
      forall all_nodes envs aux_names G1 G2,
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
        Signature_consistent G1 G2.
    Proof.
      intros all_nodes envs aux_names G1 G2
             Henvsgen Hwc Hallnl Hallstc.
      destruct (generate_all_signatures_consistent_scoped
                  all_nodes envs aux_names G1 G2 Henvsgen Hwc Hallnl Hallstc)
        as [Hcons _].
      exact Hcons.
    Qed.

    (** Lookup-based program signature theorem.
        This is the public signature-level form of the final result.  It does
        not rerun per-node signature generation.  Instead, it states directly
        that any source signature found in the generated global source
      signature environment has a matching target signature in the generated
      STC global environment, and that the pair is
      [Signature_head_consistent].  All raw/local constraint details remain
      internal to the bridge lemmas above. *)
    Corollary generated_program_signatures_preserved_global:
      forall all_nodes (G1 G2: secglobal)
             (envs: node_scoped_env) (aux_names: list node_aux_names),
        generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
        CloNL.wc_global all_nodes ->
        SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names = OK G1 ->
        SECSTCTYPING.generate_all_sys_signatures_scoped_env (translate all_nodes) envs aux_names = OK G2 ->
        forall f nsig,
          SIG.find_signature f G1 = Some nsig ->
          exists ssig,
            SIG.find_signature f G2 = Some ssig
            /\ Signature_head_consistent nsig ssig.
    Proof.
      intros all_nodes G1 G2 envs aux_names
             Henvsgen Hwc Hallnl Hallstc
             f nsig Hfindsig.
      pose proof (generate_all_signatures_consistent
                    all_nodes envs aux_names G1 G2
                    Henvsgen
                    Hwc Hallnl Hallstc) as Hcons.
      destruct (Hcons f nsig Hfindsig) as (ssig & Hfindstc & Hhead).
      exists ssig. split; assumption.
    Qed.

    (** Bridge ingredients for the weaker STC result.

        This file provides the syntactic/cross-phase preservation facts
        consumed by the STC-side semantic noninterference corollary proved in
        [SecStcNonInterference.v]:

        - not an intrinsic theorem for arbitrary STC runs;
        - but a translated-behavior corollary for STC loops produced from
          secure NLustre nodes.

        The proof should be assembled only after the source-side NLustre
        noninterference theorem is finished.  At that point, the intended
        ingredients are:

        - the source indexed NLustre noninterference theorem;
        - [NLMemSemantics.sem_msem_node] / [NLMemSemantics.msem_sem_node] to
          move between indexed NLustre semantics and memory semantics;
        - [NLustreToStc.Correctness.correctness_loop] to obtain STC loops for
          the translated system with the same input/output streams; and
        - [generated_program_signatures_preserved_global] to align the source
          and target security signatures on shared interface variables.

        This is why this file stays a preservation library, while the actual
        translated-behavior noninterference theorem should now live in
        [SecStcNonInterference.v]. *)
  End NODESYSPRES.



End SECNLUSSTCTRANSLATION.


Module SecNLusStcTranslation
  (Import Ids   : IDS)
  (Import Lat   : Lattice)
  (Import Op    : OPERATORS)
  (Import SC    : SECMONAD Ids)
  (Import SecTypes : SECTYPES Lat)
  (Import CESyn : CESYNTAX Op)
  (Import SynNL : NLSYNTAX  Ids Op CESyn)
  (Import SynStc: STCSYNTAX Ids Op CESyn)
  (Import Mem   : MEMORIES  Ids Op CESyn SynNL)
  (Import Translation  : TRANSLATION Ids Op CESyn SynNL SynStc Mem)
  (Import SIG          : SIGNATURE   Ids SC)
  (Import SIGPROOFS    : SIGNATURE_PROOFS Ids SC SIG Lat SecTypes)
  (Import NAMEGEN      : NAMEGEN Ids Op CESyn SynNL)
  (Import SECCETYPING  : SECCETYPING Ids Op CESyn)
  (Import CEIsF        : CEISFREE Ids Op CESyn)
  (Import CEClo        : CECLOCKING Ids Op CESyn)
  (Import OrdNL        : NLORDERED Ids Op CESyn SynNL)
  (Import IsD          : ISDEFINED Ids Op CESyn SynNL Mem)
  (Import IsFNL        : ISFREE Ids Op CESyn SynNL CEIsF)
  (Import CloNL        : NLCLOCKING Ids Op CESyn SynNL OrdNL Mem IsD CEIsF IsFNL CEClo)
  (Import SECNLUSTYPING: SECNLUSTYPING Ids Op SC CESyn SynNL SIG NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL)
  (Import SECNLUSTYPINGCORRECTNESS
      : SECNLUSTYPINGCORRECTNESS Ids Op SC CESyn SynNL Lat SecTypes SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo OrdNL Mem IsD IsFNL CloNL SECNLUSTYPING)
  (Import Last         : STCISLAST Ids Op CESyn SynStc)
  (Import Var          : STCISVARIABLE Ids Op CESyn SynStc)
  (Import Def          : STCISDEFINED Ids Op CESyn SynStc Var Last)
  (Import Syst         : STCISSYSTEM Ids Op CESyn SynStc)
  (Import OrdStc       : STCORDERED Ids Op CESyn SynStc Syst)
  (Import IsFStc       : STCISFREE Ids Op CESyn SynStc CEIsF)
  (Import CloStc       : STCCLOCKING Ids Op CESyn SynStc Last Var Def Syst OrdStc CEClo)
  (Import SECSTCTYPING : SECSTCTYPING Ids Op SC CESyn SynStc SIG SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc)
  (Import SECSTCTYPINGCORRECTNESS
      : SECSTCTYPINGCORRECTNESS Ids Op SC CESyn SynNL SynStc Lat SecTypes SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING)
  <: SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo OrdNL IsD IsFNL CloNL SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING SECSTCTYPINGCORRECTNESS.

  Include SECNLUSSTCTRANSLATION Ids Lat Op SC SecTypes CESyn SynNL SynStc Mem Translation SIG SIGPROOFS NAMEGEN SECCETYPING CEIsF CEClo OrdNL IsD IsFNL CloNL SECNLUSTYPING SECNLUSTYPINGCORRECTNESS Last Var Def Syst OrdStc IsFStc CloStc SECSTCTYPING SECSTCTYPINGCORRECTNESS.
End SecNLusStcTranslation.
