(** * Evidence: [fby_created_pairs] is not dischargeable

    Compiled 2026-09-29 by pasting into a copy of SecLusNormFby.v inside
    Section NormFbyNode.  The lemma below GOES THROUGH, which is the
    problem: [fby_created_pairs] together with [NoDup (map fst pairs)]
    forces the initial value's security type to add nothing to the
    ambient -- so the premise pair is unsatisfiable on exactly the
    equations this leg exists for.

    Two causes, both visible in the statement of [fby_created_pairs]:
      1. its second clause has no [is_constant e0 = false] guard, so it
         speaks about an [ite] the pass never builds on a cut equation;
      2. both clauses quantify over ALL states, so they speak about runs
         the pass never performs -- and hence about idents it never
         creates.
*)


    (** AUDIT *)
    Lemma nodup_fst_unique :
      forall {A : Type} (l : list (ident * A)) y v w,
        NoDup (List.map fst l) -> In (y, v) l -> In (y, w) l -> v = w.
    Proof.
      induction l as [|(z,a) l IH]; intros y v w Hnd Hv Hw; [contradiction|].
      cbn [List.map] in Hnd. inversion Hnd as [|z0 l0 Hz Hnd']; subst.
      destruct Hv as [Hv|Hv]; destruct Hw as [Hw|Hw].
      - inversion Hv; inversion Hw; subst. reflexivity.
      - inversion Hv; subst. exfalso. apply Hz.
        apply in_map_iff. exists (y, w). split; [reflexivity|exact Hw].
      - inversion Hw; subst. exfalso. apply Hz.
        apply in_map_iff. exists (y, v). split; [reflexivity|exact Hv].
      - exact (IH y v w Hnd' Hv Hw).
    Qed.

    Lemma fby_iteexp_px_from_fresh :
      forall e0 e ty ck name q i px eqsi q1,
        fby_iteexp e0 e (ty, (ck, name)) q =
          (Eite (Evar i (bool_type, (ck, Some i))) [e0]
             [Evar px (ty, (ck, Some px))] ([ty], (ck, name)),
           ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                      [(ty, (ck, name))]]) :: eqsi, q1) ->
        exists r r', fresh_ident norm2 ((ty, ck), false) r = (px, r').
    Proof.
      intros e0 e ty ck name q i px eqsi q1 H.
      unfold fby_iteexp in H.
      apply bind2_spec in H as (j & eqsj & s1 & Ej & H).
      apply bind_spec in H as (y & s2 & Ey & H).
      rewrite ret_spec in H. inversion H; subst.
      exists s1, s2. exact Ey.
    Qed.

    (** The premise [fby_created_pairs], together with [NoDup], forces the
        initial value's type to add nothing -- so it is dischargeable only on
        equations where it happens to.  Two reasons, both visible in its
        statement: its second clause has no [is_constant e0 = false] guard, so
        it speaks about an [ite] the pass never builds on a cut equation; and
        both clauses quantify over *all* states, so they speak about runs the
        pass never performs. *)
    Lemma AUDIT_fby_created_pairs_forces_s0_redundant :
      forall pairs to_cut x e0 e ty ck name ckty s0 s1
             q i px eqsi q1 bp,
        is_constant e0 = true ->
        PS.mem x to_cut = true ->
        fby_iteexp e0 e (ty, (ck, name)) q =
          (Eite (Evar i (bool_type, (ck, Some i))) [e0]
             [Evar px (ty, (ck, Some px))] ([ty], (ck, name)),
           ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                      [(ty, (ck, name))]]) :: eqsi, q1) ->
        Env.find px env = Some bp ->
        fby_created_pairs pairs to_cut x e0 e ty ck name ckty s0 s1 ->
        NoDup (List.map fst pairs) ->
        merge (merge [rst_ty] ckty) (merge s0 s1)
        = merge (merge [rst_ty] ckty) s1.
    Proof.
      intros pairs to_cut x e0 e ty ck name ckty s0 s1
        q i px eqsi q1 bp Hconst Hcut Hite Hbp (Hc1 & Hc2) Hnd.
      destruct (fby_iteexp_px_from_fresh e0 e ty ck name q i px eqsi q1 Hite)
        as (r & r' & Er).
      eapply nodup_fst_unique;
        [exact Hnd
        |exact (Hc1 r px r' bp Hconst Hcut Er Hbp)
        |exact (Hc2 q q1 i px eqsi bp Hite Hbp)].
    Qed.
