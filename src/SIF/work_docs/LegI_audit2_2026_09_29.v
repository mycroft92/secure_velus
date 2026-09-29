(** * Evidence: the repaired [fby_created_pairs] is exclusive and satisfiable

    Compiled 2026-09-29, same method as LegI_audit_2026_09_29.v.  Where the
    old premise FORCED the initial value's type to add nothing, the repaired
    one is satisfied by the entries each equation's own run produces:

      - AUDIT_shapes_exclusive: a cut output and an ite output cannot be the
        same list, so the two clauses never both fire and no guard on
        [is_constant] is needed;
      - AUDIT_satisfiable_cut: one entry satisfies it on a cut equation, and
        is functional;
      - AUDIT_satisfiable_ite: two entries satisfy it on an ite equation, and
        are functional given the flag and the fby variable are distinct,
        which freshness gives.
*)


    (** AUDIT 2: the repaired premise is exclusive and satisfiable *)

    Lemma AUDIT_shapes_exclusive :
      forall x x' ann e0 e i px eqsi ty ck name,
        [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])]
        <> ([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
           :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                        [(ty, (ck, name))]]) :: eqsi.
    Proof.
      intros x x' ann e0 e i px eqsi ty ck name H. inversion H.
    Qed.

    (** a cut equation's own entry satisfies it, on its own *)
    Lemma AUDIT_satisfiable_cut :
      forall x x' ann e0 e ty ck name ckty s0 s1 b',
        Env.find x' env = Some b' ->
        fby_created_pairs [(b', merge (merge [rst_ty] ckty) (merge s0 s1))]
          [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])]
          x e0 e ty ck name ckty s0 s1
        /\ levels_functional
             [(b', merge (merge [rst_ty] ckty) (merge s0 s1))].
    Proof.
      intros x x' ann e0 e ty ck name ckty s0 s1 b' Hb'.
      split; [split|].
      - intros y annq bp Heq Hbp. inversion Heq; subst y annq.
        rewrite Hb' in Hbp. inversion Hbp; subst bp. now left.
      - intros i px eqsi bp Heq Hbp.
        exfalso. eapply AUDIT_shapes_exclusive; exact Heq.
      - intros y L1 L2 [H1|[]] [H2|[]];
          inversion H1; inversion H2; reflexivity.
    Qed.

    (** and an ite equation's two entries satisfy it, together *)
    Lemma AUDIT_satisfiable_ite :
      forall x i px e0 e ty ck name ckty s0 s1 bi bp eqsi,
        Env.find px env = Some bp ->
        bi <> bp ->
        fby_created_pairs
          [(bp, merge (merge [rst_ty] ckty) s1); (bi, merge [rst_ty] ckty)]
          (([x], [Eite (Evar i (bool_type, (ck, Some i))) [e0]
                    [Evar px (ty, (ck, Some px))] ([ty], (ck, name))])
           :: ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e]
                        [(ty, (ck, name))]]) :: eqsi)
          x e0 e ty ck name ckty s0 s1
        /\ levels_functional
             [(bp, merge (merge [rst_ty] ckty) s1); (bi, merge [rst_ty] ckty)].
    Proof.
      intros x i px e0 e ty ck name ckty s0 s1 bi bp eqsi Hbp Hne.
      split; [split|].
      - intros y annq bq Heq Hbq.
        exfalso. eapply AUDIT_shapes_exclusive.
        exact (@Coq.Init.Logic.eq_sym _ _ _ Heq).
      - intros j q eqsj bq Heq Hbq.
        inversion Heq; subst j q eqsj.
        rewrite Hbp in Hbq. inversion Hbq; subst bq. now left.
      - intros y L1 L2 H1 H2.
        destruct H1 as [H1|[H1|[]]]; destruct H2 as [H2|[H2|[]]];
          inversion H1; inversion H2; subst; try reflexivity.
        + now elim Hne.
        + now elim Hne.
    Qed.
