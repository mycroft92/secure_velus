# Lustre → NLustre security preservation (the Lustre leg)

## Goal

Security types for Lustre, generated from the elaborated source program, such that
noninterference proved for the transcribed NLustre program (see
`Non-interference-proof.md`) holds for a security policy stated on the *source* program,
with no assumption about the normalised program's security data.

## Current state

All files below compile (full SIF rebuild, no `Admitted`).  Branch `constraint_gen`.

| File | Content |
|------|---------|
| `SecLusTypes.v`, `SecLNameInterface.v`, `SecLNamingTotality.v` | Lustre flow types; the naming pass and its totality/injectivity |
| `SecLTyping.v` | the Lustre constraint generator (`generate_lnode_sig`, `generate_all_lsignatures_scoped_env`) |
| `SecLusUnnesting{Base,Expr,Calls,Streams,Equations,Nodes}.v`, `SecLusUnnesting.v` | Leg U: unnesting preserves the generated constraints |
| `SecLusNormFby.v` | Leg I: `fby` normalisation preserves them |
| `SecLusTypingCorrectness.v` | structural facts about generated signatures (good, scoped, rooted, NoDup scope) |
| `SecLusNormalization.v` | program-level lockstep of both legs; `normalization_signatures_preserved` |
| `SecLusNLusTranslation.v` | Lustre signatures entail the NLustre ones of the transcribed program |
| `SecLusConstraintExport.v` | `source_signatures_entail_nlustre`, `source_policy_realised` |
| `SecNLusNodeSecurity.v` | `node_security_exists_pos`, `policy_node_security` |
| `SecEndToEnd.v` | `policy_class_noninterference` |

## The two main theorems

### 1. Full type preservation: source signatures entail the NLustre signatures

`SecLusConstraintExport.v`, `Check.source_signatures_entail_nlustre`.  For an elaborated,
well-clocked, well-typed Lustre program `G`, with `P` the NLustre program obtained by unnesting,
`fby` normalisation and transcription, the signatures generated for `G` (`GS`) entail those
generated for `P` (`GN`):

```coq
Theorem source_signatures_entail_nlustre :
  forall (G : L.Syn.global) (Hwl : L.Syn.wl_global G)
         (Hpr : Forall (fun n => L.Syn.n_prefixes n = U.elab_prefs) G)
         (Hunt : U.unnested_global (U.unnest_global G Hwl Hpr))
         (Hpref1 : Forall (fun n => L.Syn.n_prefixes n = NFm.norm1_prefs)
                     (U.unnest_global G Hwl Hpr)),
    L.Clo.wc_global G -> L.Typ.wt_global G ->
    forall envs aux stN st GS GT GM P Hp GN,
      ConcreteSecLNameGen.generate_lnode_scoped_env_st
        (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1))
        = OK (envs, aux, stN) ->
      LegN.sec_le stN st ->
      L.Ord.Ordered_nodes
        (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1) ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env (rev G) envs aux
        st = OK GS ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env
        (rev (U.unnest_global G Hwl Hpr)) envs aux st = OK GT ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env
        (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1))
        envs aux st = OK GM ->
      TR.Tr.to_global
        (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1) Hp
        = OK P ->
      ConcreteNameGen.generate_node_scoped_env (rev P) = OK (envs, aux) ->
      NL.Ord.Ordered_nodes P ->
      NL.Clo.wc_global P ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK GN ->
      Leg.Signature_entails GS GN.
```
`Signature_entails GS GN` says every
source signature `n1` has a same-named NLustre signature `n2` with `Signature_head_entails n1 n2`
(same interface, `preserves_on` the scope, and the call clause).  Its reading for policies is
`source_policy_realised`: a valuation satisfying a source signature's stored constraints
extends, agreeing on the signature scope, to one satisfying the NLustre signature.

It is assembled from `normalization_signatures_preserved` (`SecLusNormalization.v`):

```coq
Theorem normalization_signatures_preserved :
  forall (G : global) (Hwl : wl_global G) (Hpr : ...) (Hunt : ...) (Hpref1 : ...),
    wc_global G -> wt_global G ->
    forall envsF auxF stN st GS GT GM,
      generate_lnode_scoped_env_st (rev (normfby_global (unnest_global G Hwl Hpr) Hunt Hpref1))
        = OK (envsF, auxF, stN) ->
      sec_le stN st ->
      generate_all_lsignatures_scoped_env (rev G) envsF auxF st = OK GS ->
      generate_all_lsignatures_scoped_env (rev (unnest_global G Hwl Hpr)) envsF auxF st = OK GT ->
      generate_all_lsignatures_scoped_env (rev (normfby_global ...)) envsF auxF st = OK GM ->
      call_weakens GS GM /\ sigs_preserved GS GM.
```
with the Lustre→NLustre bridge of `SecLusNLusTranslation.v`.

### 2. Full noninterference on a Lustre node (`SecLusEndToEnd.v`)

`LusNI.lustre_noninterference`.  It is about the *source* Lustre program and its own coinductive
semantics (`L.Sem.sem_node`).  Take a node `nS` of `G` with source signature `sgS` and a valuation
`d1` satisfying `sgS`'s stored constraints — a security policy on the node's interface.  Then
there is `w` agreeing with `d1` on the scope of `sgS` such that any two runs of `f` whose input
streams are low-equal (and share their base clock) have low-equal output streams, where "low"
is read at levels `w` through the node's security environment `ty_env`:

```coq
Theorem lustre_noninterference :
  forall (G : L.Syn.global) (Hwl : L.Syn.wl_global G)
         (Hpr : Forall (fun n => L.Syn.n_prefixes n = Unnesting.elab_prefs) G)
         (Hunt : Unnesting.unnested_global (Unnesting.unnest_global G Hwl Hpr))
         (Hpref1 : Forall (fun n => L.Syn.n_prefixes n = NormFby.norm1_prefs)
                     (Unnesting.unnest_global G Hwl Hpr)),
    L.Clo.wc_global G -> L.Typ.wt_global G ->
    Forall L.Cau.node_causal (Unnesting.unnest_global G Hwl Hpr) ->
    forall envs aux stN st GS GT GM P Hp GN,
      ConcreteSecLNameGen.generate_lnode_scoped_env_st
        (rev (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1))
        = OK (envs, aux, stN) ->
      C.LegN.sec_le stN st ->
      L.Ord.Ordered_nodes
        (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env (rev G) envs aux
        st = OK GS ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env
        (rev (Unnesting.unnest_global G Hwl Hpr)) envs aux st = OK GT ->
      ConcreteSecLTyping.generate_all_lsignatures_scoped_env
        (rev (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1))
        envs aux st = OK GM ->
      TR.Tr.to_global
        (NormFby.normfby_global (Unnesting.unnest_global G Hwl Hpr) Hunt Hpref1) Hp
        = OK P ->
      ConcreteNameGen.generate_node_scoped_env (rev P) = OK (envs, aux) ->
      NL.Ord.Ordered_nodes P ->
      NL.Clo.wc_global P ->
      C.SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK GN ->
      forall f nS sgS d1,
        L.Syn.find_node f G = Some nS ->
        SIG.find_signature f GS = Some sgS ->
        NI.signature_satisfied d1 sgS ->
        exists w,
          C.SecT.agree_on (SIG.signature_scope sgS) d1 w /\
          forall ty_env t ins outs ins' outs',
            find_node_env f envs = Some ty_env ->
            L.Sem.sem_node G f ins outs ->
            L.Sem.sem_node G f ins' outs' ->
            L.ClSem.sem_clock_inputs G f ins ->
            L.ClSem.sem_clock_inputs G f ins' ->
            CE.Sem.clock_of (CIStr.tr_Streams ins) = CE.Sem.clock_of (CIStr.tr_Streams ins') ->
            stream_low_eq ty_env w t (List.map fst nS.(L.Syn.n_in))
              (CIStr.tr_Streams ins) (CIStr.tr_Streams ins') ->
            stream_low_eq ty_env w t (List.map fst nS.(L.Syn.n_out))
              (CIStr.tr_Streams outs) (CIStr.tr_Streams outs').
```

The hypotheses of `source_signatures_entail_nlustre` are repeated verbatim.  `stream_low_eq ty_env w t xs xss xss'` says: for every instant `k` and
position `i` with variable `x = xs[i]` low at `t` under `w`, the values of `xss` and `xss'` at `k`,
`i` are equal (presence included).

How it is derived (all proved in the file, no admits):

1. `source_run_nl`: a run of `G` descends to a coinductive NLustre run of `P` — unnesting
   correctness (`unnest_global_sem`), `fby` normalisation correctness (`normfby_global_sem`),
   and `TR.Correctness.sem_l_nl`.
2. `find_node_nl`: the node of `P` has the same input and output names as `nS`.
3. The signature half gives `sgN` with `signatures_preserved sgS sgN`
   (`source_signatures_entail_nlustre`, `source_policy_realised`), and
   `policy_node_security` turns `d1` into `w` with `node_security P GN envs aux n' w w`.
4. `nl_stream_ni`: both runs go to indexed histories (`NL.CoindToIdx.implies`), the NLustre
   theorem `node_noninterference_outputs` gives history low-equality of outputs, and
   `history_low_eq_streams` reads it back as `stream_low_eq`.

`Print Assumptions` shows only the standard Velus ones (identifier interface, Reals,
classical logic) and the lattice parameter.

The Obc-level corollary `SecEndToEnd.policy_class_noninterference` states the same for the
compiled node's Obc `step` method, from an NLustre node and a source signature related by
`signatures_preserved`.

## Proof methodology

1. **Constraint generation with scoped names.**  A single naming pass gives every node an
   environment of `sec` names and two auxiliary names (clock, reset).  A node's signature is
   generated from raw constraints by `collapse` and `simplify` (eliminating locals); the
   signature's *scope* is inputs, outputs, clock and reset formals.  Programs are processed
   callee-first: generation and naming hypotheses are over `rev all_nodes` (programs are stored
   caller-first), so a call finds its callee's signature already published.

2. **Signature preservation as `preserves_on scope`.**  Each normalisation pass is shown to
   preserve generated constraints in the sense `preserves_on scope c1 c2`: every valuation
   satisfying `c1` is agreed on the scope by one satisfying `c2`.  Passes are proved per node
   (`unnest_instance`, `normfby_instance`) and lifted by a lockstep induction over the program
   that carries the callee accumulator (`call_weakens`).  Every node is typed against the naming
   of the largest program (the normalised one); facts about the environment's range are
   redone against the node's own variables.  Nested calls are supported: a nested call's
   anonymous name is an environment key, and the typing run mints a fresh result name.

3. **Bridge to NLustre.**  Lustre signatures entail the NLustre signatures of the transcribed
   program by a lockstep fold (`generate_all_signatures_entails_scoped_inv'`) generalised over the
   callee program and `Forall (wc_node P)`.

4. **`node_security` is constructed, not assumed.**  Given a valuation `d1` satisfying a node's
   stored signature, `signature_satisfied_replays_raw` yields a raw valuation agreeing on the scope.
   The callee clauses are read off the satisfied instantiated constraints (a satisfied call block
   gives a satisfied callee signature by completeness of the substitution), and each callee is
   taken at its own witness by strong induction on the node's position in `rev all_nodes`
   (`node_security_exists_pos`).  The callee clause is `node_security callee w w` at the callee's
   own raw valuation.  A node regenerated against the final global yields the same signature
   (`regen_full2`): generation reads the global only through the signatures of called nodes.

5. **Chain to Obc.**  `node_security` yields `system_security` (Stc) and `class_security`
   (scheduled Stc and Obc) via the signature bridges, and `class_noninterference_outputs`
   concludes.  `SecEndToEnd.v` is a functor over the Obc chain's parameters; `SecNLusNodeSecurity`
   takes the NI module as a parameter so `node_security` is the same object throughout.

## Scope and remaining work

- Rebasing onto the original branches and cleanup of obsolete branches remain to be done.
