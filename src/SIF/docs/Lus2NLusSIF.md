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
      generate_lnode_scoped_env_st
        (rev (NFm.normfby_global (U.unnest_global G Hwl Hpr) Hunt Hpref1))
        = OK (envs, aux, stN) ->
      sec_le stN st ->
      NFm-normalised program is L.Ord.Ordered_nodes ->
      generate_all_lsignatures_scoped_env (rev G) envs aux st = OK GS ->
      generate_all_lsignatures_scoped_env (rev (U.unnest_global G Hwl Hpr)) envs aux st = OK GT ->
      generate_all_lsignatures_scoped_env (rev (normfby_global ...)) envs aux st = OK GM ->
      TR.Tr.to_global (normfby_global ...) Hp = OK P ->
      NAMEGEN.generate_node_scoped_env (rev P) = OK (envs, aux) ->
      NL.Ord.Ordered_nodes P -> NL.Clo.wc_global P ->
      SECNLUSTYPING.generate_all_signatures_scoped_env (rev P) envs aux = OK GN ->
      Signature_entails GS GN.
```
(abbreviated; the exact statement is in the file.)  `Signature_entails GS GN` says every
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

### 2. Full noninterference: source policy ⟹ Obc step-method noninterference

`SecEndToEnd.v`, `policy_class_noninterference`.  For a node `n` of the (NLustre) program, a
source signature `sgS` related by `signatures_preserved` to the generated signature `sgN` of `n`,
and a valuation `d1` satisfying `sgS` — a policy on the source node's interface — there is a
valuation `w` agreeing with `d1` on the scope of `sgS` such that the compiled node's Obc `step`
method is output-low-equivalent for low-equivalent inputs at levels `w`:

```coq
Theorem policy_class_noninterference:
  forall all_nodes Gsrc Gstc Gstcs Gobc envs aux_names pre n post sgS sgN d1,
    NAMEGEN.generate_node_scoped_env (rev all_nodes) = OK (envs, aux_names) ->
    NL.Ord.Ordered_nodes all_nodes ->
    NL.Clo.wc_global all_nodes ->
    Stc.Clo.wc_program (TransNL.translate all_nodes) ->
    Stc.Wdef.Well_scheduled (Sched.schedule (TransNL.translate (rev all_nodes))) ->
    SECNLUSTYPING.generate_all_signatures_scoped_env (rev all_nodes) envs aux_names = OK Gsrc ->
    SECSTCTYPING.generate_all_sys_signatures_scoped_env
      (TransNL.translate (rev all_nodes)) envs aux_names = OK Gstc ->
    SECSTCTYPING.generate_all_sys_signatures_scoped_env
      (Sched.schedule (TransNL.translate (rev all_nodes))) envs aux_names = OK Gstcs ->
    SECOBCTYPING.generate_all_class_signatures_scoped_env
      (TransObc.translate (Sched.schedule (TransNL.translate (rev all_nodes))))
      envs aux_names = OK Gobc ->
    NLCaus.nl_global_causal all_nodes ->
    rev all_nodes = pre ++ n :: post ->
    SIG.find_signature n.(n_name) Gsrc = Some sgN ->
    SIGPROOFS.signatures_preserved sgS sgN ->
    NLusSupport.signature_satisfied d1 sgS ->
    exists w,
      SecT.agree_on (SIG.signature_scope sgS) d1 w /\
      forall stepm ty_env t xss xss' yss yss' ins ins' outs outs',
        Obc.Syn.find_method step
          (TransObc.translate_system (Sched.schedule_system (TransNL.translate_node n))).(c_methods)
          = Some stepm ->
        find_node_env n.(n_name) envs = Some ty_env ->
        translated_class_behavior all_nodes (TransNL.translate_node n) xss yss ins outs ->
        translated_class_behavior all_nodes (TransNL.translate_node n) xss' yss' ins' outs' ->
        eq_str (clock_of xss) (clock_of xss') ->
        same_low_presence ty_env w t (map fst stepm.(m_in)) xss xss' ->
        obc_stream_low_eq ty_env w t (map fst stepm.(m_in)) ins ins' ->
        obc_stream_low_eq ty_env w t (map fst stepm.(m_out)) outs outs'.
```

Hypotheses: the generator/naming equations, the compiler's own facts (translated program
well-clocked, scheduled program well-scheduled), and causality.  There is **no** hypothesis on
the security data of the normalised program and no `source_guard`.  The step from the source
policy to the NLustre signature is `source_policy_realised`; composing it with
`source_signatures_entail_nlustre` for a whole Lustre program is by instantiating `sgN` with the
transcribed signature that theorem provides.

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

- The Obc-level theorem is stated for an NLustre node and a source signature related to its
  generated signature; the source-program-wide instantiation is the combination of the two
  theorems above (no single Lustre-level statement is packaged).
- Rebasing onto the original branches and cleanup of obsolete branches remain to be done.
