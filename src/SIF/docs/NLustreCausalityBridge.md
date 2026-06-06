# Bridging Lustre And NLustre Causality

## Scope

This note explains how `SIF/NLustreCausality.v` can be connected to the
existing Velus correctness pipeline.

The short version is:

- core semantic correctness from Lustre to NLustre is still proved using
  Lustre causality;
- `SIF/NLustreCausality.v` is not part of that proof today;
- but there is a clean bridge theorem that can connect the two worlds after
  Lustre normalization and transcription.

## Current Situation

On the Lustre side, normalization already produces a causal Lustre program:

```coq
Lemma normalize_global_causal : forall G G' Hwl Hprefs,
    wc_global G ->
    normalize_global G Hwl Hprefs = Errors.OK G' ->
    Forall LCA.node_causal G'.
```

This is the final normalization-side causality result used by the top-level
pipeline.

On the transcription side, semantic correctness from normalized Lustre to
NLustre is stated as:

```coq
Theorem sem_l_nl :
  forall G P Hprefs f ins outs,
    LN.NormFby.normalized_global G ->
    Lord.Ordered_nodes G ->
    Forall LCA.node_causal G ->
    LT.wt_global G ->
    LC.wc_global G ->
    to_global G Hprefs = OK P ->
    LS.sem_node G f ins outs ->
    LCS.sem_clock_inputs G f ins ->
    NLSC.sem_node P f ins outs.
```

This theorem consumes `Forall LCA.node_causal G` on the Lustre side.  It does
not require or produce an NLustre-specific causality predicate.

In contrast, the SIF noninterference development uses the NLustre-side
predicate:

```coq
Definition nl_node_causal (n : node) : Prop := ...
Definition nl_global_causal (G : global) : Prop := Forall nl_node_causal G.
```

So today there are two distinct uses:

- Lustre causality drives source-side semantic correctness.
- NLustre causality drives SIF noninterference induction over translated
  NLustre equations.

## What The Bridge Should Say

The natural connection point is transcription, not the core semantic proof.

The right theorem family is:

```coq
Lemma to_node_causal :
  forall n n' Hpref,
    to_node n Hpref = OK n' ->
    LCA.node_causal n ->
    NLCaus.nl_node_causal n'.

Theorem to_global_causal :
  forall G P Hprefs,
    to_global G Hprefs = OK P ->
    Forall LCA.node_causal G ->
    NLCaus.nl_global_causal P.
```

These statements say:

- if one Lustre node is causal, then its translated NLustre node is causal in
  the SIF sense;
- if a whole Lustre global is causal, then the translated NLustre global is
  causal in the SIF sense.

## Why This Is The Right Connection

This bridge matches the existing structure of the compiler:

1. `normalize_global` runs the Lustre causality check and proves the output
   Lustre program is causal.
2. `to_global` translates that normalized Lustre program into NLustre.
3. `to_global_causal` would transfer the causal structure to
   `NLCaus.nl_global_causal`.

This gives the useful corollary:

```coq
Corollary l_to_nl_causal :
  forall G P,
    l_to_nl G = OK P ->
    NLCaus.nl_global_causal P.
```

This is the theorem that can feed SIF directly for compiled programs.

## Why The Bridge Should Be Provable

The translation performed by `Transcription/Tr.v` is already close to the
dependency structure used in `SIF/NLustreCausality.v`.

After normalization, `to_equation` maps one Lustre equation to exactly one
NLustre equation of one of the following forms:

- `EqDef`
- `EqApp`
- `EqFby`

This matters because the SIF causality predicate is equation-local:

```coq
Definition nl_depends_on_eq (eq : equation) (x y : ident) : Prop := ...
```

The corresponding Lustre causality predicate is also graph-based:

```coq
Definition node_causal (n : node) :=
  exists {v a} (g : AcyGraph v a), graph_of_node n g.
```

So both developments use the same high-level shape:

- a graph over node variables;
- edges induced by same-instant dependencies;
- acyclicity packaged as existence of an `AcyGraph`.

The main proof obligation is therefore not conceptual.  It is a
translation-preservation lemma for dependencies:

- each dependency seen by one translated NLustre equation must correspond to a
  dependency already permitted by the source Lustre causal graph.

## What This Bridge Does Not Replace

This bridge does not remove Lustre causality from source semantic correctness.

The existing proof of `sem_l_nl` uses Lustre causality through Lustre clock and
semantic invariants such as:

- `l_sem_node_clock`
- `sc_node_sc_var_inv'`

Those lemmas are source-side results phrased in terms of `LCA.node_causal`.
They are part of the proof that a Lustre semantic execution can be replayed as
an NLustre semantic execution.

So the bridge should be viewed as an additional exported fact, not a
replacement for the existing correctness argument.

## What The Bridge Buys SIF

Once `to_global_causal` is available, the SIF proofs can obtain
`NLCaus.nl_global_causal` for NLustre programs coming from the standard Velus
pipeline without assuming it separately.

That is exactly the missing connection between:

- `normalize_global_causal` and the source correctness pipeline; and
- the `NLCaus.nl_global_causal` hypothesis currently used in
  `SecNLusNonInterference.v` and related files.

In practice, this lets the SIF stack consume a theorem derived from the
compiler pipeline instead of treating NLustre causality as an independent
external assumption.

## Suggested Placement

The most natural home for the bridge proof is near transcription, because the
theorem is about preservation through `to_node` and `to_global`.

Reasonable options are:

- a new theorem in `Transcription/Correctness.v`;
- or a separate file that depends on both `Lustre/LCausality.v` and
  `SIF/NLustreCausality.v`.

The second option keeps the core Velus proof unchanged while letting SIF add
its own causality bridge cleanly.

## Minimal Theorem Set

If only the SIF entry point matters, the minimal useful exported statements are:

```coq
Theorem to_global_causal :
  forall G P Hprefs,
    to_global G Hprefs = OK P ->
    Forall LCA.node_causal G ->
    NLCaus.nl_global_causal P.

Corollary l_to_nl_causal :
  forall G P,
    l_to_nl G = OK P ->
    NLCaus.nl_global_causal P.
```

If the proof needs to proceed node-by-node, then add `to_node_causal` first and
derive `to_global_causal` by induction over the source global.
