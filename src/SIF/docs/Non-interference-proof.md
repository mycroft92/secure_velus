# NLustre Indexed Non-Interference Proof Plan

## Goal

State and prove noninterference for the NLustre security type system directly
over the indexed semantics in:

- `src/NLustre/NLIndexedSemantics.v`

The target file is:

- `src/SIF/SecNLusNonInterference.v`

The intended result is the NLustre source-side noninterference theorem needed
before any later cross-phase reasoning about translation to STC.

## Main Design Decision

The proof should be carried out directly on indexed histories, not by reducing
to the coinductive semantics.

This is the better fit for the current repository state because:

- the indexed semantics already exposes histories as `history := stream env`;
- the core expression layer already provides indexed environment-switching
  lemmas;
- the STC translation paper also phrases its soundness argument in an indexed,
  instant-by-instant style;
- the current thesis work is already centered on generated symbolic signatures,
  indexed environments, and source-local naming facts.

So the proof should treat coinductive correspondence as background metatheory,
not as the main route.

## Scope

This plan is only for NLustre noninterference with respect to indexed
semantics.

It does not try to prove, in this file:

- translation preservation to STC;
- any coinductive/indexed equivalence result;
- any Lustre-level theorem above NLustre.

Those belong later in the pipeline.

## Paper Alignment

This plan follows the theorem shape used in the NLustre noninterference papers,
but adapts the proof architecture to the current Vélus mechanization.

Paper-level structure:

1. define low projection `⊑ t`;
2. define node security;
3. prove NLustre noninterference by induction on dependency structure.

Repository-level adaptation:

1. define low-equivalence directly on indexed histories;
2. define node security through generated signatures and satisfiable generated
   constraints;
3. prove noninterference by induction on `Ordered_nodes`, using the generated
   naming and signature correctness lemmas already present in `SIF`.

## Existing Infrastructure To Reuse

### Indexed semantics

- `src/NLustre/NLIndexedSemantics.v`
- `src/CoreExpr/CESemantics.v`

These provide:

- indexed histories as `stream env`;
- deterministic indexed semantics for expressions, clocks, and annotated
  expressions;
- node/equation semantics for `EqDef`, `EqFby`, ordinary calls, and reset
  calls.

### Environment irrelevance lemmas

- `src/CoreExpr/CEProperties.v`

These are the most important semantic lemmas for the direct indexed route:

- `sem_exp_instant_switch_env`
- `sem_cexp_instant_switch_env`
- `sem_clock_instant_switch_env`
- `sem_aexp_instant_switch_env`
- `sem_caexp_instant_switch_env`

They already express the exact idea needed for noninterference:
if two environments agree on the free variables of an expression or clock, then
the expression or clock has the same semantics in both.

### Static-to-dynamic clocking support

- `src/NLustre/NLClockingSemantics.v`

This may be useful when the proof needs to connect:

- well-clocked nodes/equations;
- semantic clock facts;
- dynamic presence/absence constraints.

It is probably not the first tool to use, but it is the right fallback for
clock-sensitive subgoals.

### Source-side symbolic typing

- `src/SIF/SecNLusTyping.v`
- `src/SIF/SecNLusTypingCorrectness.v`

These provide the source-side symbolic facts that should drive the proof:

- scopedness of generated constraints;
- well-formedness of raw generated constraints;
- structural goodness of generated signatures;
- source naming injectivity and visible-scope facts.

The most useful theorems are:

- `generate_node_sig_good_from_local_env`
- `generate_node_sig_scope_nodup_from_local_env`
- `generated_node_simplify_ready_from_local_env`

### Signature-local instantiation metatheory

- `src/SIF/SIFSignature.v`

This is what should replace any paper-style informal reasoning about callee
signatures.

The key theorems are:

- `generate_constraints_correct_inst`
- `generate_constraints_complete_good`

These let the proof move between:

- the stored generated signature of a callee;
- the instantiated constraints induced by a concrete call site.

### Generic symbolic-type metatheory

- `src/SIF/SecTypes.v`

The main facts needed here are:

- `hm_ext_list_in1`
- `hm_ext_bound_from_members`
- `constraintSatisfiable_ext`
- `listSatisfiable_ext`

These support the “if a symbolic type is below `t`, then every identifier that
contributes to it is also below `t`” reasoning.

### Naming discipline

- `src/SIF/NameInterface.v`

This should be used to recover the exact local security environment of a node
and to avoid ambiguity about which security variable corresponds to which raw
identifier.

## Recommended Statement Shape

The paper defines a projected history `H|X⊑t`. In the indexed development, the
first working definition should be relational rather than functional.

### Step 1: define low variables

Given:

- a set of raw variables `X`;
- a security environment `Γ` represented by the generated local env;
- a ground instantiation `s`;
- a lattice level `t`;

define the low subset by:

- `x` is low iff `hm_ext s [Γ(x)] ⊑ t`

Since node-local security identifiers are singletons, this can usually be
written as `s (Γ(x)) ⊑ t`, but the definition should be phrased in the same
symbolic-style vocabulary as the rest of `SIF`.

### Step 2: define low-equivalence on environments

Define a relation like:

- `env_low_eq lowvars R R'`

meaning:

- for every raw variable `x` in `lowvars`, `Env.find x R = Env.find x R'`.

This is the actual property consumed by the indexed semantic switching lemmas.

### Step 3: lift low-equivalence to histories

Define:

- `history_low_eq lowvars H H'`

meaning:

- for every instant `n`, `env_low_eq lowvars (H n) (H' n)`.

This is better than starting with a literal projected history function because:

- it matches the semantics lemmas directly;
- it avoids unnecessary `Env` rebuilding lemmas;
- it keeps the proof pointwise in time.

### Optional step 4: add a projection wrapper later

If a paper-facing statement is still desired, define a projection operation
after the relational version is in place, and prove it equivalent to
`history_low_eq`.

That avoids making projection plumbing the first obstacle.

## Recommended Security Predicate

The proof should not introduce a separate handwritten typing judgment that
duplicates the current generated-signature machinery.

Instead define node security in terms of:

- the generated local security environment for the node;
- the generated node signature;
- satisfiability of the generated constraints under a ground instantiation;
- recursive security of callees at call sites.

In other words, the node-security definition should be generated-signature
driven, not syntax-driven.

That aligns better with the actual codebase and with later translation work.

## Core Theorem Shape

The main theorem should be a direct indexed analogue of the paper theorem:

- if a node is secure with respect to a ground instantiation `s`,
- and two indexed histories both satisfy the node equations,
- and they agree on low inputs,
- then they agree on all low visible variables of the node.

The visible variables should be:

- input variables;
- output variables;
- local variables;

not arbitrary generated helper identifiers.

The helper security identifiers belong in the typing proof, not in the semantic
statement.

## Proof Architecture

### Phase 1: low-dependency lemmas for symbolic types

Add a small local library proving facts of the form:

- if `hm_ext s st ⊑ t`, then every identifier in `st` also maps below `t`;
- if a generated constraint says `lhs ⊑ [x]` and `x` is low, then everything in
  `lhs` is low.

These lemmas are the bridge from symbolic constraint satisfiability to semantic
low-dependency.

This is the direct indexed replacement for the paper’s informal step:

- “otherwise we would contradict `s(α) ⊑ t`”.

### Phase 2: semantic irrelevance lemmas for indexed environments

Package the `CEProperties` lemmas into node-proof-friendly wrappers:

- if two instant environments agree on all free variables of `e`, then
  `sem_exp_instant` agrees;
- similarly for `cexp`, `clock`, `aexp`, and `caexp`.

These wrappers should take low-equivalence assumptions over a list or set of
variables, not raw `forall x, Is_free_in_* x e -> ...` premises, so later proofs
stay readable.

### Phase 3: simple equation cases

Prove one local theorem per non-call equation form.

#### `EqDef`

From generated typing we get a constraint roughly of the form:

- `ckty ⊔ expty ⊑ [xty]`

If `xty` is low under `s`, satisfiability implies:

- `ckty` is low;
- `expty` is low.

Then every free variable of the clock and RHS expression is low by the symbolic
type lemmas, so the indexed switching lemmas yield equal RHS semantics in both
histories. The equation semantics then forces equal values for `x`.

#### `EqFby`

This is the same pattern as `EqDef`, but the RHS is an annotated expression.

The proof should again split into:

- clock low;
- expression low;
- same RHS value under both histories;
- equation semantics yields equal stream for `x`.

No special coinductive reasoning is needed because `Indexed.fby` is already an
extensional stream definition.

### Phase 4: ordinary node-call case

This is the first genuinely recursive case.

Use the call-site generated constraint block plus:

- `generate_node_sig_good_from_local_env`
- `generate_constraints_complete_good`

to reconstruct satisfiability of the callee’s stored signature under the
instantiated valuation.

Then use the induction hypothesis on the callee, instantiated with:

- the callee’s low inputs at this call;
- the two histories restricted to the concrete actual argument values.

The semantic argument should show:

- if one output of the call is low, then every input flow on which that output
  depends is also low;
- therefore the actual low inputs to the callee agree in the two executions;
- therefore the corresponding low callee outputs agree;
- therefore the caller-side assigned variables agree.

### Phase 5: reset node-call case

This should be treated as an extension of the ordinary call case, not as a
separate theorem family.

The generated NLustre call constraints already thread reset information into
the instantiated constraint block. So the reset proof should reuse the same
call-instantiation route, with one extra dependency:

- the reset stream must also be low whenever a low output depends on it.

The indexed semantics already makes reset explicit through `SEqReset`, so the
main additional semantic work is to show that:

- the masked actuals fed to the callee agree on their low parts whenever the
  relevant reset-controlled segment is observed.

This is exactly where the direct indexed route is cleaner than the coinductive
one: the semantics is already formulated instant-by-instant around masks and
reset counts.

## Induction Principle

Do not invent a new numeric dependency level unless it becomes unavoidable.

The first proof should be structured by the repository’s existing dependency
discipline:

- `Ordered_nodes`

This mirrors the paper’s induction on dependency level, but fits the actual
development better.

Operationally:

- the proof over a head node assumes the result for every node that can be
  called from that node;
- `Ordered_nodes` already guarantees those callees occur later in the global.

If a numeric level is later wanted for exposition, it can be derived from the
ordered list after the proof works.

## Proposed Local Lemma Stack

The exact names can change, but the decomposition should stay close to this.

### Low-observation definitions

- `low_var_under`
- `low_vars_of`
- `env_low_eq`
- `history_low_eq`

### Symbolic-type lemmas

- membership below a bound:
  if `hm_ext s st ⊑ t` and `x ∈ st`, then `s x ⊑ t`
- low clock dependencies from `assign_clk_type`
- low expression dependencies from `assign_exp_type`
- low control-expression dependencies from `assign_cexp_type`

These should be documented as the indexed counterpart of the paper’s simple
security reasoning.

### Semantic transfer lemmas

- `sem_exp_instant_low_eq`
- `sem_cexp_instant_low_eq`
- `sem_clock_instant_low_eq`
- `sem_aexp_instant_low_eq`
- `sem_caexp_instant_low_eq`

These will mostly be wrappers around `CEProperties`.

### Equation-local noninterference lemmas

- `eqdef_noninterference`
- `eqfby_noninterference`
- `eqapp_noninterference`
- `eqreset_noninterference`

Each should explain which paper case it corresponds to.

### Node theorem

- one theorem for a single node under a generated local env and generated
  signature;
- one corollary for node-scoped generated environments over a full global.

## Generated Environment Strategy

The proof should use the node-scoped naming discipline from `NameInterface.v`,
not the older flat shared env.

That means the final practical theorem should be phrased with:

- `generate_node_scoped_env`
- `find_node_env`
- `generate_node_sig_scoped_env`

This avoids proving a theorem against an obsolete environment model and then
rewriting it later.

## Suggested Implementation Order

### Step 1

Create the basic observation definitions in
`src/SIF/SecNLusNonInterference.v`:

- low variables;
- low-equivalence on envs;
- low-equivalence on histories.

Do not define a concrete projection function yet unless it is immediately
helpful.

### Step 2

Prove the symbolic-type membership lemmas using:

- `hm_ext_list_in1`
- lattice transitivity;
- satisfiability facts from `SecTypes.v`.

These are foundational and should be established before touching node semantics.

### Step 3

Wrap the `CEProperties` switching lemmas in low-equivalence form.

This should make later equation proofs almost mechanical.

### Step 4

Prove the local equation theorems for:

- `EqDef`
- `EqFby`

These are the cleanest sanity check that the direct indexed route is working.

### Step 5

Prove the call instantiation bridge lemma needed for `EqApp` and reset calls.

This is where `generate_node_sig_good_from_local_env` and
`generate_constraints_complete_good` should be integrated.

### Step 6

Prove the ordinary call case.

Only after that should the reset-call case be attempted.

### Step 7

Prove the reset-call case using the same instantiated-signature route.

### Step 8

Assemble the node theorem by induction over the ordered global structure.

### Step 9

Package the theorem into the generated-environment form most useful for later
translation work.

## Known Risks

### Reset semantics bookkeeping

The reset case is likely the main technical cost. The semantic proof will
probably need careful handling of:

- `bools_of`
- `mask`
- reset counts

before the induction hypothesis on the callee can be applied cleanly.

### Call-site valuation setup

The proof must be disciplined about which valuation is used where:

- source ground instantiation `s` for the caller;
- instantiated valuation at the call site for the callee signature.

This should be abstracted early in a dedicated lemma to avoid repetition.

### Scope mismatch between raw identifiers and security identifiers

The semantic theorem speaks about raw program variables.
The typing theorem speaks about generated security identifiers.

The bridge must always pass through the generated local env explicitly.

### Avoiding premature projection functions

A concrete projection operator on `Env.t` histories may look paper-like, but it
will create extra proof overhead. The first complete proof should stay
relational.

## Recommended Theorem Packaging

The public theorem stack in `SecNLusNonInterference.v` should ideally end with:

1. a low-level theorem for one node under a concrete generated local env;
2. a theorem lifted to generated node-scoped environments for a full NLustre
   global;
3. a short statement explaining that this is the indexed-semantics analogue of
   the paper’s NLustre noninterference theorem.

That will make the later translation-preservation work easier to connect to.

## Minimal First Milestone

The first milestone should not be the full theorem.

The first successful checkpoint should be:

- definitions of low-equivalence;
- symbolic-type “members are low” lemmas;
- indexed noninterference for `EqDef` and `EqFby`.

If that compiles cleanly, the direct indexed route is validated and the call
cases can be built on top of it.

## Relation To The Thesis

This proof plan keeps the development as close as possible to the papers while
respecting the current repository architecture:

- source-local security typing already lives in `SIF`;
- the naming discipline is already generated and node-scoped;
- the symbolic-call metatheory is already mechanized in `SIFSignature.v`;
- the indexed semantics already has the right environment-switching lemmas.

So the right next step is not to translate the old coinductive argument, but to
restate the paper’s noninterference theorem directly in the indexed setting and
prove it using the generated signature infrastructure that the thesis has
already built.
