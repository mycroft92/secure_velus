# NLustre Indexed Non-Interference Proof Plan

## Goal

State and prove noninterference for the NLustre security type system directly
over the indexed semantics in:

- `src/NLustre/NLIndexedSemantics.v`

The target file is:

- `src/SIF/SecNLusNonInterference.v`

The intended result is the NLustre source-side noninterference theorem needed
before any later cross-phase reasoning about translation to STC.

## Vocabulary Alignment

To keep the Coq development aligned with the papers and with the existing SIF
files, we standardize the following translation.

- paper `s` = Coq `dlt : ident -> Lat.t`
- paper `ρ` = Coq `sig.(s_constraints)`
- paper “`ρ` is satisfied by `s`” = Coq
  `listSatisfiable dlt sig.(s_constraints)`
- paper `Γ` = generated node-local typing environment from `NameInterface`

This avoids introducing a second parallel notation for the same concepts in
`SecNLusNonInterference.v`.

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

## Interesting Proof Points For The Thesis Text

These are worth explaining explicitly in the thesis, because they are the main
places where the mechanized indexed-semantics proof is less syntactic than the
paper presentation may suggest.

### 1. History-level noninterference must be reduced to instant-level semantics

The semantic low-equivalence hypothesis is stated over indexed histories:

- `history_low_eq X H H'`

But the reusable semantic irrelevance lemmas from `CEProperties` are all
instant-level:

- `sem_caexp_instant_switch_env`
- `sem_aexp_instant_switch_env`

So the proof has to explain the bridge clearly:

- fix an instant `n`;
- specialize `history_low_eq` to the snapshots `H n` and `H' n`;
- apply the instant-level switch lemma at that `n`;
- lift the resulting equality back to the stream level by extensionality or
  semantic determinism.

This is one of the main differences between the clean paper statement and the
actual Coq proof shape.

### 2. The switch lemmas consume disjunctive free-variable premises

The instant switch lemmas do not take the source-level predicates
`Is_free_in_caexp` or `Is_free_in_aexp` directly. Instead they require
pointwise agreement for premises of the form:

- `Is_free_in_clock x ck \/ Is_free_in_cexp x ce`
- `Is_free_in_clock x ck \/ Is_free_in_exp x e`

So the Coq proof has to unpack:

- `Is_free_in_caexp`
- `Is_free_in_aexp`

into the appropriate disjunct manually. This is a small but important proof
engineering point: the semantic lemma is reusable exactly because it is stated
at the lower expression/clock layer, but that means the NLustre proof must
reconstruct the right branch of the disjunction each time.

### 3. The semantic switch lemmas return equivalences, not direct equalities

`sem_caexp_instant_switch_env` and `sem_aexp_instant_switch_env` conclude an
`iff`, not an equality of streams. So the proof structure is:

- transport the old semantic judgment to the new history using one direction of
  the `iff`;
- derive two semantic judgments for the same expression under the same history;
- use semantic determinism (`sem_caexp_det` / `sem_aexp_det`) to conclude that
  the resulting streams are equal.

This is worth explaining in the thesis because it shows why determinism is not
just a background property; it is the final step that turns semantic
transport into observable equality.

### 4. The simple-security argument is split into typing and semantic halves

For the simple equation cases (`EqDef` and `EqFby`), the proof does not jump
directly from “the output is low” to “the two runs agree on the RHS”.
Instead it factors through two separate steps:

- a typing-side simple-security lemma:
  `simple_security`, specialized as `simple_security_caexp` and
  `simple_security_aexp`;
- a semantic switch step on the RHS under low-equivalent histories.

This split is useful to explain in the thesis because it makes clear that:

- the symbolic type system is used only to prove that dependencies are low;
- the indexed semantics is then used to prove that low dependencies force equal
  observations.

That separation matches the conceptual proof structure better than a single
monolithic lemma.

### 5. Security-level equality is not semantic determinacy

The current raw node theorem on `vars_defined n.(n_eqs)` cannot be justified
from signature satisfiability and `wc_node` alone.

A minimal problematic shape is an instantaneous cycle such as:

- `o = y`
- `y = o`

The generated constraints do force the two symbolic levels to coincide:

- from the first equation, `oty ⊑ yty`;
- from the second equation, `yty ⊑ oty`;
- so under antisymmetry, `dlt oty = dlt yty`.

But this is only a typing fact. It says that `o` and `y` live at the same
security level; it does **not** say that their values are uniquely determined
by the inputs.

Within a single run, the equations force:

- `H(o) = H(y)`.

But noninterference needs a cross-run conclusion:

- from equal low inputs in `H` and `H'`, conclude `H(o) = H'(o)` for low
  outputs.

The instantaneous cycle does not provide that cross-run link. Two runs may
both satisfy the equations while choosing different streams, as long as the
variables in the cycle remain equal **within** each run.

It is also important that the built-in NLustre invariant `n_ingt0` is not
enough to rule this out. A node may have a non-empty input interface and still
contain an unused instantaneous cycle among defined variables.

So the missing ingredient for the node theorem is not “the node has inputs”;
it is a causality / acyclicity property ensuring that low defined values are
determined by already-fixed dependencies.

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

The first internal theorem should be stated on the variables already tracked by
the existing typing/generation lemmas:

- `vars_defined n.(n_eqs)`

rather than immediately on a custom “visible-variable” notion.

This is the better fit because:

- `generate_eqns_constraints_shape` already characterises the generated raw
  constraints against `vars_defined n.(n_eqs)`;
- `NoDup_var_defined_n_eqs` already gives the uniqueness property needed to
  reason per defined variable;
- `n.(n_defd)` later provides the bridge to
  `map fst (n.(n_vars) ++ n.(n_out))`.

So the proof flow should be:

1. prove a proof-internal theorem on `vars_defined n.(n_eqs)` under a raw
   completed valuation that already satisfies the unsimplified node
   constraints;
2. derive a corollary on `map fst (n.(n_vars) ++ n.(n_out))` using `n_defd`;
3. derive the final output-only corollary on `map fst n.(n_out)`, where the
   valuation is pushed back to the stored simplified signature scope.

The generated helper security identifiers belong in the typing proof, not in
the semantic statement.

### Why the Internal Theorem Uses a Raw Valuation

The current node signature stores `SymTypes.simplify raw locals`, not the raw
constraints `raw` themselves.

That means:

- satisfiability of the stored signature constrains outputs and interface
  symbols directly;
- eliminated locals are only constrained after replaying `simplify_complete`;
- a theorem over `vars_defined n.(n_eqs)` cannot use the final paper-facing
  valuation blindly, because that variable set includes locals.

So the right split is:

- one replay lemma from stored signature satisfiability to a completed raw
  valuation agreeing on `signature_scope sig`;
- one proof-internal noninterference theorem on `vars_defined` under that raw
  valuation;
- one later corollary that returns to the stored signature valuation on
  outputs, where agreement on `signature_scope sig` is sufficient.

### Typing Prerequisite Discharge

The local theorem should still take `wc_node P n` at the point where it uses
the existing typing/correctness lemmas, because:

- `generate_node_sig_scoped` requires `wc_node P n`;
- `generate_node_sig_scoped_env_scoped` requires `wc_node P n`;
- `generate_node_sig_good_from_local_env` requires `wc_node P n`.

However, this should be regarded as a dischargeable local prerequisite rather
than a final theorem burden. The intended source is the global clocking
invariant of the program. This is already the pattern documented in
`SecNLusTyping.v`, where the all-signatures proof notes explicitly say that
`wc_global` supplies the current node's `wc_node` fact.

## Proof Architecture

### Phase 1: replay stored signature constraints to raw equation constraints

Before the semantic cases, prove the source-side replay lemma:

- from `signature_satisfied dlt sig`
- plus the generated-node side conditions from
  `generated_node_simplify_ready_from_local_env`

recover a completed valuation `dlt_raw` such that:

- `agree_on (signature_scope sig) dlt dlt_raw`
- `listSatisfiable dlt_raw raw`

for the raw constraints returned by `generate_eqns_constraints`.

This is the bridge from the stored generated signature to the per-equation
typing facts that the semantic proof actually consumes.

### Phase 2: low-dependency lemmas for symbolic types

Add a small local library proving facts of the form:

- if `hm_ext s st ⊑ t`, then every identifier in `st` also maps below `t`;
- if a generated constraint says `lhs ⊑ [x]` and `x` is low, then everything in
  `lhs` is low.

These lemmas are the bridge from symbolic constraint satisfiability to semantic
low-dependency.

This is the direct indexed replacement for the paper’s informal step:

- “otherwise we would contradict `s(α) ⊑ t`”.

### Phase 3: semantic irrelevance lemmas for indexed environments

Package the `CEProperties` lemmas into node-proof-friendly wrappers:

- if two instant environments agree on all free variables of `e`, then
  `sem_exp_instant` agrees;
- similarly for `cexp`, `clock`, `aexp`, and `caexp`.

These wrappers should take low-equivalence assumptions over a list or set of
variables, not raw `forall x, Is_free_in_* x e -> ...` premises, so later proofs
stay readable.

### Phase 4: simple equation cases

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

### Phase 5: ordinary node-call case

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

### Phase 6: reset node-call case

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

### Phase 7: assemble the main theorem and corollaries

After the equation-local lemmas are in place:

1. prove the node theorem on `vars_defined n.(n_eqs)`;
2. transport it across `n.(n_defd)` to node locals plus outputs;
3. package the output-only corollary that later translation-facing theorems are
   most likely to consume.

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

## Current Proof Status

The first indexed milestone is now in place in
`src/SIF/SecNLusNonInterference.v`.

Completed and compiling under the direct local `coqc` check:

- low-observation definitions for generated node-local environments:
  `low_var`, `env_low_eq`, `history_low_eq`, and the projection wrappers;
- vocabulary alignment helpers for the paper notation:
  `ground_instantiation`, `signature_constraints`, `signature_satisfied`;
- paper-style recursive `node_security`;
- replay from simplified stored node signatures back to raw generated
  constraints:
  `signature_satisfied_replays_raw`;
- simple-security lemmas:
  `simple_security`, `simple_security_caexp`, `simple_security_aexp`;
- free-variable bound lemmas for the generated symbolic types, including
  `assign_cexp_type_free_bound`;
- indexed semantic transport lemmas for the simple equation cases:
  `sem_caexp_switch_history_low` and `sem_aexp_switch_history_low`;
- indexed equation-local noninterference for the non-call cases:
  `eqdef_noninterference` and `eqfby_noninterference`.

This is the first concrete confirmation that the indexed route works with the
current SIF infrastructure: the proof now successfully combines generated
typing constraints, history-level low-equivalence, pointwise CE switching, and
semantic determinism for the simple NLustre equation cases.

## Checkpoint

Current checkpoint after the causality refactor:

- the NLustre causality formalization has been pulled out into
  `src/SIF/NLustreCausality.v`;
- that new file now contains:
  `nl_depends_on_eq`, `nl_depends_on`, `nl_graph_of_eqs`,
  `nl_graph_of_node`, `nl_node_causal`, `nl_global_causal`,
  `nl_global_causal_find`, `nl_TopoOrder_inv`, and the first
  `nl_causal_ind` / `nl_node_causal_ind` induction layer;
- `src/SIF/SecNLusNonInterference.v` has been rewired to import the new
  causality functor and thread it as `NLCaus` in the interface instead of
  keeping the causality definitions locally;
- `vfiles` and `_CoqProject` have been updated to include
  `src/SIF/NLustreCausality.v`.

Important status note:

- this refactor was intentionally checkpointed before revalidation;
- `make clean` completed, but the subsequent full `make` was stopped on
  purpose;
- there is therefore no post-refactor compile verdict yet for the extracted
  causality file plus the rewired `SecNLusNonInterference.v`.

## Immediate Next Step

The remaining work is the node theorem, not more local infrastructure.

Concretely:

- re-run direct `coqc` on `src/SIF/NLustreCausality.v` and
  `src/SIF/SecNLusNonInterference.v`, and fix any fallout from the extraction
  before resuming theorem work;
- finish `node_noninterference_vars_defined_raw`;
- make the “input low-equivalence percolates to defined low variables” argument
  precise at node level;
- add the `EqApp` and reset-call noninterference lemmas using the recursive
  `node_security` hypothesis and instantiated callee valuations;
- derive the output-facing corollaries from the internal `vars_defined`
  theorem.

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
