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

## Current Theorem Shape

The theorem layer should now be organized in two levels:

- the **paper-facing public level**, which talks only about the canonical
  signature valuation; and
- the **internal proof level**, which may still carry a replayed raw
  valuation.

Concretely:

- the recursive predicate is
  `node_security n dlt_sig dlt_raw`;
- that predicate now also stores the current node's raw generation witnesses
  and `listSatisfiable dlt_raw raw`, so recursive call proofs do not need to
  replay raw satisfiability from signatures a second time;
- the final NLustre noninterference theorem is currently stated directly on
  that paired predicate;
- `node_outputs_raw_spec` may stay in the file, but only as an internal proof
  target and never as an assumption of the final theorem statement;
- the bridge back to `generate_node_sig_scoped_env` belongs in one lookup
  inversion lemma, currently local to `SecNLusNonInterference.v`, and should
  later be moved upstream into `SecNLusTyping`/`SecNLusTypingCorrectness`.

This keeps the theorem stream flat for now while still leaving room for a
stronger internal route where the `EqApp` proof needs raw replay information.

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

### 6. The internal theorem should range over the exact generated source program

The proof-internal `vars_defined` theorem should not be stated over an
arbitrary source signature environment `G`.

Instead, it should be tied to the actual generated source program data:

- `generate_node_scoped_env all_nodes = OK (envs, aux_names)`
- `wc_global all_nodes`
- `generate_all_signatures_scoped_env all_nodes envs aux_names = OK G`

This is the right shape for the recursive call case.

Why:

- `EqApp` does not just need a local typing fact for the current node; it must
  connect back to the exact source signature stored for the callee.
- The global relation between `all_nodes`, `envs`, `aux_names`, and `G`
  provides that connection cleanly.
- `wc_global all_nodes` also supplies the `wc_node` facts needed for the
  current node and for recursive callees through the existing typing
  correctness lemmas.

So the internal theorem should be read as a theorem about one node *inside the
exact generated NLustre program*, not about one node against an arbitrary
ambient `G`.

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

### Why Paired `node_security` Is Now Necessary

The earlier single-valuation route turned out to be too weak for the `EqApp`
case once the internal theorem kept track of `vars_defined n.(n_eqs)`,
including caller locals.

There are still two different valuations in play:

- the **canonical signature valuation** `dlt_sig`, which is the paper's `s`
  and drives stored signatures plus call-site instantiation;
- the **replayed raw valuation** `dlt_raw`, which satisfies the unsimplified
  raw constraints of the current node.

The replay lemma only provides:

- `agree_on (signature_scope sig) dlt_sig dlt_raw`;
- `listSatisfiable dlt_raw raw`.

That agreement is enough for outputs in the current node signature scope, but
it is not enough for caller locals produced by a call equation:

- a call instantiation uses the caller-side output typing `outtyp`;
- if the call defines a caller local, then the corresponding symbolic
  identifier lies in `outtyp`;
- that identifier need not lie in `signature_scope sig`.

So the callee theorem needed in the caller proof must be available under both:

- the canonical instantiated valuation from `dlt_sig`; and
- the replayed instantiated valuation from `dlt_raw`.

That is why the active route now bakes both valuations directly into
`node_security` itself.  The predicate records:

- canonical signature satisfiability on `dlt_sig`;
- scope agreement between `dlt_sig` and `dlt_raw`;
- recursive callee security under the pair of instantiated valuations.

This removes the exact mismatch that blocked the older `EqApp` proof while
still keeping the final observable theorem canonical on `dlt_sig`.

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

## Compile-Pressure Refactor

To reduce rechecking pressure while the indexed proof script remains unstable,
the stable support prefix of `SecNLusNonInterference.v` was extracted into
`src/SIF/SecNLusNonInterferenceSupport.v`.

What moved in this first pass:
- the low-observation layer (`ground_instantiation`, `low_var`,
  `history_low_eq[_upto]`, projection lemmas, simple-security helpers);
- the generated node-security layer up through the paired `node_security`
  predicate.

What moved in the second pass:
- the stable `GENERATED_NODE_NONINTERFERENCE` helper block through
  `node_outputs_raw_spec`, including the `EqApp` transport lemmas and the
  generated-constraint inversion lemmas such as
  `generate_eqapp_constraint_inv` and `generate_eqreset_constraint_inv`.

What intentionally stayed in `SecNLusNonInterference.v`:
- the active theorem stack
  `node_noninterference_vars_defined_step`,
  `node_noninterference_outputs_raw`,
  `node_noninterference_outputs`.

This split is intentionally conservative: it removes roughly the first half of
the file from the main proof recheck without forcing the theorem stack to be
rewritten around newly explicit section parameters.

Completed and compiling under the direct local `coqc` check:

- low-observation definitions for generated node-local environments:
  `low_var`, `env_low_eq`, `history_low_eq`, and the projection wrappers;
- vocabulary alignment helpers for the paper notation:
  `ground_instantiation`, `signature_constraints`, `signature_satisfied`;
- paired recursive `node_security` carrying both `dlt_sig` and `dlt_raw`;
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

- after the refactor checkpoint, direct `coqc` now succeeds again for both
  `src/SIF/NLustreCausality.v` and `src/SIF/SecNLusNonInterference.v`;
- the remaining gap is no longer interface fallout, but the admitted internal
  step theorem `node_noninterference_vars_defined_step`.

## Immediate Next Step

The remaining work is the node theorem, not more local infrastructure.

Concretely:

- rebuild `node_noninterference_vars_defined_step` under paired
  `node_security`;
- then prove `node_noninterference_outputs_raw`;
- add the `EqApp` and reset-call noninterference lemmas using the step
  theorem’s paired call hypotheses;
- derive the public output theorem from `node_noninterference_outputs_raw`.

## Current Checkpoint

The helper split is now stable:

- `SecNLusNonInterferenceSupport.v` contains the low-observation and generated
  node-security support layers;
- `SecNLusNonInterferenceHelpers.v` contains the stable proof layer through
  `node_noninterference_vars_defined_step`;
- `SecNLusNonInterference.v` is reduced to the output-facing theorem layer.

At this checkpoint, `node_noninterference_outputs_raw` is intentionally left
admitted so the file boundary stays stable while the clock-sensitive theorem
shape is redesigned.

## Tomorrow's Route

The current evidence suggests that the raw output theorem should remain
two-clock, while the step theorem should stay one-clock.

So the next route is:

- keep `node_noninterference_vars_defined_step` unchanged;
- keep `node_outputs_raw_spec` with two clock streams `bk` and `bk'`;
- add an explicit prefix premise
  `clock_eq_upto bk bk' k := forall j, j <= k -> bk j = bk' j`;
- prove the callee-clock instances from the same low-output hypotheses used in
  the `EqApp` branches.

This is analogous to the reset route:

- resets need `reset_control_low_eq_upto`;
- call clocks should need `clock_eq_upto`.

The expected missing lemmas are:

- `clock_eq_upto_refl`;
- a semantic transport lemma from `sem_clock` plus environment equality;
- a generated-signature theorem showing visible source constraints still
  mention `s_clk`, so the new typing lemma
  `call_output_low_implies_clock_low` can actually be instantiated inside the
  `EqApp` branches.

The public theorem `node_noninterference_outputs` should then use the
reflexive clock case, while `node_noninterference_outputs_raw` carries the
more general internal premise.

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

## Active Theorem Stack

The theorem stack is now reset around the public noninterference theorem
first:

1. `node_noninterference_outputs`
2. `node_noninterference_outputs_raw`
3. any internal step theorem needed to prove the raw theorem

This is intentional.  The final theorem shape should stay stable, and the
proof-specific helper stack can then be rebuilt underneath it.

## Internal Proof Layer

The paired predicate `node_security n dlt_sig dlt_raw` remains the recursive
semantic invariant used by the proof.  The intended roles are:

- `dlt_sig` handles signature satisfiability and public low-observation;
- `dlt_raw` handles replayed raw constraints and caller locals;
- `node_outputs_raw_spec` is allowed as an internal proof target, but it
  should never appear in the final theorem statement as an assumption.

Any reintroduced step theorem should now be justified only as a proof device
under `node_noninterference_outputs_raw`, not as part of the public theorem
layer.

## Delayed Case Update

The `EqFby` branch is now organized around an outer induction on the instant
`k`, not around a timeless pointwise property.

That change was necessary because the delayed equation has two distinct proof
shapes:

- the current instant only depends on the current clock classification of the
  feeding annotated expression;
- the payload of the delayed value depends on the earlier prefix of the
  feeding stream.

The current file now makes that split explicit with four helper lemmas:

- `fby_eq_delay_prefix`
  shows that `fby` at time `k` only needs:
  1. equality of the feeding stream before `k`, and
  2. equality of current absence/presence at `k`;
- `sem_aexp_prefix_eq`
  reconstructs equality of the feeding annotated-expression stream on every
  earlier instant from low-equality of its free variables on that prefix;
- `sem_aexp_same_presence_from_clock`
  shows that equality of the current clock dependencies is enough to force the
  current annotated-expression stream to be absent in one run iff it is absent
  in the other;
- `eqfby_noninterference_delayed_pointwise`
  packages those two ingredients into the fixed-time noninterference step used
  in the theorem.

This also forced a matching change in the main theorem proof shape:

- `node_noninterference_vars_defined_step` is now driven by a well-founded
  induction on the instant `k`;
- inside that time induction, one uses `nl_node_causal_ind_defined` only for
  the current instant;
- the `EqFby` branch consumes earlier-instants equality through the outer
  induction hypothesis, while the current clock equality still comes from the
  causality induction.

This is the right split conceptually:

- causality handles current same-instant dependencies;
- time induction handles delayed dependencies.

## Current Status

The `EqDef` and delayed `EqFby` helper layers remain valid and should be
reused.  The current refactor point is narrower:

- the public theorem layer has been reset to the paper-facing shape;
- the final theorem is back to using `node_security` directly, without
  introducing an additional public wrapper;
- `node_noninterference_outputs_raw` is now reduced to one local remaining
  obligation: prove low-equivalence on `vars_defined n.(n_eqs)` under
  `dlt_raw`, then weaken that result to outputs;
- the next proof work is therefore to rebuild only the internal helper route
  actually needed for that `vars_defined` claim.

## Reset Design Decisions

Two reset-specific design decisions are now fixed and should stay explicit in
the thesis text.

### Typing-Level Reset Dependence

We accepted the conservative typing change that every simple NLustre equation
is implicitly at least as high as the node reset level:

- `EqDef` now generates a lhs of the form `([rst_ty] ⊔ ckty ⊔ cety)`;
- `EqFby` now generates a lhs of the form `([rst_ty] ⊔ ckty ⊔ ety)`.

The motivation is proof-theoretic, not cosmetic:

- the reset-aware noninterference proof already treats calls as depending on
  reset control;
- without threading `rst_ty` into the simple local constraints, the proof was
  forced to recover a global reset-dependence fact semantically in ad hoc
  places;
- by storing that dependency directly in the typing, low outputs now imply
  low node-reset level uniformly across all equation forms.

This is stronger than the least restrictive possible system, but it is still
security-neutral: it says that reset is an implicit control dependency of the
node, not that semantics itself depends on security.

### Reset Is A Control Input, Not A Plain Source Variable

A second design decision follows from the indexed semantics shape.

We should **not** model reset simply by extending the observable input set
from

- `map fst n.(n_in)`

to

- `map fst n.(n_in) ++ [rst_id]`.

That would blur two different notions:

- ordinary source inputs are compared by `history_low_eq`;
- reset alignment in indexed semantics is really carried by
  `bools_of`, `count`, and `mask`.

So the right theorem-side interface is:

- ordinary low-input equality remains a `history_low_eq` / `history_low_eq_upto`
  premise on `map fst n.(n_in)`;
- reset is handled by a **separate control-stream premise**, stating that when
  the relevant reset source is low, the induced reset counters agree on the
  observed prefix.

The file now contains a neutral helper definition for this intended premise:

- `reset_control_low_eq_upto`

but the main theorem stack has **not** yet been rewritten around it.  That is
deliberate: the design is recorded first, and the theorem interfaces should be
updated only in one coherent pass rather than half-threaded through one reset
branch at a time.
