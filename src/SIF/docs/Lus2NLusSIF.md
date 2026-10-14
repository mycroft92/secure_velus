# Lustre → NLustre security preservation (the Lustre leg)

## Goal

Security types for Lustre, generated from the elaborated source program, such
that noninterference proved for the transcribed NLustre program (see
`Non-interference-proof.md`) transfers back to the source.  The Lustre leg has
three parts: a constraint generator for Lustre (`SecLTyping.v`), preservation of
the generated signatures across the two normalisation passes (unnesting, then
`fby` normalisation), and the bridge to the NLustre signatures
(`SecLusNLusTranslation.v`).

## Files (build order)

| File | Content |
|------|---------|
| `SecLusTypes.v` | flow types for Lustre expressions (`LST`), `ambient`, `lconstrain` |
| `SecLNameInterface.v`, `SecLNamingTotality.v` | the Lustre naming pass (`generate_lnode_scoped_env`), its totality and its range/injectivity facts |
| `SecLTyping.v` | `assign_lexp_type`, the equation rules (`generate_l{gen,def,call,one,split,eqn,eqns}_constraint`), `generate_lnode_sig`, `generate_all_lsignatures'` |
| `SecLusUnnestingBase.v` | monotonicity of the security counter (`sec_le`, `minted`), rootedness, the window definitions `source_*_scoped_upto` |
| `SecLusUnnestingExpr.v` … `SecLusUnnestingNodes.v`, `SecLusUnnesting.v` | Leg U: the unnesting pass preserves the generated constraints (`preserves_on`), expression → right-hand side → equation → node; `call_weakens` and the lockstep induction over a program |
| `SecLusNormFby.v` | Leg I: the same for `fby` normalisation, and `normalize_signatures_weaken` composing the two legs |
| `SecLusTypingCorrectness.v` | structural facts about generated Lustre signatures (below) |
| `SecLusNormalization.v` | node instances of both legs against the naming of the largest program, the program-level lockstep, and `normalization_signatures_preserved` (below) |
| `SecLusNLusTranslation.v` | Lustre signatures entail the NLustre ones of the transcribed program |
| `SecLusConstraintExport.v`, `SecLusNonInterference.v`, `SecLusNonInterferenceStreams.v` | the dump driver and the noninterference corollaries |

All of these compile with no `Admitted`.

## Facts about generated signatures (`SecLusTypingCorrectness.v`)

Per node, against the naming of the node's own program:

- `generate_lnode_sig_good` — one constraint per output, targets exactly the outputs;
- `generate_lnode_sig_scoped` — every name mentioned is in the signature scope;
- `generate_lnode_sig_scope_nodup` — the scope has no duplicates;
- `generate_lnode_sig_rooted` — the clock and reset formals are sources of every constraint.

Per program:

- `generate_all_lsignatures_inv` — the four facts above hold for every signature the driver
  publishes, by a lockstep induction over the naming run and the signature run
  (`lsig_inv`, `lsig_step`).  Different nodes cannot interfere because the
  counter separates them: an accumulator's scopes lie below the naming state
  at the node being typed, the node's own names above it.

The naming facts the fold reads off the run are `generate_local_env_for_lnode_facts`
(injective, values are `sec` names inside the node's stretch of the counter,
the two auxiliary names first).

## The preservation interface

`call_weakens G1 G2` says that, for every instantiation that is fresh
(`call_subst_fresh`) with distinct outputs, the block built from a signature of
`G1` is entailed by the block built from the same-named signature of `G2`, and
the two signatures have the same scope.  It is transitive, and
`sig_call_weakens_from_good` produces its per-node step from the signature
facts above.  Freshness is *not* assumed for every instantiation the block
builder accepts (it accepts actuals containing a callee formal); it is asked of
the instantiations a run makes:

- `eapp_fresh_prop`, `lcall_fresh_prop` — the call rules of the typing run and of
  the equation rules, from a start state at or above the node's naming state
  `lo`, with distinct left-hand sides and a reset type of the two shapes the
  rules use.  Proved: `eapp_fresh_prop_holds`, `lcall_fresh_prop_holds`.

The Section hypotheses of Leg U (`SecLusUnnestingEquations/Streams/Nodes.v`)
are restricted to the source node's own variables, expressions and states:

| Hypothesis | Guard | Discharge |
|------------|-------|-----------|
| `source_{types,lexps,lexps_carried}_scoped_upto` | `wc_exp P vars`, start state ≥ `stLo`, end ≤ `stF` | `source_*_scoped_upto_holds` (from `lexp_scoped_tgt_all_wc`) |
| `clk_types_scoped` | `wc_global P`, `wc_exp`, `clk_src` (or a source variable's clock) | `clk_types_scoped_holds` |
| `env_range_scoped` | the variable is a source variable | by definition of the declared names |
| `sig_actuals_fresh` | actuals are caller-side names (`caller_name`) | `sig_actuals_fresh_holds` |
| `clk_types_defined` | — | `clk_types_defined_holds` under `no_anon_clocks` |

`scope` is the declared names of the source node plus the window
`minted stLo stF`; the images of the variables unnesting creates are
deliberately outside it.

The scalar-ambient chain (`carries_*`, `unnest_node_step`) quantifies over every
program and carries `scalar_wcg : forall P, wc_global P`; it is kept for the
lemmas it shares, but the pointwise chain (`*_streams`, `unnest_node_step_streams`)
is the one to instantiate.

## The program level (`SecLusNormalization.v`)

The source program `G`, its unnesting `G1 = unnest_global G` and its
normalisation `G2 = normfby_global G1` are all typed against the naming run of
`rev G2`, the program that declares the most variables.  A node of a smaller
program then meets an environment with extra keys, so the fold facts that read
the environment's whole range (scoped, rooted) are redone against the node's own
variables, guarded by clocking (`lsig_step_ext`).

- `lsig_inv`, `lsig_step_ext`, `generate_all_lsignatures_weakens_ext` — the
  lockstep.  Its relation `R P nS nM nall` carries the callee program `P` (the
  source nodes already processed, `Forall3P`) and an invariant `Jinv` of the
  target accumulator against it.
- `unnest_instance`, `normfby_instance` — one node of each leg.  Unnesting is
  stated with `scope`/`scope0` (raw entailment versus interface) and the
  extended-environment trick: freshness and rootedness are read against
  `env_images env`, not the node's declared variables.
- `normfby_clocks_pass_fact` — the clocks of the variables `fby` normalisation
  creates are over declared variables.
- `anon_names_unnested`, `anon_names_normalized`, `unnested_node_src`,
  `normalized_node_src` — the pass outputs have no anonymous streams and satisfy
  `src_exp`.
- `RU`, `RI`, `RU_facts`, `RI_facts`, `stepU`, `stepI`, `build_U`, `build_I` —
  the node relations of the two legs, one lockstep step each, and the builders of
  `Forall3P` from the structure of `unnest_global`/`normfby_global`.
- `normalization_signatures_preserved` — `call_weakens GS GM /\ sigs_preserved GS GM`.
- `source_signatures_good` — every source signature is good with a
  duplicate-free scope.
- `Check.source_signatures_entail_nlustre` (`SecLusConstraintExport.v`) — the
  signature half of the composition: `Signature_entails GS GN`.

## Assumptions and open items

1. **Source expressions (`src_exp vars AN`) and nested calls.**  The call case
   reads two facts that are properties of the elaborated program: a nested call's
   output names are the node's anonymous streams (`AN`), which are not among its
   declared variables (`n_nodup`), and the clocks of a call's arguments and of its
   reset are over the declared variables (`src_loc`, `nested_src`).  `src_exp`
   carries them through the pointwise chain.  Nested calls are supported: unnesting
   *reuses* a nested call's anonymous name as the name of a variable it declares, so
   under the shared naming (of the normalised program) that name is an environment
   key, and the typing run still mints a fresh name for the call's result.  The
   chain therefore never asks the environment to agree with a nested call's
   stream: "a named argument carries its own name" is asked of every name except
   `AN` (`bad`), and the one place a name from a formal's clock is looked up
   (`Hbadok`, from `sub_clock_vars_not_anon`) is shown not to be in `AN` because the
   arguments' clocks are over declared variables.  The hypothesis `env_anon` is
   now `AN` disjoint from the declared variables.  What remains excluded: a call
   whose arguments are clocked on the output of another nested call (the clock then
   mentions an anonymous name; `source_guard` fails).
2. (merged into 1.)
3. **Node instantiation of both legs** is done (`unnest_instance`,
   `normfby_instance`).
4. **`sig_inputs_ok GL P`** is proved for the signatures the lockstep generates
   (`sig_inputs_step`, `node_sig_inputs`), so the program theorem has no hypothesis
   about it.  It was restricted to a callee's *inputs* (its only consumer,
   `call_augment_dep_concrete`, reads only those), which is what makes it true
   without a causality assumption: the clock variables of an input are inputs, so a
   constraint's own target, which `simplify` removes from its sources, is never one
   of them.  The proof: `ldef_ok`/`call_eq_icl`/`leqn_icl`/`leqns_icl` show every raw
   constraint closed (`icl`) with targets outside the input names (`ntg`); the call
   case is `CALLS.generate_constraints_icl`, which chains the six substitution stages
   modulo the call's clock type and transfers to the plain block through
   `generate_constraints_same_inp`; `collapse_ok` and `simplify_ok` preserve closure
   because the eliminated names are never input names or the base name (`zset`).
5. **Composition theorem.**  Signature half: `Check.source_signatures_entail_nlustre`
   and its reading for policies, `Check.source_policy_realised`: a valuation satisfying
   a source signature's stored constraints extends, agreeing on the signature scope, to
   one satisfying the transcribed NLustre signature.  What is **not** done is the
   transport of `lnode_security` itself (the raw-constraint satisfaction of each node
   and the callee clauses at the induced valuations) from the source to the normalised
   program: the node-level legs prove entailment of stored signatures, and the
   security predicate looks at raw constraints and at every call site's instance.
   Noninterference of the compiled program is therefore obtained by
   `lnode_noninterference_outputs_generated` at the normalised program, with its
   security data as the hypothesis it already is.
6. The signature-fold facts for source nodes typed against the naming of the
   normalised program carry only `good` and the duplicate-free scope
   (`source_signatures_good`); scoped and rooted are used for the unnested and
   normalised programs, whose naming is their own or a superset.

## Pitfalls that cost time

- `eq_refl` / `eq_sym` are shadowed by `Env`'s; use `Logic.eq_refl` / `Logic.eq_sym`.
- `rewrite` fails between two facts that print identically when the two `snd`s
  have different (convertible) type arguments (`ST` vs `list ident`); `destruct`
  the pair and `cbn [snd]` instead.
- A bare `findST` in the Lustre files is `SIG`'s, not `SymTypes'`.
- `length` is `String.length` in these files; write `List.length`.
- A bare `subst` after `inversion` can eliminate the variable you meant to `subst`
  later; name the equations.
- Section variables are generalised only when used, in declaration order; positional
  hypothesis lists (`Local Notation`s, explicit applications in `Nodes.v`) must
  follow.
