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
| `SecLusConstraintExport.v` | the dump driver and the signature half (`source_signatures_entail_nlustre`, `source_policy_realised`) |
| `SecNLusNodeSecurity.v` | `node_security_exists_pos`, `policy_node_security`: the `node_security` witness is constructed from a signature-satisfying valuation |
| `SecLusNormTransport.v` | transport of `lnode_security` along a normalisation pass: the abstract contract `pass_contract` and the proved induction `lnode_security_transports` (below) |

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

   **Transport, step 2 (`SecLusNormTransport.v`, done).**  The generic half is proved:
   `lnode_gen` is `lnode_security` with the callee clause abstracted
   (`lnode_security_gen`, `lnode_gen_security`, `lnode_gen_mono`), and given
   `pass_contract` for a node correspondence `rel` and a valuation relation `R`,
   `lnode_security_transports` gives security of the target at any `R`-related
   valuations by induction on the callee structure; `lnode_security_transports_two`
   chains unnesting with `fby` normalisation.  `R d d'` is meant to say: `d'` agrees
   with `d` off the minted names and satisfies the target program's constraints, which
   pins each minted name to the type of the expression it replaces.
   The contract is stated for *every* `R`-related target valuation, not a chosen one:
   at a call site the target induces its own callee valuation and the induction needs
   security of the callee there.  (A first version used a function `Phi` and equality
   of `lat_valuation`s; it was dropped because the pass lemmas only produce an
   existential witness, and `Phi` cannot be extracted from one.)
   **Not done** (step 3): (a) `pass_contract` for each pass; (b) `R`-existence, an
   `R`-related valuation for each secure source valuation, which is what
   `node_carries` gives per node but needs combining across the whole program;
   (c) a check that the names a pass mints in different nodes do not clash, since a
   callee's locals are read through the caller's valuation, so one valuation must
   satisfy every node's constraints at once.  For (a) the existing `preserves_on scope`
   statements are not enough: call valuations read argument types, which mention
   locals and anonymous streams outside the interface, so `node_carries_preserves`
   must keep its `agree_off` conclusion.  The call-argument limit (arguments clocked on
   another nested call's output) stays as the `source_guard` hypothesis; picking it up
   is a separate task.
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

## Branch `anon_clock_names`: removing the call-argument clock limit (work in progress)

Goal: drop the `source_guard` part that asks call arguments and resets to be clocked
over declared variables, with no new assumption, and prove the noninterference
transport.  **Not finished; the branch does not build past `SecLusTypingCorrectness.v`.**

### The rule change (`SecLTyping.v`, `assign_lexp_type`, `Eapp`)
Only the result names change.  `fresh_idents (length anns)` became `out_idents anns`:
a flow whose annotation carries a name `w` (`stream_name = Some w`) and that has an
entry in `env` is typed by `env[w]`; every other flow gets a fresh name as before.
This is what the call equation unnesting produces does (`generate_lcall_constraint`
looks its outputs up in `env`), so the two runs now agree on a named flow, and a
later clock `Con ck w b` (typed through `assign_clk_type env`, i.e. `env[w]`) is tied
to the call that produces `w`.  Before, nothing tied `env[w]` to the minted name.
The signature's elimination set grows to `locals ++ anon_images env n ++ minted`,
where `anon_images` are the `env` names of `anon_in_eqs n.(n_eqs)`; otherwise the
stored constraints would leak them.

### Facts the change rests on (all read off the node, none assumed)
`n_nodup` keeps anonymous names apart from declared ones, `env_injective`, and
`anon_in` collects exactly the named streams of nested calls (a top-level call's own
annotations are excluded, matching `eq_named_in`).

### State of the build
Compile, in order: `SecLTyping`, `SecLusUnnestingBase` ... `SecLusUnnestingNodes`,
`SecLusUnnesting`, `SecLusNormFby`.  `SecLusTypingCorrectness.v` is migrated up to and
including `generate_lnode_sig_good` (the targets/shape/published and rooted families
carry a window predicate `ns_win NI` and a premise `named_in`/`eq_named_in`).

### Remaining, in dependency order
1. `generate_lnode_sig_scoped` (TypingCorrectness): `Hrange` and `decl` must include
   `anon_images`; a name in `anon_images` that occurs must be a target (needs a lemma
   that names in a flow type are declared or targets of its carried constraints,
   with the anonymous images not counted as declared); `NoDup (anon_images ..)` and
   its disjointness from `locals`.
2. The rest of `SecLusTypingCorrectness.v`: `RawFresh` (`eapp_fresh_prop_holds`,
   `lcall_fresh_prop_holds`: a named result is not minted, its freshness against the
   callee scope comes from `name_above`), `SourceScoped`, `ClkScoped`.
3. `SecLusNormalization.v`: every `locals ++ minted` site (see `grep`), the node
   instances, and replacing `source_guard`'s clock clause by the new facts.
4. `SecLusNonInterference.v` and `SecLusNormTransport.v`: the `SecureLNode`
   constructor's signature equation takes the new elimination set.
5. The transport itself (`pass_contract` for both passes, `R`-existence): see the
   transport section above; the carried `agree_off` facts are unchanged by this branch.

### What would make this need an assumption
Item 1's "occurs implies target" lemma and the freshness of a named result against
a callee scope are the two places a hypothesis could appear.  If either needs more
than `n_nodup`, injectivity and the existing typing hypotheses, that is a new
assumption and must be reported, not added silently.

### What `generate_lnode_sig_scoped` needs (findings, 2026-10-18)
Adding the named streams' environment names (`NI`) to the elimination set is only sound
if every `NI` name that occurs in the raw constraints is also a target of them
(`simplify` skips an eliminated name that is not a target and would leave it behind).
That needs two facts that are not in the build yet, both true of well-formed programs:
1. **Provenance of anonymous names in clocks.**  For `wc_exp P vars e`, every name in a
   clock of `e` is a declared variable or a name in `fresh_in e` (a stream named by a
   call inside `e`).  `LClocking.v` states this design ("the scope of a fresh clock is
   limited to its column"), but it is not proved; it needs an analysis of
   `WellInstantiated`/`instck` and of how the call's base clock `bck` is fixed by the
   callee's inputs.  The current `source_guard` clock clause is exactly the assumption
   of this fact for call arguments and resets.
2. **Occurrence implies target.**  Names of `NI` in a flow type or a carried
   constraint's sources are targets of what the flow carries.  With (1) this is an
   induction like `lexp_scoped_tgt_all` with the declared names only (not `NI`) in the
   scope, and the call's base-clock type scoped in `decl0 ++ tgt_names (carried argts)`.
   It uses `wc_Eifte`'s `0 < length tys`, since a branchless conditional would drop its
   scrutinee's carried constraints.
Neither is an assumption: both follow from `wc`/`wl`.  But neither is a small lemma, and
the equation-level families (`lvars`/`lcall`/`ldef`/`lgen`/`lone`/`lsplit`/`leqn`/`leqns`)
would each have to carry them, as they already carry `named_in`.

### Separation of the two goals
The noninterference transport (`pass_contract`, `R`-existence) does not depend on
removing `source_guard`.  It can be done on `constraint_gen` with the guard in place and
lifted afterwards.


### Progress on branch `anon_clock_names` (2026-10-19) and what is left

Done, with no new assumption (all compile, `SecLusUnnestingBase` ... `SecLusTypingCorrectness`):
- `SecLusClockNames.v`: `wc_exp_clock_names` -- every name in a clock of a well-clocked
  expression is a declared variable or a stream named inside the expression (needs only
  `wc_global` and `wc_env`).  This is the fact the guard's clock clause assumed.
- Naming pass: the anonymous streams of a node's calls get a security name in a last step,
  after the allocation shared with NLustre (`to_node_local_env` still holds; proved
  `to_node_anon_nil`).  `env_key_not_anon` is gone.
- Typing: `out_idents` (named results typed by the environment's name, refusing duplicate
  result names), `lexp_named_tgt_all` (a named result is a target of what the call
  carries), `clk_scoped_named`, `lexp_scoped_tgt_all_wc` without any clock hypothesis,
  `clk_types_defined_wc`, rooted/good signature theorems with `anon_images`.
- Guard: `src_loc` no longer asks arguments to be clocked over declared variables;
  `source_guard` is a proved lemma (`source_guard_holds`, `wc_global_source_guard`).
- Leg U call cases (Streams/Equations): types-defined and named-coverage no longer use the
  guard.

Not done, and bigger than expected: **Leg U for named flows.**  A named nested-call result
is typed by `env[w]`, which is also the security name of the variable unnesting creates for
`w`.  Leg U's node theorem assumes the opposite on two counts: the names a run "moved" are
outside `scope` (`Hmv`), and the source types are inside it.  For a named result both are
about the same name.  The call case (`carries_Eapp_streams`, Streams) must be redone with
shared names: `new_ids` has to exclude the anonymous names, `call_outputs_witness` has to
leave shared positions alone (the ambient is already below the result, by the callee's
rootedness), and `unnest_instance`/`normfby_instance` take `scope` = declared + anonymous
images + window.  `SecLusNormalization.v` does not build until that is done; the guard
itself no longer needs to be assumed.


### Status 2026-10-19 (late): the guard is gone, the Lustre leg builds

`SecLusUnnesting*`, `SecLusNormFby`, `SecLusTypingCorrectness`, `SecLusNormalization`,
`SecLusNLusTranslation`, `SecLusConstraintExport`, `SecLusNonInterference(Streams)` and
`SecLusNormTransport` compile on branch `anon_clock_names`.  `source_guard` is a theorem
(`wc_global_source_guard`); `normalization_signatures_preserved`, `source_signatures_good` and
`source_signatures_entail_nlustre` no longer take it.  No new assumption was added.

What changed to get there (beyond the earlier sections):
- Named nested-call results share their name with the variable unnesting declares for them:
  `moved_by` excludes the anonymous names, the call case uses `call_outputs_witness_sh`,
  and the instances take `scope = decl ++ anon_images ++ minted`.
- `AN_apart_fresh` is stated for `fresh_ident norm1` only (the all-prefix form was false).
  To prove it, `FRESHKERNEL` (`src/Lustre/Normalization/Fresh.v`) gained the provable fact
  `fresh_ident_gensym` (a generated name is `gensym pref n`); this is a theorem of the concrete
  kernel, not an assumption, but it is the one edit outside `src/SIF`.
- `anon_names_declared_M`: a source node's anonymous names are declared variables of the unnested
  node (proved by induction over `unnest_exp`), which supplies the environment keys.
- Signatures eliminate `locals ++ anon_images env n ++ minted`; for unnested and normalized
  nodes `anon_images` is empty.

Still to do: the noninterference transport itself (`pass_contract` for both passes, `R`-existence),
then a full clean build of the files downstream of `Fresh.v` that were not rebuilt here
(`VelusCorrectness`, `NLCorrectness`, `SecNLusConstraintExport`, `SecStc/ObcConstraintExport`).


### Status 2026-10-20: nested-call clause in `lnode_security` (staged: named results first)

`SecureLNode` (and its copy `GenLNode` in `SecLusNormTransport.v`) now has a third call clause
that covers every call *nested* inside an equation's expression, plus a premise
`Forall (apps_named ty_env) args` on the two existing top-level clauses.  The clause says the
callee is secure at the valuation the nested call induces, the argument types, reset level and
base clock being read by replaying `assign_lexp_type`'s call case (`app_data`) and the result
names by `out_idents`.

Why `apps_named`: a result flow the elaborator left unnamed is typed by a name the security
monad mints, which depends on where in the run the call sits; a clause quantifying over an
arbitrary state for it would be false.  `apps_named ty_env e` says every call inside `e` has all
result flows named with an environment entry, so the valuation is state independent.  The
predicate therefore makes no claim about calls with unnamed results.  This is *staged*: it is
not yet an extra premise of any end theorem; the transport proof (`pass_contract`) will need it
of the source program, and removing it (tracking call positions in the run) is the second stage.
Transcribed nodes meet the new premise vacuously (`to_lexp_apps_named`).


### Finding 2026-10-20: minted locals break the inherited-raw-valuation callee clause

Counterexample to transporting `lnode_security` (and to `node_security` of the normalised
program) along unnesting, with no nested call involved.  Take `c(a,b) = c2(ite(b,a,0))` with
`c2` the identity-like node (`in ⊑ out`), so `c` has no locals and its stored signature is
`{a,b} ⊑ o`.  Unnesting gives `y = ite(b,a,0); o = c2(y)`, so `c'` has the local `y` with raw
constraints `{a,b} ⊑ y` and `y ⊑ o`.  A caller `T` that calls `c` at two sites, `(a=H, o=H)` and
`(a=L, o=L)`, has a source witness (every site satisfies `{a,b} ⊑ o`).  The callee clause hands
`c'` the caller's raw valuation with only the signature names overwritten, so `y` is one value
for both sites, and `H ⊑ y ⊑ H` and `L ⊑ y ⊑ L` cannot both hold.  The normalised program has no
`node_security` witness although the stored signatures are preserved and noninterference is
semantically true.  The cause is the clause (callee locals inherited, not re-chosen per
instantiation), not the transport proof.


### Status 2026-10-20 (later): callee raw valuations are chosen per call site (branch `per_call_raw_valuation`)

To remove the monomorphic-local obstruction (previous finding), the callee clause of
`node_security` (`SecNLusNonInterferenceSupport.v`) no longer inherits the caller's raw
valuation.  It is now the mutual inductive `callee_secure`: the callee is secure at the
signature valuation the call induces, for *some* raw valuation `w` that agrees with the induced
one on the callee's signature scope (`signature_scope`).  The callee's locals are free; each call
instance may take its own valuation of them.  `lnode_security` has the same shape
(`lcallee_secure`), and `lnode_gen` takes `exists w, agree_on .. /\ K callee .. w`.

Proof changes: `node_noninterference_outputs_raw` is by the mutual scheme `node_security_mind`;
the four call-site blocks in `SecNLusNonInterferenceHelpers.v` / `ClockedStep.v` obtain `w` from the
induction hypothesis and move low-equivalence between the induced valuation and `w` with
`low_var_agree` / `history_low_eq_upto_agree` (observed names are in the callee's signature
scope).  The reset hypothesis `Hresetout` lost its `k_reset` premise (the spec does not depend
on it).  Compiled: Support, Helpers, ClockedStep, SecNLusNonInterference, SecStcNonInterference,
SecObcNonInterference, SecLusNonInterference(+Streams), SecLusNormTransport.  Not yet rebuilt:
everything else downstream (full clean build pending).

What this leaves for `pass_contract`: `R` must make the target's argument variables equal to the
source's argument levels on the minted names (tight), so that the target's induced callee
valuation agrees with the source's on the callee's signature scope; the callee's own minted
locals are then re-chosen per call (the relation between `w` and its target witness `w'` is
`R`-existence for the callee).  Next: tight `R` for unnesting, the tight form of the carries
theorem, then `pass_contract`.


### Finding 2026-10-20 (evening): the tight `R` is not available for hoisted control arguments

Reading what `node_carries` really builds shows the "tight R" plan above is not enough as stated.
Unnesting binds a control argument `e` of a call to a fresh `y` with the equation `y = e`; the
generator types that equation with the ambient (`generate_ldef_constraint`: `rst ⊔ clock ⊔ lvl e ⊑ y`),
and the valuation `node_carries` produces is exactly `y := rst ⊔ clock ⊔ lvl e`
(`SecLusUnnestingExpr.v`, `upd b (hm_ext dlt1 (merge (merge [rst_ty] ckty) (fst tf)))`).  The source
call, by contrast, types its argument as `lvl e` with no ambient (`assign_lexp_type`, `Eapp` case,
and `generate_lcall_constraint`).  Hence `y` can never equal the source argument level when
`rst ⊔ clock ⋢ lvl e`: any valuation satisfying the target constraints has `y ⊒ rst ⊔ clock ⊔ lvl e`.
The callee valuation induced by the target call is then *above* the source's on `s_in`, and it is
not the case that `R` (agreement off minted names) relates the two induced valuations.

Security at the higher input valuation is the *stronger* statement (fewer low inputs), true because
the stored signature has `s_clk ⊑ out` and `s_reset ⊑ out`, but it is not an instance of the source
clause.  Ways out, in order of preference:
 (B) read the callee clause at the call's ambient-joined inputs, `arg ⊔ clock ⊔ reset`, on both
     the NLustre and Lustre sides (the caller's NI proof only gets easier: the callee's low-input
     hypothesis shrinks); needs `signature_satisfied` at that valuation, i.e. the fact that generated
     signatures put `s_clk`/`s_reset` below every output;
 (C) a raise lemma `lnode_security d => lnode_security d⁺` proved by the mutual induction;
 (A) change the source call rule to join the ambient into argument types (also breaks the syntactic
     agreement with NLustre's call rule, so not recommended).


### Status 2026-10-20 (night): transport dropped; two defects found and one fixed

**1. The callee clause was unsatisfiable (fixed).**  After the per-call raw witness change,
`CalleeSecure` still asked `node_security callee dsc w` with `dsc` the signature-level valuation
the call induces.  Off the callee's scope `dsc` holds whatever the caller's valuation holds at the
callee's local names, and the callee's own call clauses read argument levels at *both* `dsc` and
`w` and need them to agree, so for nested calls with local arguments no witness exists.  The clause
is now `node_security callee w w` (`SecNLusNonInterferenceSupport.v`; the call-site blocks in
Helpers/ClockedStep read `dlt_w dlt_w`; the Lustre `LCalleeSecure` likewise).  The whole NLustre NI
chain (Support, Helpers, ClockedStep, NonInterference, Stc, Obc) and `SecLusNonInterference(+Streams)`
recompile.  `SecureLNode`/`GenLNode` also said `simplify raw` where `generate_lnode_sig` publishes
`simplify (collapse raw)`.

**2. Security data can be constructed, so the transport is not needed.**  With (1), `node_security`
of the normalised program follows from signature satisfaction alone: `signature_satisfied_replays_raw`
gives the raw extension, `generate_constraints_complete_good` gives the callee signature at the
induced valuation, and the callee is taken at its own witness by induction on the call structure.
`source_policy_realised` already takes a source policy to a valuation satisfying the NLustre
signature.  So `pass_contract`, tight `R`, `R`-existence and the raise lemma are not on the critical
path.  `SecLusNormTransport.v` and `SecLusPadding.v` (padding of raw constraints, the raise lemma
`lnode_security_raise`) were written and compiled before this was seen; they are no longer in
`vfiles` (`SecLusNormTransport.v` does not compile against the new `LCalleeSecure`).  Delete or
keep as reference.

**3. The program-level hypotheses are inconsistent for call-bearing programs (open).**  The NI
theorems (`node_noninterference_outputs`, `SecStcNonInterference`, `SecObcNonInterference`, the
Lustre corollaries, `Check.source_signatures_entail_nlustre`) take both `Ordered_nodes all_nodes` /
`wc_global all_nodes` (a callee lies in the *tail*) and `generate_all_signatures_scoped_env all_nodes
= OK G` (the fold processes the list head first, so a node's callees must precede it).  For a
program with a call these cannot hold together: the caller is processed against an accumulator that
does not yet contain its callee, and the generator answers "Signature not found".  The totality
theorem and the dump drivers use `rev all_nodes`, which is the right list; the NI chain does not.
`docs/Obc-noninterference-proof.md` and `docs/signature-generation-totality.md` already flag this as
"the `all_nodes` / `rev all_nodes` mismatch".  Until it is settled every end theorem is vacuous on
programs with calls.  The fold lemmas (`generate_all_source_signatures_*_env'`,
`SecNLusStcTranslation` folds, `SecLusNLusTranslation` lockstep) take `wc_global nodes` of the folded
list only to extract a per-node `wc_node`; they generalise to `Forall (wc_node P) nodes` for the
whole program `P`.


## Status: node_security constructed, Lustre NI files removed

- `SecNLusNodeSecurity.v` (no admits) proves `node_security_exists_pos` by strong induction
  on the position of the node in `rev all_nodes`: the raw valuation comes from
  `signature_satisfied_replays_raw`, the call and reset clauses are read off the satisfied
  instantiated constraints, and callees are taken at their own witnesses.  `policy_node_security`
  starts from `signatures_preserved sgS sgN` and a valuation satisfying the source signature;
  no security-data hypothesis is involved.
- `SecLusNonInterference.v` and `SecLusNonInterferenceStreams.v` (and earlier the transport and
  padding files) are deleted; they used the old non-reversed statements and are superseded.
- All generation/naming hypotheses are over `rev all_nodes`, so programs with calls are no longer
  vacuous.  `Check.source_signatures_entail_nlustre` takes `NL.Ord.Ordered_nodes P` explicitly.
- Not yet done: a single theorem composing `policy_node_security` with
  `class_security_from_node_security` / `class_noninterference_outputs` (they live in separate
  functors; the composition needs a functor instantiating both), and a full clean build.

## Status: end-to-end theorem

`SecEndToEnd.v` (functor over the Obc chain's parameters plus `SECOBCNONINTERFERENCE`) proves
`policy_class_noninterference`: for a node `n` in `rev all_nodes`, a source signature `sgS`
with `signatures_preserved sgS sgN` against the generated NLustre signature, and a valuation
`d1` satisfying `sgS`, there is `w` agreeing with `d1` on the scope of `sgS` such that the
Obc step method of the compiled node is low-equivalent on outputs for low-equivalent inputs
at levels `w`.  Hypotheses are the generator/naming equations, the compiler's own
well-clocked/well-scheduled facts and causality; no security-data hypothesis.
`SecNLusNodeSecurity` now takes the NI module as a parameter so `node_security` is shared.
Full SIF rebuild (vfiles order) passed before this file was added (56 min).
