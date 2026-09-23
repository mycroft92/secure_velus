# SIF for Lustre: refinement security types and Lustre→NLustre preservation

Target branch: `Lus2NLusSIF`.

> **Where things stand is in one place: [Leg U — current state](#leg-u--current-state).**
> That section is rewritten in place and is the only Leg U status to trust.
> Everything below it dated `2026-09-xx` is history, kept for the reasoning,
> and may describe designs that were later found wrong.  Each such section
> says so at its head.

## Leg U — current state

*Rewritten in place. Last checked against a clean `make -j1` on 2026-09-22.*

A design recorded here is marked either **[verified]** -- it has been checked
against the actual definitions, or better, compiled -- or **[untested]** --
it is a plan that has not yet met the definitions.  Two designs for the call
case have already died on contact with `subst_constraints_inp_map`, so the
distinction is the point, not decoration.

### Proved

*Scalar contract* (`carries_at`, one ambient per equation) -- complete:

  * `carries_exp`, `rhs_carries_exp` (`SecLusUnnestingEquations.v`)
  * `eqn_carries_all : forall P eq, eqn_carries P eq` -- **unconditional**;
    the old `Forall eqn_covered` premise is gone from both list inductions
    and from the node theorem
  * `eqns_carries`, `eqns_carries_amb`, `node_carries`,
    `node_carries_preserves` (`SecLusUnnestingNodes.v`)
  * `unnest_node_fields`, `unnest_node_equations_nodup`, and the moved-name
    freshness corollaries

*Pointwise contract* (`carries_at_streams`, one ambient per stream) -- every
form but the call: `Econst`, `Evar`, `Eunop`, `Ebinop`, the list fold,
`Ewhen`, `Emerge` and `Eite` in both their control and lifting forms,
`Efby`, `Earrow`.

*Groundwork for the call* (`SecLusUnnestingBase.v`):

  * `clock_prefix`, `assign_clk_type_prefix_incl`,
    `assign_clk_type_clock_closed` -- language-independent
  * `assign_exp_type_clock_closed`, `assign_cexp_type_clock_closed` -- these
    are the **CoreExpr** forms, so they serve the NLustre generator, *not*
    Leg U's critical path; their structure transfers to the Lustre forms
    case for case
  * `satisfiable_of_incl`, `satisfiable_same_names`,
    `listSatisfiable_same_sources`
  * `fresh_insert_domain`, `fresh_map_list_domain`,
    `fresh_map_list_domain_empty`,
    `generate_local_env_for_lnode_domain` (`SecLNameInterface.v`) -- the
    naming environment's domain is the two aux names plus the node's
    declared variables, since each node's env is built from `Env.empty`.
    This is the first of the two construction lemmas that replace the
    would-be side condition on programs.
  * `subst_ident_in_constraints_members`,
    `subst_constraints_inp_map_members` -- a *flat* description of what the
    input map produces: the source of a substituted constraint holds exactly
    the non-formal names the original held, together with the actuals of
    every formal the original mentioned.  Stating it this way avoids
    reasoning about the fold's intermediate states, which is where both
    earlier designs came apart.
  * `combine_grow_l`, `combine_grow_r`,
    `subst_constraints_inp_map_augment` -- **step 1 below, done**:
    instantiating with augmented actuals yields constraints with exactly the
    same members, provided every name an argument gains is one that some
    other argument the constraint already mentions contributes

### Assumed, not yet discharged

Section hypotheses on `GL` in `SecLusUnnestingEquations.v`: `env_inj`,
`sig_good`, `sig_nodup`, `sig_scoped`, `sig_actuals_fresh`.  A sixth, the
dependency property below, will join them.  All are discharged together at
the program level, which is not written.

`node_carries` also still carries the two ambient premises that the
per-equation statement cannot discharge; removing them is what the pointwise
contract is for.

### The open step: the call case

**The gap** *[verified]*.  `generate_constraints_mono_sem` transports
satisfaction under one ambient `amb`, which must be above every argument's
ambient (clause 3) and below every result's (the conclusion).  Both cannot
hold: clocking instantiates all formals from one base `bck`, but an input may
be declared on a strictly deeper clock than an output -- `f(x when c)` with
the input on a subclock and the output on `Cbase`.

**Two designs that failed** *[verified wrong]*:

  1. per-input ambients threaded through `cs_chain`/`cs_out`/`cs_le` -- a
     vector through the whole chain;
  2. weakening clause 3 in place, on the grounds that `cs_chain`'s third
     clause already absorbs extra slack.  True at the end of the fold, false
     during it: the fold substitutes formals one at a time, and `a_j` is
     built from the actuals of *other* positions -- `j`'s clock variables --
     which are not yet substituted when position `j` is.

**The design in force** *[partly verified]*.  Leave
`generate_constraints_mono_sem` untouched -- two other proofs use it -- and
instantiate the signature on the source side with augmented argument types

    inp1''_j  :=  inp1_j  joined with the actuals of j's clock variables

keeping the uniform ambient `amb := call_amb = [rst_ty] ⊔ assign_clk_type bck`.
Three obligations:

  * clause 3 holds uniformly, since `a_j = [rst_ty] ⊔ assign_clk_type(clock
    of arg j)` and that clock is `bck` extended by exactly `j`'s clock
    variables, so `merge a_j inp1_j ⊆ call_amb ∪ inp1''_j`  *[untested]*;
  * `amb_pair` holds, since `bck` is a prefix of every output clock --
    `assign_clk_type_prefix_incl`  *[verified: the lemma is proved; its
    application to the call is untested]*;
  * the augmentation changes nothing, since by the dependency property any
    constraint mentioning input `j` already mentions `j`'s clock variables,
    so the larger actuals add no member to any source, and
    `listSatisfiable_same_sources` carries satisfaction across
    *[verified: `subst_constraints_inp_map_augment` proves exactly this,
    with the dependency property as its one remaining premise]*.

**A near-blocker, and why it is not one, 2026-09-23.**  The augmentation
argument needs the actual at a clock position to contribute its own security
name to its type.  That does *not* follow from `wc_exp`: of the Lustre forms
only `Evar` and `Eapp` may carry an nclock name (`wc_Evar` pins it to the
variable; everything else is forced to `None` or carries
`Forall unnamed_stream`), and `wc_equation` constrains only *top-level*
names, not expressions nested inside a call's arguments.  So on the face of
it a nested call could sit at a clock position carrying a name `w`, with
nothing putting `[env w]` in its type while `clocks_covered` still demands
it.  *[verified: `LClocking.v`, `ClockDefs.v`]*

The exclusion does not need a new hypothesis on programs.  It follows from
well-formedness the `node` record already carries, plus the domain of our own
naming pass:

  1. `anon_in (Eapp f es None _) = fresh_ins es`, and
     `fresh_in (Eapp _ _ _ anns)` contains `anon_streams anns`.  So a
     *nested* call's named output lands in `anon_in_eq` of the equation, and
     hence in `anon_in_eqs n_eqs`.  *[verified, `LSyntax.v`]*
  2. `n_nodup : NoDupMembers (n_in ++ n_vars ++ n_out ++ anon_in_eqs n_eqs)`
     is a **field of the node record**, so such a name is never a declared
     variable -- by construction, for every node, with no hypothesis.
     *[verified, `LSyntax.v`]*
  3. `generate_local_env_for_node` builds each node's environment from
     `Env.empty` over `[clk_name; rst_name] ++ map fst (n_in ++ n_out ++
     n_vars)`, so `Env.find w env = Some _` forces `w` to be an aux name or
     a declared variable.  *[verified, `NameInterface.v`]*
  4. The aux names are `Ids.gensym Ids.sec _` (`fresh_ident_gen`), while
     `n_good` puts every declared and anonymous name in
     `AtomOrGensym n_prefixes` with `n_prefixes = elab_prefs`.  The two are
     disjoint, and `unnest_node_new_id_not_sec_gensym` in
     `SecLusUnnestingNodes.v` is an existing template for exactly this
     argument.  *[verified that the pieces exist; the composition is
     untested]*

Together: whenever `assign_clk_type` succeeds on an argument's clock -- which
it must, or the generator errors and there is no signature to preserve -- the
name at that clock position is a declared variable, so the argument there
cannot be a nested call.  It is an `Evar`, whose type *is* `[env w]`.

So what was going to be a syntactic side condition on user programs becomes
two lemmas about our own construction:

  * `env` domain: `Env.find w env = Some _` implies
    `In w ([clk; rst] ++ map fst (n_in ++ n_out ++ n_vars))` -- a
    `fresh_map_list` fact;
  * the composed exclusion: at a clock position of a call in a well-clocked
    node whose typing succeeds, the argument is a variable.

Neither restricts the programs the theorem covers.  The general lesson, and
worth applying to the remaining premises: **prefer assumptions the passes and
the syntax already guarantee over conditions invented to make a proof go
through** -- the `node` record's own invariants are doing work here that a
hand-written side condition would have obscured.

**The dependency property.**  For a signature generated by
`generate_lnode_sig` (the *Lustre* generator -- Leg U is Lustre-to-Lustre, so
this is `SecLTyping.v`, which is editable, not `SecNLusTyping.v`): a
constraint whose source mentions input `j` also mentions the variables of
`j`'s declared clock.

### Next steps, in order

1. ~~`subst_constraints_inp_map` with augmented actuals leaves every
   constraint source unchanged as a set, given the dependency property.~~
   **Done** -- `subst_constraints_inp_map_augment`.
2. ~~`env` domain~~ **done** (`generate_local_env_for_lnode_domain`).  Next
   the exclusion itself: at a clock position of a call in a well-clocked
   node whose typing succeeds, the argument is a variable.  It needs the
   domain lemma above, `n_nodup`, and the sec-vs-elab prefix argument for
   which `unnest_node_new_id_not_sec_gensym` is the template.  Then the
   dependency property for `generate_leqns_constraints`, mirroring the
   CoreExpr closure lemmas.

   Note on placement: Leg U takes `env` as an abstract section variable, so
   the domain fact enters it as a hypothesis and is discharged at the
   program level, where `SECLNAMEGEN` is in scope -- the same way
   `sig_good` and the others are handled.  Proving it now is what makes
   that hypothesis *known* dischargeable rather than hoped.
3. Thread `wc_global P` through `carries_at_streams` -- needed for
   `find_base_clock (clocksof es) = bck` via `find_base_clock_bck`.
4. The call case; then `carries_exp_streams`.
5. Re-establish the equation and equation-list theorems on the pointwise
   relation, which removes the two ambient premises from `node_carries`.
6. Concrete `unnest_node`: freshness to the naming run, `simplify`,
   `signatures_preserved`.
7. `unnest_global` by signature-global lockstep.  Leg U done.
8. Leg I (`normfby_global`); then prepend `normalize_global_sem` so source
   Lustre is the entry to `lnode_noninterference_streams`.

Sources of truth:

- **types and rules**: Prasad & Yerraguntla, *Normalising Lustre Preserves
  Security*, arXiv:2105.10687 (ICTAC 2021) — `~/Downloads/2105.10687v1.pdf`.
  Figures 5–11 are normative for this leg. Cited below as **[ICTAC]**.
- **proof architecture**: the NLustre→Stc leg already in `src/SIF`
  (`SecNLusTyping.v` / `SecNLusStcTranslation.v` / `SecStcNonInterference.v`)
  and the POPL draft in `../POPL_STC_translation_preservation`, cited as
  **[POPL]**.

Where the two disagree, [ICTAC] wins on *what the types are* and [POPL]/the
existing Coq wins on *how the preservation and noninterference proofs are
organised*. That split is the whole point of this document.

Constraint that governs everything: **no Coq file outside `src/SIF/` is
edited**, and **no existing `src/SIF` file is edited** except `vfiles`,
`docs/proof_outline.md` and `docs/NLustreCausalityBridge.md`. In particular
`SymTypes.v` is not touched — see §2.

---

## 0. Hard constraints, and the ledger that keeps them

Two constraints govern this leg. They are checked against every design
decision below.

**(H1 amended, 2026-09-12.)** The user lifted H1 for one specific change: the
naming pass now allocates **interface-first** -- clock, reset, inputs, outputs,
and only then locals -- so that an interface variable's security name does not
depend on how many locals its node has. `NameInterface.v` and
`SecNamingTotality.v` were edited and the whole NLustre-to-Obc chain rebuilt
green. H1 otherwise stands: any further edit to those files needs the same
explicit authorisation.

**What the reorder does and does not buy.** Within a node it works: an output
now keeps its name however many locals normalisation adds. Across nodes it does
not, because `generate_node_scoped_env'` threads one counter through the whole
program, so a node that gains a local shifts every name after it. Measured: a
two-node program whose *first* node gains one local moves the second node's
clock from `sec$9` to `sec$10` and its output from `sec$12` to `sec$13`, with
that node's own interface untouched. So independent allocation on the source
and on the normalized program still disagrees from the first such node onward;
see the options recorded with the milestones.

**(H1) Nothing from `SymTypes.v` downstream is changed. Additions only.**
No existing definition, notation, lemma statement or proof script in
`SymTypes.v`, `SecTypes.v`, `SIFSignature.v`, `SecContext.v`, `NameInterface.v`,
`SecCETyping.v`, `SecNLusTyping.v`, `SecNLusTypingCorrectness.v`,
`SecNLusTypingTotality.v`, `SecNamingTotality.v`, `SecSTCTyping.v`,
`SecStcTypingCorrectness.v`, `SecObcTyping.v`, `SecObcTypingCorrectness.v`,
`SecNLusStcTranslation.v`, `SecStcObcTranslation.v`, `SecNLusStcObcEnv.v` or
`NLustreCausality.v` is edited. New lemmas may be *appended* to those files
where a proof genuinely needs one, and only then.

**(H2) No downstream noninterference proof changes.**
`SecNLusNonInterferenceSupport.v`, `...Helpers.v`, `...ClockedStep.v`,
`SecNLusNonInterference.v`, `SecStcNonInterference.v` and
`SecObcNonInterference.v` are consumed as black boxes and not edited at all —
not even by appending.

### How the design satisfies them

| what this leg needs | where it comes from | touches an existing file? |
|---|---|---|
| refinement types `α{\|ρ\|}` | new `LST := ST * list constraint` in a new file | no — `SymTypes.ST` is untouched |
| ACUI union on `list constraint` | `SymTypes.constraint_merge` (`:1250`), already sorted + dedup | no |
| permutation-stable satisfaction | `SecTypes.listSatisfiable_Permutation`, `preserves_on_Permutation` (`:1185,1196`) | no |
| `simplify` and its correctness/completeness | `SymTypes.simplify`, `SecTypes.simplify_is_correct`, `simplify_complete` | no |
| block composition with private extras | `SecTypes.preserves_on_concat_scoped` | no |
| call replay ([ICTAC] Lemma 4) | `SIFSignature.generate_constraints_*` | no |
| `signatures_preserved`, `signature_fields_agree`, `scope_fresh` | `SIFSignature.v` (`:3408,255,288`) | no |
| `Signature_head_consistent` & friends | re-declared locally (§4) — they live inside the Stc module type | no |
| fresh per-call-site type variables | `SecContext.fresh_ident` (`:43`) | no |
| the naming monad for a Lustre allocator | client functor over `NAMEGEN` | no |
| NLustre noninterference | `SecNLusNonInterference.node_noninterference_outputs`, consumed | no |
| an NLustre `node_security` witness | *constructed* from its existing constructor | no |

The last row is the one that carries (H2). The whole Lustre leg reaches the
NI stack through exactly one door: it builds a `node_security` witness for the
transcribed NLustre node and hands it to the existing theorem. Nothing
downstream has to learn that Lustre exists.

### Correction: the fby rule must type both operands, 2026-09-12

§3 chose option (A) -- type the initial value of an `fby` as `⊥`, matching the
NLustre rule (NTfb) and keeping Leg A an equality. **That was unsound and has
been reverted.** In NLustre `EqFby x ck c e` carries a literal constant, so
typing only `e` is right. In Lustre `Efby` takes an arbitrary expression, and
`x = h fby 0` was given the constraint `κ ⊔ γ ⊑ β` -- no mention of `h`, though
`x`'s first value *is* `h`. The paper's (LTfby) joins both operands and was
right; the deviation was mine.

The equation generator no longer special-cases `fby`: it falls through to the
ordinary definition rule, whose expression case already joins both operands.

What it costs. The source constraint now mentions the initial value and the
target does not, because `to_constant` strips the `when`s and NLustre types a
constant. The source is strictly stronger -- the right way round -- but the two
constraint lists are no longer equal, so **Leg A is preservation, not
equality**, which is what [ICTAC] Theorem 1 claims anyway and what the
NLustre-to-Stc leg already lives with. Three of the four shapes stay exact.

Two things preservation needs that are not yet in place.

1. **The leg must run Lustre-to-NLustre.** The committed theorems run the other
   way, which was sound while the generators agreed and was justified by
   NLustre totality. It no longer suffices: the Lustre fby rule looks up the
   `when` variables of the initial value, which the NLustre rule never
   mentions, so NLustre success does not imply Lustre success. The
   noninterference pull-back wants the other direction anyway -- a secure
   Lustre node is one whose constraints are satisfied, and the NLustre node's
   must follow. So `to_lexp_assign_eq` and `to_cexp_assign_eq` need their
   converses; same induction.
2. **The `simplify` bridge.** Both halves exist -- `simplify_complete` pulls a
   raw valuation back, `simplify_is_correct` pushes one forward. Their side
   conditions (`wf_constraints` of the Lustre raw list, locals disjoint from
   the signature scope) are the Lustre analogues of what
   `SecNLusTypingCorrectness.v` proves for NLustre, and are the next thing to
   build.

Kept in `SecLusNLusTranslation.v`: the three exact shapes, and the inversion
lemmas for both sides, which the preservation proof reuses unchanged.

### Leg A status, 2026-09-13

Preservation runs Lustre-to-NLustre and reaches the node. Proved, no admits:

- `to_lexp_assign_rev`, `to_cexp_assign_rev`, `to_lexps_assign_rev` -- the
  converses of the expression lemmas, which is the direction preservation
  needs;
- `to_equation_entails_{def,fby,app,app_reset}` and the dispatcher
  `to_equation_entails`; `to_equations_entails` for a node's body;
- `entails_simplify` -- the bridge, from `simplify_complete` and
  `simplify_is_correct`;
- `to_node_sig_preserved` -- `signatures_preserved lsig nsig`.

`entails` records *two* things: the satisfaction implication, and that the two
lists have the same right-hand sides. The second is free -- every shape
constrains exactly the variables its equation defines, and only the delay's
left-hand side differs -- and it is what carries `wf_constraints` from the
NLustre side to the Lustre one, which the bridge needs.

### Leg A complete, 2026-09-13

Preservation runs Lustre-to-NLustre and reaches the whole program,
unconditionally. `SecLusNLusTranslation.v`, no admits, no new assumptions, and
no file outside it touched:

    to_global_signatures_entail :
      to_global G Hp = OK P ->
      LClo.wc_global G ->
      SECLNG.generate_lnode_scoped_env G = OK (envs, aux_names) ->
      generate_all_lsignatures_scoped_env G envs aux_names st = OK GLout ->
      SECNL.generate_all_signatures_scoped_env P envs aux_names = OK GNout ->
      Signature_entails GLout GNout

`Signature_entails GL GN` is the leg's relation: every callee found in `GL` is
found in `GN` under the same name with the same interface fields, and the two
instantiated call blocks entail. It is the Lustre analogue of
`Signature_consistent`, weaker in one place -- the reset actual is the same
expression on both sides here, so only the equal-actuals call clause is needed.

**The two globals.** The call shapes are the only ones that read a signature,
so they are the only ones the split touches. `call_block_step` is where it
happens: `Signature_entails` produces the callee's NLustre signature,
`generate_constraints_ok_from_good` shows the NLustre run exists at all -- it
reads only interface fields and the shape of the constraints, both of which
agree with a signature that has already generated -- and `call_block_entails`
relates the two blocks.

**Where the side conditions live.** Everything a call shape needs beyond the
two globals is in `call_context`, and every clause of it is about the *NLustre*
side. That is not a loss: transcription hands both generators the same actuals,
so `SecNLusTyping`'s scoping lemmas apply verbatim instead of being reproved
against Lustre clocking. Freshness moved there too --
`signature_fields_agree` makes the two signature scopes equal, so `scope_fresh`
transports back from `G_NL` to `G_L`.

**`signature_good` of the Lustre signature** is what the call rules want and
nothing on the Lustre side proves. It does not have to be proved there.
`wf_constraints` and `signature_good` read only right-hand sides, and what
`simplify` does to those is a function of the right-hand sides alone: `findST`
looks a target up, `subAll` drops the constraints targeting it and retargets
the rest at the names they already had. So the right-hand-side half of
`entails` survives elimination and carries `signature_good` back across
(`simplify_rhs_eq`, `signature_good_of_rhs`).

**The program level** is `generate_all_signatures_entails_scoped'`, the lockstep
induction of `generate_all_signatures_consistent_scoped'` with
`Signature_head_entails` in place of `Signature_head_consistent`. It carries
`secglobal_scoped`, `secglobal_good`, duplicate-free scopes and
`secglobal_scope_bounded_above` on the *NLustre* accumulator only -- nothing
separate is needed about the Lustre one, because `Signature_entails` keeps the
interface fields aligned. Each is re-established at a node by the facts
`generated_node_head_entails` already produces; scope-freshness comes from
splitting the naming run at the node.

The node lists are related by `transcribed` (a `Forall2` over `to_node`) rather
than by a `to_global` run, because the drivers generate over `rev nodes` and a
`Forall2` reverses where a `to_global` run does not.

**Module parameters added** to `SecLusNLusTranslation.v`: `SECNLUSTYPINGCORRECTNESS`,
`SECLNAMEGEN`, `LCLOCKING`, `TRCLOCKING`. The file remains a leaf -- nothing
imports it -- so nothing in the NLustre, Stc or Obc chain is affected.

**What is left for the noninterference pull-back.** Preservation is the
statement about generated signatures. Turning it into "a secure Lustre program
transcribes to a secure NLustre one" needs the Lustre analogue of
`SecNLusNonInterference.v`'s top-level statement, which is a separate leg.

### Correction: scope-freshness cannot include the node itself, 2026-09-13

`call_context` asked for `secglobal_scope_fresh scope GN` -- the node's scope
fresh from *every* signature of the global. At an accumulator, which is where
the preservation leg uses it, that is right: the accumulator holds the node's
callees and not the node. At a whole-program global it is unsatisfiable. The
global then holds the node's own signature, and `signature_scope sig =
s_in ++ s_out ++ [s_clk; s_reset]` is a sublist of the node's scope
`inp ++ out ++ locals ++ [clk; rst]`, so `scope_fresh` forces `s_in = []`,
which `n_ingt0` forbids.

`node_scope_fresh_in_env_self_absurd` in `SecLusNonInterference.v` records
that as a checked lemma rather than a comment.

This mattered because `SecLusNonInterference.v` instantiated `call_context` at
the *final* globals, which is what `node_security` and `lnode_security` are
stated over. Everything downstream of that hypothesis was therefore vacuous
until the fix. The preservation leg was never affected -- it instantiates at
the accumulator.

The fix threads the caller's own name through as `self`:

- `call_context` takes `self` and asks freshness only of signatures `g <> self`;
- the call shapes take `f <> self`, the dispatcher takes
  `~ Is_node_in_eq self eq`, the equation list `~ Is_node_in self eqs`, and the
  node level instantiates `self` at the node's name;
- `Ordered_nodes` is what discharges it -- `Ordered_nodes_not_self` at the
  program level, `find_node_not_Is_node_in` at the node level. A call site
  never names the node it is in, which is exactly the side condition the
  weakened clause needs.

`node_callees_scope_fresh` is the satisfiable replacement for
`node_scope_fresh_in_env` at a whole-program global. The same correction
applies to `generated_callers_scope_fresh` in `SecNLusTypingCorrectness.v`,
which is assumed rather than proved and has the same shape -- worth checking
before anyone tries to discharge it.

### Correction of scope: the pass that matters is normalisation, 2026-09-14

Leg A targets *transcription* -- normalised Lustre to NLustre. That is the
wrong half, and the codebase proves it.

`to_lexp` rejects `Eapp` outright (`Tr.v:48`, "expression not normalized").
So on any program that transcribes, `assign_lexp_type`'s `Eapp` branch is
unreachable, `fresh_idents` is never called, and `minted st st' = []` --
which is exactly `minted_refl`, the lemma `to_node_sig_preserved` leans on.
`to_lexps_assign_rev` states the consequence outright: the argument types come
back as `map (fun t => (t, [])) tys`. **The carried-constraint component of
`LST` is empty on every expression Leg A ever sees.** The refinement type
degenerates to a plain `ST` throughout.

That machinery is not incidental. It is the point. `LST = ST * list
constraint`, `carried`, `lrefine`, `ljoin`, `fresh_idents`, `minted` and the
`simplify raw (locals ++ minted st0 st1)` in `generate_lnode_sig` were all
built for nested calls -- ICTAC's (LTncall) -- and nested calls are what
*normalisation* removes, not what transcription sees.

**The correspondence the design was written for.** Unnesting, on a nested call
(`Unnesting.v:433`):

    | Eapp f es er anns =>
        do (es', eqs1) <- unnest_exps es; ...
        do xs <- idents_for_anns' anns;
        ret (map (fun '(id, ann) => Evar id ann) xs,
             (map fst xs, [Eapp f es' er' ...]) :: eqs1 ++ eqs2 ++ eqs3)

and `assign_lexp_type` on the same expression (`SecLTyping.v:168`):

    | Eapp f es er anns =>
        do argts <- assign_lexps es; ...
        do outs <- fresh_idents (length anns);
        do cs   <- generate_constraints sg (map fst argts) ckty (fst rstty) outs;
        let held := cmerge cs (cmerge (carried argts) (snd rstty)) in
        ret (map (fun o => (([o] : ST), held)) outs)

Term for term:

- `idents_for_anns' anns` mints one fresh *variable* per result;
  `fresh_idents (length anns)` mints one fresh *security name* per result.
- unnesting returns `Evar id ann`; the typer returns `([o], held)` -- a
  variable-shaped type.
- unnesting *emits an equation* `(map fst xs, [Eapp f es' er' _])`; the typer
  *carries* `held`, which is that equation's constraint set joined with what
  the arguments and the reset were carrying.
- `unnest_node` sets `n_vars := n_vars n ++ nvars` with `nvars` the minted
  variables in order; `generate_lnode_sig` eliminates `locals ++ minted st0 st1`.

So: **carried constraints are the constraints of the equations unnesting
emits, and minted security names are the variables unnesting adds.** That is
the theorem, and nothing in Leg A states it.

**Abandoning on failure is the right discipline.** `normalize_global` is
`unnest_global`, then `check_causality`, then `normfby_global` -- it returns
`Error` if causality fails. A source program that does not normalise produces
no NLustre, so there is nothing to preserve. Non-normalisable programs are not
a fragment to weaken the theorem for; they are programs the compiler rejects.

**What to build.**

- *Leg N (new, the real one).* Source Lustre to unnested Lustre. Expression
  level: `unnest_exp G false e st = (es', eqs, st')` against
  `assign_lexp_type e sst = OK (ts, sst')`, concluding that the types of `es'`
  are `map fst ts` and that the constraints generated for `eqs` are `snd ts`.
  Equation and node level follow, with `minted` in bijection with `nvars`.
  This is `preserves_on`, not `entails`: unnesting introduces variables.
- *Leg N2.* `normfby_global`, the second half of normalisation.
- *Leg A (keep).* Transcription stays as the tail. It is correct and needed;
  it is simply the easy half, and it is where `entails` suffices precisely
  because transcription introduces nothing.

The noninterference pull-back will then have to relate two valuations across
Leg N, the way the NLustre-to-Stc leg does, rather than keeping one as Leg A
does.

### The plan, redone around the passes that matter, 2026-09-14

**Hard constraints.** Nothing at or below `SecNLusTyping.v` is edited -- the
NLustre, Stc and Obc typing, correctness, translation and noninterference
files are read-only, used through module parameters. Work happens in
`SecLTyping.v`, `SecLNameInterface.v`, the Lus2NLus files, and new files.

**The pipeline, and which leg owns which pass.**

    source Lustre G
      --unnest_global-->    G1     Leg U   nested calls and control lifted out
      --check_causality-->         fails => no NLustre => nothing to prove
      --normfby_global-->   G2     Leg I   fby initial values made constant
      --to_global-->        P      Leg A   transcription            [DONE]
      --> NLustre --> Stc --> Obc          [existing, untouched]

A source program that does not normalise is rejected by the compiler. There is
no "normalisable Lustre" side condition to carry: when a pass returns `Error`
the obligation disappears.

#### Leg U -- unnesting. The leg the refinement types exist for.

`unnest_exp G false (Eapp f es er anns)` mints one variable per result with
`idents_for_anns'`, returns `Evar id ann` for each, and emits the call as its
own equation. `assign_lexp_type` on the same expression mints one security
name per result with `fresh_idents`, returns a variable-shaped type `([o], held)`
for each, and carries `held = cs ⊔ carried argts ⊔ snd rstty`.

The theorem: **carried constraints are the constraints of the equations
unnesting emits; minted security names are the variables unnesting adds.**

- *Expression level.* `unnest_exp G is_control e st = ((es', eqs), st')` against
  `assign_lexp_type e sst = OK (ts, sst')`: the types of `es'` are `map fst ts`,
  and the constraints generated for `eqs` are `snd ts`. Every non-`Eapp` case
  with `is_control = false` also lifts (merge, ite, fby, arrow all call
  `idents_for_anns`), so this is not an `Eapp`-only argument.
- *Equation level.* `unnest_equation` = `unnest_rhss` then `split_equation`;
  the split is what turns a multi-result call into one equation per result,
  which is what `generate_constraints` already produces one constraint per
  result for.
- *Node level.* `unnest_node` sets `n_vars := n_vars n ++ nvars` with
  `nvars = st_anns (snd ...)`; `generate_lnode_sig` eliminates
  `locals ++ minted st0 st1`. The two lists must correspond.
- *Program level.* Two signature globals in lockstep, as Leg A does --
  `Signature_entails` and its induction generalise directly, since callees are
  themselves unnested.

This is `preserves_on`, not `entails`. Unnesting introduces variables, so the
witness valuation must be extended on them and the single-valuation
simplification of Leg A does not survive.

**The crux, and it is not settled.** The naming pass assigns security names to
a node's declared variables; `fresh_idents` mints names for variables that do
not exist yet in the source. For the source signature and the unnested one to
be comparable, the `k`-th minted name must be the name the naming pass gives
the `k`-th variable unnesting creates. Two ways:

  1. *Make them equal.* Require the naming pass to allocate locals in the order
     unnesting creates them and the security counter to start where the naming
     pass stopped. Brittle: couples two unrelated allocators.
  2. *Relate them by a bijection* and state preservation up to that renaming.
     More robust, and `preserves_on` already tolerates a changed valuation, so
     the renaming can be absorbed into the witness.

Option 2 looks right. Decide before writing expression-level lemmas, because
the statement shape depends on it.

#### Leg I -- initialisation. The leg the two-operand fby rule exists for.

`fby_equation` has three cases:

- `([x], [Efby [e0] [e] [ann]])` with `is_constant e0`, not cut: unchanged.
- same, cut: a fresh `x'` with `([x],[Evar x']) , ([x'],[Efby [e0] [e] [ann]])`.
  A rename; the security type must travel with it.
- `¬ is_constant e0`: `fby_iteexp` gives
  `x = Eite (Evar initid) [e0] [Evar px]` together with
  `([px], [Efby [<constant>] [e] [ann]])` and the equation defining `initid`.

The third case is the content. Before the pass the initial value is arbitrary
and its level flows into `x`; after it, the `fby`'s initial value is a literal
constant and `e0`'s level reaches `x` only through the `Eite`. **That is why
the Lustre `fby` rule joins both operands** (commit a15e9ba) while the NLustre
rule types only the second: the source rule is the pre-initialisation rule.

So Leg I must show the source's `e0 ⊔ e` for `x` is preserved as
`ite(initid, e0, px)` with `px : e` -- and that `initid`, a fresh boolean on
the clock, is at the clock's level, so it adds nothing the equation's clock
type did not already contribute.

`init_var_for_clock` *reuses* an existing init variable when one exists for the
same clock (the `find` on `st_anns`). So the minted-name correspondence is not
one-per-occurrence here; it is one-per-clock. Leg U's bijection has to allow
for that, which is another reason to prefer option 2 above.

#### What Leg A contributes, and what has to change about it

Leg A stays: it is the tail, it is correct, and `entails` is sound there
precisely because transcription introduces nothing. Reusable as is:
`Signature_entails` and its program-level induction, `generate_all_signatures_domain`,
`entails_simplify`, the `simplify`-on-right-hand-sides lemmas, and the whole
`SecLusNonInterference` pull-back shape.

What changes: with Legs U and I in front, the two globals no longer diverge for
the reason Leg A assumes. Leg A's divergence came from applying the *source*
`fby` rule to an already-normalised program, where the initial value is
`add_whens (Econst _) ty ck` -- a constant under `when`s, whose type is the
clock's variables, which the equation's clock type already contributes. Once
Leg I has run, that difference should collapse. Worth re-examining whether
`Signature_entails` can be strengthened back to equality on the transcription
leg after Leg I is in place.

#### Order of work

1. Decide the naming correspondence (option 1 or 2 above). Everything else
   depends on the statement shape.
2. Leg U at expression level, `Eapp` case first -- it is the one that exercises
   `carried`, `lrefine`, `fresh_idents` and `minted` together. If the
   correspondence does not hold there, nothing downstream matters.
3. Leg U equation and node level; then the program-level lockstep.
4. Leg I, third case first for the same reason.
5. Re-examine Leg A's two-globals generalisation in light of 4.
6. Noninterference: the pull-back must now relate two valuations across U and
   I, the way the NLustre-to-Stc leg does.

#### Leg U checkpoint, 2026-09-20

*History. Superseded by [Leg U — current state](#leg-u--current-state).*

The naming-correspondence decision and the expression/equation work above are
now implemented.  Leg U is split into six compilation units plus a facade:

1. `SecLusUnnestingBase.v` -- common definitions and structural facts;
2. `SecLusUnnestingExpr.v` -- the complete expression induction;
3. `SecLusUnnestingCalls.v` -- semantic call monotonicity, output witnesses,
   and reset handling;
4. `SecLusUnnestingStreams.v` -- pointwise ambient relations, separated from
   the already-large expression unit;
5. `SecLusUnnestingEquations.v` -- general, call, mixed/split, and arbitrary
   equation preservation, ending in `eqn_carries_all`;
6. `SecLusUnnestingNodes.v` -- equation-list composition with per-equation
   ambients and the conditional raw theorem `node_carries`;
7. `SecLusUnnesting.v` -- the compatibility facade.

There are no admits.  The equation and node files contain no `eapply` or
`eexists`, compile separately, and the complete serial Docker build passes.

The obsolete `Forall eqn_covered` premise has now been removed from both list
inductions and from `node_carries`.  `node_carries_preserves` packages the raw
valuation result as `preserves_on`; `unnest_node_fields` exposes the dependent
run inside `unnest_node`; and `unnest_node_equations_nodup` discharges the
target `NoDup` premise from the constructed node's invariant.  The target
node's declaration invariant also establishes freshness of every identifier
added by the unnesting state.  Environment injectivity transports that result
to the moved security names, and `unnest_node_moved_fresh_generated_aux`
extends it to the clock/reset auxiliaries when the naming run supplies their
`sec`-generated identifiers and environment lookups.

Trying to discharge the two ambient premises exposed a statement-level gap.
One `A eq` is shared by all streams of an equation, but a multi-stream equation
may place those streams on different clocks.  Covering every emitted clock
requires the union of their ambients, while the source constraints put each
output above only its own ambient, not its siblings'.  Therefore the two
premises cannot in general be derived from well-clocking and source
satisfaction as currently stated.

Two pointwise foundations now compile:

- `lifted_defs_streams` constructs the witness for emitted definitions with
  aligned ambient, identifier, and source-type lists;
- `generate_lvars_constraints_mono_streams` consumes the same alignment at
  the equation-output generator.

Both use `Forall3`, so no sibling stream's clock is added to another stream's
obligation.  The expression/call composition still needs to expose and
preserve that relation before the scalar node premise can be removed.

The shared pointwise vocabulary now also compiles: `stream_rel`,
`stream_bounds`, `carries_result_streams`, and the aligned clock relations
`clocks_covered`/`declared_ambients`.  Compatibility with the old scalar
result, unchanged expressions, append composition, and preservation across a
sibling's fresh-name witness are proved.

The replacement expression contract, `carries_at_streams`, is now concrete.
It aligns `clockof e`, the ambient list, the source types, and the target
types; carries `state_clocks_found` through the run; and returns a
`carries_result_streams`.  Its `Econst`, `Evar`, `Eunop`, and `Ebinop` cases
compile.  `Ebinop` is the first real test of the contract: two child witnesses
compose without adding one child's ambient to the other, and the first
child's generated constraints and target type survive the second child's
fresh-name updates.  `state_clocks_found_prefix` supplies the invariant for
the intermediate fresh state.

The expression-list fold and `Ewhen` now compile as well.  The list fold
splits the flat ambient list at the head expression's stream count, composes
the two witnesses, and appends their pointwise relations.  `Ewhen` preserves
that alignment through the componentwise sampling map.  Its clock proof uses
`clock_covered_on_inv`: coverage of `ck on x` entails coverage of `ck`, once
the typing run has supplied the environment lookup for `x`.

The pointwise join helper used by the control operators also compiles.  For
`Emerge`, branch clocks are `ck on x` while result clocks are `ck`, so the
child contracts must use `merge [sec(x)] ambient` positionally.  The new
`clock_covered_on` and `stream_rel_ambient_on_normalize` lemmas justify adding
that name for each branch and absorbing it into the final joined source type.
`carries_Emerge_control_streams` now completes that composition: both branch
list witnesses are chained, the first is transported across the second, and
`ljoin_list_rel_streams_on` establishes the final pointwise result.

The non-lifting `Eite` case now compiles as
`carries_Eite_control_streams`.  The scrutinee's singleton relation is carried
across both later branch witnesses, and `stream_head_rel_of_clock` expands its
declared-clock bound to one bound per aligned result ambient before
`ljoin_list_rel_head_streams` performs the componentwise join.  In support of
that argument, `clock_covered` is now deliberately non-vacuous: it packages a
successful `assign_clk_type` result together with ambient inclusion.  Thus a
failed clock assignment can no longer satisfy coverage accidentally.  A full
serial Docker build passes with both pointwise control cases.

`state_clocks_found` and `declared_ambients_of_state` connect the abstract
clock alignment to the concrete annotated identifiers accumulated by the
unnesting fresh state.  The expression contract now carries this state lookup
invariant; the lifting cases will use it with `unnest_exp_clockof` to obtain
result-clock order.

#### Pointwise expression induction: everything but the call, 2026-09-22

*History. Superseded by [Leg U — current state](#leg-u--current-state).*

The lifting branches of `Emerge` and `Eite` and both delays now compile:
`carries_Emerge_lift_streams`, `carries_Eite_lift_streams`,
`carries_Efby_streams`, `carries_Earrow_streams`.  All four end the same way.
`idents_for_anns` mints one variable per result; those identifiers land in
the fresh state carrying their annotations; `state_clocks_found` says the
naming run knows their clocks; and `declared_ambients_of_state` turns that
into one ambient per minted variable, which `lifted_defs_streams` consumes.
So every emitted definition stays above its own ambient and no sibling's.
`ljoin_list_rel_plain_streams` is the new componentwise join with no head in
front, which is what the two delays need.

That leaves the call, and it is not a fifth instance of the same pattern.

**Why the call is different.**  `generate_constraints_mono_sem` transports
satisfaction across a call under *one* ambient `amb`: clause 3 asks each
target actual to dominate `merge amb` of the source actual, and
`amb_pair dlt os bs` makes each target output equal `amb` joined with the
source output.  Instantiating it needs `amb` to be simultaneously

  * **above** every argument's ambient, to discharge clause 3 from the
    arguments' pointwise witnesses, and
  * **below** every result's ambient, because the contract's conclusion
    demands `satisfiable dlt (fst tgt_i) (merge a_i (fst src_i))`.

For a node call those two cannot in general both hold.  Clocking
instantiates every formal from the same base `bck`, but an input may be
declared on a strictly deeper clock than an output: in `f(x when c)` with
`f`'s input declared on a subclock and its output on `Cbase`, the argument
sits on `bck on c'` while the result sits on `bck`.  The argument's ambient
is then not below the result's, and no uniform `amb` exists.

**What would close it.**  The per-input generalisation of
`generate_constraints_mono_sem` -- clause 3 with one ambient per input --
is sound only if a generated signature already carries the dependency

    a constraint that mentions input `j` also mentions the variables of
    `j`'s declared clock.

That is a property of `generate_node_sig` in `SecNLusTyping.v`.  The file is
read-only, but the property is about it rather than in it, so the lemma
belongs in an editable unit.  With it, an argument's extra clock variables
are already below every output the argument feeds, and the per-input clause
absorbs into the output side exactly as the uniform one does.

A second, smaller prerequisite: relating the call's own clock ambient to the
results' needs `find_base_clock (clocksof es) = bck`, which `find_base_clock_bck`
gives from `WellInstantiated_bck` and `WellInstantiated_parent` -- but
`WellInstantiated_bck` wants `wc_env (idck n.(n_in))`, i.e. `wc_global P`.
The contract does not carry it today; adding it to `carries_at_streams` and
threading it through the eight existing cases is mechanical.

#### The dependency lemma, designed, 2026-09-22

*History, and partly wrong: the design it records was later found to fail
during the substitution fold. See [Leg U — current state](#leg-u--current-state).*

Two corrections to the sketch above, and the shape the premise should take.

**Which generator.**  The earlier note said the dependency property is about
`generate_node_sig` in `SecNLusTyping.v`.  It is not, for Leg U's purposes.
Leg U is Lustre-to-Lustre: the same `GL` types the source equation and the
unnested one, and `GL`'s signatures come from `generate_lnode_sig` in
`SecLTyping.v` -- the *Lustre* generator, which is editable.  So the eventual
discharge is over `generate_leqns_constraints` and `assign_lexp_type`, not
over the CoreExpr generator.

`SecLusUnnestingBase.v` now carries the groundwork, but on the CoreExpr side:
`assign_exp_type_clock_closed` and `assign_cexp_type_clock_closed` are about
`CEClo.wc_exp`/`wc_cexp`, so they serve the *NLustre* signature generator, not
Leg U's critical path.  They are still wanted -- the phases' signatures have
to agree -- and their structure transfers directly to the Lustre forms, which
mirror them case for case.  `clock_prefix` and
`assign_clk_type_prefix_incl` are language-independent and are needed either
way.

**The shape of the premise.**  A first attempt tried to weaken clause 3 of
`generate_constraints_mono_sem` in place, on the grounds that `cs_chain`'s
third clause

    satisfiable dlt (remove_all R (fst c2)) (merge amb (remove_all R (fst c1)))

already bounds the target constraint's whole content by `amb` joined with
the source's, so slack added at one input is absorbed.  That is true at the
*end* of the fold but not during it: the fold substitutes the formals one at
a time, and `a_j` is built from the actuals of *other* input positions --
the clock variables of `j`.  Those are not yet in the constraint when
position `j` is substituted, so the containment cannot be discharged at that
step.  Repairing it would mean strengthening the chain invariant to carry
the not-yet-substituted positions, which is the vector through the chain the
attempt was trying to avoid.

The route that works needs **no change to `generate_constraints_mono_sem`
at all**, which matters because two other proofs already use it.  Instantiate
the signature on the source side with *augmented* argument types

    inp1''_j  :=  inp1_j  joined with the actuals of j's clock variables

and keep the uniform ambient `amb := call_amb`, the call's base-clock
ambient `[rst_ty] ⊔ assign_clk_type bck`.  Then

  * clause 3 holds uniformly, because
    `a_j = [rst_ty] ⊔ assign_clk_type(clock of arg j)` and that clock is
    `bck` extended by exactly `j`'s clock variables, so
    `merge a_j inp1_j` is contained in `call_amb` joined with `inp1''_j`;
  * `amb_pair` holds, because `bck` is a prefix of every output clock, so
    `call_amb` is below every result's ambient --
    `assign_clk_type_prefix_incl`;
  * and the augmentation changes *nothing*: by the dependency property, any
    constraint mentioning input `j` already mentions `j`'s clock variables,
    so substituting the larger actuals adds no member to any source.
    `listSatisfiable_same_sources` then carries the source's satisfaction
    across, since `hm_ext` is a join over members and cannot tell two types
    with the same members apart.

`satisfiable_of_incl`, `satisfiable_same_names` and
`listSatisfiable_same_sources` are proved in `SecLusUnnestingBase.v`.

The next tasks are, in order:

1. prove that substituting augmented actuals leaves every constraint source
   unchanged as a set, given the dependency property -- the one new lemma
   about `subst_constraints_inp_map`; then prove the Lustre-side dependency
   lemma for `generate_leqns_constraints` (mirroring the CoreExpr ones
   already in `SecLusUnnestingBase.v`), thread `wc_global` through the
   contract, and do the call case, which completes the pointwise expression
   induction.  `generate_constraints_mono_sem` itself is not touched;
2. re-establish the arbitrary-equation and equation-list theorems with that
   relation, then connect the proved moved-name freshness lemma to the naming
   run's clock/reset witnesses;
3. use the already-proved raw `preserves_on` packaging and target `NoDup`
   lemma, transport the result through `simplify`, and prove
   `signatures_preserved` for `unnest_node`;
4. lift it through `unnest_global` by a signature-global lockstep;
5. proceed to Leg I (`normfby_global`).

`SecLusConstraintExport.v` currently instantiates the Leg U functor against
the concrete Velus modules.  That catches module-interface drift but is not
yet the end-to-end preservation theorem.

### Source Lustre is the only entry, 2026-09-14

Normalised Lustre is not a statement-level input. Any theorem whose
hypothesis is "G is already normalised" is deprecated: such a G is not a
program anyone wrote, it is an intermediate the compiler produced. The
typing, the preservation and the noninterference all start at source Lustre
and go **through unnesting and initialisation**.

    source Lustre G                    <- the only entry
      --unnest_global-->   G1          Leg U
      --check_causality->              failure => no obligation
      --normfby_global-->  G2          Leg I
      --to_global-->       P           the last step, not an entry
      --> NLustre --> Stc --> Obc      pre-existing, untouched

Transcription stays in the chain because the chain has to reach NLustre, but
it is demoted: it is the step where nothing is introduced and therefore
nothing interesting happens, and it must never again appear as the place a
statement begins.

**Top-level shapes to aim at.**

    (preservation)
      normalize_global G _ _ = OK G' ->  to_global G' _ = OK P ->
      generate_all_lsignatures G ...  preserves  generate_all_signatures P ...

    (noninterference)
      normalize_global G _ _ = OK G' ->  to_global G' _ = OK P ->
      lnode_security ... (on the SOURCE node) ->
      LSem.sem_node G f ins outs -> LSem.sem_node G f ins' outs' ->
      low inputs agree -> low outputs agree

Both compose U ; I ; A. Neither mentions a normalised program in its
hypotheses beyond naming the pass outputs.

**What the transcription work contributes.** Everything generic over two
signature globals, which is most of it:

- `Signature_entails`, `Signature_head_entails`, `Signature_call_entails`,
  `Signature_entails_{nil,cons}`, `call_block_step`, `call_context`;
- `Signature_domain_incl` and its induction;
- `entails`, `entails_{refl,rhs,sat,app}`, `entails_simplify`,
  `simplify_rhs_eq`, `subAll_rhs_eq`, `wf_constraints_of_rhs`,
  `signature_good_of_rhs`, `signature_scope_agree`;
- the program-level lockstep `generate_all_signatures_entails_scoped'`, whose
  shape Legs U and I reuse with their own per-node step;
- `SecLusNonInterference`'s `lnode_security` and the pull-back *shape*
  (`generated_signature_provenance`, `node_callees_scope_fresh_proved`,
  `security_data_transports`).

Legs U and I differ from it in one structural way: they introduce variables,
so they are `preserves_on` and their pull-backs relate two valuations. The
single-valuation simplification is transcription-only and does not generalise.

**What was deleted, 2026-09-14.** Checked by build, not by eye:

- `to_equation_constraint_eq_{def,app,app_reset}` -- the equality-direction
  theorems from before the leg became preservation, superseded by the
  `entails` versions and referenced by nothing;
- the abstract program-level chain `node_step_entails`, `node_bridge`,
  `node_step_entails_from_bridge`, `generate_all_signatures_entails'`,
  `generate_all_signatures_entails` -- superseded by the scoped chain that
  `to_global_signatures_entail` actually runs;
- `signature_constraints_entail` -- written as an interface for the layer
  above, which ended up using `signatures_preserved` directly.

198 lines. Nothing else in the transcription work is dead: the
`to_equation_*_inv` inversions and the `entails` theorems are what the
scoped chain runs on, and transcription is still the last step of the chain.

**Semantic files: take the bundles.** `SecLusNonInterferenceStreams.v`
currently imports `Transcription.Correctness`, and `Lustre/Normalization/`
has a module type of the same name. Composing `normalize_global_sem` in front
of `sem_l_nl` needs both, so the semantic files should take `L : LUSTRE`,
`NL : NLUSTRE` and `TR : TRANSCRIPTION` -- the bundles `Instantiator` uses --
rather than the leaves, and reach the pieces as `L.Norm.Correct.*`,
`TR.Correctness.*`, `NL.CoindToIdx.*`. That also removes the name clash.

### Leg U: how the expression-level statement is shaped, 2026-09-14

The blocker for the induction is not any case, it is the statement. At
expression level the source's residual type `fst ts` mentions the *minted*
security names, while the unnested expression's type mentions the naming
pass's names for the variables unnesting created. Those are different names --
`gensym sec _` against `gensym norm1 _` -- so the types are not equal, they are
related by a renaming.

**Decision: the renaming is internal, and it is not a new operation.**
`SIFSignature.v` already has it. The renaming of a constraint list's target
identifiers, list-wise and with a capture check, is

    subst_constraints_out_map (cs : list constraint)
                              (xs vs : list ident) : Sec (list constraint)

and it is not incidental machinery: `generate_constraints` *is* four
substitutions in sequence -- `subst_constraints_inp_map` for the formals,
`subst_ident_in_constraints` for the clock and the reset, then
`subst_constraints_out_map` for the results, then `reorder_constraints`.
Instantiating a signature at a call site and renaming minted names to the
variables unnesting created are the same operation.

Both directions are already proved, and they are exactly the two halves a
`preserves_on` needs:

    subst_constraints_out_map_correct  (2506)
      dlt satisfies cs  ->  Forall2 (fun x v => dlt v = dlt x) xs vs
      ->  dlt satisfies cs'
    subst_constraints_out_map_complete (2650)
      dlt satisfies cs' ->  upd_idents_rev dlt xs vs  satisfies cs

`upd_idents_rev` (`SecTypes.v:1403`) is the witness constructor -- the same one
`lat_valuation` uses to instantiate a callee. So the expression-level statement
is phrased over these, not over an invented substitution:

    unnest_exp G is_control e st = ((es', eqs), st') ->
    assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
    exists outs news,
         (* the minted names and the variables unnesting created, in order *)
         subst_constraints_out_map (carried ts) outs news sst0 = OK (cs, sst1)
      /\ (* and those renamed constraints are what the emitted equations give *)
         preserves_on scope cs (constraints generated for eqs)

with the residual types related by the same `outs`/`news` pairing rather than
by a substitution written for the purpose. Above expression level neither list
appears: both are eliminated by `simplify`, the minted names through
`locals ++ minted st0 st1` and the new variables through `locals ++ nvars`, so
`preserves_on scope` closes over them.

Do not define a second substitution. If something is missing it is a *lemma*
about `subst_constraints_out_map`, not a new operation.

**Status of Leg U, 2026-09-14.** Fifteen lemmas, no admits:

- `assign_lexp_Eapp_inv` / `unnest_exp_Eapp_inv` -- both sides of a call;
- `unnest_exp_Efby_inv` -- the delay, which is also where Leg I picks up;
- `fresh_idents_length`, `assign_lexp_Eapp_length`,
  `idents_for_anns'_length` (Velus's) -- both result lists have length
  `length anns`, which makes the bijection positional;
- `assign_lexp_Evar_inv`, `unnested_call_results_carry_nothing` -- after
  unnesting nothing is carried, which is the postcondition transcription was
  silently relying on;
- `unnest_exp_Econst`, `unnest_exp_Evar` -- base cases;
- `carried_uniform`, `assign_lexp_Eapp_carried` -- a call's total carried set
  is its emitted equation's constraint set;
- `carried_app`, `assign_lexps_carried_{cons,nil}` -- argument lists decompose.

Remaining for Leg U: the other lifting cases (`Earrow`, `Emerge`, `Eite` --
same shape as `Efby`, simpler carried list), then the induction with the
statement above, then equation, node and program level.

### Leg U: exactly where it stops, and the next lemma

*History, long superseded. See [Leg U — current state](#leg-u--current-state).*

Everything structural in the `Eapp` case is done. Both sides instantiate the
*same* signature -- the source expression looks `f` up to build what it
carries, the equation unnesting emits looks `f` up to build what it generates
-- so the two constraint sets have the same shape,

    cmerge (generate_constraints sg _ _ _ <results>)
           (cmerge (carried args) (snd rst))

and differ only in two places, both of which now have their lemma:

- the **arguments**: `carried_app` and `assign_lexps_carried_{cons,nil}` let the
  argument list decompose on both sides, so the induction applies pointwise;
- the **result names**: minted on one side, the variables unnesting created on
  the other, both lists of length `length anns`
  (`fresh_idents_length`, `idents_for_anns'_length`), related by
  `subst_constraints_out_map` whose two directions are already proved.

**The next lemma**, and why it was not written here: packaging that as

    Eapp_and_emitted_share_signature :
      assign_lexp_type ... (Eapp f es er anns) = OK (ts, _) ->
      generate_leqn_constraint ... (x :: xs, [Eapp f es'' er'' anns'']) = OK (ce, _) ->
      ... both sides are generate_constraints at the same sg ...

needs a case analysis on the *emitted* equation's reset expression. The
emitted `er''` is whatever `unnest_reset` produced -- an `Evar` in the normal
case, but `unnest_reset` also has a branch that mints a variable and emits an
equation when the head is not already a variable. So the target-side inversion
is not a single `generate_lcall_constraint_inv`; it needs
`unnest_reset_spec` (`Unnesting.v:288`) first, to know which of the two shapes
`er''` has. Write that step before attempting the lemma.

After it: the expression-level induction, mutual over `unnest_exp` at both
control flags and `map_bind2` over lists, with the statement recorded above.
Then equation, node and program level, reusing `Signature_entails` and the
scoped lockstep from the transcription work.

### Correction: the two sides do not mint together, 2026-09-14

Checked, not assumed: `fresh_idents` occurs **once** in `SecLTyping.v`, at
line 183, in the `Eapp` case. `Efby`, `Earrow`, `Emerge` and `Eite` all just
`ljoin_list` their operands' types and mint nothing.

Unnesting lifts all five. So the two allocators coincide only for calls.

For `Efby` at `is_control = false`:

    source type : ljoin_list ts us          -- a compound type
    target type : [env x]                   -- a single variable
    emitted     : (x, [fby e0' e'])         -- constrains env x to dominate
                                               the operands' join

The target type is *not* a renaming of the source type. It is a fresh name
constrained to sit above it. So the statement recorded earlier -- residual
types related by the renaming -- is wrong for four of the five lifting
constructors, and would have failed four cases into the induction.

**The corrected statement.** One relation for every constructor, and it is
`preserves_on` throughout:

    unnest_exp G is_control e st = ((es', eqs), st') ->
    assign_lexp_type GL env base_ty rst_ty e sst = OK (ts, sst') ->
    generate_leqns_constraints GN env base_ty rst_ty cenv eqs xst = OK (ce, xst') ->
    preserves_on scope <the source's contribution> <the target's contribution>

where a contribution is the carried constraints together with the defining
constraint of whatever consumes the expression. A valuation satisfying the
source's set extends to one satisfying the target's by giving each variable
unnesting created the value of the source type it stands for -- which is what
the emitted equation constrains it to.

**Where the renaming machinery belongs.** Not in the type clause, which is
gone. It belongs to the `Eapp` case alone, where the typer *did* mint: there
the carried constraints mention minted names, the emitted equation mentions
the call's result variables, and `subst_constraints_out_map` matches them.
`subst_idents_in_type` is for the actual argument types handed to
`generate_constraints` in that same case. Everything proved for the renaming
stands; its scope is narrower than the plan claimed.

**Why this is the right shape anyway.** For the four non-call lifting
constructors the target name is *freer* than the source type -- constrained
to dominate it, not equal to it -- which is exactly the direction preservation
wants, and exactly why the leg is `preserves_on` and not `entails`. The
transcription leg got `entails` because it introduced nothing; this leg
cannot, and now for two independent reasons rather than one.

### TODO: rebasing onto Velus head

Not started, and deliberately deferred. What a plan will have to account for:

- **What this branch depends on, outside `src/SIF/`.** `Transcription/Tr.v`
  (`to_node`, `to_equation`, `to_global`, `tonodeInv`, `to_node_{name,in,out,vars}`,
  `find_node_global`, `find_node_global'`), `Transcription/TrClocking.v`
  (`wc_node`, `wc_transcription`), `Lustre/LSyntax.v` (node record,
  `vars_defined`, `NoDup_vars_defined_n_eqs`), `Lustre/LClocking.v`,
  `NLustre/NLClocking.v` (`wc_equation`'s three-constructor shape, inverted by
  hand in several places), and `Instantiator.v` (`L`, `NL`, `TR`, `CE`).
  A rebase breaks on any change to those, and the `wc_equation` inversions and
  the `to_equation` case analysis are the brittle ones -- both are written
  against the current constructor lists.
- **The normalisation frontier.** `to_equation` only accepts a normalized
  fragment, and the shapes it accepts are hard-coded in
  `to_equation_{app,app_reset,EqApp,EqApp_reset}_inv` and in the
  `to_equation_entails` dispatcher. If head has changed what normalisation
  produces (extra expression forms, a different reset shape), those are the
  first things to re-derive.
- **Order of attack.** `SecLNameInterface` -> `SecLTyping` ->
  `SecLusNLusTranslation` -> `SecLusConstraintExport` -> `SecLusNonInterference`,
  which is `vfiles` order. The export file is the cheap early warning: it
  applies the whole Lustre stack to `Instantiator`'s real modules, so it fails
  fast if a module type's parameter list moved.
- **What is insulated.** Nothing in the NLustre, Stc or Obc legs was edited, so
  a rebase there is Velus's problem, not this branch's.

### Decision: one naming pass (option A), 2026-09-12

Signature preservation needs the Lustre and NLustre signatures to have the
same interface fields. Reading `generate_node_sig`, each of those fields is a
function of exactly two things: the node's `n_name`/`n_in`/`n_out`, and the
naming environment. The first is preserved -- definitionally by
`to_node_name`/`to_node_in`/`to_node_out`, and by `node_iface_eq` through
`normalize_global_iface_eq`. So everything turns on the environment.

**Two ways to make the environment agree, and the choice between them.**

*Interface-first allocation alone is not enough.* The reorder committed today
makes an interface variable's name independent of *its own node's* locals, but
`generate_node_scoped_env'` threads one counter through the program, so a node
that gains a local shifts every name after it. Measured: a two-node program
whose first node gains one local moves the second node's clock from `sec$9` to
`sec$10` and its output from `sec$12` to `sec$13`, with that node's own
interface untouched. Independent allocation on the source and on the
normalized program therefore still disagrees from the first such node onward.
Fixing that would mean splitting allocation into an interface sweep and a
locals sweep, restating every lemma about `generate_local_env_for_node` across
two stages.

*The paper says not to bother.* (LTndef) reads "Let `α₁,…,αₙ, δ₁,…δₖ,
β₁,…βₘ, γ` be **distinct fresh type variables**" -- it does not say which, and
Theorem 1 then writes the *same* `ᾱ, γ, β̄` on both sides of normalisation. It
is entitled to that only because the rule lets you choose them: a signature is
a scheme and its variable names carry no content. The paper obtains the
coincidence by choosing, not by computing.

**So: the naming pass runs once, and every generator reads its result.** This
is the mechanised form of that choice, it is the discipline the Stc and Obc
generators already follow, and the interface fields then agree by computation
with nothing to discharge. `SecLNameInterface.v` keeps its value: with
`to_global_lscoped_env` the Lustre allocator, run on the normalized program,
*is* the NLustre one, so the Lustre typing can still be presented as
allocating its own names.

Consequences for `SecLTyping.v`, as implemented:

- `generate_lnode_sig` and `generate_all_lsignatures_scoped_env` take `envs`
  and `aux_names` as parameters, like `SECSTCTYPING` and `SECOBCTYPING`.
- They also take and return a `sec_state`, because unlike the NLustre
  generator this one is not `state_pure`: a nested call mints a name per
  result flow. Start the run at the naming pass's final state
  (`generate_lnode_scoped_env_st`) and every minted name is clear of every
  program variable's, both drawing `gensym` from `Ids.sec`.
- `simplify` must eliminate the minted names *as well as* the declared locals.
  `minted st0 st1` reads them back off the state the run consumed. A
  call-output name is local to the node's body exactly as a declared local is,
  and neither may reach the interface -- without this, `signature_scoped`
  fails and the interfaces stop matching. Working the `scaled` example is what
  surfaced this; the NLustre entry point passes only the locals, because
  minted names do not exist there.

**If the Lustre typing is ever wanted genuinely standalone**, the principled
route is not the two-sweep allocator but relaxing `signature_fields_agree` to
a *renaming* of the interface variables -- which is what the paper actually
means, and for which the machinery half exists already, since
`generate_constraints` instantiates a callee signature by substitution. The
cost is generalising `signature_fields_agree` and its uses through
`Signature_head_consistent`, the simplify bridge and the noninterference
transport, which reaches into the Stc and Obc legs.

### Where a new lemma about types goes

A standing rule for this leg, to keep (H1) mechanical rather than a judgement
call each time:

- a property of `SymTypes.ST` / `SymTypes.constraint` that is about the
  **NLustre or Stc level** → append to `SymTypes.v` / `SecTypes.v`;
- a property that is about the **Lustre level, or about the Lustre→NLustre
  bridge on types** → it goes in `SymLusTypes.v` (syntactic) or
  `SecLusTypes.v` (semantic), never in `SymTypes.v` / `SecTypes.v`.

`SymLusTypes.v` and `SecLusTypes.v` are assembled into one `LusTypes.v`
module, the way `Lustre.v` assembles `LSyntax`/`LTyping`/`LClocking`. That is
what keeps the two already-large base modules from growing.

### Where additions are foreseeable

Only two, both append-only, both to files named in (H1) and never to (H2):

1. `SymTypes.v` — possibly a `simplify` stability lemma under permutation of
   its input list, if Leg C's constraint order cannot be made to line up.
   Avoidable if the `preserves_on_Permutation` route (§2) suffices; try that
   first.
2. `SecTypes.v` — possibly `constraintSatisfiable_shrink_lhs` (a constraint
   with a larger left-hand side implies one with a smaller). Needed **only**
   if §5 option (B) is taken. Option (A) avoids it entirely.

If either turns out to need more than an appended lemma, stop and re-plan
rather than editing.

---

## 1. Scope: this is three legs, not one

[ICTAC] calls its target "NLustre", but its Figures 10 and 11 are Velus's
*unnesting* and *fby-initialisation* passes, which are `L.global → L.global`.
Getting to Velus's actual `NL.global` needs transcription on top. Reading
`Lustre/Normalization/Normalization.v:25` and `VelusCorrectness.v:54`:

```
L.global --unnest_global--> L.global --normfby_global--> L.global --to_global--> NL.global
   (full Lustre)              unnested              normalized              NLustre
        ^ Leg C                    ^ Leg B                  ^ Leg A
        [ICTAC] Fig 10             [ICTAC] Fig 11           not in [ICTAC]
```

| leg | Velus pass | [ICTAC] | what it costs SIF |
|---|---|---|---|
| **C** | `unnest_global` | Fig 10, `Xcnst`–`Xeqs` | **the novel leg.** de-nesting discharges refinement types into equations; fresh locals per subexpression |
| **B** | `normfby_global` | Fig 11 | one fby → three equations (`xinit`, `px`, `ite`); fresh locals, no calls |
| **A** | `to_global` | — | one-to-one; **constraint equality**, not preservation |

Each Velus pass has its own forward semantics theorem
(`unnest_global_sem`, `normfby_global_sem`, composed as
`normalize_global_sem` at `Lustre/Normalization/Correctness.v:2611`; then
`Transcription/Correctness.sem_l_nl:700`). All of them preserve `ins`/`outs`
**as the same stream objects**. That is what makes §6 cheap.

**Recommended order: type system → A → B → C.** A is the cheapest and
validates the new generator against the already-proved NLustre one; B is local
and call-free; C is the research contribution. Do not start C until A and B
compile.

---

## 2. The types: refinement types as a pair, `SymTypes.v` untouched

[ICTAC] §3 extends the NLustre type algebra with **refinement types**:

```
α, β ::= ⊥ | δ ∈ STV | α ⊔ β | α{|ρ|}          ρ ::= (θ ⊑ α)*
```

`α{|ρ|}` is "type α, provided ρ holds"; `s(α{|ρ|}) = s(α)` when `s` satisfies
`ρ` and is **undefined otherwise**. They exist for exactly one reason: a node
call *inside an expression* has to publish the callee's instantiated
constraints without an equation to hang them on (rule `LTncall`).

The current development has `SymTypes.ST := list ident` (sorted, dup-free) and
`constraint := ST * ST` (`SymTypes.v:11`). Changing `ST` would break every
NLustre, Stc and Obc proof. Do not.

**Design decision: represent `α{|ρ|}` as the pair `(α, ρ)`.**

```coq
(* new file SymLusTypes.v *)
Definition LST : Type := (SymTypes.ST * list SymTypes.constraint)%type.
Definition lbot  : LST := ([], []).
Definition lvar (d : ident) : LST := ([d], []).
Definition ljoin (a b : LST) : LST := (fst a ⊔ fst b, constraint_merge (snd a) (snd b)).
Definition lrefine (a : LST) (r : list constraint) : LST := (fst a, constraint_merge (snd a) r).
(* the hoisting rule, [ICTAC] Fig 5 line 4 *)
Definition lconstrain (a : LST) (b : ident) : list constraint :=
  constraint_merge [(fst a, [b])] (snd a).
```

`constraint_merge` is **already in `SymTypes.v:1250`** — a sorted merge over
`constraint_compare` whose `Eq` branch keeps one copy. It is therefore
associative, commutative, idempotent and unital on canonical lists: the ACUI
union Figure 5 asks for, already in the repo, no addition needed.

Under this representation **every equation of [ICTAC] Figure 5 holds
definitionally or by `constraint_union` being ACUI**:

| [ICTAC] Fig 5 | here |
|---|---|
| `α{||} = α` | `lrefine a [] = a` |
| `α1{|ρ1|} ⊔ α2{|ρ2|} = (α1⊔α2){|ρ1∪ρ2|}` | the definition of `ljoin` |
| `α{|ρ1|}{|ρ2|} = α{|ρ1∪ρ2|}` | associativity of `constraint_merge` |
| `vec(αi){|ρ|} = vec(αi{|ρ|})` | `map (fun a => lrefine a r)` |
| `{α{|ρ1|} ⊑ β{|ρ2|}} = {α⊑β} ∪ ρ1 ∪ ρ2` | the definition of `lconstrain` |
| substitution distributes | componentwise |

Should any Fig-5 equation resist a *syntactic* proof, there is a second line
of defence that also needs no changes: satisfaction of a constraint list is a
`Forall`, and `SecTypes.v:1185,1196` already proves
`listSatisfiable_Permutation` and `preserves_on_Permutation`. The Stc→Obc leg
already runs on that footing — its generated list is a permutation of the
source's, not equal to it. So the Fig-5 theory can be stated at satisfaction
level rather than syntactically wherever that is more convenient.

**Consequence: [ICTAC] Lemma 2 (confluence modulo AC, Knuth–Bendix completion,
strongly-coherent rewriting) is not mechanised at all.** It is a statement
about deciding equality of *terms* in the type algebra; choosing a canonical
representation discharges it by construction, exactly as [POPL]'s "Notes on
formalisation" says Lemma 1 is discharged by `sortST` today. Say this
explicitly in `docs/` — a reader of the paper will look for it.

`lconstrain` is where refinement obligations *leave* the type and enter the
constraint set, and it is the only place they can. That single choke point is
what keeps the rest of the development on the existing `constraint` type, so
`simplify`, `preserves_on`, `SIFSignature.generate_constraints` and every
correctness lemma in `SecTypes.v` apply unchanged.

**Degeneracy lemma** (needed by Legs A and B):

```coq
Lemma unnested_exp_no_refinement :
  unnested_exp e -> assign_lexp_type env e = Some tys -> Forall (fun t => snd t = []) tys.
```

After Leg C every `LST` has an empty refinement component, so `LST` collapses
to `ST` and Legs B and A never see a refinement type. Prove this early; it is
what lets the *same* generator serve all three Lustre stages.

---

## 3. `SecLTyping.v`: typing full Lustre

One generator, defined on the full `L.exp` — not on a normalized subset.
Section variables mirror `SECNLUSTYPING`'s (`G : secglobal`, `env : Env.t
ident`, `base_ty`, `rst_ty`) plus `cenv : Env.t (type * clock)`, the clock
environment `to_equation` consults (`Tr.v`, `to_node`).

### Expressions — `assign_lexp_type : L.exp -> Sec (list LST)`

Returns a **list**, one `LST` per flow: Lustre expressions denote flow lists
and [ICTAC] Fig 7 is componentwise throughout. It lives in `Sec`, not
`option`, because the call case mints fresh names.

| `L.exp` | [ICTAC] rule | result |
|---|---|---|
| `Econst c` | LTcnst | `[lbot]` |
| `Evar x _` | LTvar | `[lvar (env x)]` |
| `Eunop _ e _` | LTunop | type of `e` |
| `Ebinop _ e1 e2 _` | LTbinop | `ljoin` componentwise |
| `Ewhen es x b _` | LTwh | `map (fun a => ljoin a (lvar (env x))) tys` |
| `Emerge x ets efs _` | LTmrg | `θ ⊔ αi ⊔ βi` componentwise |
| `Eite e ets efs _` | LTite | `θ ⊔ αi ⊔ βi` componentwise |
| `Efby e0s es _` | LTfby | `αi ⊔ βi` componentwise |
| `Earrow e0s es _` | **not in [ICTAC]** | same as `Efby` — see §7 |
| `Eapp f es er _` | LTncall | see below |

### The call case — the novelty

`LTncall` gives `f(e⃗)` the type `β⃗{|ρ'|}` with `ρ' = ρ[γ'/γ][α'/α⃗]`. The
`β⃗` are per-call-site and must be **freshly minted**, because a nested call
has no declared variable to borrow a name from. `SecContext.fresh_ident`
(`SecContext.v:43`, `Ids.gensym Ids.sec`) already does this, and
`SIFSignature.generate_constraints` already performs exactly the substitution
`ρ[α'/α⃗][β'/β⃗][γ'/γ][κ'/κ]` and reorders the result into caller-output order.
So:

```coq
| Eapp f es er anns =>
    do argtys <- mmap assign_lexp_type es;          (* list LST, then flatten *)
    do sg     <- find_signature f G;
    do rstty  <- lreset_type er;                    (* see below *)
    do outs   <- fresh_idents (length anns);        (* the per-call-site β⃗ *)
    do cs     <- generate_constraints sg (map fst (concat argtys)) ckty rstty outs;
    ret (map (fun o => (([o] : ST),
                        constraint_union cs (union_all (map snd (concat argtys)))))
             outs)
```

Each output flow gets type `o_i` refined by the call's instantiated
constraints **plus** everything floated up out of the arguments — which is
`β{|ρ'|}` composed with Fig 5's `α1{|ρ1|} ⊔ α2{|ρ2|}` rule. Nested calls
compose because `ljoin` unions refinements; nothing special is needed for
depth.

`ckty` here is the type of the call's base clock, computed the way
`to_equation` computes it (`find_base_clock (L.clocksof es)`) so Leg A lines
up (§5).

**Where the per-call-site names come from.** `SecContext.fresh_ident`
(`SecContext.v:43`) mints `Ids.gensym Ids.sec n` -- the *same prefix*
`NameInterface.fresh_ident_gen` (`NameInterface.v:318`) uses for program
variables' security names. It has no users today, because every existing
generator is `state_pure` (`SecContext.v`, "State-pure computations"): they
look names up, they never mint. The Lustre call case is the first that must
mint, so the collision is real and would break every freshness and scopedness
fact downstream (`generate_node_env_sec_range`, `env_sec_bounded`, ...).

Adding a fourth prefix to `Ident.v` is out -- that file is outside `src/SIF`.
The fix needs no edit anywhere: **run the equation generator from the naming
pass's final state rather than from `SC.init_state`.** Every name it then
mints is `Ids.gensym Ids.sec n` with `n` at or above that bound, so it is
fresh from every program-variable name by the bound facts `NameInterface.v`
already proves (`generate_local_env_for_node_fresh_from_bound`,
`generate_node_scoped_env'_bounded`).

`generate_node_scoped_env` discards that final state, but
`generate_node_scoped_env'` -- which `SecNLusStcTranslation.v` already calls
directly -- returns it. `SecLNameInterface.v` therefore runs the primed form
and keeps the state, and `NameInterface.v` is not touched.

**Two degeneracy facts, not one.** On an unnested expression the generator
mints nothing and carries nothing, so *both* `lst_plain` (empty refinement,
`SecLusTypes.v`) and `state_pure` hold. They are what make Leg A an equality:
the NLustre generator is state-pure and its types are plain, and on the
normalized fragment so is this one.

**Reset in nested position is new work beyond both papers.** [ICTAC] has no
`reset` at all; [POPL] added reset-stacking but only for NLustre, where the
reset is an `(ident * clock)`. In full Lustre `er : option exp` is an
arbitrary expression (`unnest_reset` only makes it an `Evar` later). So
`lreset_type` must type an *expression* and join it onto the ambient reset the
way (NTrc) does:

```
lreset_type None       = [rst_ty]
lreset_type (Some er)  = [rst_ty] ⊔ (type of er)        (* refinements float *)
```

This is the one rule with no precedent in either paper. Flag it in `docs/`
and in the paper draft: it is the point where [ICTAC]'s refinement types and
[POPL]'s reset-stacking have to be combined, and neither source covers it.

### Equations — [ICTAC] `LTeq` plus reset

```
Γ ⊢ x⃗ =ck e⃗ :> { (κ ⊔ γ ⊔ αi ⊑ βi)i } ∪ (floated refinements)
```

i.e. `map2 lconstrain tys (get_mappings xs env)` after joining in
`[rst_ty] ⊔ ckty` — `lconstrain` does the hoisting, so the refinements land in
the constraint list automatically. The `κ` (ambient reset) is [POPL]'s
addition to [ICTAC]'s rule; keep it, the NLustre generator has it and Leg A
needs the two to match.

### Node and global

`generate_lnode_sig`, `generate_lnode_sig_scoped_env`,
`generate_all_lsignatures'`, `generate_all_lsignatures_scoped_env` — same
shapes and same names as `SecNLusTyping.v`, and the same `simplify` over the
node's local type variables ([ICTAC] `LTndef`, Fig 9 — which is the *same*
`simplify` as `SymTypes.simplify`, generalised there to types-and-constraints
pairs; our pair representation means the generalisation is free).

Generate over `rev nodes` for the accumulator reason recorded in
`docs/proof_outline.md`.

### Naming

`SecLNameInterface.v`: a functor `SECLNAMEGEN (Ids)(Op)(LSyn)(NAMEGEN)` that
reuses NAMEGEN's `Name` monad and `fresh_*` combinators — they are
`Definition`s inside the functor, so a client functor can use them and
`NameInterface.v` needs no edit. It provides `gather_linsts` (the Lustre
spelling of `NLSyntax.gather_inst_eq`) and `generate_lnode_scoped_env`, plus:

```coq
Lemma generate_lnode_scoped_env_to_global :
  to_global LG H = OK P -> generate_lnode_scoped_env LG = NAMEGEN.generate_node_scoped_env P.
```

which holds because `to_node` keeps `n_name`/`n_in`/`n_vars`/`n_out`
**definitionally** and `to_equation` keeps `xs` and `f`. This is what lets
every Lustre-side statement reuse the `envs`/`aux_names` the NLustre stack
already threads.

Across Legs B and C the environment does **not** stay equal — those passes add
locals. There the relation is `env ⊆ env'` plus freshness of the additions,
which is exactly the `node_scope_fresh_in_env` / extras discipline the Stc leg
already uses.

---

## 4. Preservation: what to reuse, what is new

[ICTAC] Theorem 1 is `s(ρ) ⟹ s(ρ')` — source constraints imply target
constraints, same direction as [POPL] Theorem `THM:STCSecurityTypePreservation`
and the same direction as `SecTypes.preserves_on`. So the existing vocabulary
applies verbatim:

- `signatures_preserved`, `signature_fields_agree`, `scope_fresh`,
  `call_subst_fresh`, `call_subst_scoped` — all in **`SIFSignature.v`**
  (`:3408`, `:255`, `:288`), reusable directly.
- `Signature_call_preserves`, `Signature_head_consistent`,
  `Signature_consistent` — these sit *inside* the `SECNLUSSTCTRANSLATION`
  module type (`SecNLusStcTranslation.v:109,114`), so using them would mean
  instantiating that functor and dragging Stc in. **Re-declare the three in
  the Lustre translation file** — they are three short definitions over
  `signature` and `preserves_on`. Duplication is the right trade here: it
  keeps the Lustre leg from depending on the Stc leg at all. A later refactor
  could lift them into `SIFSignature.v` alongside `signatures_preserved`,
  which is where the first one already migrated.
- `preserves_on_concat_scoped` (`SecTypes.v`) — **this is the load-bearing
  reuse**. The Stc leg built it so that translated blocks could be
  concatenated while each block's private *reset-instance extras* stayed
  outside the shared scope. In Leg C the fresh variables that
  `idents_for_anns` / `idents_for_anns'` / `unnest_noops_exps` /
  `unnest_reset` introduce play exactly that role. Same lemma, different
  extras.
- `SIFSignature.generate_constraints_correct_inst` /
  `generate_constraints_complete_good` — the call replay metatheory, which is
  [ICTAC] Lemma 4 (Security of Node Calls) in mechanised form. Already proved.
- `SymTypes.simplify` + `simplify_is_correct` / `simplify_complete` —
  [ICTAC] Lemma 3. Already proved.

What is genuinely new per leg:

**Leg A — `SecLusNLusTranslation.v`.** Equalities, not preservation.
`to_lexp`/`to_cexp`/`to_equation` are structural, `to_node` preserves the
interface definitionally, so with the generator written case-for-case against
them (§5) the generated `signature` values come out **equal**. Then
`signatures_preserved` is `preserves_on_refl`, and no analogue of
`generated_signatures_preserved_from_simplify_bridge_scoped` is needed. Est.
900 lines.

**Leg B — `SecLusNormFbyTranslation.v`.** [ICTAC] Fig 11. One source equation
`x =ck e0 fby e` becomes `xinit =ck true fby false`, `px =ck c fby e`,
`x =ck if xinit then e0 else px`, with `xinit`/`px` fresh. Two fresh locals per
fby, both defined once, both eliminated by `simplify`; the composite
constraint `γ ⊔ δ1 ⊔ α ⊔ δ2 ⊑ θ` reduces to the source's `γ ⊔ α ⊔ β ⊑ θ` by
`simplify_is_correct` case (1). No calls involved, so no signature replay.
This is the leg to cut your teeth on. Est. 1200 lines.

**Leg C — `SecLusUnnestTranslation.v`.** [ICTAC] Fig 10, Theorem 1. The real
one. Structure it as the Stc leg is structured:

1. `lexp_preserv` — one source expression, by induction on `unnest_exp`'s
   recursion, relating the source `LST` list to (target expression types +
   target equation constraints). **The induction hypothesis has to say that
   the refinement component of the source type is implied by the constraints
   of the generated equations.** That sentence is the whole theorem; write it
   down before writing any Coq.
2. `leqn_preserv` — one source equation, via `unnest_rhss` + `split_equation`.
3. `leqns_preserv_scoped` — the list fold, gluing with
   `preserves_on_concat_scoped`, accumulating the fresh idents of each block
   as extras (mirrors `eqns_preserv_scoped` and `eqns_reset_extras`).
4. `lnode_preserv_scoped`, then the simplify bridge, then
   `generate_all_lsignatures_consistent'` — the lockstep global induction,
   mirroring `generate_all_signatures_consistent_scoped'` step for step.

Est. 3000–4000 lines, i.e. comparable to `SecNLusStcTranslation.v`.

**The `is_control` flag.** `unnest_exp` takes `is_control : bool` and does
*not* allocate fresh variables for `Emerge`/`Eite` when it is set. Both
branches must be covered by `lexp_preserv`; the `is_control = true` branch is
the easy one (no extras), the `false` branch allocates. Do not try to unify
them — two cases, stated separately, like the ordinary/reset call split in the
Stc leg.

---

## 5. Leg A in detail: aim for equality

Write `assign_lexp_type` so that its `normalized_lexp` / `normalized_cexp`
cases coincide with `SecCETyping.assign_exp_type` / `assign_cexp_type` on the
transcribed expression:

```coq
Lemma to_lexp_assign_eq : to_lexp e = OK le -> assign_exp_type env le = Some a -> assign_lexp_type env e = ret [(a, [])].
Lemma to_cexp_assign_eq : (* same for cexp *)
Lemma to_equation_constraint_eq :
  to_equation cenv envo eq = OK eq' ->
  generate_leqn_constraint G env base_ty rst_ty cenv eq = generate_eqn_constraint G env base_ty rst_ty eq'.
Lemma to_node_sig_eq / to_global_signatures_eq : (* lift to node and global *)
```

Each of the four `normalized_equation` shapes
(`Lustre/Normalization/NormFby.v:392`) maps to one NLustre equation, so each
is a direct case split. Compute the clock the way `to_equation` does:
`find_clock cenv x` for `EqDef`/`EqFby`, `find_base_clock (L.clocksof es)` for
`EqApp`, and the reset `Evar`'s **annotation** clock for the reset call.
Keeping the two generators syntactically aligned is the standing invariant for
this development; it is what makes this leg equalities rather than a second
simplify bridge.

**One asymmetry to decide.** `to_constant` strips the `when`s off a `fby`
initial value, so the NLustre side loses the sampling variables' types. Two
options:

- **(A) recommended.** Match [ICTAC] Fig 11 and [POPL] (NTfb): the initial
  constant contributes `⊥`. Exact equality in all four cases. Not a real
  weakening — `add_whens` builds `e0` with exactly the `when`s of `ck`, so each
  `Γ(yᵢ)` is already joined in through `ckty`.
- (B) type `e0` fully. Equality is lost, the statement becomes `preserves_on`,
  and it needs a new lemma `constraintSatisfiable_shrink_lhs` plus a full
  simplify-bridge analogue.

Take (A). Note that this asymmetry is *created by Leg B*, so state the
`⊥`-for-constant convention once, in Leg B's rule, and let Leg A inherit it.

---

## 6. Noninterference: the pull-back, exactly as [ICTAC] Theorem 5

This leg does **not** re-attack the semantics. [ICTAC] Theorem 5's proof
sketch is: well-typed Lustre → (Theorem 1) well-typed NLustre → (Theorem 4)
NLustre noninterference → (Theorems 2,3: semantics preservation) Lustre
noninterference. We have Theorem 4 already
(`SecNLusNonInterference.node_noninterference_outputs`) and Velus has
Theorems 2 and 3. So:

```
LS.sem_node LG f ins outs                                      (two runs)
  --Normalization.Correctness.normalize_global_sem-->  LS.sem_node G' f ins outs
  --Transcription.Correctness.sem_l_nl-->              NLSC.sem_node P f ins outs
  --NL.CoindToIdx.implies-->     Indexed.sem_node P f (tr_Streams ins) (tr_Streams outs)
  --NLusSupport.sem_node_inv-->  bk, H, Forall Indexed.sem_equation, sem_vars
  --lnode_security_transfer-->   node_security P G envs aux n dlt_sig dlt_raw
  --node_noninterference_outputs--> history_low_eq on n_out
  --tuple_stream_low_eq_of_history_low_eq + conversion--> conclusion
```

Every arrow is forward and every arrow keeps `ins`/`outs` as the *same*
streams, so the transport is `nth_error`/`Str_nth` bookkeeping, not semantics.

`lnode_security_transfer` is the one real obligation: an inductive
`lnode_security` mirroring
`SecNLusNonInterferenceSupport.node_security` over the Lustre generators, and

```coq
Lemma lnode_security_transfer :
  l_to_nl LG = OK P -> to_node ln _ = OK n ->
  lnode_security LG GL envs aux ln dlt_sig dlt_raw ->
  node_security P G envs aux n dlt_sig' dlt_raw'.
```

Through Leg A the valuations are **the same** (constraints are equal).
Through Legs B and C they are not: `preserves_on` produces a new valuation
agreeing with the old on the visible signature scope. That agreement is
exactly what keeps `low_var` classification of the node's inputs and outputs
unchanged, so the low-equivalence hypothesis and conclusion still speak about
the same set of variables. `SecTypes.agree_on` + `preserves_on` already carry
this; do not invent a new relation.

Note the direction contrast, and write it in `docs/`: the Stc and Obc legs
**push** noninterference forward from NLustre to their targets; this leg
**pulls it back** to the source, because NLustre is downstream here. [POPL]
`stc_correctness.tex:11` records the same observation about the two papers.

Exported theorem (mirrors
`SecStcNonInterference.translated_system_noninterference_outputs` in shape):

```coq
Theorem lnode_noninterference_outputs :
  ... ->
  lnode_security LG GL envs aux_names ln dlt_sig dlt_raw ->
  lnode_behavior LG ln ins  outs  ->
  lnode_behavior LG ln ins' outs' ->
  <base clocks agree> ->
  lustre_stream_low_eq ty_env dlt_sig t (map fst ln.(n_in))  ins  ins' ->
  lustre_stream_low_eq ty_env dlt_sig t (map fst ln.(n_out)) outs outs'.
```

with `lnode_behavior LG ln ins outs := LS.sem_node LG ln.(n_name) ins outs /\
LCS.sem_clock_inputs LG ln.(n_name) ins` — the second conjunct is what both
`normalize_global_sem` and `sem_l_nl` demand.

Carry the same source-to-target direction note the other exported theorems
carry: hypotheses constrain *Lustre* runs, conclusion constrains *Lustre*
outputs, even though every transport lemma inside reads NLustre-ward.

### Causality

`sem_l_nl` wants `Forall LCA.node_causal`; the NI theorem wants
`NLCaus.nl_global_causal`. `docs/NLustreCausalityBridge.md` already specifies
the missing file:

```coq
Theorem to_global_causal : to_global G H = OK P -> Forall LCA.node_causal G -> NLCaus.nl_global_causal P.
```

`normalize_global_causal` supplies the Lustre side for real programs.
**Deferrable** — until `SecLusNLusCausality.v` exists, carry
`nl_global_causal P` as an extra hypothesis and say so in the docs.

---

## 7. Beyond both papers — call these out explicitly

Four things this mechanisation must handle that neither paper covers. Each
needs a paragraph in `docs/` and, eventually, in the paper draft.

1. **`Earrow`.** Not in [ICTAC]. Type it like `Efby` (componentwise join);
   `normfby_global` turns it into `fby` + `ite`, so Leg B must cover it too.
2. **Reset in nested position** (§3). `Eapp`'s reset is an arbitrary
   expression in full Lustre. This is where [ICTAC]'s refinement types and
   [POPL]'s reset-stacking meet, and neither source says how.
3. **`unnest_noops_exps`.** Unnesting introduces *further* fresh variables for
   call arguments that are not "noops" under the callee's input clocks
   (`Unnesting.v:1960`). More extras for `preserves_on_concat_scoped`; no new
   idea, but it is not in Fig 10.
4. **`is_control`** (§4). Fig 10 has no analogue of the control-position
   optimisation, which changes whether `Emerge`/`Eite` allocate fresh
   variables.

And one thing the mechanisation does *not* need: **[ICTAC] Lemma 2**
(confluence modulo AC / Knuth–Bendix completion). §2 discharges it by
representation.

---

## 8. Files, in `vfiles` order

Insert after `SecNLusTypingTotality.v`, before `SecSTCTyping.v`: the leg
depends on the NLustre generator and on nothing downstream of it. `_CoqProject`
is generated — add to **`vfiles`** and re-run `./configure`.

| # | file | mirrors | est. |
|---|---|---|---|
| 1a | `SymLusTypes.v` | `SymTypes.v` (syntactic layer) | 900 |
| 1b | `SecLusTypes.v` | `SecTypes.v` (semantic layer) | 700 |
| 1c | `LusTypes.v` | `Lustre.v` (module assembly) | 80 |
| 2 | `SecLNameInterface.v` | `NameInterface.v` node-level allocators | 250 |
| 3 | `SecLTyping.v` | `SecNLusTyping.v` | 1400 |
| 4 | `SecLTypingCorrectness.v` | `SecNLusTypingCorrectness.v` | 900 |
| 5 | `SecLusNLusTranslation.v` (Leg A) | — | 900 |
| 6 | `SecLusNormFbyTranslation.v` (Leg B) | `SecNLusStcTranslation.v` | 1200 |
| 7 | `SecLusUnnestTranslation.v` (Leg C) | `SecNLusStcTranslation.v` | 3500 |
| 8 | `SecLusNLusCausality.v` | spec in `docs/NLustreCausalityBridge.md` | 400 |
| 9 | `SecLusNonInterference.v` | `SecStcNonInterference.v` | 500 |
| 10 | `SecLusConstraintExport.v` | `SecNLusConstraintExport.v` | 200 |

`Instantiator.v:17,25` already exposes `L` and `TR`, so file 10 is a copy of
`SecNLusConstraintExport.v` with `NL.Syn` → `L.Syn`.

Docs, one per Coq file (house rule), plus:

- `docs/SymLusTypes.md` — the syntactic layer and the confluence result (§2).
- `docs/SecLusTypes.md` — the semantic layer: partial ground instantiation,
  satisfaction, and the bridge to `SecTypes.preserves_on`.
- `docs/Lus-noninterference-proof.md` — must state §6's push/pull contrast.
- update `docs/proof_outline.md` (new "Source Language Leg" section) and
  `docs/NLustreCausalityBridge.md` once file 8 lands.

---

## 9. Milestones

0. **Done.** `SymLusTypes.v` (algebra + confluence, no axioms), `SecLusTypes.v`
   (semantics, `lconstrain_sound`), `LusTypes.v`, `SecLNameInterface.v`
   (`to_global_lscoped_env`), interface-first allocation, `SecLTyping.v`
   through expression, equation, node and global level, and **Leg A complete**
   in `SecLusNLusTranslation.v`, ending at `to_global_all_signatures_eq`:
   on a program that transcribes, the Lustre generator produces the *same*
   signature global as the NLustre one.

   Three notes for the legs still to come.  Reduce by stepping binds
   (`bind_OK`, `bind2_OK`) and the per-shape reduction lemmas, never by a
   blanket `simpl` -- that unfolds `SymTypes.merge` into its inner `fix` on
   one side of a goal only.  Write generators with nested matches, on the
   expression list before the defined variables, or the `[x]` patterns leave
   the term stuck on any equation whose variable list is not literal.  And
   state these theorems NLustre-to-Lustre: equality of the two `Sec`
   computations is false where generation fails, since the generators report
   different messages, and the NLustre totality theorem makes the one
   direction sufficient.

   Next: Leg B (`normfby_global`), then Leg C (`unnest_global`).

1. `SymLusTypes.v` compiles; Fig-5 rewriting confluent, `lty_eq a b <-> norm a = norm b`.
1b. `SecLusTypes.v` compiles; Lemma 1 (soundness) proved; degeneracy lemma proved.
1c. `LusTypes.v` assembles the two.
2. `SecLNameInterface.v` compiles; `generate_lnode_scoped_env_to_global` proved.
3. `SecLTyping.v` compiles with its structural lemmas `admit`ted.
4. **Leg A equalities proved.** This is the first real checkpoint: it says the
   new generator agrees with the already-verified NLustre one. If exact
   equality does not close here, fall back to §5-(B) and re-plan.
5. Back-fill `SecLTyping.v` / `SecLTypingCorrectness.v` from the equalities.
6. **Leg B / Leg I: pending.** First genuine `normfby_global` preservation,
   call-free.
7. **Leg C / Leg U: in progress.** Expression and arbitrary-equation
   preservation are complete; conditional raw node composition is complete;
   concrete `unnest_node` and `unnest_global` signature preservation remain.
8. `SecLusNonInterference.v` — the exported Lustre theorem.
9. `SecLusNLusCausality.v`; drop the extra hypothesis.
10. `SecLusConstraintExport.v`; run it on `tests/`.

Commit at each milestone, plain messages, no AI attribution.

---

## 10. Build protocol

Compile **only** in docker container `funny_franklin`; `/workspace` is a copy,
not a mount.

```
# new file: add to vfiles first (git-tracked; _CoqProject is generated)
docker cp vfiles           funny_franklin:/workspace/vfiles
docker cp src/SIF/F.v      funny_franklin:/workspace/src/SIF/F.v
docker exec funny_franklin bash -lc 'cd /workspace && ./configure -clightgen x86_64-linux'
docker exec funny_franklin bash -lc 'cd /workspace && make -j4; echo $?'
```

`make <path>.vo` is **not** a valid target — it exits 0 having done nothing.
Only bare `make` is evidence. Single-file iteration via
`coqc <the -R lines of _CoqProject> src/SIF/F.v`, but always finish with
configure + `make`.

---

## 11. Leg U — where the induction stands

*History, long superseded. See [Leg U — current state](#leg-u--current-state).*

**Blocker 1, cleared: the clock environment.** `generate_leqns_constraints`
reads declared clocks through `eqn_clock_type`, so the two generators cannot
be compared until the two `lnode_clock_env`s are known to agree. Unnesting
leaves `n_in`/`n_out` alone and appends to `n_vars`; the *target* node's own
`n_nodup` says the appended names are fresh for the declared ones, which
rules out `Env.adds'` shadowing. `lnode_clock_env_extended` /
`find_clock_extended`. Freshness is read off the node the pass returns, not
assumed.

**Blocker 2, found and designed around: `agree_on` does not compose.**
The first statement had the witness only fixing `scope`. That is too weak:
it leaves the witness free to move the names the security monad minted for a
*sibling* sub-expression, and the sibling's hypothesis still has to be applied
to constraints over exactly those names. The statement now bounds where the
witness may move (`agree_off`), and indexes that bound by the **pair** of
fresh states (`moved_by st st'`), so siblings move over disjoint stretches.
`agree_on scope` comes back out via `agree_off_agree_on`.

Two further conclusions were forced by the same argument and are now part of
the statement: `constraints_scoped (scope ++ moved_by st st') ce` and the
same bound on the target types. Without them nothing stops a later sibling
from moving the names an earlier one's conclusion mentions.

Two hypotheses are now explicit: `env_injective env` (distinct variables get
distinct security names — so disjoint variable sets give disjoint name sets)
and `st_scoped scope amb` (the ambient names program variables only).

**Cases proved:** `Econst`, `Evar`, `Eunop`, `Ebinop`. `Ebinop` is the first
real composition and validates the whole design.

**Remaining, in order of content:**
- the list cases (`unnest_exps` / `map_bind2`) — a fold of the `Ebinop`
  argument, needs `Forall (carries P) es -> carries_list P es`;
- `Ewhen` — no lifting, but list-shaped, and `unnest_when` is a map;
- `Emerge` / `Eite` — split on `is_control`: the control branch does not
  lift, the other mints with `idents_for_anns`;
- `Efby` / `Earrow` — lift, four of the five lifting constructors; the
  target type is a fresh variable and the emitted equation's constraint is
  what pins it, so the witness is *chosen* to make the domination tight;
- `Eapp` — the case the refinement machinery exists for; the helper lemmas
  (`Eapp_and_emitted_shape`, `Eapp_renaming_lists`,
  `subst_constraints_out_map_{correct,complete}`) are already in place.

**The one honest premise still to discharge**, and it is a clocking fact,
not a security one: `amb` must dominate the ambient of every equation the
pass lifts out. For `Efby`/`Earrow` the lifted variable carries the
annotation's own clock, so it matches the enclosing equation exactly. Under a
`merge`/`ite` branch the lifted clock is `ck on x`, higher than the equation's
`ck` — but `x`'s level is in the *source type* of the `merge`, so the bound
still holds. Turning that into a lemma needs `wc_exp` and a
"clock level is dominated by expression type" fact about `assign_clk_type`,
which does not exist yet.

### Leg U — cases proved, and what each one forced

*History: this list stops at `Emerge` under `is_control`. See
[Leg U — current state](#leg-u--current-state).*

`Econst`, `Evar`, `Eunop`, `Ebinop`, the list level, `Ewhen`,
`Emerge` under `is_control`.  Each new case has changed the statement once,
and in every case the change was forced rather than chosen:

- **`Ebinop`** forced the witness bound (`agree_off`, indexed by the pair of
  fresh states) and the two scoping conclusions.
- **the list level** forced nothing — it is the `Ebinop` argument folded,
  which is the evidence that the statement had settled.
- **`Emerge`/`Eite`** forced `is_control` into the statement (their branches
  unnest under `true`), and forced the *purity* of the generator on the
  pass's output: `unnest_merge` interleaves the two branches where
  `assign_lexps` takes one and then the other, and purity is what makes the
  order stop mattering.
- **`Eite`** forced the clocking judgement in.  An `Eite` with no result
  streams drops its scrutinee from the target expression list while still
  emitting the scrutinee's equations, so the scrutinee's hypothesis could not
  be applied; `wc_Eifte` requires at least one stream and rules it out.
  `wc_exp` is needed later anyway — it is what will discharge the ambient.
- **`Eite`** also forced the generator's result length (one flow per stream),
  since the scrutinee's target type is read out of the first resulting
  stream.

Standing hypotheses, all true and all discharged at the node level:
`env_injective env`, `st_scoped scope amb`, and the ambient's syntactic
containment premise.

Next: assemble `carries_at P true (Eite ...)` from the pieces (all now in
place), then the two lifting branches, `Efby`/`Earrow`, and `Eapp`.

### The next decision: which state-validity invariant to carry

*History: this decision was taken. See [Leg U — current state](#leg-u--current-state).*

The four lifting constructors (`Emerge`/`Eite` without `is_control`,
`Efby`/`Earrow`) and `Eapp` all end by minting one variable per result with
`idents_for_anns` (`idents_for_anns'` for the call).  The witness is then
*chosen* on those names -- each gets exactly the value its emitted equation's
constraint demands -- and `upds` / `hm_ext_upds` are in place for that.

What is missing is that the minted names are **new**, i.e. that their
security names land in `moved_by st st'` rather than somewhere the statement
forbids moving.  In Velus that is only true under the pass's own
state-validity invariant, and the shape of that invariant is a real choice:

- `st_valid_after st norm1 aft` is the simpler one, and
  `idents_for_anns_st_valid_after` preserves it -- but Velus proves **no**
  `st_valid_after` preservation for `unnest_exp` itself, only for
  `idents_for_anns`.
- `st_valid_reuse` is what `unnest_exp_st_valid` actually threads, and it is
  what `Eapp` needs anyway, since `idents_for_anns'` may *reuse* a name from
  the reusable set rather than mint one.  The cost is that the premise is not
  uniform across a constructor's operands: the reusable set shrinks, so the
  premise for a sub-expression is `ps_adds (map fst (fresh_in e)) reusable`
  where the parent's is `reusable`.

`st_valid_reuse` is the one to carry: it is what the pass's own induction
carries, it is the only one strong enough for the call case, and matching the
pass's discipline is what makes `unnest_exp_st_valid` reusable rather than
re-derived. The shrinking set is threaded exactly as `unnest_exp_st_valid`
threads it.


**Superseded.** The state-validity decision above is no longer the one taken.
`unnest_exp_vars_perm` gives `Permutation (vars_defined eqs ++ st_ids st)
(st_ids st')`, so a single `NoDup` premise delivers everything the lifting
cases need of freshness, uniformly and without the shrinking reusable set.
See `docs/SecLusUnnesting.md`.
