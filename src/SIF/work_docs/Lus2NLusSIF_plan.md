# SIF for Lustre: refinement security types and Lustre→NLustre preservation

Target branch: `Lus2NLusSIF`.

> **Where things stand is in one place: [Leg U — current state](#leg-u--current-state).**
> That section is rewritten in place and is the only Leg U status to trust.
> Everything below it dated `2026-09-xx` is history, kept for the reasoning,
> and may describe designs that were later found wrong.  Each such section
> says so at its head.

## Leg U — current state

*Rewritten in place. Last checked against a clean `make -j1` on 2026-09-25.*

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

*Pointwise contract* (`carries_at_streams`, one ambient per stream) -- **the
expression level is closed** (2026-09-30):

  * every constructor: `Econst`, `Evar`, `Eunop`, `Ebinop`, the list fold
    (`carries_list_streams_intro`), `Ewhen`, `Emerge` and `Eite` in both
    their control and lifting forms, `Efby`, `Earrow`, and now
    `carries_Eapp_streams`;
  * `carries_exp_streams` and `carries_exps_streams` -- the induction, with
    `wc_global P` and `CALLS.sig_inputs_ok GL P` as its only two premises.

What the call case needed that the scalar one did not:

  * `reset_step_streams`.  The scalar `reset_step` **cannot** be reused: its
    ambient premise is a containment for *every* variable the reset's
    unnesting lifts, which is exactly the premise the pointwise contract
    exists to avoid.  In its place go the two facts the rest of the streams
    development uses -- the reset expression has one stream, so one ambient
    covers it (`clocks_covered`), and the variable `unnest_reset` binds it
    to carries that same stream's clock, which `state_clocks_found` reads
    back.  Run at `merge (merge [rst_ty] ckty) rck`, its conclusion
    collapses into what the transfer wants, because the source reset type
    already contains `rck`.  *That ambient is forced*: anything larger is
    not below `merge amb_call (fst rstty)`, so a "big enough" ambient is not
    an option here.
  * `stream_rel_compose` -- the scalar `amb_trans`/`Forall2_amb_compose`,
    transposed.  The arguments cross two passes and each relates its own
    pair of type lists.
  * the augmented instantiation, `generate_constraints_mono_sem_aug`, rather
    than the plain `generate_constraints_mono_sem` the scalar call uses.
    This is what lets each argument keep its own slot's ambient instead of
    being weakened to a common one -- which it could not be, since the
    slots' clocks differ.  Its two remaining obligations are
    `CALLS.augment_actuals_fresh` and `CALLS.call_augment_dep_concrete`,
    both of which were prepared for exactly this.

And the four premises it added, each a node-level fact and none new in kind:

  * on the lemma: `wc_global P` (for `wc_exp_Eapp_base_clock`, which is what
    makes the call's base clock the common parent of its arguments') and
    `CALLS.sig_inputs_ok GL P`;
  * in `Section ExpressionContract`: `clk_types_defined` -- every clock of a
    well-clocked expression has a type, the totality fact the argument
    ambients are built from -- and `call_anon_not_env_key`, which is the
    premise `assign_lexp_named_covered` documents as
    `call_arg_fresh_not_env_key` and which `SecLNamingTotality.v` already
    proves at the program level.

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

*Lustre naming pass* (`SecLNamingTotality.v`, new) -- **complete**.
`SecNamingTotality.v` did this for the NLustre pass only, so until now every
Lustre-side theorem was conditioned on a naming hypothesis that had never
been shown to hold of anything.  Now:

  * per node: `generate_local_env_for_lnode_ok`,
    `generate_local_env_for_lnode_covers`, with the bridges the Lustre node
    record needs (`AtomOrGensym_mono`, `lnode_var_not_sec`,
    `lnode_declared_NoDup`, `lnode_gather_linsts_NoDup`);
  * per program: `generate_lnode_scoped_env_ok` and
    `generate_lnode_scoped_env_ok_from_ordered`, the latter taking
    `LOrd.Ordered_nodes` -- which the Lustre entry point already assumes --
    via `lOrdered_nodes_NoDup_names`;
  * the exclusion the call case needs, end to end:
    `anon_stream_not_sec`, `declared_not_anon`, `env_key_not_anon` -- no key
    of a node's environment is one of its anonymous streams -- and then
    `fresh_in_arg_in_anon_in`, `anon_in_exp_in_eqs`,
    `call_arg_fresh_not_env_key`, `nested_call_name_fresh`.  Together: a
    name appearing among the fresh streams of a call's argument is never in
    the environment, so a nested call cannot sit at another input's clock
    position and still have `assign_clk_type` succeed.  **The prefix
    argument that was previously only "verified in pieces" is now
    composed.**
  * and the one new hypothesis, `PS.Subset n_prefixes gensym_prefs`, is
    shown *satisfiable* rather than merely assumed: `singleton_elab_subset`
    for elaborated nodes, `unnested_prefixes_subset` and
    `normalized_prefixes_subset` for what the two passes add.  Without those
    the result would have relocated the vacuity rather than removed it.

*The security monad's ordering, and the checkmark bound* (2026-09-25) --
complete and compiled:

  * `sec_le` with `refl`/`trans`/`succ`, `state_pure_sec_le`, `sec_bind_le`,
    `fresh_ident_sec_le`, `fresh_idents_sec_le`, `assign_lexps_sec_le_of`,
    `assign_lexp_type_sec_le`, `assign_lexps_sec_le`,
    `assign_lexp_Eapp_stages_le` (`SecLusUnnestingBase.v`);
  * the equation generator's monotonicity:
    `state_pure_generate_lvars_constraints`, then `sec_le` for
    `generate_lvars_constraints`, `generate_lgen_constraint`,
    `generate_lcall_constraint`, `generate_ldef_constraint`,
    `generate_lone_constraint`, `generate_lsplit_constraints`,
    `generate_leqn_constraint`, `generate_leqns_constraints`
    (`SecLusUnnestingEquations.v`);
  * the discharge steps and their hint database, `sec_le_of_lexp`,
    `sec_le_of_lexps`, `sec_le_of_ljoin_list`, `sec_le_of_single`
    (`SecLusUnnestingBase.v`, db `sec`);
  * the three scoping statements, factored:
    `source_types_scoped_upto`, `source_lexps_scoped_upto`,
    `source_lexps_carried_scoped_upto` (`SecLusUnnestingBase.v`), each
    bounded by `stF`, quoted by all five sections.

### Assumed, not yet discharged

Section hypotheses on `GL` in `SecLusUnnestingEquations.v`: `env_inj`,
`sig_good`, `sig_nodup`, `sig_scoped`, `sig_actuals_fresh`.  A sixth, the
dependency property below, will join them.  All are discharged together at
the program level, which is not written.

The three scoping hypotheses on the source generator --
`source_types_scoped`, `source_lexps_scoped`,
`source_lexps_carried_scoped` -- are now bounded by a checkmark state and so
are *satisfiable*; see the section below.  They are still undischarged, and
the discharge is the node level's job.

### RESOLVED 2026-10-02: the `A eq` pair is gone

The scalar `node_carries`/`unnest_node_step` carried two ambient premises
that the per-equation statement could not discharge, and they were not
merely inconvenient: for a multi-output equation whose outputs sit on
differing clocks they are **jointly unsatisfiable**, since the first forces
`A eq` to contain every lifted variable's clock type and the second forces
it below every left-hand variable's level.  The node theorem was therefore
vacuous on exactly the equations that matter.

The pointwise chain is now complete and the pair is gone:

  * `rhs_carries_streams`, `rhs_carries_other_streams`,
    `rhs_carries_Efby_streams`, `rhs_carries_Earrow_streams`,
    `rhs_carries_exp_streams`, `rhs_carries_list_streams` and its fold
    (`SecLusUnnestingEquations.v`);
  * `eqn_bounds`, `eqn_carries_plain_streams`, `eqn_carries_call_streams`,
    `eqn_carries_one_streams`, `eqn_carries_split_streams`,
    `eqn_carries_streams`, `eqn_carries_covered_streams`,
    `eqn_carries_all_streams` (same file);
  * `eqns_carries_streams`, `node_carries_streams`,
    `node_carries_preserves_streams`, `unnest_node_entailment_streams`,
    `unnest_node_step_streams` (`SecLusUnnestingNodes.v`).

`normalize_signatures_weaken` needed no change: it takes the per-node step
as an abstract premise, so `unnest_node_step_streams` discharges it exactly
where `unnest_node_step` did.

Three things were learned doing it.

*The delays were cheap and the equations were not.*  `wc_exp` puts both
operand lists of an `fby`/`arrow` on the result clocks, so one ambient list
serves the two recursive calls and the join.  An equation's left-hand
variables need not share a clock, which is the whole reason the chain had to
be redone.

*The call needed a forced ambient, twice.*  Inside an expression and at the
top of an equation the transfer runs at `merge [rst_ty] ckty` -- the call's
own ambient -- because `generate_constraints_mono_sem_aug` wants a single one
for the clock, the reset and the outputs while the argument slots' clocks
differ.  Anything larger is not below `merge amb_call (fst rstty)`, so a
"big enough" ambient is not an option.  At the equation level this is also
what makes the per-stream bound *enough* for the outputs: the call's ambient
sits inside every result's ambient (`call_amb_below_result_ambients`), and
`satisfiable` only gets easier as its left-hand side shrinks, so each
output's own bound implies the one the instantiated block needs.  The scalar
proof had to be handed that bound; here it is derived.

*The reset could not be reused.*  `reset_step` asks for a containment
covering every variable the reset's unnesting lifts, which is precisely the
premise the pointwise contract exists to avoid, so `reset_step_streams` is a
separate ~200-line lemma resting on `clocks_covered` and
`state_clocks_found` instead.

### DONE 2026-10-02: the bound is derived, not assumed

The premise above is gone as well, and in the end **no new program-level
invariant was needed**: the `sig_outputs_clock_closed` the previous section
predicted turned out to be unnecessary, because the call rule never needed
the *per-output* clock ambient -- only the call's own base ambient, which the
block already gives.

What replaced it, in two halves:

  * *the call rule* -- `generate_constraints_targets`,
    `generate_constraints_target_In`, `all_sources_below_target` and
    `generate_constraints_amb_below_out` (`SecLusUnnestingCalls.v`).  The
    generated block has exactly one constraint per output, and
    `generate_constraints_clk_reaches` / `_rst_reaches` say the clock and
    reset levels reach every constraint; so satisfying the block already puts
    them below each output.  `generate_constraints_targets` is the `map snd`
    half of `generate_constraints_shape` *without* its `NoDup out` premise --
    that premise is there for the `wf_constraints` half, and a source
    equation's variable list comes with no `NoDup` at the equation level.
    `eqn_carries_call_streams` consequently needs **no ambients at all**: its
    `ambs`, `stream_ambients_scoped`, `clocks_covered`, length and bound
    premises are all gone.
  * *the general rule* -- `generate_lvars_constraints_bounds`
    (`SecLusUnnestingEquations.v`).  The source rule emits
    `ambient ckty_i ⊔ t_i ⊑ b_i`; dropping the right operand is the bound.

`eqn_bounds` was then replaced by `eqn_ambients` -- "each ambient is the
ambient of its variable's declared clock" -- which mentions no valuation, so
the transport of the bound to each successive witness disappeared from the
chunked rule and from `eqns_carries_streams`, and the three node-level
statements lost the `forall dlt, listSatisfiable dlt ce -> ...` wrapper.

Finally `canonical_ambients` (`SecLusUnnestingNodes.v`, after
`End NodeEquations`) discharges `eqn_ambients` and `As_scoped` by
construction.  **What is left of the ambient story is one premise about clock
environments**, `canonical_ambients_cover`'s hypothesis:

    (forall x ck, In (x, ck) vars -> find_clock cenv x = OK ck)

the agreement between the target node's clock environment and the source
node's declared variables.  It is true -- `lnode_clock_env (unnest_node ...)`
keeps every source variable with its clock and only adds the fresh ones -- and
it is proved where `cenv` is chosen, which is the program level.

#### Superseded: the old reading of the bound

The paragraph below is kept because the shape of the mistake is worth
recognising: I assumed the call rule needed its outputs to dominate their own
*instantiated* clock ambients, and went looking for a signature invariant
strong enough to give that.  The call rule needs only the base ambient, so no
such invariant exists in the development -- and did not need to.

    "each defined variable is above its own stream's ambient".  For every rule
but the call it is the equation's own generated constraint, read off
`generate_lvars_constraints`, which emits exactly
`merge (merge [rst_ty] ckty_i) (fst t_i) ⊑ b_i`.

For a call equation it is *not* the call's own constraint: the source call
rule passes the **base** clock's type to `generate_constraints`, so the block
gives `merge [rst_ty] bckty ⊑ b_i` and no more, while an output on
`bck on c` needs `typeof c ⊑ b_i` as well.

Where that comes from, and a correction.  My first reading was that
`sig_inputs_clock_closed` -- which `sig_inputs_ok` already supplies --
would do it.  **It does not** *[verified against the definition]*.  That
invariant propagates clock names from a source *already present* in a
constraint:

    In (x, ck) ins -> nm x = Some y -> In y (fst c) ->
      forall x' y', In x' (clock_vars ck) -> nm x' = Some y' -> In y' (fst c)

and an output's own name is the constraint's *target*, not one of its
sources, so the hypothesis never fires for it.

What is needed is a sibling invariant about outputs, say

    sig_outputs_clock_closed sg outs nm :=
      forall c o cko y,
        In c (s_constraints sg) -> snd c = [y] ->
        In (o, cko) outs -> nm o = Some y ->
        forall x' y', In x' (clock_vars cko) -> nm x' = Some y' ->
          In y' (fst c)

"the constraint that targets an output holds the names of that output's own
declared clock".  It is true of generated signatures for the same reason the
non-call case is immediate: inside the callee the output is defined by a
general-rule equation on its declared clock, and that rule emits
`ambient ckty ⊔ t ⊑ o`, whose sources are exactly `rst_ty`, `ckty` and the
defining stream's type.  And the constraint exists: `signature_good` already
says the targets of a signature's constraints are a permutation of
`map (fun ty => [ty]) s_out`, so each output is targeted exactly once.

So the remaining step is: state `sig_outputs_clock_closed`, carry it beside
`sig_inputs_ok` at the program level, and prove from it (plus
`assign_clk_type_instck_incl`, which splits an instantiated clock's type into
the base's plus the formal's clock variables' actuals) that a call equation's
outputs dominate their own clock ambients.  *[untested]*

### DONE 2026-10-02: the ambient story, and both legs' run facts

*The last gap of the ambient story.*  `lnode_clock_env_from_list` collapses
the three layers of `lnode_clock_env` into one `Env.from_list`, after which
the node's own `n_nodup` makes any lookup in its interface unambiguous
(`lnode_clock_env_find`).  `unnest_node_interface` and
`unnest_node_cenv_vars` then give the agreement -- the unnested node's clock
environment finds every *source* variable at its declared clock, since
unnesting keeps the interface and only extends the locals -- and
`unnest_node_canonical_cover` combines it with `wc_equation`'s third
component.  **Nothing about ambients is assumed at the node level any more.**

*Both legs' run facts.*  `state_clocks_found` was a hypothesis on both
sides; it is a fact about the passes.  Both put the fresh state's annotations
into the target node's local variables -- unnesting verbatim, `normfby`
dropping only the cut flag -- so a variable a run created is found at exactly
the clock the run stored (`unnest_node_state_clocks_found`,
`normfby_node_state_clocks`).  And `NoDup (st_ids stf)` is Velus's own
`st_valid_after` invariant, which `fby_equations` preserves and `init_st`
starts in; taking the "after" set empty makes it exactly that
(`fby_run_st_ids_NoDup`).  So `unnest_node_step_streams` lost its
`state_clocks_found` premise and `normfby_node_step`'s run-facts premise lost
two of its three conjuncts.

### Assumed, not yet discharged: the program level, in eight pieces

This is all that is left of Leg U and Leg I, and none of it is
phase-specific.  `unnest_node_step_streams`'s surviving premises, grouped by
what discharges them:

  1. *the naming pass, read at one node* -- `find_node_env` and the
     `get_node_aux` lookups.  `SecLNamingTotality.v` has the per-node pieces
     (`generate_local_env_for_lnode_ok/_binds/_covers`) and the program-level
     existence (`generate_lnode_scoped_env_ok`); what is missing is the
     *split at a node*, an induction over the accumulating fold
     `generate_lnode_scoped_env'`.  Leg A's
     `generate_all_signatures_entails_scoped'` is the template.
  2. *choices, not obligations* -- `cenv = lnode_clock_env (unnest_node ...)`,
     and `base_ty`/`rst_ty` being `env`'s values at the two aux names.  These
     are discharged by *instantiating* the section, not by proof.
  3. *Velus's own* -- `Forall (unnested_equation Q)` from
     `unnest_node_unnested_eq`, and the `wl_equation`/`wc_equation` lists
     from `wl_node`/`wc_node`.
  4. *the scope, and what a run moves* -- the moved-name freshness, the
     locals-and-minted exclusion, and (what is left of the run facts) that a
     created variable has a security name outside the scope and its clock a
     type inside it.  All four are about the *choice of* `scope` against the
     naming pass's domain; `SecLNamingTotality.v`'s
     `generate_local_env_for_lnode_domain` family is the input.
  5. *clock-type totality* -- `clk_types_defined`, and the "clocks occurring
     in the node have types" premise of `unnest_node_canonical_cover`.  One
     fact: `env` is total on the node's declared variables, which the naming
     pass gives, plus `assign_clk_type_total`.
  6. *that generated signatures are good* -- `signature_good`,
     `signature_scoped`, `NoDup (signature_scope ...)`,
     `generate_lnode_sig_instantiations`, and `sig_rooted`.  Templates, all in
     `SecNLusTypingCorrectness.v` (3022 lines) and each about 200 lines there:
     `generate_node_sig_good_from_local_env`,
     `generate_node_sig_scoped_env_scoped`,
     `generate_node_sig_scope_nodup_from_local_env`, and
     `generated_signature_constraints_mention_clock_scoped_env` /
     `..._mention_reset_scoped_env` for `sig_rooted`.
  7. *the raw constraints' shape* -- `wf_constraints ce` for a Lustre node's
     generated constraints.  The Lustre analogue of what the NLustre side
     proves on the way to `signature_good`: the targets are the defined
     variables' names together with the minted ones, each once.
  8. *`sig_inputs_ok GL P`* -- the pairing of the published signature's input
     list with the callee's node inputs, and the clock closure of its
     constraints.  Documented at `SecLusUnnestingCalls.v`'s
     `sig_inputs_ok` as a program-level fact from the start.

Items 6 and 7 are the bulk; 1 and 5 are each a contained induction; 2, 3 and
8 are bookkeeping at the instantiation site.  They need a new file after
`SecLusUnnesting.v`/`SecLusNormFby.v`, since they speak about
`generate_all_lsignatures_scoped_env`, which is built there.  Prose for each
is in `work_docs/Next_remaining.v`.

One caution, learned twice on this leg: state each of them about the run the
generator *actually performs*, not about a description of it.  A premise
quantified over all states, or keyed on a recorded annotation, speaks about
identifiers the pass never created -- and is then unsatisfiable.  See the
`source_types_scoped` and `fby_created_pairs` corrections above.

### RESOLVED 2026-09-25: `source_types_scoped` was unsatisfiable for programs with calls

*Found 2026-09-24 while deriving the Lustre closure lemma; verified against
the definitions, not conjectured.  Repaired 2026-09-25 (Repair 1, the
checkmark bound) and the repair compiles.  The diagnosis is kept in full
below because the shape of the mistake -- over-quantification in a hypothesis
that looks innocuous -- is the kind worth recognising again.*

`Section Preservation` in `SecLusUnnestingEquations.v` declares

    Hypothesis source_types_scoped :
      forall e ts s s',
        assign_lexp_type GL env base_ty rst_ty e s = OK (ts, s') ->
        Forall (fun t => st_scoped scope (fst t)) ts.

For a call, `assign_lexp_type` returns
`map (fun o => (([o] : ST), held)) outs` where
`outs <- fresh_idents (length anns)` *[verified, `SecLTyping.v`]*, and
`fresh_idents` mints `gensym sec s, gensym sec (succ s), …` from the state it
is run at *[verified, `SecLTyping.v`, `SecContext.v`]*.  So
`st_scoped scope (fst t_i)` demands `In (gensym sec s) scope`.

The hypothesis quantifies over **all** states `s`, and `scope : list ident`
is finite.  It therefore demands membership for unboundedly many distinct
names: **unsatisfiable**, as soon as one call expression types at all.  The
same applies to the `constraints_scoped scope (carried ts)` premises, since a
call's carried constraints mention the same minted names.

Consequence: every theorem in that section -- `carries_exp`,
`eqn_carries_all`, `node_carries`, `node_carries_preserves` -- is currently
**vacuous for any program containing a node call**, which is precisely the
case the refinement types exist for.  Nothing has instantiated the section
yet, so this has not bitten; it would have bitten at the program level.

**Repair 1 chosen (2026-09-25), and its foundation is now proved.**  The
framing: name identity only has to be tracked for names generated *in
lockstep up to a checkmark state*, not for all eternity -- and not for every
local or clock name either.  So the window is two-sided and `scope` stays
finite.

The Sec monad had no ordering at all, so that came first
(`SecLusUnnestingBase.v`):

  * `sec_le` with `refl`/`trans`/`succ`, `state_pure_sec_le`, `sec_bind_le`,
    `fresh_ident_sec_le`, `fresh_idents_sec_le`;
  * `assign_lexps_sec_le_of` and `assign_lexp_type_sec_le` -- **typing an
    expression never moves the counter backwards**, by `exp_ind2` over all
    ten constructors.  The only case that advances it is the call, through
    `fresh_idents`; everything else is pure (`find_env`, `single`,
    `ljoin_list`, `option_to_sec`, `generate_constraints`).

With that, a run's minted names lie in `[s, s')`, every sub-run's window sits
inside its parent's, and a finite `scope` containing `minted st0 stF` covers
them all.

**Repair 1 carried out, 2026-09-25.**  Three things, in this order.

*The statements, factored.*  The three hypotheses were written out,
identically, in five separate sections, and carried the same defect in all
five.  They are now definitions in `SecLusUnnestingBase.v` --
`source_types_scoped_upto`, `source_lexps_scoped_upto`,
`source_lexps_carried_scoped_upto` -- each taking the checkmark `stF` and
each demanding `sec_le s' stF` of the run it speaks about, *after* the run
hypothesis so that a use site resolves the run first.  The five sections now
quote a name rather than a body, so they cannot drift again, and each gained
`Variable stF : sec_state` right after `scope`.

*The bound, threaded.*  A single premise `sec_le <source run's final state>
stF` was added, last, to each of the five contracts: `carries_at` and
`carries_list` (`SecLusUnnestingExpr.v`), `rhs_carries` and
`rhs_carries_list` and `eqn_carries` (`SecLusUnnestingEquations.v`), plus the
five equation-level lemma statements that restate `eqn_carries`'s shape and
the four node-level ones (`eqns_carries`, `eqns_carries_amb`, `node_carries`,
`node_carries_preserves`).  Every proof of a contract now has the bound as a
hypothesis; every application of one discharges it.

*The monotonicity that discharges it.*  A sub-run's bound follows from its
parent's only if the generator advances monotonically, so the missing pieces
were filled in:

  * `assign_lexps_sec_le` (`SecLusUnnestingBase.v`) -- the list form with no
    side condition, and a `sec` hint database holding it and its siblings, so
    the ~19 expression-level sites discharge with `eauto with sec`;
  * `assign_lexp_Eapp_stages_le` (`SecLusUnnestingBase.v`) -- the call is the
    only constructor whose run has stages, so its three stage bounds are
    packaged once instead of being re-derived in `carries_Eapp` and in
    `eqn_carries_call`;
  * `state_pure_generate_lvars_constraints`, then
    `generate_lvars_constraints_sec_le`, `generate_lgen_constraint_sec_le`,
    `generate_lcall_constraint_sec_le`, `generate_ldef_constraint_sec_le`,
    `generate_lone_constraint_sec_le`,
    `generate_lsplit_constraints_sec_le`, `generate_leqn_constraint_sec_le`,
    `generate_leqns_constraints_sec_le` (`SecLusUnnestingEquations.v`) -- the
    **equation** generator advances monotonically too.  This family was
    needed for the chunked rule (the head chunk's run must be bounded by the
    tail's) and for the equation list, and it is the same family the node
    level will need to reason about `minted st0 st1`.

*Cost, and one lesson about the discharge tactic.*  A first attempt put
`sec_le_trans` in the hint database and discharged the expression-level sites
with `eauto 8 with sec`.  It worked but opened a goal with an unknown middle
state at every site, and `SecLusUnnestingExpr.v` went from about a minute to
over eighteen.  Replacing it with two *directed* steps -- `sec_le_of_lexp`
and `sec_le_of_lexps`, each of which consumes a run hypothesis and leaves a
bound on an earlier state -- plus `sec_le_of_ljoin_list` and
`sec_le_of_single` for the pure stages, brought it back to 66s.  `eauto 4
with sec` suffices.  *[verified: clean `rm -f src/SIF/*.vo src/SIF/*.glob &&
make -j1` passes, extraction and the OCaml build included, 0 admits.]*

*What this does and does not settle.*  It makes the three hypotheses
satisfiable in principle: a run bounded by `stF` mints only inside
`minted <start> stF`, and `generate_lnode_sig` already builds its scope as
`locals ++ minted st0 st1`, so taking `stF := st1` covers them.  It does
**not** discharge them -- that happens at the node level, and the node-level
`scope` will have to be `locals ++ minted st0 st1` *plus the interface names*,
which the current `simplify` argument does not yet spell out.  Recorded as
the next obligation, not as done.

**The original diagnosis, for the record: over-quantification, not a wrong
idea.**  For the run the
node level actually performs, the minted names *are* a finite set, and
`SecLTyping.v` already names it: `minted st0 st1`, built from `sec_span`.
`generate_lnode_sig` eliminates exactly `locals ++ minted st0 st1` with
`simplify`.  Two repairs, in increasing invasiveness:

1. **Bound the state.**  Give the section a starting state `st0`, quantify
   the hypothesis over runs with `st0 ≤ s`, and let `scope` include
   `minted st0 stfinal`.  The intended fact -- minted names are visible names
   of the comparison, since both sides mint them and `simplify` removes them
   together -- then holds, and `scope` stays finite.
2. **A second moved-set.**  Carry the Sec-minted names the way `moved_by`
   carries the unnesting-minted ones, with the witness free to move them.
   This is the same shape as the existing `agree_off`/`moved_by` treatment
   and would be uniform, but touches every statement in the leg.

Repair 1 looks right: the minted names are not "moved" in the `moved_by`
sense -- both sides of the comparison mint the *same* names, because the
source and target runs start from the same state -- so they belong in
`scope`, not in a moved-set.  What is missing is only the bound that keeps
`scope` finite.

This must be settled before more is built on the section, and it should be
checked whether the analogous hypotheses in Leg A have the same defect.

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
    variables, so `merge a_j inp1_j ⊆ call_amb ∪ inp1''_j`
    *[verified 2026-09-25: `call_amb_covers_augmented`, from
    `assign_clk_type_instck_incl`]*;
  * `amb_pair` holds, since `bck` is a prefix of every output clock --
    `assign_clk_type_prefix_incl`  *[verified 2026-09-25:
    `instck_clock_prefix` says instantiation only ever extends the base
    clock, and `assign_clk_type_instck_base_incl` turns that into
    `incl bkty ckty`, which is what makes the uniform ambient small enough
    for every result]*;
  * the augmentation changes nothing, since by the dependency property any
    constraint mentioning input `j` already mentions `j`'s clock variables,
    so the larger actuals add no member to any source, and
    `listSatisfiable_same_sources` carries satisfaction across
    *[verified 2026-09-25: `subst_constraints_inp_map_augment` proves this
    given `Hdep`; `call_augment_dep` proves `Hdep` from the callee-side
    invariant; and `call_augment_dep_at_call` reads its positional
    hypotheses off what the call site has -- `wc_exp`'s `WellInstantiated`
    chain, the callee's `wc_env (idck n_in)`, and the argument types the
    generator produced]*.

**All three obligations of the design in force are discharged, and now on the
concrete augmentation** *[verified, compiles]*.

*The augmentation, built.*  `sub_names`, `clock_actuals`, `augment_actuals`
(`SecLusUnnestingCalls.v`), with `clock_actuals_inv` / `clock_actuals_intro`,
`augment_actuals_cons` / `_nth` / `_nth_inv` / `_grows`:

    clock_actuals sub ck   = the security names of the streams that ck's
                             variables were instantiated to
    augment_actuals sub ins argts
                           = per slot, merge (fst argts_i)
                                            (clock_actuals sub ck_i)

This is the design's "joined with the actuals of j's clock variables" made
precise, and it is *minimal*: by `assign_clk_type_instck` the only part of an
argument's own ambient the uniform ambient does not already carry is exactly
those names.  `augment_actuals_grows` also closes the growth premise of
`subst_constraints_inp_map_augment`.

*The two program-level facts, named.*  `sig_inputs_ok P` pairs them, because
they are established together when `generate_lnode_sig` runs: a callee's
signature input list lines up with its node's inputs under the callee's own
naming, and its constraints are closed under those inputs' declared clocks.
It is parameterised by the Lustre program, since the pairing of `GL` with `P`
is fixed at the program level, and it joins `sig_good`, `sig_scoped` and
`sig_actuals_fresh` as a hypothesis discharged there.

*The whole thing.*  `call_augment_dep_concrete` is the premise
`subst_constraints_inp_map_augment` asks for, on the concrete augmentation,
with nothing abstract left but `sig_inputs_ok`.
`call_amb_covers_augmented_concrete` is clause 3 on the same augmentation.

**Correction, 2026-09-26: the scalar `carries_Eapp` is not the open case --
it was already proved.**  `CALLS.carries_Eapp` applies
`generate_constraints_mono_sem` directly with the plain actuals, and its
per-argument premise is met because the *scalar* contract is handed an ambient
by hypothesis: `carries_at` requires
`incl (merge [rst_ty] ckty) amb` for **every** variable the emitted equations
define, lifted arguments included.  So one ambient large enough for every
argument is simply given there, and no augmentation is needed.

The open call case is the **streams** one, `carries_Eapp_streams`, which does
not exist yet.  That is where the gap is real: the pointwise contract gives
each source stream *its own* ambient (`ambs`, pinned by
`clocks_covered (clockof e) ambs`), so there is no single ambient to be handed
the argument obligations, and the uniform one has to be constructed and
reconciled -- which is what all the machinery above is for.  Every other
constructor has its streams lemma (`carries_Econst_streams` through
`carries_Earrow_streams`, including both `Emerge`/`Eite` branches); `Eapp` is
the only one missing.

**The reconciliation, proved 2026-09-26** *[verified, compiles]*.
`wc_Eapp_out_instck` and `call_amb_below_result_ambients`
(`SecLusUnnestingStreams.v`): every output clock instantiates the *same* base
clock, so `bck`'s type is inside each output clock's type, and therefore the
call's uniform ambient `merge [rst_ty] bckty` is inside every result's
ambient.  That is the `amb_pair` obligation in the form the streams call case
needs, and it is what lets `generate_constraints_mono_sem` be applied with
`amb := call_amb` inside a contract whose ambients are per-stream.

**The freshness premises, and the argument ambients** -- **done 2026-09-26**
*[verified, compiles]*.  `augment_actuals_fresh`: the two freshness premises
of `subst_constraints_inp_map_augment` come free for the augmented actuals,
because every member of the augmentation is a member of *some* actual -- its
own, or the one at the slot of the clock variable it came from -- so freshness
transfers from the plain actuals, which `call_subst_fresh` already gives.

`call_arg_ambient sub bckty ck := merge (merge [rst_ty] bckty)
(clock_actuals sub ck)` with `call_arg_ambient_covers`: the ambient the streams
call case hands each argument, and the proof that it covers
`merge [rst_ty] (the instantiated clock's type)`.  It is the *same* set the
augmentation uses, which is not a coincidence -- both are "the call's own
ambient plus this slot's clock actuals".

**What is left, and both pieces are session-sized.**

*(A0) The augmented run can be built* -- **done 2026-09-26**
*[verified, compiles]*.  Nothing previously produced the augmented
instantiation; `subst_constraints_inp_map_augment` and
`generate_constraints_mono_sem` both take their two runs as given.
`generate_constraints_total_inp` produces it: a successful
`generate_constraints` with one set of actuals gives a successful one with any
other of the same length.

The reason it holds is that `findST` looks a constraint up by its *target*, so
every stage's success depends on the targets alone, and every stage preserves
them.  Hence `findST_targets_some`/`_none`, then
`subst_constraints_inp_map_targets`/`_total`,
`subst_ident_in_constraints_targets`/`_total`,
`subst_constraints_out_map_total`, and `mmap_findST_total` for the final
lookup.  `augment_actuals_fresh` supplies the freshness premises, so
`subst_constraints_inp_map_augment` now has **every** premise met.

*(A1) Propagating set-equality of sources through stages 2-4* -- **done
2026-09-26** *[verified, compiles]*.  `generate_constraints_same_inp`: given
that the input map's two results agree as sets, the final constraint lists do,
which is what `listSatisfiable_same_sources` needs to carry satisfaction from
the plain instantiation to the augmented one.

It rests on one fact -- `subst_ident_in_type` reads its argument only through
membership -- so `subst_ident_in_type_notIn` (new, covering what the existing
`subst_ident_in_type_In` does not) plus `subst_ident_in_type_same` give it at
the type level.  `cs_same_src` is the relation each stage preserves (targets
equal, sources equal as sets), `cs_same_src_weaken` drops it to what the
satisfaction lemma consumes, and the stages are
`subst_ident_in_constraints_same` (clock and reset),
`subst_constraints_out_map_same` via `subst_ident_constraints_same` (outputs),
and `mmap_findST_same` via `findST_same` (the final lookup).

**So the satisfaction transfer is now complete end to end**: build the
augmented run (`generate_constraints_total_inp`), show its sources agree with
the plain one's (`subst_constraints_inp_map_augment` with `Hdep` from
`call_augment_dep_concrete`, propagated by
`generate_constraints_same_inp`), carry satisfaction across
(`listSatisfiable_same_sources`), then transport to the target with
`generate_constraints_mono_sem` at `amb := call_amb`, whose per-slot premises
are `call_amb_covers_augmented_concrete` for the arguments and
`call_amb_below_result_ambients` for the results.

*(A1-old) The former next atom, for the record.*
`subst_constraints_inp_map_augment` concludes exactly the relation
`listSatisfiable_same_sources` consumes -- pointwise set-equality of both
components -- but only for the *input-map* stage.  The satisfaction transfer
needs it at the end of `generate_constraints`, so it has to survive the clock,
reset and output substitutions and the final lookup.  It does: substituting the
same name by the same type on set-equal sources yields set-equal sources,
because `subst_ident_in_type` depends on its argument only through membership
(`subst_ident_in_type_In`).  For the clock and reset stages
`subst_ident_in_constraints_members` gives the description needed directly;
for `subst_constraints_out_map` **there is no members lemma yet**, and writing
one is the next task.  *[untested]*

*(A) `carries_Eapp_streams`.*  Its ingredients are all present now --
`carries_list_streams_intro` for the arguments, `call_arg_ambient` and
`call_arg_ambient_covers` for their ambients, the augmentation with its three
obligations and both freshness premises,
`call_amb_below_result_ambients` for the results, `lifted_defs_streams` and
`state_clocks_found` for the variables unnesting binds.  What remains is the
assembly, and its siblings run 300-1500 lines each; this one has arguments, a
reset, lifted results and the signature chain at once *[untested]*.

*(B) Discharging `sig_inputs_ok`, which needs the call rule of the
constraint-level closure.*  Analysis, 2026-09-26, so the next attempt starts
from it rather than rediscovering it:

`sig_inputs_clock_closed` **is** `constraint_clock_closed` read at an input:
for `b = env v` in a source with `In (v, ckv) vars`, `incl ckvty (fst c)`, and
for an input `ckvty` is `[base_ty]` plus the names of its clock's variables.
So (B) reduces to `constraints_clock_closed` of the *published* constraints,
which is `generate_leqns_constraints_clock_closed` plus
`simplify_clock_closed` -- both proved -- and the one missing per-equation
case, the call rule.

For that call rule, of the four types `generate_constraints` substitutes,
**three are self-closed and only the actuals are not** *[verified against the
generator]*:

  * the clock slot is `bckty`, self-closed by
    `assign_clk_type_clock_closed`;
  * the reset slot is `fst rstty = merge [rst_ty] (merge (fst a1) rck)`, and
    `rck` is the *reset expression's own clock type* -- the generator merges it
    in deliberately -- so the closure obligation on `fst a1` is met from
    inside the same set.  `rst_ty` itself is covered by `rst_not_var`;
  * the output slot's names appear only as targets.
  * the **actuals** are not: closure of an argument's type needs that
    argument's clock type, and whether *that* is in the instantiated source is
    exactly the content.  It is, from two facts about the callee: its own
    `sig_inputs_clock_closed` (so the argument's clock variables' formals are
    in the callee source, hence their actuals are substituted in) -- this is
    the induction over the call graph -- and that every callee source mentions
    `s_clk`, which puts `bckty` there.

So (B) needs the "every source mentions `s_clk` and `s_reset`" predicate after
all -- as a definition in an editable file entering on `GL`, since
`SIFSignature.v` is read-only -- plus a members description for each of the
four substitution stages (stages 1-3 have one; `subst_constraints_out_map`
does not) and a `findST` step for the final lookup, which
`findST_clock_closed` already models.

**Rootedness: done end to end, 2026-09-26** *[verified, compiles]*.  The
predicate is `constraint_rooted` / `constraints_rooted` (the source mentions
the base name and the reset), and it now holds of everything the generator
produces:

  * the non-call rules -- `generate_lvars_constraints_rooted`,
    `generate_ldef_constraint_rooted`, `generate_lgen_constraint_rooted`,
    `generate_leqn_constraint_rooted_plain`,
    `generate_leqns_constraints_rooted` with its call-free corollary, and
    `assign_clk_type_base` as the reason (every clock type contains the base
    name);
  * the **call rule** -- `generate_constraints_rooted`.  The base name reaches
    every final source through the *clock* slot: the callee's clock formal is
    in every callee source, and the base name is in the type substituted for
    it.  The reset level arrives the same way through the reset slot.
    Everything else is preservation.  The side conditions are exactly
    `call_subst_fresh` and `NoDup (s_in ++ s_clk :: s_reset :: s_out)` -- both
    already hypotheses of the leg;
  * through `simplify` -- `subAll_rooted`, `simplify_rooted`, on the same
    `keep` discipline as closure but for a simpler reason: the base name and
    the reset are kept, and elimination only removes the eliminated name and
    the constraint's own target.

The machinery is `all_sources_have` plus one keep/intro pair per stage:
`subst_constraints_inp_map_all_keeps`,
`subst_ident_in_constraints_all_keeps`/`_all_intro`,
`subst_ident_constraints_all_keeps`,
`subst_constraints_out_map_all_keeps`, `mmap_findST_all_keeps`.

So of (B) what remains is the **closure** call rule.  Its cases, worked out
2026-09-26 by tracing where a name in a final source can come from -- the
callee's own names are all substituted away, since `signature_scoped` confines
them to `signature_scope` and every part of that is a substitution slot:

  * from `clk` (`= bckty`): `assign_clk_type_clock_closed` gives
    `incl ckvty bckty`, and `bckty` reaches the final source by the rootedness
    argument (`s_clk` is in every callee source) and survives the later stages
    by `call_subst_fresh`;
  * from `rst` (`= fst rstty`): self-closed, because the generator merges the
    reset expression's *own* clock type `rck` into `rstty`, and `rst_ty` is
    covered by `rst_not_var`.  Same survival;
  * from an actual argument type `inp_i`: closed relative to that argument's
    clock type `ck_i`, and `ck_i` is inside `merge bckty (clock_actuals ...)`,
    whose second part is covered by the callee's invariant plus the named-stream
    lemma;
  * **from an actual output name** -- the case I had missed.  The out-map
    substitutes output formals into sources, so a callee constraint whose source
    mentions another output formal contributes one of the *caller's defined
    variables*, and that variable's clock type then has to be accounted for.

**Consequence, and the fix, 2026-09-26** *[verified, compiles]*.  The invariant
has to be stated over the whole interface, not just the inputs.  That is
sound because `simplify` eliminates `locals ++ minted` and therefore **keeps**
the outputs, and because `wc_node` gives `wc_env (idck (n_in ++ n_out))`, so an
output's declared clock mentions only inputs and outputs -- exactly the names
the `keep` set retains.  No new definition was needed:
`sig_inputs_clock_closed` instantiated at `idck (n_in ++ n_out)` *is* the
interface version, and `sig_inputs_clock_closed_incl` restricts it back to the
inputs for the augmentation argument, which needs only those.  `sig_inputs_ok`
now carries the stronger form.

Had this been noticed only at the node level it would have invalidated the
`keep` set as well; the two fit together because outputs are kept.

**Correction, 2026-09-26: closure has to be stated modulo a cover.**  A first
pass at the per-slot closure lemmas gave them the premise "each actual type is
closed", i.e. `st_clock_closed ... (fst argts_i)`.  That premise is met by
nothing: an actual's type is closed only *relative to* the clock the argument
runs on, so demanding `incl ckvty (fst argts_i)` would force the argument's
clock type into the argument's own type -- and since every clock type contains
`base_ty`, it would force `base_ty` into it.  **Exactly the same shape of
mistake as the original `source_types_scoped`**: a premise that reads
plausibly and is satisfiable by nothing.

The repair is the same in spirit as the checkmark bound -- weaken the
statement to what is actually true and discharge the difference separately.
`constraint_closed_mod ns cov` asks for `incl ckvty (merge cov (fst c))`, with
`cov` a fixed set holding every clock type the call involves:

    cov := bckty  joined with  the clock actuals of every argument and output
                               formal's declared clock

Every slot is then closed modulo `cov` *[verified]*: the actuals because
`ck_i` is inside `merge bckty (clock_actuals ...)`, the clock slot because
`incl ckvty bckty`, the reset slot because it is self-closed, the output names
because an output's clock type is inside `cov` too, and the callee's own names
vacuously by `sig_scope_fresh_for_env`.  Closure modulo `cov` *is* preserved by
substitution -- `subst_ident_in_constraints_closed_mod` and
`subst_constraints_inp_map_closed_mod` -- and at the end `cov` is shown to be
inside the source anyway, which upgrades it to closure proper.

**Discharging `cov` splits in two, and only one half is uniform**
*[analysed 2026-09-26]*.

*The uniform half -- done* *[verified, compiles]*.  Every member of the clock
actual reaches **every** final source, for the same reason the base name does,
and likewise for the reset.  `generate_constraints_clk_reaches` and
`generate_constraints_rst_reaches` are the rootedness proof generalised from
`base_ty`/`rst_ty` to any member of the slot, and
`generate_constraints_rooted` is now the corollary at those two names.  So the
`bckty` and `fst rstty` parts of the cover need no reference to which formals a
constraint mentions.

*The per-constraint half -- the remaining design decision.*  The **actuals**
cannot be handled uniformly: an actual enters only those sources whose formal
appears in the corresponding callee source.  So `cov` has to be **per callee
constraint**:

    cov_c := bckty ⊔ fst rstty
             ⊔ the actuals and clock actuals of the formals occurring in fst c

and then `cov_c ⊆ fst c_final` holds for every `c`, because each part's formal
is in `fst c` by construction and the callee invariant supplies the clock
formals.  The consequence is that the four per-slot lemmas want a `Forall2`
over covers rather than one fixed `cov` -- the stages preserve element order, so
the covers ride along unchanged.  The one wrinkle is the final `mmap`, which
re-pairs by target and so permutes the correspondence; `signature_good`'s
`Permutation (map snd s_constraints) (map (fun t => [t]) s_out)` is what relates
them.

Recorded rather than started, so the reformulation is done once: the choice is
between indexing the per-slot lemmas by a cover list, or carrying the cover
inside the relation as a function of the constraint.  The first is closer to
what is already written.

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

**Expression level: done, 2026-09-25** *[verified, compiles]*.
`assign_lexp_type_clock_closed` in `SecLusUnnestingBase.v`, stated through
two single-name pieces so that every case of the induction makes only one of
two moves -- widen the target, or account for a sampling variable:

    name_clock_closed env base_ty vars ckty target b :=
      forall v ckv ckvty,
        Env.find v env = Some b -> In (v, ckv) vars ->
        assign_clk_type env base_ty ckv = Some ckvty ->
        incl ckvty (merge ckty target)

    lst_clock_closed env base_ty vars nomint t ck :=
      forall ckty b,
        assign_clk_type env base_ty ck = Some ckty ->
        ~ In b nomint -> In b (fst t) ->
        name_clock_closed env base_ty vars ckty (fst t) b

and the theorem, by `exp_ind2` over all ten constructors:

    wc_exp P vars e ->
    incl (minted s s') ns ->
    assign_lexp_type G env base_ty rst_ty e s = OK (ts, s') ->
    Forall2 (lst_clock_closed env base_ty vars ns) ts (clockof e)

Three things are worth recording.

*The clocking rules do the work, in two directions.*  `Ewhen` deepens the
clock by one `Con` and adds the sampling variable's own security name to the
type, which is exactly what pays for the deeper clock.  `Emerge` is the
reverse: the branches run on `Con ck x true/false` while the result is on
`ck`, and again the sampling name sits in the merged type, so the branches'
extra `Con` is covered.  These are `lst_clock_closed_when` and
`lst_clock_closed_merge_el`.

*The call case needs a name to be known not to be minted.*  A call's type is
its freshly minted result name, which belongs to no program variable, so
nothing about declared clocks can be said about it.  The statement therefore
carries `~ In b nomint`, and the case is discharged by showing the result
names lie in the run's window.  That needed the window algebra --
`sec_span_spec`, `minted_spec`, `minted_gensym`, `minted_window`,
`fresh_ident_minted`, `fresh_idents_minted` (`SecLusUnnestingBase.v`), where
`minted_spec` is the load-bearing one: membership in `minted s s'` is
*exactly* a `sec` gensym at an index in `[s, s')`, which is what lets a name
be shown **not** to be minted.  At the use site the premise is free:
`generate_lnode_sig` runs `simplify` over `minted st0 st1`, so no minted name
survives into a signature.

*The exclusion set is a parameter, not the run's own window.*  A first
version wrote `minted s s'` into the conclusion; every case then had to
re-state which window it was talking about, and the proofs broke on which of
two equal state names `subst` happened to keep.  Taking `ns` with
`incl (minted s s') ns` makes the conclusion stable under any sub-run, and
`minted_incl_sub` is then the only plumbing.

**Constraint level: done for every rule but the call, 2026-09-25**
*[verified, compiles]*.  A constraint's source is
`merge (merge [rst_ty] ckty) (fst t)`, so the property to carry up is
self-contained -- no separate clock type to quantify over:

    constraint_clock_closed env base_ty vars nomint c :=
      forall v b ckv ckvty,
        Env.find v env = Some b -> ~ In b nomint -> In b (fst c) ->
        In (v, ckv) vars -> assign_clk_type env base_ty ckv = Some ckvty ->
        incl ckvty (fst c)

Three parts of that source, three arguments.  The reset name is not a
declared variable's -- a new hypothesis `rst_not_var`, the exact sibling of
the `base_not_var` the CoreExpr closure lemmas already take.  The clock type
is handled by `assign_clk_type_clock_closed` (already proved).  The
right-hand side's type is handled by `assign_lexp_type_clock_closed`.  That
is `constraint_clock_closed_head`, and
`constraints_clock_closed_lconstrain` wraps it for the shape the generators
emit.

Proved on top of it, all in `SecLusUnnestingBase.v`:

  * `generate_lvars_constraints_clock_closed` -- the variable rule, one
    ordering per defined name.  Its hypothesis is the one the equation level
    can actually supply: each right-hand side type is closed at the clock its
    defined variable is *declared* on, which is what `wc_equation` pins;
  * `generate_ldef_constraint_clock_closed` -- one variable, one expression;
  * `generate_lgen_constraint_clock_closed` -- a list against a list.  The
    two `Forall2`s (variables against `clocksof es` from `wc_equation`, types
    against the same list from the closure theorem) are composed by
    `Forall2_trans_clock`, with `NoDupMembers vars` supplying the clock's
    uniqueness;
  * `generate_leqn_constraint_clock_closed_plain` -- a whole equation whose
    right-hand side holds no call.

Supporting: `eqn_clock_type_inv`, `generate_lvars_constraints_advances`
(the variable rule mints nothing -- proved here rather than reused from the
equation file, which comes later), `constraints_clock_closed_cmerge` and
`_app`.

The carried constraints are isolated as one hypothesis,
`lexp_carried_closed`, with `assign_lexps_carried_closed_of` for the list
form.  That is deliberate: carried constraints come *only* from nested calls,
so this is exactly the hypothesis the callee-signature invariant will
discharge, and nothing above it depends on that step.

**Equation list: done, 2026-09-25** *[verified, compiles]*.
`generate_leqns_constraints_clock_closed` in
`SecLusUnnestingEquations.v`: each equation's run is a sub-run of the list's,
so the window it mints in sits inside the list's and the per-equation
hypothesis applies unchanged -- `generate_leqn_constraint_sec_le` and
`generate_leqns_constraints_sec_le` (from the monotonicity family) are what
split the window.  The corollary
`generate_leqns_constraints_clock_closed_plain` discharges the per-equation
hypothesis for a node whose equations all have a call-free right-hand side,
reading the two premises the equation rule needs straight off
`wc_equation`.

**Transport through `simplify`: done, 2026-09-25** *[verified, compiles]*.
`generate_lnode_sig` publishes `simplify cs (locals ++ minted st0 st1)`, not
`cs`, so the property has to survive elimination.  `subAll_clock_closed`,
`subAll_targets`, `findST_clock_closed`, `simplify_clock_closed` and
`subST_cases` (`SecLusUnnestingBase.v`).

The point worth recording is **why it survives, and for which variables**.
Elimination *removes* names from a source -- three of them per step: the
eliminated name from the source, the eliminated name from the substituted
type, and the constraint's own target -- so a clock type mentioning any of
those would not survive.  That never happens for an **input**: `wc_node`
requires `wc_env (idck n_in)`, so an input's declared clock mentions only
inputs, and inputs are exactly what `simplify` keeps.  The lemmas take that
as a `keep` set: the names a clock type of interest may mention, and which no
elimination touches.  Had the property been stated for all declared
variables, it would be **false** after `simplify` -- a local's clock type can
mention another local, and that name is eliminated.  This is the kind of
thing that would have been found only at the node level.

What `findST` substitutes in is itself the source of a constraint of the
list, hence itself closed, which is the other half of the step.

**The call rule: its three ingredients, two of them now proved.**

*(i) What an instantiated clock's type can mention* -- **done 2026-09-25**
*[verified, compiles]*.  `clock_vars`, `assign_clk_type_instck`,
`assign_clk_type_instck_incl`, `clock_vars_wc`, and
`wc_exp_Eapp_base_clock` (`SecLusUnnestingBase.v`).  A formal's declared
clock is instantiated as `instck bck sub ck`, and its security type mentions
only the base clock's type and the security names of the substituted streams
-- nothing else.  `wc_exp_Eapp_base_clock` settles that the generator's base
clock, `find_base_clock (clocksof es)`, is clocking's `bck`; this is where
`wc_global` is needed, because it is the *callee's* `wc_env (idck n_in)` that
makes `bck` the common parent.  The argument is Velus's, lifted out of
`TrClocking` so both consumers use it as a lemma.

*(ii) A named argument stream carries its own name* -- **done 2026-09-25**
*[verified, compiles]*.  `assign_lexp_named_covered`, with
`named_covered_vacuous` and `unnamed_no_key`.  Only two constructors can
carry a stream name: `wc_exp` forces `None` on the other eight.  `Evar`'s
name is pinned to the variable and its type is exactly that variable's
security name.  `Eapp`'s names are *anonymous* and therefore not keys of
`env` at all -- which cannot be proved where `env` is abstract, so it is a
premise, discharged at the program level by `call_arg_fresh_not_env_key`.
The statement is about top-level streams only, so no recursion is needed and
the premise is needed only for a call at the top of the expression.

*(iii) The callee-side invariant, and the [Hdep] discharge* -- **done
2026-09-25** *[verified, compiles]*.  `sig_inputs_clock_closed` and
`call_augment_dep` (`SecLusUnnestingCalls.v`), with `In_combine_nth_error`,
`nth_error_In_combine`, `nth_error_lt`, `nth_error_lt_inv`
(`SecLusUnnestingBase.v`) for the positional matching.

The invariant is the dependency property itself, read at the callee and
restricted to its inputs:

    sig_inputs_clock_closed sg ins nm :=
      forall c, In c (s_constraints sg) ->
      forall x ck y, In (x, ck) ins -> nm x = Some y -> In y (fst c) ->
      forall x' y', In x' (clock_vars ck) -> nm x' = Some y' -> In y' (fst c)

so the property is **inductive over the call graph**, and the `keep` set of
the `simplify` transport -- the base name plus the inputs' security names --
is exactly what carries it into the published signature.  Each node has its
own naming, so the invariant is stated over the callee's `ins` and its own
`nm`, never the caller's `env`.

`call_augment_dep` discharges the one premise
`subst_constraints_inp_map_augment` had left open, matching the call's four
lists -- the callee's inputs with clocks, its formal names, the actuals'
nclocks, the actuals' types -- by position.  Its two substantive inputs are
(i) and (ii) above: the clock names an augmentation may add are exactly
`env (sub x')` for `x'` a variable of the formal's clock, and the actual at
`x'`'s own slot carries that name because its stream is named `sub x'`.

**RESOLVED 2026-09-25, and it was a misreading on my part, not a gap in the
design.**  The design in force (see "The open step: the call case" below)
already specifies the augmentation as

    inp1''_j := inp1_j joined with *the actuals of j's clock variables*

-- clock names only.  The base and reset levels are **not** the
augmentation's job: they are the uniform ambient's,
`call_amb = [rst_ty] ⊔ assign_clk_type bck`.  So the obstruction I had
written down does not arise, and `call_augment_dep`'s hypothesis on the
augmentation's shape is exactly right as stated.

`call_amb_covers_augmented` (`SecLusUnnestingCalls.v`) discharges the
inclusion this leaves -- `merge a_j inp1_j ⊆ call_amb ∪ inp1''_j` -- straight
from `assign_clk_type_instck_incl`.  That was the first of the three
obligations the design lists, and it was the one marked `[untested]`.

Also settled: the fact that every generated constraint source mentions
`s_clk` and `s_reset` is **not needed** for this argument.  It is true and
could be packed into a signature predicate, but nothing here wants it, so it
is not being built.

**The former open question, kept because the reasoning is worth having.**  `call_augment_dep` takes the augmentation's *shape* as a hypothesis:
what it adds must be clock names of its own formal's clock.  Instantiating
that with a concrete augmentation runs into this.  An argument's ambient is
`merge [rst_ty] ck_i`, so the natural augmentation is
`merge w_i (merge [rst_ty] ck_i)`; but `assign_clk_type_instck` says `ck_i`'s
members are either such clock names **or members of the base clock type
`bckty`** -- and `bckty` is *not* covered by any actual.  An argument can be a
constant, whose type is `[]`, so nothing forces `base_ty` into an actual.

The base and reset parts *are* present in the final instantiated source, but
only after the `clk` and `reset` substitutions of `generate_constraints`
replace `s_clk sg` and `s_reset sg`.  At the stage
`subst_constraints_inp_map_augment` speaks about -- after the input map alone
-- they are still the *formal* names, so the augmented and plain sources are
not yet equal as sets; they become equal one stage later.

So the augmentation argument has to be applied **after** the clk and reset
substitutions, not to the input map in isolation -- or the statement has to
be about the whole of `generate_constraints`.  Which of the two is right is a
decision about `generate_constraints_mono_sem`'s clause 3, whose repair is
not written.  It would also need a new fact about generated signatures --
that every constraint source mentions `s_clk` and `s_reset` -- which is
plausible by construction but is **not** implied by `signature_good`,
`signature_scoped` or `wf_constraints` *[verified: none of the three
mentions sources]*.

Recorded rather than guessed: two designs for this call case have already
died on contact with `subst_constraints_inp_map`, and this is the same kind
of decision.  The next step is to settle it against
`generate_constraints_mono_sem`, not to pick an augmentation and hope.

**Two new hypotheses, both discharge-able and neither restricting programs**:
`rst_not_var` (the reset name is not a declared variable's -- true because it
is an aux name and `env` is injective) and the `cenv`/`vars` agreement
`find_clock cenv y = OK ck -> In (y, ck) vars` (true because `cenv` is
`lnode_clock_env n` and `vars` is `idck` of the same three lists), plus
`wc_env`-style `In (y, ck) vars -> wc_clock vars ck`, which is a field of
`wc_node`.

### Next steps, in order

0. ~~Repair the three scoping hypotheses, which were unsatisfiable for any
   program with a call.~~ **Done 2026-09-25** -- Repair 1, the checkmark
   bound; see the section above.  What it leaves open is the *discharge*,
   which belongs to step 6.
0b. ~~The dependency property at the **expression** level.~~ **Done
   2026-09-25** -- `assign_lexp_type_clock_closed`
   (`SecLusUnnestingBase.v`), the Lustre mirror of
   `assign_cexp_type_clock_closed`: the type of an expression, taken with
   the type of the clock it runs on, already contains the clock type of
   every declared variable it mentions.
0c. ~~The same at the **constraint** level, for every rule but the call.~~
   **Done 2026-09-25** -- the variable, definition and general rules, and a
   whole call-free equation.  What is left is the call rule, which needs the
   property as an invariant on `GL`.  Details of both in the section below.
1. ~~`subst_constraints_inp_map` with augmented actuals leaves every
   constraint source unchanged as a set, given the dependency property.~~
   **Done** -- `subst_constraints_inp_map_augment`.
2. ~~`env` domain~~ and ~~the exclusion~~ **both done**
   (`generate_local_env_for_lnode_domain`, `call_arg_fresh_not_env_key`).
   What remains before the call case is the dependency property for
   `generate_leqns_constraints`, mirroring the CoreExpr closure lemmas
   already in `SecLusUnnestingBase.v`; and threading these facts into Leg U,
   where `env` is abstract, as hypotheses discharged at the program level.

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
   `signatures_preserved`.  **Substantially done, 2026-09-26**
   *[verified, compiles]*:

     * `lnode_sig_inv` -- the projection lemma for `generate_lnode_sig`,
       reproved in `SecLusUnnestingNodes.v` because Leg A's `l_node_sig_inv`
       sits later in the build order;
     * `unnest_node_sig_interface` -- **five of a signature's six fields are
       equal on the nose**, not merely related, because `unnest_node` copies
       `n_name`, `n_in` and `n_out` and only extends `n_vars`.  Only
       `s_constraints` can differ, which is exactly what `preserves_on`
       speaks about.  The plan had this recorded as verified by inspection;
       it is now proved;
     * `preserves_on_simplify` (`SecLusUnnestingBase.v`) -- the entailment
       survives elimination **on both sides**, although the two sides
       eliminate different sets: the target has more locals and its run
       minted more names.  Three moves -- back through the source's
       elimination by `simplifyRel_complete`, across by the equation-level
       theorem, forward through the target's by `simplify_is_correct`.  Both
       directions were already in `SecTypes.v`; the only side condition is
       that what the source eliminates lies outside the scope, which is what
       `generate_lnode_sig` arranges;
     * `unnest_node_signatures_preserved` -- the phase's statement for one
       node: same interface, and the published constraints entailed on it.

   This runs on the **scalar** contract, whose `node_carries_preserves` was
   already proved, so it did not wait on `carries_Eapp_streams`.  What the
   streams contract is for is removing `node_carries`'s two ambient premises,
   which appear here as the equation-level entailment hypothesis.

   Also done: `locals_not_interface` -- half of the elimination-disjointness
   side condition, and the half provable at this level.  The locals' security
   names lie outside the interface because `env` is injective and a local is
   neither an input nor an output, which is `n_nodup`, a *field of the node
   record*.  The other half (the minted names) is a fact about where the run
   starts and belongs at the program level, where `st0` is chosen.

   **A gap found and closed, 2026-09-26.**  `node_carries_preserves` fixes a
   *single* `cenv` for both runs, but `generate_lnode_sig` runs the source
   equations against `lnode_clock_env n` and the unnested ones against
   `lnode_clock_env (unnest_node ...)`, and the second is strictly larger --
   `n_vars` grew.  So the node level cannot simply quote the equation-level
   theorem.

   It does not have to: `cenv` reaches the generator *only* through
   `eqn_clock_type`, and only at the variables an equation **defines**.  Two
   environments agreeing there give the same constraints, which is
   `generate_leqns_constraints_cenv_ext` *[verified, compiles]*, proved down
   the whole dispatch -- `eqn_clock_type_cenv_ext`,
   `generate_lvars_constraints_cenv_ext`,
   `generate_ldef_constraint_cenv_ext`, `generate_lgen_constraint_cenv_ext`,
   `generate_lone_constraint_cenv_ext`,
   `generate_lsplit_constraints_cenv_ext`,
   `generate_leqn_constraint_cenv_ext`.  The call rules do not consult `cenv`
   at all, which is why that case is `reflexivity`.

   Still open at this level: assembling the equation-level entailment from
   `node_carries_preserves` (its `wc`/`NoDup`/ambient premises have to be
   supplied for the node), and the two program-level hypotheses -- the aux
   lookup and the minted-name disjointness, for which
   `unnest_node_moved_fresh_generated_aux` is the template *[untested]*.  This is also where the three scoping hypotheses
   are discharged, with `stF := st1` (the state `generate_lnode_sig` ends at)
   and `scope` covering `locals ++ minted st0 st1`.  Open question to settle
   there and not before: the node-level `scope` must also contain the
   interface names, which the current `simplify cs (locals ++ minted st0 st1)`
   does not by itself give.
7. `unnest_global` by signature-global lockstep.  **The lockstep itself is
   done, 2026-09-26** *[verified, compiles]*, and it turned out to be
   **phase-independent** -- which means Leg I inherits it rather than
   repeating it.  Four pieces:

     * `call_weakens G1 G2` -- the *whole* content the generator needs about
       two signature globals: at every call site the target's signature is
       found and its instantiated block is entailed by the source's, at the
       same valuation and in the same state.  One invariant, not the six that
       re-deriving it at each call would need.  `call_weakens_cons` extends it
       a node at a time; `sig_call_weakens_from_good` is where a node pays for
       it.

       **Reuse found, not rebuilt.**  `sig_call_weakens_from_good` is
       essentially two `SIFSignature.v` theorems composed:
       `generate_constraints_ok_from_good` supplies the target block (every
       premise transfers across equal interface fields), and
       `signatures_preserved_equal_calls_from_good` supplies the entailment.
       Both were already there, hoisted out of the NLustre-to-Stc bridge.
       The only new observation is that an instantiated block is scoped to the
       *actuals*, so taking the scope to be the actuals' own names makes
       `scope_fresh` and `call_subst_scoped` free and leaves `call_subst_fresh`
       as the single real side condition.

     * `generate_leqns_constraints_entails_G` -- the generator is monotone in
       its callees, proved down the whole dispatch.  Because
       `preserves_on` at a call site collapses to plain implication under the
       caller's valuation, the weakening travels as a `cs_entails` between
       constraint lists at a *fixed* valuation: no witness to move, no scope
       to track, composing over `cmerge` and `++` by
       `listSatisfiable_cmerge` alone.  The types and the state do not move,
       so the statement is a `Forall2` of `lst_entails` -- equal on the left,
       entailed on the right.

     * `unnest_node_signatures_preserved_decoupled` -- one node, two
       accumulators, **two independent states**.  The composition goes through
       an intermediate run, the *source* equations read against the *target*
       accumulator: it exists and ends in the same state because a signature's
       constraints reach only the blocks and those are state-pure.

     * `generate_all_lsignatures_weakens'` -- the induction along the program.
       The node lists are related by a parameter `R`, the per-node step is a
       hypothesis, and `call_weakens` is the invariant.  Nothing in it mentions
       unnesting.

   **The states must be decoupled, 2026-09-26.**  The two drivers cannot be
   held at a common state.  A source node's nested call mints one security
   name per result; the equation the pass lifts it into borrows the name of
   the variable it defines and mints *nothing*.  So the target run falls
   behind from the first node with a nested call, and a shared `st0` is not
   available.

   Nothing is lost, and again the lemma was already there:
   `state_pure_generate_leqns` (`SecLusUnnestingEquations.v`) says the
   generator is state-pure on an unnested equation list, so the target run can
   be *restarted* at the source's state -- which is where the equation-level
   theorem wants it.  The target's own `simplify` window needs no attention at
   all, because `preserves_on_simplify` eliminates on each side
   independently.

   What is left at the program level is not structural: the naming-pass facts
   (the aux lookup; `find_node_env` for the node), and `signature_good` /
   `signature_scoped` / `NoDup (signature_scope _)` for a *generated Lustre*
   signature.  The last three are the Lustre analogue of what
   `SecNLusTypingCorrectness.v` proves for NLustre, and they live after
   `SecLusUnnesting.v` in the build order, so they enter the per-node step as
   hypotheses exactly as Leg A's `node_step_entails` leaves its own.
8. Leg I (`normfby_global`).  **The equation level is done, 2026-09-27**
   *[verified, compiles]*, in `src/SIF/SecLusNormFby.v`.

   Leg I is much cheaper than Leg U, and for a structural reason worth
   recording: `fby_equation` rewrites only at the **top** of an equation and
   carries the operands over verbatim.  There is no expression induction
   anywhere in this leg -- only a four-way case analysis, which
   `fby_equation_spec` supplies.

     * the node skeleton -- `normfby_node_fields`,
       `normfby_node_sig_interface` (five of six signature fields equal on the
       nose), `generate_leqns_normfby_node_cenv`.  The last is a *quotation*:
       `find_clock_node_ext_defd` (moved into the shared part) needs nothing
       about which pass extended the variables, because `n_defd` puts a
       defined variable among the node's own and the extended node's
       `node_NoDup` -- which the pass had to prove to build the record --
       keeps the added ones out.  That replaces Leg U's
       `unnest_node_new_ids_fresh` and its three supporting lemmas.

     * `preserves_on_fresh_names` -- the **whole semantic content of the
       leg**, stated once: give each variable the pass created exactly the
       level of the left-hand side of the equation it was created for.  The
       equation that *defines* a created variable then holds because that
       level is its own bound, and the equation that *uses* it holds because
       the source equation already bounded that level by the variable it
       defines.  No `NoDup` on the created names is needed, because they all
       get the *same* level -- which also removes any need for `env`
       injectivity here: `b <> bp` follows from `b` being in scope and `bp`
       not.

     * the three interesting shapes: `fby_cut_entails` (a constant initial
       value, cut at an output), `fby_ite_entails`, `arrow_entails`.  The two
       remaining shapes leave the equation alone, so the two runs are the same
       run.

     * `fby_equation_entails` -- the dispatch.  The node's data enters as one
       hypothesis quantified over the shape, so it is vacuous precisely on the
       shapes that need nothing.  The created variables' clocks and names come
       off the fresh state through `init_var_for_clock_In` and
       `fresh_ident_In`, which NormFby and Fresh already prove.

   **`fby_ite_entails` is where the two-operand `fby` rule pays.**  The pass
   turns a non-constant-initialised `fby` into an `ite` between the initial
   value and a fresh variable carrying the delayed one.  The `ite`'s first
   branch needs the *initial* value's level to be below the variable being
   defined -- and it is, but only because the source constraint mentions it.
   The NLustre rule, which legitimately types only the delayed operand, would
   leave nothing there to appeal to.  This is the first place in the
   development where the corrected rule is load-bearing rather than merely
   stronger.

   **Done since:** each chunk also yields its created security names and
   `constraints_scoped (scope ++ extras) cet` *[verified, compiles]*.  The
   shape facts moved outside the valuation, because a target chunk has to be
   shown scoped whether or not the source is satisfiable at all.  Two premises
   went away with it: `~ In bi L` follows from `~ In bi scope` once `L` is
   known visible, and `b <> bi` follows from `In b scope` with it.

   ### CORRECTION 2026-09-27: the per-chunk composition does not apply

   The route recorded above -- assemble the chunks with
   `preserves_on_concat_list` -- **cannot be used**, and the reason is a fact
   about the pass, not about the proof.

   `init_var_for_clock` *reuses* an initialisation flag:

   ```coq
   match find (fun '(_, ((ty, cl'), isinit)) =>
                 isinit && (cl' ==b cl) && (ty ==b bool_type)) (st_anns st) with
   | Some (x, _) => ((x, []), st)          (* reuse: creates nothing *)
   | None => ... fresh_ident norm2 ((bool_type, cl), true) ...
   end
   ```

   So two `arrow`s (or two non-constant `fby`s) on the **same clock** share one
   flag.  The first group creates it and emits its equation; the second merely
   mentions it.  Both groups' `extras` therefore contain that flag's security
   name, and `NoDup (concat extras)` -- which `preserves_on_concat_list`
   requires -- is **false**.  Nor can the flag be dropped from the second
   group's `extras`: its constraint mentions the name, so
   `constraints_scoped (scope ++ extras_2) tgt_2` would fail; and it cannot be
   put into `scope`, because then the witness could not move it and the flag's
   own equation would have nothing to make it hold.

   ### The composition that does work

   One application over the **whole** target list, with a level *per created
   name* rather than one level per chunk.  The level of a created name is the
   left-hand side of the target constraint that **defines** it:

     * a flag on clock `ck` gets `merge (merge [rst_ty] ckty) sw`, the lhs of
       its own `init` equation, with `sw` the samplers of `ck`;
     * a `px` gets `merge (merge [rst_ty] ckty) (merge sw s1)`, the lhs of its
       own delayed definition.

   Three things make this work, and they are worth stating because they are
   what the earlier route missed:

     1. **It is uniform on the shared name.**  A flag's level depends only on
        its clock, so every group that mentions it wants the same level.  That
        is exactly why sharing stopped being a problem.
     2. **`NoDup` is recovered.**  The created names are collected *once*
        globally, not per chunk, so each appears once.  What it needs is `env`
        injectivity and `NoDup (st_ids st_final)`, from
        `fby_equations_st_valid` and `st_valid_NoDup`.
     3. **The assignment is not circular.**  A created name's defining
        constraint mentions only *visible* names -- clock samplers and the
        delayed operand's type, never another created name -- so the levels are
        values of the original valuation, and nothing has to be solved.

   The obligations per target constraint `(lhs, [d])` are then:

     * if `d` is created: `lhs` is its recorded level (and every name in `lhs`
       is visible);
     * otherwise: there is a source level `Lsrc` the source constraint bounds
       by `d`, every visible name of `lhs` is in `Lsrc`, and every created name
       `z` of `lhs` has its level inside `Lsrc`.

   Both discharge exactly as the three case lemmas already do -- `sw ⊆ ckty`
   from `add_whens_const_type`, and `s1 ⊆ s1`.

   **What this costs.**  The membership arguments in `fby_cut_entails`,
   `arrow_entails` and `fby_ite_entails` are already the per-constraint facts
   needed; what changes is the *packaging*: each case lemma should produce a
   `Forall` of per-constraint facts instead of a `preserves_on`, and
   `preserves_on_created` (replacing `preserves_on_fresh_names`) applies once,
   at the node, over the whole list.  The composition over the equation list is
   then a plain `Forall_app` induction with no disjointness bookkeeping at all
   -- which is why this is the cheaper route as well as the correct one.

   Then prepend `normalize_global_sem` so source Lustre is the entry to
   `lnode_noninterference_streams`.  Everything from `call_weakens` upwards is
   shared with Leg U and needs nothing new.

### Leg I complete, and what the remaining two items cost, 2026-09-29

Leg I is closed.  `normfby_node_step` asks for nothing pass-specific: the
naming pass's two lookups, that the run's state records each identifier once
with a clock whose type is visible, and that a generated Lustre signature is
good and scoped.  `node_pairs_exists` discharged the level assignment, built
from two constructions -- flags once from the state at a level that is a
function of their clock, delayed variables by walking the run -- with
functionality following from `NoDup (st_ids stf)` and `env` injectivity.

`normalize_signatures_weaken` therefore reduces preservation across
normalisation to exactly two families of hypothesis, and **neither is a
blocker**.  Concretely:

**(A) The `A eq` ambients.**  Every piece of infrastructure exists:
`carries_at_streams` is defined and *every* constructor but `Eapp` has its
`_streams` lemma (`Econst`, `Evar`, `Eunop`, `Ebinop`, `Ewhen`, `Emerge`
control and lift, `Eite` control and lift, `Efby`, `Earrow`), and every
call-case helper is proved -- `stream_rel_amb_weaken`, `wc_Eapp_out_instck`,
`call_amb_below_result_ambients`, `call_arg_ambients`,
`clocks_covered_call_args`, `call_arg_ambients_length`,
`call_arg_ambients_scoped`.  What is left is `carries_Eapp_streams` (the
scalar `carries_Eapp` is 622 lines and is the template), the expression
induction, and re-establishing the equation/equation-list/node chain on the
pointwise relation.

**There is no shortcut, and this is worth recording before someone tries
it.**  The obvious cheap route is to pick `A eq` to be the equation's own
ambient, `merge [rst_ty] ckty`, and discharge the second premise from the
source constraints -- which are available, since `eqns_carries_amb` already
has `listSatisfiable dlt ce`.  That works for a single-variable equation.  It
**fails for a multi-output equation whose outputs are on different clocks**:
the second premise forces `A eq` *below* every output's ambient, the first
forces it *above* every lifted variable's ambient, and those are incompatible
once the clocks differ -- which `wc_equation` permits (a call's outputs need
not share a clock).  Replacing one `A eq` by a per-stream ambient is exactly
what the pointwise contract is for, so it is required, not merely convenient.

**(B) The program-level facts about a generated Lustre signature.**  The
NLustre analogue is `SecNLusTypingCorrectness.v`, 3022 lines, and it is the
template: `generate_node_sig_good_from_local_env`,
`generate_node_sig_scope_nodup_from_local_env`,
`generate_node_sig_scoped_env_scoped`,
`generate_all_source_signatures_good_scoped_env`.  The one Lustre-specific
difference is that the generator mints, so `simplify` eliminates
`locals ++ minted st0 st1` where NLustre eliminates only the locals; that
machinery is already in Leg U (`minted_spec`, `fresh_idents_NoDup`,
`unnest_node_moved_fresh_*`).

The one thing that *could* have blocked this is whether a callee's formal
names leak into the caller's published constraints through the call rule.
They do not: `generate_constraints_scoped` (`SIFSignature.v`) says an
instantiated block is scoped to the actuals, and Leg U already relies on it.

So: no blockers, and (A) is the larger of the two.

### Why the passes make preservation work

Checked 2026-09-23, and worth recording because it is what makes the
signature comparison meaningful at all.  Both `unnest_node` and
`normfby_node` set

    n_name := n_name n;   n_in := n_in n;   n_out := n_out n;
    n_vars := n_vars n ++ nvars

so the interface is *syntactically* unchanged and `n_vars` only grows.
Hence `s_name`, `s_in`, `s_out`, `s_clk`, `s_reset` of a source and a
transformed node's signature are **equal by computation**; only
`s_constraints` differs, which is exactly what `preserves_on` speaks about.
And since `n_vars n` is a *prefix* of the transformed node's, and
`fresh_map_list` allocates in order from `Env.empty`, a variable keeps its
security name.  *[verified: `Unnesting.v`, `NormFby.v`, `NameInterface.v`]*

One architectural obligation follows and is not yet in any statement: the
environment must come from the **normalised** program and be used for every
phase, because `moved_by env init_st st'` presumes `env` maps the minted
variables.  *[untested]*

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
