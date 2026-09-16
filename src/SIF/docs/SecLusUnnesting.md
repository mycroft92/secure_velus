# SecLusUnnesting — the unnesting leg (Leg U)

## Role

`SecLusUnnesting.v` proves that the security constraints generated for a
Lustre node survive `unnest_exp` / `unnest_equations`, the first pass of
Velus's normalisation.  It is the leg on which the Lustre-level results
actually rest: typing preservation into NLustre, and through it
noninterference for source Lustre.

This document records the *code-level* shape of that proof — the statement,
why each of its premises and conclusions is there, which case forced each
one, and which facts about the pass had to be established before the
induction could be attempted at all.  Almost none of this appears in the
ICTAC paper, which states the rules and their soundness but not the
invariants a mechanised induction over `unnest_exp` needs.

## Why this leg, and not transcription

The refinement component of a Lustre security type, `LST = ST * list
constraint`, exists to type an expression that contains a **nested node
call**: rule (LTncall) gives each result of a call a fresh name refined by
the callee's instantiated constraints.

Transcription (`Tr.to_equation` and friends) cannot exercise any of that.
`to_lexp` rejects `Eapp` outright, so by the time transcription runs every
call has already been lifted into its own equation and the carried component
is empty everywhere.  A preservation proof over transcription is therefore
true but vacuous as far as the refinement machinery is concerned — it never
sees a non-empty `snd` of an `LST`.

Unnesting is the pass that *does* the lifting, so it is the pass where the
carried constraints turn into emitted equations.  That is the content of
this leg: **the constraints an expression carries are the constraints of the
equations unnesting emits for it**, and the fresh security names the typer
minted correspond to the program variables unnesting minted.

The two allocators cannot agree on names — unnesting mints `gensym norm1 _`
and the security monad mints `gensym sec _` — so the two sides are related
by a correspondence, never by equality of names.  Absorbing that
correspondence is what the witness algebra below is for.

## The statement

The expression-level property is `carries_at P is_control e`, and
`carries P e := forall is_control, carries_at P is_control e`.  Its shape:

    unnest_exp P is_control e st            = ((es', eqs), st')
    assign_lexp_type GL env base_ty rst_ty e sst  = OK (ts,  sst')
    generate_leqns_constraints ... cenv eqs xst   = OK (ce,  xst')
    assign_lexps GL env base_ty rst_ty es'  yst   = OK (ts'', yst')
    listSatisfiable dlt (carried ts)
    ------------------------------------------------------------------
    exists dlt',
         agree_off (moved_by st st') dlt dlt'
      /\ listSatisfiable dlt' ce
      /\ Forall2 (fun t t'' => satisfiable dlt' (fst t'') (merge amb (fst t)))
           ts ts''
      /\ constraints_scoped (scope ++ moved_by st st') ce
      /\ Forall (fun t'' => st_scoped (scope ++ moved_by st st') (fst t'')) ts''

One valuation goes in — one satisfying what the *source* expression carries,
i.e. the obligations its nested calls impose on the names the security monad
minted.  One comes out, satisfying what unnesting *emitted*.

### Why the third conjunct is domination, and in that direction

This took the longest to get right, and it is the one place where the
mechanisation departs visibly from the paper's presentation.

It is **not** "the two sides give the expression the same type".  In four of
the five lifting cases the pass replaces a compound expression by a variable
whose defining equation carries an ambient — the reset level joined with the
clock the variable is defined on.  The target's type for that result is
therefore the source's type *raised by that ambient*, never equal to it.

Nor is the useful direction "source below target".  What the enclosing
equation needs is the target's type below the source's-plus-ambient, because
the enclosing equation sits under the same ambient and absorbs it.  Hence
`satisfiable dlt' (fst t'') (merge amb (fst t))`: target dominated by
ambient-joined source.

An earlier draft had the relation the other way round.  It typechecked, and
it was useless: it does not let the target's defining constraint be derived
from the source's.

### Why `amb` is a parameter

Which ambient a lifted equation sits under is a fact about *clocks*, and
belongs where clocks are known — at the equation level — not inside an
induction over expressions.  So `amb : ST` is a section variable, pinned by
a premise:

    forall x ck ckty,
      In x (vars_defined eqs) ->
      find_clock cenv x = OK ck ->
      assign_clk_type env base_ty ck = Some ckty ->
      incl (merge [rst_ty] ckty) amb

The premise is deliberately **syntactic** — containment of name lists, not
domination of valuations.  Two reasons.  A domination premise would depend
on the witness being constructed, which is circular.  And a syntactic
premise passes to the sub-expressions for free, since a sub-expression's
emitted equations are a sublist of the parent's
(`vars_defined_incl_l` / `vars_defined_incl_r`).  `hm_ext` is monotone under
inclusion (`hm_ext_incl`), so domination still follows where it is needed.

It also makes the eventual equation-level step an absorption rather than an
argument: instantiate `amb` as the equation's own ambient joined with the
source type and `merge amb (fst t)` *is* `amb`.

## The witness algebra, and why `agree_on` is not enough

The natural first statement says the witness keeps the visible names fixed:
`agree_on scope dlt dlt'`.  That is too weak, and `Ebinop` is where it
breaks.

`agree_on scope` says nothing about names outside `scope` — and those
include the names the security monad minted for a **sibling** sub-expression,
whose own hypothesis still has to be applied to constraints over exactly
those names.  A witness free to move them cannot be composed with its
sibling's.

The fix is to bound *where the witness may move* rather than where it may
not, and to index that bound by the **pair** of fresh states:

    new_ids st st'  :=  st_ids st' minus st_ids st
    sec_of xs       :=  the security names the naming pass gave xs
    moved_by st st' :=  sec_of (new_ids st st')
    agree_off xs d1 d2 := forall x, ~ In x xs -> d1 x = d2 x

Sibling sub-expressions run over consecutive stretches of the fresh state,
so their moved sets are disjoint (`moved_by_disjoint`), and each sibling's
conclusion survives the other's witness.  Widening in either direction is
available (`moved_by_prefix`, `moved_by_suffix`), which is how the premise
passes down to sub-expressions and the conclusions come back up.

Nothing is lost: `agree_off_agree_on` recovers `agree_on scope` whenever the
moved names miss the scope, which is what the node level asks for.

`moved_by_disjoint` is where `env_injective env` is used: disjoint *variable*
sets give disjoint *security-name* sets only because distinct variables get
distinct names.

### The two scoping conclusions

They are forced by the same argument.  The emitted constraints `ce` name the
variables this run created, which `scope` cannot see; without saying so,
nothing stops a later sibling from moving exactly the names an earlier
sibling's conclusion mentions.  Hence
`constraints_scoped (scope ++ moved_by st st') ce` and the matching bound on
the target types.  `listSatisfiable_off_scope` is the transfer that uses
them.

## What the pass's output gives for free

Three facts about `assign_lexp_type` **on the target side** do a lot of work,
and all three come from the same observation: unnesting returns *normalized*
expressions, and a normalized expression contains no call.

- `assign_lexp_normalized_lexp_pure` / `assign_lexp_normalized_cexp_pure` /
  `assign_lexps_normalized_pure` — the call case is the only place the
  generator touches its state, so on the pass's output the generator is
  **state-pure**, and gives a normalized expression exactly one flow.

  This is what makes `unnest_merge`'s interleaving harmless.  `unnest_merge`
  emits `Emerge ckid [e1_i] [e2_i] _` per stream, so the target types the two
  branches *alternately*, where `assign_lexps` on the source takes one branch
  and then the other.  With purity every sub-call starts and ends at the state
  the whole list started at, and the order stops mattering.

- `assign_lexp_type_length` / `assign_lexps_length` — the generator returns
  one flow per stream, just as the pass returns one expression per stream.
  Needed wherever the two sides are lined up positionally.  This one is a
  full induction over `exp` and is **not** restricted to normalized
  expressions; it needs `wl_exp`.

## The clock environment

`generate_leqns_constraints` does not read the equations alone: through
`eqn_clock_type` it looks every defined variable up in the node's
`lnode_clock_env`.  So the two generators cannot be compared at all until the
two environments are known to answer alike.

`unnest_node` leaves `n_in` and `n_out` untouched and only *appends* to
`n_vars`.  Extension by itself would not be enough — `Env.adds'` lets a later
binding shadow an earlier one, so an appended name colliding with a declared
one would silently change the answer.  But the *target* node carries its own
`n_nodup`, and that is exactly the statement that the appended names are
fresh for the declared ones.

`unnested_locals_fresh`, `lnode_clock_env_extended`, `find_clock_extended`.
Freshness here is read off the node the pass returns; it is not assumed.

## Case by case, and what each one forced

Each new case changed the statement once, and in every case the change was
forced rather than chosen.  That progression is the most useful thing to know
when picking the proof back up.

- **`Econst`, `Evar`** (`carries_Econst`, `carries_Evar`) — the pass returns
  the expression untouched and emits nothing, so the witness is the valuation
  we started with.  `carries_unchanged` is the shared shape.

- **`Eunop`** (`carries_Eunop`) — forced `wl_exp` into the statement.  The
  pass returns `Eunop op (hd_default e1') a`, and `hd_default` only loses
  nothing because the operand is single-stream, which is a `wl_exp`
  condition (`unnest_exp_one`).

- **`Ebinop`** (`carries_Ebinop`) — the first genuine composition, and it
  forced both the witness bound (`agree_off`, state-indexed) and the two
  scoping conclusions, for the reasons above.

- **the list level** (`carries_list`, `carries_list_intro`) — forced
  nothing.  It is the `Ebinop` argument folded, and it went through
  unchanged.  That is the best evidence the statement had settled.

- **`Ewhen`** (`carries_Ewhen`) — lifts nothing; the pass pushes the sampling
  inward, one `Ewhen` per stream, and the typer's rule is a map, so the
  target types are the source's transformation applied to the operands'
  target types (`assign_lexps_unnest_when_inv`, `carried_map_when`).

  The one thing needing care is that the sampling variable's level is
  visible.  That is **not** a new hypothesis: the level is already inside the
  source type and the source type is scoped.  The degenerate case — no
  streams, so the variable never appears — is handled by a disjunction
  rather than by an assumption.

- **`Emerge` under `is_control`** (`carries_Emerge_control`) — forced
  `is_control` into the statement, since the branches unnest under `true`;
  and forced the purity results, for the interleaving reason above.

- **`Eite` under `is_control`** (`carries_Eite_control`) — the first
  three-way composition: the scrutinee supplies the head the two branches
  are joined under, so the witness is built in three steps and the
  scrutinee's bound must survive both branches' witnesses.

  Forced two things.  The **clocking judgement**: an `Eite` with no result
  streams drops its scrutinee from the target expression list while still
  emitting the scrutinee's equations, so the scrutinee's hypothesis could not
  be applied and its emitted constraints could not be satisfied.  This was
  not a proof-engineering inconvenience — the statement was *unprovable*
  there.  `wc_Eifte` requires `0 < length tys` and rules it out.  And the
  **length** result, since the scrutinee's target type is read out of the
  first resulting stream, so there has to be one.

  It also needed the scrutinee's obligations to be read out of the result's
  by *containment* (`carried_map_ljoin_mono`, `carried_map_ljoin_head`,
  `constraints_scoped_sub`, `listSatisfiable_sub`) rather than by computing
  the result's carried set: the merge's head is a variable and carries
  nothing, but the conditional's head is a whole type and may carry a nested
  call's obligations of its own.

### The join lemmas

`Emerge` and `Eite` both build their result with
`ljoin_list (map (ljoin h) _) _`, on the source and on the target alike, so
the relation between the two sides is established once by walking the two
joins together: `ljoin_list_rel_head`, `ljoin_list_scoped_head`,
`ljoin_list_scoped_head_inv`.  The head is a parameter because `Emerge`
joins a sampling variable's level while `Eite` joins the scrutinee's whole
type — and that type *differs between the two sides*, so the head carries
its own domination premise.  The sampling cases are corollaries.

`fst (ljoin a b)` is a rewrite (`fst_ljoin`, `fst_lvar`), never a `simpl`:
`simpl` unfolds `merge` into its inner `fix` on one side of a goal only, and
two otherwise identical sides then stop being syntactically equal.  This is
the same hazard `SecLTyping.v` warns about for `bind`.

## The lifting cases

Not yet proved.  All five — `Emerge` / `Eite` without `is_control`,
`Efby`, `Earrow`, `Eapp` — end identically: `idents_for_anns` (or
`idents_for_anns'` for the call) mints one variable per result, the pass
returns an `Evar` for each, and it emits one equation per result binding
that variable to the compound expression it replaced.

So the target's type for a result is a **bare name**, and what pins it down
is the emitted equation's own constraint,

    merge (merge [rst_ty] ckty_i) (fst t_i)  ⊑  [env(x_i)]

which means the witness is **chosen** there rather than inherited: give each
minted name exactly the value its constraint demands and the emitted
constraints hold by construction.  `upd`, `upds`, `upds_notin`,
`upds_agree_off`, `upds_nth`, `hm_ext_upds` are that machinery.

Two things make the choice legitimate.  The names are minted in this run, so
moving them is inside the bound the statement allows; and nothing the values
are computed from mentions them, since everything else was minted earlier or
is visible.

### How the pass's freshness is obtained

The other half — that the minted names are **new**, so that their security
names land in `moved_by st st'` rather than somewhere the statement forbids
moving — looked at first as though it required carrying Velus's own
state-validity invariant, `st_valid_reuse`, with the shrinking reusable set
that `unnest_exp_st_valid` threads.

It does not.  `unnest_exp_vars_perm` says the pass adds to the fresh state
exactly the variables its emitted equations define:

    Permutation (vars_defined eqs ++ st_ids st) (st_ids st')

With a single `NoDup (vars_defined eqs ++ st_ids st)` premise that turns the
abstract moved-set into something concrete and checkable — the names a run
may move are the security names of `vars_defined eqs`, which is the *same
list the ambient premise already quantifies over*.  `vars_defined_in_new_ids`
and `sec_of_vars_defined_moved` are the bridge.

The premise is uniform across a constructor's operands and splits along the
concatenation of their emitted equations (`NoDup_vd_app_l`,
`NoDup_vd_app_r`), so it threads without the non-uniformity
`st_valid_reuse` would have forced.  It is discharged once, at the node
level, from `st_valid_NoDup`.

This is worth recording as a case where the obvious route — match the pass's
own induction — was the more expensive one, and a derived fact the pass
already proves was enough.

### The operands are not in the target expression list

One thing the delay cases forced that nothing before them did.  The
operands' hypotheses need the operands' *target* typings as a premise, and
for `Ewhen`, `Emerge` and `Eite` those are available: the target expression
list is built out of the unnested operands, so inverting the target typing
of the whole expression yields them.

For `Efby` and `Earrow` it is not.  The target expression list is the minted
variables — the operands appear nowhere in it.  They appear only inside the
*emitted equations*, as the operands of the delays those equations bind.  So
the operands' typings have to be recovered from the emitted block rather
than from the returned expressions, which is a small extra induction
(`defs_operand_types`, still to write) over the same zipped list
`lifted_defs` walks.

It is worth recording because it is the first place where the returned
expressions and the emitted equations carry genuinely different information,
and because it is a symptom of the statement's shape: the target typing is a
*premise* rather than a conclusion.  Making it a conclusion — proving the
target types whenever the source does, which is the stronger and more
natural "type preservation" statement — would remove this wrinkle and the
`Eite` zero-stream one together.  That is a larger change and is not being
made now.

### The block lemma

`lifted_defs` is what the four non-call lifting cases share: given the
operands' relation, it produces the extended witness together with all four
conclusions for the emitted block.  Its supporting pieces are
`generate_leqn_constraint_def` (the emitted right-hand sides are never
calls, so the equation generator takes its ordinary-definition branch),
`generate_ldef_constraint_inv`, `assign_lexps_evars` (the target types are
the minted variables' names), and the two form lemmas that put `Efby`'s and
`Earrow`'s differently-spelled emitted lists into one shape.

### What the call case needs

The call is the case the refinement machinery exists for, and its
scaffolding predates the induction: `assign_lexp_Eapp_inv`,
`unnest_exp_Eapp_inv`, `Eapp_and_emitted_shape`,
`assign_lexp_Eapp_result_types`, `unnest_exp_Eapp_result_vars`,
`Eapp_renaming_lists`, `unnest_reset_shape`,
`unnest_exp_Eapp_reset_is_var`, and the renaming algebra
`subst_idents_in_type` / `subst_constraints_out_map_{correct,complete}`.

Note `idents_for_anns'` **reuses** a name when the annotation already carries
one, so the correspondence with `fresh_idents (length anns)` is not
mint-for-mint.  It does not need to be: both lists have length
`length anns`, so the correspondence is positional over the call's results,
and whether a result's variable is new or reused only changes which side of
it was already named.

The call also breaks the shape the other four lifting constructors share.
They emit **one equation per result**, which is what `lifted_defs` walks; the
call emits a **single** equation binding all of them at once, and its
constraint comes from `generate_lcall_constraint` rather than from
`generate_ldef_constraint`.  So `lifted_defs` does not apply and the call
gets its own block argument.

The one genuinely missing ingredient is a **semantic** monotonicity of
`generate_constraints` in its actual argument types:

    Forall2 (fun t1 t2 => satisfiable dlt t2 t1) inp1 inp2 ->
    generate_constraints sig inp1 clk rst out _ = OK (cns1, _) ->
    generate_constraints sig inp2 clk rst out _ = OK (cns2, _) ->
    listSatisfiable dlt cns1 -> listSatisfiable dlt cns2

`SIFSignature.v` already has `generate_constraints_mono_inp`, but that is
*syntactic* — it asks that every name of one actual occur in the other, and
concludes `constraints_src_le`.  It was written for the Stc-to-Obc bridge,
where the compiled arguments literally drop the `when` guards the source
arguments carry, so inclusion holds on the nose.  The unnesting leg gives no
such inclusion: the two sides' argument types are related by domination under
a valuation and by nothing syntactic at all.

Two things are known about the semantic form, and the second is the reason
it is not simply the syntactic proof with `⊑` in place of `⊆`.

**It needs a freshness side condition the syntactic one did not.**
Substitution replaces a formal by `st_remove x ty ⊔ st_remove x v` — it
removes the formal from the *actual* as well as from the body.  `st_remove`
preserves set inclusion, which is what carries the syntactic chain; it does
**not** preserve domination, since dropping a name can shrink the larger side
below the smaller.  What rescues it is that the formal is a callee name while
the actual is built from caller names, so the removal is vacuous on the
actual.  `subst_ident_in_type_mono_sem` proves the one-step case with that
premise, and the premise is exactly what the call-site freshness lemmas
establish elsewhere in the development.

**The obvious invariant for the chain does not hold.**  The natural move is
to carry "same targets, dominated sources, pointwise" (`cs_dom`) through the
four substitution steps.  That fails at the second step, because its
two-sided form —

    satisfiable dlt ty2 ty1 -> satisfiable dlt v2 v1 ->
    satisfiable dlt (subst ty2 x v2) (subst ty1 x v1)

— is **false**.  If `x` occurs in `ty1` but not in `ty2`, the right-hand side
drops `x`'s contribution and replaces it by `v1`, while the left keeps `ty2`
whole; `hm_ext ty2 ⊑ hm_ext ty1` says nothing about `hm_ext ty2` against
`hm_ext (st_remove x ty1)`.

The real invariant is structural rather than relational, and it does not
have to be *syntactic*.  Writing it as an equation `fst c = F ⊔ V` — a common
residual joined with a side-specific accumulation of the actuals — would need
`st_remove` to distribute over `merge` on the nose, which holds only up to
sortedness, since `st_remove` is a plain list filter and `merge` a sorted
union.  Sortedness would then have to be threaded through every step.

`hm_ext` depends on a type only through its members, so the chain runs at the
level of **membership** instead and domination is recovered at each use.
Each substitution step then only has to say which names survive it, which is
what the freshness premise decides directly.  `remove_all` with its
membership characterisation, `satisfiable_of_members`, `hm_ext_union_le` and
`hm_ext_union_ge` are the foundation.

`cs_chain dlt rest cs1 cs2` is the invariant.  `rest` is the formals still to
be substituted, and it carries three clauses: the targets never move; the
remaining formals occur on one side exactly when they occur on the other, so
the two sides **branch alike** at every remaining step; and domination holds
not as it stands but *after dropping any of the remaining formals*.  That
third clause is what the naive pointwise invariant lacked and what survives
the next substitution.  `cs_chain_refl` starts it (both sides are the same
signature) and `cs_chain_nil_dom` collapses it to `cs_dom` at the end.

`subst_ident_in_constraints_chain` is one formal;
`subst_constraints_inp_map_chain` folds it over the input map, leaving the
clock and reset still in `rest` — so those two are the same lemma again with
the same actual on both sides, which makes them preservation rather than
progress.  Threading `rest` is what lets one lemma cover all six
substitutions instead of needing a separate argument for the last two.

### What is left of the call chain

The output substitution is **not** another step of the same chain.  The two
sides rename the formal outputs to *different* actuals — the source to the
names the security monad minted, the target to the security names of the
variables the pass minted — so the invariant's first clause, that the targets
never move, is exactly what it breaks.

That is the renaming `subst_constraints_out_map_correct` and
`subst_constraints_out_map_complete` already exist for: they relate the two
sides under a valuation that identifies each formal with its actual, which is
how the witness is chosen on the target names anyway.  So the output half
should be discharged through those rather than by extending `cs_chain`, and
then the final lookup pass (`findST` over the substituted constraints, one
per output) reads the two sides' sources off in the same order.

## Standing hypotheses

Three, all true and all to be discharged at the node level:

- `env_injective env` — distinct variables get distinct security names.
  Used by `moved_by_disjoint`.
- `st_scoped scope amb` — the ambient names program variables only.
- the syntactic ambient premise described above.

## Things the paper leaves implicit

Collected, because they are the difference between the rules being sound and
the mechanisation going through:

1. The direction of the type relation between the two sides, and that it is
   domination modulo an ambient rather than equality.
2. That a witness must be bounded in *where it moves*, not merely pinned on
   the visible names, or sibling sub-expressions cannot be composed.
3. That the emitted constraints and target types need their own scope bound,
   for the same reason.
4. That the two constraint generators read declared clocks, so the two
   nodes' clock environments have to be shown to agree before anything else.
5. That the generator is state-pure on the pass's output, which is what
   makes the pass's operand *ordering* irrelevant.
6. That `wc_exp`, not just `wl_exp`, is needed — and not for the ambient
   (which was the expected reason) but to rule out a zero-stream conditional
   whose scrutinee is dropped while its equations are kept.

## Status

Proved, no admits: **every constructor except the call**, at both
`is_control` flags — `Econst`, `Evar`, `Eunop`, `Ebinop`, the list level,
`Ewhen`, `Emerge` and `Eite` in both their control and lifting branches,
`Efby` and `Earrow` — together with all the infrastructure above,
`lifted_defs`, and the per-constructor support (`unnest_fby_types`,
`unnest_arrow_types`, `unnest_merge_types`, `unnest_ite_types`, the
`defs_operand_types_*` family, and the state-independence and
elementwise-typing results they rest on).

`Earrow` was obtained from `Efby` by substituting the constructor and the
emitted list's spelling, and went through unchanged — which is the intended
reading of "the two differ only in what the initialisation pass will later
act on".  `Eite`'s lifting branch is the merge's with the scrutinee composed
in front: four witnesses in sequence, each surviving the ones after it
because they move over disjoint stretches of the fresh state.

Remaining: `Eapp`; then the equation, node and program levels (reusing
`Signature_entails` for the two-globals lockstep), then Leg I
(`normfby_global`).

## Downstream use

`SecLusConstraintExport.v` applies this functor to `Instantiator`'s real
modules, so a change to the parameter list is caught immediately rather than
at the end of the chain.  Nothing at or below `SecNLusTyping.v` is touched by
this leg; the NLustre, Stc and Obc layers are used only through module
parameters.
