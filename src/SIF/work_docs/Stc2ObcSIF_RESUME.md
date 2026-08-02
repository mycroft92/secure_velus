# Stc→Obc SIF preservation — resume state

**Branch** `Stc2ObcSIF`, HEAD `377ab66`.
137 commits since `constraint_gen`. **Build green, zero admits.**

Companion docs: `Stc2ObcSIF_plan.md` (design), `Stc2ObcSIF_progress.md`
(worklist + design notes), `Stc2ObcSIF_tccall.md` (the call case).

---

## 0. Build workflow (mandatory)

Compile **only** inside the docker container `funny_franklin`. `/workspace`
is a copy — edit locally, then `docker cp` the file in.

```
docker cp src/SIF/F.v funny_franklin:/workspace/src/SIF/F.v
docker exec funny_franklin bash -lc 'cd /workspace && bash /tmp/coqc_cmd.sh src/SIF/F.v'
docker exec funny_franklin bash -lc 'cd /workspace && make -j8 >/dev/null 2>&1; echo $?'
```

- `make <path>.vo` is **not** a valid target — the Makefile defines no
  per-file rule, so it exits 0 having done nothing.  Treat any such run as
  no evidence at all.  Only bare `make` / `make -j4` builds.
- Re-run `./configure -clightgen x86_64-linux` whenever `vfiles` changes —
  adding a file *or* reordering one.  `_CoqProject` is generated from
  `vfiles` and is gitignored, so hand-edits are not picked up.  (An earlier
  note here said never to re-run configure; that is wrong, and following it
  makes new files silently fail to build.)
- "inconsistent assumptions over library X" after editing X just means
  dependents are stale: run `make` to rebuild them, then recompile.
- A new file only compiles once it is listed in `vfiles`.
- Commit messages: plain, no AI attribution.

---

## 1. What the goal is

`Signature_consistent Gstc Gobc` for the Stc→Obc translation, mirroring
the NLustre→Stc chain. **Hard constraint:** do not change NLustre→Stc
*top-level* theorem statements.

Verified unchanged against base `997438d`:
`Signature_consistent_cons`, `generated_signature_consistent_step`,
`generate_all_signatures_consistent'_abstract`,
`generate_all_signatures_consistent_scoped'`.

Four *intermediate* NL→Stc statements did change, all forced by the
shared-naming refactor (§2): `eqns_reset_extras_nodup` (qualifier only),
`generated_reset_env_maps_reset_calls`, `generated_eqns_reset_extras`,
`node_preserv_scoped` (hypothesis weakened), and
`generated_signatures_preserved_from_simplify_bridge_local_env` (one
hypothesis added, parallel to the `get_node_aux` one it already had).

---

## 2. The central design decision: one instance environment

STC used to mint reset-instance names from `resets_of s_tcs`; Obc minted
state names from `c_objs`. Different key lists ⇒ **different identifiers
for the same instance**, which made `tcreset_preserv`'s hypothesis
`Env.find s reset_env = Env.find s state_env` unsatisfiable for the real
generators.

Fixed by extending `NameGen`, exactly as clock/reset types already were:

- `node_aux_names` gained `ninst : Env.t ident`, read back by
  `get_node_inst`; minted by `fresh_inst_map_list` over
  `gather_insts n.(n_eqs)`, with the `sec_reset` prefix.
- `generate_sys_signature` and `generate_class_signature` both read it;
  neither calls `generate_reset_env` / `generate_state_env` any more.
- In the bridge, `state_env` was collapsed into `reset_env` — there is
  now one section variable and no equality hypothesis anywhere.

**Consequence to remember:** the two languages hide *different* sets and
that is correct. `simplify_scoped` needs every hidden name to have a
defining constraint; STC only constrains instances it resets, Obc's reset
method defines every instance. So STC hides `resets_of s_tcs`, Obc hides
all of `c_objs`.

---

## 3. What is proved

### Shared combinators (`SecTypes.v`)
- `preserves_on_incl` (1287) — cut a result down to a sublist of the target.
- `preserves_on_collapse` (1306) — move onto the collapsed target.
- `preserves_on_simplify_bridge` (1324) — **item 8**. Generic; the two
  sides may hide unrelated name sets.
- `preserves_on_app_scope_entailed`, `preserves_on_concat_list`,
  `preserves_on_Permutation`, `constraints_src_le_satisfaction`.

### STC side
- `generate_sys_signature_good` (`SecStcTypingCorrectness.v:748`) — **item C**,
  fully discharged. Its reset-uniqueness side condition is derived from
  `Is_well_sch` via `Is_well_sch_resets_nodup` (`StcWellDefined.Reset_not_Reset_in`:
  a `TcReset` is a sub at index 0, so nothing later can reset the same
  instance).
- `generate_trconstrs_constraints_{blocks,targets,wf,last_source,reset_source}`,
  `trconstrs_targets_perm`, `Reset_in_resets_of`, `resets_of_Reset_in`,
  `trconstrs_reset_keys_{cases,in_resets}`, `In_resets_of`.

### Bridge (`SecStcObcTranslation.v`)
- Per-trconstr: `tcdef_preserv`, `tcnext_preserv`, `tcreset_preserv`,
  and three call forms — `tccall_reset_preserv_eq` (equal actuals),
  `tccall_unreset_preserv_rst` (head kept), `preserves_on_reset_only_extra`
  (call with no outputs).
- `tc_preserv_aug` (1657) / `tcs_preserv_aug` (1790) — blocks own the
  reset-method constraint of the instance they name, via `zip_app`.
- Reset method: `generate_translate_reset_blocks`, `reset_mems_targets`,
  `reset_insts_targets`, `reset_targets_satisfied`,
  `preserves_on_app_reset_shared`.
- Extras: `tc_obc_extras` / `tcs_obc_extras`, `tcs_obc_extras_concat`,
  `tcs_obc_extras_nodup` (1604), `unreset_call_insts`.
- Scope: `raw_scope` (2144) = `inp ++ out ++ locals ++ lasts ++ rids ++
  [clk; rst]`, `rst_ty_in_raw_scope`, `sig_scope_in_raw_scope`,
  `extras_fresh_raw_scope` (2190).
- **`class_preserv_raw` (2247)** — item 7's raw theorem.
- **`class_preserv_signature` (2306)** — item 7 + 8 composed.

---

## 4. Status: signature preservation is complete

The whole chain is proved, admit-free, and ends in a public lookup
theorem.  The *chain skeleton* matches `SecNLusStcTranslation.v` item for
item -- the table below is exact, statement and often proof.  The
call-preservation rules underneath it are now literally shared with the
NLustre chain; see §4b.

| NLustre-Stc                                                | Stc-Obc                                              |
|------------------------------------------------------------|------------------------------------------------------|
| `generated_signatures_preserved_from_simplify_bridge_scoped` | `generated_signatures_preserved_obc`                 |
| `Signature_consistent_cons`                                  | `Signature_consistent_obc_full_cons`                 |
| `generated_signature_consistent_step`                        | `generated_signature_consistent_step`                |
| `generated_signature_step_consistent_from_bridges`           | `generated_signature_step_consistent_obc_from_bridges` |
| `generate_all_signatures_consistent'_abstract`               | `generate_all_signatures_consistent_obc'_abstract`   |
| `generate_all_signatures_consistent_abstract`                | `generate_all_signatures_consistent_obc_abstract`    |
| `generate_all_signatures_consistent_scoped'`                 | `generate_all_signatures_consistent_obc_scoped'`     |
| `generate_all_signatures_consistent_scoped`                  | `generate_all_signatures_consistent_obc_scoped`      |
| `generate_all_signatures_consistent`                         | `generate_all_signatures_consistent_obc`             |
| `generated_program_signatures_preserved_global`              | `generated_program_signatures_preserved_obc_global`  |

The scoped induction takes **no** step predicate.  An earlier
`generated_signature_step_consistent_obc_scoped` assumed
`Signature_consistent_obc_full G1 G2` for arbitrary `G1 G2` — the very thing
the induction has to establish — and has been deleted.  Consistency,
`secglobal_scoped` on both sides, `secglobal_scope_sec` on both sides, and
`secglobal_scope_bounded_above` on the STC accumulator are carried as
invariants and re-established per system, exactly as NLustre does.

Both Stc-side conditions of `generated_signatures_preserved_obc` are
discharged, mirroring NLustre:

| NLustre                                          | Stc                                              |
|--------------------------------------------------|--------------------------------------------------|
| `generated_node_simplify_ready_from_generated_env` | `generated_sys_simplify_ready_from_generated_env` |
| `generated_node_simplify_ready_from_local_env`     | `generated_sys_simplify_ready_from_local_env`     |
| `node_scope_fresh_in_env_from_bounds`              | `sys_scope_fresh_in_env_from_bounds`              |

### 4a. The naming bundle

`NAMEGEN.naming_env_props env aux_names` bundles the five facts every
consumer needs: `env_injective env`, the `sec` range of `env`, the `sec`
range of the auxiliary clock/reset names, injectivity plus the `sec_reset`
range of each instance environment, and `aux_clk_rst_distinct`.  It has two
constructors, `naming_env_props_from_generated_env` (flat whole-program
environment) and `naming_env_props_from_local_env` (a node's own environment
plus the scoped run that produced the auxiliary list), so a single proof
serves both settings.  `generate_sys_signature_good`,
`generate_sys_signature_scope_nodup`, `generated_sys_simplify_ready` and
`generated_signatures_preserved_obc` all take the bundle rather than a
`generate_node_env` equation.

Clock/reset distinctness is *derived*, never assumed:
`generate_local_env_for_node_clk_rst_distinct` reads it off the two
consecutive `fresh_ident_gen` calls (`st` vs `Pos.succ st`), and
`generate_node_scoped_env'_clk_rst_distinct` accumulates it over the scoped
run.

### 4b. Layer differences, all real rather than incidental

- **The Obc bridge carries three call/consistency notions, not one.**
  `Signature_call_preserves_obc_{eq,rst}` are the two shared rules;
  `_obc_full` is their conjunction, and only it reaches
  `Signature_head_consistent_obc` and the exported chain.  NLustre needs
  one two-conjunct definition because both its calls pass the same reset
  actual; the Obc side splits them because a call to an instance the
  system never resets passes `rst_ty` on the STC side and the instance's
  state type on the Obc side.  (`Signature_consistent_obc_eq` is a local
  intermediate.)  An earlier fourth notion built on a weaker rule, with
  its own per-trconstr correspondence, was superseded by `tc_preserv_aug`
  and has been deleted.

- **The two call rules are shared, and live in `SIGNATURE_PROOFS`.**
  `call_preserves_eq` and `call_preserves_rst` (`SIFSignature.v`) are
  stated at the general actuals -- `inp_le inptyp1 inptyp2`, since an Obc
  argument's type is the type of the *translated* expression and need
  only be contained in the STC one; the NLustre-to-Stc case is the
  instance where the two coincide.  `Signature_call_preserves_obc_eq` and
  `_obc_rst` *are* those definitions, and their `..._from_good` producers
  are one-line delegations to `call_preserves_{eq,rst}_from_good`.
  `SecNLusStcTranslation.Signature_call_preserves` keeps its own copy
  deliberately: the NL-Stc side is not to be changed (§6).

  Neither rule takes a freshness hypothesis on the *target* signature for
  actuals the two calls share: those transfer from the source through
  `signature_fields_agree_scope_eq`, which is what
  `call_preserves_rst_from_good` does inline.  Only the reset actual of
  `call_preserves_rst`, the one actual the two calls do not share, needs
  `type_fresh (sig_scope n2) [sty]`.  Do not add a target-side hypothesis
  to `call_preserves_eq`: there is no actual there that differs.

- `generated_signatures_preserved_obc` carries `Is_well_sch`, which NLustre
  needs no counterpart for.  Two `TcReset`s for one instance would put the
  same target on two constraints, breaking `wf_constraints`.
- `sys_scope_fresh_in_env_from_bounds` cannot run the index-bound argument on
  the reset instances: they are `sec_reset` gensyms, not `sec` ones, so
  `scope_lower_bounded` does not apply.  They are excluded from any signature
  scope by prefix instead (`sec_reset_not_in_signature_scope`), which is why
  the lemma also takes `secglobal_scope_sec G`.
- The naming environment is generated from NLustre nodes.  NLustre's bridge
  can write `translate nodes`; this one must not depend on the NLustre-to-Stc
  translation, so the scoped theorems relate the two lists by
  `Forall2 (fun n s => s.(s_name) = n.(n_name)) nodes systems`.  Names are
  preserved by that translation, so this is exactly what `translate` gives.
- The Obc accumulator's `secglobal_scope_sec` comes from the STC one through
  `signature_fields_agree_scope_eq`: the two signatures have the same scope.

### 4c. The chain layer

`SecNLusStcObcEnv.v` (`vfiles` after `SecStcObcTranslation.v`) threads the
environment facts and nothing else.  It follows the convention
`SecStcNonInterference` set: take the `CE`, `NL`, `Stc` bundles plus the
upstream bridge as a *parameter*, not a flat list of module arguments.
Only `OBCSYNTAX` is taken on the Obc side -- no Obc semantics or typing.

It exports `scoped_envs_windowed_from_scoped_env` (the naming run, walked
once), `translate_names` / `schedule_names` / `scheduled_translate_names`
(alignment before and after scheduling, `schedule_names` built on Velus's
own `Scheduler.schedule_system_name`), and
`generated_program_signatures_preserved_obc_{chain,scheduled}`.

Two module gotchas cost time here:

- `STCSCHEDULE` takes a 17th parameter (`EXT_STCSCHEDULER`).  Passing 16
  yields a *functor type*, not a module, so `Sched.schedule` will not
  resolve.  This is why `NLCorrectness.v:58` writes
  `Stc.Scheduler ExternalSchedule`.  Take `ExtSch` and `Sched` separately.
- `schedule_system` builds a record with `s_name := b.(s_name)`, so `simpl`
  reduces the projection and `auto` closes the goal before a
  `rewrite schedule_system_name` can fire.  Use
  `first [now rewrite Sched.schedule_system_name | exact Hname]`.

### 4d. B4 -- scheduling equivalence.  DONE

The compiler does **not** hand `translate all_nodes` to the Obc pass.
`NLCorrectness.nl_to_cl` is
`NL2Stc.translate` -> `schedule_program` -> `Stc2Obc.translate`, so the SIF
STC signatures the NL-Stc bridge produces are not the ones the Stc-Obc
bridge consumes, and the two had to be related.  This was the plan doc's
B4 option (b); option (a) -- proving `simplify` itself permutation-stable
-- stays rejected, because `simplify` eliminates hidden names in list
order and the results then agree only up to equivalence.

Constraint generation mints no identifier, so reordering `s_tcs` permutes
the raw constraints *with identical names*: no renaming or
alpha-equivalence argument anywhere.

**The layer, bottom to top.**

| where | what |
|---|---|
| `SecContext.v` | `state_pure` + `_ret/_error/_bind/_mmap/_option_to_sec/_find_env/_det` |
| `SIFSignature.v` | `state_pure_generate_constraints` and the four `subst_*` steps |
| `SecSTCTyping.v` | `state_pure_generate_trconstr(s)_constraints`, `tc_constraints`, `generate_trconstrs_constraints_{eq,Permutation,Permutation_ok}`, `Permutation_List_concat`, `tc_generates` + `..._ok_elems` / `..._ok_from_elems`, `wc_trconstr_call_actuals_scoped`, `sys_raw_scope` + `sys_raw_scope_facts`, `In_trconstrs_reset_keys_call` |
| `SecStcTypingCorrectness.v` | `sig_env_preserved` (+`_nil`/`_cons`), `call_actuals_in_scope(_from_wc)`, `generate_trconstr(s)_constraint(s)_preserved`, `resets_of_Permutation` / `resets_nodup_Permutation`, `generated_sys_signature_name`, `sys_reordered`, `generate_sys_signature_reorder_preserved`, `generate_all_sys_signatures_reorder_preserved_scoped(')` |
| `SecNLusStcObcEnv.v` | `schedule_reordered`, `scheduled_resets_nodup`, **`generated_signatures_preserved_by_scheduling`** |

**Two things worth remembering about the shape of the argument.**

- The two runs never compare permuted lists directly.  The target run is
  first moved back onto the *source's* body order --
  `generate_trconstrs_constraints_Permutation_ok`, which needs success to
  transfer across the reordering, hence `tc_generates` -- compared chunk
  for chunk there by `preserves_on_concat_scoped` with every `extras`
  empty, and only then permuted into place by `preserves_on_Permutation`.
- `preserves_on_simplify_bridge` runs at the *raw* scope
  `inp ++ out ++ locals ++ lasts ++ rids ++ [clk; rst]`, not the signature
  scope, because the chunkwise comparison needs the hidden names too.
  That is exactly the list `sys_scope_fresh_in_env` is stated over, which
  is why no new freshness premise appeared.

**The premise that had to change.**  `Is_well_sch` was a premise of
`generate_sys_signature_good` and of `generated_sys_simplify_ready`, and
B4 needs both of those for the **unscheduled** program -- which is
well-scheduled nowhere; that is the whole reason the scheduler pass
exists.  Both only ever used it through `Is_well_sch_resets_nodup`, so
both now ask for `NoDup (map fst (resets_of s_tcs))` directly.  That is a
property of the *multiset* of transition constraints, so it comes back
from the scheduled program across the permutation
(`resets_nodup_Permutation`); `Is_well_sch` does not.  Consumers on the
Obc side still hold `Is_well_sch` and insert `Is_well_sch_resets_nodup`
at the call.

Coq gotchas hit while proving the above: `eq_refl` resolves to the
`Lattice`'s -- write `Logic.eq_refl`; `state_pure_mmap` cannot infer its
implicit `A`, so apply it to the explicit function;
`signatures_preserved_equal_calls_from_good` lives in `SIGPROOFS`
(unqualified) while `call_subst_fresh_from_scope_fresh` lives in `SIG`;
`map` resolves to the *stream* map in `SecNLusStcObcEnv.v`, so write
`List.map`; `constraints_scoped` is two `Definition` hops from `Forall`,
so `rewrite Forall_app` will not fire on it but `apply Forall_app in`
will; and `edestruct H` puts the main goal *after* `H`'s side conditions,
not before.

### 4e. Phase 6 -- the NI transport.  DONE

`SecObcNonInterference.v` follows `SecStcNonInterference.v` item for item,
with the correspondence below.  Like it, it is a *transport*: the
imperative semantics is never attacked directly.  Note that one Stc
conversion lemma becomes two here, the input and output directions no
longer being symmetric.

| Stc | Obc |
|---|---|
| `tuple_stream_low_eq` | `obc_stream_low_eq` |
| `translated_system_behavior` | `translated_class_behavior` |
| (behaviour built from `correctness_loop`) | `translated_class_behavior_from_system` |
| `history_low_eq_of_tuple_stream_low_eq` | `obc_stream_low_eq_of_tuple_stream_low_eq` (outputs) and `tuple_stream_low_eq_of_obc_stream_low_eq` (inputs) |
| `system_security` | `class_security` |
| `system_security_from_node_security` | `class_security_from_node_security` |
| `translated_system_noninterference_outputs` | `class_noninterference_outputs` |

Three things about the shape are worth keeping.

- **The two stream correspondences are not symmetric.**  Outputs are exact
  -- `outs` is the pointwise image of `yss` under `value_to_option` -- so
  low-equivalence crosses them in both directions.  Inputs are not:
  `eq_if_present absent o` holds for *every* `o`, so an Obc input slot
  whose dataflow value is absent carries no information at all.
  Recovering the dataflow-level hypothesis therefore needs
  `same_low_presence`: the two runs agree on which of their *low* inputs
  are present.

  This is **not** an extra demand on the program, and not new to this
  layer.  NLustre and Stc streams carry `value`, so `env_low_eq`'s
  `Env.find x R = Env.find x R'` and `tuple_stream_low_eq`'s `v = v'`
  already force low positions to agree on presence: the requirement sits
  *inside* the low-equivalence relation there rather than beside it.  Obc
  streams carry `option val`, `eq_if_present` discards absence, and so the
  same content has to be written down separately.  It is guarded by
  `low_var` for exactly that reason -- quantifying over all positions
  instead would be strictly stronger than what the layers above assume.
- **`class_security` is indexed by the system, not by the class.**  A class
  does not determine its system: `schedule_tcs` is not injective, so two
  differently-ordered bodies translate to the same class.  Every signature
  lookup in it is nevertheless the class's own, names being preserved.  It
  records the two chain facts B4 and phase 4 supply: `signatures_preserved`
  from the unscheduled accumulator to the scheduled one, and
  `Signature_head_consistent_obc` out of the latter.
- **The conclusion is read off the emitted class's own `step` method**
  (`translated_class_step_interface`), `translate_system` taking
  `m_in := idty s_in` and `schedule_system` copying it.

There is no composed NLustre-to-Obc *signature* theorem, and none is
needed: exactly as `system_security` carries the source witness and
`Signature_head_consistent` side by side rather than composing them,
`class_security` carries all three legs side by side.  Composing them
would need transitivity of `Signature_head_consistent_obc`, whose premises
mention `call_subst_fresh` of the *middle* signature -- not available from
the two ends.  Do not try to strengthen this.

Note also that nothing yet *applies* these functors to concrete arguments;
there is no concrete `Lattice` and that is deliberate -- the proofs are for
an arbitrary lattice, and a user extracts constraints from the pipeline and
checks them against whatever concrete lattice they want.

## 5. Gotchas worth keeping

- `simpl` unfolds `merge` into fix-form; use `cbn [hm_ext]`,
  `cbn [get_mappings]`, `change` to a folded form instead.
- Name shadowing: `eq_refl`/`eq_sym`/`eq_trans` (Lattice) need `Logic.`;
  `Var`/`State`/`Call`/`AssignSt` need `SynObc.`; `concat` is
  `String.concat` where `String` is imported — write `List.concat`.
- `Lat.order_refl : forall x y, eq x y -> order x y` — it needs an `eq`
  witness, so `apply Lat.order_refl, Lat.eq_refl`.
- `destruct … eqn:H` rewrites the scrutinee in *other hypotheses* too;
  a `forall … find_signature f G1 = Some n1 → …` hypothesis becomes
  `Some n1 = Some n1`, so pass `Logic.eq_refl`.
- Adding a monadic bind to a generator breaks every `name_bind_inv`
  chain that inverts it — patch each inversion site, and watch for
  lemmas whose state bounds shift (`env_sec_bounded_le`).


---

## 6. Open items

None of these affect what is proved.

- **`Signature_call_preserves` (NL) stays as it is.  Decided, do not
  revisit.**  It is `SecNLusStcTranslation.v:89`, its own conjunction of
  two rules that are the special case of `call_preserves_{eq,rst}` at
  equal actuals, plus a target-side `call_subst_fresh` that its own
  producer (`signatures_preserved_equal_calls_from_good`) never uses.
  Replacing it with `call_preserves_eq n1 n2 /\ call_preserves_rst n1 n2`
  would give the two bridges one definition -- but it would strengthen
  `Signature_head_consistent` and hence `Signature_consistent`, whose
  statements §1 records as verified unchanged against base `997438d`.
  The theorem *text* would not move but its meaning would.  The NL-Stc
  side is not to be changed; the sharing is one-directional by design,
  the Obc bridge reading the general rule and NLustre keeping its
  instance of it.

Nothing outstanding.

## 7. Evidence the chain is not vacuous

Every top-level theorem is conditioned on `generate_... = OK G`; there
are no totality lemmas, exactly as for Velus's own passes.  So vacuity is
ruled out empirically:

```
velus -dsif <file>.lus     ->  <file>.{n,s,o}.sif
```

`.s.sif` is of the *unscheduled* Stc program -- the one the
NLustre-to-Stc bridge proves about -- while `.o.sif` is of
`Stc2Obc.translate` of the *scheduled* one, which is what the compiler
emits; `velusmain.ml` hands `generate_obc_constraint_dump` the output of
`NLCorrectness.schedule_program`.  Each dump therefore sits at the point
its own theorem is stated, and B4 relates them.  (Threading the schedule
through changed 32 of the 42 dumps -- by constraint *order* only, the
sets and the simplified signatures being unaffected, exactly as B4
predicts.)

Over all 42 of `tests/ok_*.lus` that compile, the Stc and Obc
*simplified* constraint sets are **identical** in every case (compare the
constraint lines as sets -- comparing the text from `simplified
constraints:` to end of file is wrong, it swallows the next system's
section).  The theorem only claims `preserves_on`, so equality is
stronger than what is proved, and it is what the generator actually does.

A worked example (`tests/ok_alias.lus`, class `wrong`) showing the Obc
extras and `collapse` doing their job:

```
Stc  raw:        [sec$13, sec$14] <= [sec$18]
Obc  raw:        [sec$13, sec_reset$1] <= [sec$18]
                 [sec$14] <= [sec_reset$1]        <- reset method
Obc  collapsed:  both, reordered
both simplified: [sec$13, sec$14] <= [sec$18]
```
