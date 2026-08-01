# Stc→Obc SIF preservation — resume state

**Branch** `Stc2ObcSIF`, HEAD `f6e7645`.
119 commits since `constraint_gen`. **Build green, zero admits.**

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

The whole chain is proved, admit-free, and mirrors `SecNLusStcTranslation.v`
member for member, ending in a public lookup theorem:

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

### 4d. B4 -- scheduling equivalence.  IN PROGRESS

The compiler does **not** hand `translate all_nodes` to the Obc pass.
`NLCorrectness.nl_to_cl` is
`NL2Stc.translate` -> `schedule_program` -> `Stc2Obc.translate`, and
`Well_scheduled` holds only after that middle pass.  So the SIF STC
signatures the NL-Stc bridge produces (from `translate all_nodes`) are not
the ones the Stc-Obc bridge consumes (from `schedule (translate
all_nodes)`), and the two must be related.  This is the plan doc's B4
option (b).

**The risk is gone.**  Constraint generation mints no identifier --
`SecSTCTyping.v` and `SIFSignature.v` contain no `fresh_ident`/`gensym` on
that path, and `generated_sys_signature_scope_key` independently confirms
every scope element comes from `Env.find x env`.  So reordering `s_tcs`
permutes the raw constraints *with identical names*: no renaming or
alpha-equivalence argument is needed.  Option (a) -- proving `simplify`
itself permutation-stable -- remains rejected: `simplify` eliminates hidden
names in list order, and when one hidden name's definition mentions another
the results agree only up to equivalence, not syntactically.

**Done and admit-free:**

| where | what |
|---|---|
| `SecContext.v` | `state_pure` + `_ret/_error/_bind/_mmap/_option_to_sec/_find_env/_det` |
| `SIFSignature.v` | `state_pure_generate_constraints` and the four `subst_*` steps |
| `SecSTCTyping.v` | `state_pure_generate_trconstr(s)_constraints`, `tc_constraints`, `generate_trconstrs_constraints_eq`, `Permutation_List_concat`, `generate_trconstrs_constraints_Permutation` |
| `SecStcTypingCorrectness.v` | `generate_sys_signature_reorder_preserved` (fixed accumulator), `sig_env_preserved`, `call_actuals_in_scope`, `generate_trconstr_constraint_preserved` |

`generate_sys_signature_reorder_preserved` is short because
`preserves_on_simplify_bridge` already allows the two hidden-name lists to
be *unrelated* -- and they genuinely differ, since reset instances are
collected in body order.

**Remaining, in order.**  All against lemmas that exist; no open questions.

1. **Body combination.**  `preserves_on_concat_list` wants
   `Forall2 (preserves_on scope) srcs tgts` *pointwise in the same order*,
   so factor the permutation out first: generate both sides over the same
   `tcs`, combine, then move to scheduled order with
   `preserves_on_Permutation`.  Take `extras := map (fun _ => []) tcs` --
   there are no target-side-only names at Stc-Stc -- which makes its `NoDup`
   and freshness premises vacuous.  Its `Forall2 (fun t e =>
   constraints_scoped (scope ++ e) t)` premise is
   `generate_trconstr_constraint_scoped_on_keys` (`SecSTCTyping.v:735`) at
   `G := G'`, needing `secglobal_scoped G'`.
2. **Discharge `call_actuals_in_scope`.**  Do **not** re-derive it: the
   `TcCall` case of `generate_trconstr_constraint_scoped_on_keys`
   (`SecSTCTyping.v`, ~955-965) already builds exactly `Hckscope`,
   `HinpScope : Forall (st_scoped scope) inptyp` and
   `HoutScope : Forall (fun x => In x scope) outtyp` from `wc_trconstr` +
   `vars_env_scoped`.  Factor that block out as its own lemma and use it on
   both sides.
3. **Per-system lift.**  Reuses the `preserves_on_simplify_bridge` call
   already written in `generate_sys_signature_reorder_preserved`; only the
   raw-level premise changes from permutation to step 1's result.
4. **Program induction** maintaining `sig_env_preserved` pointwise.  Trivial
   in shape: `schedule = map schedule_system` never reorders the program, so
   the accumulators grow in lockstep and every `find_signature` matches.

Coq gotchas hit while proving the above: `eq_refl` resolves to the
`Lattice`'s -- write `Logic.eq_refl`; `state_pure_mmap` cannot infer its
implicit `A`, so apply it to the explicit function; and
`signatures_preserved_equal_calls_from_good` lives in `SIGPROOFS`
(unqualified) while `call_subst_fresh_from_scope_fresh` lives in `SIG`.

### 4e. Later phases

The NI transport (phase 6), ~370 lines mirroring `SecStcNonInterference.v`.
Also note nothing yet *applies* these functors to concrete arguments; there
is no concrete `Lattice` and that is deliberate -- the proofs are for an
arbitrary lattice, and a user extracts constraints from the pipeline and
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

## 6. Deferred cleanups (after all theorems are proved)

- **Naming.** The Stc-to-Obc bridge inherited `nsig`/`ssig` from the
  NLustre-to-STC chain, where they mean *NLustre* and *STC*.  Here they
  mean *STC* and *Obc*, which is actively misleading — `NoDup
  (signature_scope nsig)` reads as an NLustre fact but is an STC one.
  Rename to something layer-neutral (`src_sig`/`tgt_sig`) or explicit
  (`stcsig`/`obcsig`) once the proofs are closed, so the rename is a
  pure refactor with a green build either side.
- `get_mappings_nodup` still has section-scoped copies in
  `SecNLusTyping`/`SecSTCTyping` that should collapse onto
  `NameInterface.get_mappings_nodup_gen`.
- `nodup_singleton_map` exists both in `SIFSignature` (SIG) and in
  `SecNLusTyping`.
