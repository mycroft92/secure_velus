# Stc→Obc SIF preservation — resume state

**Branch** `Stc2ObcSIF`, HEAD `0553c47`, pushed to `origin`.
58 commits since `constraint_gen`. **Build green, zero admits.**

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

- **Never re-run `./configure`** — it clobbers `Archi.vo` and yields bogus
  "inconsistent assumptions" errors.
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

## 4. What remains

### 4a. The one open obligation (next thing to do)

`class_preserv_raw` takes a per-block target-scopedness hypothesis:

```coq
Forall2 (fun tc e =>
  forall blk sa sb,
    generate_stmt_constraints G2 env reset_env rst_ty [clk_ty]
      (translate_tc memset clkvars tc) sa = OK (blk, sb) ->
    constraints_scoped (rawscope ++ e)
      (blk ++ map (fun ty => ([rst_ty], [ty])) e))
  tcs extras
```

`SecObcTyping.generate_stmt_constraints_scoped_on_keys` discharges it,
and all its premises are available except one:

```coq
names_scoped env (raw_scope …) (stmt_free (translate_tc memset clkvars tc))
```

— the free names of a *translated* trconstr map into the scope. This is
new content, not plumbing: NL→Stc has no analogue because it does not
recompile expressions, whereas `translate_tc` compiles clocks to `Ifte`
via `Control` and expressions via `translate_exp`. Estimate 60–100 lines.
Route: induct on `Control`/`translate_cexp`, relating `stmt_free` of the
translation to `Is_free_in_tc` of the source, then use the STC-side
`vars_env_scoped` facts already used by
`generate_trconstr_constraint_scoped_on_keys`.

The other hypotheses are available: `wf_constraints nconst` from
`generate_trconstrs_constraints_wf` + `targets_nodup`; `hidden_stc`
disjointness from `generated_sys_hidden_disjoint`; scope inclusion from
`sig_scope_in_raw_scope`; `NoDup`/freshness of extras from
`tcs_obc_extras_nodup` / `extras_fresh_raw_scope`.

### 4b. Items 9–10 — the lockstep

Port `generated_signature_consistent_step` /
`generate_all_signatures_consistent'_abstract` from
`SecNLusStcTranslation.v` (`:2315`, `:2326`). Mechanical. This is where
`generate_sys_signature_good` and
`signatures_preserved_obc_full_from_good` get consumed to build
`Signature_consistent_obc_full` for the callee pairs.

### 4c. Later phases (out of scope for preservation)

Scheduling equivalence (B4) and the NI transport.

---

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
