# Stc→Obc SIF preservation — resume state

**Branch** `Stc2ObcSIF`, HEAD `fb936db`, pushed to `origin`.
72 commits since `constraint_gen`. **Build green, zero admits.**

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

### 4a. Item 2 — instantiate at the generated signatures (in progress)

All the individual obligations of `class_preserv_signature` are proved:
`rst_ty_in_raw_scope`, `sig_scope_in_raw_scope`, `tcs_obc_extras_exists`,
`tcs_obc_extras_nodup` (via `unreset_call_insts_nodup`),
`extras_fresh_raw_scope`, `translated_tc_constraints_scoped`,
`reset_mems_targets` / `reset_insts_targets`,
`generate_translate_reset_blocks` + `calls_of_reset_or_unreset`,
`generate_trconstrs_constraints_wf` + `targets_nodup`,
`generated_sys_hidden_disjoint`, and the component identification
(`translated_class_{step_in,step_out,step_vars,mems,objs}` with
`get_mappings_from_node_map_fst`).

**A redesign is needed first, and `tc_preserv_hyps_aug` is unsound as
written.** Its call cases read

```coq
| TcCall _ _ ck true f _ =>
    forall ckty n1 inptyp1 rinst outtyp,
      assign_clk_type env clk_ty ck = Some ckty ->
      find_signature f G1 = Some n1 ->
      scope_fresh scope n1
      /\ call_subst_scoped scope inptyp1 ckty [rinst] outtyp
      /\ call_subst_fresh n1 inptyp1 ckty [rinst] outtyp
```

`inptyp1`, `rinst` and `outtyp` are universally quantified with nothing
tying them to the call, yet `call_subst_scoped` requires them to be
scoped.  Nothing constrains them, so the predicate is **not
dischargeable** — not from `wc_system`, not from anything.  Step 3 as
originally planned cannot work against it.

**The correct shape is NL's.**  `eqn_preserv` takes no per-equation
predicate.  It takes `wc_equation`, `vars_env_scoped`,
`secglobal_scope_fresh`, `secglobal_scope_sec` and derives the call side
conditions *inside* its proof, after inverting the generator — at which
point the actuals are the real ones and the scopedness facts apply.

**Port plan.**

1. Delete `tc_preserv_hyps_aug`.  Give `tc_preserv_aug` the NL
   hypothesis set: `Signature_consistent_obc_full`,
   `secglobal_scope_fresh scope G1`, `secglobal_scope_sec G2`,
   `secglobal_scoped G2`, `wc_env vars`, `wc_trconstr P vars tc`,
   `vars_env_scoped env vars scope`, `In clk_ty scope`,
   `In rst_ty scope`, and the instance-type range/freshness facts.
2. Derive `call_side_conditions` in-proof, porting the two `EqApp`
   branches of `eqn_preserv` (roughly 100 lines each).  Ingredients, all
   already present: `assign_clk_type_scoped` (`SecCETyping.v`), the
   `mmap` scopedness lemmas used inside
   `generate_trconstr_constraint_scoped_on_keys` (`SecSTCTyping.v`),
   `call_subst_fresh_from_scope_fresh`,
   `call_subst_fresh_reset_from_scope_fresh`, `scope_fresh_fields_agree`
   (`SIFSignature.v`).
   - `[rinst] ⊆ scope` for a reset'd call: `reset_consistency` makes
     `rst = true` imply the instance is reset, so its type is in `rids`,
     which is inside `raw_scope`.
   - `¬ In sty scope` for an unreset call: `extras_fresh_raw_scope` via
     `tcs_obc_extras_concat`.
   - the callee-side `call_subst_fresh n2`: needs
     `signature_fields_agree n1 n2`, which is why
     `Signature_head_consistent_obc` was added (commit `fb936db`); the
     two signatures then share a scope.
3. Re-signature `tcs_preserv_aug`, `class_preserv_raw` and
   `class_preserv_signature` accordingly.
4. Then the assembly theorem, which inverts both signature generators,
   identifies components via `translated_class_*` and
   `get_mappings_from_node_map_fst`, sets `rawscope`, and discharges the
   remaining six obligations with the lemmas listed above.

The tree will be red for a stretch during step 1-3; commit only at green
points.

### 4a-bis. Items 1-3 are done (superseded checkpoint)

The port described above is complete and merged.  The earlier checkpoint
here blamed the `HoutScope` assert for the mid-port failure; that was
wrong — it was the `Hfr1` assert-`by`, where
`call_subst_fresh_from_scope_fresh`'s five premises had to be supplied
explicitly instead of via `eauto`.

What landed:

- `tccall_reset_preserv_eq` and `tccall_unreset_preserv_rst` both take
  the NLustre-Stc hypothesis set and **derive** `scope_fresh`,
  `call_subst_scoped` and `call_subst_fresh` from the real actuals after
  inverting the generator.  The callee side of the unreset case uses
  `call_subst_fresh_reset_from_scope_fresh`, since the instance state
  type is deliberately outside the scope and the plain version's
  `st_scoped scope [sty]` is false there.
- `tc_preserv_hyps_aug` is **deleted** — it had no content left.
- Specialising `rawscope` to `raw_scope` made three further hypotheses
  provable (`In rst_ty`, `In clk_ty`, and the reset-instance condition),
  via `rst_ty_in_raw_scope`, `clk_ty_in_raw_scope` and
  `reset_inst_in_raw_scope`.
- Item 3, `generated_signature_fields_agree`.

Recurring gotcha: `eauto` / `easy` after `eapply` is unreliable in this
file once the goal count shifts — name the arguments instead.  Two
scripted replaces also hit the wrong lemma because hypothesis prefixes
repeat; check `s.count` before replacing.

### 4b. Item 3 — `signature_fields_agree`

Both signatures read the same `env` and `aux_names`, so name, inputs,
outputs, clock and reset agree; the shape facts of item 2 give it.

### 4c. Item 4 — the lockstep

Port `generated_signature_consistent_step` /
`generate_all_signatures_consistent'_abstract` from
`SecNLusStcTranslation.v` (`:2315`, `:2326`).  Mechanical.  This is where
`generate_sys_signature_good` and
`signatures_preserved_obc_full_from_good` are consumed.

### 4d. Later phases (out of scope for preservation)

Scheduling equivalence (B4) and the NI transport.

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
