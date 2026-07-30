# SIF for Obc: security type system and Stc→Obc preservation plan

Branch: `Stc2ObcSIF`. Status: analysis/plan (no code yet).

Goal: a security (SIF) type system for Obc living in `src/SIF`, plus a
constraint/signature preservation proof along the Stc→Obc translation,
following the same route as the NLustre→STC chain
(`SecSTCTyping.v` / `SecNLusStcTranslation.v` / `SecStcNonInterference.v`).

**Terminology note.** `src/StcToObc/Stc2ObcTyping.v` is a *different entity*:
it is about ordinary data types (`wt_exp` / `wt_stmt` / `wt_program` from
`Obc/ObcTyping.v`), not security types. In this document, "typing" without
qualification means the SIF *security* typing (symbolic types `ST`,
constraints, signatures). The ordinary Obc typing judgment is used by us only
as *scoping infrastructure* (its `In (x,ty) vars/mems` premises bound the free
variables of expressions/statements), playing the role that `wc_trconstr`
played in the STC scopedness proofs. Nothing from `Stc2ObcTyping.v` is part of
the security type system itself.

---

## 1. What the translation produces (read from `StcToObc/Translation.v`)

`translate_system` maps an STC system `s` to a class:

- `c_mems := s_lasts` (state variables, names preserved)
- `c_objs := s_subs` (instance, class) pairs, names preserved
- exactly **two methods**:
  - `step`: `m_in/m_vars/m_out = s_in/s_vars/s_out`, body `translate_tcs s_tcs`
  - `reset`: no args, body `reset_mems s_lasts ; reset_insts s_subs`

Per trconstr:

| STC | Obc |
|---|---|
| `TcDef x ck ce` | `Control ck (translate_cexp x ce)` — nested `Ifte`s, `Assign` at leaves |
| `TcNext x ck e` | `Control ck (AssignSt x e')` |
| `TcCall s xs ck rst f es` | `Control ck (Call xs f s step es')` |
| `TcReset s ck f` | `Control ck (Call [] f s reset [])` |

`Control ck s` compiles the clock into `Ifte (bool_var x) s Skip` nests, i.e.
every dataflow clock becomes imperative control flow. `translate_tcs` is a
`fold_left Comp` in *reverse* execution order (irrelevant for constraint sets,
relevant when destructing statement structure).

## 2. Key observation: STC clock types are already pc labels

Every STC constraint LHS joins in `[rst_ty] ⊔ (base_ty-seeded clock type)`.
In the translated Obc code, that same variable set reappears as the branch
conditions guarding the statement. So the Obc security system is a classic
**pc-carrying constraint generator** over statements:

```
gen_stmt (pc : ST) : stmt -> Sec (list constraint)
  Assign x e           => [(pc ⊔ ty(e), [τ(x)])]
  AssignSt x e         => [(pc ⊔ ty(e), [τ(x)])]     (* mems share the env; names preserved *)
  Ifte e s1 s2         => gen_stmt (pc ⊔ ty(e)) s1 ++ gen_stmt (pc ⊔ ty(e)) s2
  Comp s1 s2           => gen_stmt pc s1 ++ gen_stmt pc s2
  Skip                 => []
  Call ys c o step es  => generate_constraints (sig c) (map ty es) pc [state_ty o] (map τ ys)
  Call [] c o reset [] => [(pc, [state_ty o])]
```

- `ty(e)`: an Obc mirror of `assign_exp_type` (`Var`/`Valid`/`State` → env
  lookup, `Const` → `[]`, unop/binop → join).
- `state_ty o`: per-instance state security type from a generated environment —
  the exact analogue of `generate_reset_env`/`rids` in `SecSTCTyping.v`
  (STC's `reset_env` is keyed by the same instance idents).

**Class signature: reuse `SIG.signature` verbatim** (third reuse of
`SIFSignature.v`). For `translate_system s`:

- `s_in`/`s_out` from step's input/output types, `s_clk` = step entry pc seed,
  `s_reset` = reset dependence;
- constraints = `simplify (collapse (gen_stmt ([s_reset] ⊔ [s_clk]) step_body
  ++ reset_method_constraints)) (locals ++ lasts ++ state_tys)`.

Step body generated with entry pc `[rst_ty] ⊔ [base_ty]` reproduces the
`[rst_ty] ⊔ ckty` prefix of every STC constraint.

**Why the 2026-07-14 change (commit 997438d) matters here.** The pc at a
translated reset call `Control (Con ckr r true) (Call [] f o reset [])` is
`[rst_ty] ⊔ [base_ty] ⊔ clkvars(ckr) ⊔ [τ(r)]` — exactly the new `TcReset`
rule (`[rst_ty] ⊔ ([rty] ⊔ base_ty-seeded rstckty)`). Under the old
(rst-seeded, no `base_ty`) rule the STC reset constraint would not match the
pc semantics of the imperative code, and this bridge would have needed the
"reset-implies-clk in LHS through simplify" generalization we avoided. The
generators are now pc-consistent by construction.

## 3. Blockers and design decisions (ranked)

None is mathematically fatal; the classic imperative problem (implicit flows)
is already paid for by clock types.

- **B1 — Multiple constraints per target (real design decision).**
  `translate_cexp x (Emerge y t f)` yields two `Assign x` leaves ⇒ two
  constraints for `τ(x)`, each with a smaller LHS than STC's single
  `([rst] ⊔ ck) ⊔ cexpty` (Obc is strictly more precise). But
  `simplify`/`findST`/`wf_constraints`/shape lemmas assume one constraint per
  hidden target; `findST` returns the first match, so hidden-var elimination
  with duplicate targets silently drops flows.
  *Decision:* (a) add a `collapse` pass joining LHSs per target before
  `simplify` — makes the Obc signature pointwise equal to the STC one, bridge
  nearly free (**recommended**); or (b) keep per-leaf precision and generalize
  `simplify` — much more work for precision the end-to-end theorem cannot use
  (it is bounded by the NLustre-level signature anyway).

- **B2 — Flow-insensitivity vs re-assignment.** `gen_stmt` unions constraints
  over `Comp`; sound for any program, but shape/NoDup lemmas need
  single-assignment method bodies. Translated bodies satisfy this
  (`s_nodup_defined` / `Is_well_sch`); state it as a precondition, as STC
  lemmas assume `NoDup (defined tcs)`. Hand-written Obc: imprecise, not
  unsound. Non-blocker for the compiler chain.

- **B3 — ACI alignment of pc joins (proof engineering).** `Control` nests
  conditions outside-in; `assign_clk_type` folds the clock inside-out. Leaf pc
  equals the STC clock type only up to `merge` assoc/comm (`MergeFacts`).
  Prove once: `gen_stmt pc (Control ck s) = gen_stmt (pc ⊔ clkty(ck)) s`
  (ST-equality via merge ACI); then each per-tc bridge case discharges
  reflexivity-style like `eqn_preserv`.

- **B4 — Scheduling sits between SIF-STC and Obc (largest new obligation).**
  `correctness_loop_call` (the semantic transport) requires `Well_defined P`,
  i.e. the *scheduled* program; all SIF STC signatures are generated from the
  unscheduled `Translation.translate all_nodes`. `StcSchedule` permutes
  `s_tcs`; raw constraints permute (per-tc concatenation), satisfaction is
  permutation-invariant, but `simplify` output is order-sensitive
  syntactically. Need: "signatures of a system and its scheduled permutation
  are `preserves_on`-equivalent" (or generate Obc signatures from the
  scheduled program and bridge STC ↔ scheduled-STC first).

- **B5 — Reset method's non-local writes.** `reset_insts` calls `reset` on
  every child ⇒ constraints `(pc, [state_ty child])`, whereas at STC level
  whole-system reset is implicit (modeled by `rst_ty` as an input). All
  `state_ty` are hidden (like `rids`), so these constraints matter only via
  `simplify` substitution into step-call constraints — where STC's `rst_inst`
  machinery also lands. Expected to correspond; most likely place for a
  surprise, budget verification time.

- **B6 — Two methods, one signature.** Do not build per-method signature
  machinery: translated classes have exactly `step`/`reset` with fixed roles,
  so one class-level `SIG.signature` keeps `generate_constraints`,
  `Signature_consistent`, `preserves_on` unchanged. Consequence to flag:
  **the SIF Obc system covers `translate P` output, not arbitrary Obc** (in
  particular not post-`Fusion`/`ObcAddDefaults` code — those would need
  per-method signatures and revisiting B2).

- **B7 — Scoping without clocks.** STC scopedness lemmas leaned on
  `wc_trconstr`. Obc has no clocks; use ordinary typing `wt_stmt`/`wt_exp`
  (`Obc/ObcTyping.v`) purely for free-variable containment (`st_scoped`).
  `StcToObc/Stc2ObcTyping.v` proves translated programs well-typed in that
  ordinary sense — we *consume* that result; it is not part of the security
  system. Straightforward infrastructure substitution.

## 4. Proof plan (NLustre→STC pattern, transplanted)

New files in `src/SIF`, mirroring the existing layout:

1. **`SecObcTyping.v`** (mirror of `SecSTCTyping.v`): Obc `assign_exp_type`,
   `gen_stmt`, `generate_state_env` (≅ `generate_reset_env`), `collapse`,
   `generate_class_signature` (+ `_scoped_env` variant), scopedness + shape
   theorems using `wt_stmt`. *Largest new file; mostly transliteration.*
2. **`SecObcConstraintExport.v`**: exporter, mirrors
   `SecStcConstraintExport.v`. *Small.*
3. **`SecObcTypingCorrectness.v`**: `generate_class_signature_inv`,
   NoDup/scope-sec/goodness lemmas. *Mechanical, mirrors
   `SecStcTypingCorrectness.v`.*
4. **`SecStcObcTranslation.v`** (bridge, mirror of
   `SecNLusStcTranslation.v`): the `Control` pc-lemma (B3), per-tc
   correspondence `tc_preserv` (≅ `eqn_preserv`; `Call/step` case reuses the
   `Signature_call_preserves` shape, `TcReset` case aligns with
   `(pc, [state_ty])`), lockstep induction ⇒ `Signature_consistent Gstc Gobc`.
   With `collapse` (B1a) per-tc cases should discharge near-reflexivity after
   monadInv.
5. **Scheduling equivalence** (inside 4 or separate): permutation-stability of
   signature generation up to `preserves_on` (B4).
6. **`SecObcNonInterference.v`** (mirror of `SecStcNonInterference.v`):
   `class_security` (≅ `system_security`: STC witness +
   `Signature_head_consistent`), then transport the STC output-noninterference
   theorem to Obc behaviors through `correctness_loop_call`
   (`loop_call (translate P) f step ins outs 0 me0`), converting
   `tuple_stream_low_eq` to low-equivalence of the `ins`/`outs`
   option-val streams. Like the STC file, this is a *transport*, not a fresh
   NI proof — the imperative semantics is never attacked directly.

Order of attack: 1 → 3 → 4 (bridge on unscheduled programs first; isolates
the type-system correspondence) → 5 → 6; 2 whenever the exporter is wanted.

## 5. Immediate next steps

- [ ] Decide B1 (`collapse` — recommended) and B4 insertion point.
- [ ] Draft `SecObcTyping.v` definitions section (generator + signature);
      this forces B1/B3 to become concrete.
- [ ] Add new files to `_CoqProject` as they appear.
