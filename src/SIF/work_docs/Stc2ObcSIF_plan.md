# SIF for Obc: security type system and Stc→Obc preservation plan

Branch: `Stc2ObcSIF`. **Status: implemented and compiling.** This file is the
original design note; §2 and the blocker list below have been corrected in
place where the implementation diverged from the plan. For live status see
`Stc2ObcSIF_progress.md`; for the call case see `Stc2ObcSIF_tccall.md`.

Goal: a security (SIF) type system for Obc living in `src/SIF`, plus a
constraint/signature preservation proof along the Stc→Obc translation,
following the same route as the NLustre→STC chain
(`SecSTCTyping.v` / `SecNLusStcTranslation.v` / `SecStcNonInterference.v`).

**Terminology note.** `src/StcToObc/Stc2ObcTyping.v` is a *different entity*:
it is about ordinary data types (`wt_exp` / `wt_stmt` / `wt_program` from
`Obc/ObcTyping.v`), not security types. In this document, "typing" without
qualification means the SIF *security* typing (symbolic types `ST`,
constraints, signatures).

The original plan was to use the ordinary Obc typing judgment as scoping
infrastructure. **That was dropped**: `OBCTYPING` is parameterised by
`OBCSEMANTICS`, so depending on it would drag the Obc *semantics* into a
purely syntactic constraint generator. `SecObcTyping.v` therefore depends on
`Obc.ObcSyntax` and nothing else from Obc, and scopedness is stated over the
syntactic free names `exp_free` / `stmt_free` / `names_scoped`. Nothing from
`Stc2ObcTyping.v` is part of, or used by, the security type system.

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
`fold_left Comp` in *reverse* execution order. The generated constraint list
is therefore the reverse-order concatenation of the per-trconstr blocks, while
the STC generator concatenates them in order: the two are **permutations**, not
equal. Satisfaction is a `Forall`, hence permutation-stable
(`listSatisfiable_Permutation` / `preserves_on_Permutation`), but the proof has
to say so explicitly.

## 2. Key observation: STC clock types are already pc labels

Every STC constraint source joins in `[rst_ty] ⊔ ckty`, where
`ckty = assign_clk_type env clk_ty ck` is the clock type seeded at `clk_ty`.
In the translated Obc code the *same* variables reappear as the branch
conditions guarding the statement, so the Obc system is a pc-carrying
constraint generator over statements.

**The rules as implemented** (`SecObcTyping.v`, section `SECSTMTTYPING`,
with section parameters `G` (callee signatures), `env` (names ↦ security
types, written `τ`), `state_env` (instances ↦ state types, written `σ`)
and `rst_ty`):

```
gen (pc : ST) : stmt -> Sec (list constraint)
  Skip                  ↦  []
  Assign   x e          ↦  [( ([rst_ty] ⊔ pc) ⊔ ty(e) , [τ x] )]
  AssignSt x e          ↦  [( ([rst_ty] ⊔ pc) ⊔ ty(e) , [τ x] )]
  Ifte e s₁ s₂          ↦  gen (pc ⊔ ty(e)) s₁  ++  gen (pc ⊔ ty(e)) s₂
  Comp s₁ s₂            ↦  gen pc s₁ ++ gen pc s₂
  Call [] c o reset _   ↦  [( [rst_ty] ⊔ pc , [σ o] )]
  Call ys c o step  es  ↦  generate_constraints (G c) (map ty es) pc [σ o] (map τ ys)
```

Note where `rst_ty` does and does **not** appear. It is added at the
*leaves* (assignments, reset calls); it is **not** folded into `pc`, so a
step call passes `pc` alone as the callee's clock actual. The earlier
draft of this document had `pc` already containing `rst_ty` and no
`[rst_ty] ⊔ …` at the leaves; that design leaked the reset dependence into
every callee's clock formal and was corrected on 2026-07-30 (see
`Stc2ObcSIF_tccall.md` §2).

- `ty(e)`: Obc expression types — `Var`/`State`/`Valid` ↦ env lookup,
  `Const` ↦ `[]`, unop ↦ recurse, binop ↦ join.
- `σ o`: per-instance state type from `generate_state_env`, the analogue of
  `generate_reset_env`/`rids` in `SecSTCTyping.v`.

**Class signature** (`generate_class_signature`), reusing `SIG.signature`
verbatim — the third reuse of `SIFSignature.v`. With `clk_ty`/`rst_ty` the
aux names of the class:

```
craw_step  = gen [clk_ty] (step  method body)      (* entry pc = [clk_ty] *)
craw_reset = gen []       (reset method body)      (* entry pc = []       *)
s_constraints = simplify (collapse (craw_step ++ craw_reset))
                         (hidden_class_vars locals lasts stids)
s_in = inp,  s_out = out,  s_clk = clk_ty,  s_reset = rst_ty
```

**Why this is exactly right.** `assign_clk_type env clk_ty Cbase = [clk_ty]`,
so seeding the step body at `pc = [clk_ty]` makes the pc at any site guarded
by clock `ck` equal to `ckty` *on the nose*:

> `clock_pc_from_assign` (with `pc0 = []`):
> `assign_clk_type env b ck = Some ckty  ⟹  clock_pc (pc0 ⊔ [b]) ck = Some (pc0 ⊔ ckty)`

Hence, at a site under `ck`:

| construct | Obc source | STC source | relation |
|---|---|---|---|
| `TcDef`/`TcNext` | `([rst_ty] ⊔ ckty) ⊔ ty(e)` | `([rst_ty] ⊔ ckty) ⊔ ety` | equal (mod. the `Ewhen`-guard absorption of §2 below) |
| `TcReset` | `[rst_ty] ⊔ ckty` | `[rst_ty] ⊔ ([rty] ⊔ rstckty)` | equal up to merge ACI |
| `TcCall` | clock actual `ckty`, reset actual `[σ o]` | clock actual `ckty`, reset actual `[rst_ty]` or `[rst_inst]` | **clock actuals identical**; reset actual differs by name only |

**Expression types differ, in the safe direction.** `translate_exp` drops
`Ewhen` guards. For a guarded assignment the dropped variables are clock
variables of `ck`, hence already in `ckty` — absorbed
(`translate_exp_type_correspondence`). For *call arguments* the guards belong
to the instantiated argument clocks and need not be recoverable, so Obc
argument types are strict *subsets* of the STC ones
(`translate_args_type_incl`); smaller sources mean weaker constraints, which
is the direction preservation needs.

**Why the 2026-07-14 change (commit 997438d) matters here.** With `TcReset`
seeded at `base_ty` and joined with `[rst_ty]`, the STC reset source is
`[rst_ty] ⊔ ([rty] ⊔ rstckty)`, which is exactly the Obc pc at a translated
reset call. Under the old (rst-seeded, no `base_ty`) rule the two would not
have matched, and the bridge would have needed the "reset-implies-clk in the
source through `simplify`" generalisation we avoided.

## 3. Blockers and design decisions — outcomes

None turned out to be mathematically fatal. The classic imperative problem
(implicit flows) is paid for by clock types, which the translation turns into
exactly the branch conditions the pc tracks.

- **B1 — Several constraints per target. RESOLVED (option a).**
  `translate_cexp x (Emerge y t f)` yields two `Assign x` leaves, so two
  constraints for `τ x`; but `simplify`/`findST` assume one constraint per
  hidden target and `findST` takes the first match, which would silently drop
  flows. `collapse` joins the sources per target before `simplify`.
  Crucially it is **precision-neutral, not merely sound**:
  `collapse_satisfaction` proves `listSatisfiable dlt (collapse cns) ↔
  listSatisfiable dlt cns`. Now in `SymTypes.v` / `SecTypes.v`.

- **B2 — Flow-insensitivity vs re-assignment. Stands as a precondition.**
  `gen` unions constraints over `Comp`, which is sound for any program but
  imprecise if a variable is assigned twice. Translated bodies are
  single-assignment (`s_nodup_defined`); the shape lemmas take that as a
  hypothesis, exactly as the STC lemmas assume `NoDup (defined tcs)`.

- **B3 — ACI alignment of pc joins. RESOLVED.**
  `generate_stmt_constraints_Control` proves
  `gen pc (Control ck s) = gen (clock-extended pc) s` as an *equality of
  `Sec` results* (the `Skip` branches contribute `[]` and no state change),
  with `clock_pc_from_assign` relating the walk to `assign_clk_type` by one
  `merge_assoc` per `Con`.

- **B4 — Scheduling. IN PROGRESS** (phase 5; see `RESUME.md` §4d for what is
  proved and the four remaining steps).  The recommended route below is the
  one taken. `correctness_loop_call` needs
  `Well_defined P`, i.e. the *scheduled* program, while the SIF STC signatures
  are generated from the unscheduled `translate all_nodes`. Recommended route:
  generate the Obc signatures from the scheduled program and add a small
  STC ↔ scheduled-STC signature bridge, rather than proving `simplify` stable
  under permutation.

- **B5 — Reset-method writes. RESOLVED.**  Assembled in the bridge as
  `reset_shared_targets`, `reset_body_constraints_classified` and
  `preserves_on_app_reset_shared`.
  `reset_insts` emits `([rst_ty] ⊔ []) ⊑ [σ o]` for **every** instance and
  `reset_mems` emits `[rst_ty] ⊑ [τ mem]`. The STC side has no counterpart:
  those are discharged by the `dlt'` choice and by the `TcNext` source (which
  contains `rst_ty`; every last has a `TcNext` by `s_lasts_in_tcs`). The
  `counter_paper` dump confirms the predicted shape, including a never-reset
  instance whose state type is constrained only by the reset method.

- **B6 — Two methods, one signature. Stands.** Translated classes have exactly
  `step`/`reset` with fixed roles, so one class-level `SIG.signature` suffices
  and `generate_constraints` / `Signature_consistent` / `preserves_on` are
  reused unchanged. **Consequence:** the system covers `translate P` output,
  not arbitrary Obc — in particular not post-`Fusion`/`ObcAddDefaults` code,
  which would need per-method signatures and revisiting B2.

- **B7 — Scoping without clocks. RESOLVED, differently than planned.**
  The plan was to use `wt_stmt` for free-variable containment. That was
  rejected because `OBCTYPING` is parameterised by `OBCSEMANTICS`. Scopedness
  is now stated over the syntactic free names `exp_free`/`stmt_free` and
  `names_scoped`, and the scopedness theorems lost their `p`/`insts`/`mems`/
  `vars` parameters as a result.

## 4. Proof plan (NLustre→STC pattern, transplanted)

New files in `src/SIF`, mirroring the existing layout:

1. **`SecObcTyping.v`** (mirror of `SecSTCTyping.v`): Obc `assign_exp_type`,
   `gen_stmt`, `generate_state_env` (≅ `generate_reset_env`), `collapse`,
   `generate_class_signature` (+ `_scoped_env` variant), scopedness + shape
   theorems over the syntactic free names (**not** `wt_stmt` — see B7).
   *Largest new file; mostly transliteration.*
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

## 5. Where the files ended up

All five files exist and compile; `collapse` (B1a) was taken, and the `_CoqProject`
entries are generated from `vfiles`. Two divergences from the plan above are worth
recording:

- **`collapse` and its lemmas do not live in `SecObcTyping.v`.** They are generic
  over constraints, so they were moved to `SymTypes.v` (syntax) and `SecTypes.v`
  (satisfaction). Likewise `env_injective`/`env_values` went to `SIF/Helpers.v`
  and the fresh per-key machinery to `SecContext.v`, shared with the STC side.
- **`generate_class_signature_inv` lives in `SecObcTypingCorrectness.v`**, not in
  the typing file: implementation in `SecObcTyping`, bridge-facing correctness in
  the Correctness module.

For the live worklist and per-item status see `Stc2ObcSIF_progress.md` §4b.
