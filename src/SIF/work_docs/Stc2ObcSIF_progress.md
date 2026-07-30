# Stc2ObcSIF — implementation working doc (resumable)

Branch: `Stc2ObcSIF`. Companion documents:
- `Stc2ObcSIF_plan.md` — design/blocker analysis (read first: pc-generator
  design, blockers B1–B7, overall theorem chain).
- `Stc2ObcSIF_tccall.md` — **the TcCall case in detail**: its three proof
  obligations, why each is sound, the `dlt'` construction, the
  risk item (valuation surgery) and its mitigation route, sequencing, and a
  verified lemma inventory. Read before starting phase-4 TcCall work.

This document tracks implementation status and contains everything needed to
resume the work cold (with any model/person).

---

## 0. Build workflow (mandatory)

- Coq compilation works ONLY inside docker container `funny_franklin`
  (Coq 8.9.1). `/workspace` there is a **copy** of this repo, not a mount.
- Edit locally, then: `docker cp <file> funny_franklin:/workspace/<file>`.
- **Adding a NEW .v file — the canonical flow:**
  1. add it to `vfiles` (tracked in git; keep dependency order),
  2. `docker cp` both the file and `vfiles` into `/workspace`,
  3. regenerate `/workspace/_CoqProject` from `vfiles` (the `-R` header
     lines + `cat vfiles`, exactly what `configure` does — `_CoqProject`
     is GENERATED and gitignored; never rely on hand-edits alone),
  4. `make -j4` (its `proof` target regenerates `Makefile.auto` from
     `_CoqProject`).
  A `make` run without refreshing `_CoqProject` is a **vacuous pass** for
  new files: make's dependency graph comes from the generated project
  file, so it silently ignores files it doesn't know about.
  **WARNING — do NOT re-run `./configure` in the container**: it also
  re-runs CompCert's configure, which regenerated/clobbered
  `CompCert/x86_64/Archi.vo` on 2026-07-30 and broke `.vo` digest
  consistency ("inconsistent assumptions over Velus.Common.CompCertLib"),
  forcing a full `make clean` + CompCert-cascade rebuild. Only step 3 is
  needed to register files.
- For fast iteration on a single file (after it is in the generated
  project): helper `/tmp/coqc_cmd.sh` in the container (recreate if
  missing: `cd /workspace && coqc <the -R lines of _CoqProject> <file>`).
  Always finish with configure+make to validate for real.
- Keep local and container file hashes in sync (`md5 -q` vs `md5sum`).
- **`/workspace` is NOT a git checkout** (`git rev-parse` there fails): the
  host repo is the source of truth, the container is only a build sandbox.
  Nothing appears in `/workspace` except via `docker cp`, so non-build files
  (these `work_docs/*.md`, notes, examples) must be copied explicitly and
  re-copied after every edit, or the container copy goes stale:
  `docker cp src/SIF/work_docs funny_franklin:/workspace/src/SIF/`
  Likewise, example `.lus` files must be copied in before running `velus` on
  them (`examples/` in the container is the original image seed).
- Commit messages: plain text, no AI attribution, ever.

## 1. Status

| Phase | File | Status |
|---|---|---|
| 1 | `src/SIF/SecObcTyping.v` | **DONE, compiles** |
| 2 | `src/SIF/SecObcConstraintExport.v` | **DONE, compiles** — full pipeline wired: extraction entry (`extraction/Extraction.v`), printers (`src/SIF/siflib.ml`), `osif_destination`/`print_obcsif_if` (`src/veluslib.ml`), driver call + `-dsif` writes `<file>.o.sif` (`src/velusmain.ml`); dump shows raw, collapsed, and simplified constraints per class plus name maps |
| 3 | `src/SIF/SecObcTypingCorrectness.v` | **mostly DONE, compiles** — remaining: scope_key/scope_sec (need NAMEGEN; may live in bridge instead) |
| 4 | `src/SIF/SecStcObcTranslation.v` (bridge) | **in progress, compiles** — done: Control/pc lemmas, merge ACI helpers (`merge_swap/merge_factor/merge_rotate`), `translate_exp_type_correspondence` (Ewhen-guard absorption via wc), `translate_cexp_constraints` (TcDef core: leaf constraints all target τx, state untouched, `lhs_join` = STC source; uses `lhs_join`/`collapse_same_target`/`lhs_join_app` from SecObcTyping.v). DONE also: per-tc lemmas `translate_tcdef_constraints` (collapsed = STC constraint), `translate_tcnext_constraints`, `translate_tcreset_constraints` (cns = `[(([rstty] ⊔ ckty), [sty])]` — for translated `Con ckr r true` clocks this is the STC source up to ACI). **2026-07-30 generator refinement**: `rst_ty` is now a section variable of `generate_stmt_constraints`; the pc carries control dependence only (step entry pc `[clk_type]`, reset entry pc `[]`), and `[rst_ty]` is added explicitly at Assign/AssignSt/reset-call sources. Call clk actuals therefore coincide exactly with the STC `ckty`, which **eliminated TcCall obligation A** (see tccall doc §2 — the STC `constraints_mention` port was blocked by reset'd calls using `[rst_inst]`, whose `rst_ty` content only appears post-simplify). All per-tc lemmas survived with adjusted ACI. NEXT: **TcCall** — see `Stc2ObcSIF_tccall.md` for the full analysis (three obligations: STC `constraints_mention s_reset` port, `translate_arg` monotonicity, valuation surgery; plus the `dlt'` construction and the Route-B mitigation). Then tcs-level assembly + signature lockstep. Proof-engineering note: `simpl`/`cbn` unfold `merge` on cons-headed args into fix-form; recover with `change` to the convertible folded form (three precedents in this file). |
| 5 | scheduling equivalence (in 4 or separate) | not started |
| 6 | `src/SIF/SecObcNonInterference.v` | not started |

Recommended order: finish 3 → 4 → 5 → 6 (2 whenever the exporter is wanted).

Phase-3 slice already proved (in `SecObcTypingCorrectness.v`):
`constraint_satisfiable_merge_split`, `join_into_satisfaction`,
`collapse_satisfaction` (listSatisfiable dlt (collapse cns) ↔ ... cns —
so collapse is precision-neutral, closing the soundness question of
design decision B1a), `generate_constraints_rhs_singleton` (no NoDup
needed — direct induction on the final mmap of
`SIG.generate_constraints`), `generate_stmt_constraints_rhs_singleton`,
`generate_stmt_constraints_collapse_wf` (wf_constraints of the collapsed
step+reset raw constraints).

## 1b. Empirical validation (2026-07-30)

`velus -dsif examples/counter_paper.lus` now also writes `counter_paper.o.sif`
(the Obc dump). On both classes of that example the **post-simplify Obc
signature constraints are syntactically identical to the STC ones**, while
the pre-simplify sets differ exactly as the plan predicts: merge leaves are
split then collapsed; reset-method constraints `[rst] <= state/mem` are
absorbed; step-call constraints carry the extra `rst` from pc-as-clk and a
`state_ty` instead of `rst_ty`/`rst_inst`, all reconciled by `simplify`
substitution. This is strong evidence for the bridge target
(`signatures_preserved`, plausibly even syntactic equality post-simplify).
Also note: the dump shows a **never-reset instance** (`spd`) getting its
state constraint `[rst] <= state` only from the reset method — the case
flagged as plan blocker B5 behaves as predicted.

## 2. What phase 1 contains (`SecObcTyping.v`)

Mirrors `SecSTCTyping.v`. Module type `SECOBCTYPING (Ids Op OpAux SC SynObc
SemObc TypObc SIG)` + functor `SecObcTyping`. Inserted in `_CoqProject`
after `SecStcTypingCorrectness.v`.

- `hidden_class_vars locals lasts stids` — ≅ `hidden_sys_vars` (locals =
  step `m_vars` types, lasts = `c_mems` types, stids = instance state types).
- `env_injective` — same 4-line def as the STC/NLus files.
- **STATEHANDLER**: `fresh_state_ident` (gensym `Ids.sec_reset`, same prefix
  as STC reset-instance types so freshness lemmas can be shared),
  `fresh_state_insert`, `generate_state_env(')` keyed on `c_objs` instance
  names (⊇ STC's reset_env: EVERY instance gets a state type, since every
  step call reads one and the class reset method writes all of them).
  Lemmas: `fresh_state_insert_find_in_acc/_find_self/_preserves_find`,
  `generate_state_env'_find_in_acc`, `generate_state_env_find_in`,
  `generate_state_env'_preserves_find` — verbatim ports of the RESETHANDLER
  lemmas of `SecSTCTyping.v`.
- **SECEXPTYPING**: `assign_exp_type` over Obc exps (`Var`/`State`/`Valid` →
  env lookup, `Const` → `[]`, `Unop` → recurse, `Binop` → merge);
  `assign_exp_type_scoped` proved against ordinary typing `TypObc.wt_exp`
  (NOT `wc_*` — Obc has no clocks; wt is used purely for free-var bounds).
- **collapse** (design decision B1a): `join_into`/`collapse` join the LHSs of
  constraints sharing a target, restoring one-constraint-per-target before
  `simplify`. Lemmas: `join_into_rhs_in`, `join_into_rhs_nodup`,
  `collapse_rhs_nodup`, `collapse_rhs_in` (In-map-snd preserved both ways),
  `join_into_scoped`, `collapse_scoped`, `join_into_rhs_len`, `collapse_wf`
  (wf_constraints of the collapsed list from singleton RHSs).
  Satisfaction-equivalence of collapse (listSatisfiable dlt cns ↔ collapsed)
  is NOT here — it needs the lattice (Lat), so it belongs in phase 3.
- **SECSTMTTYPING** (section vars `G env state_env`):
  `generate_stmt_constraints (pc: ST) (s: stmt)` — the pc-carrying generator:
  - `Assign/AssignSt x e` → `[(pc ⊔ ety, [τ x])]` (vars and mems share `env`)
  - `Ifte e s1 s2` → recurse with `pc ⊔ ety`, append
  - `Comp` → append; `Skip` → `[]`
  - `Call [] _ o m _` → if `m = reset` then `[(pc, [state_ty o])]` else `ret []`
  - `Call (y::ys) cls o m es` → if `m = step` then
    `generate_constraints (sig cls) inptyps pc [state_ty o] outtyps`
    (callee s_clk ↦ pc, s_reset ↦ state type — see plan §2 and the argument
    in plan B-section for why pc-as-clk is post-simplify equivalent to the
    STC substitution) else error.
  - `stmt_state_keys` ≅ `trconstr_reset_keys` (all Call instance names).
  - `mmap_assign_exp_type_scoped`, and the main theorem
    `generate_stmt_constraints_scoped_on_keys` + corollary
    `generate_stmt_constraints_scoped` (≅ the STC `..._scoped_on_keys` pair,
    with `wt_stmt p insts mems vars s` in place of `wc_trconstr`).
- **SECCLSTYPING**: `generate_class_signature` — same monadic shape as
  `generate_sys_signature`: aux (clk_id, rst_id) from `aux_names`
  (`get_node_aux`), clk/rst types from the node-local env, step/reset methods
  via `find_method Ids.step/Ids.reset`, in/out/locals from the step method,
  lasts from `c_mems`, state env from `c_objs`, then
  `simplify (collapse (craw_step ++ craw_reset)) (hidden_class_vars ...)`
  where `craw_step` uses entry pc `[rst_type] ⊔ [clk_type]` and `craw_reset`
  uses `[rst_type]`. `generate_class_signature_scoped_env` (find_node_env
  wrapper), `generate_class_signature_inv` (full monadInv inversion lemma,
  ≅ `generate_sys_signature_inv` — lives HERE, unlike STC where it is in
  the Correctness file, because phase 3/4 both want it).
- **SECOBCPROGRAMTYPING**: `generate_all_class_signatures(')` and
  `_scoped_env` variants (accumulator style, ≅ STC).

**Deliberately NOT in phase 1** (see plan): the signature-level scopedness
theorem (`generate_sys_signature_scoped` analogue). It needs "every hidden
var has a defining constraint", which for Obc classes is not derivable from
the class record (no `s_vars_out_in_tcs` analogue) — it holds only for
*translated* classes and will be proved in phase 4 with the translation in
hand (or in phase 3 with explicit defining-targets hypotheses).

## 2c. Architectural rules for this development (2026-07-30)

Two corrections applied after review; treat them as standing rules.

**(1) The Obc security typing is syntax-level only.** `SecObcTyping.v`
depends on `Obc.ObcSyntax` and nothing else from Obc — **not**
`ObcSemantics`, **not** `ObcTyping`. The first draft used `wt_exp`/`wt_stmt`
as the scoping premise, which was wrong: `OBCTYPING` is parameterised by
`OBCSEMANTICS`, so it dragged the Obc *semantics* into a purely syntactic
constraint generator. `SecSTCTyping.v` never does this — it uses clocking,
which is syntactic. Scopedness is now stated over syntactic free names:

```coq
Fixpoint exp_free  (e: exp)  : list ident   (* Var/State/Valid → [x], ... *)
Fixpoint stmt_free (s: stmt) : list ident   (* writes ++ reads *)
Definition names_scoped env scope xs :=
  forall x, In x xs -> exists ty, Env.find x env = Some ty /\ In ty scope.
```

`generate_stmt_constraints_scoped(_on_keys)` now takes
`names_scoped env scope (stmt_free s)` in place of
`wt_stmt p insts mems vars s`, and lost the `p`/`insts`/`mems`/`vars`
parameters entirely — shorter statements and shorter proofs. When the
bridge needs these premises for a *translated* statement, derive them from
the STC-side `wc_trconstr` plus the translation, not from Obc typing.

**(1b) General lemmas go in the general module.** Added to `SecTypes.v`:
`preserves_on_from_entailment` (if every `dlt` satisfying `c1` satisfies
`c2`, then `preserves_on scope c1 c2` — the `dlt' = dlt` case) and
`preserves_on_refl`. Both are signature-agnostic and belong next to
`preserves_on_nil` / `preserves_on_weaken`.

**(2) Reuse, don't duplicate.** `in_merge_left` / `in_merge_right` were
defined inside `SecNLusTypingCorrectness.v` although they are pure
`SymTypes` facts (`in_merge_inv`, their elimination counterpart, already
lived in `SymTypes.v`). They are now **in `SymTypes.v`**, and the copies in
`SecNLusTypingCorrectness.v` were deleted — both that file and
`SecNLusNonInterferenceSupport.v` `Require Import SIF.SymTypes` directly, so
their unqualified uses resolve to the shared ones. General rule: if a needed
lemma is missing, add it to the module where it belongs and let dependents
pick it up; never make a local copy.

## 3. Phase 3 — `SecObcTypingCorrectness.v` (next up)

Mirror `SecStcTypingCorrectness.v`. Module params used: `Lat : Lattice`,
`SecT : SECTYPES Lat`, `SIGPROOFS : SIGNATURE_PROOFS` (NAMEGEN to be added
when the freshness ports need it — note NAMEGEN's functor params drag in
CESyn/SynNL). Checklist:

1. ~~`collapse_satisfaction` + rhs-singleton/shape lemmas~~ **DONE** (see §1).
2. `generate_state_env` freshness/range lemmas — port
   `fresh_reset_insert_sec_range`, `generate_reset_env_range`,
   `reset_env_sec_bounded`, `generate_reset_env_injective`,
   `reset_env_values_fresh_notin` from `SecStcTypingCorrectness.v`
   (search "reset_env" there; proofs should port with s/reset/state/).
3. Targets machinery: `stmt_targets` (types of assigned vars + state types
   of reset-called instances), `stmt_targets_contains_assigned`,
   rhs-singleton lemma for `generate_stmt_constraints` (per-call needs
   `NoDup outtyp` from wt's `NoDup ys` + `env_injective` — port
   `get_mappings_nodup` and `mmap_find_env_inv` from `SecSTCTyping.v`
   SECTRCONSTRTYPING section, they are generic).
4. `generated_class_signature_scope_key/_scope_sec` — port from STC
   equivalents (uses NAMEGEN gensym-range lemmas; note state idents use
   prefix `sec_reset`, clk/rst use `sec`, program vars use their own — the
   existing `sec_neq_sec_reset` and `node_var_not_sec_gensym`-style lemmas in
   `Ident.v`/`SecNLusTypingCorrectness.v` are the tools).
5. (If not deferred to phase 4) signature-level scopedness with explicit
   defining-targets hypotheses, via `generate_class_signature_inv` +
   `simplify_scoped` + `collapse_scoped`/`collapse_rhs_in`.

## 4. Phase 4 — `SecStcObcTranslation.v` (the bridge)

Mirror `SecNLusStcTranslation.v`. Relates `SECSTCTYPING.generate_sys_signature
s` to `SECOBCTYPING.generate_class_signature (translate_system s)` over the
same `node_scoped_env`/`aux_names`. Checklist (in order):

1. ~~**Control/pc lemma (B3)**~~ **DONE** in `SecStcObcTranslation.v`
   (CONTROLPC section): `clock_pc` (assign_clk_type with the seed replaced
   by the incoming pc), `clock_pc_from_assign`
   (`assign_clk_type env b ck = Some ckty -> clock_pc (pc0 ⊔ [b]) ck =
   Some (pc0 ⊔ ckty)` — one `merge_assoc` per Con), and
   `generate_stmt_constraints_Control` /
   `generate_stmt_constraints_Control_assign`: generating under
   `Control memset ck s` at pc equals generating for bare `s` at the
   clock-extended pc, as a plain equality of `Sec` results (the Skip
   branches contribute `[]` and no state change; one `app_nil_r`).
   Note the statement is insensitive to the memories set (`bool_var` is
   `Var`/`State`, both type via the same env lookup). Instantiate with
   `pc0 := [rst_type]` and `b := clk_type` to line the step-body
   constraints up with the STC `([rst_ty] ⊔ ckty) ⊔ ...` shapes.
2. `translate_cexp` vs `assign_cexp_type`: per-leaf constraints are each
   ⊑ the STC single constraint; after `collapse` on the class side the
   joined LHS EQUALS the STC LHS (as ST sets — prove as ST equality via
   merge-ACI, or as two-sided `hm_ext` bounds if equality gets painful; the
   `preserves_on` framework only needs the ⊑ direction from STC to Obc plus
   the defining-constraint equality for hidden vars).
3. Per-tc correspondence `tc_preserv` (≅ `eqn_preserv`): compare
   `generate_trconstr_constraint` output with the collapsed constraints of
   `translate_tc`. Cases: TcDef (via 2), TcNext (direct), TcReset →
   `(pc_at_site, [state_ty])` vs STC `([rst_ty] ⊔ ([rty] ⊔ rstckty), [rst_inst])`
   — equal by the pc lemma + merge-ACI (this alignment EXISTS because of the
   2026-07-14 rule change, commit 997438d — do not revert it); TcCall →
   reuse the `Signature_call_preserves` second-conjunct machinery; note the
   Obc side passes pc (⊇ ckty ∪ {rst_ty}) as the callee clk — the
   post-simplify equality argument is spelled out in the plan doc (§B-section
   discussion, "pc-as-clk"); expect this to be the hard case, and expect to
   need the `signatures_preserved_reset_underlying_calls_from_good`-style
   valuation surgery from `SecNLusStcTranslation.v` (lines ~2100–2330) as a
   template.
4. `reset_mems`/`reset_insts` constraints vs nothing on the STC side:
   `([rst_type], [τ mem])` collapses into the TcNext constraint (LHS ⊇
   rst_type already) and `([rst_type], [state_ty o])` collapses into the
   TcReset one (or stands alone for never-reset instances, where STC used
   `[rst_ty]` directly as call reset source — both give the same
   post-simplify sources; this is plan blocker B5, verify carefully).
5. Signature-level: `signatures_preserved` (fields agree + `preserves_on`),
   lockstep induction over the program (≅
   `generate_all_signatures_consistent_scoped'`), producing
   `Signature_consistent Gstc Gobc` + scopedness + scope_sec of Gobc.
   Discharge here the phase-1-deferred signature-scopedness for translated
   classes (hidden-defined facts come from `s_vars_out_in_tcs`,
   `s_lasts_in_tcs`, `s_subs` of the source system + translation shape).
6. Fold direction gotcha: `translate_tcs` is `fold_left Comp` in REVERSE
   order; constraint lists come out permuted w.r.t. the STC tc order.
   Collapse/satisfaction are permutation-stable; keep everything at the
   level of `Permutation` or set-satisfaction, never syntactic list equality
   across the fold.

## 4b. Pending work mapped onto the NL→STC chain

Line numbers refer to `SecNLusStcTranslation.v`. Keep the Obc bridge as
close to this chain as possible; deviations are flagged at the end.

**Layer 0 — definitions (`:84`–`:113`).** `signatures_preserved`,
`Signature_call_preserves`, `Signature_head_consistent`,
`Signature_consistent` are all generic over signatures (no NLustre/STC
syntax). Restate them in the Obc bridge (~30 lines) rather than importing
`SECNLUSSTCTRANSLATION`, which would drag the NLustre module stack in.
Note `Signature_call_preserves` has two conjuncts (simple calls / reset
calls); **Obc uses the reset-call shape for every call**, since all calls
route their reset actual through `sty`. So the Obc version needs one clause
only — generalized in a single dimension: `inp` is weaker (item 1). After
the 2026-07-30 pc refinement `clk` and `out` agree exactly.

| # | Obc item | NL→STC analogue | status / notes |
|---|---|---|---|
| 1 | `translate_arg` monotonicity | — (NL→STC shares CE syntax) | **DONE**: `translate_exp_type_incl`, `translate_arg_type_incl`, `translate_args_type_incl` (obligation B, tccall doc §3) |
| 2 | generalized reset-call preservation | `:2105` `signatures_preserved_reset_underlying_calls_from_good` | obligation C (§4); Route B (§5) in reserve |
| 3 | TcCall case | part of `eqn_preserv :752` | consumes 1+2 |
| 4 | `tc_preserv` (all four cases) | `eqn_preserv :752` | **three of four DONE**: `tcdef_preserv`, `tcnext_preserv`, `tcreset_preserv` in `SecStcObcTranslation.v` section `TCPRESERV`, stated against the real `SECSTCTYPING.generate_trconstr_constraint` and discharged with `dlt' = dlt` (via `collapse_satisfaction` / `preserves_on_refl`). TcCall outstanding. |
| 5 | tcs-list assembly | `eqns_preserv_scoped :1080` | `preserves_on_concat_scoped` with extras = `stids`; needs an `eqns_reset_extras` analogue (state-env lemmas already done) |
| 6 | reset-method constraints | — (none) | `[rst_ty] ⊑ [sty]` from the `dlt'` choice; `[rst_ty] ⊑ [mem]` from the STC TcNext source (every last has a TcNext by `s_lasts_in_tcs`) |
| 7 | class-level raw `preserves_on` | `node_preserv_scoped :1341`, `:1418`, `:1496` | scope = `inp ++ out ++ locals ++ [clk; rst]` |
| 8 | simplify bridge | `:1685` / `:1806` / `:1938` | needs "every hidden var has a definer" for `locals`/`lasts`/`stids` — only derivable **with the translation in hand**; this is the class-scopedness deferred from phase 1. Most likely place for a surprise. |
| 9 | lockstep induction | `:2503` + `:2382` + `:2342` | yields `Signature_consistent Gstc Gobc` + scopedness + scope_sec of Gobc; needs the phase-3 scope_sec port |
| 10 | global corollary | `:2785` `generated_program_signatures_preserved_global` | the export the NI transport (phase 6) consumes |

**Structural deviations from NL→STC (no analogue there):**
- *Expression / cexp correspondence* — NL→STC keeps CE expressions unchanged;
  Obc compiles them. **Done** (`translate_exp_type_correspondence`,
  `translate_cexp_constraints`).
- *`Control`/pc* — STC keeps clocks; Obc compiles them to `Ifte`. **Done.**
- *`collapse`* — Obc can emit several constraints per target. **Done**
  (incl. `collapse_satisfaction`).
- *Reset-method constraints* (item 6) — pending.
- *Fold order* — `translate_tcs` is `fold_left Comp` in **reverse**
  execution order, so the Obc constraint list is permuted w.r.t. the tc
  order. State item 5 permutation-tolerantly (satisfaction is `Forall`,
  hence permutation-stable); never as syntactic list equality across the
  fold.
- *Scheduling* (phase 5) and the *NI transport* (phase 6) — pending.

**Where the work actually is:** items 1–3 are the real proofs; 4–7 are
assembly largely dictated by existing lemmas; 8–10 are ports of proofs that
already exist.

## 5. Phase 5 — scheduling (B4)

`StcToObc/Correctness.correctness_loop_call` needs `Well_defined P`
(scheduled). SIF STC signatures are generated from unscheduled
`NLustreToStc.Translation.translate all_nodes`. Options (pick one):
(a) prove `generate_sys_signature` of a system and of its scheduled
permutation are `preserves_on`-equivalent (constraints permute per-tc;
`simplify` output differs syntactically → work at `preserves_on` level);
(b) generate the Obc signatures from the *scheduled* STC program and make
the phase-4 bridge relate scheduled-STC ↔ Obc, then add a small
STC ↔ scheduled-STC signature bridge. (b) is likely less total work since
phase 4 needs the translated system's tcs list anyway and
`Scheduler.schedule` only permutes `s_tcs` (`StcSchedule.scheduler_wc_program`
etc. give the invariant carriers).

## 6. Phase 6 — `SecObcNonInterference.v`

Mirror `SecStcNonInterference.v` (it is a transport, ~370 lines):
- `class_security` ≅ `system_security`: ∃ source node n, STC witness,
  `Signature_head_consistent` pairs for both hops (NLus↔STC from the
  existing bridge, STC↔Obc from phase 4).
- `translated_class_behavior` via `correctness_loop_call`:
  `stmt_call_eval (translate P) mempty f reset [] me0` +
  `loop_call (translate P) f step ins outs 0 me0`.
- Final theorem: two Obc loop behaviors with low-equivalent `ins` streams
  (as `list (option val)` per instant; define option-val low-equivalence ≅
  `tuple_stream_low_eq` composed with `value_to_option`) have low-equivalent
  `outs`. Proof: invert `correctness_loop_call` back to Stc loops, apply
  `translated_system_noninterference_outputs`, push equality through
  `map value_to_option`.

## 7. Coq/proof-engineering gotchas learned so far (repo-specific)

- `eauto` does NOT unfold `vars_env_scoped`/similar Definitions — apply
  lemmas with explicit `(exact H)` argument lists when premises are stated
  through such definitions (`exact` converts, `eauto` doesn't).
- Section-variable discharge order: `assign_exp_type_scoped` gets `ctxt` as
  FIRST argument after section close; `wt_exp` discharges as
  `wt_exp mems vars`, `wt_stmt` as `wt_stmt p insts mems vars`.
- Bullet discipline is strict (Coq 8.9): `- + * -- ++ **` nesting; a failed
  closing tactic inside `{ }` reports "cannot be unfocused".
- `tauto` won't prove `x = y \/ P <-> y = x \/ P` (opaque atoms) — use
  `split; intros [..|..]; [left; congruence|right; assumption]`.
- Name clashes: `inversion` auto-names collide with later `eqn:H1` — always
  use explicit `as [...]` patterns and `eqn:Hfoo` names.
- The Sec-monad `do` notation (SECMONADNotations) shadows/coexists with
  Errors' and Common's option `do` — in SIF files, write option-code with
  explicit `match` to avoid ambiguity.
- `monadInv` for Sec is `sec_bind_inv`/`sec_bind2_inv` chains; copy the
  patterns from `SecSTCTyping.v`/`SecStcTypingCorrectness.v`.
- `In (x, ty) vars → InMembers x vars` is `In_InMembers`;
  `Forall2_in_left : Forall2 P xs ys -> In x xs -> exists y, In y ys /\ P x y`.

## 8. Key file map (mirrors)

| Obc SIF file (new) | Mirror (existing) |
|---|---|
| SecObcTyping.v | SecSTCTyping.v (+ SecCETyping.v for exps) |
| SecObcConstraintExport.v | SecStcConstraintExport.v |
| SecObcTypingCorrectness.v | SecStcTypingCorrectness.v (+ parts of SecNLusTypingCorrectness.v) |
| SecStcObcTranslation.v | SecNLusStcTranslation.v |
| SecObcNonInterference.v | SecStcNonInterference.v |

Shared, unchanged: SymTypes.v (merge/simplify/scoped), SIFSignature.v
(signature record, generate_constraints, preserves_on machinery in
SIGPROOFS), SecContext.v (Sec monad), NameInterface.v (envs/aux names).
`collapse` currently lives in SecObcTyping.v (not SymTypes.v) to avoid
touching shared files; move it to SymTypes.v only if the bridge needs it on
the STC side too.
