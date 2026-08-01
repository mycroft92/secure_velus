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
| 1 | `src/SIF/SecObcTyping.v` | **DONE** |
| 2 | `src/SIF/SecObcConstraintExport.v` | **DONE** — full pipeline wired: extraction entry (`extraction/Extraction.v`), printers (`src/SIF/siflib.ml`), `osif_destination`/`print_obcsif_if` (`src/veluslib.ml`), driver call + `-dsif` writes `<file>.o.sif` (`src/velusmain.ml`); dump shows raw, collapsed and simplified constraints per class plus name maps |
| 3 | `src/SIF/SecObcTypingCorrectness.v` | **DONE** — the scope_key/scope_sec leftovers landed as `generated_sys_signature_scope_key` and `generated_sys_signature_scope_sec_from_env_props` in `SecStcTypingCorrectness.v`, plus `generate_class_signature_scoped` here |
| 4 | `src/SIF/SecStcObcTranslation.v` (bridge) | **DONE, admit-free** — signature preservation complete, from `generated_signatures_preserved_obc` up to `generated_program_signatures_preserved_obc_global`.  The chain skeleton matches `SecNLusStcTranslation.v` item for item; the call-preservation core underneath is a deliberate generalization of it (`RESUME.md` §4b).  The scoped induction carries its accumulator invariants rather than assuming a step predicate.  See `RESUME.md` §4 for the correspondence table |
| 4b | `src/SIF/SecNLusStcObcEnv.v` | **DONE** — chain-level environment threading; discharges the name alignment and builds `scoped_envs_windowed`, ending in `generated_program_signatures_preserved_obc_scheduled` (the program `nl_to_cl` actually reaches).  See `RESUME.md` §4c |
| 5 | scheduling equivalence (B4) | **DONE, admit-free** — constraint generation mints no identifiers, so reordering `s_tcs` permutes the raw constraints with identical names.  Runs from the `state_pure` stack up to `generated_signatures_preserved_by_scheduling` in `SecNLusStcObcEnv.v`.  See `RESUME.md` §4d for the layer table and for the `Is_well_sch` → `NoDup (map fst (resets_of _))` premise change it forced |
| 6 | `src/SIF/SecObcNonInterference.v` | **DONE, admit-free** — the transport, mirroring `SecStcNonInterference.v` member for member.  See `RESUME.md` §4e |

All six phases are done.  Deferred cleanups are listed in `RESUME.md` §6.

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

**(1c) Ownership refactor (2026-07-31).** Everything generic that had
accumulated in `SecObcTyping.v` before the `SECSTMTTYPING` section has
been moved to the module that owns it, and the pre-existing duplicates
elsewhere were deleted at the same time:

| moved to | items |
|---|---|
| `SymTypes.v` (ST / constraint syntax) | `st_eq_dec`, `join_into`, `collapse`, `join_into_rhs_in`, `join_into_rhs_nodup`, `collapse_rhs_nodup`, `collapse_rhs_in`, `join_into_scoped`, `collapse_scoped`, `join_into_rhs_len`, `collapse_wf`, `lhs_join`, `collapse_same_target`, `lhs_join_app` |
| `SecTypes.v` (satisfaction) | `constraint_satisfiable_merge_split`, `join_into_satisfaction`, `collapse_satisfaction` |
| `SecContext.v` (Sec monad + Env) | `env_injective`, `names_scoped`, `names_scoped_app`, `fresh_reset_ident`, `fresh_reset_insert`, `fresh_reset_insert_find_in_acc`, `fresh_reset_insert_find_self`, `fresh_reset_insert_preserves_find` |

`SecSTCTyping.v` had a **verbatim duplicate** of the fresh-key machinery
(`fresh_reset_ident/insert` + the same three lemmas); those were deleted
and now resolve to `SecContext`. The Obc copies (`fresh_state_*`) are
gone too — only the *drivers* remain in their own files, since they
differ: STC walks `trconstr`s and filters `TcReset`, Obc walks `c_objs`.
No statement changed; `SECSTCTYPING.generate_reset_env` and
`SECOBCTYPING.generate_state_env` still resolve for the exporters, and
`SECOBCTYPING.collapse` became `SymTypes.collapse` there.

**(1d) Second ownership pass (2026-07-31).** The env range/injectivity
family was *triplicated*: `SecStcTypingCorrectness.v`,
`SecObcTypingCorrectness.v`, and (at the `sec` prefix)
`NameInterface.v`. The two `sec_reset` copies are now one, in
`SecContext.v`:

`env_values`, `env_values_add`, `env_values_nodup_injective`,
`env_reset_bounded` (was `reset_env_sec_bounded` / `state_env_sec_bounded`),
`env_reset_bounded_step`, `env_values_reset_fresh_notin`,
`fresh_reset_insert_sec_range`, `fresh_reset_insert_env_props`; plus
`SecStcTypingCorrectness`'s third copy of `fresh_reset_insert_preserves_find`
(already hoisted in pass 1c).

Only the *drivers* stay in their own Correctness files
(`generate_reset_env_range/_props/_injective` over trconstrs;
`generate_state_env_range/_props/_injective/_key_from_objs` over
`c_objs`).

**(1e) Third pass — one shared instance (2026-07-31).** The genuinely
monad- and prefix-independent facts now live once, in **`SIF/Helpers.v`**
(top-level, built first, depends only on `Common`/`Environment`):
`env_injective`, `env_values`, `env_values_add`,
`env_values_nodup_injective`. `NameInterface.v`, `SecContext.v` and
`SecSTCTyping.v` all dropped their copies and `Require Import
SIF.Helpers` instead; the two qualified references
(`NAMEGEN.env_injective`, `SECSTCTYPING.env_injective`) were repointed.

`SecContext.v` keeps only what is genuinely `sec_reset`- and
Sec-monad-specific: `env_reset_bounded(_step)`,
`env_values_reset_fresh_notin`, `fresh_reset_insert*`. `NameInterface.v`
keeps its `sec`-prefixed `env_sec_bounded` family and its Name-monad
`fresh_insert_env_props` — those are *not* duplicates: different gensym
prefix, different monad.

One variant is deliberately left: `SecNLusTyping.v`'s `env_injective` is
0-ary over a section variable rather than taking `env` as a parameter.
Repointing it to the shared one would preserve its type but break the
`unfold env_injective` steps in its proofs, for no real gain.

**Why `NameInterface.v` keeps its own bounded family.** Its copies are hard-wired to
the `Ids.sec` prefix (not `sec_reset`), it is built *before*
`SecContext.v`, and `NAMEGEN` does not take a `SECMONAD` parameter — so
reusing the shared family there would mean changing `NAMEGEN`'s
signature and every instantiation of it. Deliberately out of scope; the
duplication is prefix-specific rather than verbatim.

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
| 2 | generalized reset-call preservation | `:2105` `signatures_preserved_reset_underlying_calls_from_good` (now hoisted into `SIGNATURE_PROOFS`) | **DONE** — `signatures_preserved_obc_calls_from_good` in `SecStcObcTranslation.v`. Sub-tasks A (`generate_constraints_mono_inp`) and A′ (`generate_constraints_ok_change_inp`) proved; B (hoist) done. Only sub-task **C** (`signature_good` for generated STC signatures) is still needed, and only to *discharge this theorem's hypotheses* at the lockstep (item 9). |: prove `Signature_call_preserves_obc n1 n2` for *generated* signature pairs (obligation C, tccall doc §4; Route B §5 in reserve). Everything else is now expressed in terms of it. |
| 3 | TcCall case | part of `eqn_preserv :752` | **DONE**: `tccall_preserv` — inverts both generators, matches clk/outputs, feeds `translate_args_type_incl` and the assumed `Signature_call_preserves_obc`, exactly as `eqn_preserv` consumes `Signature_consistent` |
| 4 | `tc_preserv` (all four cases) | `eqn_preserv :752` | **DONE** — `tc_preserv` dispatches on the four cases; the side conditions each case needs are collected in `tc_preserv_hyps`. Three cases go via equalities (`tcdef_preserv`, `tcnext_preserv`, `tcreset_preserv`, discharged with `dlt' = dlt` through `collapse_satisfaction` / `preserves_on_refl`); `tccall_preserv` supplies the fourth. |
| 5 | tcs-list assembly | `eqns_preserv_scoped :1080` | **DONE** — `tcs_preserv` in `SecStcObcTranslation.v`. Both sides are decomposed into per-trconstr blocks (`generate_trconstrs_constraints_blocks` in `SecSTCTyping.v`; `translate_tcs_fold_right` + `generate_fold_right_Comp` on the Obc side, which pairs blocks with `rev tcs`). The pairing is reversed with `Forall2_rev`, combined via `Forall2_combine{,_with}`, fed to `preserves_on_concat_list`, and the residual order difference is closed by `preserves_on_Permutation` + `concat_rev_Permutation`. `extras` (the Obc-only names, i.e. callee instance state types) and their scopedness stay **hypotheses** of `tcs_preserv`; discharging them at system level is part of item 7. |
| 6 | reset-method constraints | — (none) | **DONE bar the assembly.** Both halves of `translate_reset` emit exactly one constraint `([rst_ty], [ty])` per memory and per instance (`generate_reset_mems_blocks`, `generate_reset_insts_blocks`, `generate_translate_reset_blocks`, on top of `generate_fold_left_Comp` in `SecObcTyping.v` — note the reset method folds `Comp acc new`, so unlike `translate_tcs` it comes out *in order*). Each is entailed under the *same* valuation by an STC constraint with the same target and `rst_ty` in its source (`reset_constraint_entailed`), and the STC side supplies exactly those: `generate_trconstrs_constraints_last_source` (every last has a `TcNext`) and `..._reset_source` (every reset instance has a `TcReset`, on either shape of reset clock). What is left is attaching each reset constraint to the right block — part of item 7. |
| 7 | class-level raw `preserves_on` | `node_preserv_scoped :1341`, `:1418`, `:1496` | **in progress.** Combinators done: `preserves_on_collapse` and `preserves_on_incl` (`SecTypes.v`), `preserves_on_app_scope_entailed`, `preserves_on_app_reset_shared`. Reset method done: `generate_translate_reset_blocks` gives its shape, `reset_mems_targets` / `reset_insts_targets` supply the STC constraints backing its shared targets, `reset_targets_satisfied` discharges them with no witness. Extras done: `tc_obc_extras` / `tcs_obc_extras` with `tcs_obc_extras_Forall2`, `tc_obc_extras_spec`, `tcs_obc_extras_concat`, `tcs_obc_extras_nodup`. **Remaining:** fix the raw scope (`inp ++ out ++ locals ++ lasts ++ rids ++ [clk; rst]`), prove the extras fresh w.r.t. it, per-block target scopedness, then assemble. |
| 8 | simplify bridge | `:1685` / `:1806` / `:1938` | needs "every hidden var has a definer" for `locals`/`lasts`/`stids` — only derivable **with the translation in hand**; this is the class-scopedness deferred from phase 1. Most likely place for a surprise. |
| 9 | lockstep induction | `:2503` + `:2382` + `:2342` | yields `Signature_consistent Gstc Gobc` + scopedness + scope_sec of Gobc; needs the phase-3 scope_sec port |
| 10 | global corollary | `:2785` `generated_program_signatures_preserved_global` | the export the NI transport (phase 6) consumes |

### The reset-instance/extras interaction (resolved, 2026-07-31)

The Obc reset method constrains `rst_ty ⊑ sty_o` for every instance
`o`, while the step method's call block also touches `sty_o`.  Two
blocks wanting the same name would break the disjoint-`extras`
requirement of `preserves_on_concat_list`.  `reset_consistency` splits
the instances so that it does not:

- **Reset instances** (`Step_with_reset_in o true`): the STC call's
  reset actual is `[rst_inst]` and the Obc call's is `[sty]`, and these
  are the *same identifier* (`Env.find o reset_env = Env.find o
  state_env`).  Nothing needs bridging, so the reset-underlying call
  theorem — which is where `~ In sty scope` comes from — is not used.
  `signatures_preserved_equal_calls_from_good` (`SIFSignature.v`),
  its Obc counterpart `signatures_preserved_obc_equal_calls_from_good`
  and the trconstr-level `tccall_reset_preserv_eq` handle this case
  with the instance identifier *inside* `scope`, so extras stay empty
  and the `TcReset` block may mention it freely.  The reset-method
  constraint is then entailed by the `TcReset` constraint.
- **Non-reset instances**: STC passes `[rst_ty]`, Obc passes `[sty]`,
  and `sty` occurs nowhere on the STC side — a genuine private extra of
  the call block.  The existing reset-underlying theorem applies, and
  its witness sets `dlt' sty = hm_ext dlt [rst_ty] = dlt rst_ty`, so
  `rst_ty ⊑ sty` holds with equality.

The two cases use different theorems and their extras never collide.

### Item 7: per-trconstr chunking suffices (superseded note, 2026-08-01)

An earlier note here concluded that the constraint lists had to be
chunked by *instance group* rather than per trconstr.  That is no longer
true and the note has been removed.

It was a consequence of STC and Obc minting instance names separately
(`resets_of s_tcs` vs `c_objs`), which made `sty` and `rst_inst`
different identifiers for the same instance and left `sty` referenced by
three blocks at once.  Since the shared name generator mints instance
names once (`ninst`), that is gone.  Each Obc-only name now belongs to
exactly one block:

- **Reset instances** — one identifier for both languages.  It lives in
  the raw scope, is hidden by *both* signatures, and the Obc `TcReset`
  block is the STC one.  The call's reset actual coincides on the two
  sides, so `signatures_preserved_equal_calls_from_good` applies and the
  `~ In sty scope` side condition of the reset-underlying theorem is
  never needed.
- **Non-reset instances** — genuinely Obc-exclusive.  `sty` is a private
  extra of its own `TcCall` block, defined by that instance's
  reset-method constraint, hidden by `hidden_class_vars`, and eliminated
  by `simplify`: the "temporary environment we simplify away".

So `preserves_on_concat_list`'s disjointness holds per trconstr and
`tcs_preserv` stands as written — no partition of the tc list and no
permutation lemma over instance groups.

Two general rules the Obc side relies on, both already proved:

- a variable with several defining statements (a compiled `merge`
  produces one `Assign` leaf per branch) gets one constraint whose
  source is the ⊔ of all of them — `collapse`, with
  `collapse_same_target` and the *equivalence* `collapse_satisfaction`;
- names local to one language are hidden and simplified away —
  `hidden_sys_vars` on the STC side, `hidden_class_vars` on the Obc side.

### How the reset method's constraints get owned (2026-08-01)

`craw_reset` emits one constraint `rst_ty ⊑ ty` per memory and per
instance.  They are discharged three ways, and none of it needs the
transition-constraint list to be partitioned:

- **memories** and **reset instances** — their targets are shared with
  the STC side, so any valuation agreeing with the source one on the
  scope already satisfies them (`preserves_on_app_reset_shared`); the
  backing STC constraints come from `reset_mems_targets` and
  `reset_insts_targets`.
- **non-reset instances** — the call block already *produces* that
  constraint: `signatures_preserved_reset_underlying_calls_from_good`
  concludes with `(srcrst, [sty]) :: sconst`, which
  `Signature_call_preserves_obc_rst` now keeps instead of discarding.
  `preserves_on_incl` then cuts the proved target list down to the
  generated one.

So the class bridge proves preservation against a target mentioning
each Obc constraint at least once, and narrows afterwards.

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

**Where the work actually is (updated 2026-07-31, later):** items 1, 2,
3, 4 are **done** — every per-trconstr case of the bridge is proved,
including TcCall, and the call-preservation property is established for
signature pairs related by `signatures_preserved`. Item 5 and
sub-task C are now done too.  What remains is items 6–7 (reset-method
constraints and the class-level assembly, which also discharges the
`extras`/scopedness hypotheses `tcs_preserv` currently takes), the
simplify bridge (8) and the lockstep (9–10) — ports of proofs that
already exist on the NL→STC side. Nothing else in the chain is blocked on new
ideas.

**Definitions now in place** (`SecStcObcTranslation.v`, section
`TCPRESERV`): `call_side_conditions`, `Signature_call_preserves_obc`
(one clause — Obc routes *every* call's reset actual through `sty`, and
`inp` is weaker), `Signature_consistent_obc`.

### Item C status — **DONE** (2026-07-31)

`generate_sys_signature_good` (`SecStcTypingCorrectness.v`): every
generated STC signature is good.  Ingredients, all additions only:

- `trconstrs_targets_perm`, `generate_trconstrs_constraints_wf`,
  `generate_trconstrs_constraints_blocks`, `generate_reset_env_rids`,
  `generate_reset_env_keys_nodup` (`SecSTCTyping.v`)
- `targets_nodup` (`SecStcTypingCorrectness.v`) — variables and lasts get
  distinct `sec` names (source names distinct via `s_nodup`, environment
  injective), reset instances get distinct `sec_reset` names, and the two
  prefixes never collide (`Ids.sec_neq_sec_reset`)
- `atom_or_gensym_not_sec`, `sys_name_not_sec_gensym`,
  `sys_hidden_visible_disjoint`, `generated_sys_hidden_disjoint`
  (`SecStcTypingCorrectness.v`) — the names `simplify` eliminates never
  appear in the public scope
- `get_mappings_nodup_gen` / `get_mappings_perm` hoisted into the
  `Env_helpers` section of `NameInterface.v` (where `get_mappings` is
  defined), together with `get_mappings_In`, which had been stranded
  inside the `NAMEGEN` module type

The endgame mirrors `generate_node_sig_good_from_local_env`
(`SecNLusTypingCorrectness.v:560`): `NoDup_Permutation` showing the
post-`simplify` targets are exactly the outputs.

*Known duplication to collapse later:* `get_mappings_nodup` still has
section-scoped copies in `SecNLusTyping`/`SecSTCTyping`, and
`nodup_singleton_map` exists both in `SIFSignature` (SIG) and in
`SecNLusTyping`.

## 5. Phase 5 — scheduling (B4).  DONE

`StcToObc/Correctness.correctness_loop_call` needs `Well_defined P`
(scheduled), while the SIF STC signatures the NL-Stc bridge produces come
from the unscheduled `NLustreToStc.Translation.translate all_nodes`.

Option (b) was taken: the Obc signatures are generated from the *scheduled*
STC program, and `generated_signatures_preserved_by_scheduling`
(`SecNLusStcObcEnv.v`) is the STC ↔ scheduled-STC bridge.  Option (a) —
proving `simplify` itself permutation-stable — stays rejected: it eliminates
hidden names in list order, so when one hidden name's definition mentions
another the two results agree only up to equivalence, not syntactically.

`RESUME.md` §4d has the full layer table.  The one thing that had to move
outside phase 5: `generate_sys_signature_good` and
`generated_sys_simplify_ready` used to take `Is_well_sch`, which the
unscheduled program does not satisfy.  Both only used it through
`Is_well_sch_resets_nodup`, so both now take
`NoDup (map fst (resets_of s_tcs))` — a property of the multiset of
transition constraints, hence one that survives the reordering.

## 6. Phase 6 — `SecObcNonInterference.v`.  DONE

Follows `SecStcNonInterference.v` item for item (it is a transport, not a fresh NI proof):
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
