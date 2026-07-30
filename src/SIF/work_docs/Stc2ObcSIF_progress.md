# Stc2ObcSIF — implementation working doc (resumable)

Branch: `Stc2ObcSIF`. Companion design/blocker analysis: `Stc2ObcSIF_plan.md`
(read it first — it defines the pc-generator design, the B1–B7
blockers/decisions, and the overall theorem chain).

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
- Commit messages: plain text, no AI attribution, ever.

## 1. Status

| Phase | File | Status |
|---|---|---|
| 1 | `src/SIF/SecObcTyping.v` | **DONE, compiles** |
| 2 | `src/SIF/SecObcConstraintExport.v` | **DONE, compiles** — full pipeline wired: extraction entry (`extraction/Extraction.v`), printers (`src/SIF/siflib.ml`), `osif_destination`/`print_obcsif_if` (`src/veluslib.ml`), driver call + `-dsif` writes `<file>.o.sif` (`src/velusmain.ml`); dump shows raw, collapsed, and simplified constraints per class plus name maps |
| 3 | `src/SIF/SecObcTypingCorrectness.v` | **mostly DONE, compiles** — remaining: scope_key/scope_sec (need NAMEGEN; may live in bridge instead) |
| 4 | `src/SIF/SecStcObcTranslation.v` (bridge) | **started, compiles** — Control/pc lemmas done (§4 item 1); per-tc correspondence next |
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
