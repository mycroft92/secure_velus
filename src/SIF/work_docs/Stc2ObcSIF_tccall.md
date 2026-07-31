# TcCall in the Stc→Obc security bridge: obligations, risks, mitigations

Status: **CLOSED 2026-07-31** — `signatures_preserved_obc_calls_from_good`
is proved in `SecStcObcTranslation.v`; no admits, full build green.
The analysis below is retained for the record. Companion docs: `Stc2ObcSIF_plan.md` (design,
blockers B1–B7), `Stc2ObcSIF_progress.md` (phase status, build workflow).

TcCall is the last per-trconstr case of the bridge and the only one where the
existing NLustre→STC machinery cannot be reused near-verbatim. **There is no
mathematical blocker**: every gap below closes on paper, and every inequality
points in the direction preservation needs. The cost is concentrated in one
proof-engineering item (§4), which has a documented fallback (§5).

All file:line references below were checked against the tree at commit
`9dc31e0`.

---

## 1. What has to be proved

The bridge's per-tc obligation is *semantic*, not syntactic — unlike TcDef /
TcNext / TcReset, which are already proved as constraint-list equalities
(`translate_tcdef_constraints` etc. in `SecStcObcTranslation.v`). For TcCall
the target is `preserves_on` (`SecTypes.v:869`):

```coq
preserves_on (xs: list ident) (cns1 cns2: list constraint) : Prop :=
  forall dlt, listSatisfiable dlt cns1 ->
    exists dlt', agree_on xs dlt dlt' /\ listSatisfiable dlt' cns2.
```

i.e. *any* valuation satisfying the STC call constraints can be extended
(off the visible scope) to one satisfying the Obc call constraints.

### The two sides, side by side

STC (`SecSTCTyping.v:456–474`), for `TcCall i xs ck rst f es`:

| | unreset (`rst = false`) | reset (`rst = true`) |
|---|---|---|
| callee sig | `sig_stc = find_signature f Gstc` | same |
| inp | `inptyp_stc` = `assign_exp_type` of CE args | same |
| clk | `ckty` = `assign_clk_type env base_ty ck` | same |
| **rst** | `[rst_ty]` | `[rst_inst]` (from `reset_env`) |
| out | `outtyp` = `get_mappings xs env` | same |

Obc (`SecObcTyping.v`, `generate_stmt_constraints`, `Call` step branch), for
the translated `Control ck (Call xs f o step (map (translate_arg ck) es))`:

| | value |
|---|---|
| callee sig | `sig_obc = find_signature f Gobc` |
| inp | `inptyp_obc` = `assign_exp_type` of `translate_arg`-ed args |
| **clk** | `pc = ckty` — identical to STC since the 2026-07-30 refinement (§2); was `[rst_ty] ⊔ ckty` before |
| **rst** | `[sty]` (`state_env` lookup for instance `o`) |
| out | `outtyp` (same idents, same env) |

So after the §2 refinement there are **three deltas**: callee signature
(handled by the induction hypothesis / `Signature_consistent`, exactly as in
the NLustre→STC bridge), the weaker `inp` (§3), and the reset actual (§4).
The clock slot now agrees exactly.

---

## 2. Obligation A — RESOLVED by a generator refinement (2026-07-30)

**Status: eliminated. No longer an obligation.** The analysis below is kept
because it explains *why* the refinement was necessary.

**What we found when attempting Route A.** The domination argument needs
`constraints_mention s_reset` for **STC** signatures. That port turned out
NOT to be mechanical: STC's reset'd `TcCall` uses `[rst_inst]` as its reset
actual (`SecSTCTyping.v:466-474`), which contains no `rst_ty` at raw level.
So `constraints_mention rst_ty raw` is **false** for any system with a
reset'd call — the mention only materialises *after* `simplify` substitutes
the hidden `rst_inst` away. Proving it would have required a new
"substitution creates mention" lemma family over `subAll`/`simplify`
(roughly: if `findST cns d = Some st` and `In ty st`, then constraints
mentioning `d` mention `ty` after substitution), which is a genuinely new
~150-line development. That was the real blocker on the straightforward
route — not the valuation surgery.

**The refinement (implemented).** The root cause was a design choice, not a
mathematical necessity: the step method's entry pc was `[rst_ty] ⊔
[clk_type]`, so the reset dependence rode along inside the pc and leaked
into the callee's **clock** formal at every call. Instead, `rst_ty` is now a
section variable of `generate_stmt_constraints`, added explicitly at the
places that genuinely depend on it, and the pc carries control dependence
only:

| construct | source |
|---|---|
| `Assign x e` / `AssignSt x e` | `([rst_ty] ⊔ pc) ⊔ ty(e)` |
| `Call [] c o reset []` | `([rst_ty] ⊔ pc, [state_ty o])` |
| `Call ys c o step es` | `generate_constraints (sig c) inp **pc** [state_ty o] out` |
| entry pc | step method `[clk_type]`, reset method `[]` |

Since `assign_clk_type env clk_type Cbase = [clk_type]`, the pc at a site
under clock `ck` is now exactly the STC clock type `ckty`
(`clock_pc_from_assign` with `pc0 := []`), so:

- TcDef/TcNext/TcReset sources are **unchanged** (`[rst_ty] ⊔ pc` reproduces
  the old pc), and their per-tc correspondence lemmas still hold — only the
  internal ACI bookkeeping shifted.
- **Call clk actuals now coincide exactly with STC's `ckty`.** The extra
  `rst_ty` is gone, so no mention invariant is needed at all.

This is also the more faithful design: the pc models *control* dependence;
the caller's reset dependence reaches call outputs transitively through the
instance state type (which the reset method constrains with
`[rst_ty] ⊑ [state_ty]`), not by being conflated into the callee's clock.

**Empirical confirmation** (`counter_paper.o.sif`, class `odometer`):

```
before:  [sec$12, sec$13, sec$14, sec_reset$1] <= [sec$17]
after:   [sec$12,          sec$14, sec_reset$1] <= [sec$17]
STC:     [sec$12, sec$13, sec$14]              <= [sec$17]
```

The only remaining difference at a call site is the **reset actual's name**
(`sec_reset$k` vs `rst_ty`/`rst_inst`) — precisely the shape that
`signatures_preserved_reset_underlying_calls_from_good` already handles.
Post-simplify signatures still match STC exactly.

**Consequence for the roadmap.** §3 (weaker args) and §4/§5 (valuation
surgery) stand as written, but §4 is now much closer to the existing proof:
identical `clk`, identical `out`, weaker `inp`, reset actual replaced by a
fresh id with a defining constraint. Route A is correspondingly more likely
to close, and the §7 sequencing loses its first item.

---

## 2b. (historical) Obligation A — the extra `rst_ty` in the clock slot

**The delta.** Obc passes `[rst_ty] ⊔ ckty` where STC passes `ckty`. After
substitution, every generated constraint whose formal source mentions the
callee's `s_clk` gets `dlt(rst_ty)` added to its source. A *larger* source is
a *stronger* constraint, so this is the one delta that does not come for
free.

**Why it is sound.** Every constraint of a generated signature also mentions
`s_reset`. Hence the substituted source already contains the reset actual,
and the extra `rst_ty` is dominated:

- *Unreset call*: STC's reset actual is literally `[rst_ty]`, so the source
  already contains `dlt(rst_ty)`. Adding it again is idempotent — nothing to
  prove beyond the mention invariant.
- *Reset call*: STC's reset actual is `[rst_inst]`, and the TcReset
  constraint (post-`997438d`) is
  `([rst_ty] ⊔ ([rty] ⊔ rstckty)) ⊑ [rst_inst]`, so any `dlt` satisfying the
  system's constraints has `dlt(rst_ty) ⊑ dlt(rst_inst)`. The extra `rst_ty`
  is therefore below a term already present in the source.

  *This is the payoff of the July rule change.* Under the old (rst-seeded,
  no `base_ty`) TcReset rule the same domination argument still held for
  `rst_ty`, but the clock part did not line up with the pc, so the two
  generators disagreed syntactically at every reset site. Keep
  `997438d` — reverting it re-breaks this case.

**What is missing.** The domination argument needs, on the **STC** side:

```coq
constraints_mention ty cns := forall lhs y, In (lhs, [y]) cns -> In ty lhs
```

(`SecNLusTypingCorrectness.v:1479`) instantiated at `ty := sig.(s_reset)`
for every generated STC signature. That theorem does not exist yet for STC —
but its NLustre twin does, fully proved, and every ingredient is
signature-generic (i.e. does not mention NLustre syntax):

| lemma | location | reusable as-is? |
|---|---|---|
| `constraints_mention` (def) | `SecNLusTypingCorrectness.v:1479` | yes (move or re-state) |
| `simplify_mentions_other` | `:1618` | yes — pure `SymTypes.simplify` fact |
| `generate_constraints_mentions_reset` | `:1808` | yes — pure `SIG.generate_constraints` fact |
| `generate_constraints_mentions_clock` | `:2473` | yes |
| `generated_signature_constraints_mention_reset_scoped_env'` | `:2252` | **no** — NLustre-specific; port per-trconstr |
| `generated_signature_constraints_mention_reset_scoped_env` | `:2434` | ditto |

So the port is: replay the `..._scoped_env'` induction over `s_tcs` instead
of `n_eqs`, discharging four cases instead of three. Each case is a
two-liner (`in_merge_left` for the seeded `[rst_ty] ⊔ …` sources; the
`generate_constraints_mentions_reset` lemma for the two call cases). The
non-trivial side conditions (`~ In [rst_type] (map snd raw)`, `rst_type` not
among the eliminated `ds`) are exactly the ones already discharged in the
NLustre proof via `node_var_not_sec_gensym` and the `sec` vs `sec_reset`
prefix disjointness (`Ids.sec_neq_sec_reset`).

**Risk: low.** Mechanical port, ~250–350 lines, no new ideas.
**Bonus:** the same port at `ty := s_clk` (`mentions_clock`) is free and is
needed anyway if the NI transport is ever run on the Obc side.

---

## 3. Obligation B — weaker arguments (`translate_arg`)

**The delta.** `translate_arg ck e` (StcToObc `Translation.v:70–77`) either
emits `Valid x ty` (when `var_on_base_clock ck x`) or `translate_exp e`,
and `translate_exp` **drops `Ewhen` guards**. Those guards are variables of
the *instantiated* argument clock `instck ck sub xck`, which are not all in
`ckty`. Consequently `inptyp_obc` can be a strict subset of `inptyp_stc`.

**Why it is sound.** Smaller input types ⇒ smaller substituted sources ⇒
*weaker* constraints. For `preserves_on` we must satisfy the Obc side given
the STC side, so weaker is exactly the direction we want; formally we need
monotonicity of the input substitution in the actual (see §4/§5), never an
equality.

Note this is *not* the same absorption argument as
`translate_exp_type_correspondence` (already proved,
`SecStcObcTranslation.v`): there the dropped guards were variables of the
expression's own clock `ck`, recovered from `ckty`. Here the arguments live
on instantiated clocks, and the dropped guards need not be recoverable at
all — which is why the statement is an inequality rather than an equality.

**What is missing.** A `Forall2` plumbing lemma from `wc_trconstr`'s
call case:

```coq
Forall2 (fun '(x,(_,xck)) le => SameVar (sub x) le
          /\ exists lck, wc_exp vars le lck /\ instck ck sub xck = Some lck) ins es
```

to `Forall2 (fun stc_ty obc_ty => hm_ext dlt obc_ty ⊑ hm_ext dlt stc_ty)
inptyp_stc inptyp_obc`, by induction on the args with a per-expression
lemma `assign_exp_type (translate_arg ck e) ⊆ assign_exp_type e` (as
`hm_ext` bound). The `Valid` branch is trivial (`Valid x ty` and `Var x ty`
have the same security type — both are `Env.find x env`).

**Risk: low–medium.** Fiddly `instck`/`sub` plumbing, no conceptual gap.
~150–250 lines.

---

## 4. Obligation C — the valuation surgery (the real risk)

**The delta.** The existing call-preservation machinery,
`Signature_call_preserves` (`SecNLusStcTranslation.v:88–106`) and its proof
`signatures_preserved_reset_underlying_calls_from_good`
(`SecNLusStcTranslation.v:2117–2294`), assumes the two sides share
**identical `inp`, `clk`, and `out`**, differing only in the reset actual
(`srcrst` vs `rst_inst`). Its proof works by exact agreement of the two
`lat_valuation`s (`SIFSignature.v:1238`) on `sig_scope`, via
`lat_valuation_fields_agree_on_sig_scope_reset` (`:2044`).

Here `inp` is weaker (§3) and `clk` is larger (§2), so those *equalities*
become **⊑-monotonicity** obligations, and the ~180-line proof must be
generalized.

**The specific risk.** That proof pivots on
`generate_constraints_complete_good` (`SIFSignature.v:2801`), the
*backward* (completeness) direction: from satisfaction of the generated
constraints, reconstruct satisfaction of the callee signature's own
constraints under `upd_types_rev (upd_type (upd_type (upd_idents_rev …)))`.
Backward reasoning is where equality is genuinely load-bearing — with
weaker actuals you cannot in general reconstruct the formal-level
satisfaction. **This is the step that may resist generalization**, and it is
the only place in the whole bridge where I cannot promise the existing proof
shape survives.

**The `dlt'` construction** (needed in every route). `preserves_on` lets us
choose `dlt'` off the visible scope, and the Obc-only names are exactly the
fresh state ids (`sec_reset` gensyms, proved fresh and injective by
`generate_state_env_range` / `generate_state_env_injective` in
`SecObcTypingCorrectness.v`). Set:

```
dlt'(sty_o) := dlt(rst_inst_o)   if instance o is reset somewhere (TcReset o …)
dlt'(sty_o) := dlt(rst_ty)       if o is never reset
dlt'(x)     := dlt(x)            otherwise
```

This is well defined (state ids are distinct per instance and disjoint from
the scope) and immediately discharges both state-related goals: the reset
method's `[rst_ty] ⊑ [sty]` constraint, and the reset-call source
domination of §2. The never-reset branch is plan blocker **B5**, and the
`counter_paper` dump confirms it occurs in practice (instance `spd`).

---

## 5. Mitigation for §4 — the substitution-level route

If the generalization of `generate_constraints_complete_good` stalls, there
is a route that **never invokes the backward direction at all**.

**Key observation (verified in the tree).** The *forward* direction of the
substitution chain is already stated with `⊑`, not `=`:

```coq
(* SIFSignature.v:1085 *)
Definition inp_replace_cond dlt (x: ident) (v: ST) : Prop := hm_ext dlt v ⊑ dlt x.

(* SIFSignature.v:1087 *)
Lemma subst_constraints_inp_map_correct:
  subst_constraints_inp_map cs xs vs st = OK (cs', st') ->
  forall dlt, listSatisfiable dlt cs -> Forall2 (inp_replace_cond dlt) xs vs ->
              listSatisfiable dlt cs'.

(* SIFSignature.v:1074 *)
Lemma subst_ident_in_constraints_correct:
  subst_ident_in_constraints cs x v st = OK (cs', st') ->
  forall dlt, listSatisfiable dlt cs -> hm_ext dlt v ⊑ dlt x -> listSatisfiable dlt cs'.
```

Both take an **inequality** as the substitution side condition. So does the
type-level core, `subst_ident_in_type_correct1` (`:983`). This means the
whole forward pipeline — and therefore `generate_constraints_correct_inst`
(`:2464`), which chains exactly these lemmas — is *already* monotone-friendly
in the actuals.

**Route B, concretely:**

1. Take `dlt` satisfying the STC call constraints `nconst`.
2. Build `dlt'` as in §4, and let
   `V := lat_valuation dlt' sig_obc inptyp_obc pc [sty] outtyp`.
3. Establish `listSatisfiable V sig_obc.(s_constraints)` — **not** by
   completeness on the Obc side, but by transporting the callee's signature
   satisfaction from the STC side through the induction hypothesis
   (`signatures_preserved sig_stc sig_obc`, i.e. the already-established
   `preserves_on (sig_scope sig_stc)` between the two callee signatures) —
   this is the same move the existing proof makes at
   `destruct (Hpres _ Hsat_nsig) as (dlt_mid & Hagree_mid & Hsat_ssig)`.
4. Apply `generate_constraints_correct_inst` (forward, ⊑-friendly) to get
   `listSatisfiable V sconst`.
5. The formal→actual side conditions in step 4 are precisely
   `inp_replace_cond`-style inequalities, discharged by §3 (inputs), §2
   (clock, using the mention invariant) and the `dlt'` choice (reset).

The only genuinely new lemmas Route B needs are **substitution
monotonicity** statements of the form "if `hm_ext dlt v' ⊑ hm_ext dlt v`
then satisfaction after substituting `v'` follows from satisfaction after
substituting `v`" — which are strictly weaker than what the three lemmas
above already prove, and provable by the same inductions.

**Cost comparison**

| | Route A (generalize existing) | Route B (substitution-level) |
|---|---|---|
| reuses | `signatures_preserved_reset_underlying_calls_from_good` skeleton | forward lemmas only |
| new lemmas | monotone `generate_constraints_complete_good` | 3–4 substitution-monotonicity lemmas |
| risk | **medium-high** (backward direction) | **low** (forward direction already ⊑) |
| est. lines | 250–400 if it works | 400–600 |

**Recommendation:** attempt Route A for one focused session (it produces a
tidier `Signature_call_preserves`-shaped statement reusable by phase 6); on
the first sign that completeness resists monotonicity, switch to Route B
rather than fighting it. Route B is strictly more likely to close.

### Fallback of last resort (scope reduction)

If both routes stall, the theorem can be weakened without losing the
end-to-end story: state the bridge for **call-free class bodies plus a
per-call hypothesis** (`Signature_call_preserves sig_stc sig_obc` assumed
rather than derived), and discharge that hypothesis only for the concrete
programs the exporter runs on. The NI transport (phase 6) consumes
`Signature_head_consistent`, so it does not care how the call clause was
obtained. Document this as an explicit assumption if used.

---

## 5b. The remaining gap, decomposed (2026-07-31)

After the pc refinement (§2) and `tccall_preserv`, the *only* open proof
obligation of the translation is:

```coq
Theorem signatures_preserved_obc_calls_from_good:
  forall nsig ssig,          (* nsig = STC callee, ssig = Obc callee *)
    signature_good nsig -> NoDup (sig_scope nsig) ->
    signature_scoped ssig -> signatures_preserved nsig ssig ->
    Signature_call_preserves_obc nsig ssig.
```

It decomposes into three independent sub-tasks. **Sub-task A is the new
mathematical content; B and C are refactoring/porting.**

### A. Monotonicity of `generate_constraints` in the inputs

The one thing the existing machinery cannot express. Needed:

```coq
Lemma generate_constraints_mono_inp:
  Forall2 (fun t1 t2 => forall z, In z t2 -> In z t1) inp1 inp2 ->
  generate_constraints sig inp1 clk rst out st1 = OK (cns1, _) ->
  generate_constraints sig inp2 clk rst out st2 = OK (cns2, _) ->
  constraints_src_le cns1 cns2.
```

Then satisfaction descends by `constraints_src_le_satisfaction`.

**Already in place** (added 2026-07-31, all compiling):
- `SymTypes.merge_incl_mono` — `⊔` is monotone w.r.t. inclusion;
- `SecTypes.hm_ext_incl` — `hm_ext` is monotone w.r.t. inclusion
  (from `hm_ext_bound_from_members` + `hm_ext_list_in1`);
- `SecTypes.constraints_src_le` and
  `SecTypes.constraints_src_le_satisfaction` — the ordering "same
  targets, smaller sources" and the fact that satisfaction descends
  along it. **This is the semantic core of the whole argument.**

**DONE 2026-07-31** — `constraints_src_le` is now threaded through all
five stages, in `SIGNATURE_PROOFS`: `st_remove_mono`,
`subst_ident_in_type_mono` (monotone in *both* source and actual —
the delicate case `x ∈ ty1, x ∉ ty2` is handled),
`subst_inp_ident_in_constraint_mono`, `subst_ident_in_constraints_mono`,
`constraints_src_le_refl`, `subst_constraints_inp_map_mono`,
`subst_ident_constraint_mono`, `subst_ident_constraints_mono`,
`constraints_src_le_findST`, `subst_constraints_out_map_mono`, and the
top-level **`generate_constraints_mono_inp`**. All compiling.

**A′ — success transfer. DONE.** `generate_constraints_ok_change_inp`,
with `findST_none_targets`, `subst_ident_in_constraints_ok_change`,
`subst_ident_constraints_ok_change`, `subst_constraints_inp_map_ok_change`,
`subst_constraints_out_map_ok_change`, `final_lookup_ok_change`; plus
`mmap_cons_ok` / `mmap_nil_ok` added to `SecContext.v` (the introduction
counterpart of `sec_bind_inv`, needed to *construct* successful runs
rather than invert them).

*(original statement of A′)* To apply
the hoisted theorem at `inp1` on both sides we must know the *Obc*
signature also generates at `inp1`, given that it generated at `inp2`:

```coq
Lemma generate_constraints_ok_change_inp:
  length inp = length inp' ->
  generate_constraints sig inp  clk rst out st = OK (cns, st') ->
  exists cns' sa', generate_constraints sig inp' clk rst out sa = OK (cns', sa').
```

It holds because every error case in the chain inspects only a
right-hand side (malformed target, formal captured by a target,
`findST` hitting an existing target) — never an actual type. Drafted and
mostly proved; the pieces already written are `findST_none_targets`,
`subst_ident_in_constraints_ok_change`,
`subst_constraints_inp_map_ok_change`. **Remaining: the out-map stage**
— a `subst_ident_constraints_ok_change` twin (~40 lines, same shape as
`subst_ident_in_constraints_ok_change`, using
`subst_ident_constraints_rhs` for the target bookkeeping) and then the
final `mmap` lookup pass. Nothing was committed for A′: the draft had
`admit`s and was discarded rather than merged.

*(historical: the original five-stage plan)*
1. `subst_ident_in_type` monotone in the *actual*: `v2 ⊆ v1` ⇒
   `subst ty x v2 ⊆ subst ty x v1` (the `st_mem` branch is
   `(st_remove x ty) ⊔ v`, so `merge_incl_mono` applies).
2. `subst_ident_in_type` monotone in the *source*: `ty2 ⊆ ty1` ⇒
   `subst ty2 x v ⊆ subst ty1 x v`. Case `x ∈ ty1`, `x ∉ ty2`: LHS is
   `ty2 ⊆ st_remove x ty1 ⊆ (st_remove x ty1) ⊔ v`, using `x ∉ ty2`.
3. lift 1–2 to `subst_constraints_inp_map` (Forall2 induction);
4. lift 2 to the `clk` / `reset` / out-map stages (same actuals on both
   sides, so only source-monotonicity is used);
5. `findST` and the final `mmap`: targets are equal pointwise, so the
   looked-up sources stay ordered.

### B. Hoist the existing call-preservation theorem — **DONE**

With A, the theorem follows from
`signatures_preserved_reset_underlying_calls_from_good`
(`SecNLusStcTranslation.v:2105`) applied at `inp1` on *both* sides, then
A to descend to `inp2`. Note its conclusion prepends the reset-defining
constraint; ours does not, and `preserves_on scope c (x :: cs) ->
preserves_on scope c cs` discards it.

That theorem is **generic over signatures** — it mentions only
`signature`, `generate_constraints`, `preserves_on` — and sits in the
NLustre→STC file only by historical accident. Per the project rule
(§2c(2) of the progress doc) it should be **hoisted into
`SIGNATURE_PROOFS`** (`SIFSignature.v`), together with
`signatures_preserved` (`:84`), and `SecNLusStcTranslation.v` edited to
use the hoisted versions. Mechanical but touches a 2900-line file, so do
it as its own commit with a full rebuild.

### C. `signature_good` for generated STC signatures

Sub-task B's hypothesis `signature_good nsig` exists for NLustre
signatures (`generate_node_sig_good_from_local_env`) but **has no STC
analogue** — `SecStcTypingCorrectness.v` does not prove it. Needed:
`wf_constraints` plus `Permutation (map snd constraints) (map (fun ty =>
[ty]) s_out)` for `generate_sys_signature` output. The ingredients exist
(`generate_trconstrs_constraints_targets`, `simplify` shape lemmas); this
is a port of the NLustre proof.

**Estimated total: A ≈ 200–250 lines, B ≈ mechanical move + fixups,
C ≈ 150 lines.** None requires a new idea; A is the only part where the
existing lemma set is genuinely insufficient, and its semantic core is
now proved.

## 6. Empirical evidence

`velus -dsif examples/counter_paper.lus` → `counter_paper.o.sif` vs
`counter_paper.s.sif` (commit `7ef7492`, dumps reproduced in
`Stc2ObcSIF_progress.md` §1b):

- **Post-simplify Obc signatures are syntactically identical to the STC
  ones** for both classes, including the class `odometer` which exercises
  *both* a reset'd call (`dist`, via `TcReset`) and a never-reset call
  (`spd`).
- The pre-simplify difference is exactly the three deltas above: the Obc
  step-call source carries the extra `sec$13` (= `rst_ty`) — obligation A —
  and a `sec_reset$k` state id where STC has `rst_ty`/`rst_inst`; the
  reset-method constraints `[rst] <= state/mem` are the `dlt'` witnesses of
  §4.

This is not a proof, but it does mean: the target statement is true on real
translated programs, the `dlt'` construction is the one the generator
actually forces, and B5 (never-reset instances) behaves as predicted.

---

## 7. Recommended sequencing

1. ~~STC `constraints_mention s_reset`~~ **no longer needed** — removed by
   the generator refinement of §2 (already implemented and compiling).
2. **`translate_arg` monotonicity** (§3). Start here.
3. **Valuation surgery** (§4) via Route A, falling back to Route B (§5).
   With the refinement, the two sides now differ only in `inp` (weaker) and
   the reset actual, so the existing
   `signatures_preserved_reset_underlying_calls_from_good` is a much closer
   template than originally estimated.
4. Then: tcs-level assembly (whole-body `collapse` with reset-method
   constraints interleaved — B5 bookkeeping), signature-level lockstep
   (`Signature_consistent Gstc Gobc`), then phases 5 (scheduling) and 6 (NI
   transport) per `Stc2ObcSIF_progress.md`.

## 8. Verified lemma inventory (file:line at `9dc31e0`)

Mention machinery — `SecNLusTypingCorrectness.v`: `constraints_mention` 1479,
`simplify_mentions_other` 1618, `generate_constraints_mentions_reset` 1808,
`generate_constraints_mentions_clock` 2473, `…_mention_reset_scoped_env'`
2252, `…_mention_reset_scoped_env` 2434.

Substitution / valuation — `SIFSignature.v`: `subst_ident_in_type_correct1`
983, `subst_ident_in_constraints_correct` 1074, `inp_replace_cond` 1085,
`subst_constraints_inp_map_correct` 1087, `hm_ext_upd_type_subst` 1213,
`lat_valuation` 1238, `lat_valuation_agree_on_scope` 1250,
`lat_valuation_fields_agree_on_sig_scope_reset` 2044,
`generate_constraints_correct_inst` 2464, `generate_constraints_complete_good`
2801.

Bridge templates — `SecNLusStcTranslation.v`: `Signature_call_preserves` 88,
`eqn_preserv` 752 (reset-call case ~800–960),
`signatures_preserved_reset_underlying_calls_from_good` 2117,
`signatures_preserved_reset_calls_from_good` 2296, lockstep induction
`generate_all_signatures_consistent_scoped'` 2513.

Obc side — `SecObcTypingCorrectness.v`: `collapse_satisfaction`,
`generate_stmt_constraints_targets`, `generate_state_env_range`,
`generate_state_env_injective`, `generate_state_env_key_from_objs`.
`SecStcObcTranslation.v`: `generate_stmt_constraints_Control(_assign)`,
`translate_exp_type_correspondence`, `translate_cexp_constraints`,
`translate_tc{def,next,reset}_constraints`.

`preserves_on` — `SecTypes.v:869`.
