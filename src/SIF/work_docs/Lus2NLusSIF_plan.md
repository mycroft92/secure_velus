# SIF for Lustre: refinement security types and Lustre→NLustre preservation

Target branch: `constraint_gen` (or a new `Lus2NLusSIF`). **Status: not started.**

Sources of truth:

- **types and rules**: Prasad & Yerraguntla, *Normalising Lustre Preserves
  Security*, arXiv:2105.10687 (ICTAC 2021) — `~/Downloads/2105.10687v1.pdf`.
  Figures 5–11 are normative for this leg. Cited below as **[ICTAC]**.
- **proof architecture**: the NLustre→Stc leg already in `src/SIF`
  (`SecNLusTyping.v` / `SecNLusStcTranslation.v` / `SecStcNonInterference.v`)
  and the POPL draft in `../POPL_STC_translation_preservation`, cited as
  **[POPL]**.

Where the two disagree, [ICTAC] wins on *what the types are* and [POPL]/the
existing Coq wins on *how the preservation and noninterference proofs are
organised*. That split is the whole point of this document.

Constraint that governs everything: **no Coq file outside `src/SIF/` is
edited**, and **no existing `src/SIF` file is edited** except `vfiles`,
`docs/proof_outline.md` and `docs/NLustreCausalityBridge.md`. In particular
`SymTypes.v` is not touched — see §2.

---

## 0. Hard constraints, and the ledger that keeps them

Two constraints govern this leg. They are checked against every design
decision below.

**(H1 amended, 2026-09-12.)** The user lifted H1 for one specific change: the
naming pass now allocates **interface-first** -- clock, reset, inputs, outputs,
and only then locals -- so that an interface variable's security name does not
depend on how many locals its node has. `NameInterface.v` and
`SecNamingTotality.v` were edited and the whole NLustre-to-Obc chain rebuilt
green. H1 otherwise stands: any further edit to those files needs the same
explicit authorisation.

**What the reorder does and does not buy.** Within a node it works: an output
now keeps its name however many locals normalisation adds. Across nodes it does
not, because `generate_node_scoped_env'` threads one counter through the whole
program, so a node that gains a local shifts every name after it. Measured: a
two-node program whose *first* node gains one local moves the second node's
clock from `sec$9` to `sec$10` and its output from `sec$12` to `sec$13`, with
that node's own interface untouched. So independent allocation on the source
and on the normalized program still disagrees from the first such node onward;
see the options recorded with the milestones.

**(H1) Nothing from `SymTypes.v` downstream is changed. Additions only.**
No existing definition, notation, lemma statement or proof script in
`SymTypes.v`, `SecTypes.v`, `SIFSignature.v`, `SecContext.v`, `NameInterface.v`,
`SecCETyping.v`, `SecNLusTyping.v`, `SecNLusTypingCorrectness.v`,
`SecNLusTypingTotality.v`, `SecNamingTotality.v`, `SecSTCTyping.v`,
`SecStcTypingCorrectness.v`, `SecObcTyping.v`, `SecObcTypingCorrectness.v`,
`SecNLusStcTranslation.v`, `SecStcObcTranslation.v`, `SecNLusStcObcEnv.v` or
`NLustreCausality.v` is edited. New lemmas may be *appended* to those files
where a proof genuinely needs one, and only then.

**(H2) No downstream noninterference proof changes.**
`SecNLusNonInterferenceSupport.v`, `...Helpers.v`, `...ClockedStep.v`,
`SecNLusNonInterference.v`, `SecStcNonInterference.v` and
`SecObcNonInterference.v` are consumed as black boxes and not edited at all —
not even by appending.

### How the design satisfies them

| what this leg needs | where it comes from | touches an existing file? |
|---|---|---|
| refinement types `α{\|ρ\|}` | new `LST := ST * list constraint` in a new file | no — `SymTypes.ST` is untouched |
| ACUI union on `list constraint` | `SymTypes.constraint_merge` (`:1250`), already sorted + dedup | no |
| permutation-stable satisfaction | `SecTypes.listSatisfiable_Permutation`, `preserves_on_Permutation` (`:1185,1196`) | no |
| `simplify` and its correctness/completeness | `SymTypes.simplify`, `SecTypes.simplify_is_correct`, `simplify_complete` | no |
| block composition with private extras | `SecTypes.preserves_on_concat_scoped` | no |
| call replay ([ICTAC] Lemma 4) | `SIFSignature.generate_constraints_*` | no |
| `signatures_preserved`, `signature_fields_agree`, `scope_fresh` | `SIFSignature.v` (`:3408,255,288`) | no |
| `Signature_head_consistent` & friends | re-declared locally (§4) — they live inside the Stc module type | no |
| fresh per-call-site type variables | `SecContext.fresh_ident` (`:43`) | no |
| the naming monad for a Lustre allocator | client functor over `NAMEGEN` | no |
| NLustre noninterference | `SecNLusNonInterference.node_noninterference_outputs`, consumed | no |
| an NLustre `node_security` witness | *constructed* from its existing constructor | no |

The last row is the one that carries (H2). The whole Lustre leg reaches the
NI stack through exactly one door: it builds a `node_security` witness for the
transcribed NLustre node and hands it to the existing theorem. Nothing
downstream has to learn that Lustre exists.

### Correction: the fby rule must type both operands, 2026-09-12

§3 chose option (A) -- type the initial value of an `fby` as `⊥`, matching the
NLustre rule (NTfb) and keeping Leg A an equality. **That was unsound and has
been reverted.** In NLustre `EqFby x ck c e` carries a literal constant, so
typing only `e` is right. In Lustre `Efby` takes an arbitrary expression, and
`x = h fby 0` was given the constraint `κ ⊔ γ ⊑ β` -- no mention of `h`, though
`x`'s first value *is* `h`. The paper's (LTfby) joins both operands and was
right; the deviation was mine.

The equation generator no longer special-cases `fby`: it falls through to the
ordinary definition rule, whose expression case already joins both operands.

What it costs. The source constraint now mentions the initial value and the
target does not, because `to_constant` strips the `when`s and NLustre types a
constant. The source is strictly stronger -- the right way round -- but the two
constraint lists are no longer equal, so **Leg A is preservation, not
equality**, which is what [ICTAC] Theorem 1 claims anyway and what the
NLustre-to-Stc leg already lives with. Three of the four shapes stay exact.

Two things preservation needs that are not yet in place.

1. **The leg must run Lustre-to-NLustre.** The committed theorems run the other
   way, which was sound while the generators agreed and was justified by
   NLustre totality. It no longer suffices: the Lustre fby rule looks up the
   `when` variables of the initial value, which the NLustre rule never
   mentions, so NLustre success does not imply Lustre success. The
   noninterference pull-back wants the other direction anyway -- a secure
   Lustre node is one whose constraints are satisfied, and the NLustre node's
   must follow. So `to_lexp_assign_eq` and `to_cexp_assign_eq` need their
   converses; same induction.
2. **The `simplify` bridge.** Both halves exist -- `simplify_complete` pulls a
   raw valuation back, `simplify_is_correct` pushes one forward. Their side
   conditions (`wf_constraints` of the Lustre raw list, locals disjoint from
   the signature scope) are the Lustre analogues of what
   `SecNLusTypingCorrectness.v` proves for NLustre, and are the next thing to
   build.

Kept in `SecLusNLusTranslation.v`: the three exact shapes, and the inversion
lemmas for both sides, which the preservation proof reuses unchanged.

### Leg A status, 2026-09-13

Preservation runs Lustre-to-NLustre and reaches the node. Proved, no admits:

- `to_lexp_assign_rev`, `to_cexp_assign_rev`, `to_lexps_assign_rev` -- the
  converses of the expression lemmas, which is the direction preservation
  needs;
- `to_equation_entails_{def,fby,app,app_reset}` and the dispatcher
  `to_equation_entails`; `to_equations_entails` for a node's body;
- `entails_simplify` -- the bridge, from `simplify_complete` and
  `simplify_is_correct`;
- `to_node_sig_preserved` -- `signatures_preserved lsig nsig`.

`entails` records *two* things: the satisfaction implication, and that the two
lists have the same right-hand sides. The second is free -- every shape
constrains exactly the variables its equation defines, and only the delay's
left-hand side differs -- and it is what carries `wf_constraints` from the
NLustre side to the Lustre one, which the bridge needs.

### Leg A complete, 2026-09-13

Preservation runs Lustre-to-NLustre and reaches the whole program,
unconditionally. `SecLusNLusTranslation.v`, no admits, no new assumptions, and
no file outside it touched:

    to_global_signatures_entail :
      to_global G Hp = OK P ->
      LClo.wc_global G ->
      SECLNG.generate_lnode_scoped_env G = OK (envs, aux_names) ->
      generate_all_lsignatures_scoped_env G envs aux_names st = OK GLout ->
      SECNL.generate_all_signatures_scoped_env P envs aux_names = OK GNout ->
      Signature_entails GLout GNout

`Signature_entails GL GN` is the leg's relation: every callee found in `GL` is
found in `GN` under the same name with the same interface fields, and the two
instantiated call blocks entail. It is the Lustre analogue of
`Signature_consistent`, weaker in one place -- the reset actual is the same
expression on both sides here, so only the equal-actuals call clause is needed.

**The two globals.** The call shapes are the only ones that read a signature,
so they are the only ones the split touches. `call_block_step` is where it
happens: `Signature_entails` produces the callee's NLustre signature,
`generate_constraints_ok_from_good` shows the NLustre run exists at all -- it
reads only interface fields and the shape of the constraints, both of which
agree with a signature that has already generated -- and `call_block_entails`
relates the two blocks.

**Where the side conditions live.** Everything a call shape needs beyond the
two globals is in `call_context`, and every clause of it is about the *NLustre*
side. That is not a loss: transcription hands both generators the same actuals,
so `SecNLusTyping`'s scoping lemmas apply verbatim instead of being reproved
against Lustre clocking. Freshness moved there too --
`signature_fields_agree` makes the two signature scopes equal, so `scope_fresh`
transports back from `G_NL` to `G_L`.

**`signature_good` of the Lustre signature** is what the call rules want and
nothing on the Lustre side proves. It does not have to be proved there.
`wf_constraints` and `signature_good` read only right-hand sides, and what
`simplify` does to those is a function of the right-hand sides alone: `findST`
looks a target up, `subAll` drops the constraints targeting it and retargets
the rest at the names they already had. So the right-hand-side half of
`entails` survives elimination and carries `signature_good` back across
(`simplify_rhs_eq`, `signature_good_of_rhs`).

**The program level** is `generate_all_signatures_entails_scoped'`, the lockstep
induction of `generate_all_signatures_consistent_scoped'` with
`Signature_head_entails` in place of `Signature_head_consistent`. It carries
`secglobal_scoped`, `secglobal_good`, duplicate-free scopes and
`secglobal_scope_bounded_above` on the *NLustre* accumulator only -- nothing
separate is needed about the Lustre one, because `Signature_entails` keeps the
interface fields aligned. Each is re-established at a node by the facts
`generated_node_head_entails` already produces; scope-freshness comes from
splitting the naming run at the node.

The node lists are related by `transcribed` (a `Forall2` over `to_node`) rather
than by a `to_global` run, because the drivers generate over `rev nodes` and a
`Forall2` reverses where a `to_global` run does not.

**Module parameters added** to `SecLusNLusTranslation.v`: `SECNLUSTYPINGCORRECTNESS`,
`SECLNAMEGEN`, `LCLOCKING`, `TRCLOCKING`. The file remains a leaf -- nothing
imports it -- so nothing in the NLustre, Stc or Obc chain is affected.

**What is left for the noninterference pull-back.** Preservation is the
statement about generated signatures. Turning it into "a secure Lustre program
transcribes to a secure NLustre one" needs the Lustre analogue of
`SecNLusNonInterference.v`'s top-level statement, which is a separate leg.

### Decision: one naming pass (option A), 2026-09-12

Signature preservation needs the Lustre and NLustre signatures to have the
same interface fields. Reading `generate_node_sig`, each of those fields is a
function of exactly two things: the node's `n_name`/`n_in`/`n_out`, and the
naming environment. The first is preserved -- definitionally by
`to_node_name`/`to_node_in`/`to_node_out`, and by `node_iface_eq` through
`normalize_global_iface_eq`. So everything turns on the environment.

**Two ways to make the environment agree, and the choice between them.**

*Interface-first allocation alone is not enough.* The reorder committed today
makes an interface variable's name independent of *its own node's* locals, but
`generate_node_scoped_env'` threads one counter through the program, so a node
that gains a local shifts every name after it. Measured: a two-node program
whose first node gains one local moves the second node's clock from `sec$9` to
`sec$10` and its output from `sec$12` to `sec$13`, with that node's own
interface untouched. Independent allocation on the source and on the
normalized program therefore still disagrees from the first such node onward.
Fixing that would mean splitting allocation into an interface sweep and a
locals sweep, restating every lemma about `generate_local_env_for_node` across
two stages.

*The paper says not to bother.* (LTndef) reads "Let `α₁,…,αₙ, δ₁,…δₖ,
β₁,…βₘ, γ` be **distinct fresh type variables**" -- it does not say which, and
Theorem 1 then writes the *same* `ᾱ, γ, β̄` on both sides of normalisation. It
is entitled to that only because the rule lets you choose them: a signature is
a scheme and its variable names carry no content. The paper obtains the
coincidence by choosing, not by computing.

**So: the naming pass runs once, and every generator reads its result.** This
is the mechanised form of that choice, it is the discipline the Stc and Obc
generators already follow, and the interface fields then agree by computation
with nothing to discharge. `SecLNameInterface.v` keeps its value: with
`to_global_lscoped_env` the Lustre allocator, run on the normalized program,
*is* the NLustre one, so the Lustre typing can still be presented as
allocating its own names.

Consequences for `SecLTyping.v`, as implemented:

- `generate_lnode_sig` and `generate_all_lsignatures_scoped_env` take `envs`
  and `aux_names` as parameters, like `SECSTCTYPING` and `SECOBCTYPING`.
- They also take and return a `sec_state`, because unlike the NLustre
  generator this one is not `state_pure`: a nested call mints a name per
  result flow. Start the run at the naming pass's final state
  (`generate_lnode_scoped_env_st`) and every minted name is clear of every
  program variable's, both drawing `gensym` from `Ids.sec`.
- `simplify` must eliminate the minted names *as well as* the declared locals.
  `minted st0 st1` reads them back off the state the run consumed. A
  call-output name is local to the node's body exactly as a declared local is,
  and neither may reach the interface -- without this, `signature_scoped`
  fails and the interfaces stop matching. Working the `scaled` example is what
  surfaced this; the NLustre entry point passes only the locals, because
  minted names do not exist there.

**If the Lustre typing is ever wanted genuinely standalone**, the principled
route is not the two-sweep allocator but relaxing `signature_fields_agree` to
a *renaming* of the interface variables -- which is what the paper actually
means, and for which the machinery half exists already, since
`generate_constraints` instantiates a callee signature by substitution. The
cost is generalising `signature_fields_agree` and its uses through
`Signature_head_consistent`, the simplify bridge and the noninterference
transport, which reaches into the Stc and Obc legs.

### Where a new lemma about types goes

A standing rule for this leg, to keep (H1) mechanical rather than a judgement
call each time:

- a property of `SymTypes.ST` / `SymTypes.constraint` that is about the
  **NLustre or Stc level** → append to `SymTypes.v` / `SecTypes.v`;
- a property that is about the **Lustre level, or about the Lustre→NLustre
  bridge on types** → it goes in `SymLusTypes.v` (syntactic) or
  `SecLusTypes.v` (semantic), never in `SymTypes.v` / `SecTypes.v`.

`SymLusTypes.v` and `SecLusTypes.v` are assembled into one `LusTypes.v`
module, the way `Lustre.v` assembles `LSyntax`/`LTyping`/`LClocking`. That is
what keeps the two already-large base modules from growing.

### Where additions are foreseeable

Only two, both append-only, both to files named in (H1) and never to (H2):

1. `SymTypes.v` — possibly a `simplify` stability lemma under permutation of
   its input list, if Leg C's constraint order cannot be made to line up.
   Avoidable if the `preserves_on_Permutation` route (§2) suffices; try that
   first.
2. `SecTypes.v` — possibly `constraintSatisfiable_shrink_lhs` (a constraint
   with a larger left-hand side implies one with a smaller). Needed **only**
   if §5 option (B) is taken. Option (A) avoids it entirely.

If either turns out to need more than an appended lemma, stop and re-plan
rather than editing.

---

## 1. Scope: this is three legs, not one

[ICTAC] calls its target "NLustre", but its Figures 10 and 11 are Velus's
*unnesting* and *fby-initialisation* passes, which are `L.global → L.global`.
Getting to Velus's actual `NL.global` needs transcription on top. Reading
`Lustre/Normalization/Normalization.v:25` and `VelusCorrectness.v:54`:

```
L.global --unnest_global--> L.global --normfby_global--> L.global --to_global--> NL.global
   (full Lustre)              unnested              normalized              NLustre
        ^ Leg C                    ^ Leg B                  ^ Leg A
        [ICTAC] Fig 10             [ICTAC] Fig 11           not in [ICTAC]
```

| leg | Velus pass | [ICTAC] | what it costs SIF |
|---|---|---|---|
| **C** | `unnest_global` | Fig 10, `Xcnst`–`Xeqs` | **the novel leg.** de-nesting discharges refinement types into equations; fresh locals per subexpression |
| **B** | `normfby_global` | Fig 11 | one fby → three equations (`xinit`, `px`, `ite`); fresh locals, no calls |
| **A** | `to_global` | — | one-to-one; **constraint equality**, not preservation |

Each Velus pass has its own forward semantics theorem
(`unnest_global_sem`, `normfby_global_sem`, composed as
`normalize_global_sem` at `Lustre/Normalization/Correctness.v:2611`; then
`Transcription/Correctness.sem_l_nl:700`). All of them preserve `ins`/`outs`
**as the same stream objects**. That is what makes §6 cheap.

**Recommended order: type system → A → B → C.** A is the cheapest and
validates the new generator against the already-proved NLustre one; B is local
and call-free; C is the research contribution. Do not start C until A and B
compile.

---

## 2. The types: refinement types as a pair, `SymTypes.v` untouched

[ICTAC] §3 extends the NLustre type algebra with **refinement types**:

```
α, β ::= ⊥ | δ ∈ STV | α ⊔ β | α{|ρ|}          ρ ::= (θ ⊑ α)*
```

`α{|ρ|}` is "type α, provided ρ holds"; `s(α{|ρ|}) = s(α)` when `s` satisfies
`ρ` and is **undefined otherwise**. They exist for exactly one reason: a node
call *inside an expression* has to publish the callee's instantiated
constraints without an equation to hang them on (rule `LTncall`).

The current development has `SymTypes.ST := list ident` (sorted, dup-free) and
`constraint := ST * ST` (`SymTypes.v:11`). Changing `ST` would break every
NLustre, Stc and Obc proof. Do not.

**Design decision: represent `α{|ρ|}` as the pair `(α, ρ)`.**

```coq
(* new file SymLusTypes.v *)
Definition LST : Type := (SymTypes.ST * list SymTypes.constraint)%type.
Definition lbot  : LST := ([], []).
Definition lvar (d : ident) : LST := ([d], []).
Definition ljoin (a b : LST) : LST := (fst a ⊔ fst b, constraint_merge (snd a) (snd b)).
Definition lrefine (a : LST) (r : list constraint) : LST := (fst a, constraint_merge (snd a) r).
(* the hoisting rule, [ICTAC] Fig 5 line 4 *)
Definition lconstrain (a : LST) (b : ident) : list constraint :=
  constraint_merge [(fst a, [b])] (snd a).
```

`constraint_merge` is **already in `SymTypes.v:1250`** — a sorted merge over
`constraint_compare` whose `Eq` branch keeps one copy. It is therefore
associative, commutative, idempotent and unital on canonical lists: the ACUI
union Figure 5 asks for, already in the repo, no addition needed.

Under this representation **every equation of [ICTAC] Figure 5 holds
definitionally or by `constraint_union` being ACUI**:

| [ICTAC] Fig 5 | here |
|---|---|
| `α{||} = α` | `lrefine a [] = a` |
| `α1{|ρ1|} ⊔ α2{|ρ2|} = (α1⊔α2){|ρ1∪ρ2|}` | the definition of `ljoin` |
| `α{|ρ1|}{|ρ2|} = α{|ρ1∪ρ2|}` | associativity of `constraint_merge` |
| `vec(αi){|ρ|} = vec(αi{|ρ|})` | `map (fun a => lrefine a r)` |
| `{α{|ρ1|} ⊑ β{|ρ2|}} = {α⊑β} ∪ ρ1 ∪ ρ2` | the definition of `lconstrain` |
| substitution distributes | componentwise |

Should any Fig-5 equation resist a *syntactic* proof, there is a second line
of defence that also needs no changes: satisfaction of a constraint list is a
`Forall`, and `SecTypes.v:1185,1196` already proves
`listSatisfiable_Permutation` and `preserves_on_Permutation`. The Stc→Obc leg
already runs on that footing — its generated list is a permutation of the
source's, not equal to it. So the Fig-5 theory can be stated at satisfaction
level rather than syntactically wherever that is more convenient.

**Consequence: [ICTAC] Lemma 2 (confluence modulo AC, Knuth–Bendix completion,
strongly-coherent rewriting) is not mechanised at all.** It is a statement
about deciding equality of *terms* in the type algebra; choosing a canonical
representation discharges it by construction, exactly as [POPL]'s "Notes on
formalisation" says Lemma 1 is discharged by `sortST` today. Say this
explicitly in `docs/` — a reader of the paper will look for it.

`lconstrain` is where refinement obligations *leave* the type and enter the
constraint set, and it is the only place they can. That single choke point is
what keeps the rest of the development on the existing `constraint` type, so
`simplify`, `preserves_on`, `SIFSignature.generate_constraints` and every
correctness lemma in `SecTypes.v` apply unchanged.

**Degeneracy lemma** (needed by Legs A and B):

```coq
Lemma unnested_exp_no_refinement :
  unnested_exp e -> assign_lexp_type env e = Some tys -> Forall (fun t => snd t = []) tys.
```

After Leg C every `LST` has an empty refinement component, so `LST` collapses
to `ST` and Legs B and A never see a refinement type. Prove this early; it is
what lets the *same* generator serve all three Lustre stages.

---

## 3. `SecLTyping.v`: typing full Lustre

One generator, defined on the full `L.exp` — not on a normalized subset.
Section variables mirror `SECNLUSTYPING`'s (`G : secglobal`, `env : Env.t
ident`, `base_ty`, `rst_ty`) plus `cenv : Env.t (type * clock)`, the clock
environment `to_equation` consults (`Tr.v`, `to_node`).

### Expressions — `assign_lexp_type : L.exp -> Sec (list LST)`

Returns a **list**, one `LST` per flow: Lustre expressions denote flow lists
and [ICTAC] Fig 7 is componentwise throughout. It lives in `Sec`, not
`option`, because the call case mints fresh names.

| `L.exp` | [ICTAC] rule | result |
|---|---|---|
| `Econst c` | LTcnst | `[lbot]` |
| `Evar x _` | LTvar | `[lvar (env x)]` |
| `Eunop _ e _` | LTunop | type of `e` |
| `Ebinop _ e1 e2 _` | LTbinop | `ljoin` componentwise |
| `Ewhen es x b _` | LTwh | `map (fun a => ljoin a (lvar (env x))) tys` |
| `Emerge x ets efs _` | LTmrg | `θ ⊔ αi ⊔ βi` componentwise |
| `Eite e ets efs _` | LTite | `θ ⊔ αi ⊔ βi` componentwise |
| `Efby e0s es _` | LTfby | `αi ⊔ βi` componentwise |
| `Earrow e0s es _` | **not in [ICTAC]** | same as `Efby` — see §7 |
| `Eapp f es er _` | LTncall | see below |

### The call case — the novelty

`LTncall` gives `f(e⃗)` the type `β⃗{|ρ'|}` with `ρ' = ρ[γ'/γ][α'/α⃗]`. The
`β⃗` are per-call-site and must be **freshly minted**, because a nested call
has no declared variable to borrow a name from. `SecContext.fresh_ident`
(`SecContext.v:43`, `Ids.gensym Ids.sec`) already does this, and
`SIFSignature.generate_constraints` already performs exactly the substitution
`ρ[α'/α⃗][β'/β⃗][γ'/γ][κ'/κ]` and reorders the result into caller-output order.
So:

```coq
| Eapp f es er anns =>
    do argtys <- mmap assign_lexp_type es;          (* list LST, then flatten *)
    do sg     <- find_signature f G;
    do rstty  <- lreset_type er;                    (* see below *)
    do outs   <- fresh_idents (length anns);        (* the per-call-site β⃗ *)
    do cs     <- generate_constraints sg (map fst (concat argtys)) ckty rstty outs;
    ret (map (fun o => (([o] : ST),
                        constraint_union cs (union_all (map snd (concat argtys)))))
             outs)
```

Each output flow gets type `o_i` refined by the call's instantiated
constraints **plus** everything floated up out of the arguments — which is
`β{|ρ'|}` composed with Fig 5's `α1{|ρ1|} ⊔ α2{|ρ2|}` rule. Nested calls
compose because `ljoin` unions refinements; nothing special is needed for
depth.

`ckty` here is the type of the call's base clock, computed the way
`to_equation` computes it (`find_base_clock (L.clocksof es)`) so Leg A lines
up (§5).

**Where the per-call-site names come from.** `SecContext.fresh_ident`
(`SecContext.v:43`) mints `Ids.gensym Ids.sec n` -- the *same prefix*
`NameInterface.fresh_ident_gen` (`NameInterface.v:318`) uses for program
variables' security names. It has no users today, because every existing
generator is `state_pure` (`SecContext.v`, "State-pure computations"): they
look names up, they never mint. The Lustre call case is the first that must
mint, so the collision is real and would break every freshness and scopedness
fact downstream (`generate_node_env_sec_range`, `env_sec_bounded`, ...).

Adding a fourth prefix to `Ident.v` is out -- that file is outside `src/SIF`.
The fix needs no edit anywhere: **run the equation generator from the naming
pass's final state rather than from `SC.init_state`.** Every name it then
mints is `Ids.gensym Ids.sec n` with `n` at or above that bound, so it is
fresh from every program-variable name by the bound facts `NameInterface.v`
already proves (`generate_local_env_for_node_fresh_from_bound`,
`generate_node_scoped_env'_bounded`).

`generate_node_scoped_env` discards that final state, but
`generate_node_scoped_env'` -- which `SecNLusStcTranslation.v` already calls
directly -- returns it. `SecLNameInterface.v` therefore runs the primed form
and keeps the state, and `NameInterface.v` is not touched.

**Two degeneracy facts, not one.** On an unnested expression the generator
mints nothing and carries nothing, so *both* `lst_plain` (empty refinement,
`SecLusTypes.v`) and `state_pure` hold. They are what make Leg A an equality:
the NLustre generator is state-pure and its types are plain, and on the
normalized fragment so is this one.

**Reset in nested position is new work beyond both papers.** [ICTAC] has no
`reset` at all; [POPL] added reset-stacking but only for NLustre, where the
reset is an `(ident * clock)`. In full Lustre `er : option exp` is an
arbitrary expression (`unnest_reset` only makes it an `Evar` later). So
`lreset_type` must type an *expression* and join it onto the ambient reset the
way (NTrc) does:

```
lreset_type None       = [rst_ty]
lreset_type (Some er)  = [rst_ty] ⊔ (type of er)        (* refinements float *)
```

This is the one rule with no precedent in either paper. Flag it in `docs/`
and in the paper draft: it is the point where [ICTAC]'s refinement types and
[POPL]'s reset-stacking have to be combined, and neither source covers it.

### Equations — [ICTAC] `LTeq` plus reset

```
Γ ⊢ x⃗ =ck e⃗ :> { (κ ⊔ γ ⊔ αi ⊑ βi)i } ∪ (floated refinements)
```

i.e. `map2 lconstrain tys (get_mappings xs env)` after joining in
`[rst_ty] ⊔ ckty` — `lconstrain` does the hoisting, so the refinements land in
the constraint list automatically. The `κ` (ambient reset) is [POPL]'s
addition to [ICTAC]'s rule; keep it, the NLustre generator has it and Leg A
needs the two to match.

### Node and global

`generate_lnode_sig`, `generate_lnode_sig_scoped_env`,
`generate_all_lsignatures'`, `generate_all_lsignatures_scoped_env` — same
shapes and same names as `SecNLusTyping.v`, and the same `simplify` over the
node's local type variables ([ICTAC] `LTndef`, Fig 9 — which is the *same*
`simplify` as `SymTypes.simplify`, generalised there to types-and-constraints
pairs; our pair representation means the generalisation is free).

Generate over `rev nodes` for the accumulator reason recorded in
`docs/proof_outline.md`.

### Naming

`SecLNameInterface.v`: a functor `SECLNAMEGEN (Ids)(Op)(LSyn)(NAMEGEN)` that
reuses NAMEGEN's `Name` monad and `fresh_*` combinators — they are
`Definition`s inside the functor, so a client functor can use them and
`NameInterface.v` needs no edit. It provides `gather_linsts` (the Lustre
spelling of `NLSyntax.gather_inst_eq`) and `generate_lnode_scoped_env`, plus:

```coq
Lemma generate_lnode_scoped_env_to_global :
  to_global LG H = OK P -> generate_lnode_scoped_env LG = NAMEGEN.generate_node_scoped_env P.
```

which holds because `to_node` keeps `n_name`/`n_in`/`n_vars`/`n_out`
**definitionally** and `to_equation` keeps `xs` and `f`. This is what lets
every Lustre-side statement reuse the `envs`/`aux_names` the NLustre stack
already threads.

Across Legs B and C the environment does **not** stay equal — those passes add
locals. There the relation is `env ⊆ env'` plus freshness of the additions,
which is exactly the `node_scope_fresh_in_env` / extras discipline the Stc leg
already uses.

---

## 4. Preservation: what to reuse, what is new

[ICTAC] Theorem 1 is `s(ρ) ⟹ s(ρ')` — source constraints imply target
constraints, same direction as [POPL] Theorem `THM:STCSecurityTypePreservation`
and the same direction as `SecTypes.preserves_on`. So the existing vocabulary
applies verbatim:

- `signatures_preserved`, `signature_fields_agree`, `scope_fresh`,
  `call_subst_fresh`, `call_subst_scoped` — all in **`SIFSignature.v`**
  (`:3408`, `:255`, `:288`), reusable directly.
- `Signature_call_preserves`, `Signature_head_consistent`,
  `Signature_consistent` — these sit *inside* the `SECNLUSSTCTRANSLATION`
  module type (`SecNLusStcTranslation.v:109,114`), so using them would mean
  instantiating that functor and dragging Stc in. **Re-declare the three in
  the Lustre translation file** — they are three short definitions over
  `signature` and `preserves_on`. Duplication is the right trade here: it
  keeps the Lustre leg from depending on the Stc leg at all. A later refactor
  could lift them into `SIFSignature.v` alongside `signatures_preserved`,
  which is where the first one already migrated.
- `preserves_on_concat_scoped` (`SecTypes.v`) — **this is the load-bearing
  reuse**. The Stc leg built it so that translated blocks could be
  concatenated while each block's private *reset-instance extras* stayed
  outside the shared scope. In Leg C the fresh variables that
  `idents_for_anns` / `idents_for_anns'` / `unnest_noops_exps` /
  `unnest_reset` introduce play exactly that role. Same lemma, different
  extras.
- `SIFSignature.generate_constraints_correct_inst` /
  `generate_constraints_complete_good` — the call replay metatheory, which is
  [ICTAC] Lemma 4 (Security of Node Calls) in mechanised form. Already proved.
- `SymTypes.simplify` + `simplify_is_correct` / `simplify_complete` —
  [ICTAC] Lemma 3. Already proved.

What is genuinely new per leg:

**Leg A — `SecLusNLusTranslation.v`.** Equalities, not preservation.
`to_lexp`/`to_cexp`/`to_equation` are structural, `to_node` preserves the
interface definitionally, so with the generator written case-for-case against
them (§5) the generated `signature` values come out **equal**. Then
`signatures_preserved` is `preserves_on_refl`, and no analogue of
`generated_signatures_preserved_from_simplify_bridge_scoped` is needed. Est.
900 lines.

**Leg B — `SecLusNormFbyTranslation.v`.** [ICTAC] Fig 11. One source equation
`x =ck e0 fby e` becomes `xinit =ck true fby false`, `px =ck c fby e`,
`x =ck if xinit then e0 else px`, with `xinit`/`px` fresh. Two fresh locals per
fby, both defined once, both eliminated by `simplify`; the composite
constraint `γ ⊔ δ1 ⊔ α ⊔ δ2 ⊑ θ` reduces to the source's `γ ⊔ α ⊔ β ⊑ θ` by
`simplify_is_correct` case (1). No calls involved, so no signature replay.
This is the leg to cut your teeth on. Est. 1200 lines.

**Leg C — `SecLusUnnestTranslation.v`.** [ICTAC] Fig 10, Theorem 1. The real
one. Structure it as the Stc leg is structured:

1. `lexp_preserv` — one source expression, by induction on `unnest_exp`'s
   recursion, relating the source `LST` list to (target expression types +
   target equation constraints). **The induction hypothesis has to say that
   the refinement component of the source type is implied by the constraints
   of the generated equations.** That sentence is the whole theorem; write it
   down before writing any Coq.
2. `leqn_preserv` — one source equation, via `unnest_rhss` + `split_equation`.
3. `leqns_preserv_scoped` — the list fold, gluing with
   `preserves_on_concat_scoped`, accumulating the fresh idents of each block
   as extras (mirrors `eqns_preserv_scoped` and `eqns_reset_extras`).
4. `lnode_preserv_scoped`, then the simplify bridge, then
   `generate_all_lsignatures_consistent'` — the lockstep global induction,
   mirroring `generate_all_signatures_consistent_scoped'` step for step.

Est. 3000–4000 lines, i.e. comparable to `SecNLusStcTranslation.v`.

**The `is_control` flag.** `unnest_exp` takes `is_control : bool` and does
*not* allocate fresh variables for `Emerge`/`Eite` when it is set. Both
branches must be covered by `lexp_preserv`; the `is_control = true` branch is
the easy one (no extras), the `false` branch allocates. Do not try to unify
them — two cases, stated separately, like the ordinary/reset call split in the
Stc leg.

---

## 5. Leg A in detail: aim for equality

Write `assign_lexp_type` so that its `normalized_lexp` / `normalized_cexp`
cases coincide with `SecCETyping.assign_exp_type` / `assign_cexp_type` on the
transcribed expression:

```coq
Lemma to_lexp_assign_eq : to_lexp e = OK le -> assign_exp_type env le = Some a -> assign_lexp_type env e = ret [(a, [])].
Lemma to_cexp_assign_eq : (* same for cexp *)
Lemma to_equation_constraint_eq :
  to_equation cenv envo eq = OK eq' ->
  generate_leqn_constraint G env base_ty rst_ty cenv eq = generate_eqn_constraint G env base_ty rst_ty eq'.
Lemma to_node_sig_eq / to_global_signatures_eq : (* lift to node and global *)
```

Each of the four `normalized_equation` shapes
(`Lustre/Normalization/NormFby.v:392`) maps to one NLustre equation, so each
is a direct case split. Compute the clock the way `to_equation` does:
`find_clock cenv x` for `EqDef`/`EqFby`, `find_base_clock (L.clocksof es)` for
`EqApp`, and the reset `Evar`'s **annotation** clock for the reset call.
Keeping the two generators syntactically aligned is the standing invariant for
this development; it is what makes this leg equalities rather than a second
simplify bridge.

**One asymmetry to decide.** `to_constant` strips the `when`s off a `fby`
initial value, so the NLustre side loses the sampling variables' types. Two
options:

- **(A) recommended.** Match [ICTAC] Fig 11 and [POPL] (NTfb): the initial
  constant contributes `⊥`. Exact equality in all four cases. Not a real
  weakening — `add_whens` builds `e0` with exactly the `when`s of `ck`, so each
  `Γ(yᵢ)` is already joined in through `ckty`.
- (B) type `e0` fully. Equality is lost, the statement becomes `preserves_on`,
  and it needs a new lemma `constraintSatisfiable_shrink_lhs` plus a full
  simplify-bridge analogue.

Take (A). Note that this asymmetry is *created by Leg B*, so state the
`⊥`-for-constant convention once, in Leg B's rule, and let Leg A inherit it.

---

## 6. Noninterference: the pull-back, exactly as [ICTAC] Theorem 5

This leg does **not** re-attack the semantics. [ICTAC] Theorem 5's proof
sketch is: well-typed Lustre → (Theorem 1) well-typed NLustre → (Theorem 4)
NLustre noninterference → (Theorems 2,3: semantics preservation) Lustre
noninterference. We have Theorem 4 already
(`SecNLusNonInterference.node_noninterference_outputs`) and Velus has
Theorems 2 and 3. So:

```
LS.sem_node LG f ins outs                                      (two runs)
  --Normalization.Correctness.normalize_global_sem-->  LS.sem_node G' f ins outs
  --Transcription.Correctness.sem_l_nl-->              NLSC.sem_node P f ins outs
  --NL.CoindToIdx.implies-->     Indexed.sem_node P f (tr_Streams ins) (tr_Streams outs)
  --NLusSupport.sem_node_inv-->  bk, H, Forall Indexed.sem_equation, sem_vars
  --lnode_security_transfer-->   node_security P G envs aux n dlt_sig dlt_raw
  --node_noninterference_outputs--> history_low_eq on n_out
  --tuple_stream_low_eq_of_history_low_eq + conversion--> conclusion
```

Every arrow is forward and every arrow keeps `ins`/`outs` as the *same*
streams, so the transport is `nth_error`/`Str_nth` bookkeeping, not semantics.

`lnode_security_transfer` is the one real obligation: an inductive
`lnode_security` mirroring
`SecNLusNonInterferenceSupport.node_security` over the Lustre generators, and

```coq
Lemma lnode_security_transfer :
  l_to_nl LG = OK P -> to_node ln _ = OK n ->
  lnode_security LG GL envs aux ln dlt_sig dlt_raw ->
  node_security P G envs aux n dlt_sig' dlt_raw'.
```

Through Leg A the valuations are **the same** (constraints are equal).
Through Legs B and C they are not: `preserves_on` produces a new valuation
agreeing with the old on the visible signature scope. That agreement is
exactly what keeps `low_var` classification of the node's inputs and outputs
unchanged, so the low-equivalence hypothesis and conclusion still speak about
the same set of variables. `SecTypes.agree_on` + `preserves_on` already carry
this; do not invent a new relation.

Note the direction contrast, and write it in `docs/`: the Stc and Obc legs
**push** noninterference forward from NLustre to their targets; this leg
**pulls it back** to the source, because NLustre is downstream here. [POPL]
`stc_correctness.tex:11` records the same observation about the two papers.

Exported theorem (mirrors
`SecStcNonInterference.translated_system_noninterference_outputs` in shape):

```coq
Theorem lnode_noninterference_outputs :
  ... ->
  lnode_security LG GL envs aux_names ln dlt_sig dlt_raw ->
  lnode_behavior LG ln ins  outs  ->
  lnode_behavior LG ln ins' outs' ->
  <base clocks agree> ->
  lustre_stream_low_eq ty_env dlt_sig t (map fst ln.(n_in))  ins  ins' ->
  lustre_stream_low_eq ty_env dlt_sig t (map fst ln.(n_out)) outs outs'.
```

with `lnode_behavior LG ln ins outs := LS.sem_node LG ln.(n_name) ins outs /\
LCS.sem_clock_inputs LG ln.(n_name) ins` — the second conjunct is what both
`normalize_global_sem` and `sem_l_nl` demand.

Carry the same source-to-target direction note the other exported theorems
carry: hypotheses constrain *Lustre* runs, conclusion constrains *Lustre*
outputs, even though every transport lemma inside reads NLustre-ward.

### Causality

`sem_l_nl` wants `Forall LCA.node_causal`; the NI theorem wants
`NLCaus.nl_global_causal`. `docs/NLustreCausalityBridge.md` already specifies
the missing file:

```coq
Theorem to_global_causal : to_global G H = OK P -> Forall LCA.node_causal G -> NLCaus.nl_global_causal P.
```

`normalize_global_causal` supplies the Lustre side for real programs.
**Deferrable** — until `SecLusNLusCausality.v` exists, carry
`nl_global_causal P` as an extra hypothesis and say so in the docs.

---

## 7. Beyond both papers — call these out explicitly

Four things this mechanisation must handle that neither paper covers. Each
needs a paragraph in `docs/` and, eventually, in the paper draft.

1. **`Earrow`.** Not in [ICTAC]. Type it like `Efby` (componentwise join);
   `normfby_global` turns it into `fby` + `ite`, so Leg B must cover it too.
2. **Reset in nested position** (§3). `Eapp`'s reset is an arbitrary
   expression in full Lustre. This is where [ICTAC]'s refinement types and
   [POPL]'s reset-stacking meet, and neither source says how.
3. **`unnest_noops_exps`.** Unnesting introduces *further* fresh variables for
   call arguments that are not "noops" under the callee's input clocks
   (`Unnesting.v:1960`). More extras for `preserves_on_concat_scoped`; no new
   idea, but it is not in Fig 10.
4. **`is_control`** (§4). Fig 10 has no analogue of the control-position
   optimisation, which changes whether `Emerge`/`Eite` allocate fresh
   variables.

And one thing the mechanisation does *not* need: **[ICTAC] Lemma 2**
(confluence modulo AC / Knuth–Bendix completion). §2 discharges it by
representation.

---

## 8. Files, in `vfiles` order

Insert after `SecNLusTypingTotality.v`, before `SecSTCTyping.v`: the leg
depends on the NLustre generator and on nothing downstream of it. `_CoqProject`
is generated — add to **`vfiles`** and re-run `./configure`.

| # | file | mirrors | est. |
|---|---|---|---|
| 1a | `SymLusTypes.v` | `SymTypes.v` (syntactic layer) | 900 |
| 1b | `SecLusTypes.v` | `SecTypes.v` (semantic layer) | 700 |
| 1c | `LusTypes.v` | `Lustre.v` (module assembly) | 80 |
| 2 | `SecLNameInterface.v` | `NameInterface.v` node-level allocators | 250 |
| 3 | `SecLTyping.v` | `SecNLusTyping.v` | 1400 |
| 4 | `SecLTypingCorrectness.v` | `SecNLusTypingCorrectness.v` | 900 |
| 5 | `SecLusNLusTranslation.v` (Leg A) | — | 900 |
| 6 | `SecLusNormFbyTranslation.v` (Leg B) | `SecNLusStcTranslation.v` | 1200 |
| 7 | `SecLusUnnestTranslation.v` (Leg C) | `SecNLusStcTranslation.v` | 3500 |
| 8 | `SecLusNLusCausality.v` | spec in `docs/NLustreCausalityBridge.md` | 400 |
| 9 | `SecLusNonInterference.v` | `SecStcNonInterference.v` | 500 |
| 10 | `SecLusConstraintExport.v` | `SecNLusConstraintExport.v` | 200 |

`Instantiator.v:17,25` already exposes `L` and `TR`, so file 10 is a copy of
`SecNLusConstraintExport.v` with `NL.Syn` → `L.Syn`.

Docs, one per Coq file (house rule), plus:

- `docs/SymLusTypes.md` — the syntactic layer and the confluence result (§2).
- `docs/SecLusTypes.md` — the semantic layer: partial ground instantiation,
  satisfaction, and the bridge to `SecTypes.preserves_on`.
- `docs/Lus-noninterference-proof.md` — must state §6's push/pull contrast.
- update `docs/proof_outline.md` (new "Source Language Leg" section) and
  `docs/NLustreCausalityBridge.md` once file 8 lands.

---

## 9. Milestones

0. **Done.** `SymLusTypes.v` (algebra + confluence, no axioms), `SecLusTypes.v`
   (semantics, `lconstrain_sound`), `LusTypes.v`, `SecLNameInterface.v`
   (`to_global_lscoped_env`), interface-first allocation, `SecLTyping.v`
   through expression, equation, node and global level, and **Leg A complete**
   in `SecLusNLusTranslation.v`, ending at `to_global_all_signatures_eq`:
   on a program that transcribes, the Lustre generator produces the *same*
   signature global as the NLustre one.

   Three notes for the legs still to come.  Reduce by stepping binds
   (`bind_OK`, `bind2_OK`) and the per-shape reduction lemmas, never by a
   blanket `simpl` -- that unfolds `SymTypes.merge` into its inner `fix` on
   one side of a goal only.  Write generators with nested matches, on the
   expression list before the defined variables, or the `[x]` patterns leave
   the term stuck on any equation whose variable list is not literal.  And
   state these theorems NLustre-to-Lustre: equality of the two `Sec`
   computations is false where generation fails, since the generators report
   different messages, and the NLustre totality theorem makes the one
   direction sufficient.

   Next: Leg B (`normfby_global`), then Leg C (`unnest_global`).

1. `SymLusTypes.v` compiles; Fig-5 rewriting confluent, `lty_eq a b <-> norm a = norm b`.
1b. `SecLusTypes.v` compiles; Lemma 1 (soundness) proved; degeneracy lemma proved.
1c. `LusTypes.v` assembles the two.
2. `SecLNameInterface.v` compiles; `generate_lnode_scoped_env_to_global` proved.
3. `SecLTyping.v` compiles with its structural lemmas `admit`ted.
4. **Leg A equalities proved.** This is the first real checkpoint: it says the
   new generator agrees with the already-verified NLustre one. If exact
   equality does not close here, fall back to §5-(B) and re-plan.
5. Back-fill `SecLTyping.v` / `SecLTypingCorrectness.v` from the equalities.
6. **Leg B.** First genuine `preserves_on` with fresh extras, call-free.
7. **Leg C.** Write `lexp_preserv`'s statement before any tactic.
8. `SecLusNonInterference.v` — the exported Lustre theorem.
9. `SecLusNLusCausality.v`; drop the extra hypothesis.
10. `SecLusConstraintExport.v`; run it on `tests/`.

Commit at each milestone, plain messages, no AI attribution.

---

## 10. Build protocol

Compile **only** in docker container `funny_franklin`; `/workspace` is a copy,
not a mount.

```
# new file: add to vfiles first (git-tracked; _CoqProject is generated)
docker cp vfiles           funny_franklin:/workspace/vfiles
docker cp src/SIF/F.v      funny_franklin:/workspace/src/SIF/F.v
docker exec funny_franklin bash -lc 'cd /workspace && ./configure -clightgen x86_64-linux'
docker exec funny_franklin bash -lc 'cd /workspace && make -j4; echo $?'
```

`make <path>.vo` is **not** a valid target — it exits 0 having done nothing.
Only bare `make` is evidence. Single-file iteration via
`coqc <the -R lines of _CoqProject> src/SIF/F.v`, but always finish with
configure + `make`.
