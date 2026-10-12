# Lustre → NLustre security preservation (the Lustre leg)

## Goal

Security types for Lustre, generated from the elaborated source program, such
that noninterference proved for the transcribed NLustre program (see
`Non-interference-proof.md`) transfers back to the source.  The Lustre leg has
three parts: a constraint generator for Lustre (`SecLTyping.v`), preservation of
the generated signatures across the two normalisation passes (unnesting, then
`fby` normalisation), and the bridge to the NLustre signatures
(`SecLusNLusTranslation.v`).

## Files (build order)

| File | Content |
|------|---------|
| `SecLusTypes.v` | flow types for Lustre expressions (`LST`), `ambient`, `lconstrain` |
| `SecLNameInterface.v`, `SecLNamingTotality.v` | the Lustre naming pass (`generate_lnode_scoped_env`), its totality and its range/injectivity facts |
| `SecLTyping.v` | `assign_lexp_type`, the equation rules (`generate_l{gen,def,call,one,split,eqn,eqns}_constraint`), `generate_lnode_sig`, `generate_all_lsignatures'` |
| `SecLusUnnestingBase.v` | monotonicity of the security counter (`sec_le`, `minted`), rootedness, the window definitions `source_*_scoped_upto` |
| `SecLusUnnestingExpr.v` … `SecLusUnnestingNodes.v`, `SecLusUnnesting.v` | Leg U: the unnesting pass preserves the generated constraints (`preserves_on`), expression → right-hand side → equation → node; `call_weakens` and the lockstep induction over a program |
| `SecLusNormFby.v` | Leg I: the same for `fby` normalisation, and `normalize_signatures_weaken` composing the two legs |
| `SecLusTypingCorrectness.v` | structural facts about generated Lustre signatures (below) |
| `SecLusNLusTranslation.v` | Lustre signatures entail the NLustre ones of the transcribed program |
| `SecLusConstraintExport.v`, `SecLusNonInterference.v`, `SecLusNonInterferenceStreams.v` | the dump driver and the noninterference corollaries |

All of these compile with no `Admitted`.

## Facts about generated signatures (`SecLusTypingCorrectness.v`)

Per node, against the naming of the node's own program:

- `generate_lnode_sig_good` — one constraint per output, targets exactly the outputs;
- `generate_lnode_sig_scoped` — every name mentioned is in the signature scope;
- `generate_lnode_sig_scope_nodup` — the scope has no duplicates;
- `generate_lnode_sig_rooted` — the clock and reset formals are sources of every constraint.

Per program:

- `generate_all_lsignatures_inv` — the four facts above hold for every signature the driver
  publishes, by a lockstep induction over the naming run and the signature run
  (`lsig_inv`, `lsig_step`).  Different nodes cannot interfere because the
  counter separates them: an accumulator's scopes lie below the naming state
  at the node being typed, the node's own names above it.

The naming facts the fold reads off the run are `generate_local_env_for_lnode_facts`
(injective, values are `sec` names inside the node's stretch of the counter,
the two auxiliary names first).

## The preservation interface

`call_weakens G1 G2` says that, for every instantiation that is fresh
(`call_subst_fresh`) with distinct outputs, the block built from a signature of
`G1` is entailed by the block built from the same-named signature of `G2`, and
the two signatures have the same scope.  It is transitive, and
`sig_call_weakens_from_good` produces its per-node step from the signature
facts above.  Freshness is *not* assumed for every instantiation the block
builder accepts (it accepts actuals containing a callee formal); it is asked of
the instantiations a run makes:

- `eapp_fresh_prop`, `lcall_fresh_prop` — the call rules of the typing run and of
  the equation rules, from a start state at or above the node's naming state
  `lo`, with distinct left-hand sides and a reset type of the two shapes the
  rules use.  Proved: `eapp_fresh_prop_holds`, `lcall_fresh_prop_holds`.

The Section hypotheses of Leg U (`SecLusUnnestingEquations/Streams/Nodes.v`)
are restricted to the source node's own variables, expressions and states:

| Hypothesis | Guard | Discharge |
|------------|-------|-----------|
| `source_{types,lexps,lexps_carried}_scoped_upto` | `wc_exp P vars`, start state ≥ `stLo`, end ≤ `stF` | `source_*_scoped_upto_holds` (from `lexp_scoped_tgt_all_wc`) |
| `clk_types_scoped` | `wc_global P`, `wc_exp`, `clk_src` (or a source variable's clock) | `clk_types_scoped_holds` |
| `env_range_scoped` | the variable is a source variable | by definition of the declared names |
| `sig_actuals_fresh` | actuals are caller-side names (`caller_name`) | `sig_actuals_fresh_holds` |
| `clk_types_defined` | — | `clk_types_defined_holds` under `no_anon_clocks` |

`scope` is the declared names of the source node plus the window
`minted stLo stF`; the images of the variables unnesting creates are
deliberately outside it.

The scalar-ambient chain (`carries_*`, `unnest_node_step`) quantifies over every
program and carries `scalar_wcg : forall P, wc_global P`; it is kept for the
lemmas it shares, but the pointwise chain (`*_streams`, `unnest_node_step_streams`)
is the one to instantiate.

## Assumptions and open items

1. **Source expressions (`src_exp vars AN`).**  The call case reads two facts that are
   properties of the elaborated program, not of every well-clocked expression: a nested
   call's output names are the node's anonymous streams (`AN`, i.e. `anon_in_eqs`; `n_nodup`
   keeps them off the declared variables, `env_key_not_anon` off the environment), and a
   call's arguments are clocked over the declared variables.  `src_exp` is a predicate on
   the expression, closed under subexpressions (`imm_sub`, `src_exp_imm`), threaded through
   the pointwise expression and equation chains (`carries_at_streams`, `rhs_carries_streams`,
   `eqn_carries_*_streams`, `eqns_carries_streams`, `node_carries_streams`,
   `unnest_node_step_streams`).  The Section hypotheses it replaces (`clk_types_defined`,
   `call_anon_not_env_key`, universal over expressions and programs) were unsatisfiable;
   what remains are the satisfiable `env_total` and `env_anon`.  The scalar chain
   (`carries_exp`, `unnest_node_step`) still carries the old universal hypotheses and is
   kept only for its shared lemmas.
2. (merged into 1.)
3. **Node instantiation of Leg U** (the remaining Section hypotheses: moved names
   outside `scope`, the canonical ambients, the generation bounds) is not
   written.
4. **`sig_inputs_ok GL P`** — a callee's signature inputs line up with its node's
   inputs and its constraints are closed under the declared clocks.  The
   per-equation input covers call-free equations only.
5. **Composition theorem**, noninterference half: chaining the result below with
   `lnode_noninterference_outputs_generated`.  The signature half is
   `Check.source_signature_entails` (`SecLusConstraintExport.v`): from
   `sigs_preserved GS GT` (both Lustre legs), `Signature_entails GT GN`
   (`to_global_signatures_entail`), and per-signature facts (source good with
   duplicate-free scope, NLustre scoped) it gives `Signature_entails GS GN`.
6. The signature-fold facts assume each node is typed against the naming of its
   own program.  For source nodes typed against the normalised program's naming
   only `good` and the duplicate-free scope carry over; scoped and rooted would
   need the guarded forms.

## Pitfalls that cost time

- `eq_refl` / `eq_sym` are shadowed by `Env`'s; use `Logic.eq_refl` / `Logic.eq_sym`.
- `rewrite` fails between two facts that print identically when the two `snd`s
  have different (convertible) type arguments (`ST` vs `list ident`); `destruct`
  the pair and `cbn [snd]` instead.
- A bare `findST` in the Lustre files is `SIG`'s, not `SymTypes'`.
- `length` is `String.length` in these files; write `List.length`.
- A bare `subst` after `inversion` can eliminate the variable you meant to `subst`
  later; name the equations.
- Section variables are generalised only when used, in declaration order; positional
  hypothesis lists (`Local Notation`s, explicit applications in `Nodes.v`) must
  follow.
