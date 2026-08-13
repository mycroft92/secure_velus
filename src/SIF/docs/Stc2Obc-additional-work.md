# Crossing the Imperative Frontier

*What the Stc-to-Obc security bridge required beyond the NLustre-to-Stc one*

## Abstract

Both compilation phases of the security-signature development are proved by the
same schema: generate a symbolic constraint signature on each side, prove the
target signature preserves the source one on the shared scope, and lift the
per-construct result to whole programs by a lockstep induction.  Applied to
NLustre-to-Stc, that schema is nearly mechanical -- the two constraint
generators are syntactically aligned, so most cases close by matching the two
monadic expressions.  Applied to Stc-to-Obc it is not.  The translation stops
being a relabelling of one dataflow form as another and becomes a compilation
into an imperative language: clocks become control flow, a control expression
becomes a decision tree, guards are deleted, a system becomes a class with two
methods, and one of those methods emits constraints for names the source never
mentions.  This note isolates the six places where the second bridge needed
genuinely new mathematics rather than a port, states what was proved in each,
and records the two engineering costs -- an extra compiler pass in the middle
of the chain, and the absence of a well-formedness record on the target -- that
the first bridge never had to pay.

## 1. The common schema

Write $C_{src}$ and $C_{tgt}$ for the raw constraints generated on each side of
a phase and $\Sigma$ for the *signature scope*: inputs, outputs, and the two
auxiliary names $\beta$ (base clock) and $\rho$ (reset).  The relation both
bridges establish is

$$
 \mathit{preserves\_on}\;\Sigma\;C_{src}\;C_{tgt}
 \;\;\equiv\;\;
 \forall\delta \models C_{src}.\;\exists\delta'.\;
   \delta \approx_\Sigma \delta' \;\wedge\; \delta' \models C_{tgt},
$$

any source valuation extends to a target one agreeing on the shared scope.
`signatures_preserved` adds field agreement and moves the statement onto the
*stored* (collapsed and simplified) signatures; `Signature_head_consistent`
packages one aligned pair; `Signature_consistent` lifts it to whole globals, and
is what the noninterference files consume.

The schema is identical on both bridges.  What differs is everything underneath
it.

## 2. Six new obligations

### 2.1 The clock leaves the rule and enters the program counter

In Stc a transition constraint carries its clock explicitly, and
`generate_trconstr_constraint` reads the clock's security type $K(ck)$ as one
join argument.  Obc has no clocks: `Control ck s` expands the clock into nested
`Ifte`s, and Obc statement typing accumulates a *program counter* type across
those branches.  The two sides therefore compute the same join by different
means, and the bridge needs a lemma saying so.  That is `clock_pc`, the pc
accumulated by walking a clock, together with

$$
 C_{Obc}(pc_0 \sqcup [\beta],\; Control\;ck\;s)
   \;=\; C_{Obc}(pc_0 \sqcup K(ck),\; s)
$$

(`generate_stmt_constraints_Control_assign`, with its inversion
`generate_stmt_constraints_Control_inv` used to recover the clock type from a
*successful* Obc run rather than assuming it).  Under an entry pc of
$[\mathit{clk\_ty}]$ this makes the pc at every translated leaf exactly the Stc
clock type -- the fact every per-transition case then rests on.  Nothing in
NLustre-to-Stc corresponds to this: there, the clock is an argument on both
sides.

### 2.2 One constraint becomes many, and must be collapsed back

`translate_cexp x ce` compiles `Emerge`/`Eite` into a decision tree with an
`Assign x` at each leaf, so the Obc generator emits *one constraint per leaf*,
all with target $[x_t]$, where Stc emitted a single constraint.  Their sources
join to exactly the Stc source.  Recovering the single constraint is what
`collapse` does, and `preserves_on_collapse` is what lets a preservation result
be moved onto the collapsed list.  The join reassociation itself is
`merge_factor`, `merge_rotate`, `merge_swap` and `merge_cong_under`, with
`translate_cexp_constraints` as the shape theorem.  NLustre-to-Stc has a
one-to-one correspondence at this level and needs none of it.

### 2.3 Guards are deleted, so call actuals shrink

`translate_exp` drops `Ewhen` nodes: the guard's contribution is already in the
clock, which `Control` compiles separately.  For an ordinary expression this is
harmless -- `translate_exp_type_correspondence` shows
$K(ck) \sqcup T(e) = K(ck) \sqcup T_O(\mathit{translate\_exp}(e))$ -- but for a
*call argument* it is not, because the argument type is handed to the callee's
signature, and the two calls now instantiate the same signature at **different**
actuals: the Obc ones are pointwise contained in the Stc ones
(`translate_arg_type_incl`, `translate_args_type_incl`).

This forced the call-preservation rules to be re-proved at a strictly greater
generality: over `inp_le` (pointwise containment of input actuals) rather than
equality.  The ingredients are `generate_constraints_ok_change_inp`, the source-ordering
`constraints_src_le` with `constraints_src_le_satisfaction` (`SecTypes.v`), and
the monotonicity theorem `generate_constraints_mono_inp` saying that shrinking
an input actual can only shrink constraint sources, hence only weaken them.  The resulting rules `call_preserves_eq` and
`call_preserves_rst` were then hoisted into `SIGNATURE_PROOFS` and **shared by
both bridges**: NLustre-to-Stc is the degenerate case where the containment is
an equality.  This is the one place where the second bridge's work improved the
first.

### 2.4 Three call cases, not two, and one of them owns a private name

Stc-to-Obc has to split on how the system treats each instance -- and
`reset_consistency` makes that split exactly the call's $rst$ flag:

| case | Stc reset actual | Obc reset actual | consequence |
| --- | --- | --- | --- |
| $rst = \mathit{true}$ | $[\iota(i)]$ | $[\iota(i)]$ | same actual; equal-actuals rule; $\iota(i)$ may sit in the shared scope (`tccall_reset_preserv_eq`) |
| $rst = \mathit{false}$, $xs \neq []$ | $[\rho]$ | $[\iota(i)]$ | the `rst` rule *produces* $[\rho] \Rightarrow [\iota(i)]$, which is precisely the reset method's constraint for that instance; the block owns it (`tccall_unreset_preserv_rst`) |
| $xs = []$ | $\emptyset$ | $\emptyset$ | both generators are silent, yet $i \in c\_objs$, so the reset method still constrains $\iota(i)$ and the block discharges it alone (`preserves_on_reset_only_extra`) |

The first bridge has a two-way split (ordinary / reset application) in which the
target-only name is always an Stc-side reset auxiliary that no other equation
can mention.  Here the private name is an *Obc* name that a second block -- the
reset method -- also constrains, which is what makes ownership a real question.

The design that resolves it is to mint the instance security name **once**, in
the shared name generator (`ninst` in `node_aux_names`, read by
`get_node_inst`), so that
$\mathit{reset}(s) = \mathit{state}(s) = \iota(s)$ *by construction* and no
hypothesis relating two environments appears anywhere in the bridge.  That is a
change to the naming pass made for this leg alone.

### 2.5 The target has constraints the source cannot see

The Obc reset method emits $[\rho] \Rightarrow [\Gamma(x)]$ for every memory and
$[\rho] \Rightarrow [\iota(o)]$ for every object.  Stc constrains the memories
(each has a `TcNext` whose source contains $\rho$) and the instances it resets
(each has a `TcReset`), but says nothing at all about the instances it never
resets.  So the target's constraints split three ways
(`reset_body_constraints_classified`):

- **entailed**: memories and reset instances.  `reset_shared_targets` finds a
  source constraint with the same target whose source already contains $\rho$,
  so `reset_constraint_entailed` discharges them under *any* scope-agreeing
  valuation.  `preserves_on_app_reset_shared` appends them for free.
- **owned**: unreset instances, handled by their own call block as above.

Because the private names are now per-block and each block must be checked
scoped against *its own* extras, the binary `preserves_on_concat_scoped` of the
first bridge is not enough.  The n-ary `preserves_on_concat_list` (with
`constraints_scoped_concat`) was added, along with the pointwise augmentation
`zip_app` that attaches each block the reset-method constraints of the instances
it owns, and `preserves_on_incl` to cut the proved target -- which mentions each
Obc constraint at least once -- back down to the generated list.

The consequence at signature level is that **the two hidden sets differ, and
must**: Stc hides $locals \cup lasts \cup \{\iota(o) \mid o\text{ reset}\}$,
Obc hides $locals \cup mems \cup \{\iota(o) \mid o \in c\_objs\}$.  `simplify`
may only eliminate a name that has a defining constraint, and Stc never
constrains an instance it does not reset.  `preserves_on_simplify_bridge` is
therefore stated with two *unrelated* hidden sets -- a generalisation the first
bridge never needed.

### 2.6 The target carries no well-formedness with it

An Stc `system` is a dependent record: `s_lasts_in_tcs`, `s_vars_out_in_tcs`,
`s_subs_calls_of`, `s_nodup_variables` come free with any system in scope, and
the Stc scopedness proof simply reads them off.  An Obc `class` is a plain
record with no such fields.  Every corresponding fact about the emitted class
therefore had to be *proved from the translation*, by a syntactic analysis of
`Control`, `translate_cexp`, `translate_tc` and the two reset folds along four
axes -- free names, written names, constraint targets, and state keys -- in both
directions.  That is roughly twenty-five lemmas (`stmt_free_*`,
`stmt_writes_*`, `stmt_targets_*`, `stmt_state_keys_*`) whose product is
`translate_system_well_defined`.

The same asymmetry shows in `signature_targets_out`, the half of
`signature_good` that call generation actually needs.  On the Stc side it falls
out of goodness (`signature_good_targets_out`).  On the Obc side goodness is not
available, so it is proved directly against the translation, through
`translate_class_out_is_target`, `translate_class_target_is_out`,
`translate_class_out_nodup` and `translate_class_hidden_disjoint`, giving
`generate_class_signature_targets_out`.

## 3. Two costs outside the bridge proper

### 3.1 A pass sits between the two languages

The compiler does not hand Obc `translate systems`; it hands it
`schedule (translate systems)`.  The scheduler permutes each system's body.
Nothing in the first bridge's chain had to survive an intervening pass, so a
new layer was needed: constraint generation is stable under reordering a body
(`generate_sys_signature_reorder_preserved`, `generate_sys_signature_reorder_ok`),
this lifts to programs (`generate_all_sys_signatures_reorder_*_scoped`), and
`generated_signatures_preserved_by_scheduling` carries the signatures across the
scheduling step.  `generated_program_signatures_preserved_obc_scheduled` glues
the two legs, scheduling included.

### 3.2 The layer must not mention NLustre

The naming pass runs once, over NLustre nodes.  If the Stc-to-Obc induction
quantified over that run, the layer would depend on the syntax of a language two
phases above it.  Instead the induction is stated against
`scoped_envs_windowed` -- each system's environment together with the state
window its names occupy, consecutive windows abutting -- and the new module
`SecNLusStcObcEnv.v` is where that predicate is discharged from the actual
naming run.  It threads proofs and introduces no new typing rule or signature
notion.

## 4. Relative totality, and the one genuinely new side condition

For the exported noninterference theorem to require no signature environment
from its caller, each generator must be shown to succeed wherever the previous
one did.  This was proved for the whole chain -- and, because the Obc leg needed
it, back-ported to the NLustre leg as well:
`generate_constraints_ok_from_good` at the signature level,
`generate_class_signature_ok_from_wc` per system,
`generate_all_class_signatures_scoped_env_ok` per program, with the NLustre-side
`generate_all_sys_signatures_scoped_env_ok` as its counterpart.

Exactly one hypothesis in that chain has no Stc counterpart: `sys_insts_named`,
that the naming pass gave *every* instance of a system a state name.  Stc only
ever looks up the instances it resets; the translated reset method touches all
of them.  It is discharged rather than assumed, in `SecNLusStcObcEnv.v`, by
reading it off `generate_local_env_for_node`, which builds the instance
environment from exactly `map fst (gather_insts n_eqs)`.

One further hypothesis is strengthened rather than new: the bridge asks for
`Well_scheduled` (per system, `Is_well_sch`), from which reset uniqueness
follows.  A doubly-reset instance would give two constraints the same target
and break signature goodness.

## 5. Summary

| Concern | NLustre-to-Stc | Stc-to-Obc |
| --- | --- | --- |
| clock type | an argument on both sides | accumulated as an Obc pc (`clock_pc`, `..._Control_assign`) |
| constraints per construct | one-to-one | one-to-many; recovered by `collapse` |
| call actuals | identical | contained; `inp_le`, `generate_constraints_mono_inp` |
| call cases | 2 | 3, one of which owns an Obc-private name |
| target-only names | one per reset application | one per unreset instance, also constrained by the reset method |
| composition | binary `preserves_on_concat_scoped` | n-ary `preserves_on_concat_list` + `zip_app` |
| hidden sets | track each other | unrelated; `preserves_on_simplify_bridge` generalised |
| target well-formedness | free, from the `system` record | proved: `translate_system_well_defined` |
| `signature_targets_out` | from `signature_good` | proved against the translation |
| intervening pass | none | `schedule`; reorder theorems + scheduling transport |
| naming data | the run itself | `scoped_envs_windowed`, discharged in a separate module |

Proof size is a fair proxy: `SecNLusStcTranslation.v` is 3.8k lines and 92 closed
proofs; `SecStcObcTranslation.v` is 5.8k lines and 155, with a further 0.9k lines
in `SecObcTypingCorrectness.v` and the reordering half of
`SecStcTypingCorrectness.v` attributable to this leg.

## 6. Source pointers

- Local correspondence and preservation: `src/SIF/SecStcObcTranslation.v`
- The typing-rule comparison in full: `src/SIF/docs/SecStcObcTyping.md`
- Proof structure of the file: `src/SIF/docs/SecStcObcTranslation.md`
- Shared call rules and `inp_le`: `src/SIF/SIFSignature.v`
- Preservation combinators: `src/SIF/SecTypes.v`
- Reordering and scheduling: `src/SIF/SecStcTypingCorrectness.v`,
  `src/SIF/SecNLusStcObcEnv.v`
- The first bridge, for comparison: `src/SIF/docs/SecNLusStcTranslation.md`
