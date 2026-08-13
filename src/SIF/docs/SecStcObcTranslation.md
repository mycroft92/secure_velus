# SecStcObcTranslation

## Role

`SecStcObcTranslation.v` is the Stc-to-Obc cross-phase preservation file, the
counterpart of `SecNLusStcTranslation.v` one phase down.  It compares generated
Stc system signatures with generated Obc class signatures and proves that every
generated source signature has a matching generated target signature with the
same visible interface and the same call behaviour.

Two things make it longer than its NLustre counterpart: the target is
imperative, so a single transition constraint compiles to a *statement* whose
constraints have to be reassembled; and the target class has an extra method --
`reset` -- that constrains names the source never mentions.  Both are discussed
below.  The typing rules themselves, on both sides, are in
`docs/SecStcObcTyping.md`; this note is about the proof structure.

## Core Interfaces

- `Signature_call_preserves_obc_eq`, `Signature_call_preserves_obc_rst`
  are thin aliases for `SIGPROOFS.call_preserves_eq` and
  `SIGPROOFS.call_preserves_rst`, the two call-instantiation rules **shared with
  the NLustre bridge**.  Both are stated over `inp_le` -- pointwise containment
  of input actuals -- because a translated Obc argument's type is contained in,
  not equal to, the Stc argument's.
- `Signature_call_preserves_obc_full` is their conjunction.
- `Signature_head_consistent_obc` packages one aligned pair: matching name,
  `signature_fields_agree`, and full call preservation.
- `Signature_consistent_obc_full` lifts that to whole generated globals.

`signatures_preserved_obc_full_from_good` builds a head-consistent pair from
source goodness, source scope `NoDup`, target scopedness and
`signatures_preserved` -- the same four ingredients the NLustre side uses.

## The pc/clock correspondence

Obc has no clocks.  `Control ck s` expands the clock into nested `Ifte`s, and
statement typing accumulates a program-counter type through them.  This section
is what reduces every per-transition case to an Stc constraint shape.

- `clock_pc` computes the pc accumulated by walking a clock.
- `generate_stmt_constraints_Control` and `generate_stmt_constraints_Control_inv`
  push a `Control` wrapper into the pc, in both directions.  The inverse is used
  to *derive* the clock type from a successful Obc run rather than assume it.
- `clock_pc_assign_clk_type` identifies `clock_pc` with the Stc clock type.
- `generate_stmt_constraints_Control_assign` is the corollary the rest of the
  file uses: with entry pc $[\mathit{clk\_ty}]$, the pc at each translated leaf
  is exactly $K(ck)$.

## Expression and argument types

`translate_exp` drops `Ewhen` guards, since the guard is already in the clock.

- `translate_exp_type_correspondence` shows the drop is invisible once the clock
  type is joined in.
- `translate_exp_type_incl`, `translate_arg_type_incl`, `translate_args_type_incl`
  give the weaker fact needed for call actuals: every identifier of a translated
  argument's type occurs in the Stc argument's.  This is what feeds `inp_le`.
- `translate_args_type_ok` is the totality companion: the Obc side types the
  translated actuals wherever the Stc side typed the originals.

`translate_cexp_constraints` and `translate_cexp_constraints_ok` describe the
decision tree: one constraint per leaf, all with the same target, sources
joining to the Stc source.  `merge_factor`, `merge_rotate`, `merge_swap` and
`merge_cong_under` are the join reassociations that argument needs.

## Per-transition preservation

One lemma per transition-constraint form, each stated as `preserves_on scope`
between the Stc constraint and the translated block:

1. `tcdef_preserv` -- `TcDef`.  Uses `collapse` to fold the decision tree's
   leaves back into one constraint; `preserves_on_collapse` moves the result.
2. `tcnext_preserv` -- `TcNext`.  A direct match after `Control`.
3. `tcreset_preserv` -- `TcReset`.  The two targets are the *same identifier*
   (see "One instance environment" in `SecStcObcTyping.md`), so the lemma carries
   no side condition.
4. `tccall_reset_preserv_eq` -- `TcCall` with $rst = \mathit{true}$: both sides
   pass the same reset actual, so the equal-actuals rule applies and the
   instance name may live inside the shared scope.
5. `tccall_unreset_preserv_rst` -- `TcCall` with $rst = \mathit{false}$ and
   outputs: Obc passes the instance state where Stc passes $\rho$.  The `rst`
   rule bridges them and *produces* $[\rho] \Rightarrow [\iota(i)]$, which is
   exactly the reset method's constraint for that instance.  The block keeps it.
6. `preserves_on_reset_only_extra` -- `TcCall` with no outputs: both generators
   are silent, but the instance is still an object, so its reset-method
   constraint is discharged here.

`translate_tcs_fold_right` and `generate_fold_right_Comp` handle ordering:
`translate_tcs` is a left fold nesting `Comp` in reverse execution order, so the
Obc blocks come out reversed relative to the Stc list.  Satisfaction is a
conjunction, so permutation tolerance suffices.

## Obc-exclusive names, per block

The names the target constrains and the source does not are computed
syntactically and attached to the block that owns them.

- `tc_obc_extras` gives the Obc-exclusive identifiers of one transition
  constraint -- the instance of an unreset call, and nothing else.
- `tcs_obc_extras` accumulates them along a body; `tcs_obc_extras_Forall2`,
  `tcs_obc_extras_concat` and `tcs_obc_extras_exists` are its shape,
  concatenation and existence facts.
- `unreset_call_insts` is the same set read off the body directly, with
  `unreset_call_insts_incl_calls`, `unreset_call_insts_nodup` and
  `unreset_call_insts_step`.
- `extras_fresh_raw_scope` proves the extras stay outside the shared scope --
  prefix separation for the `sec` names, injectivity of the instance environment
  together with `reset_consistency` for the reset instances.

`zip_app` is the pointwise augmentation: it appends to each Obc block the
reset-method constraints of the instances that block owns.  `zip_app_covers_blocks`,
`zip_app_covers_extras` and `zip_app_Forall2_scoped` are its coverage and
scopedness lemmas.

## Body-level assembly

- `tc_preserv_aug` is the per-transition statement in augmented form: the Stc
  constraint preserves to the Obc block *plus* the reset constraints of that
  block's extras.  It dispatches on the six cases above.
- `tcs_blocks_preserv_aug` lifts it to a list of blocks.
- `tcs_preserv_aug` composes the blocks with the n-ary
  `preserves_on_concat_list` from `SecTypes.v`, producing a target that mentions
  each Obc constraint at least once.

The n-ary combinator is required here where the NLustre bridge used binary
`preserves_on_concat_scoped`, because every unreset call contributes its own
private name and each block must be checked scoped against its own extras.

## The reset method

The reset method's constraints have no Stc counterpart at all.  They are
classified, not preserved:

- `generate_reset_mems_blocks`, `generate_reset_insts_blocks` and
  `generate_translate_reset_blocks` show every constraint the method emits has
  the shape $[\rho] \Rightarrow [ty]$, with `ty` ranging over the memories'
  types and the objects' instance types.
- `reset_shared_targets` shows that for a memory or a *reset* instance there is
  already an Stc constraint with the same target whose source contains $\rho$.
- `reset_constraint_entailed` and `reset_targets_satisfied` turn that into
  satisfaction under any scope-agreeing valuation, and
  `preserves_on_app_reset_shared` appends them to a preservation result for
  free -- no witness changes.
- `reset_body_constraints_classified` is the disposition theorem: every
  constraint of the reset body is either shared (memory or reset instance) or
  belongs to some block's extras.

## Scopedness of the translated class

Where an Stc `system` carries its well-formedness in the record, an Obc `class`
carries nothing, so the corresponding facts are proved from the translation.
Four families of lemmas, in both directions:

- **free names**: `translate_exp_free`, `translate_arg_free`,
  `translate_cexp_free`, `stmt_free_Control`, `translate_tc_free`,
  `stmt_free_translate_tcs_fold`, `stmt_free_reset_mems_fold`,
  `stmt_free_reset_insts_fold`.  The translation invents no variables.
- **written names**: `stmt_writes_Control`, `stmt_writes_translate_cexp`,
  `stmt_writes_translate_tc`, `stmt_writes_translate_tcs_fold` and their
  inverses; `stmt_writes_reset_mems_fold(_inv)`.
- **targets**: `stmt_targets_Control_inv`, `stmt_targets_translate_cexp`,
  `stmt_targets_translate_tc_variables`, `stmt_targets_fold_inv`.
- **state keys**: `stmt_state_keys_Control`, `..._translate_cexp`,
  `..._translate_tc`, `..._translate_tcs_fold`, `..._reset_mems_fold`,
  `..._reset_insts_fold`, `stmt_reset_insts_state_keys`.

Their product is `translate_system_well_defined`, feeding
`SECOBCTYPINGCORRECTNESS.generate_class_signature_scoped`.  Alongside it,
`translate_class_hidden_disjoint` keeps the Obc hidden set away from the
signature scope, and `translate_class_out_nodup`, `translate_class_out_is_target`
and `translate_class_target_is_out` combine into
`generate_class_signature_targets_out` -- the half of `signature_good` that call
generation needs, which the Stc side gets free from goodness and the Obc side
must prove.

`translated_tc_constraints_scoped`, `translated_tcs_constraints_scoped`,
`tc_names_env_scoped`, `tc_state_keys_in_scope_or_extras` and
`sys_vars_env_scoped_from_mappings` discharge the per-block scopedness
obligation that `tcs_preserv_aug` takes as a hypothesis.

## Raw scope

`raw_scope inp out slocals slasts rids` is everything the two constraint sets
share: the signature scope, the system's locals and lasts, and the instances it
resets.  The instances it does *not* reset are deliberately outside -- they are
the per-block extras.  `rst_ty_in_raw_scope`, `clk_ty_in_raw_scope`,
`reset_inst_in_raw_scope` and `sig_scope_in_raw_scope` are its membership facts;
specialising the scope this way collapsed three separate hypotheses of an
earlier formulation into one.

## Class-level theorems

- `class_preserv_raw` is the raw statement:

  $$
   \mathit{preserves\_on}\;\Sigma_{raw}\;\;C_{Stc}\;\;
     \mathit{collapse}(C_{step} \mathbin{+\!\!+} C_{reset}).
  $$

  It runs `tcs_preserv_aug` for the step body, appends the shared reset
  constraints with `preserves_on_app_reset_shared`, and narrows the proved
  target -- which mentions each Obc constraint at least once -- down to the
  generated list with `preserves_on_incl`.
- `class_preserv_signature` lifts it across `simplify` using the generic
  `preserves_on_simplify_bridge`.  The two hidden sets are **unrelated**, which
  is what the asymmetry between the Stc and Obc hidden sets requires: `simplify`
  may only eliminate a name that has a defining constraint, and Stc never
  constrains an instance it does not reset.
- `generated_signature_fields_agree` proves the two generated signatures agree
  on name, inputs, outputs, clock and reset -- both generators read the same
  environment and the same auxiliary names, and the class's step method carries
  the system's own interface up to `idty`.
- `generated_signatures_preserved_obc` is the per-system instantiation: both
  generators inverted, their components matched through the translation, and the
  raw scope handed to `class_preserv_signature`.  Its hypotheses are the
  NLustre ones with `wc_system` for `wc_node`, plus `Is_well_sch` (a doubly-reset
  instance would give two constraints the same target).

## Relative totality

`generate_class_signature_ok` and `generate_class_signature_ok_from_wc` prove
the Obc signature generator succeeds wherever the Stc one did, discharging the
generator's hypotheses from the ones preservation already takes.  The supporting
success lemmas are `translate_tcdef_constraints_ok`, `translate_tcnext_constraints_ok`,
`translate_tcreset_constraints_ok`, `translate_tccall_constraints_ok`,
`translate_tccall_nil_constraints_ok`, `translate_tcs_constraints_ok`,
`generate_reset_mems_ok`, `generate_reset_insts_ok` and
`generate_translate_reset_ok`, with `assign_clk_type_ok` and
`wc_trconstr_wc_clock` for the clocks.

The single requirement with no Stc counterpart is `sys_insts_named`: the naming
pass gave *every* instance of the system a state name.  The Stc layer only looks
up the instances it resets; the translated reset method touches all of them.  It
is a hypothesis here and is discharged in `SecNLusStcObcEnv.v`.

`generate_all_class_signatures_scoped_env_ok'` and its corollary
`generate_all_class_signatures_scoped_env_ok` run this over a whole program.

## Global induction

`generate_all_signatures_consistent_obc_scoped'` is the main accumulator
theorem.  One induction over the system list builds three results at once for
the generated Obc global:

- `Signature_consistent_obc_full G1 G2`
- `SIG.secglobal_scoped G2`
- `SIG.secglobal_scope_sec G2`

Nothing about the accumulators is assumed: consistency, scopedness and the
freshness bound are invariants re-established at each step, which is why there
is no per-step predicate to supply.  The abstract version
`generate_all_signatures_consistent_obc'_abstract` factors the lockstep walk out
from the invariant maintenance, and
`generated_signature_step_consistent_obc_from_bridges` builds one head-consistent
pair per system from the preservation bridge plus the two signature-shape facts
each layer proves about its own generator.

The naming run itself does not appear.  All the induction needs from it is
`scoped_envs_windowed`: each system's environment together with the state window
its names occupy, with consecutive windows abutting.  Producing that from the
NLustre naming pass is `SecNLusStcObcEnv.v`'s job -- which is what keeps this
layer free of NLustre syntax.

## Public Theorem

`generated_program_signatures_preserved_obc_global` is the exported lookup-based
result: once both generated globals have been built over the same windowed
environments, every Stc signature found in `G1` has a matching Obc class
signature in `G2` with `Signature_head_consistent_obc`.

It is the exact interface consumed by `SecObcNonInterference.v`, through
`SecNLusStcObcEnv.generated_program_signatures_preserved_obc_scheduled`, which
composes it with the scheduling transport.

## Related notes

- `docs/SecStcObcTyping.md` -- the typing rules on both sides, in full.
- `docs/Stc2Obc-additional-work.md` -- what this bridge needed beyond the
  NLustre-to-Stc one, and why.
- `docs/SecNLusStcTranslation.md` -- the bridge one phase up.
- `docs/Obc-noninterference-proof.md` -- the client of this file.
