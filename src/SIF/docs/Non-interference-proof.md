# NLustre Noninterference

## Scope

This document explains the current NLustre noninterference development.  The
main Coq files are:

- `SecNLusNonInterferenceSupport.v`
- `SecNLusNonInterferenceHelpers.v`
- `SecNLusNonInterferenceClockedStep.v`
- `SecNLusNonInterference.v`

The exported theorem is `node_noninterference_outputs`, which states that two
indexed executions of a secure node with low-equivalent inputs have
low-equivalent outputs.

## Module Split

### `SecNLusNonInterferenceSupport.v`

This file defines the observation model and the generic semantic transport
lemmas:

- low variables:
  `low_var`, `vars_le_t`, `env_low_eq`, `history_low_eq`,
  `history_low_eq_upto`
- environment and history projection:
  `project_env_le_t`, `project_history_le_t`
- generic expression and clock transport:
  `sem_caexp_switch_history_low`,
  `sem_aexp_switch_history_low`,
  `sem_exps_switch_history_low`
- base equation reasoning:
  `eqdef_noninterference`,
  `eqfby_noninterference`,
  and their pointwise / instant variants
- the security predicate:
  `node_security`

This is the semantic foundation of the proof.  It does not yet perform the
generated-program bookkeeping needed for real call sites.

### `SecNLusNonInterferenceHelpers.v`

This file adds the generated-program machinery:

- replay of raw satisfiability from stored signatures:
  `signature_satisfied_replays_raw`
- lookup and membership inversion for generated constraints
- caller-scope freshness and generated-environment facts
- call-input and call-output transport lemmas for both ordinary and reset
  calls
- the intermediate specifications
  `node_outputs_raw_spec` and `node_outputs_raw_spec_clocked`
- the base step theorem
  `node_noninterference_vars_defined_step_base_mainline`

The helper file is where generic semantic lemmas become usable on actual
generated nodes and actual generated call signatures.

### `SecNLusNonInterferenceClockedStep.v`

This file proves the successor-step theorem:

- `node_noninterference_vars_defined_step_mainline`

It is the time-indexed induction that extends low-equivalence from instant `k`
to instant `S k` for the variables defined by the current node equations.

### `SecNLusNonInterference.v`

This file packages the step theorem into the two public layers:

- `node_noninterference_outputs_raw`
  turns a `node_security` witness into the clocked raw-output specification.
- `node_noninterference_outputs`
  is the exported source noninterference theorem on observable outputs.

## The Security Predicate

`node_security all_nodes G envs aux_names n dlt_sig dlt_raw` is the central
inductive invariant.  A witness contains:

- the generated local environment and generated stored signature of `n`;
- the generated clock/reset identifiers and the generated input/output/local
  mappings of `n`;
- the raw generated constraints and the simplified stored signature equation
  that links them;
- satisfiability of the stored signature under `dlt_sig`;
- satisfiability of the raw generated constraints under `dlt_raw`;
- agreement of `dlt_sig` and `dlt_raw` on the visible signature scope;
- recursive security obligations for every ordinary call and every reset call
  in `n`.

The proof keeps both `dlt_sig` and `dlt_raw` because the stored signature is
the reusable public summary, while the equation-by-equation step proof needs
the unsimplified raw constraints.

## What The Main Step Theorem Proves

`node_noninterference_vars_defined_step_mainline` proves:

- if two histories are low-equivalent on the node inputs up to instant `k`,
- and the current node is secure,
- and both histories satisfy the node equations,
- and the base clocks agree up to `k`,

then the two histories are low-equivalent up to `k` on every variable defined
by the node equations.

This theorem is stronger than the final output theorem because it tracks all
defined variables, not only the observable outputs.  That stronger statement is
what makes the induction go through for equations that depend on earlier
equations in the same node.

## How The Induction Works

There are two interacting proof structures.

### 1. Time induction on `k`

The theorem in `SecNLusNonInterferenceClockedStep.v` is proved by induction on
the time bound `k`.

#### Base case

At `k = 0`, the proof uses
`node_noninterference_vars_defined_step_base_mainline` from the helper file.
This theorem handles the first instant directly, where:

- `EqDef` only depends on current inputs and already available environment
  facts,
- `EqFby` uses its initial branch,
- call equations only need the callee result at the initial instant.

#### Successor case

For `S k`, the proof first invokes the induction hypothesis to recover
low-equivalence on all variables defined by the node up to instant `k`.
That gives the delayed information needed by `EqFby` and the prefix facts
needed by call equations.

The proof then establishes pointwise equality at instant `S k` for every low
defined variable.  That pointwise statement is turned back into
`history_low_eq_upto ... (S k)` with `history_low_eq_upto_succ_intro`.

### 2. Causal induction on defined variables at the current instant

Inside the successor case, the proof uses
`nl_node_causal_ind_defined` to reason over variables in the node's causal
order.  This is what handles dependencies between equations within the same
instant.

For a currently defined low variable `x`, the proof picks the equation that
defines `x` and uses the theorem corresponding to that equation form.

#### `EqDef`

The proof uses the generated typing witness for the defining equation and the
instant-level switch lemmas from `CEProperties`.  Because every low free
variable of the defining expression already agrees between the two histories,
the current output of the expression agrees as well.

#### `EqFby`

The initial value or delayed predecessor is handled with the `fby` lemmas from
the support file.  The delayed branch uses the induction hypothesis on `k`
because the predecessor value comes from an earlier instant, not from the
current one.

#### Ordinary `EqApp`

The proof first shows that the actual input arguments of the call are
low-equivalent up to the relevant instant.  This uses the helper lemmas that
transport low-equivalence from caller variables to the instantiated callee
inputs.

It then applies the recursive `node_security` witness for the callee, but under
the instantiated valuations
`inst_valuation dlt_sig ...` and `inst_valuation dlt_raw ...`.  The callee
gives low-equivalent outputs, and the helper lemmas transport that result back
to the caller-side output variables.

#### Reset `EqApp`

The reset-call case follows the same structure, but it also carries:

- low-equivalence of the reset control stream,
- clock alignment for the reset clock,
- the reset type contribution `([rty] ⊔ rstty)` used in the instantiated
  callee valuation.

The helper layer contains the extra transport lemmas that keep the reset
control aligned across the two histories.

## From Defined Variables To Observable Outputs

`node_noninterference_outputs_raw` takes a `node_security` witness and builds
`node_outputs_raw_spec_clocked`.  The only additional step is to weaken the
defined-variable result to the output list using the node's `n_defd`
permutation between `vars_defined n.(n_eqs)` and the declared outputs/locals.

`node_noninterference_outputs` then converts the clocked raw specification into
the public theorem on outputs alone.  The statement only exposes:

- successful generated environments and source signatures,
- the secure-node witness,
- two indexed executions of the node,
- and low-equivalent inputs.

All raw-constraint replay, generated-name lookup, and callee-security recursion
remain internal to the proof.

## Why The Proof Is Structured This Way

The theorem has to reason about three different kinds of dependency at once:

- same-instant equation dependencies inside one node;
- previous-instant dependencies created by `fby`;
- inter-node dependencies introduced by calls.

The current split assigns one mechanism to each:

- causal induction handles same-instant dependencies;
- time induction handles delayed dependencies;
- `node_security` handles recursive call dependencies.

That is the reason the public theorem looks compact while the internal proof
stack is split across support, helper, step, and final packaging files.
