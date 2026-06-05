# NLustre Noninterference

## Scope

This document explains the source-side noninterference development across:

- `SecNLusNonInterferenceSupport.v`
- `SecNLusNonInterferenceHelpers.v`
- `SecNLusNonInterferenceClockedStep.v`
- `SecNLusNonInterference.v`

The exported theorem is `node_noninterference_outputs`: two indexed
executions of a secure node with low-equivalent inputs have low-equivalent
observable outputs.

## Module Split

### `SecNLusNonInterferenceSupport.v`

This file provides the semantic base:

- the observation predicates `low_var`, `env_low_eq`, `history_low_eq`, and
  `history_low_eq_upto`
- projection helpers such as `project_env_le_t` and `project_history_le_t`
- expression and clock transport lemmas for low-equivalent histories
- base noninterference lemmas for `EqDef` and `EqFby`
- the central security predicate `node_security`

This is the semantic foundation.  It does not yet perform the
generated-program bookkeeping needed for real call sites.

### `SecNLusNonInterferenceHelpers.v`

This file connects the semantic base to generated signatures and generated
program structure:

- replay of raw satisfiability from stored signatures
- lookup and membership inversion for generated constraints
- caller-scope freshness and generated-environment facts
- ordinary-call and reset-call transport lemmas
- the base step theorem
  `node_noninterference_vars_defined_step_base_mainline`

The crucial bridge here is:

- `signature_satisfied_replays_raw`

It starts from satisfaction of the stored simplified signature and reconstructs
satisfaction of the raw generated constraints used by the step proof.

### `SecNLusNonInterferenceClockedStep.v`

This file proves the successor-step theorem:

- `node_noninterference_vars_defined_step_mainline`

It extends low-equivalence from time `k` to time `S k` for every variable
defined by the current node equations.

### `SecNLusNonInterference.v`

This file packages the internal step theorem into:

- `node_noninterference_outputs_raw`
- `node_noninterference_outputs`

The second theorem hides the replay machinery and exports the source-facing
statement on observable outputs.

## The Security Predicate

`node_security all_nodes G envs aux_names n dlt_sig dlt_raw` is the central
invariant.  A witness contains:

- the generated local environment and stored signature of `n`
- the generated clock/reset identifiers and generated input/output/local
  mappings of `n`
- the raw generated constraints and the equation linking them to the stored
  simplified signature
- satisfiability of the stored signature under `dlt_sig`
- satisfiability of the raw constraints under `dlt_raw`
- agreement of `dlt_sig` and `dlt_raw` on the visible stored signature scope
- recursive security obligations for ordinary calls and reset calls

The proof keeps both `dlt_sig` and `dlt_raw` because the stored signature is
the reusable public summary, while the equation-by-equation reasoning still
needs the raw node constraints.

## Where Simplification Enters

The stored signature inside `node_security` is already in the shared normal
form produced by `SymTypes.simplify`.  That means:

- node locals have been eliminated
- singleton-right-hand-side constraints have had trivial self-dependencies
  removed

The helper layer is what reconnects that stored summary to the raw generated
constraints needed by the semantic induction.

## What The Main Step Theorem Proves

`node_noninterference_vars_defined_step_mainline` says:

- if two histories are low-equivalent on the node inputs up to instant `k`
- and the current node is secure
- and both histories satisfy the node equations
- and the base clocks agree up to `k`

then the histories are low-equivalent up to `k` on every variable defined by
the node equations.

This stronger statement is what makes the induction work for equations that
depend on earlier equations in the same node.

## How The Induction Works

There are two interacting proof structures.

### 1. Time Induction

The theorem in `SecNLusNonInterferenceClockedStep.v` proceeds by induction on
the time bound `k`.

- base case:
  `node_noninterference_vars_defined_step_base_mainline`
- successor case:
  reuse the induction hypothesis on time `k`, then prove pointwise equality at
  time `S k`

### 2. Causal Induction Inside One Instant

Inside the successor step, the proof uses the node causality induction to
reason over variables in the order they are defined at the current instant.

- `EqDef`
  current expression equality follows from low-equivalence of free variables
- `EqFby`
  delayed values come from the induction hypothesis on the previous instant
- ordinary `EqApp`
  call inputs are transported to the callee, the recursive security witness is
  applied, and the result is transported back
- reset `EqApp`
  same structure, with extra bookkeeping for the reset control and reset type

## Result

The exported theorem `node_noninterference_outputs` is the exact source-side
noninterference statement justified by the current development.
