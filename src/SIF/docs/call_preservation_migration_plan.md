# Call Preservation Migration Plan

## Goal

Eliminate the final two call-side assumptions from the theorem stack in
`SecNLusStcTranslation.v`:

- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

## Diagnosis

The current global freshness assumption is stronger than the translation proof
actually needs.  The development never requires freshness for arbitrary
successful `generate_constraints` calls.  It only needs freshness for the
concrete substitutions that arise at real typed call sites.

Because of that mismatch, proving `successful_call_substitutions_fresh` as a
standalone global theorem is not the clean target.

## Migration Strategy

### 1. Make freshness local to call preservation

Refactor `Signature_call_preserves` so that each ordinary/reset call clause
takes explicit `call_subst_fresh` premises for the instantiated source and
target signatures.

This turns freshness into a local side condition of one call-preservation
obligation instead of a separate global theorem assumption.

### 2. Simplify the remaining semantic bridge

After step 1, redefine `signatures_preserved_calls` so it no longer depends on
`successful_call_substitutions_fresh`.

The desired bridge is:

- `signature_scoped nsig`
- `signature_scoped ssig`
- `signatures_preserved nsig ssig`

implies

- `Signature_call_preserves nsig ssig`

where the latter now quantifies over local freshness assumptions per call.

### 3. Prove freshness where calls actually occur

Discharge the local `call_subst_fresh` hypotheses only at real generated call
sites, using:

- `NameInterface.v` for generated-name range and separation facts
- source/target scopedness theorems from the correctness modules
- the concrete call arguments/outputs produced by NLustre/STC typing

This avoids proving an unrealistically general freshness theorem.

### 4. Use NameInterface strengthening only if needed

The flat shared-variable env turned out to be too strong: two different nodes
may reuse the same raw input/local/output name, but the old naming pass
rejected that.

So the first concrete migration step is now:

- replace the flat shared variable env by a node-scoped env-of-envs
- outer env keyed by unique node names
- inner env keyed by raw variable/helper names local to that node

This keeps the typing layer on raw local names while making inter-node name
reuse legal by construction.

Once that pivot is in place, prove caller/callee separation from:

- generated signature variables are images of callee local keys
- actual call arguments/outputs are images of caller local keys
- prefix/current-node separation in the outer naming pass
- `generate_node_env_injective`-style range facts for generated security ids

Only if that still proves insufficient should the `IDS`/`Ident` namespace
setup itself be strengthened further.

## Expected End State

The final theorem stack should mention neither:

- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

Instead, freshness should be proved locally where `EqApp`/`TcCall` preservation
actually uses it.
