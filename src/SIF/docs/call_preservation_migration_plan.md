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

First try to prove the required caller/callee separation from the current
shared environment discipline:

- generated signature variables are images of callee keys
- actual call arguments/outputs are images of caller keys
- `generate_node_env` enforces global key uniqueness
- `generate_node_env_injective` transfers source-key separation to generated
  security-name separation

If that is not sufficient, then strengthen `NameInterface.v` or the
`IDS`/`Ident` namespace setup in the smallest possible way.

## Expected End State

The final theorem stack should mention neither:

- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

Instead, freshness should be proved locally where `EqApp`/`TcCall` preservation
actually uses it.
