# Call Metatheory

## Role

This note records the call-side metatheory behind the weakened
NLustre-to-STC preservation theorem in `SecNLusStcTranslation.v`.

At the current stage of the development, the public theorem stack no longer
mentions either of the earlier call-side bridge assumptions:

- `successful_call_substitutions_fresh`
- `signatures_preserved_calls`

Both are now discharged internally.  This note remains as the explanation of
why the call bridge needed more structure than plain `signature_scoped`.

## Why These Assumptions Are Harder

The scopedness assumptions are structural:

- a generated signature only mentions its visible variables
- a generated global list is `secglobal_scoped`

Those facts follow from local typing/scoping theorems plus list induction.

The call-side assumptions are harder because they are lattice-mapping instantiation
facts. They quantify over future uses of a generated signature at call sites.

### 1. `successful_call_substitutions_fresh`

This assumption says that when `generate_constraints` succeeds, the caller-side
actual names/types used for the instantiation are fresh with respect to the
callee formal signature scope.

To prove it, we need facts from several layers at once:

- the callee formal variables come from the generated signature scope
- the caller actual names/types come from the caller environment/current node
  scope
- the naming discipline prevents collisions between those two scopes

So this is not just a local typing lemma. It depends on:

- `NameInterface.v`
- the call cases in `SecNLusTyping.v`
- the call cases in `SecSTCTyping.v`
- the lattice-mapping interface of `generate_constraints`

### Fallback: strengthen `NameInterface`

If the freshness proof gets stuck for genuine namespace-collision reasons,
the right place to fix that is `NameInterface.v`.

The desired structural properties are:

- callee formal signature names live in a namespace disjoint from caller raw
  identifiers
- generated helper names for clock/reset/reset-instance variables are disjoint
  from ordinary shared names
- ideally, names generated for one node are distinguishable from names
  generated for another node

If those properties hold by construction, then the freshness proof becomes
mostly a range/lookup theorem rather than a delicate capture-avoidance proof.

This assumption is no longer part of the public theorem stack, but the
diagnosis remains useful because it explains why the old flat naming scheme was
too weak and why the proof migrated to the node-scoped environment design.

### 2. `signatures_preserved_calls`

The historical definition in `SecNLusStcTranslation.v` was:

```coq
Definition signatures_preserved_calls : Prop :=
  forall nsig ssig,
    signature_scoped nsig ->
    signature_scoped ssig ->
    signatures_preserved nsig ssig ->
    Signature_call_preserves nsig ssig.
```

It asked for source/target signature preservation to survive call-time
instantiation.

Semantically, the proof must:

1. start from satisfiability of an instantiated NLustre call block
2. reconstruct a lattice mapping on the callee formal signature variables
3. use `signatures_preserved` on the formal signature constraints
4. transport the result back to the instantiated STC call block

For reset calls, the target side also introduces one fresh reset-instance
variable and one extra reset constraint.

So this is the actual substitution/capture-avoidance metatheory, not just a
scopedness result.

### Why the current statement is too weak

The issue is not with the lattice-mapping goal `Signature_call_preserves`. The issue
is that the current premises only give `signature_scoped`, which controls
*which identifiers may appear* in the stored signature constraints.

That is not enough to replay `generate_constraints` backwards and forwards,
because `generate_constraints` does more than just substitute formal variables:

1. it substitutes inputs, clock, reset, and outputs;
2. then it rebuilds the final concrete call block by looking up each caller
   output through `findST`, in caller output order.

To justify that final reorder step at the lattice-mapping level, the stored signature needs a
stronger structural invariant such as:

- singleton RHS targets,
- unique RHS targets,
- RHS targets aligned with visible outputs.

Those are exactly the kinds of facts packaged by `signature_good` for generated
signatures. A merely scoped signature can still be malformed in ways that
break the replay argument, even though generated signatures never are.

The honest end state was:

- keep the *public* theorem stack assumption-free;
- strengthen the *internal* call bridge with the generated-signature
  structural invariant it really uses.

## Recommended Elimination Strategy

The clean plan is to avoid proving these assumptions in an unrealistically
generic form unless necessary. The final public theorem only needs the
generated-program case.

### Step 1. Prove generated-call freshness

Instead of proving a fully generic freshness theorem first, prove the version
actually needed by the final theorem:

- callee signatures are generated from `generate_node_env`
- caller actuals come from the generated caller environment/current node scope
- successful `generate_constraints` instantiations are fresh

This should be the bridge from the naming discipline to
`successful_call_substitutions_fresh`.

If the current naming discipline is too weak, strengthen `NameInterface`
before trying to prove a maximally generic freshness lemma.

### Step 2. Prove generated-call preservation from `signatures_preserved`

Use:

- generated scoped source signature
- generated scoped target signature
- generated-call freshness
- generated-signature structural goodness
- `signatures_preserved`

to derive:

- `Signature_call_preserves`

This is the theorem shape that replaced `signatures_preserved_calls`.

### Step 4. Inline the generated-call bridge into the global theorem stack

The final theorem family now rebuilds the call bridge internally inside the
generated-global proofs.

## Expected Shape Of The Proof

### Ordinary calls

- show that `generate_constraints` is formal-signature instantiation plus the
  caller-facing reshaping already introduced in the signature layer
- reconstruct a lattice mapping on formal variables from the caller's lattice
  mapping
- apply `signatures_preserved`
- push the result back to the caller-instantiated target constraints

### Reset calls

- use the same argument as ordinary calls
- add one fresh STC reset-instance variable
- account for one extra STC reset constraint

## Practical Guideline

If the freshness theorem is difficult to prove in full generality, that is a
sign the statement should stay specialized to generated signatures and
generated caller environments. That is still sufficient to remove the
assumptions from the final public theorem, which is the actual thesis goal.

Likewise, if the current name-generation scheme does not give the needed
separation properties, the intended repair is to strengthen
`NameInterface.v`, not to leave a broad call-side assumption in the final
theorem stack.

The same principle applies to the last lattice-mapping bridge:

- if `signatures_preserved_calls` is too weak in full generality,
- strengthen the *internal* proof to use the real generated-signature
  invariant (`signature_good` or the exact structural facts derived from it),
- but keep the final public theorem free of extra assumptions.
