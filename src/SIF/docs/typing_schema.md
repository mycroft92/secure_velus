# The typing schema across the phases

What each phase's constraint generator emits, rule by rule, and where the
phases agree.  The point of the table is that a node's *signature* is meant
to be the same object however it is generated, so that the legs of the chain
compose by entailment rather than by translation.

Read together with `SecLTyping.v` (Lustre), `SecNLusTyping.v` (NLustre),
`SecSTCTyping.v` (Stc) and `SecObcTyping.v` (Obc).  `SIFSignature.v` holds
what is shared.

## Notation

`ambient(ck)` is `[rst_ty] ⊔ ckty(ck)`, the reset level joined with the level
of the clock a variable is defined on; `ckty` is `assign_clk_type`, which
sends `Cbase` to `[base_ty]` and `ck on x` to `ckty(ck) ⊔ [sec x]`.  `[x]`
is the security name the naming pass gave the program variable `x`.

## Expressions

| form | Lustre (`assign_lexp_type`) | CoreExpr (`assign_exp_type` / `assign_cexp_type`) |
|---|---|---|
| constant | `⊥` | `⊥` |
| variable `x` | `[x]` | `[x]` |
| `unop e` | `t(e)` | `t(e)` |
| `binop e1 e2` | `t(e1) ⊔ t(e2)` | `t(e1) ⊔ t(e2)` |
| `e when x` | `t(e) ⊔ [x]` | `t(e) ⊔ [x]` |
| `merge x e1 e2` | `[x] ⊔ t(e1) ⊔ t(e2)` | `[x] ⊔ t(e1) ⊔ t(e2)` |
| `ite e e1 e2` | `t(e) ⊔ t(e1) ⊔ t(e2)` | `t(e) ⊔ t(e1) ⊔ t(e2)` |
| `fby e0s es` | `t(e0s) ⊔ t(es)`, componentwise | — (no `fby` in CoreExpr) |
| `arrow e0s es` | `t(e0s) ⊔ t(es)`, componentwise | — |
| **call** | fresh name per result, **refined by** the instantiated block joined with what the arguments and the reset carry | — (no nested calls) |

Aligned, including the associativity of `merge` and `ite`, which is
deliberate so that the two generators agree on the nose.

The call row is the one genuinely Lustre-only rule.  It exists because only
Lustre has nested calls, and it is what Leg U is about: the refinement a
nested call carries becomes, after unnesting, an emitted equation.

## Equations

| rule | Lustre | NLustre | Stc |
|---|---|---|---|
| definition | `ambient(ck) ⊔ t(e) ⊑ [x]`, plus what `t(e)` carries | `ambient(ck) ⊔ t(ce) ⊑ [x]` | same as NLustre |
| delay | falls through to the definition rule, whose expression rule joins **both** `fby` operands | `ambient(ck) ⊔ t(e) ⊑ [x]` -- only the second operand | same as NLustre |
| call, no reset | instantiate at `ckty(find_base_clock (clocksof args))`, reset `[rst_ty]`, outputs the equation's own variables | instantiate at `ckty(ck)`, reset `[rst_ty]` | same as NLustre |
| call, reset | reset level `[rst_ty] ⊔ ([r] ⊔ ckty(ckr))` | same | the reset is its own constraint `[rst_ty] ⊔ ([r] ⊔ ckty(ckr)) ⊑ [rst_inst]`, and the call instantiates at `[rst_inst]` |

### Where they agree, and why

*The clock.*  Lustre reads the call's base clock off its arguments;
NLustre and Stc read the equation's clock.  These coincide because
`to_equation` builds `EqApp xs (find_base_clock (L.clocksof es)) f les ...`.

*The delay.*  Lustre joins both operands, NLustre and Stc only the second.
This is deliberate and it is sound in both directions once `normfby` has
run: after it the initial value is a constant under `when`s, whose type is
exactly the sampling variables of the clock -- and those are already in
`ambient(ck)`.  So the extra join Lustre performs is subsumed.  Before
`normfby` the Lustre rule is strictly the stronger of the two, which is the
direction Leg I needs.

*The reset.*  Stc's extra `TcReset` constraint names the reset instance and
gives it exactly the level the other two phases inline.

## Signatures

All three build the same record, and each eliminates *its own* intermediate
names with `simplify`:

| | Lustre | NLustre | Stc |
|---|---|---|---|
| `s_in`, `s_out` | `get_mappings_from_node` | same | same |
| `s_clk`, `s_reset` | from the node's auxiliary names | same | same |
| eliminated | `locals ++ minted` | `locals` | `locals ++ lasts ++ reset instances` |

`minted` is the names the security monad took for nested calls' results;
they exist only in Lustre.  `lasts` and the reset instances exist only in
Stc.  So the eliminated sets differ exactly by what each phase has that the
others do not, which is what makes the surviving constraints comparable.

`SecLusConstraintExport.v`, `SecNLusConstraintExport.v` and
`SecStcConstraintExport.v` dump these records in the same shape so that a
transcribed program can be diffed node by node.

## The one hole

**A Lustre equation has two ways to type a call; NLustre and Stc have one.**

`generate_leqn_constraint` dispatches on the syntax of the right-hand side.
A call reaches the call rule only when the equation is literally
`(x :: xs, [Eapp f args er anns])` with `er` absent or an `Evar`.  Anything
else -- a call reset by a compound expression, or a call sitting among other
expressions in a multi-expression right-hand side -- falls through to the
general or definition rule, which types the call *as an expression*: fresh
names for its results, and the instantiated block carried as a refinement.

The two treatments are not equivalent, and the call rule is the stronger.
With the equation's own variables as the callee's outputs, a dependency
between two of the callee's outputs becomes a constraint between two of the
equation's variables; with fresh names it becomes a constraint between two
fresh names that are merely *below* those variables.  A valuation can
satisfy the second and fail the first.

Concretely, for `(x1, x2) = f(a)` where `f`'s second output depends on its
first: the expression treatment gives the block over fresh `o1, o2` together
with `ambient ⊔ [o1] ⊑ [x1]` and `ambient ⊔ [o2] ⊑ [x2]`; the call treatment
gives the block over `x1, x2`, which contains `… ⊔ [x1] ⊑ [x2]`.  Take
`[x1]` high and `[x2]` low: the first is satisfiable, the second is not.

This matters beyond tidiness, because unnesting *moves an equation from one
treatment to the other*: it lifts the call's arguments, leaves the call in
place, and the result then matches the call rule's pattern.  So security is
not preserved for those two shapes -- not because the proof is missing, but
because the source program was typed by the weaker of two rules that the
generator should not have had in the first place.

### The fix

Make every call go through the call rule, so that the Lustre generator has
the same single treatment NLustre and Stc do.

  * **(A)** Accept `[Eapp f args (Some e) _]` for *any* reset expression
    `e`, folding in `e`'s own level and the level of the clock it is sampled
    on.  That formula is already what `assign_lexp_type`'s call case uses,
    so the expression and equation rules then agree for every reset shape.
  * **(B)** Make the general rule split its right-hand side by
    `numstreams` -- as `split_equation` does -- and send a call chunk to the
    call rule.

Both *strengthen* the source type system: programs typed by the weaker
treatment may stop typing.  That is sound, and it is the direction that
agrees with NLustre, Stc and Obc.  The alternative -- weakening the equation
call rule to mint fresh outputs like the expression rule -- would
desynchronise Lustre from everything downstream, and is not recommended.
