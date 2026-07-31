# STC-to-Obc Security Typing Correspondence

## Purpose and scope

This note compares the symbolic security-typing generators on the two sides
of the STC-to-Obc translation:

- `SecSTCTyping.v` types STC transition constraints (`trconstr`);
- `SecObcTyping.v` types Obc statements and classes;
- `StcToObc/Translation.v` defines the syntactic translation; and
- `SecStcObcTranslation.v` proves the local correspondence lemmas.

The rules below are the mathematical reading of the executable generators.
They use $\Gamma$ for the local security environment, $[a]$ for the singleton
symbolic type containing security variable $a$, $\sqcup$ for type join, and
$L \Rightarrow R$ for one security constraint with source $L$ and target $R$.
$\rho$ is the system/class reset type, and $\beta$ is the base clock type.

`C_STC(tc)` and `C_Obc(pc, s)` denote the constraints returned by
`generate_trconstr_constraint` and `generate_stmt_constraints`, respectively.
Both functions can fail when a required environment or signature lookup fails;
the displayed rules describe their successful cases.

## Expression and clock rules

### STC core expressions

`SecCETyping.assign_exp_type` gives the following security types for CoreExpr
expressions:

| Expression | STC type |
| --- | --- |
| `Econst c` | $[]$ |
| `Evar x t` | $[\Gamma(x)]$ |
| `Ewhen e x b` | $T(e) \sqcup [\Gamma(x)]$ |
| `Eunop op e t` | $T(e)$ |
| `Ebinop op e1 e2 t` | $T(e_1) \sqcup T(e_2)$ |

For clocks, `assign_clk_type Γ β` gives

$$
  K(Cbase) = [\beta]
  \qquad
  K(Con\ ck\ x\ b) = K(ck) \sqcup [\Gamma(x)].
$$

Control expressions are typed by `assign_cexp_type`:

$$
\begin{array}{rcl}
  T(Eexp\ e) &=& T(e),\\
  T(Eite\ e\ ct\ cf) &=& T(e) \sqcup T(ct) \sqcup T(cf),\\
  T(Emerge\ x\ ct\ cf) &=& [\Gamma(x)] \sqcup T(ct) \sqcup T(cf).
\end{array}
$$

### Obc expressions after translation

`SecObcTyping.assign_exp_type` has the analogous ordinary-expression rules:

$$
\begin{array}{rcl}
  T_O(Const\ c) &=& [],\\
  T_O(Var\ x) = T_O(State\ x) = T_O(Valid\ x) &=& [\Gamma(x)],\\
  T_O(Unop\ e) &=& T_O(e),\\
  T_O(Binop\ e_1\ e_2) &=& T_O(e_1) \sqcup T_O(e_2).
\end{array}
$$

`translate_exp` turns an STC `Evar` into either `Var` or `State` according to
whether it is a memory variable, and otherwise preserves the expression shape.
It *drops* `Ewhen` nodes.  This is sound because the surrounding STC clock is
compiled separately by `Control`.

More precisely, `translate_exp_type_correspondence` proves that, if
`K(ck) = ckty` and `T(e) = ety`, then there is an Obc type `oty` such that

$$
  T_O(translate\_exp(e)) = oty
  \qquad\text{and}\qquad
  ckty \sqcup ety = ckty \sqcup oty.
$$

Thus a guard dropped from an `Ewhen` is not lost: its type is already in the
clock type.  `translate_arg_type_incl` supplies the weaker fact needed for
call arguments: every identifier in the translated argument's type occurs in
the original STC argument type.

## Clock control becomes statement pc

The syntactic translation wraps every transition constraint in
`Control ck ...`.  `Control` expands a clock into nested `Ifte`s.  Obc
statement typing carries a program-counter type `pc`; typing an `Ifte e s1 s2`
uses $pc \sqcup T_O(e)$ for both branches.

The bridge is `generate_stmt_constraints_Control_assign`.  If
`assign_clk_type Γ β ck = Some ckty`, then

$$
 C_{Obc}(pc_0 \sqcup [\beta],\ Control\ ck\ s)
 = C_{Obc}(pc_0 \sqcup ckty,\ s).
$$

In a translated step method, the entry pc is $[clk\_ty]$; taking
$\beta = clk\_ty$ and $pc_0 = []$ makes the pc at each translated leaf exactly
$K(ck)$.  This is
why both sides include the same clock dependency.

## Transition constraints and translated statements

For local writes, an Obc assignment has the rule

$$
 \frac{T_O(e)=t \qquad \Gamma(x)=x_t}
      {C_{Obc}(pc, Assign\ x\ e)
       = C_{Obc}(pc, AssignSt\ x\ e)
       = \{(([\rho]\sqcup pc)\sqcup t) \Rightarrow [x_t]\}}.
$$

The following table gives the corresponding STC rule, syntax translation, and
Obc result under an entry pc $[\beta]$.  Here $K(ck)=k$, $T(ce)=q$,
$T(e)=t$, and $\Gamma(x)=x_t$.

| STC transition constraint | STC generated constraint | Translation | Obc generated constraint | Bridge lemma |
| --- | --- | --- | --- | --- |
| `TcDef x ck ce` | $(([\rho] \sqcup k) \sqcup q) \Rightarrow [x_t]$ | `Control ck (translate_cexp x ce)` | After `collapse`: $(([\rho] \sqcup k) \sqcup q) \Rightarrow [x_t]$ | `translate_tcdef_constraints`, `tcdef_preserv` |
| `TcNext x ck e` | $(([\rho] \sqcup k) \sqcup t) \Rightarrow [x_t]$ | `Control ck (AssignSt x (translate_exp e))` | $(([\rho] \sqcup k) \sqcup t) \Rightarrow [x_t]$ | `translate_tcnext_constraints`, `tcnext_preserv` |
| `TcReset s ck f` | see reset rules below | `Control ck (Call [] f s reset [])` | $([\rho] \sqcup k) \Rightarrow [state(s)]$ | `translate_tcreset_constraints`, `tcreset_preserv` |

### Why `TcDef` needs `collapse`

`translate_cexp x ce` compiles `Emerge` and `Eite` into nested Obc `Ifte`s
with an `Assign x` at each leaf.  The Obc generator therefore produces one
constraint per leaf.  Each has target $[x_t]$; its source includes the reset
type, the accumulated pc, and the leaf expression type.  The join of the leaf
sources is exactly $(([\rho] \sqcup k) \sqcup q)$.

`collapse` joins sources with duplicate targets, so its result is the single
STC `TcDef` constraint.  Collapse is satisfaction-neutral, which is why
`tcdef_preserv` establishes `preserves_on` even though the raw Obc list can
contain multiple constraints.

### Reset transition details

For a base/reset-false clock, STC uses

$$
 C_{STC}(TcReset\ s\ ck\ f) = ([\rho] \sqcup K(ck)) \Rightarrow [reset(s)].
$$

For the distinguished positive reset clock `Con ckr r true`, its generator
spells the same dependency as

$$
 ([\rho] \sqcup ([\Gamma(r)] \sqcup K(ckr))) \Rightarrow [reset(s)].
$$

The Obc reset call has the general rule

$$
 C_{Obc}(pc, Call\ []\ f\ s\ reset\ [])
 = ([\rho] \sqcup pc) \Rightarrow [state(s)].
$$

After `Control`, $pc=K(ck)$.  `tcreset_preserv` assumes the intended
environment alignment $reset(s) = state(s)$; the positive-reset form then
matches up to commutativity/associativity/idempotence of $\sqcup$.

### Calls

For a real STC call (`xs` nonempty), STC invokes the callee signature with

$$
 generate\_constraints(N_f,\ inputs_{STC}, K(ck), R_{STC}, outputs),
$$

where $R_{STC} = [reset(i)]$ for a reset call and $R_{STC} = [\rho]$ otherwise.
The compiled Obc statement is

$$
 Control\ ck\ (Call\ xs\ f\ i\ step\
                  (map\ (translate\_arg\ ck)\ es)),
$$

and invokes its callee signature with

$$
 generate\_constraints(O_f,\ inputs_{Obc}, K(ck), [state(i)], outputs).
$$

The outputs and clock actual agree; translated input types are included in
the STC input types.  Calls are therefore not a literal equality of local
constraints.  `tccall_preserv` reduces the case to
`Signature_call_preserves_obc`, including freshness/scopedness side
conditions.  `signatures_preserved_obc_calls_from_good` discharges that
property when the source signature is good, the target one is scoped, and the
two callee signatures satisfy the existing signature-preservation relation.

For `TcCall _ [] _ _ _ _`, both generators produce `[]`.

## From systems to classes

`translate_system` maps an STC system `s` to an Obc class of the same name:

$$
\begin{array}{rcl}
 c\_mems    &=& s\_lasts,\\
 c\_objs    &=& s\_subs,\\
 c\_methods &=& [step\_method(s), reset\_method(s)].
\end{array}
$$

The step body is `translate_tcs s_tcs`; each element is translated by the
table above.  The reset body resets memory cells and calls `reset` on every
object.  Ordinary data typing is preserved separately by
`StcToObc/Stc2ObcTyping.v` (`translate_system_wt` and `translate_wt`).

At the security-signature level, the two generators have parallel shapes:

| STC system signature | Translated Obc class signature |
| --- | --- |
| Create `reset_env` for reset-instance keys. | Create `state_env` for class objects. |
| Generate and concatenate `C_STC(tc)` for `s_tcs`. | Generate step constraints at pc `[clk_ty]`, and reset-method constraints at pc `[]`. |
| `simplify` after hiding system locals, lasts, and reset-instance identifiers. | `collapse` the combined step/reset constraints, then `simplify` after hiding method locals, memory cells, and object-state identifiers. |

The difference in raw ordering is intentional: `translate_tcs` is a left fold
that nests `Comp` in reverse execution order.  STC concatenates in source
order, whereas the Obc blocks are reverse-order concatenations.
`translate_tcs_fold_right` and `generate_fold_right_Comp` make this explicit;
the resulting lists are compared through permutation because constraint
satisfaction is order-insensitive.

## What is established here

`SecStcObcTranslation.v` proves per-transition `preserves_on` lemmas for
`TcDef`, `TcNext`, `TcReset`, and `TcCall`, plus the control, expression, and
composition lemmas needed to assemble them.  It deliberately distinguishes:

- **exact constraints:** `TcNext`, and `TcDef` after collapse;
- **exact up to reset/state-name alignment and join ACI:** `TcReset`; and
- **semantic preservation through callee signatures:** `TcCall`.

The file provides the fold/concatenation facts for lifting these results from
one transition constraint to an entire step method.  It does not currently
state one final theorem equating complete STC-system and Obc-class stored
signatures; such a theorem must also connect generated reset and state
environments and account for the class reset method and the two sides'
different hidden-name sets.

## Source pointers

- STC expression, clock, control-expression, and transition generation:
  `src/SIF/SecCETyping.v`, `src/SIF/SecSTCTyping.v`.
- Obc expression, statement, and class generation:
  `src/SIF/SecObcTyping.v`.
- Syntactic system/class translation and ordinary type preservation:
  `src/StcToObc/Translation.v`, `src/StcToObc/Stc2ObcTyping.v`.
- Security correspondence lemmas:
  `src/SIF/SecStcObcTranslation.v`.
