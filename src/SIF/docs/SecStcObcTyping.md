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

After `Control`, $pc=K(ck)$.  The two targets are *the same identifier*:
$reset(s)$ and $state(s)$ are both $\iota(s)$ (see "One instance
environment" below), so the constraints coincide up to
commutativity/associativity/idempotence of $\sqcup$, with no side
condition.  `tcreset_preserv` carries none.

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

The outputs and clock actual agree, and translated input types are included
in the STC input types, so calls are not a literal equality of local
constraints.  Three cases arise, distinguished by whether the system resets
the instance (`reset_consistency` makes this exactly the call's $rst$ flag):

- **$rst = \mathit{true}$.**  Then $R_{STC} = [\iota(i)] = [state(i)]$: the two
  calls pass the *same* reset actual, so the equal-actuals preservation
  applies and $\iota(i)$ may sit inside the shared scope.
  (`Signature_call_preserves_obc_eq`, `tccall_reset_preserv_eq`.)
- **$rst = \mathit{false}$, $xs \neq []$.**  Then $R_{STC} = [\rho]$ while Obc
  passes $[\iota(i)]$.  The reset-underlying preservation bridges them and
  *produces* the extra constraint $[\rho] \Rightarrow [\iota(i)]$, which is
  precisely the constraint the reset method emits for that instance.  The
  block therefore owns $\iota(i)$, which is a name the STC side never sees.
  (`Signature_call_preserves_obc_rst`, `tccall_unreset_preserv_rst`.)
- **$xs = []$.**  Both generators produce $\emptyset$, yet $i \in c\_objs$ so
  the reset method still constrains $\iota(i)$.  Nothing else mentions it, so
  the block discharges $[\rho] \Rightarrow [\iota(i)]$ directly.
  (`preserves_on_reset_only_extra`.)

`signatures_preserved_obc_full_from_good` establishes both call properties
when the source signature is good, the target one is scoped, and the two
callee signatures satisfy the existing signature-preservation relation.

For `TcCall _ [] _ _ _ _`, both generators produce `[]`.

## One instance environment

Both languages need a security type per subsystem instance: STC for the
reset instances it names in `TcReset`/reset'd `TcCall`, Obc for the object
state it resets and passes to `step`.  These are minted **once**, by the
shared name generator, exactly as the clock and reset types $\beta,\rho$
already were.  Write

$$
 \iota : \mathit{ident} \rightharpoonup \mathit{ident}
$$

for that per-node environment (`ninst` in `node_aux_names`, read back by
`get_node_inst`); its values carry the `sec_reset` prefix, so they are
disjoint from the `sec` names of program variables.  Consequently

$$
  reset(s) \;=\; state(s) \;=\; \iota(s)
$$

*by construction*, and no hypothesis relating two environments is needed
anywhere in the bridge.

## From systems to classes

`translate_system` maps an STC system `s` to an Obc class of the same name:

$$
\begin{array}{rcl}
 c\_mems    &=& s\_lasts,\\
 c\_objs    &=& s\_subs,\\
 c\_methods &=& [step\_method(s), reset\_method(s)].
\end{array}
$$

The step body is `translate_tcs s_tcs`, typed at entry pc $[\beta]$ with
$\beta = clk\_ty$.  The reset body is
`Comp (reset_mems s_lasts) (reset_insts s_subs)`, typed at entry pc $[]$.

### The reset method

Both halves of the reset method produce constraints of one shape.  With
$pc = []$, the assignment and reset-call rules give

$$
 C_{Obc}([],\ reset\_mems(\overline{x}))
   = \{\, [\rho] \Rightarrow [\Gamma(x)] \;\mid\; x \in \overline{x} \,\},
 \qquad
 C_{Obc}([],\ reset\_insts(\overline{o}))
   = \{\, [\rho] \Rightarrow [\iota(o)] \;\mid\; o \in \overline{o} \,\}.
$$

These have no STC counterpart, so they are *discharged* rather than
preserved, in three ways:

- **memories.**  Every last $x$ has a `TcNext` defining it, and that
  constraint's source contains $\rho$; hence $[\rho] \Rightarrow [\Gamma(x)]$
  is entailed by the STC side under the *same* valuation.
- **reset instances.**  Likewise, every reset instance has a `TcReset` whose
  source contains $\rho$, giving $[\rho] \Rightarrow [\iota(o)]$.
- **unreset instances.**  $\iota(o)$ is invisible to STC, and the constraint
  is produced by that instance's call block, as described above.

The first two need no witness at all: any valuation agreeing with the source
one on the shared scope satisfies them.

### Ordering

`translate_tcs` is a left fold nesting `Comp` in reverse execution order, so
the Obc blocks come out as the reverse-order concatenation of the
per-transition blocks while STC concatenates in source order.  The two lists
are therefore permutations of each other, and constraint satisfaction, being
a conjunction, is order-insensitive.  (`translate_tcs_fold_right`,
`generate_fold_right_Comp`, and the permutation-tolerance of
`preserves_on`.)

### The two hidden sets differ, and must

STC hides $locals \cup lasts \cup \{\iota(o) \mid o \text{ reset}\}$; Obc
hides $locals \cup mems \cup \{\iota(o) \mid o \in c\_objs\}$.  The
asymmetry is forced: `simplify` may only eliminate a name that *has* a
defining constraint, and STC never constrains an instance it does not reset,
whereas the Obc reset method constrains every one of them.  The bridge does
not require the two sets to agree.

### Scopes

Write $\Sigma = inputs \cup outputs \cup \{\beta, \rho\}$ for the signature
scope, and

$$
 \Sigma_{raw} = \Sigma \cup locals \cup lasts \cup \{\iota(o) \mid o \text{ reset}\}
$$

for the raw scope: everything the two constraint sets share.  The unreset
instances are deliberately outside $\Sigma_{raw}$ — they are the per-block
private names ("extras"), and are provably distinct from every element of it
(prefix separation for the `sec` names, injectivity of $\iota$ together with
`reset_consistency` for the reset instances).

## The two theorems

Let $C_{STC}$ be the STC system's raw constraints and $C_{step}, C_{reset}$
the Obc class's.  Raw preservation is

$$
 \mathit{preserves\_on}\;\Sigma_{raw}\;\;C_{STC}\;\;
   \mathit{collapse}(C_{step} \mathbin{+\!\!+} C_{reset})
$$

(`class_preserv_raw`), proved by giving each transition constraint's block a
target consisting of its own Obc constraints *together with* the
reset-method constraint of any instance it owns.  Every Obc-exclusive name
then belongs to exactly one block, so the $n$-ary composition applies per
transition constraint; the memories and reset instances are appended for
free; and the proved target — which mentions each Obc constraint at least
once — is finally narrowed to the generated list.

Lifting across `simplify` is generic:

$$
 \frac{\mathit{wf}(C) \quad
       H_1 \cap \Sigma = \emptyset \quad
       \Sigma \subseteq \Sigma_{raw} \quad
       \mathit{preserves\_on}\;\Sigma_{raw}\;C\;D}
      {\mathit{preserves\_on}\;\Sigma\;\;\mathit{simplify}(C, H_1)\;\;
        \mathit{simplify}(D, H_2)}
$$

(`preserves_on_simplify_bridge`).  Note $H_1$ and $H_2$ are unrelated, which
is what the differing hidden sets require.  Composing the two gives
`class_preserv_signature`, relating the *stored* signature constraints of an
STC system and its translated Obc class.

## What is established

The per-transition results for `TcDef`, `TcNext`, `TcReset` and all three call
forms; the whole-body result; the reset method; the raw scope and the freshness
of the extras; that the free names of a translated transition constraint are
free or defined in the source; `class_preserv_raw`; the `simplify` bridge; and
`class_preserv_signature`.

`class_preserv_signature` is then instantiated at the *generated* signatures:
the per-block scopedness obligation is discharged
(`translated_tcs_constraints_scoped`), the two signatures are shown to agree on
their visible fields (`generated_signature_fields_agree`), and the per-system
result `generated_signatures_preserved_obc` is lifted by a program-level
lockstep to `Signature_consistent_obc_full`, exported as
`generated_program_signatures_preserved_obc_global`.  The Obc generator is also
proved total wherever the STC one succeeded
(`generate_all_class_signatures_scoped_env_ok`).  See
`docs/SecStcObcTranslation.md` for the proof structure.

## Source pointers

- STC expression, clock, control-expression, and transition generation:
  `src/SIF/SecCETyping.v`, `src/SIF/SecSTCTyping.v`.
- Obc expression, statement, and class generation:
  `src/SIF/SecObcTyping.v`.
- Syntactic system/class translation and ordinary type preservation:
  `src/StcToObc/Translation.v`, `src/StcToObc/Stc2ObcTyping.v`.
- Security correspondence lemmas:
  `src/SIF/SecStcObcTranslation.v`.
