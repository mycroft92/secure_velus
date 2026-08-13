# Signature Generation Totality

## Why this exists

Every top-level theorem in the development is conditioned on a successful
run of the generators.  The exported Obc noninterference theorem, for
instance, takes

```coq
NAMEGEN.generate_node_scoped_env all_nodes = OK (envs, aux_names) ->
SECNLUSTYPING.generate_all_signatures_scoped_env all_nodes envs aux_names
  = OK Gsrc ->
```

and the STC and NLustre layers carry the same pair.  Stating passes this
way is normal — Velus does it for its own — but it leaves one question
open: is there any program at all for which the hypotheses hold?  Until
they are proved, every theorem downstream could be vacuously true.

Two files close that.  `SecNamingTotality.v` handles the naming pass;
`SecNLusTypingTotality.v` handles the generator that runs on its output.
Composed, they give

```coq
Theorem source_signature_generation_total:
  forall all_nodes,
    Ordered_nodes all_nodes ->
    wc_global all_nodes ->
    exists envs aux_names G,
      generate_node_scoped_env (rev all_nodes) = OK (envs, aux_names)
      /\ generate_all_signatures_scoped_env (rev all_nodes) envs aux_names
         = OK G.
```

This is the *head* of the chain.  Everything downstream of it was already
relative — NLustre success implies STC success implies Obc success — and
is assembled by `SecObcNonInterference.generate_all_signatures_chain_ok`.

## Part 1: the naming pass

`generate_node_scoped_env` can fail in exactly three places, all of them
`Env.mem` guards:

| Guard | Refuses | Discharged by |
| --- | --- | --- |
| `fresh_insert` | a variable already mapped | `n_nodup`, `n_good` |
| `fresh_inst_insert` | a repeated instance | `n_defd` + `n_nodup` |
| `fresh_insert_node_env` | a repeated node name | `Ordered_nodes` |

The first two are properties of a single node and need **no hypothesis at
all** beyond what the `node` record already carries.  That is worth
stating plainly: `generate_local_env_for_node_ok` is hypothesis-free.

- **Declared variables are distinct** — `n_nodup` directly.
- **The minted clock and reset names are not declared variables** —
  `n_good` says every declared name is an atom or a gensym drawn from the
  elaboration prefixes, and `sec_not_in_gensym_prefs` says `sec` is not
  one of those.  `atom_or_gensym_not_sec_gensym` is the general form.
- **The two minted names differ from each other** — `gensym` is injective
  in its counter and the counter advances (`Pos.succ_discr`).
- **Gathered instances are distinct** — `gather_insts` names an instance
  by the first variable its call defines, so distinct calls get distinct
  names exactly because a body defines each variable once.  That is
  `n_defd` plus `n_nodup`, routed through Velus's `NoDup_In_gather_insts`
  (`gather_insts_NoDupMembers`).

Only the third guard needs anything of the program, and only that node
names are distinct, which `Ordered_nodes_NoDup_names` extracts from
`Ordered_nodes`.

### Coverage

Totality alone is not enough: the environment produced must also *answer*
every lookup the generators make.  `naming_run_total_and_covering` says
that for each node of the run there is an entry, and that entry answers

- the clock and reset names (`Env.find rec.(nclk)`, `Env.find rec.(nrst)`),
- the three interface lists through `get_mappings_from_node`,
- and every instance the body gathers, through `rec.(ninst)`.

All of it comes from one observation — the keys the pass inserted are
exactly the names it will later be asked about — made precise by
`generate_local_env_for_node_binds` and `..._inst_binds`.

## Part 2: the generator

`generate_all_signatures_scoped_env` fails wherever a lookup does.  Each
kind is discharged from a different source:

- **`assign_clk_type`, `assign_exp_type`, `assign_cexp_type`** — each is a
  structural recursion whose only partiality is `Env.find` on a free
  variable.  Well-clocking bounds the free variables of a clock, an
  expression, or a control expression to the declared ones
  (`wc_clock_free_in_vars` and friends), and Part 1 binds those.
  (`assign_*_type_total`.)
- **`find_env` on defined variables** — the same, through `wc_equation`.
- **The callee lookup** — from the accumulator; see below.
- **`generate_constraints`** — `generate_constraints_ok_from_good`, whose
  hypotheses are the callee's `signature_targets_out`, a duplicate-free
  scope, matching arities, and freshness of the caller's outputs.

The last of those is the only one that does not follow from the callee's
own well-formedness, and it is worth spelling out.  A call's results are
variables the caller's body defines, so they lie in the caller's own name
window; `node_scope_fresh_in_env` keeps that window disjoint from every
signature generated earlier.  That is `call_outputs_fresh`.

### The reversal is load-bearing

`Ordered_nodes` places a callee **after** its caller.  The generator's
accumulator grows front-to-back, so when it reaches a node it holds the
signatures of the nodes *before* it.  Those two orders are opposite,
which is why the driver reverses the program before generating
(`SecNLusConstraintExport.generate_nlustre_constraint_dump`):

```coq
let ordered_nodes := rev nodes in
match NAMEGEN.generate_node_scoped_env ordered_nodes with ...
```

This is not cosmetic.  Without the reversal no callee signature would
ever be found, and the generator would fail on any program with a call.
`rev_calls_precede` is the lemma that converts "further along the
program" into "already in the accumulator"; it rests on
`Ordered_nodes_calls_later` and `In_find_node`.

### The walk

`generate_all_signatures_scoped_env'_ok` inducts with `prefix` (already
generated) and `nodes` (left to do), splitting the naming run at the same
point so that the state `st` separates the two.  Three invariants ride
along:

1. `acc_covers acc prefix` — every node already walked has a signature in
   the accumulator, good, with a duplicate-free scope, and with the arity
   of its node.  This is exactly the data a call site needs.
2. `secglobal_scoped acc` — needed by `generate_node_sig_scoped` to keep
   the fresh signature scoped.
3. `secglobal_scope_bounded_above acc st` — every name the accumulator
   mentions lies below the window the next node will mint from.  This is
   what makes the caller's outputs fresh for the callee, via
   `node_scope_fresh_in_env_from_bounds`.

Re-establishing (3) across a step uses
`generated_node_sig_scope_upper_bound_from_local_env` for the fresh
signature and `secglobal_scope_bounded_above_cons/_monotone` for the rest;
re-establishing (1) needs distinct node names so that `find_signature`
still answers the same way for older entries.

One supporting fact had to be proved: `wc_global` relates each node only
to the *tail* below it, while the walk wants each node well-clocked
against the whole program.  `wc_global_Forall_wc_node` supplies that from
Velus's `wc_find_node'`.

## What is proved, and what is not

Proved: both halves above, with no admits and no axioms beyond the two
`gensym` axioms Velus already assumes (`gensym_injective'`,
`gensym_not_atom`).

Not done: the top-level theorems have not been *restated* without their
`generate_… = OK` hypotheses.  They can be, by composing with
`source_signature_generation_total` — but the chain is phrased over
`all_nodes` while totality delivers `rev all_nodes`, so it needs either a
reversal-invariance lemma for the generators or the chain restated over
the reversed list.  Nothing is unsound meanwhile: the caller supplies
what it can now prove.

## Source pointers

- Naming pass: `src/SIF/SecNamingTotality.v`
- Generator: `src/SIF/SecNLusTypingTotality.v`
- The relative chain above it: `docs/Obc-noninterference-proof.md`
- The generators themselves: `src/SIF/NameInterface.v`,
  `src/SIF/SecNLusTyping.v`
- The structural facts reused: `src/SIF/SecNLusTypingCorrectness.v`
