# SecContext

## Role

`SecContext.v` provides the small state-and-error monad used by the SIF
generators together with the lookup lemmas that keep the typing files from
repeating the same environment plumbing.

## Main Operations

- `Sec`, `sec_state`, `init_state`
  the generator monad and its initial fresh-name state
- `ret`, `bind`, `bind2`, `error`
  monadic return, sequencing, pair unpacking, and failure
- `find_env`
  monadic lookup in a generated environment
- `mmap`
  monadic map over a list with state threading and early failure
- `option_to_sec`
  lifts an `option` helper into the same monadic error interface

`SecNLusTyping.v`, `SecSTCTyping.v`, and parts of the signature machinery all
use this monad so that fresh-name allocation and lookup failure are handled in
one uniform way.

## Main Lemmas

- `sec_bind_inv`, `sec_bind2_inv`
  invert a successful monadic run into its exact intermediate results
- `find_env_consistent`, `find_env_of_Env_find`
  monadic lookup agrees with plain `Env.find`
- `find_env_in_scope`
  a successful lookup stays inside the expected generated scope
- `mmap_find_env_scoped`
  list-level version of the same scopedness fact
- `option_to_sec_consistent`
  two successful lifts of the same `option` value agree
- `mmap_consistent`
  pointwise-equal monadic functions produce the same successful mapped result

## Downstream Use

- the typing files use the scope lemmas when recovering inputs, outputs,
  locals, clocks, and resets from generated environments
- the correctness files use the inversion lemmas to unpack successful
  generator runs
- the translation proof uses the consistency lemmas so that source and target
  generation can share lookup arguments without reproving monad facts locally
