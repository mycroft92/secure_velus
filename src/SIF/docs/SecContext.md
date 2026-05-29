# SecContext

## Role

`SecContext.v` provides the state-and-error monad used by the SIF generators
and the small lookup lemmas that keep the typing files from repeating the same
environment plumbing.

## Main Operations

- `Sec`, `sec_state`, `init_state`
- `ret`, `bind`, `bind2`, `error`
- `find_env`
- `mmap`
- `option_to_sec`

The generators in `SecNLusTyping.v`, `SecSTCTyping.v`, and `SIFSignature.v`
all run in this monad so that generated fresh names and lookup failures are
handled uniformly.

## What The Lemmas Prove

- `sec_bind_inv` and `sec_bind2_inv` invert successful monadic computations
  into their intermediate results.
- `find_env_consistent` and `find_env_of_Env_find` relate monadic lookups back
  to plain `Env.find`.
- `find_env_in_scope` and `mmap_find_env_scoped` lift pointwise scope facts to
  successful monadic lookups.
- `option_to_sec_consistent` and `mmap_consistent` provide extensionality facts
  used when two generators are known to compute the same result.

## Downstream Use

- The typing files use `find_env_in_scope` and `mmap_find_env_scoped` whenever
  interface variables are recovered from a generated environment.
- The correctness files use the inversion lemmas to unpack successful generator
  runs.
- The translation proof relies on the consistency lemmas so that source and
  target generation can share lookup arguments without reproving monad facts
  locally.
