# SecContext

## Role

`SecContext.v` provides the state-and-error monad used by the SIF generators
and the small lookup lemmas that keep the typing files from repeating the same
environment plumbing.

## Main Operations

- `Sec`, `sec_state`, `init_state`
  define the state-and-error monad used by all security generators and the
  initial fresh-name state they start from.
- `ret`, `bind`, `bind2`, `error`
  are the monadic constructors for returning values, sequencing computations,
  unpacking pairs, and reporting generation failure.
- `find_env`
  lifts a plain environment lookup into the monad so missing names become
  explicit generator errors.
- `mmap`
  runs a monadic generator over a list while threading state and stopping on
  the first failure.
- `option_to_sec`
  turns an `option`-producing helper into the same monadic error interface.

The generators in `SecNLusTyping.v`, `SecSTCTyping.v`, and `SIFSignature.v`
all run in this monad so that generated fresh names and lookup failures are
handled uniformly.

## What The Lemmas Prove

- `sec_bind_inv` and `sec_bind2_inv`
  let a successful monadic run be split back into the exact intermediate value
  and state produced by each stage.
- `find_env_consistent` and `find_env_of_Env_find`
  show that monadic lookup and plain `Env.find` return the same identifier when
  both succeed.
- `find_env_in_scope`
  turns a local scope hypothesis on raw variables into a scope fact for the
  generated identifier returned by `find_env`.
- `mmap_find_env_scoped`
  lifts that same argument from one lookup to a whole successful list lookup.
- `option_to_sec_consistent`
  says two successful lifts of the same `option` value must return the same
  result.
- `mmap_consistent`
  gives list-level extensionality: pointwise-equal monadic functions produce
  the same successful mapped result.

## Downstream Use

- The typing files use `find_env_in_scope` and `mmap_find_env_scoped` whenever
  interface variables are recovered from a generated environment.
- The correctness files use the inversion lemmas to unpack successful generator
  runs.
- The translation proof relies on the consistency lemmas so that source and
  target generation can share lookup arguments without reproving monad facts
  locally.
