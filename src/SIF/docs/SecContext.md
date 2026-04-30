# SecContext

## Role

`SecContext.v` provides the small state/error monad and generic environment
lookup lemmas used by every SIF generator.

It is not a typing file by itself.  Its job is to keep the recurring
environment plumbing out of the NLustre, STC, and translation proofs.

## Main Definitions

- `Sec`: stateful error monad used by the generators
- `sec_state`, `init_state`
- `bind`, `bind2`, `ret`, `error`
- `find_env`: monadic wrapper around `Env.find`
- `mmap`: monadic list traversal
- `option_to_sec`: convert `option` failures into monadic failures

## Key Theorem Families

- monad inversion:
  - `sec_bind_inv`
  - `sec_bind2_inv`
- environment lookup consistency/scopedness:
  - `find_env_consistent`
  - `find_env_of_Env_find`
  - `find_env_in_scope`
  - `mmap_find_env_scoped`
- generic monadic extensionality/consistency:
  - `option_to_sec_consistent`
  - `mmap_consistent`

## Relation To The Final Theorem

These lemmas sit below every later proof layer:

- `SecNLusTyping.v` and `SecSTCTyping.v` use them to turn lookups into scoped
  typing facts.
- the correctness modules reuse them when reconstructing generated naming and
  signature facts.
- `SecNLusStcTranslation.v` relies on the shared lookup-consistency facts so
  it does not have to duplicate environment plumbing in the cross-phase proof.

