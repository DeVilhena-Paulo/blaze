# `blaze`: A Relational Separation Logic for Effect Handlers

## Structure

### Language (Section 3)

* [syntax.v](/theories/syntax.v): Syntax of `lambda_blaze` (`λ-blaze` in the
  paper).
* [notation.v](/theories/notation.v): Notation for `lambda_blaze` programs.
* [semantics.v](/theories/semantics.v): Semantics of `lambda_blaze`.
* [iris_instantiation.v](/theories/iris_instantiation.v): Instantiation of
  `Iris` with `lambda_blaze`.

### Logic (Section 4)

* [lifting.v](/theories/lifting.v): Lemmas about `Iris`'s `wp` needed in the
  proof of `baze`'s reasoning rules.
* [spec_rules.v](/theories/spec_rules.v): Definition of specification-side
  resources: `spec_ctx` (`specCtx` in the paper), `i ⤇ e`, `spec_label`
  (`labelₛ` in the paper), and `ℓ ↦ₛ v`.
* [state_rules.v](/theories/state_rules.v): Definition of implementation-side
  pointsto `ℓ ↦ v` (`ℓ ↦ᵢ v` in the paper).
* [logic.v](/theories/logic.v): Definition of the domain of relational theories
  `iThy`. Definition of the refinement relations from both `baze` and `blaze`.
  Statement and proof of all reasoning rules.
* [adequacy.v](/theories/adequacy.v): Proof of adequacy.

### Case studies (Section 5 + Examples)

* [countdown.v](/theories/examples/countdown.v): Example from Section 2
  whose verification in `baze` is explained in Section 4.1.
* [ask.v](/theories/examples/ask.v): Example from Section 3
  whose verification in `blaze` is explained in Section 4.2.
* [fork_1.v](/theories/examples/fork_1.v): Alternative implementation of
  the concurrency library where, in the handling of a `Fork task` effect,
  the task is stored in the queue and the continuation is immediately
  resumed.
* [fork_2.v](/theories/examples/fork_2.v): Case study from Section 5.1.
* [async_await.v](/theories/examples/async_await.v): Case study of
  the asynchronous-computation library discussed in Section 5.1 and
  included in Appendix C.2.
* [termination.ml](/src/termination.ml): `OCaml` code illustrating termination
  of a client of the handler-based implementation of `async`/`await` (Theorem C.1).
* [divergence.v](/theories/examples/divergence.v): Proof that a client
  of a handler-free implementation of `async`/`await` diverges (Theorem C.3).
* [non_determinism.v](/theories/examples/non_determinism.v): Case study from
  Section 5.2 including proof of claim that, without later credits, we can
  relate a terminating program to a diverging spec.
* [state.v](/theories/examples/state.v): Adaptation of example from
  Biernacki et al. (POPL'18).
* [exception.v](/theories/examples/exception.v): Refinement between
  (1) the iteration of a function that raises exceptions and
  (2) the iteration of a function where errors are handled in the
  option monad.


## Correspondence between paper and formalisation

|                               | Paper                   | `Rocq` formalisation         |
|-------------------------------|-------------------------|------------------------------|
| Empty protocol                | `⊥`                     | `iThyBot`                    |
| Theory sum                    | `T ⊕ F`                 | `iThySum T F`               |
| Ordering                      | `T ⊑ F`                 | `iThy_le T F`                |
| Context-closure operator      | `(lsₗ, lsᵣ) ⥯ T`        | `iThyTraverse lsₗ lsᵣ T`     |
| One-shot operator             | `◯ₘ T`                  | `iThyIfMono m T`            |
| Traversable predicat          | `traversable(Kₗ, Kᵣ, T)` | `traversable Kₗ Kᵣ T`        |
| Theory-list interpretation    | `interp(L)`              | `to_iThy L`                  |
| Theory-list validity          | `valid(L)`               | `valid L ∗ distinct' L`      |
| Theory-list one-shot operator | `◯ₘ L`                   | `to_iThyIfMono m T`         |
| Context labels                | `ℒ(K)`                   | `ectx_labels K`              |
| Labels                        | `labels_{i/s}`           | `labels_{l/r}`               |
| Label predicate               | `label_{i/s}`            | `is_label`/`spec_label`      |
| Ghost thread-pool resource    | `i ⤇ e`                  | `i ⤇ e`                     |
| Observational refinement      | `𝒪(eₗ, eᵣ, S)`           | `obs_refines eₗ eᵣ S`        |
| Validation of a theory        | `{R} Kₗ ≾ Kᵣ {S}`        | `kwp R Kₗ Kᵣ S`              |
| Refinement in `baze`          | `eₗ ≾ eᵣ ⟨T⟩ {R}`        | `EWP eₗ ≤ eᵣ <\|T\|> {{R}}`  |
| Refinement in `blaze`         | `eₗ ≾_* eᵣ ⟨L⟩ {R}`      | `BEWP eₗ ≤ eᵣ <\|L\|> {{R}}` |


## Installation

### Automatic

To install `blaze`'s dependencies and compile the proofs, it suffices to run
the script `setup.sh`:

```
chmod +x ./setup.sh
```
```
./setup.sh
```

The script creates a *local opam switch* with correct versions of `Rocq`, `stdpp`,
and `Iris` and compiles the project.

**Note**: You need the `OCaml` package manager `opam` to run this command.
We have tested with version `2.3.0`.

### Manual

Alternatively, you can install `blaze`'s dependencies manually:

- Rocq: `coq.8.20.1`
- Iris: `coq-iris-heap-lang.dev.2025-05-13.0.9f18e97d`

First, install a fresh *opam switch* (called *blaze* for example):

```
opam switch create blaze ocaml-base-compiler.5.3.0
```

Then, add the `Rocq`'s and `Iris`'s `opam` repositories:

```
opam repo add coq-released https://coq.inria.fr/opam/released
```
```
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

Finally, install `Rocq` and `Iris` with the following commands:

```
opam install coq.8.20.1
```
```
opam install coq-iris-heap-lang.dev.2025-05-13.0.9f18e97d`
```

### Troubleshooting

When running `./setup.sh`, `opam` may complain that the repository
`iris-dev` already exists with a different URL. If this happens,
please type

```
opam repo remove iris-dev --all
```

then try `./setup.sh` again. (You will later need to re-declare
the `iris-dev` repository.)
