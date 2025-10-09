# `blaze`: A Relational Separation Logic for Effect Handlers

This repository contains the Rocq formalisation of the paper
*A Relational Separation Logic for Effect Handlers*.

To build the project, either automatically or manually,
please follow the [installation instructions](https://github.com/DeVilhena-Paulo/blaze/tree/main?tab=readme-ov-file#installation)
in this page.

## Repository structure

### Language

These files contain the definition of the syntax and semantics
of the `λ-blaze` defined in Section 3.

* [syntax.v](/theories/syntax.v): Syntax of `lambda_blaze` (`λ-blaze` in the
  paper).
* [notation.v](/theories/notation.v): Notation for `lambda_blaze` programs.
* [semantics.v](/theories/semantics.v): Semantics of `lambda_blaze`.
* [iris_instantiation.v](/theories/iris_instantiation.v): Instantiation of
  `Iris` with `lambda_blaze`.

### Logic

These files contain the definition of the model and the statement
and proof of the reasoning rules of the `blaze` and `baze` logics
defined in Section 4.

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

### Case studies

These files contain the case studies from Section 5 and
various examples studied throughout the paper.

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

### Refinements

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| Refinement 2 (§2.1)     | Lemma `countdown_refines` ([countdown.v](/theories/examples/countdown.v)) |
| Refinement 3 (§2.1)     | Lemma `run_st_passing_refines_run_heap` ([countdown.v](/theories/examples/countdown.v)) |
| Refinement 6 (§2.2)     | Lemma `countdown_refines2` ([countdown.v](/theories/examples/countdown.v)) |
| Refinement 7 (§2.2)     | Lemma `run_st_passing_refines_run_spec` ([countdown.v](/theories/examples/countdown.v)) |
| Refinement 11 (§4.2)     | Lemma `run_ask_refines` ([ask.v](/theories/examples/ask.v)) |

### Language

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| Syntax (Fig. 1.a)       | Types `expr`, `val`, `frame`, and `ectx` ([syntax.v](/theories/syntax.v)) |
| Operational rules (Fig. 1.b) | Relations `base_step` and `prim_step` ([semantics.v](/theories/semantics.v)) |
| Pure-reduction rules (Fig. 1.c) | Relation `pure_base_step` ([iris_instantiation.v](/theories/iris_instantiation.v)) |

### Model

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| Model of `baze` (Fig. 2) | Definitions in section `ewp` ([logic.v](/theories/logic.v)) |
| Model of `blaze` (Fig. 4) | Definitions in section `bewp` ([logic.v](/theories/logic.v)) |

### Rules

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| Rule `Value` (Fig. 3) | Lemma `ewp_value` ([logic.v](/theories/logic.v)) |
| Rule `Introduction` (Fig. 3) | Lemma `ewp_introduction` ([logic.v](/theories/logic.v)) |
| Rule `Bind` (Fig. 3) | Lemma `ewp_bind` ([logic.v](/theories/logic.v)) |
| Rule `Exhaustion` (Fig. 3) | Lemma `ewp_exhaustion` ([logic.v](/theories/logic.v)) |
| Rule `Monotonicity` (Fig. 3) | Lemma `ewp_wand'` ([logic.v](/theories/logic.v)) |
| Rule `Step-L` (Fig. 3) | Lemma `ewp_pure_step_l` ([logic.v](/theories/logic.v)) |
| Rule `Step-R` (Fig. 3) | Lemma `ewp_pure_step_r` ([logic.v](/theories/logic.v)) |
| Rule `Effect-L-★` (Fig. 5) | Lemma `bewp_effect_l` ([logic.v](/theories/logic.v)) |
| Rule `Effect-R-★` (Fig. 5) | Lemma `bewp_effect_r` ([logic.v](/theories/logic.v)) |
| Rule `Add-Label-L-★` (Fig. 5) | Lemma `bewp_add_label_l` ([logic.v](/theories/logic.v)) |
| Rule `Add-Label-R-★` (Fig. 5) | Lemma `bewp_add_label_r` ([logic.v](/theories/logic.v)) |
| Rule `New-Theory-★` (Fig. 5) | Lemma `bewp_new_theory` ([logic.v](/theories/logic.v)) |
| Rule `Introduction-★` (Fig. 5) | Lemma `bewp_introduction` ([logic.v](/theories/logic.v)) |
| Rule `Exhaustion-★` (Fig. 5) | Lemma `bewp_exhaustion` ([logic.v](/theories/logic.v)) |
| Rule `Bind-★` (Fig. 5) | Lemma `bewp_bind''` ([logic.v](/theories/logic.v)) |
| Rule `Gen-Monotonicity` | Lemma `ewp_mono` ([logic.v](/theories/logic.v)) |
| Rule `Fork-L-★` | Lemma `bewp_fork_l` ([logic.v](/theories/logic.v)) |
| Rule `Fork-R-★` | Lemma `bewp_fork_r` ([logic.v](/theories/logic.v)) |
| Rule `Logical-Fork-★` | Lemma `bewp_logical_fork` ([logic.v](/theories/logic.v)) |
| Rule `Thread-Swap-★` | Lemma `bewp_thread_swap` ([logic.v](/theories/logic.v)) |

### Adequacy

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| Theorem 4.1 (§4.4) | Theorem `ewp_adequacy` ([adequacy.v](/theories/adequacy.v)) |

### Case studies

| Paper                   | `Rocq` formalisation                                                |
|-------------------------|---------------------------------------------------------------------|
| `run_fork` (§5.1) | Definition `fork_handler` ([fork_2.v](/theories/examples/fork_2.v)) |
| _"`runForkSpec` holds"_ (Fig. 6) | Theorem `fork_handler_spec` ([fork_2.v](/theories/examples/fork_2.v)) |
| `Fork` (Fig. 8) | Definition `COOP` ([fork_1.v](/theories/examples/fork_1.v)) |
| `queueInv` (Fig. 8) | Definition `preInv` ([fork_2.v](/theories/examples/fork_2.v)) |
| `run_coop₁` (Fig. 9) | Definition `run_coop₁` ([async_await.v](/theories/examples/async_await.v)) |
| `run_coop₂` (Fig. 9) | Definition `run_coop₂` ([async_await.v](/theories/examples/async_await.v)) |
| _"`run_coop₃ deadlock` diverges"_ (§5.1.3) | Lemma `main_diverges_toplevel_alt` ([divergence.v](/theories/examples/divergence.v)) |
| _"`run_coop₁ deadlock` terminates"_ (§5.1.3) | Execution of [termination.ml](/src/termination.ml) |
| `Nd` | Definition `Nd` ([non_determinism.v](/theories/non_determinism.v)) |
| _"`runNdCorrect(run_nd_pure)` holds"_ | Lemma `ndet_run_pure_correct` ([non_determinism.v](/theories/non_determinism.v)) |
| _"`runNdCorrect(run_nd_rand)` holds"_ | Lemma `ndet_run_rand_correct` ([non_determinism.v](/theories/non_determinism.v)) |


### Notation

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

**Note**: To run this command, you need
[`opam`](https://opam.ocaml.org/doc/Install.html), the OCaml package manager.
We have tested with version `2.3.0`.

### Manual

Alternatively, you can install `blaze`'s dependencies manually:

- Rocq: `coq.8.20.1`
- Iris: `coq-iris-heap-lang.dev.2025-05-13.0.9f18e97d`

First, install a fresh *opam switch* (called *blaze* for example):

```
opam switch create blaze ocaml-base-compiler.5.3.0
```

Then, add `Rocq`'s and `Iris`'s `opam` repositories:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

Finally, install `Rocq` and `Iris` with the following commands:

```
opam install coq.8.20.1
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
