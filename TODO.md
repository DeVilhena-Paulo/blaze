## TODO

* Multishot/oneshot
    - [x] Add syntax and semantics for oneshot continuations.
    - [x] Add support for oneshot continuations in the logic.

* Multiple effect branches
    - [x] Add support both in the logic for handlers with multiple effect branches

* Concurrency & mutable state
    - [x] Add support for concurrency and mutable state in the language and in the logic.

* Applications
    - [x] Asynchronous library.
    - [ ] Binary logical relations.
    - [ ] Relational logic for multiple control operators (`call/cc`, `shift` & `reset`, etc).

* Better names
    - [x] `iEff` -> `iProtTraverse`? (because it makes the protocol "traverse" a context)
    - [x] `compatible` -> `traversable`?
    - [x] `isEffLeft`/`isEffRight` (I got rid of these)
    - [ ] `is_label` -> `impl_label`/`arg_label`/`src_label`?

* Refactoring
    - [x] Get rid of `NeutralEctx`/`NeutralFrame` and write `∀ l, l ∈ ls → l ∉ ectx_labels k` instead of `NeutralEctx ls k`. (I didn't get rid of `NeutralEctx`/`NeutralFrame`, but `NeutralEctx ls k` is now defined as `∀ l, l ∈ ls → l ∉ ectx_labels k` .)
    - [x] Change definition of `to_eff` to a function of type `expr → option (ectx, label, val)` s.t. `to_eff e = Some (k, l, v) ⇔ e = fill k (do l v)` and place conditions on `ectx_labels k` only in the definition of `base_step`.
