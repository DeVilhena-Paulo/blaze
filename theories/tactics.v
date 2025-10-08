(* tactics.v *)

(* Adapted from [iris_heap_lang/tactics.v]. *)

From stdpp Require Import fin_maps.
From iris.prelude Require Import options.

From blaze Require Export syntax semantics.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.
