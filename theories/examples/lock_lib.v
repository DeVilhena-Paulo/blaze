(* lock.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants token.
From iris.program_logic Require Import weakestpre lifting.

From blaze Require Import stdpp_ext logic state_rules proofmode lifting.


(* ========================================================================== *)
(** Implementation of a spin lock. *)

Section implementation.

  Definition new_lock : val := (λ: <>, ref #0)%V.

  Definition acquire : val := (rec: "try_acquire" "lock" :=
    let: "succeeded?" := Snd (CmpXchg "lock" #0 #1) in
    if: "succeeded?" then #() else "try_acquire" "lock"
  )%V.

  Definition release : val := (λ: "lock", "lock" <- #0)%V.

End implementation.


(* ========================================================================= *)
(** Reasoning rules [bewp]. *)

(* For now, we only have reasoning rules for the specication side,
 * because we lack useful [bewp] rules to manipulate invariants. *)

Section bewp_reasoning_rules.
  Context `{!blazeGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Specification side. *)

  Lemma ewp_new_lock_r X R e1 k2 :
    (∀ lock2, lock2 ↦ₛ #0 -∗ EWP e1 ≤ fill k2 #lock2 <|X|> {{R}}) -∗
    EWP e1 ≤ fill k2 (new_lock #()) <|X|> {{R}}.
  Proof.
    iIntros "Hfill". rewrite /new_lock. ewp_pures_r.
    by iApply ewp_alloc_r.
  Qed.

  Lemma bewp_new_lock_r L R e1 k2 :
    (∀ lock2, lock2 ↦ₛ #0 -∗ BEWP e1 ≤ fill k2 #lock2 <|L|> {{R}}) -∗
    BEWP e1 ≤ fill k2 (new_lock #()) <|L|> {{R}}.
  Proof.
    iIntros "Hfill". rewrite /new_lock.
    bewp_pures_r.
    by iApply bewp_alloc_r.
  Qed.

  Lemma ewp_acquire_r_with_mask E X R e1 k2 lock2 :
    ↑specN ⊆ E →
    lock2 ↦ₛ #0 -∗
    (lock2 ↦ₛ #1 -∗ EWP e1 ≤ fill k2 #() @E <|X|> {{R}}) -∗
    EWP e1 ≤ fill k2 (acquire #lock2) @E <|X|> {{R}}.
  Proof.
    iIntros (HE) "Hlock Hfill". rewrite /acquire.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, _. } { done. } simpl.
    rewrite -(fill_app k2 [AppRCtx _; SndCtx]).
    iApply (ewp_cmpxchg_suc_r_with_mask with "Hlock"); try done.
    iIntros "Hlock". rewrite fill_app. simpl.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, (pure_exec_fill [AppRCtx _]), _. } { done. } simpl.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, (pure_exec_fill [AppLCtx _]), _. } { done. } simpl.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, _. } { done. } simpl.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, _. } { done. } simpl.
    by iApply "Hfill".
  Qed.    

  Lemma bewp_acquire_r L R e1 k2 lock2 :
    lock2 ↦ₛ #0 -∗
    (lock2 ↦ₛ #1 -∗ BEWP e1 ≤ fill k2 #() <|L|> {{R}}) -∗
    BEWP e1 ≤ fill k2 (acquire #lock2) <|L|> {{R}}.
  Proof.
    iIntros "Hlock Hfill". rewrite /acquire.
    bewp_pures_r.
    iApply (bewp_cmpxchg_suc_r with "Hlock"); first done.
    iIntros "Hlock". rewrite fill_app //=.
    bewp_pures_r.
    by iApply ("Hfill" with "Hlock").
  Qed.

  Lemma ewp_release_r_with_mask E X R e1 k2 lock2 :
    ↑specN ⊆ E →
    lock2 ↦ₛ #1 -∗
    (lock2 ↦ₛ #0 -∗ EWP e1 ≤ fill k2 #() @E <|X|> {{R}}) -∗
    EWP e1 ≤ fill k2 (release #lock2) @E <|X|> {{R}}.
  Proof.
    iIntros "%HE Hlock Hfill". rewrite /release.
    iApply ewp_pure_step_r_with_mask; auto.
    { apply pure_exec_fill, _. } { done. } simpl.
    by iApply (ewp_store_r_with_mask with "Hlock"); first done.
  Qed.

  Lemma bewp_release_r L R e1 k2 lock2 :
    lock2 ↦ₛ #1 -∗
    (lock2 ↦ₛ #0 -∗ BEWP e1 ≤ fill k2 #() <|L|> {{R}}) -∗
    BEWP e1 ≤ fill k2 (release #lock2) <|L|> {{R}}.
  Proof.
    iIntros "Hlock Hfill". rewrite /release.
    bewp_pures_r.
    iApply (bewp_store_r with "Hlock").
    iIntros "Hlock".
    by iApply ("Hfill" with "Hlock").
  Qed.

End bewp_reasoning_rules.
