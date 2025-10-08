(* rand_lib.v *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From blaze Require Import stdpp_ext logic state_rules proofmode lifting.


(* ========================================================================== *)
(** Implementation. *)

Section implementation.

  Definition rand : val := λ: <>,
    let: "b" := ref #false in Fork ("b" <- #true);; !"b".

End implementation.


(* ========================================================================== *)
(** Reasoning rules. *)

Section reasoning_rules.
  Context `{!blazeGS Σ}.

  Lemma ewp_rand_l k e2 L R :
    (∀ (b : bool), EWP fill k #b ≤ e2 <|L|> {{R}}) -∗
    EWP fill k (rand #()) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hewp". rewrite !ewp_unfold /ewp_def.
    iIntros (k1 k2 S) "Hkwp".
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (j k') "#Hspec Hj". rewrite -!fill_app.
    rewrite /rand. iModIntro. wp_pures. rewrite -!fill_app.
    iApply (wp_bind _).
    iApply (wp_alloc [_]). iIntros "!>" (l) "Hl _". wp_pures.
    iApply (wp_bind [_]).

    (* Invariant: [∃ (b : bool), l ↦ #b] *)
    set proof_inv := (∃ (b : bool), l ↦ #b)%I.
    set N := nroot .@ "rand".

    iApply fupd_wp.
    iMod (inv_alloc N ⊤ proof_inv with "[$]") as "#Hinv".
    iModIntro.

    iApply (wp_fork []).
    { iModIntro.
      iApply wp_atomic.
      iMod (inv_acc _ N with "Hinv") as "[[%b Hl] Hclose]"; first done.
      iModIntro. iApply (wp_store [] with "Hl").
      iIntros "!> Hl"; simpl. iApply wp_value.
      by iMod ("Hclose" with "[$]").
    }

    iModIntro. simpl. iApply wp_value. wp_pures.
    iApply wp_atomic.
    iMod (inv_acc _ N with "Hinv") as "[[%b Hl] Hclose]"; first done.
    iModIntro. iApply (wp_load [] with "Hl").
    iIntros "!> Hl"; simpl. iApply wp_value.
    iMod ("Hclose" with "[$]"). iModIntro.
    iSpecialize ("Hewp" $! b).
    rewrite !ewp_unfold /ewp_def.
    iSpecialize ("Hewp" with "Hkwp").
    rewrite obs_refines_eq /obs_refines_def !fill_app.
    iApply fupd_wp. by iApply ("Hewp" with "Hspec Hj").
  Qed.

  Lemma bewp_rand_l k e2 L R :
    (∀ (b : bool), BEWP fill k #b ≤ e2 <|L|> {{R}}) -∗
    BEWP fill k (rand #()) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbewp #Hvalid %Hdistinct". iApply ewp_rand_l.
    iIntros (b). by iApply ("Hbewp" $! b).
  Qed.

  Lemma bewp_rand_r (b : bool) k e1 L R :
    BEWP e1 ≤ fill k #b <|L|> {{R}} -∗
    BEWP e1 ≤ fill k (rand #()) <|L|> {{R}}.
  Proof.
    iIntros "Hbewp".
    rewrite /rand. bewp_pures_r. iApply bewp_alloc_r.
    iIntros (l2) "Hl2". rewrite fill_app //=. bewp_pures_r.
    iApply bewp_fork_r. iIntros (i) "Hi". rewrite fill_app //=. bewp_pures_r.
    destruct b.
    - iIntros "#Hvalid %Hdistinct".
      iSpecialize ("Hbewp" with "Hvalid [//]").
      rewrite !ewp_unfold /ewp_pre. iIntros (k1 k2 S) "Hkwp".
      iSpecialize ("Hbewp" with "[$]").
      rewrite obs_refines_eq /obs_refines_def.
      iIntros (j k') "#Hspec Hj". iApply fupd_wp.
      iMod (step_store _ _ [] with "Hspec Hi Hl2") as "[Hi Hl2]"; first done.
      iEval (rewrite -!fill_app) in "Hj".
      iMod (step_load with "Hspec Hj Hl2") as "[Hj Hl2]"; first done.
      iEval (rewrite !fill_app) in "Hj".
      by iApply ("Hbewp" with "Hspec Hj").
    - iApply (bewp_load_r with "Hl2"). iIntros "Hl2".
      by iApply "Hbewp".
  Qed.

End reasoning_rules.
