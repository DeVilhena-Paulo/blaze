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

  Lemma rel_rand_l k e2 L R :
    (∀ (b : bool), REL fill k #b ≤ e2 <|L|> {{R}}) -∗
    REL fill k (rand #()) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hrel". rewrite !rel_unfold /rel_def.
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
    iSpecialize ("Hrel" $! b).
    rewrite !rel_unfold /rel_def.
    iSpecialize ("Hrel" with "Hkwp").
    rewrite obs_refines_eq /obs_refines_def !fill_app.
    iApply fupd_wp. by iApply ("Hrel" with "Hspec Hj").
  Qed.

  Lemma brel_rand_l k e2 L R :
    (∀ (b : bool), BREL fill k #b ≤ e2 <|L|> {{R}}) -∗
    BREL fill k (rand #()) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbrel #Hvalid %Hdistinct". iApply rel_rand_l.
    iIntros (b). by iApply ("Hbrel" $! b).
  Qed.

  Lemma brel_rand_r (b : bool) k e1 L R :
    BREL e1 ≤ fill k #b <|L|> {{R}} -∗
    BREL e1 ≤ fill k (rand #()) <|L|> {{R}}.
  Proof.
    iIntros "Hbrel".
    rewrite /rand. brel_pures_r. iApply brel_alloc_r.
    iIntros (l2) "Hl2". rewrite fill_app //=. brel_pures_r.
    iApply brel_fork_r. iIntros (i) "Hi". rewrite fill_app //=. brel_pures_r.
    destruct b.
    - iIntros "#Hvalid %Hdistinct".
      iSpecialize ("Hbrel" with "Hvalid [//]").
      rewrite !rel_unfold /rel_pre. iIntros (k1 k2 S) "Hkwp".
      iSpecialize ("Hbrel" with "[$]").
      rewrite obs_refines_eq /obs_refines_def.
      iIntros (j k') "#Hspec Hj". iApply fupd_wp.
      iMod (step_store _ _ [] with "Hspec Hi Hl2") as "[Hi Hl2]"; first done.
      iEval (rewrite -!fill_app) in "Hj".
      iMod (step_load with "Hspec Hj Hl2") as "[Hj Hl2]"; first done.
      iEval (rewrite !fill_app) in "Hj".
      by iApply ("Hbrel" with "Hspec Hj").
    - iApply (brel_load_r with "Hl2"). iIntros "Hl2".
      by iApply "Hbrel".
  Qed.

End reasoning_rules.
