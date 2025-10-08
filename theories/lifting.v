From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From blaze Require Import syntax semantics iris_instantiation tactics.

(** Lifting lemmas where we can do a [base_step] under an evaluation context.
    We need these because we cannot easily write down a bind lemma, due to the non-local control flow of effects. *)
Section lifting.
  Context `{!irisGS lambda_blaze Σ}.

  Lemma wp_lift_fill_base_step {K s E Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
      ⌜base_reducible e1 σ1⌝ ∗
      ▷ ∀ e2 σ2 efs, ⌜base_step e1 σ1 e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        WP fill K e2 @ s; E {{ Φ }} ∗
        [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP fill K e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step; first by apply fill_not_val.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" with "Hσ1") as "[% H]".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iSplit; first destruct s; auto using reducible_fill, base_reducible_reducible.
    iNext. iIntros (e2 σ2 efs Hstep) "Hcred". iMod "Hclose" as "_".
    destruct κ as [|??]; last done.
    apply base_reducible_prim_step_ctx in Hstep as (e' & -> & Hstep); last done.
    by iApply "H".
  Qed.

  Lemma wp_lift_fill_base_step_fupd {K s E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
      ⌜base_reducible e1 σ1⌝ ∗
      ∀ e2 σ2 efs, ⌜base_step e1 σ1 e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        WP fill K e2 @ s; E1 {{ Φ }} ∗
        [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP fill K e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupd; first by apply fill_not_val.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" with "Hσ1") as "[% H]".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iSplit; first by destruct s; auto using reducible_fill, base_reducible_reducible.
    iIntros (e2 σ2 efs Hstep) "Hcred". iMod "Hclose" as "_".
    destruct κ as [|??]; last done.
    apply base_reducible_prim_step_ctx in Hstep as (e' & -> & Hstep); last done.
    iMod ("H" with "[//] Hcred") as "H".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iNext. iMod "Hclose" as "_". by iMod "H" as "($ & $ & $)".
  Qed.

  Lemma wp_lift_fill_base_step_no_fork_fupd {K s E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
      ⌜base_reducible e1 σ1⌝ ∗
      ∀ e2 σ2 efs, ⌜base_step e1 σ1 e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
        ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ WP fill K e2 @ s; E1 {{ Φ }})
    ⊢ WP fill K e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_fill_base_step_fupd; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
    iIntros (v2 σ2 efs Hstep) "Hcred".
    iMod ("H" $! v2 σ2 efs with "[# //] Hcred") as "H".
    iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
  Qed.

  Lemma wp_lift_fill_base_step_no_fork {K s E Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
      ⌜base_reducible e1 σ1⌝ ∗
      ▷ ∀ e2 σ2 efs, ⌜base_step e1 σ1 e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
        ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ WP fill K e2 @ s; E {{ Φ }})
    ⊢ WP fill K e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_fill_base_step; first done.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
    iNext; iIntros (v2 σ2 efs Hstep) "Hcred".
    iMod ("H" $! v2 σ2 efs with "[//] Hcred") as "(-> & ? & ?) /=". by iFrame.
  Qed.

  Lemma wp_bind k E e Φ :
    WP e @ NotStuck; E {{ v, WP fill k (of_val v) @ NotStuck; E {{ Φ }} }}
    ⊢ WP fill k e @ NotStuck; E {{ Φ }}.
  Proof.
    iIntros "Hwp". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { apply of_to_val in He as ->. by iApply fupd_wp. }
    rewrite wp_unfold /wp_pre. simpl.
    rewrite fill_not_val He //=.
    iIntros (σ1 step κ κs n) "Hσ".
    iMod ("Hwp" with "[$]") as "[%Hreducible Hwp]".
    specialize (reducible_not_eff _ _ Hreducible) as Hnot_eff.
    iModIntro; iSplit.
    { eauto using reducible_fill. }
    iIntros (e2 σ2 efs Hstep) "Hcred".
    destruct κ => //=. simpl in Hstep.
    destruct (Ectx_prim_step_not_val_not_eff_inv _ _ _ _ _ _ He Hnot_eff Hstep) as (e2'&Hstep'&->).
    iMod ("Hwp" $! e2' σ2 efs with "[//] Hcred") as "Hwp". iIntros "!>!>".
    iMod "Hwp". iModIntro. iApply (step_fupdN_wand with "Hwp"). iIntros "Hwp".
    iMod "Hwp" as "($ & H & $)". iModIntro. by iApply "IH".
  Qed.

End lifting.
