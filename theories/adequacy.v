From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.

From blaze Require Import logic.

Lemma rel_adequacy Σ `{!blazeGpreS Σ} e1 e2 σ1 σ2 φ :
  (∀ `{!blazeGS Σ}, ⊢ REL e1 ≤ e2 <|iThyBot|> {{ v1; v2, ⌜φ v1 v2⌝ }}) →
  adequate NotStuck e1 σ1 (λ v1 _,
    ∃ efs2 σ2' v2,
      rtc erased_step ([e2], σ2) (of_val v2 :: efs2, σ2') ∧
      φ v1 v2).
Proof.
  intros Hrel.
  apply adequate_alt=> efs σ1' /erased_steps_nsteps [n [κs Hsteps]].
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (?).
  iMod (gen_heap_init σ1.(heap)) as (?) "[Hh _]".
  iMod (ghost_map_alloc (to_labels σ1.(next_label))) as (γlabels) "[Hlabels _]".
  iMod (spec_init e2 σ2) as (?) "[#Hinv Hj]"; first done.
  iPoseProof (Hrel (BlazeGS _ _ (StateGS _ _ _ _ γlabels))) as "Hrel".
  rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iSpecialize ("Hrel" $! [] [] (λ v1 v2, ⌜φ v1 v2⌝)%I with "[]"); last simpl.
  { iApply kwp_empty. }
  iSpecialize ("Hrel" $! 0 [] with "[$Hinv] Hj").
  iModIntro.
  iExists
    (λ σ ns κs nt, gen_heap_interp σ.(heap) ∗ ghost_map_auth γlabels 1%Qp (to_labels (next_label σ)))%I,
    [(λ v1, ∃ v2 : val, 0 ⤇ v2 ∗ ⌜φ v1 v2⌝)%I],
    (λ _, True%I), _ => /=.
  iFrame. iSplitL; [iSplitL|]. { by iApply fupd_wp. } { done. }
  iIntros (efs1'' efs1' -> Hefs1'' ?) "_ Hφ _".
  assert (∃ e1', efs1'' = [e1']) as [e1' ->].
  { destruct efs1'' as [|? [|? ?]]; simpl in Hefs1''; lia || eauto. }
  rename efs1' into efs1. rewrite big_sepL2_singleton.
  destruct (to_val e1') as [v1|] eqn:He1'; last first.
  { iApply fupd_mask_intro_discard; first done. iSplit; last done.
    iIntros (v1 ? [= -> <-]). exfalso. by simpl in He1'. }
  apply of_to_val in He1' as -> => /=.
  iDestruct "Hφ" as "(%v2 & Hj & %Hφ)".
  iMod (spec_adequacy with "Hinv Hj") as (efs2 σ2') "%Hstep"; first done.
  iApply fupd_mask_intro_discard; first done. iSplit; last done.
  iIntros (? ? [= <- <-]). eauto 10.
Qed.

Lemma brel_adequacy Σ `{!blazeGpreS Σ} e1 e2 σ1 σ2 φ :
  (∀ `{!blazeGS Σ}, ⊢ BREL e1 ≤ e2 <|[]|> {{ v1; v2, ⌜φ v1 v2⌝ }}) →
  adequate NotStuck e1 σ1 (λ v1 _,
    ∃ efs2 σ2' v2,
      rtc erased_step ([e2], σ2) (of_val v2 :: efs2, σ2') ∧
      φ v1 v2).
Proof.
  intros Hbrel. eapply (rel_adequacy Σ). intros ?.
  rewrite -to_iThy_nil. iApply Hbrel.
  - iApply valid_nil.
  - iPureIntro. apply distinct_nil.
Qed.
