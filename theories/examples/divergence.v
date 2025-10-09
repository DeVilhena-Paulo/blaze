(* divergence.v *)

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic Require Import weakestpre lifting adequacy.

From blaze Require Import stdpp_ext logic state_rules tactics semantics
                          class_instances proofmode lifting adequacy.

Import uPred.


(* ========================================================================= *)
(** Handler-free implementation of [async/await]. *)

Notation Done y := (InjL y) (only parsing).
Notation DoneV y := (InjLV y) (only parsing).
Notation Ongoing := (InjRV #()) (only parsing).

Section implementation.

  (* Async. *)
  Definition async : val := λ: "f",
    let: "p" := ref Ongoing in
    Fork ("p" <- Done ("f" #()));;
    "p".

  (* Await. *)
  Definition await : val := (rec: "await" "p" :=
    match: !"p" with
      (* Ongoing: *) InjL "v" =>
        "v"
    | (* Done; *) InjR <> =>
        "await" "p"
    end)%V.

  (* Example of a diverging client. *)
  Definition main : expr :=
    let: "r" := ref (InjL #()) in
    let: "f" := rec: "f" <> :=
      match: !"r" with
        InjL <> => async (λ: <>, #());; "f" #()
      | InjR "p" => await "p"
      end
    in
    let: "p" := async "f" in
    "r" <- InjR "p";;
    await "p".

End implementation.


(* ========================================================================= *)
(** Specification of [async/await]. *)

Section async_await_spec.
  Context `{!blazeGS Σ}.
  Let N := nroot .@ "promise".

  Definition promise_inv (p : loc) (Q : val → iProp Σ) : iProp Σ :=
    p ↦ Ongoing ∨ ∃ v, p ↦ DoneV v ∗ □ Q v.

  Definition is_promise (p : loc) (Q : val → iProp Σ) : iProp Σ :=
    inv (N .@ p) (promise_inv p Q).

  Global Instance is_promise_pers p Q : Persistent (is_promise p Q).
  Proof. apply _. Qed.

  Lemma async_spec (f : val) Q R :
    WP f #() {{y, □ Q y}} -∗
    (∀ (p : loc), is_promise p Q -∗ R #p) -∗
    WP async f {{R}}.
  Proof.
    iIntros "Hf HR".
    rewrite /async. wp_pures.
    iApply (wp_bind [_]).
    iApply (wp_alloc []); iIntros "!>" (p) "Hp _". simpl.
    iApply wp_value. wp_pures.
    iApply fupd_wp.
    iMod (inv_alloc (N .@ p) ⊤ (promise_inv p Q) with "[$]") as "#Hinv".
    iModIntro. iApply (wp_bind [_]).
    iApply (wp_fork [] with "[Hf]").
    { iModIntro. iApply (wp_bind [_;_]). iApply (wp_wand with "Hf").
      iIntros "%v #Hv". iApply (wp_bind [_]). wp_pures. iModIntro.
      iApply wp_atomic.
      iMod (inv_acc _ (N .@ p) with "Hinv") as "[[Hp|[%v' [Hp Hv']]] Hclose]"; first done.
      - iModIntro. iApply (wp_store [] with "Hp"). iIntros "!> Hp". simpl.
        iApply wp_value.
        iMod ("Hclose" with "[Hp]"); last done.
        by iRight; iExists v; iFrame.
      - iModIntro. iApply (wp_store [] with "Hp"). iIntros "!> Hp". simpl.
        iApply wp_value.
        iMod ("Hclose" with "[Hp]"); last done.
        by iRight; iExists v; iFrame.
    }
    simpl. iModIntro.
    iApply wp_value. wp_pures.
    by iApply "HR".
  Qed.

  Lemma await_spec p Q R :
    is_promise p Q -∗
    (∀ v, □ Q v -∗ R v) -∗
    WP await #p {{R}}.
  Proof.
    iIntros "#Hinv HR". rewrite /await.
    iLöb as "IH". wp_pures. iApply (wp_bind [_]).
    iApply wp_atomic.
    iMod (inv_acc _ (N .@ p) with "Hinv") as "[[Hp|[%v [Hp #Hv]]] Hclose]"; first done; iModIntro.
    - iApply (wp_load [] with "Hp"). iIntros "!> Hp"; simpl. iApply wp_value.
      iMod ("Hclose" with "[$]"). iModIntro. do 3 wp_pure.
      by iApply "IH".
    - iApply (wp_load [] with "Hp"). iIntros "!> Hp"; simpl. iApply wp_value.
      iMod ("Hclose" with "[Hp]"). { iRight. by iFrame. }
      iModIntro. wp_pures. by iApply "HR".
  Qed.

End async_await_spec.


(* ========================================================================= *)
(** Proof of divergence. *)

Section proof_of_divergence.
  Let N := nroot .@ "divergence".

  Lemma main_diverges `{!blazeGS Σ} : ⊢ WP main {{_, False}}.
  Proof.
    rewrite /main. iApply (wp_bind [_]). wp_pure.
    iApply (wp_alloc).
    iIntros "!> %l Hl _". simpl. iApply wp_value.
    wp_pures.

    (* Invariant on [l]: *)
    set proof_inv :=
      (l ↦ InjLV #() ∨ ∃ (p : loc), l ↦ InjRV #p ∗ is_promise p (λ _, False%I))%I.

    iApply fupd_wp.
    iMod (inv_alloc N ⊤ proof_inv with "[$]") as "#Hinv".

    iModIntro.

    iApply (wp_bind [_]).
    iApply (async_spec _ (λ _, False%I)).

    (* Verification of [f]. *)
    { iLöb as "IH".
      wp_pures. iApply (wp_bind [_]).
      iApply wp_atomic.
      iMod (inv_acc _ N with "Hinv") as "[[Hl|[%p [Hl #Hp]]] Hclose]"; first done.
      - iApply fupd_intro.
        iApply (wp_load [] with "Hl").
        iIntros "!> Hl". simpl.
        iApply wp_value.
        iSpecialize ("Hclose" with "[$]").
        iMod "Hclose". iModIntro.
        wp_pures. iApply (wp_bind [_]).
        iApply (async_spec _ (λ _, True%I)); first by wp_pures.
        iIntros (?) "_". do 2 wp_pure.
        iApply "IH".
      - iApply fupd_intro.
        iApply (wp_load [] with "Hl").
        iIntros "!> Hl". simpl.
        iApply wp_value.
        iSpecialize ("Hclose" with "[Hl]").
        { iRight. iExists p. by iFrame. }
        iMod "Hclose". iModIntro.
        wp_pures.
        by iApply (await_spec with "Hp"); auto.
    }

    iIntros (p) "#Hp". wp_pures.
    iApply (wp_bind [_]).
    iApply wp_atomic.
    iMod (inv_acc _ N with "Hinv") as "[[Hl|[% [Hl _]]] Hclose]"; first done.
    - iModIntro. iApply (wp_store [] with "Hl").
      iIntros "!> Hl". simpl. iApply wp_value.
      iMod ("Hclose" with "[Hl]"). { by iRight; iExists p; iFrame. }
      iModIntro. wp_pures.
      iApply (await_spec with "Hp"). by auto.
    - iModIntro. iApply (wp_store [] with "Hl").
      iIntros "!> Hl". simpl. iApply wp_value.
      iMod ("Hclose" with "[Hl]"). { by iRight; iExists p; iFrame. }
      iModIntro. wp_pure. wp_pure.
      iApply (await_spec with "Hp"). by auto.
  Qed.

  Lemma adequate_mono `{!blazeGpreS Σ} s (e : expr) σ P Q :
    (∀ v σ', P v σ' → Q v σ') →
    adequate s e σ P → adequate s e σ Q.
  Proof.
    intro HPQ. rewrite !adequate_alt //=. intros Hadequate.
    intros ?? Hrtc. split; [|by apply Hadequate].
    intros ?? Heq. apply HPQ. revert Heq. by apply Hadequate.
  Qed.

  Lemma main_diverges_toplevel σ : adequate NotStuck main σ (λ _ _, False).
  Proof.
    assert (∀ {H: blazeGS blazeΣ}, ⊢ REL main ≤ (#() #())%E <|iThyBot|> {{_; _, ⌜ False ⌝}}) as Hmain.
    { intros ?. rewrite rel_unfold /rel_pre.
      iIntros (k1 k2 S) "Hkwp".
      rewrite obs_refines_eq /obs_refines_def.
      iIntros "%j %k #Hspec Hj". iApply (wp_bind k1).
      iApply wp_mono; last iApply main_diverges. by iIntros (??).
    }
    eapply (@adequate_mono blazeΣ), (@rel_adequacy blazeΣ _ main _ σ σ  (λ _ _, False) Hmain).
    { by apply subG_blazeGpreS, subG_refl. }
    by intros ?? [? [? [? [? HFalse]]]].
  Qed.

  Lemma main_diverges_toplevel_alt σ :
    ∀ e' t σ',
    rtc erased_step ([main], σ) (e' :: t, σ') → reducible e' σ'.
  Proof.
    intros ??? Hrtc. simpl in *.
    specialize (main_diverges_toplevel σ) as Hadequate.
    rewrite adequate_alt in Hadequate.
    destruct (Hadequate _ _ Hrtc) as [Hnot_val Hnot_stuck].
    cut ((not_stuck e' σ') ∧ (to_val e' = None)).
    { intros [[Hval | ?] Hnot_val']; last done.
      rewrite //= Hnot_val' in Hval. by destruct Hval as [? ?].
    }
    split.
    - by apply Hnot_stuck; [|set_solver].
    - destruct (to_val e') as [v'|] eqn:Heq; last done.
      exfalso. apply (Hnot_val v' t). by rewrite //= (of_to_val e' v').
  Qed.

End proof_of_divergence.
