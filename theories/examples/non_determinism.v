(* non_determinism.v *)

From iris.proofmode Require Import base tactics classes.
From blaze Require Import stdpp_ext logic state_rules proofmode list_lib rand_lib.


(* ************************************************************************* *)
(** Non-Determinism. *)

(* ========================================================================= *)
(* Implementation & Specification. *)

Section implemantation_and_specification.

  Definition fail' (ndet : eff_val) : expr := do: ndet (InjRV #())%V.
  Definition pick (ndet : eff_val) (e1 e2 : expr) : expr :=
    (do: ndet (InjL ((λ: <>, e1), (λ: <>, e2)))) #().

  (* ----------------------------------------------------------------------- *)
  (* Pure implementation using lists. *)

  (* This implementation validates the equations
       [pick e1 (pick e2 e3) = pick (pick e1 e2) e3]
     and
       [pick e fail = pick fail e = e].
   *)

  Definition ndet_run_pure (ndet : eff_val) (e : expr) : expr :=
    handle: e with
    | effect ndet "request", rec "k" as multi =>
        match: "request" with
          (* Pick: *) InjL "args" =>
            let: "e1" := Fst "args" in let: "e2" := Snd "args" in
            list_concat ("k" "e1") ("k" "e2")
        | (* Fail: *) InjR <> =>
            list_nil
        end
    | return "y" =>
        list_singleton "y"
    end%E.

  (* ----------------------------------------------------------------------- *)
  (* Imperative implementation using actual non-determinism. *)

  (* This implementation additionally validates the equation
       [pick e1 e2 = pick e2 e1].
   *)

  Definition rand_bool : val := λ: <>,
    let: "b" := ref #false in Fork ("b" <- #true);; !"b".
  Definition diverge : expr := (rec: "diverge" <> := "diverge" #()) #().
  Definition ndet_run_rand (ndet : eff_val) (e : expr) : expr :=
    handle: e with
    | effect ndet "request", rec "k" as multi =>
        match: "request" with
          (* Pick: *) InjL "args" =>
            let: "e1" := Fst "args" in let: "e2" := Snd "args" in
            if: rand_bool #() then "k" "e1" else "k" "e2"
        | (* Fail: *) InjR <> =>
            diverge
        end
    | return "y" =>
        "y"
    end%E.

End implemantation_and_specification.


(* ========================================================================= *)
(* Non-Determinism Relational Theory. *)

Section ndet_theory.
  Context `{!blazeGS Σ}.

  Definition same_result : val → val → iProp Σ := λ v1 v2, ⌜ v1 = v2 ⌝%I.

  Program Definition Refl1 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e11 e12 e21 e22 : expr),
    ⌜ e1 = pick ndet e11 e12 ⌝ ∗
    ⌜ e2 = pick ndet e21 e22 ⌝ ∗
    □ Q e11 e21 ∗
    □ Q e12 e22
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Refl2 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ⌜ e1 = fail' ndet ⌝ ∗
    ⌜ e2 = fail' ndet ⌝
  )%I.

  Program Definition Assoc1 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e11 e12 e13 e21 e22 e23 : expr),
    ⌜ e1 = pick ndet e11 (pick ndet e12 e13) ⌝ ∗
    ⌜ e2 = pick ndet (pick ndet e21 e22) e23 ⌝ ∗
    □ Q e11 e21 ∗
    □ Q e12 e22 ∗
    □ Q e13 e23
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Assoc2 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e11 e12 e13 e21 e22 e23 : expr),
    ⌜ e1 = pick ndet (pick ndet e11 e12) e13 ⌝ ∗
    ⌜ e2 = pick ndet e21 (pick ndet e22 e23) ⌝ ∗
    □ Q e11 e21 ∗
    □ Q e12 e22 ∗
    □ Q e13 e23
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Unit1 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e1' : expr),
    ⌜ e1 = pick ndet (fail' ndet) e1' ⌝ ∗
    □ Q e1' e2
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Unit2 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e1' : expr),
    ⌜ e1 = pick ndet e1' (fail' ndet) ⌝ ∗
    □ Q e1' e2
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Unit3 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e2' : expr),
    £ 1 ∗
    ⌜ e2 = pick ndet (fail' ndet) e2' ⌝ ∗
    □ Q e1 e2'
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Unit4 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e2' : expr),
    £ 1 ∗
    ⌜ e2 = pick ndet e2' (fail' ndet) ⌝ ∗
    □ Q e1 e2'
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Comm (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e11 e12 e21 e22 : expr),
    ⌜ e1 = pick ndet e11 e12 ⌝ ∗
    ⌜ e2 = pick ndet e21 e22 ⌝ ∗
    □ Q e11 e22 ∗
    □ Q e12 e21
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition ND ndet : iThy Σ :=
    iThySum (Refl1  ndet) (
    iThySum (Refl2  ndet) (
    iThySum (Assoc1 ndet) (
    iThySum (Assoc2 ndet) (
    iThySum (Unit1  ndet) (
    iThySum (Unit2  ndet) (
    iThySum (Unit3  ndet) (
            (Unit4  ndet)
    ))))))).

  Program Definition ND_ext ndet : iThy Σ :=
    iThySum (ND ndet) (Comm ndet).

End ndet_theory.


(* ========================================================================= *)
(* Handlee Examples. *)

Section handlee_examples.
  Context `{!blazeGS Σ}.

  Variables (ndet : label).

  Notation pick' e1 e2 := (pick ndet e1 e2).
  Notation fail' := (fail' ndet).

  Example ex1 (n : Z) L :
    let L' := ([ndet], [ndet], ND ndet) :: L in
    ⊢ BREL (if: pick' fail' #true then
              pick' #n (pick' fail' (#n + #1))
            else
              fail')
      ≤    (pick' #n (#n + #1))
           <|L'|> {{same_result}}.
  Proof.
    intros L'. rewrite /L'.

    iApply (brel_introduction' [ndet] [ndet] (ND ndet)).
    { by apply elem_of_cons; left. }
    iExists (pick' fail' #true), (pick' _ _), [IfCtx (pick' _ (pick' fail' _)) fail'], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by simpl; iIntros "!> %% H"; iApply "H"].
    iRight. iRight. iRight. iRight. iLeft.
    iExists #true. iSplit; try done.
    iIntros "!>". simpl.
    brel_pure_l.

    iApply (brel_introduction' [ndet] [ndet] (ND ndet)); last auto.
    { by apply elem_of_cons; left. }

    iExists (pick' _ (pick' fail' _)), (pick' _ _), [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by simpl; iIntros "!> %% H"; iApply "H"].
    iLeft.
    iExists #n, (pick' fail' (#n + #1)%E), #n, (#n + #1)%E.
    (repeat iSplit; try done); last auto.
    { iIntros "!>"; by iApply brel_value. }

    iIntros "!>". simpl.

    iApply (brel_introduction' [ndet] [ndet] (ND ndet)).
    { by apply elem_of_cons; left. }
    iExists (pick' fail' _), _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by simpl; iIntros "!> %% H"; iApply "H"].
    iRight. iRight. iRight. iRight. iLeft.
    iExists (#n + #1)%E. iSplit; try done.
    iIntros "!>". simpl.
    brel_pures_l. by brel_pures_r.
  Qed.

  Example ex2 L :
    let L' := ([ndet], [ndet], ND ndet) :: L in
    ⊢ BREL (let: "x" := pick' #0 (pick' #1 #2) in
            if: pick' fail' #true then
              pick' "x" (pick' fail' ("x" + #1))
            else
              fail')
      ≤    (let: "x" := pick' (pick' #0 #1) #2 in
            pick' "x" ("x" + #1))
           <|L'|> {{same_result}}.
  Proof.
    intros L'. rewrite /L'.
    iApply (brel_bind' [_] [AppRCtx _]).
    { iApply traversable_to_iThy; intros ?; constructor; set_solver. }

    iApply (brel_introduction' [ndet] [ndet] (ND ndet)).
    { by apply elem_of_cons; left. }

    iExists (pick' #0 (pick' #1 #2)), (pick' (pick' #0 #1) #2), [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by simpl; iIntros "!> %% H"; iApply "H"].
    iRight. iRight. iLeft.
    iExists #0, #1, #2, #0, #1, #2. do 2 (iSplit; try done).
    by iSplit; [|iSplit]; iModIntro; iApply brel_value;
    do 2 brel_pure_l; do 2 brel_pure_r;
    iApply ex1.
  Qed.

End handlee_examples.


(* ========================================================================= *)
(* Handler Correctness. *)

Section ndet_run_pure_correctness.
  Context `{!blazeGS Σ}.

  Lemma ndet_run_pure_correct ndet e1 e2 L :
    BREL e1 ≤ e2 <|([ndet], [ndet], ND ndet) :: L|> {{same_result}} -∗
    BREL ndet_run_pure ndet e1 ≤
         ndet_run_pure ndet e2
         <|([ndet], [ndet], iThyBot) :: L|>
         {{v1; v2, ∃ xs, ⌜ v1 = v2 ⌝ ∗ ⌜ v2 = list_to_val xs ⌝ }}.
  Proof.
    iIntros "Hbrel".
    rewrite /ndet_run_pure.
    iLöb as "IH" forall (e1 e2).
    iApply (brel_exhaustion with "Hbrel"). { by simpl. } { by simpl. }
    iSplit.
    - iIntros "!> %%->". brel_pures_l. brel_pures_r.
      iModIntro. by iExists [v2].
    - iIntros "!> %%%%% %Hk1' %Hk2' HND #Hk".
      iDestruct "HND" as "[HND|[HND|[HND|[HND|[HND|[HND|[HND|HND]]]]]]]".

      (* Refl1. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e21 [%e22 HND]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pure_l.
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r.
        iApply (brel_bind' [_] [_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%ys [-> ->]]".
        do 2 brel_pures_l.
        do 2 brel_pures_r.
        iApply (brel_bind' [_;_] [_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%xs [-> ->]]".
        iApply brel_list_concat_l. iNext.
        iApply brel_list_concat_r.
        iApply brel_value.
        by iExists (xs ++ ys).

      (* Refl2. *)
      + iDestruct "HND" as "[-> ->]".
        brel_pures_l.
        { apply neutral_ectx; set_solver. }
        brel_pures_r.
        { apply neutral_ectx; set_solver. }
        by iExists [].

      (* Assoc1. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e13 [%e21 [%e22 [%e23 HND]]]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2 & #He3)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r. brel_pures_l.
        iApply (brel_bind' [_; _] [_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%zs [-> ->]]".
        do 2 brel_pures_l. do 6 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r.
        iApply (brel_bind' [_;_;_] [_;_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%ys [-> ->]]".
        iApply (brel_list_concat_l). iNext.
        do 2 brel_pures_l. do 2 brel_pures_r.
        iApply (brel_bind' [_;_] [_;_;_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%xs [-> ->]]".
        iApply (brel_list_concat_l). iNext.
        iApply (brel_list_concat_r).
        iApply (brel_list_concat_r).
        rewrite -app_assoc.
        iApply brel_value.
        by iExists (xs ++ ys ++ zs).

      (* Assoc2. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e13 [%e21 [%e22 [%e23 HND]]]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2 & #He3)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r. brel_pures_l.
        iApply (brel_bind' [_] [_; _]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%zs [-> ->]]".
        do 2 brel_pures_r. do 6 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_l.
        iApply (brel_bind' [_;_;_] [_;_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%ys [-> ->]]".
        iApply (brel_list_concat_r).
        do 2 brel_pures_l. do 2 brel_pures_r.
        iApply (brel_bind' [_;_;_;_] [_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> % % [%xs [-> ->]]".
        iApply (brel_list_concat_l). iNext.
        iApply (brel_list_concat_l). iNext.
        iApply (brel_list_concat_r).
        rewrite -app_assoc.
        iApply brel_value.
        by iExists (xs ++ ys ++ zs).

      (* Unit1. *)
      + iDestruct "HND" as "[%e11 [-> #HQ]]".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_l.
        iApply (brel_bind' [_] []).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%xs [-> ->]]".
        do 2 brel_pures_l. { by apply neutral_ectx; set_solver. }
        iApply (brel_list_concat_l _ []). iNext.
        iApply brel_value.
        by iExists xs.

      (* Unit2. *)
      + iDestruct "HND" as "[%e11 [-> #HQ]]".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_l.
        { by apply neutral_ectx; set_solver. }
        brel_pures_l.
        iApply (brel_bind' [_;_] []).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%xs [-> ->]]".
        iApply (brel_list_concat_l _ xs []). iNext.
        rewrite app_nil_r.
        iApply brel_value.
        by iExists xs.

      (* Unit3. *)
      + iDestruct "HND" as "[%e22 (Hlc & -> & #HQ)]".
        iAssert (▷ □ _)%I as "IHHk".
        { iNext. iCombine "IH Hk" as "#IHHk". by iApply "IHHk". }
        iClear "IH Hk".
        iApply fupd_brel.
        iMod (lc_fupd_elim_later ⊤ with "Hlc IHHk") as "[#IH #Hk]". iClear "IHHk".
        iModIntro. do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r.
        iApply (brel_bind' [] [_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%xs [-> ->]]".
        do 2 brel_pures_r. { by apply neutral_ectx; set_solver. }
        iApply (brel_list_concat_r _ []).
        iApply brel_value.
        by iExists xs.

      (* Unit4. *)
      + iDestruct "HND" as "[%e22 (Hlc & -> & #HQ)]".
        iAssert (▷ □ _)%I as "IHHk".
        { iNext. iCombine "IH Hk" as "#IHHk". by iApply "IHHk". }
        iClear "IH Hk".
        iApply fupd_brel.
        iMod (lc_fupd_elim_later ⊤ with "Hlc IHHk") as "[#IH #Hk]". iClear "IHHk".
        iModIntro. do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        brel_pures_r.
        { by apply neutral_ectx; set_solver. }
        brel_pures_r.
        iApply (brel_bind' [] [_;_]).
        { iApply traversable_to_iThy; intros ?; constructor; set_solver. }
        iApply brel_wand.
        { iApply "IH". by iApply "Hk". }
        iIntros "!> %% [%xs [-> ->]]".
        iApply (brel_list_concat_r _ xs []).
        rewrite app_nil_r.
        iApply brel_value.
        by iExists xs.
  Qed.

End ndet_run_pure_correctness.


Section ndet_run_rand_correctness.
  Context `{!blazeGS Σ}.

  Lemma ndet_run_rand_correct ndet e1 e2 L :
    BREL e1 ≤ e2 <|([ndet], [ndet], ND_ext ndet) :: L|> {{same_result}} -∗
    BREL ndet_run_rand ndet e1 ≤
         ndet_run_rand ndet e2
         <|([ndet], [ndet], iThyBot) :: L|>
         {{same_result}}.
  Proof.
    iIntros "Hbrel".
    rewrite /ndet_run_rand.
    iLöb as "IH" forall (e1 e2).
    iApply (brel_exhaustion with "Hbrel"). { by simpl. } { by simpl. }
    iSplit.
    - iIntros "!> %%->". brel_pures_l. by brel_pures_r.
    - iIntros "!> %%%%% %Hk1' %Hk2' HND #Hk".
      iDestruct "HND" as "[[HND|[HND|[HND|[HND|[HND|[HND|[HND|HND]]]]]]]|HND]".

      (* Refl1. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e21 [%e22 HND]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b).
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply (brel_rand_r b).
        destruct b.
        * do 2 brel_pures_l. do 2 brel_pures_r. iApply "IH". by iApply "Hk".
        * do 2 brel_pures_l. do 2 brel_pures_r. iApply "IH". by iApply "Hk".

      (* Refl2. *)
      + iDestruct "HND" as "[-> ->]".
        brel_pure_l.
        { apply neutral_ectx; set_solver. }
        do 8 brel_pure_l.
        iLöb as "IH'". brel_pure_l. by iApply "IH'".

      (* Assoc1. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e13 [%e21 [%e22 [%e23 HND]]]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2 & #He3)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b). destruct b.
        * brel_pures_l. brel_pures_l. iApply (brel_rand_r true).
          do 6 brel_pures_r.
          { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
          iApply (brel_rand_r true). do 2 brel_pures_r.
          iApply "IH". by iApply "Hk".
        * do 6 brel_pures_l.
          { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
          iApply brel_rand_l. iIntros (b). destruct b.
          -- do 2 brel_pures_l. iApply (brel_rand_r true).
             do 6 brel_pures_r.
             { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
             iApply (brel_rand_r false).
             do 2 brel_pures_r.
             iApply "IH". by iApply "Hk".
          -- do 2 brel_pures_l. iApply (brel_rand_r false). do 2 brel_pures_r.
             iApply "IH". by iApply "Hk".

      (* Assoc2. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e13 [%e21 [%e22 [%e23 HND]]]]]]".
        iDestruct "HND" as "(-> & -> & #He1 & #He2 & #He3)".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b). destruct b.
        * do 6 brel_pures_l.
          { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
          iApply brel_rand_l. iIntros (b). destruct b.
          -- do 2 brel_pures_l. iApply (brel_rand_r true). do 2 brel_pures_r.
             iApply "IH". by iApply "Hk".
          -- do 2 brel_pures_l. iApply (brel_rand_r false).
             do 6 brel_pures_r.
             { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
             iApply (brel_rand_r true).
             do 2 brel_pures_r.
             iApply "IH". by iApply "Hk".
        * brel_pures_l. brel_pures_l. iApply (brel_rand_r false).
          do 6 brel_pures_r.
          { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
          iApply (brel_rand_r false). do 2 brel_pures_r.
          iApply "IH". by iApply "Hk".

      (* Unit1. *)
      + iDestruct "HND" as "[%e11 [-> #HQ]]".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b). destruct b.
        * brel_pures_l. do 2 brel_pure_l. { by apply neutral_ectx; set_solver. }
          do 8 brel_pure_l.
          iLöb as "IH'". brel_pure_l. by iApply "IH'".
        * do 2 brel_pures_l. by iApply "IH"; iApply "Hk".

      (* Unit2. *)
      + iDestruct "HND" as "[%e11 [-> #HQ]]".
        do 5 brel_pures_l.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b). destruct b.
        * do 2 brel_pures_l. by iApply "IH"; iApply "Hk".
        * brel_pures_l. do 2 brel_pure_l. { by apply neutral_ectx; set_solver. }
          do 8 brel_pure_l.
          iLöb as "IH'". brel_pure_l. by iApply "IH'".

      (* Unit3. *)
      + iDestruct "HND" as "[%e22 (Hlc & -> & #HQ)]".
        iAssert (▷ □ _)%I as "IHHk".
        { iNext. iCombine "IH Hk" as "#IHHk". by iApply "IHHk". }
        iClear "IH Hk".
        iApply fupd_brel.
        iMod (lc_fupd_elim_later ⊤ with "Hlc IHHk") as "[#IH #Hk]". iClear "IHHk".
        iModIntro. do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply (brel_rand_r false). brel_pures_r. brel_pures_r.
        iApply "IH". by iApply "Hk".

      (* Unit4. *)
      + iDestruct "HND" as "[%e22 (Hlc & -> & #HQ)]".
        iAssert (▷ □ _)%I as "IHHk".
        { iNext. iCombine "IH Hk" as "#IHHk". by iApply "IHHk". }
        iClear "IH Hk".
        iApply fupd_brel.
        iMod (lc_fupd_elim_later ⊤ with "Hlc IHHk") as "[#IH #Hk]". iClear "IHHk".
        iModIntro. do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply (brel_rand_r true). brel_pures_r. brel_pures_r.
        iApply "IH". by iApply "Hk".

      (* Comm. *)
      + iDestruct "HND" as "[%e11 [%e12 [%e21 [%e22 (-> & -> & #HQ1 & #HQ2)]]]]".
        do 5 brel_pures_l. 
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        do 5 brel_pures_r.
        { rewrite ectx_labels_app not_elem_of_app; split; [apply neutral_ectx|]; set_solver. }
        iApply brel_rand_l. iIntros (b). destruct b.
        * brel_pures_l. brel_pures_l. iApply (brel_rand_r false). do 2 brel_pures_r.
          iApply "IH". by iApply "Hk".
        * brel_pures_l. brel_pures_l. iApply (brel_rand_r true). do 2 brel_pures_r.
          iApply "IH". by iApply "Hk".
  Qed.

End ndet_run_rand_correctness.


(* ========================================================================= *)
(* Unsound Non-Determinism Relational Theory. *)

(* Unsound version onf [ND] where [Unit3] and [Unit4] do not charge later
   credits. *)

Section unsound_ndet_theory.
  Context `{!blazeGS Σ}.

  Program Definition UnsoundUnit3 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e2' : expr),
    ⌜ e2 = pick ndet (fail' ndet) e2' ⌝ ∗
    □ Q e1 e2'
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition UnsoundUnit4 (ndet : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ (e2' : expr),
    ⌜ e2 = pick ndet e2' (fail' ndet) ⌝ ∗
    □ Q e1 e2'
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition UnsoundND ndet : iThy Σ :=
    iThySum (Refl1         ndet) (
    iThySum (Refl2         ndet) (
    iThySum (Assoc1        ndet) (
    iThySum (Assoc2        ndet) (
    iThySum (Unit1         ndet) (
    iThySum (Unit2         ndet) (
    iThySum (UnsoundUnit3  ndet) (
            (UnsoundUnit4  ndet)
    ))))))).

End unsound_ndet_theory.


(* ========================================================================= *)
(* Terminating Implementation and Diverging Specification. *)

(* Proof that, with [UnsoundND], we can relate any implementation (including
   terminating ones) to a diverging spec. *)

Section diverging_spec.
  Context `{!blazeGS Σ}.

  Variables (ndet : label).

  Notation pick' e1 e2 := (pick ndet e1 e2).
  Notation fail' := (fail' ndet).

  Example ex_absurd (e : expr) L :
    let L' := ([ndet], [ndet], UnsoundND ndet) :: L in
    let f := (rec: "f" <> := pick' ("f" #()) fail')%V in
    ⊢ BREL e ≤ f #() <|L'|> {{same_result}}.
  Proof.
    iIntros (L' f). iLöb as "IH". rewrite /f.
    brel_pure_r.
    set Q : expr → expr → iProp Σ := (λ s1 s2, ⌜ s1 = e ⌝ ∗ ⌜ s2 = f #() ⌝%E)%I.
    iApply (brel_introduction [ndet] [ndet] (UnsoundND ndet) Q).
    { by apply elem_of_cons; left. }
    iExists e, _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by simpl; iIntros "!> %% H"; iApply "H"].
    { iRight. iRight. iRight. iRight. iRight. iRight. iRight.
      iExists (f #()). by iSplit.
    }
    iIntros "!> !> %% [-> ->]". by iApply "IH".
  Qed.

End diverging_spec.
