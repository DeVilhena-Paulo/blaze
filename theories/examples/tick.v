From blaze Require Import logic state_rules proofmode.

Section tick.
  Context `{!blazeGS Σ}.

  Definition both_unit (e1 e2 : expr) : iProp Σ := ⌜e1 = #()⌝ ∗ ⌜e2 = #()⌝.
  Program Definition Tick (tick : label) : iThy Σ := (λ e1 e2, λne Q,
    ⌜ e1 = do: tick #() ⌝%E ∗ ⌜ e2 = #() ⌝ ∗ □ Q #() #())%I.
  Next Obligation. solve_proper. Qed.

  Lemma tick_handler_correct e1 e2 (tick : label) L :
    let f2 := (λ: <>, #())%V in
    let h_e1 :=
      handle: e1 with effect tick <>, rec "k" => "k" #() | return <> => #() end%E in

    BREL e1 ≤ e2 <| (([tick], []), Tick tick) :: L |> {{ both_unit }} -∗
    BREL h_e1 ≤ e2 <| (([tick], []), iThyBot) :: L |> {{ both_unit }}.
  Proof.
    iIntros (??) "Hbrel". rewrite /h_e1. clear h_e1.
    iLöb as "IH" forall (e1 e2).
    iApply (brel_exhaustion with "Hbrel"); first by simpl. { done. }
    iSplit.
    - iIntros "!> %% [-> ->]". by brel_pures_l.
    - iIntros "!> %k1 %k2 % % %Q %Hk1 %Hk2 (-> & -> & #HQ) #Hk".
      iApply brel_handle_os_l.
      { by apply NeutralEctx_ectx_labels_singleton. }
      iIntros "!> %r Hr".
      brel_pures_l.
      iApply (brel_cont_l with "Hr").
      iApply "IH". by iApply "Hk".
  Qed.

  Example ex (ff : val) :
    let e1 :=
      (effect "tick"
      handle: (ff (λ: <>, do: "tick" #())%E) with
      | effect "tick" <>, rec "k" => "k" #()
      | return <> => #()
      end)%E
    in
    let e2 := (ff (λ: <>, #())%V)%E in

    (∀ (f1 f2 : val) L,
       BREL f1 #() ≤ f2 #() <|L|> {{ both_unit }} -∗
       BREL ff f1 ≤ ff f2 <|L|> {{ both_unit }}
    ) -∗
    BREL e1 ≤ e2 <| [] |> {{ both_unit }}.
  Proof.
    iIntros (??) "Hff".
    iApply brel_effect_l.
    iIntros "!>" (tick) "Htick !>". simpl.
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Htick").
    iApply tick_handler_correct.
    brel_pure_l. iApply "Hff". brel_pures_l. brel_pures_r.
    iApply (brel_introduction [tick] []). { by rewrite elem_of_cons; left. }
    { iExists (do: tick #())%E, #().
      iExists [], [], both_unit. simpl.
      iSplit; [done|].
      iSplit; [by iPureIntro; apply _|].
      iSplit; [done|]. iSplit; [by iPureIntro; apply _|]. iSplit; [auto|].
      { iIntros "!> %% HR". by iApply "HR". }
    }
    { iIntros "!> !> % % [-> ->]". by iApply brel_value. }
  Qed.

End tick.
