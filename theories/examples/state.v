From blaze Require Import logic state_rules proofmode.

Section state.
  Context `{!blazeGS Σ}.

  Section state_theory_and_handler_refinement.
    Variables (ask tell cell : label).

    Program Definition STATE : iThy Σ := λ e1 e2, λne Q, (
      (⌜ e1 = (do: ask #())%E ⌝ ∗
       ⌜ e2 = (do: cell (InjLV #()))%E ⌝ ∗
       □ ∀ (w : val), Q w w)
        ∨
      (∃ (s : val),
       ⌜ e1 = (do: tell s)%E ⌝ ∗
       ⌜ e2 = (do: cell (InjRV s))%E ⌝ ∗
       □ Q #() #()
      )
    )%I.
    Next Obligation. solve_proper. Qed.

    Lemma state_handler_refines e1 e2 (init : val) :
      let ResEq := (λ (v1 v2 : val), ⌜ v1 = v2 ⌝)%I in

      let h_e1 := (
        handle: (
          handle: e1 with
          | effect tell "s", rec "k" as multi =>
              (handle: "k" #() with
              | effect ask <>, rec "k" as multi => "k" "s"
              | return "y" => "y"
              end)
          | return "y" => "y"
          end
        ) with
        | effect ask <>, rec "k" as multi => "k" init
        | return "y" => "y"
        end
      )%E
      in

      let h_e2 := (
        handle: e2 with
        | effect cell "args", rec "k" as multi =>
            (match: "args" with
              InjL <>  => λ: "s", "k" "s" "s"
            | InjR "s" => λ: <>, "k" #() "s"
            end)
        | return "y" => λ: <>, "y"
        end
      )%E
      in

      BREL e1 ≤ e2 <|[(([ask; tell], [cell]), STATE)]|> {{ ResEq }} -∗

      BREL h_e1 ≤ h_e2 init <|[(([ask; tell], [cell]), iThyBot)]|> {{ ResEq }}.
    Proof.
      iIntros (???) "Hbrel". rewrite /h_e1 /h_e2. clear h_e1 h_e2.
      iLöb as "IH" forall (e1 e2 init).
      iApply (brel_exhaustion e1 e2 with "Hbrel"); [by simpl| by simpl|].
      iSplit.
      - iIntros "!> %% ->".
        brel_pures_l. by brel_pures_r.
      - iIntros "!> %% %% % %Hneutral_k1 %Hneutral_k2".
        iIntros "[(-> & -> & #HQ)|[%s (-> & -> & #HQ)]] #Hbrel /=".
        + iSpecialize ("Hbrel" $! init init with "[]"). { by iApply "HQ". }
          brel_pures_r. { by apply neutral_ectx; set_solver. }
          iApply brel_learn. iIntros "[%Hdistinct _] _".
          rewrite /distinct_l /labels_l //= in Hdistinct.
          brel_pures_l.
          { simpl. rewrite not_elem_of_cons. split.
            - specialize (NoDup_cons_1_1 _ _ Hdistinct). by set_solver.
            - apply neutral_ectx; set_solver.
          }
          iApply "IH". by iApply "Hbrel".
        + iSpecialize ("Hbrel" $! #() #() with "[]"). { by iApply "HQ". }
          brel_pures_r. { by apply neutral_ectx; set_solver. }
          brel_pures_l. { by apply neutral_ectx; set_solver. }
          iApply (brel_exhaustion _ _ [_] with "[Hbrel]").
          { set_solver. } { set_solver. }
          { by iApply "IH". }
          iSplit; [|by iIntros "!> %%%%%%% ?"].
          iIntros "!> %% ->". by brel_pures_l.
    Qed.

  End state_theory_and_handler_refinement.

  Example ex (ff init : val) :
    let e1 := (
      effect "tell"
      effect "ask"
      let: "get" := λ: <>, do: "ask" #() in
      let: "set" := λ: "s", do: "tell" "s" in
      handle: (
        handle: (ff "get" "set") with
        | effect "tell" "s", rec "k" as multi =>
            (handle: "k" #() with
            | effect "ask" <>, rec "k" as multi => "k" "s"
            | return "y" => "y"
            end)
        | return "y" => "y"
        end
      )
      with
      | effect "ask" <>, rec "k" as multi => "k" init
      | return "y" => "y"
      end
    )%E
    in

    let e2 := (
      effect "cell"
      let: "get" := λ: <>, do: "cell" (InjL #()) in
      let: "set" := λ: "s", do: "cell" (InjR "s") in
      (handle: (ff "get" "set") with
      | effect "cell" "args", rec "k" as multi =>
          match: "args" with
            InjL <>  => λ: "s", "k" "s" "s"
          | InjR "s" => λ: <>, "k" #() "s"
          end
      | return "y" => λ: <>, "y"
      end) init
    )%E
    in

    let ResEq := (λ (v1 v2 : val), ⌜ v1 = v2 ⌝ : iProp Σ)%I in
    let ResUnit := (λ (v1 v2 : val), ⌜ v1 = #() ⌝ ∗ ⌜ v2 = #() ⌝)%I in

    (∀ (get1 get2 set1 set2 : val) L,
      (□ BREL get1 #() ≤ get2 #() <|L|> {{ ResEq }}) -∗
      (□ ∀ (s : val), BREL set1 s ≤ set2 s <|L|> {{ ResUnit }}) -∗
      BREL ff get1 set1 ≤ ff get2 set2 <|L|> {{ ResEq }}
    ) -∗

    BREL e1 ≤ e2 <|[]|> {{ ResEq }}.
  Proof.
    iIntros (????) "Hff". rewrite /e1 /e2. clear e1 e2.
    iApply brel_effect_l.
    iIntros "!>" (tell) "Htell !>". simpl.
    iApply brel_effect_l.
    iIntros "!>" (ask) "Hask !>". simpl.
    iApply brel_effect_r.
    iIntros (cell) "Hcell !>". simpl.
    brel_pures_l.
    brel_pures_r.
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Htell").
    iApply (brel_add_label_l with "Hask").
    iApply (brel_add_label_r with "Hcell").
    iApply brel_learn. iIntros "[%Hdistinct_l _] _".
    iApply state_handler_refines.
    iApply "Hff"; iModIntro.
    { brel_pures_l. brel_pures_r.
      set R : _ → _ → iProp Σ :=
        (λ (e1 e2 : expr), ∃ (v : val), ⌜ e1 = Val v ⌝ ∗ ⌜ e2 = Val v ⌝)%I.
      iApply (brel_introduction [ask; tell] [cell] _ R).
      { by rewrite elem_of_cons; left. }
      { iExists (do: ask #())%E, (do: cell (InjLV #()))%E.
        iExists [], [], (λ e1 e2, R e1 e2). simpl.
        iSplit; [done|].
        iSplit; [by iPureIntro; apply _|].
        iSplit; [done|]. iSplit; [by iPureIntro; apply _|]. iSplit.
        { iLeft. repeat (iSplit; [done|]). iIntros "!> %". by iExists w. }
        { iIntros "!> %% HR". by iApply "HR". }
      }
      { iIntros "!> !> %% [% [-> ->]]". by iApply brel_value. }
    }
    { iIntros (s).
      brel_pures_l. brel_pures_r.
      set R : _ → _ → iProp Σ :=
        (λ (e1 e2 : expr), ⌜ e1 = #() ⌝ ∗ ⌜ e2 = #() ⌝)%I.
      iApply (brel_introduction [ask; tell] [cell] _ R).
      { by rewrite elem_of_cons; left. }
      { iExists (do: tell s)%E, (do: cell (InjRV s))%E.
        iExists [], [], (λ e1 e2, R e1 e2). simpl.
        iSplit; [done|].
        iSplit; [by iPureIntro; apply _|].
        iSplit; [done|]. iSplit; [by iPureIntro; apply _|]. iSplit.
        { iRight. iExists s. auto. }
        { iIntros "!> %% HR". by iApply "HR". }
      }
      { iIntros "!> !> %% [-> ->]". by iApply brel_value. }
    }
  Qed.

End state.
