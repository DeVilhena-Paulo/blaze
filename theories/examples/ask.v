(* ask.v *)

From iris.proofmode Require Import base tactics classes.
From blaze Require Import stdpp_ext logic state_rules proofmode list_lib spec_rules.


(* ========================================================================= *)
(* Implementation. *)

Section implementation.

  Definition run_ask_handler (ask : eff_val) (e : expr) (x : expr) : expr :=
    handle: e with
    | effect ask <>, rec "k" as multi => "k" x
    | return "z" => "z"
    end.

  Definition run_ask : val := λ: "x" "main",
    effect "ask"
    run_ask_handler "ask" ("main" (λ: <>, do: "ask" #())) "x".

End implementation.


Section verification.
  Context `{!blazeGS Σ}.

  Definition both_int (x : Z) (v1 v2 : val) : iProp Σ :=
    ⌜ v1 = #x ⌝ ∗ ⌜ v2 = #x ⌝.

  Program Definition AskT (ask : label) (x : Z) : iThy Σ :=
    λ e1 e2, λne Q,
      (⌜ e1 = do: ask #() ⌝%E ∗ ⌜ e2 = #x ⌝ ∗ □ Q #x #x)%I.
  Next Obligation. solve_proper. Qed.

  Lemma run_ask_handler_refines (ask : label) (x : Z) L R e1 e2 :
    BEWP e1 ≤ e2 <|([ask], [], AskT ask x) :: L|> {{R}} -∗
    BEWP run_ask_handler ask e1 #x ≤ e2 <|([ask], [], iThyBot) :: L|> {{R}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    iIntros "He". rewrite /run_ask_handler.
    iApply (bewp_exhaustion _ _ [_] with "He"); try done.
    iSplit; [by iIntros "!> %% HR"; by bewp_pures_l|].
    iIntros "!> %k1 %k2 %%% %Hk1 %Hk2 (-> & -> & #HQ) #Hk".
    bewp_pures_l. { by apply Hk1; apply elem_of_list_singleton. }
    iApply "IH". by iApply "Hk".
  Qed.

  Lemma run_ask_refines (main1 main2 : val) (x : Z) L R :
    (∀ (ask1 ask2 : val) M,
      □ BEWP ask1 #() ≤ ask2 #() <|M|> {{both_int x}} -∗
      BEWP main1 ask1 ≤ main2 ask2 <|M ++ L|> {{R}}
    ) -∗
    BEWP run_ask #x main1 ≤ main2 (λ: <>, #x) <|L|> {{R}}.
  Proof.
    iIntros "Hmain".
    rewrite /run_ask. bewp_pures_l. bewp_pures_r.
    iApply bewp_new_theory.
    iApply bewp_effect_l. iIntros "!> %ask Hask !>".
    iApply (bewp_add_label_l with "Hask"). bewp_pures_l.
    iApply run_ask_handler_refines.
    iApply ("Hmain" $! _ _ [([ask], [], AskT ask x)]).
    iIntros "!>". bewp_pures_l. bewp_pures_r.
    iApply bewp_introduction'. { apply elem_of_cons. by left. }
    iExists (do: ask #())%E, #x, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by iIntros "!> %% H"; iApply "H"].
    do 2 (iSplit; [done|]). by iModIntro; iApply bewp_value.
  Qed.

End verification.
