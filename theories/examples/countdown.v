(* countdown.v *)

From iris.proofmode Require Import base tactics classes.
From blaze Require Import stdpp_ext logic state_rules proofmode list_lib spec_rules.


(* ========================================================================= *)
(* Implementation. *)

Section implementation.

  Definition while (get : expr) (set : expr) : expr :=
    (rec: "while" <> :=
       if: get #() < #0 then #() else
         set (get #() - #1);; "while" #()
    ) #().

  Definition countdown : val := λ: "get" "set",
    "set" #10%Z;; while "get" "set".

  Definition get (timer : label) : val := λ: <>,
    do: timer (InjL #()).

  Definition set (timer : label) : val := λ: "y",
    do: timer (InjR "y").

  Definition run_st_passing_handler (timer : eff_val) (e : expr) (init : expr) : expr :=
    handle: e with
    | effect timer "request", rec "k" as multi => λ: "x",
        match: "request" with
          InjL <>  => "k" "x" "x"
        | InjR "y" => "k" #() "y"
        end
    | return "y" => λ: <>, "y"
    end init.

  Definition run_st_passing (timer : eff_val) : val := λ: "init" "main",
    run_st_passing_handler timer ("main" #()) "init".

  Definition run_heap_handler (timer : eff_val) (e : expr) (l : expr) : expr :=
    handle: e with
    | effect timer "request", rec "k" as multi =>
        match: "request" with
          InjL <>  =>  "k" (! l)%E
        | InjR "y" => l <- "y";; "k" #()
        end
    | return "y" => "y"
    end.

  Definition run_heap (timer : eff_val) : val := λ: "init" "main",
    let: "r" := ref "init" in
    run_heap_handler timer ("main" #()) "r".

  Definition run_spec : val := λ: "init" "main",
    let: "r" := ref "init" in
    let: "get" := λ: <>, !"r" in
    let: "set" := λ: "y", "r" <- "y" in
    "main" "get" "set".

End implementation.


(* ************************************************************************* *)
(* Refinements from Section 2.2. *)

Section section_2_2.

(* ========================================================================= *)
(* Handlee. *)

Section handlee_verification.
  Context `{!blazeGS Σ}.
  Context (timer1 timer2 : label).

  Program Definition ReadRefl : iThy Σ := λ e1 e2, (λne Q,
    ⌜ e1 = do: timer1 (InjLV #()) ⌝%E ∗
    ⌜ e2 = do: timer2 (InjLV #()) ⌝%E ∗
    □ (∀ (x : Z), Q #x #x)
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition WriteRefl : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x : Z),
    ⌜ e1 = do: timer1 (InjRV #x) ⌝%E ∗
    ⌜ e2 = do: timer2 (InjRV #x) ⌝%E ∗
    □ Q #() #()
  )%I.
  Next Obligation. solve_proper. Qed.

  Definition TimerRefl : iThy Σ := iThySum ReadRefl WriteRefl.

  Lemma get_refines :
    ⊢ EWP get timer1 #() ≤
          get timer2 #()
          <|iThyTraverse [timer1] [timer2] TimerRefl|>
          {{v1; v2, ∃ (x : Z), ⌜ v1 = #x ⌝ ∗ ⌜ v2 = #x ⌝}}.
  Proof.
    rewrite /get. ewp_pures_l. ewp_pures_r.
    iApply ewp_introduction'.
    iExists _, _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iLeft. do 2 (iSplit; [done|]).
    iIntros "!> %x". iApply ewp_value. by iExists x.
  Qed.

  Lemma set_refines (x : Z) :
    ⊢ EWP set timer1 #x ≤
          set timer2 #x
          <|iThyTraverse [timer1] [timer2] TimerRefl|>
          {{v1; v2, ⌜ v1 = #() ⌝ ∗ ⌜ v2 = #() ⌝}}.
  Proof.
    rewrite /set. ewp_pures_l. ewp_pures_r.
    iApply ewp_introduction'.
    iExists _, _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iRight. iExists x. do 2 (iSplit; [done|]).
    iModIntro. by iApply ewp_value.
  Qed.

  Lemma while_refines :
    ⊢ EWP while (get timer1) (set timer1) ≤
          while (get timer2) (set timer2)
          <|iThyTraverse [timer1] [timer2] TimerRefl|>
          {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    rewrite /while.
    ewp_pure_l. ewp_pure_r.
    iLöb as "IH".
    ewp_pures_l. ewp_pures_r.
    iApply (ewp_bind' [_; BinOpLCtx _ _] [_; BinOpLCtx _ _]).
    { by iApply traversable_iThyTraverse; apply _. }
    iApply ewp_wand. { by iApply get_refines. }
    iIntros "!> %% [%x [-> ->]]".
    ewp_pures_l. ewp_pures_r.
    case_eq (decide (x < 0)%Z).
    - intros Hneg Hdec. rewrite bool_decide_eq_true_2; [|done].
      ewp_pures_l. ewp_pures_r. by auto.
    - intros Hnneg Hdec. rewrite bool_decide_eq_false_2; [|done].
      ewp_pures_l. ewp_pures_r.
      iApply (ewp_bind' [_; _; BinOpLCtx _ _] [_; _; BinOpLCtx _ _]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply ewp_wand. { by iApply get_refines. }
      iIntros "!> %% [%x' [-> ->]]".
      ewp_pures_l. ewp_pures_r.
      iApply (ewp_bind' [_] [_]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply ewp_wand. { by iApply set_refines. }
      iIntros "!> %% [-> ->]".
      do 2 ewp_pure_l. do 2 ewp_pure_r.
      by iApply "IH".
  Qed.

  Lemma countdown_refines :
    ⊢ EWP countdown (get timer1) (set timer1) ≤
          countdown (get timer2) (set timer2)
          <|iThyTraverse [timer1] [timer2] TimerRefl|>
          {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    rewrite /countdown. ewp_pures_l. ewp_pures_r.
    iApply (ewp_bind' [AppRCtx _] [AppRCtx _]).
    { by iApply traversable_iThyTraverse; apply _. }
    iApply ewp_wand. { by iApply set_refines. }
    iIntros "!> %% [-> ->]". simpl. do 2 ewp_pure_l. do 2 ewp_pure_r.
    by iApply while_refines.
  Qed.

End handlee_verification.

(* ========================================================================= *)
(* Handler. *)

Section handler_verification.
  Context `{!blazeGS Σ}.

  Lemma run_st_passing_handler_refines_run_heap_handler
    (timer1 timer2 : label) (e1 e2 : expr) (l2 : loc) (init : Z) :
    let Timer := iThyTraverse [timer1] [timer2] (TimerRefl timer1 timer2) in
    EWP e1 ≤ e2 <|Timer|> {{v1; v2, ⌜ v1 = v2 ⌝}} -∗
    l2 ↦ₛ  #init -∗
    EWP run_st_passing_handler timer1 e1 #init ≤
        run_heap_handler timer2 e2 #l2
        <|iThyBot|>
        {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    iIntros (L) "He Hl2".
    iLöb as "IH" forall (e1 e2 init).
    rewrite /run_st_passing_handler /run_heap_handler /L.
    iApply (ewp_exhaustion [_; _] [_] with "He").
    iSplit; [by iIntros (??) "->"; ewp_pures_l; ewp_pures_r|].
    clear e1 e2.
    iIntros (e1 e2 ?)
      "[%e1' [%e2' [%k1 [%k2 [%S
        (-> & %Hk1 & -> & %Hk2 & [HRead|HWrite] & #HQ)
       ]]]]] #Hk".
    - iDestruct "HRead" as "(-> & -> & #HS)".
      ewp_pures_l. { apply Hk1. set_solver. }
      ewp_pures_r. { apply Hk2. set_solver. }
      iApply (ewp_load_r with "Hl2"). iIntros "Hl2".
      ewp_pures_r.
      iApply ("IH" with "[Hk] Hl2").
      iApply "Hk". by iApply "HQ".
    - iDestruct "HWrite" as "[%y (-> & -> & #HS)]".
      ewp_pures_l. { apply Hk1. set_solver. }
      ewp_pures_r. { apply Hk2. set_solver. }
      iApply (ewp_store_r with "Hl2"). iIntros "Hl2".
      ewp_pures_r.
      iApply ("IH" with "[Hk] Hl2").
      iApply "Hk". by iApply "HQ".
  Qed.


  Lemma run_st_passing_refines_run_heap
    (timer1 timer2 : label) (main1 main2 : val) (init : Z) :
    let Timer := iThyTraverse [timer1] [timer2] (TimerRefl timer1 timer2) in
    EWP main1 #() ≤ main2 #() <|Timer|> {{v1; v2, ⌜ v1 = v2 ⌝}} -∗
    EWP run_st_passing timer1 #init main1 ≤
        run_heap timer2 #init main2
        <|iThyBot|>
       {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    iIntros (Timer) "Hmain". rewrite /run_st_passing /run_heap.
    ewp_pures_l. ewp_pures_r.
    iApply ewp_alloc_r. iIntros (l2) "Hl2". ewp_pures_r.
    by iApply (run_st_passing_handler_refines_run_heap_handler with "Hmain Hl2").
  Qed.

End handler_verification.

End section_2_2.

(* ************************************************************************* *)



(* ************************************************************************* *)
(* Refinements from Section 2.3. *)

Section section_2_3.

(* ========================================================================= *)
(* Handlee. *)

Section handlee_verification.
  Context `{!blazeGS Σ} `{!frac_cell Σ}.
  Context (timer : label).

  Program Definition Read (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x : Z),
    l ↦ₛ {# 1/2} #x ∗
    ⌜ e1 = do: timer (InjLV #()) ⌝%E ∗
    ⌜ e2 = ! #l ⌝%E ∗
    □ (l ↦ₛ {# 1/2} #x -∗ Q #x #x)
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Write (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x y : Z),
    l ↦ₛ {# 1/2} #x ∗
    ⌜ e1 = do: timer (InjRV #y) ⌝%E ∗
    ⌜ e2 = (#l <- #y)%E ⌝ ∗
    □ (l ↦ₛ {# 1/2} #y -∗ Q #() #())
  )%I.
  Next Obligation. solve_proper. Qed.

  Definition Timer l : iThy Σ := iThySum (Read l) (Write l).

  Lemma while_refines2 (l : loc) (x : Z) :
    l ↦ₛ {# 1/2} #x -∗
    EWP while (get timer) (set timer) ≤
        while (λ: <>, ! #l)%V (λ: "y", #l <- "y")%V
        <|iThyTraverse [timer] [] (Timer l)|>
        {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    rewrite /while /get /set.
    iIntros "Hl". 
    ewp_pure_l. ewp_pure_r.
    iLöb as "IH" forall (x).
    ewp_pures_l. ewp_pures_r.
    iApply (ewp_bind' [_; BinOpLCtx _ _] [_; BinOpLCtx _ _]).
    { by iApply traversable_iThyTraverse; apply _. }
    iApply ewp_introduction'.
    iExists _, _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iLeft. iFrame. do 2 (iSplit; [done|]).
    iIntros "!> Hl". iApply ewp_value.
    ewp_pures_l. ewp_pures_r.
    case_eq (decide (x < 0)%Z).
    - intros Hneg Hdec. rewrite bool_decide_eq_true_2; [|done].
      ewp_pures_l. ewp_pures_r. by auto.
    - intros Hnneg Hdec. rewrite bool_decide_eq_false_2; [|done].
      ewp_pures_l. ewp_pures_r.
      iApply (ewp_bind' [_; _; BinOpLCtx _ _] [_; _; BinOpLCtx _ _]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply ewp_introduction'.
      iExists _, _, [], [], _.
      do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
      iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
      iLeft. iFrame. do 2 (iSplit; [done|]).
      iIntros "!> Hl". iApply ewp_value.
      ewp_pures_l. ewp_pures_r.
      iApply (ewp_bind' [_] [_]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply ewp_introduction'.
      iExists _, _, [], [], _.
      do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
      iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
      iRight. iFrame. iExists (x - 1)%Z. do 2 (iSplit; [done|]).
      iIntros "!> Hl". iApply ewp_value.
      do 2 ewp_pure_l. do 2 ewp_pure_r.
      by iApply ("IH" with "Hl").
  Qed.

  Lemma countdown_refines2 (l : loc) (x : Z) :
    l ↦ₛ {# 1 / 2} #x -∗
    EWP countdown (get timer) (set timer) ≤
        countdown (λ: <>, ! #l)%V (λ: "y", #l <- "y")%V
        <|iThyTraverse [timer] [] (Timer l)|>
        {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    iIntros "Hl". rewrite /countdown /get /set.
    ewp_pures_l. ewp_pures_r.
    iApply ewp_introduction'.
    iExists (do: timer (InjRV #10%Z))%E, (#l <- #10%Z)%E.
    iExists [AppRCtx _], [AppRCtx _], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]); simpl.
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iRight. iExists x, 10%Z. iFrame.
    do 2 (iSplit; [done|]).
    iIntros "!> Hl".
    do 2 ewp_pure_l.
    do 2 ewp_pure_r.
    iApply (while_refines2 with "Hl").
  Qed.

End handlee_verification.


(* ========================================================================= *)
(* ========================================================================= *)
(* Handler. *)

Section handler_verification.
  Context `{!blazeGS Σ}.
  Context (timer : label).

  Definition same_result (l : loc) (x : Z) (v1 v2 : val) : iProp Σ :=
    ⌜ v1 = #x ⌝ ∗ ⌜ v2 = #x ⌝ ∗ l ↦ₛ {# 1/2} #x.
  Definition both_unit (l : loc) (y : Z) (v1 v2 : val) : iProp Σ :=
    ⌜ v1 = #() ⌝ ∗ ⌜ v2 = #() ⌝ ∗ l ↦ₛ {# 1/2} #y.

  Lemma run_st_passing_handler_refines (l : loc) (e1 e2 : expr) (init : Z) :
    l ↦ₛ {# 1/2} #init -∗
    EWP e1 ≤ e2 <|iThyTraverse [timer] [] (Timer timer l)|> {{ v1 ; v2, ⌜ v1 = v2 ⌝ }} -∗
    EWP run_st_passing_handler timer e1 #init ≤ e2
        <|iThyBot|>
        {{ v1 ; v2, ⌜ v1 = v2 ⌝ }}.
  Proof.
    iIntros "Hl He".
    iLöb as "IH" forall (e1 e2 init).
    rewrite /run_st_passing_handler.
    iApply (ewp_exhaustion [_; _] [] with "He").
    iSplit; [by iIntros (??) "->"; ewp_pures_l|].
    clear e1 e2. iIntros (e1 e2 ?)
      "[%e1' [%e2' [%k1 [%k2 [%S
        (-> & %Hk1 & -> & %Hk2 & [HRead|HWrite] & #HQ)
       ]]]]] #Hk".
    - iDestruct "HRead" as "[%x [Hl'  (-> & -> & #HS)]]".
      iDestruct (pointstoS_agree with "Hl Hl'") as "->".
      ewp_pures_l. { apply Hk1. set_solver. }
      iApply (ewp_load_r with "Hl"). iIntros "Hl".
      iApply ("IH" with "Hl").
      iApply "Hk". iApply "HQ". by iApply ("HS" with "Hl'").
    - iDestruct "HWrite" as "[%x [%y [Hl' (-> & -> & #HS)]]]".
      iDestruct (pointstoS_combine with "Hl Hl'") as "[Hl ->]".
      rewrite dfrac_op_own Qp.half_half.
      iApply (ewp_store_r with "Hl"). iIntros "Hl".
      iEval (rewrite -Qp.half_half) in "Hl".
      iDestruct (pointstoS_split with "Hl") as "[Hl Hl']".
      ewp_pures_l. { apply Hk1. set_solver. }
      iApply ("IH" with "Hl").
      iApply "Hk". iApply "HQ". by iApply ("HS" with "Hl'").
  Qed.

  Lemma run_st_passing_refines l (main1 : val) (main2 : expr) (init : Z) :
    l ↦ₛ {# 1/2} #init -∗
    EWP main1 #() ≤ main2 <|iThyTraverse [timer] [] (Timer timer l)|> {{v1; v2, ⌜ v1 = v2 ⌝}} -∗
    EWP run_st_passing timer #init main1 ≤ main2 <|iThyBot|> {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    iIntros "Hl Hmain". rewrite /run_st_passing. ewp_pures_l.
    by iApply (run_st_passing_handler_refines with "Hl Hmain").
  Qed.

  Lemma run_st_passing_refines_run_spec (init : Z) :
    let e1 := run_st_passing timer #init (λ: <>, countdown (get timer) (set timer))%V in
    let e2 := run_spec #init countdown in
    ⊢ EWP e1 ≤ e2 <|iThyBot|> {{v1; v2, ⌜ v1 = v2 ⌝}}.
  Proof.
    iIntros (e1 e2). rewrite /e1 /e2 /run_st_passing /run_spec.
    ewp_pures_l. ewp_pures_r. iApply ewp_alloc_r. iIntros (l) "Hl". ewp_pures_r.
    iEval (rewrite -Qp.half_half) in "Hl".
    iDestruct (pointstoS_split with "Hl") as "[Hl Hl']".
    iApply (run_st_passing_handler_refines with "Hl'").
    by iApply (countdown_refines2 with "Hl").
  Qed.

End handler_verification.

End section_2_3.

(* ************************************************************************* *)
