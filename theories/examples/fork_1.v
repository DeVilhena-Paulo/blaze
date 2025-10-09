(* fork_1.v *)

From blaze Require Import stdpp_ext logic state_rules proofmode queue_lib.


(* ************************************************************************* *)
(* Theory. *)

Section theory.
  Context `{!blazeGS Σ}.

  Variables (fork : label).

  Program Definition COOP_pre : iThy Σ → iThy Σ := λ COOP e1 e2, λne Q, (
    ∃ (task1 : val) (task2 : expr),
    ⌜ e1 = (do: fork task1)%E ⌝ ∗
    ⌜ e2 = (Fork task2)%E ⌝ ∗
    ▷ BREL task1 #() ≤ task2 <| [(([fork], []), COOP)] |> {{ _; _, True }} ∗
    Q #() #()
  )%I.
  Next Obligation. solve_proper. Qed.

  Local Instance COOP_pre_contractive : Contractive COOP_pre.
  Proof.
    rewrite /COOP_pre => n COOP COOP' Hdist e1 e2 Q /=.
    f_equiv=>task1. f_equiv=>task2.
    do 3 f_equiv. f_contractive. do 2 f_equiv.
    - by apply pair_ne.
    - auto.
  Qed.

  Definition COOP_def := fixpoint COOP_pre.
  Definition COOP_aux : seal COOP_def. Proof. by eexists. Qed.
  Definition COOP := COOP_aux.(unseal).

  Definition COOP_eq : COOP = COOP_def := COOP_aux.(seal_eq).
  Global Lemma COOP_unfold e1 e2 Q : COOP e1 e2 Q ⊣⊢ COOP_pre COOP e1 e2 Q.
  Proof. rewrite COOP_eq /COOP_def. apply (fixpoint_unfold COOP_pre e1 e2 Q). Qed.

End theory.


(* ************************************************************************* *)
(* Verification. *)

Section verification.
  Context `{!blazeGS Σ} `{QueueLib Σ}.

  Section handler_refinement.
    Variables (fork : label) (q : val).

    Definition fork_handler_pre (e : expr) (run : expr) : expr :=
      handle: e with
      | effect fork "task", rec "k" as multi =>
          queue_add q (λ: <>, run "task");;
          "k" #()
      | return <> =>
          if: queue_empty q then #() else queue_take q #()
      end%E.

    Definition run : val := (rec: "run" "task" :=
      fork_handler_pre ("task" #()) "run"
    )%V.

    Definition fork_handler (e : expr) : expr :=
      fork_handler_pre e run.

    Definition queue_inv_pre (queue_inv : iProp Σ) : iProp Σ := (∃ (k1s : list val),
      is_queue q k1s ∗
      [∗ list] k1 ∈ k1s,
        ∃ (i : nat) (e2 : expr),
        i ⤇ e2 ∗
        (▷ queue_inv -∗ BREL Val k1 #() ≤ e2 <| [(([fork], []), iThyBot)] |> {{ _; _, True }})
    )%I.

    Local Instance queue_inv_pre_contractive : Contractive queue_inv_pre.
    Proof.
      rewrite /queue_inv_pre => n queue_inv queue_inv' Hdist.
      repeat (f_contractive || f_equiv). by apply Hdist.
    Qed.

    Definition queue_inv_def := fixpoint queue_inv_pre.
    Definition queue_inv_aux : seal queue_inv_def. Proof. by eexists. Qed.
    Definition queue_inv := queue_inv_aux.(unseal).

    Definition queue_inv_eq : queue_inv = queue_inv_def := queue_inv_aux.(seal_eq).
    Global Lemma queue_inv_unfold : queue_inv ≡ queue_inv_pre queue_inv.
    rewrite queue_inv_eq /queue_inv_def. apply (fixpoint_unfold queue_inv_pre). Qed.

    Lemma exploit_queue_inv (k1s l1s : list val) k1 :
      k1s = l1s ++ [k1] →
      ([∗ list] (k1 : val) ∈ k1s,
        ∃ (i : nat) (e2 : expr),
        i ⤇ e2 ∗
        (▷ queue_inv -∗ BREL k1 #() ≤ e2 <| [([fork], [], iThyBot)] |> {{ _; _, True }})
      ) -∗
      is_queue q l1s -∗
      ∃ i (e2 : expr),
      i ⤇ e2 ∗
      BREL k1 #() ≤ e2 <| [([fork], [], iThyBot)] |> {{ _; _, True }}.
    Proof.
      iIntros (Heq) "Hl Hq".
      case_eq (reverse k1s).
      - intros Heq'.
        rewrite (reverse_eq_nil _ Heq') //= in Heq.
        specialize (f_equal reverse Heq) as Habsurd.
        by rewrite reverse_app //= in Habsurd.
      - intros k1' k1s' Heq'.
        specialize (f_equal reverse Heq') as Heq''.
        rewrite reverse_involutive reverse_cons //= in Heq''.
        rewrite Heq'' //= in Heq.
        destruct (app_inj_tail _ _ _ _ Heq) as [Hl' ->].
        rewrite Heq'' big_sepL_app //=.
        iDestruct "Hl" as "(Hl & [%i [%e2 [Hi Hbrel]]] & _)".
        iExists i, e2. iFrame.
        rewrite Hl'.
        iApply "Hbrel".
        rewrite {-1}queue_inv_unfold /queue_inv_pre.
        iExists l1s. by iFrame.
    Qed.

    Lemma run_refines (e1 e2 : expr) :
      queue_inv -∗
      BREL e1 ≤ e2 <| [(([fork], []), COOP fork)] |> {{ _; _, True }} -∗
      BREL fork_handler e1 ≤ e2 <| [(([fork], []),  iThyBot)] |> {{ _; _, True }}.
    Proof.
      rewrite queue_inv_unfold /queue_inv_pre.
      iIntros "[%k1s [Hq Hk1s]] Hbrel".
      iLöb as "IH" forall (k1s e1 e2).
      iApply (brel_exhaustion' OS with "Hbrel"); try done.
      iSplit.
      - iIntros (??) "_". simpl.
        brel_pures_l.
        iApply (queue_empty_spec with "Hq"). iIntros "!> Hq".
        case_eq (reverse k1s).
        + intros Heq. rewrite (reverse_eq_nil _ Heq).
          by brel_pures_l.
        + intros k1 l1s Heq.
          specialize (f_equal reverse Heq) as Heq'.
          rewrite reverse_involutive reverse_cons in Heq'.
          rewrite Heq' length_app //= Nat.add_1_r.
          brel_pures_l.
          iApply (queue_take_spec with "Hq").
          iIntros "!> Hq".
          iDestruct (exploit_queue_inv with "Hk1s Hq") as "H"; first done.
          iDestruct "H" as "[%i [%e2' [Hi Hbrel]]]".
          iApply (brel_logical_fork _ [] with "Hi [Hbrel]").
          { by iApply "Hbrel". }
          iIntros "%% _ _". by iApply brel_value.
      - clear e1 e2.
        iIntros "%k1 %k2 %e1 %e2 %Q %Hk1 %Hk2 HCOOP Hk".
        rewrite COOP_unfold /COOP_pre //=.
        iDestruct "HCOOP" as "[%task1 [%task2 (->& -> & Hbrel & HQ)]]".
        brel_pures_l. { by apply neutral_ectx; set_solver. }
        iSpecialize ("Hk" with "HQ").
        iApply brel_fork_r.
        iIntros "%i Hi".
        iApply (queue_add_spec with "Hq").
        iIntros "!> Hq".
        brel_pures_l.
        iApply ("IH" with "Hq [Hbrel Hk1s Hi] Hk").
        iFrame.
        iIntros "Hq". brel_pures_l.
        rewrite /run. brel_pures_l.
        rewrite {-1}queue_inv_unfold /queue_inv_pre.
        iDestruct "Hq" as "[%k1s' [Hq Hk1s']]".
        by iApply ("IH" with "Hq Hk1s'").
    Qed.

  End handler_refinement.

  Lemma fork_refines (fork : label) (task1 task2 : val) :
    let e1 : expr := (do: fork task1)%E in
    let e2 : expr := (Fork (task2 #()))%E in

    BREL task1 #() ≤ task2 #() <| [([fork], [], COOP fork)] |> {{ _; _, True }} -∗
    BREL e1 ≤ e2 <| [([fork], [], COOP fork)] |> {{ _; _, True }}.
  Proof.
    iIntros (??) "Hbrel". rewrite /e1 /e2. clear e1 e2.
    set Q : expr → expr → iProp Σ := (λ (s1 s2 : expr), ⌜ s1 = #() ⌝ ∗ ⌜ s2 = #() ⌝)%I.
    iApply (brel_introduction _ _ _ Q with "[Hbrel]"); first (by rewrite elem_of_cons; left).
    { iExists (do: fork task1)%E, (Fork (task2 #()))%E, [], [], Q.
      iSplit; [done|]. iSplit; [by iPureIntro; apply _|].
      iSplit; [done|]. iSplit; [by iPureIntro; apply _|].
      iSplit; [|auto].
      rewrite COOP_unfold.
      iExists task1, (task2 #()).
      do 2 (iSplit; [done|]). by iSplit; auto.
    }
    { iIntros "!> !> %% [-> ->]". by iApply brel_value. }
  Qed.

  Theorem fork_handler_spec (main1 main2 : val) :
    let e1 : expr := (
      effect "fork"
      let: "q" := queue_create #() in
      let: "run" := rec: "run" "task" :=
        handle: "task" #() with
        | effect "fork" "task", rec "k" as multi =>
            queue_add "q" (λ: <>, "run" "task");;
            "k" #()
        | return <> =>
            if: queue_empty "q" then #() else queue_take "q" #()
        end
      in
      "run" (λ: <>, main1 (λ: "task", do: "fork" "task"))
    )%E
    in

    let e2 : expr := (
      main2 (λ: "task2", Fork ("task2" #()))
    )%E
    in

    (∀ (fork1 fork2 : val) L,
      □ (∀ (task1 task2 : val),
         BREL task1 #() ≤ task2 #() <| L |> {{ _; _, True }} -∗
         BREL fork1 task1 ≤ fork2 task2 <| L |> {{ _; _, True }}
      ) -∗
      BREL main1 fork1 ≤ main2 fork2 <| L |> {{ _; _, True }}
    ) -∗

    BREL e1 ≤ e2 <| [] |> {{ _; _, True }}.
  Proof.
    iIntros (??) "Hmain". rewrite /e1 /e2. clear e1 e2.
    iApply brel_effect_l.
    iIntros "!> %fork Hfork !>". simpl.

    brel_pures_r.

    iApply queue_create_spec.
    iIntros "!> %q Hq". simpl.

    brel_pures_l.

    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hfork").

    iApply (run_refines fork q (main1 _) (main2 _) with "[Hq]").
    { rewrite queue_inv_unfold. iExists []. by iFrame. }

    iApply "Hmain".
    iIntros "!> %task1 %task2 Htask".

    brel_pures_l.
    brel_pures_r.

    by iApply fork_refines.
  Qed.

End verification.
