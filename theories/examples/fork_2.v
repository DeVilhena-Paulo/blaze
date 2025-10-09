(* fork_2.v *)

From stdpp Require Import list.
From blaze Require Import stdpp_ext logic state_rules
                          proofmode fork_1 queue_lib.


(* ************************************************************************* *)
(* Verification. *)

Section verification.
  Context `{!blazeGS Σ} `{QueueLib Σ}.

  Section handler_refinement.
    Variables (fork : label) (s : val).

    Definition fork_handler_pre (e : expr) (run : expr) : expr :=
      handle: e with
      | effect fork "task", rec "k" as multi =>
          queue_add s "k";;
          run "task"
      | return <> =>
         if: queue_empty s then #() else
           queue_take s #()
      end%E.

    Definition run : val := (rec: "run" "task" :=
      fork_handler_pre ("task" #()) "run"
    )%V.

    Definition fork_handler (e : expr) : expr :=
      handle: e with
      | effect fork "task", rec "k" as multi =>
          queue_add s "k";;
          run "task"
      | return <> =>
         if: queue_empty s then #() else
           queue_take s #()
      end%E.

    Definition inv_type := list (option val * nat * ectx) -d> iProp Σ.

    Definition postInv : inv_type := (λ l,
      is_queue s [] ∗
      [∗ list] '(_, j, k) ∈ l, ∃ (v : val), j ⤇ fill k v
    )%I.

    Definition preInv_pre : inv_type → inv_type := (λ preInv l,
      let k1s : list val := omap id l.*1.*1 in
      is_queue s k1s ∗
      [∗ list] '(k1_opt, j, k) ∈ l,
        match k1_opt with
        | None =>
            ∃ (v : val), j ⤇ fill k v
        | Some k1 =>
            ∃ (e2 : expr),
            j ⤇ fill k e2 ∗
            ∀ l,
            ▷ preInv l -∗
            BREL Val k1 #() ≤ e2 <|[([fork], [], iThyBot)]|> {{ _; _, postInv l }}
        end
    )%I.

    Local Instance preInv_pre_contractive : Contractive preInv_pre.
    Proof.
      rewrite /preInv_pre => n preInv preInv' Hdist l //=.
      repeat (f_contractive || f_equiv). by apply (Hdist a1).
    Qed.

    Definition preInv_def := fixpoint preInv_pre.
    Definition preInv_aux : seal preInv_def. Proof. by eexists. Qed.
    Definition preInv := preInv_aux.(unseal).

    Definition preInv_eq : preInv = preInv_def := preInv_aux.(seal_eq).
    Global Lemma preInv_unfold l : preInv l ≡ preInv_pre preInv l.
    Proof. rewrite preInv_eq /preInv_def. apply (fixpoint_unfold preInv_pre l). Qed.

    Lemma find_kont_pos (l : list (option val * nat * ectx)) k1 k1s :
      omap id l.*1.*1 = k1s ++ [k1] →
      ∃ (p q : list (option val * nat * ectx)) j k,
      l = p ++ (Some k1, j, k) :: q ∧
      omap id p.*1.*1 = k1s ∧
      omap id q.*1.*1 = [].
    Proof.
      intros Heq.
      have Helem: k1 ∈ omap id l.*1.*1. { rewrite Heq. by set_solver. }
      rewrite elem_of_list_omap in Helem.
      destruct Helem as [k1' [Helem Hk1']].
      simpl in Hk1'. rewrite Hk1' in Helem. clear Hk1' k1'.
      destruct (elem_of_list_split_r _ _ Helem) as [p' [q' [Happ Hnot_in]]].

      have Homap_q': omap id q' = [].
      { clear Helem. rewrite Happ in Heq. clear Happ.
        revert Hnot_in Heq.
        apply (rev_ind (λ q, _ ∉ q → _ (_ ++ _ :: q) = _ → _ q = _)); first done.
        intros k1_opt' q IH Hnot_in Heq.
        case_eq k1_opt'.
        - intros k1' ->. simpl in *.
          rewrite cons_as_app !omap_app //= in Heq.
          rewrite cons_as_app !app_assoc in Heq.
          destruct (app_inj_tail _ _ _ _ Heq) as [_ ->].
          by set_solver.
        - intros ->. rewrite omap_app app_nil_r //=.
          apply IH; first set_solver.
          rewrite cons_as_app !omap_app app_nil_r //= in Heq.
          by rewrite cons_as_app omap_app.
      }

      have Hlkp: l.*1.*1 !! (length p') = Some (Some k1).
      { rewrite Happ lookup_app_r; last lia.
        by rewrite Nat.sub_diag //=.
      }

      assert (∃ j k, l !! (length p') = Some (Some k1, j, k)) as [j [k Hlkp_l]].
      { rewrite !list_lookup_fmap in Hlkp.
        case_eq (l !! (length p')).
        - intros ((opt, j), k) Hlkp_l.
          rewrite Hlkp_l //= in Hlkp.
          injection Hlkp as ->.
          by exists j, k.
        - intros Hlkp_l.
          by rewrite Hlkp_l //= in Hlkp.
      }

      destruct (elem_of_list_split_length _ _ _ Hlkp_l) as [p [q [Hl Hlen]]].
      exists p, q, j, k. split; [done|].

      have Hq': q.*1.*1 = q'.
      { rewrite Hl !fmap_app !fmap_cons //= in Happ.
        have Hlen': length p.*1.*1 = length p'.
        { by rewrite Hlen !length_fmap. }
        destruct (app_inj_1 _ _ _ _ Hlen' Happ) as [_ Heq'].
        by injection Heq' as ->.
      }

      split; [|by rewrite Hq'].
      rewrite Hl !fmap_app !fmap_cons omap_app Hq' in Heq.
      rewrite cons_as_app omap_app Homap_q' app_nil_r //= in Heq.
      by destruct (app_inj_tail _ _ _ _ Heq) as [-> _].
    Qed.

    Lemma exploit_preInv l k1 k1s :
      omap id l.*1.*1 = k1s ++ [k1] →
      ([∗ list] pat ∈ l,
        match pat with
        | (None, j, k) =>
            ∃ (v : val), j ⤇ fill k v
        | (Some k1, j, k) =>
            ∃ (e2 : expr),
            j ⤇ fill k e2 ∗
            ∀ l,
            ▷ preInv l -∗
            BREL Val k1 #() ≤ e2 <|[([fork], [], iThyBot)]|> {{ _; _, postInv l }}
        end
      ) -∗
      is_queue s k1s -∗
      ∃ l' j k (e2 : expr),
      j ⤇ fill k e2 ∗
      BREL Val k1 #() ≤ e2 <|[([fork], [], iThyBot)]|> {{ _; _, postInv l' }} ∗
      □ (∀ (v : val), postInv l' -∗ j ⤇ fill k v -∗ postInv l).
    Proof.
      iIntros (Heq) "Hl Hs".
      destruct (find_kont_pos _ _ _ Heq) as
        [p [q [j [k (-> & Hp & Hq)]]]].
      rewrite big_sepL_app //=.
      iDestruct "Hl" as "(Hp & [%e2 [Hj Hk1]] & Hq)".
      iExists (p ++ q), j, k, e2. iFrame.
      iSplitL.
      { iApply "Hk1". iNext.
        rewrite preInv_unfold /preInv_pre //=.
        rewrite !fmap_app !omap_app Hp Hq big_sepL_app app_nil_r //=.
        by iFrame.
      }
      { iIntros "!> %v [Hs Hpq] Hj". iFrame.
        rewrite big_sepL_app. by iFrame.
      }
    Qed.

    Lemma establish_postInv l :
      omap id l.*1.*1 = [] →
      ([∗ list] pat ∈ l,
        match pat with
        | (None, j, k) =>
            ∃ (v : val), j ⤇ fill k v
        | (Some k1, j, k) =>
            ∃ (e2 : expr),
            j ⤇ fill k e2 ∗
            ∀ l,
            ▷ preInv l -∗
            BREL Val k1 #() ≤ e2 <|[([fork], [], iThyBot)]|> {{ _; _, postInv l }}
        end
      ) -∗
      is_queue s [] -∗
      postInv l.
    Proof.
      iIntros (?) "Hl Hs". iFrame.
      iInduction l as [|((k1_opt, j), k) l] "IH"; [done|].
      destruct k1_opt =>//. simpl. iFrame.
      iDestruct "Hl" as "[$ Hl]".
      iApply ("IH" with "[] Hl").
      by simpl in *.
    Qed.

    Lemma run_refines (e1 e2 : expr) l :
      BREL e1 ≤ e2 <|[(([fork], [], COOP fork))]|> {{ _; _, True }} -∗
      preInv l -∗
      BREL fork_handler e1 ≤ e2 <|[(([fork], [], iThyBot))]|> {{ _; _, postInv l }}.
    Proof.
      iIntros "Hbrel".
      iLöb as "IH" forall (e1 e2 l).
      iIntros "HpreInv".
      iApply (brel_exhaustion' OS with "Hbrel"); try done. iSplit.
      - iIntros (??) "_".
        brel_pures_l.
        rewrite preInv_unfold.
        iDestruct "HpreInv" as "[Hqueue Hl]".
        iApply (queue_empty_spec with "Hqueue").
        iIntros "!>  Hqueue".
        case_eq (reverse (omap id l.*1.*1)); [|intros k1 k1s]; intros Heq.
        + specialize (reverse_eq_nil _ Heq) as Heq'.
          rewrite Heq'.
          brel_pures_l.
          by iApply (establish_postInv with "Hl Hqueue").
        + specialize (f_equal reverse Heq) as Heq'.
          rewrite reverse_involutive reverse_cons in Heq'.
          rewrite Heq' length_app Nat.add_1_r //=.
          brel_pures_l.
          iApply (queue_take_spec with "Hqueue").
          iIntros "!> Hqueue".
          iDestruct (exploit_preInv with "Hl Hqueue") as "H"; first done.
          iDestruct "H" as "[%l' [%j [%k [%e2' (Hj & Hk1 & #Hpost)]]]]".
          iApply (brel_logical_fork with "Hj [Hk1]").
          { simpl. by iApply "Hk1". }
          iIntros (??) "Hl' Hj". iApply brel_value.
          by iApply ("Hpost" with "Hl' Hj").
      - clear e1 e2.
        iIntros "%k1 %k2 %e1 %e2 %Q %Hk1 %Hk2 HCOOP Hk".
        rewrite COOP_unfold /COOP_pre //=.
        iDestruct "HCOOP" as "[%task1 [%task2 (->& -> & Hbrel & HQ)]]".
        brel_pures_l. { by apply neutral_ectx; set_solver. }
        iSpecialize ("Hk" with "HQ").
        rewrite preInv_unfold.
        iDestruct "HpreInv" as "[Hqueue Hl]".
        iApply (queue_add_spec with "Hqueue").
        iIntros "!> Hqueue". brel_pures_l.
        iApply brel_fork_r.
        iIntros (i) "Hi".
        iApply (brel_thread_swap _ _ _ [] with "Hi").
        iIntros (j k) "Hj". simpl.
        unfold run.
        brel_pures_l.
        iApply (brel_wand' _ _ _ (λ _ _, postInv ((Some _, j, k) :: l))%I).
        { iIntros "!> _ _ [Hs Hl]". simpl.
          iDestruct "Hl" as "[[%v Hj] Hl]".
          iExists v. by iFrame.
        }
        iApply ("IH" with "Hbrel").
        rewrite preInv_unfold /preInv_pre.
        simpl. iFrame.
        clear l. iIntros (l) "HpreInv".
        brel_pures_l.
        by iApply ("IH" with "Hk HpreInv").
    Qed.

  End handler_refinement.

  Theorem fork_handler_spec (main1 main2 : val) :
    let e1 : expr := (
      effect "fork"
      let: "s" := queue_create #() in
      let: "run" := rec: "run" "task" :=
        handle: "task" #() with
        | effect "fork" "task", rec "k" as multi =>
            queue_add "s" "k";;
            "run" "task"
        | return <> =>
            if: queue_empty "s" then #() else
              queue_take "s" #()
        end
      in
      "run" (λ: <>, main1 (λ: "task", do: "fork" "task"))
    )%E
    in

    let e2 : expr := (
      main2 (λ: "task2", Fork ("task2" #()))
    )%E
    in

    (∀ (fork1 fork2 : val) (L : iLblThy Σ),
      □ (∀ (task1 task2 : val),
         BREL task1 #() ≤ task2 #() <|L|> {{ _; _, True }} -∗
         BREL fork1 task1 ≤ fork2 task2 <|L|> {{ _; _, True }}
      ) -∗
      BREL main1 fork1 ≤ main2 fork2 <|L|> {{ _; _, True }}
    ) -∗

    BREL e1 ≤ e2 <|[]|> {{ _; _, True }}.
  Proof.
    iIntros (??) "Hmain". rewrite /e1 /e2. clear e1 e2.
    iApply brel_effect_l.
    iIntros "!> %fork Hfork !>". simpl.

    brel_pures_r.

    iApply queue_create_spec.
    iIntros "!> %s Hs". simpl.

    brel_pures_l.

    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hfork").

    iApply (brel_wand' _ _ _ (λ _ _, postInv s [])%I); first auto.
    iApply (run_refines with "[Hmain]"); last
    by rewrite preInv_unfold /preInv_pre; auto.

    iApply "Hmain".
    iIntros "!> %task1 %task2 Htask".

    brel_pures_l.
    brel_pures_r.

    by iApply fork_refines.
  Qed.

End verification.
