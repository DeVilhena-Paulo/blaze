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

    Definition inv_run_type :=
      (list (val * nat * ectx) * list (val * nat * ectx)) -d> iPropO Σ.

    Definition ready_type :=
      expr -d> expr -d> iPropO Σ.

    Program Definition queue_inv_pre : ready_type -n> inv_run_type := (λne ready, λ l,
      (* Queue ownership: *)
      is_queue s l.1.*1.*1 ∗
      (* Reduced spec. threads: *)
      ([∗ list] args ∈ l.2,
         let j := args.1.2 in
         let k := args.2 in
         ∃ (v : val), j ⤇ fill k v
      ) ∗
      (* Running impl. fibers: *)
      ([∗ list] args ∈ l.1,
         let k1 := args.1.1 in
         let j := args.1.2 in
         let k := args.2 in
         ∃ (e2 : expr), j ⤇ fill k e2 ∗
         ready ((Val k1) #()) e2
      )
    )%I.
    Next Obligation.
      repeat intros ?; repeat (f_equiv || simpl). by apply (H0 _ _).
    Qed.

    Definition postInv : inv_run_type := (λ l,
      is_queue s [] ∗
      [∗ list] args ∈ l.1 ++ l.2,
      let j := args.1.2 in
      let k := args.2 in
      ∃ (v : val), j ⤇ fill k v
    )%I.

    Definition ready_pre : ready_type → ready_type :=
    (λ ready e1 e2,
      ∀ l,
      ▷ queue_inv_pre ready l -∗
      BREL e1 ≤ e2 <|[([fork], [], iThyBot)]|> {{ _; _, postInv l }}
    )%I.

    Local Instance ready_pre_contractive : Contractive ready_pre.
    Proof.
      rewrite /ready_pre => n ready ready' Hdist e1 e2 //=.
      repeat (f_contractive || f_equiv). by apply (Hdist _ _).
    Qed.

    Definition ready_def := fixpoint ready_pre.
    Definition ready_aux : seal ready_def.
    Proof. by eexists. Qed.

    (* Definition of [ready]. *)
    Definition ready := ready_aux.(unseal).

    Definition ready_eq : ready = ready_def := ready_aux.(seal_eq).
    Global Lemma ready_unfold e1 e2 :
      ready e1 e2 ≡ ready_pre ready e1 e2.
    Proof.
      rewrite ready_eq /ready_def.
      apply (fixpoint_unfold ready_pre e1 e2).
    Qed.

    Definition queue_inv := queue_inv_pre ready.

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

    Lemma run_refines (e1 e2 : expr) l :
      BREL e1 ≤ e2 <|[(([fork], [], COOP fork))]|> {{ _; _, True }} -∗
      queue_inv l -∗
      BREL fork_handler e1 ≤ e2 <|[(([fork], [], iThyBot))]|> {{ _; _, postInv l }}.
    Proof.
      iIntros "Hbrel".
      iLöb as "IH" forall (e1 e2 l).
      iIntros "HpreInv".
      iApply (brel_exhaustion' OS with "Hbrel"); try done. iSplit.
      - iIntros (??) "_".
        brel_pures_l.
        rewrite /queue_inv.
        iDestruct "HpreInv" as "[Hqueue [Hl2 Hl1]]".
        iApply (queue_empty_spec with "Hqueue").
        iIntros "!>  Hqueue".
        case_eq (reverse l.1); [|intros ((k1, j), k) l1s]; intros Heq.
        + specialize (reverse_eq_nil _ Heq) as Heq'.
          rewrite Heq' //=. simpl.
          brel_pures_l. iModIntro. iFrame. by rewrite Heq' //=.
        + specialize (f_equal reverse Heq) as Heq'.
          rewrite reverse_involutive reverse_cons in Heq'.
          rewrite Heq' length_fmap length_fmap length_app Nat.add_1_r.
          rewrite fmap_app fmap_app //=.
          brel_pures_l.
          iApply (queue_take_spec with "Hqueue").
          iIntros "!> Hqueue".
          rewrite big_sepL_app //=.
          iDestruct "Hl1" as "[Hl1 [[%e' [Hj Hk1]] _]]".
          rewrite ready_unfold /ready_pre.
          iSpecialize ("Hk1" $! (reverse l1s, l.2) with "[$]").
          iApply (brel_logical_fork with "Hj [Hk1]").
          { by iApply "Hk1". }
          iIntros (??) "[Hqueue Hl'] Hj". iApply brel_value.
          iFrame. simpl. rewrite Heq'.
          rewrite !big_sepL_app //=.
          iDestruct "Hl'" as "[Hl1 Hl2]". by iFrame.
      - clear e1 e2.
        iIntros "%k1 %k2 %e1 %e2 %Q %Hk1 %Hk2 HCOOP Hk".
        rewrite COOP_unfold /COOP_pre //=.
        iDestruct "HCOOP" as "[%task1 [%task2 (->& -> & Hbrel & HQ)]]".
        brel_pures_l. { by apply neutral_ectx; set_solver. }
        iSpecialize ("Hk" with "HQ").
        rewrite /queue_inv.
        iDestruct "HpreInv" as "[Hqueue Hl]".
        iApply (queue_add_spec with "Hqueue").
        iIntros "!> Hqueue". brel_pures_l.
        iApply brel_fork_r.
        iIntros (i) "Hi".
        iApply (brel_thread_swap _ _ _ [] with "Hi").
        iIntros (j k) "Hj". simpl.
        unfold run.
        brel_pures_l.
        iApply (brel_wand' _ _ _ (λ _ _, postInv ((_, j, k) :: l.1, l.2))%I).
        { iIntros "!> _ _ [Hs Hl]". simpl.
          iDestruct "Hl" as "[[%v Hj] Hl]".
          iExists v. by iFrame.
        }
        iApply ("IH" with "Hbrel").
        rewrite /queue_inv.
        simpl. iFrame. iDestruct "Hl" as "[??]". iFrame.
        rewrite ready_unfold /ready_pre.
        iIntros (l') "Hqueue_inv".
        brel_pures_l.
        by iApply ("IH" with "Hk Hqueue_inv").
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

    iApply (brel_wand' _ _ _ (λ _ _, postInv s ([], []))%I); first auto.
    iApply (run_refines with "[Hmain]"); last by iFrame; auto.

    iApply "Hmain".
    iIntros "!> %task1 %task2 Htask".

    brel_pures_l.
    brel_pures_r.

    by iApply fork_refines.
  Qed.

End verification.
