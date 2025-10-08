(* exception.v *)

From iris.proofmode Require Import base tactics classes.
From blaze Require Import stdpp_ext logic state_rules proofmode list_lib.


Section implementation.

  Definition list_map : val := rec: "map" "f" "xs" :=
    match: "xs" with
      InjL <> => list_nil
    | InjR "args" =>
        let: "y" := "f" (Fst "args") in
        let: "ys" := "map" "f" (Snd "args") in
        list_cons "y" "ys"
    end.

  Definition list_map_exn (error : label) : val := λ: "f" "xs",
    let: "f_exn" := λ: "x",
      match: "f" "x" with
        InjL <> => do: error #()
      | InjR "y" => "y"
      end
    in
    handle: list_map "f_exn" "xs" with
    | effect error <>, <> as multi => InjL #()
    | return "ys" => InjR "ys"
    end.

  Definition option_bind : val := λ: "o" "f",
    match: "o" with
      InjL <> => InjL #()
    | InjR "x" => "f" "x"
    end.

  Definition list_map_opt : val := rec: "map" "f" "xs" :=
    match: "xs" with
      InjL <> => InjR (list_nil)
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "xs" := Snd "args" in
        option_bind ("f" "x") (λ: "y",
        option_bind ("map" "f" "xs") (λ: "ys",
        InjR (list_cons "y" "ys")))
    end.

End implementation.


Section verification.
  Context `{!blazeGS Σ}.

  Fixpoint option_bind_ectx (fs : list val) : ectx :=
    match fs with [] => [] | f :: fs =>
      AppLCtx f :: AppRCtx option_bind :: option_bind_ectx fs
    end.

  Lemma option_bind_ectx_app fs fs' :
    option_bind_ectx (fs ++ fs') = option_bind_ectx fs ++ option_bind_ectx fs'.
  Proof. by induction fs as [|f fs]; [|rewrite //= IHfs //=]. Qed.

  Lemma ewp_fill_option_bind_ectx_r e1 k fs X R :
    EWP e1 ≤ fill k (InjLV #()) <|X|> {{R}} -∗
    EWP e1 ≤ fill k (fill (option_bind_ectx fs) (InjLV #())) <|X|> {{R}}.
  Proof.
    iInduction fs as [|f fs] "IH" forall (k); iIntros "Hewp"; [done|]; simpl.
    iSpecialize ("IH" $! (k ++ [AppLCtx f; AppRCtx option_bind])).
    rewrite !fill_app //=. iApply "IH".
    rewrite /option_bind. by ewp_pures_r.
  Qed.

  Program Definition Error (error : label) : iThy Σ := (λ e1 e2, λne Q, ∃ k fs,
    ⌜ error ∉ ectx_labels k ⌝ ∗
    ⌜ e1 = fill k (do: error #()) ⌝ ∗
    ⌜ e2 = fill (option_bind_ectx fs) (InjLV #()) ⌝)%I.

  Definition both_opt (v1 v2 : val) : iProp Σ :=
    ⌜ v1 = v2 ⌝ ∗ (⌜ v2 = InjLV #() ⌝ ∨ ∃ v, ⌜v2 = InjRV v⌝).

  Lemma traversable_Error (error : label) (fs : list val) k :
    error ∉ ectx_labels k →
    ⊢ traversable k (option_bind_ectx fs) (Error error).
  Proof.
    intros Hk. iIntros "!> %%% [%k' [%fs' (%Hk' & -> & ->)]]".
    iExists (λ _ _, False)%I; iSplit; [|by iIntros "!> %% Habsurd"].
    iExists (k ++ k'), (fs ++ fs'). iSplit; [|iSplit]; iPureIntro.
    { by rewrite ectx_labels_app; set_solver. }
    { by rewrite fill_app. }
    { by rewrite option_bind_ectx_app fill_app. }
  Qed.

  Lemma list_map_refines_opt (f1 f2 : val) (xs : list val) (error : label) X :
    (∀ k1 k2, ectx_labels k1 ⊆ [error] → ectx_labels k2 ⊆ [] → ⊢ traversable k1 k2 X) →
    let f1_exn := (λ: "x",
      match: f1 "x" with
        InjL <> => do: error #()
      | InjR "y" => "y"
      end)%V
    in
    (□ ∀ x, EWP f1 x ≤ f2 x <|X|> {{both_opt}}) -∗
    EWP list_map f1_exn (list_to_val xs) ≤
        list_map_opt f2 (list_to_val xs)
        <|iThySum (Error error) X|> {{v1; v2,
      ∃ (ys : list val), ⌜ v1 = list_to_val ys ⌝ ∗ ⌜ v2 = InjRV (list_to_val ys) ⌝
    }}.
  Proof.
    iIntros (HX ?) "#Hf".
    iInduction xs as [|x xs] "IH";
    rewrite /list_map /list_map_opt.
    - ewp_pures_l. ewp_pures_r. by iExists [].
    - rewrite /option_bind /f1_exn.
      ewp_pures_l. ewp_pures_r.
      iApply (ewp_bind [AppRCtx _; CaseCtx _ _] [AppLCtx _; AppRCtx _] _ _ X).
      { by iApply HX; set_solver. }
      { by iApply iThy_le_sum_r_2. }
      iApply (ewp_wand with "Hf"). iIntros "!>" (v1 v2) "[-> [->|[%y ->]]]".
      + simpl. ewp_pures_l. ewp_pures_r.
        iApply ewp_introduction'. iLeft. iExists [AppRCtx _], [].
        iSplit; [iPureIntro; set_solver|]. by iSplit.
      + simpl.
        do 6 ewp_pure_l. do 7 ewp_pure_r.
        iApply (ewp_bind' [AppRCtx _] [AppLCtx _; AppRCtx _]).
        { iApply traversable_sum.
          * by iApply (traversable_Error error [_]); set_solver.
          * by iApply HX; set_solver.
        }
        simpl.
        iApply (ewp_wand with "IH").
        iIntros "!> %% [% [-> ->]]". ewp_pures_l. ewp_pures_r.
        by iExists (y :: ys).
  Qed.

  Lemma list_map_exn_refines_opt (f1 f2 : val) (xs : list val) (error : label) X :
    (∀ k1 k2, ectx_labels k1 ⊆ [error] → ectx_labels k2 ⊆ [] → ⊢ traversable k1 k2 X) →
    (□ ∀ x, EWP f1 x ≤ f2 x <|X|> {{both_opt}}) -∗
    EWP list_map_exn error f1 (list_to_val xs) ≤
        list_map_opt f2 (list_to_val xs) <|X|>
        {{v1; v2, ⌜ v1 = v2 ⌝ ∗ 
           (⌜ v2 = InjLV #() ⌝ ∨ ∃ (ys : list val), ⌜ v2 = InjRV (list_to_val ys) ⌝)
        }}.
  Proof.
    iIntros (HX) "#Hf".
    rewrite /list_map_exn /list_map_opt //=.
    ewp_pures_l.
    iApply ewp_introduction_mono; last iApply iThy_le_sum_bot_r.
    iApply (ewp_exhaustion_sum_l [HandleCtx _ _ _ _ _] [] _ _ _ (Error error)).
    { by iApply HX; set_solver. }
    { iApply ewp_introduction_mono; last iApply iThy_le_sum_swap.
      by iApply list_map_refines_opt. }
    { iIntros "!>"; iSplit.
      - iIntros (??) "[%ys [-> ->]]". ewp_pures_l. iPureIntro.
        split; [done|]. right. by exists ys.
      - iIntros (???) "[%k [%fs (%Hk & -> & ->)]] _". simpl.
        ewp_pures_l.
        iApply ewp_fill_option_bind_ectx_r.
        by iApply ewp_value; auto.
    }
  Qed.

End verification.
