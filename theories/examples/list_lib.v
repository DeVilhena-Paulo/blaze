(* list_lib.v *)

From blaze Require Import logic proofmode.

Section lists_implementation.

  Definition list_nilV : val := InjLV #().
  Definition list_consV (x xs : val) : val := InjRV (x, xs).

  Definition list_nil : expr:= InjL #().
  Definition list_cons (x xs : expr) : expr := InjR (x, xs).

  Definition list_singletonV (x : val) : val := InjRV (x, InjLV #()).
  Definition list_singleton (x : expr) : expr := InjR (x, InjL #()).

  Definition list_iter : val := (rec: "iter" "f" "xs" :=
    match: "xs" with
      InjL <> => #()
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "xs" := Snd "args" in
        "f" "x";;
        "iter" "f" "xs"
    end
  )%V.

  Definition list_concat : val := (rec: "concat" "xs" "ys" :=
    match: "xs" with
      InjL <> => "ys"
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "xs" := Snd "args" in
        list_cons "x" ("concat" "xs" "ys")
    end
  )%V.

  Definition list_to_val : list val → val :=
    fix list_to_val xs :=
      match xs with
      | [] =>
          list_nilV
      | x :: xs =>
          list_consV x (list_to_val xs)
      end.

End lists_implementation.


Section lists_reasoning_rules.
  Context `{!blazeGS Σ}.

  Lemma brel_list_iter_cons (f1 x1 x1s f2 x2 x2s : val) L R :
    BREL f1 x1 ≤ f2 x2 <|L|> {{ _; _,
      BREL list_iter f1 x1s ≤ list_iter f2 x2s <|L|> {{R}}
    }} -∗
    BREL list_iter f1 (list_consV x1 x1s) ≤
         list_iter f2 (list_consV x2 x2s) <|L|> {{R}}.
  Proof.
    iIntros "Hf".
    rewrite !{3}/list_iter.
    brel_pures_l.
    brel_pures_r.
    iApply (brel_bind' [_] [_]).
    { by iApply (traversable_to_iThy L); intros ?; apply _. }
    iApply (brel_wand with "Hf").
    iIntros "!>" (??) "Hiter".
    do 2 brel_pure_l.
    do 2 brel_pure_r.
    by iApply "Hiter".
  Qed.

  Lemma brel_list_iter'
    (I : list (val * val) → list (val * val) → iProp Σ)
    (f1 f2 : val) L :
    (□ ∀ x12s_l x1 x2 x12s_r,
       I (x12s_l) ((x1, x2) :: x12s_r) -∗
       BREL f1 x1 ≤ f2 x2 <|L|> {{ _; _, I (x12s_l ++ [(x1, x2)]) x12s_r }}
    ) -∗
    ∀ x12s_l x12s_r,
    I x12s_l x12s_r -∗
    BREL list_iter f1 (list_to_val x12s_r.*1) ≤
         list_iter f2 (list_to_val x12s_r.*2) <|L|> {{ _; _, I (x12s_l ++ x12s_r) [] }}.
  Proof.
    iIntros "#Hf12" (x12s_l x12s_r) "HI".
    iInduction x12s_r as [|(x1, x2) x12s_r] "IH" forall (x12s_l).
    - rewrite /list_iter app_nil_r. brel_pures_l. brel_pures_r. by iFrame.
    - iApply brel_list_iter_cons.
      iSpecialize ("Hf12" with "HI").
      iApply (brel_wand with "Hf12").
      iIntros "!> _ _ HI". iSpecialize ("IH" with "HI").
      by rewrite -app_assoc //=.
  Qed.

  Lemma brel_list_iter
    (I : list (val * val) → list (val * val) → iProp Σ)
    (f1 f2 : val) x12s L :
    (□ ∀ x12s_l x1 x2 x12s_r,
       I (x12s_l) ((x1, x2) :: x12s_r) -∗
       BREL f1 x1 ≤ f2 x2 <|L|> {{ _; _, I (x12s_l ++ [(x1, x2)]) x12s_r }}
    ) -∗
    I [] x12s -∗
    BREL list_iter f1 (list_to_val x12s.*1) ≤
         list_iter f2 (list_to_val x12s.*2) <|L|> {{ _; _, I x12s [] }}.
  Proof. by iIntros "Hf12 HI"; iApply (brel_list_iter' with "Hf12 HI"). Qed.

  Lemma brel_list_concat_l k (xs ys : list val) e2 L R :
    ▷ BREL fill k (list_to_val (xs ++ ys)) ≤ e2 <|L|> {{R}} -∗
    BREL fill k (list_concat (list_to_val xs) (list_to_val ys)) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbrel".
    iInduction xs as [|x xs] "IH" forall (k ys).
    - rewrite /list_concat //=. by brel_pures_l.
    - rewrite {-1}/list_concat //=. do 12 brel_pure_l.
      rewrite -(fill_app k [InjRCtx; PairRCtx x]).
      iApply "IH". iModIntro.
      rewrite !fill_app //=. by brel_pures_l.
  Qed.

  Lemma brel_list_concat_r k (xs ys : list val) e1 L R :
    BREL e1 ≤ fill k (list_to_val (xs ++ ys)) <|L|> {{R}} -∗
    BREL e1 ≤ fill k (list_concat (list_to_val xs) (list_to_val ys)) <|L|> {{R}}.
  Proof.
    iIntros "Hbrel".
    iInduction xs as [|x xs] "IH" forall (k ys).
    - rewrite /list_concat //=. by brel_pures_r.
    - rewrite {-1}/list_concat //=. do 12 brel_pure_r.
      rewrite -(fill_app k [InjRCtx; PairRCtx x]).
      iApply "IH".
      rewrite !fill_app //=. by brel_pures_r.
  Qed.

End lists_reasoning_rules.
