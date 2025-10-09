(* async_await.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic Require Import weakestpre lifting.

From blaze Require Import stdpp_ext logic state_rules proofmode
                          queue_lib list_lib lock_lib lifting.


(* ========================================================================= *)
(* Implementation & Specification. *)

Notation Done y := (InjL y) (only parsing).
Notation Waiting ks := (InjR ks) (only parsing).

Notation DoneV y := (InjLV y) (only parsing).
Notation WaitingV ks := (InjRV ks) (only parsing).

Section implementation_and_specification.
  Context `{!blazeGS Σ} `{QueueLib Σ}.

  (* Template for taking a thread from a (non-empty) queue. *)
  Definition next_tmpl (q : expr) : expr :=
    if: queue_empty q then #() else queue_take q #().

  (* Async/await handler template. (Implementation side.) *)
  Definition coop_handler_tmpl (coop : label) (q : val) (p e run : expr) : expr :=
    handle: e with
    | effect coop "request", rec "k" as multi =>
        match: "request" with
          (* Async: *) InjL "task'" =>
            let: "p'" := ref (Waiting list_nil) in
            queue_add q (λ: <>, "k" "p'");;
            run "p'" "task'"
        | (* Await: *) InjR "p'" =>
            match: !"p'" with
              (* Done: *) InjL "v" =>
                "k" "v"
            | (* Waiting: *) InjR "ks" =>
                "p'" <- Waiting (list_cons "k" "ks");;
                next_tmpl q
            end
        end
    | return "y" =>
        match: !p with
          (* Done: *) InjL <> => #() #() (* absurd *)
        | (* Waiting: *) InjR "ks" =>
            list_iter (λ: "k", queue_add q (λ: <>, "k" "y")) "ks"
        end;;
        p <- Done "y";;
        next_tmpl q
    end%E.

  Definition coop_run (coop : label) (q : val) : val := (rec: "run" "p" "task" :=
    coop_handler_tmpl coop q "p" ("task" #()) "run"
  )%V.

  Definition coop_handler (coop : label) (q : val) (p e : expr) : expr :=
    coop_handler_tmpl coop q p e (coop_run coop q).

  (* Await handler template. (Specification side.) *)
  Definition await_handler_tmpl (await : eff_val) (p e : expr) : expr :=
    handle: e with
    | effect await "p'", rec "k" as multi =>
        acquire (Fst "p'");;
        match: !(Snd "p'") with
          (* Done: *) InjL "v" =>
            release (Fst "p'");;
            "k" "v"
        | (* Waiting: *) InjR "ks" =>
            (Snd "p'") <- Waiting (list_cons "k" "ks");;
            release (Fst "p'")
        end
    | return "y" =>
        acquire (Fst p);;
        match: !(Snd p) with
          (* Done: *) InjL <> => #() #() (* absurd *)
        | (* Waiting: *) InjR "ks" =>
            (Snd p) <- Done "y";;
            release (Fst p);;
            list_iter (λ: "k", Fork ("k" "y")) "ks"
        end
    end%E.

  (* Async & await. *)
  Definition async_implV (coop_lbl : label) : val :=
    (λ: "e", do: coop_lbl (InjL "e"))%V.
  Definition await_implV (coop_lbl : label) : val :=
    (λ: "p", do: coop_lbl (InjR "p"))%V.

  Definition async_specV (await_lbl : label) : val := (λ: "e",
    let: "p" := (new_lock #(), ref (Waiting list_nil)) in
    Fork (await_handler_tmpl await_lbl "p" ("e" #()));;
    "p"
  )%V.
  Definition await_specV (await_lbl : label) : val :=
    (λ: "p", do: await_lbl "p")%V.

End implementation_and_specification.


(* ========================================================================== *)
(** Ghost theory. *)

(* -------------------------------------------------------------------------- *)
(* Cameras. *)

Class promiseGpreS Σ := {
  promise_mapG :: inG Σ
    (authR (gmapUR ((loc * (loc * loc)) * gname)
                   (agreeR (laterO (val -d> val -d> iPropO Σ)))
           )
    );
  tokenG :: inG Σ (exclR unitO);
}.

Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF ((loc * (loc * loc)) * gname)
             (agreeRF (laterOF (valO -d> valO -d> idOF))))
    );
  GFunctor (exclR unitO)
].

Instance subG_promiseΣ {Σ} : subG promiseΣ Σ → promiseGpreS Σ.
Proof. solve_inG. Qed.

Class promiseGS Σ := {
  promise_inG :: promiseGpreS Σ;
  promise_map : gname;
}.


(* -------------------------------------------------------------------------- *)
(* Predicates. *)

Section predicates.
  Context `{!blazeGS Σ, !promiseGS Σ}.
  Context `{!QueueLib Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* token τ ≜ own τ (Excl ())

     isPromise pi ps τ Φ ≜
       ∃ γ, own promise_name (◯ {[((pi, ps), τ) := Φ]})

     isPromiseMap M ≜
       own promise_name (● M)

     promiseInv q ≜
       ∃ M, promiseMap M ∗
       [∗ map] {((pi, ps), τ) ↦ Φ} ∈ M,
           (∃ y1 y2,
            □ Φ y1 y2 ∗ token τ ∗
            pi ↦_i Done y1 ∗
            ps.1 ↦_s 0 ∗
            ps.2 ↦_s Done y2)
         ∨
           (∃ k12s,
            pi ↦_i Waiting k12s.*1 ∗
            ps.1 ↦_s 0 ∗
            ps.2 ↦_s Waiting k12s.*2 ∗
            [∗ list] (k1, k2) ∈ ks, waiting q Φ k1 k2)

     waiting q Φ k ≜
       ∀ y1 y2 l.
       □ Φ y1 y2 -∗
       ▷ promiseInv q -∗
       queue_inv q l -∗
       (k1 y1) ≼ (k2 y2) <[(([coop], [await]), iThyBot)]> (λ _ _,
         queue_inv q ([], l.1 ++ l2.)
       )

    queue_inv q l ≜
      let k1s = l.1.*1 in
      is_queue s k1s ∗
      ([∗ list] '(_ , j, k) ∈ l.2, ∃ (v : val), j ⤇ fill k v) ∗
      ([∗ list] '(k1, j, k) ∈ l.1,
         ∃ (e2 : expr),
         j ⤇ fill k e2 ∗
         ∀ l,
         ▷ promiseInv q -∗
         ▷ pre_run q l -∗
         (k1 #()) ≼ e2 <[(([coop], [await]), iThyBot)]> (λ _ _,
           queue_inv q ([], l.1 ++ l.2)
         )
      )

  *)

  (* Unique token [τ]. *)
  Definition token τ := own τ (Excl tt).

  (* Inject a relation [R] into the camera [Ag(Next(val -d> val -d> iProp))]. *)
  Definition promise_unfold (Φ : val → val → iProp Σ) :
    agree (later (val -d> val -d> iPropO Σ)) :=
    to_agree (Next (λ y1 y2, (Φ y1 y2))).

  Definition isMember pi ps τ Φ :=
    own promise_map (◯ {[((pi, ps), τ) := promise_unfold Φ]}).

  Definition isPromise pi ps Φ := (
    ∃ τ, isMember pi ps τ Φ
  )%I.

  Definition isPromiseMap (M : gmap _ (val → val → iProp Σ)) :=
    own promise_map (● (promise_unfold <$> M : gmap _ _)).

  (* Types definitions. *)
  Definition promiseInv_type := val -d> iPropO Σ.
  Definition inv_run_type :=
    val -d> (list (val * nat * ectx) * list (val * nat * ectx)) -d> iPropO Σ.
  Definition ready_type :=
    val -d> expr -d> expr -d> iPropO Σ.
  Definition waiting_type :=
    val -d> (val -d> val -d> iPropO Σ) -d> val -d> val -d> iPropO Σ.

  (* [waiting]'s pre-fixpoint. *)
  Program Definition waiting_pre : ready_type -n> waiting_type :=
  (λne ready, λ q Φ k1 k2,
    ∀ y1 y2, □ Φ y1 y2 -∗ ready q (k1 y1) (k2 y2)
  )%I.
  Next Obligation.
    repeat intros ?. repeat f_equiv. by apply (H x0).
  Qed.

  (* [queue_inv]'s pre-fixpoint. *)
  Program Definition queue_inv_pre : ready_type -n> inv_run_type :=
  (λne ready, λ q l,
    (* Queue ownership: *)
    is_queue q l.1.*1.*1 ∗
    (* Reduced spec. threads: *)
    (* FIXME: for some reason, using "Program Definition"
         doesn't work with the syntax ['(_, j, k) ∈ l.2]. *)
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
       ready q ((Val k1) #()) e2
    )
  )%I.
  Next Obligation.
    repeat intros ?; repeat (f_equiv || simpl). by apply (H x0).
  Qed.

  (* [promiseInv]'s pre-fixpoint. *)
  Program Definition promiseInv_pre : ready_type -n> promiseInv_type :=
  (λne ready, λ q,
    (* Map ownership: *)
    ∃ M, isPromiseMap M ∗
    (* Descripton of the map's contents: *)
    [∗ map] args ↦ Φ ∈ M,
      let pi := args.1.1 in let ps := args.1.2 in let τ := args.2 in
        ((* Fulfilled: *) ∃ (y1 y2 : val),
           □ Φ y1 y2 ∗ token τ ∗ pi ↦  DoneV y1 ∗
           ps.1 ↦ₛ #0 ∗ ps.2 ↦ₛ DoneV y2
        )
      ∨
        ((* Unfulfilled: *) ∃ k12s,
           pi ↦  WaitingV (list_to_val k12s.*1) ∗
           ps.1 ↦ₛ #0 ∗ ps.2 ↦ₛ WaitingV (list_to_val k12s.*2) ∗
           [∗ list] args ∈ k12s,
           let k1 := args.1 in let k2 := args.2 in
           waiting_pre ready q Φ k1 k2)
  )%I.
  Next Obligation.
    simpl. repeat intros ?; repeat f_equiv. by apply (H x0).
  Qed.

  (* [ready]'s pre-fixpoint. *)
  Definition ready_pre (coop await : label) : ready_type → ready_type :=
  (λ ready q e1 e2,
    ∀ l,
    ▷ promiseInv_pre ready q -∗
    ▷ queue_inv_pre ready q l -∗
    BREL e1 ≤ e2 <| [(([coop], [await]), iThyBot)] |> {{ _; _,
      queue_inv_pre ready q ([], l.1 ++ l.2)
    }}
  )%I.

  Local Instance ready_pre_contractive coop await :
    Contractive (ready_pre coop await).
  Proof.
    rewrite /ready_pre => n ready ready' Hdist q e1 e2 //=.
    repeat (f_contractive || f_equiv).
    - by apply (Hdist q).
    - by apply (Hdist q).
  Qed.

  Definition ready_def coop await :=
    fixpoint (ready_pre coop await).
  Definition ready_aux coop await :
    seal (ready_def coop await).
  Proof. by eexists. Qed.

  (* Definition of [ready]. *)
  Definition ready coop await :=
    (ready_aux coop await).(unseal).

  Definition ready_eq coop await : ready coop await = ready_def coop await :=
    (ready_aux coop await).(seal_eq).
  Global Lemma ready_unfold c a q e1 e2 :
    ready c a q e1 e2 ≡ ready_pre c a (ready c a) q e1 e2.
  Proof.
    rewrite ready_eq /ready_def.
    apply (fixpoint_unfold (ready_pre c a) q e1 e2).
  Qed.

  (* Definition of [waiting]. *)
  Definition waiting coop await := waiting_pre (ready coop await).

  (* Definition of [queue_inv]. *)
  Definition queue_inv coop await := queue_inv_pre (ready coop await).

  (* Definition of [promiseInv]. *)
  Definition promiseInv coop await := promiseInv_pre (ready coop await).

  (* Definition of [promiseSt]. *)
  Program Definition promiseSt coop await q pi ps τ :
    (val -d> val -d> iPropO Σ) -n> iPropO Σ
  :=
  (λne Φ,
    ((* Fulfilled: *) ∃ (y1 y2 : val),
       □ Φ y1 y2 ∗ token τ ∗ pi ↦  DoneV y1 ∗
       ps.1 ↦ₛ #0 ∗ ps.2 ↦ₛ DoneV y2
    )
  ∨
    ((* Unfulfilled: *) ∃ k12s,
       pi ↦  WaitingV (list_to_val k12s.*1) ∗
       ps.1 ↦ₛ #0 ∗ ps.2 ↦ₛ WaitingV (list_to_val k12s.*2) ∗
       [∗ list] args ∈ k12s,
       let k1 := args.1 in let k2 := args.2 in
       waiting coop await q Φ k1 k2)
  )%I.
  Next Obligation. by rewrite /waiting //=; solve_proper. Qed.

  Lemma promiseInv_alt coop await q :
    promiseInv coop await q ⊣⊢
    ∃ M, isPromiseMap M ∗
    [∗ map] args ↦ Φ ∈ M,
      let pi := args.1.1 in let ps := args.1.2 in let τ := args.2 in
      promiseSt coop await q pi ps τ Φ.
  Proof. by rewrite /promiseInv /promiseInv_pre //=. Qed.

  (* ------------------------------------------------------------------------ *)
  (* Non-expansiveness. *)

  (* [ready]. *)
  Global Instance ready_ne coop await n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (ready coop await).
  Proof. by solve_proper. Qed.
  Global Instance ready_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) ready.
  Proof. by solve_proper. Qed.

  (* [waiting]. *)
  Global Instance waiting_ne coop await n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
      (waiting coop await).
  Proof. by solve_proper. Qed.
  Global Instance waiting_proper coop await :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (waiting coop await).
  Proof. by solve_proper. Qed.

  (* [promiseInv]. *)
  Global Instance promiseInv_ne coop await n :
    Proper ((dist n) ==> (dist n)) (promiseInv coop await).
  Proof. by solve_proper. Qed.
  Global Instance promiseInv_proper coop await :
    Proper ((≡) ==> (≡)) (promiseInv coop await).
  Proof. by solve_proper. Qed.

  (* [promiseSt]. *)
  Global Instance promiseSt_ne n coop await q pi ps τ :
    Proper ((dist n) ==> (dist n)) (promiseSt coop await q pi ps τ).
  Proof. by solve_proper. Qed.
  (*Global Instance promiseSt_proper coop await q pi ps γs :
    Proper ((≡) ==> (≡)) (promiseSt coop await q pi ps γs).*)


  (* ------------------------------------------------------------------------ *)
  (* Properties. *)

  (* Logical rules governing the predicate [token]. *)
  Section token.

    Lemma forge_token : ⊢ |==> ∃ τ, token τ.
    Proof. by iMod (own_alloc (Excl tt)) as (τ) "Htoken"; last iExists τ. Qed.

    Lemma claim_uniqueness τ : (token τ ∗ token τ) -∗ False.
    Proof. rewrite /token -own_op own_valid excl_validI. iIntros "$". Qed.

  End token.

  (* Logical rules governing the predicates [isPromiseMap], [isPromise], and
     [promiseInv]. *)
  Section promise_preds.

    (* Persistent predicates. *)
    Global Instance isMember_Persistent pi ps τ Φ :
      Persistent (isMember pi ps τ Φ).
    Proof. by apply _. Qed.
    Global Instance isPromise_Persistent pi ps Φ :
      Persistent (isPromise pi ps Φ).
    Proof. by apply _. Qed.

    Lemma update_promise_map M pi ps τ Φ :
      M !! ((pi, ps), τ) = None →
      isPromiseMap M ==∗
      isPromiseMap (<[((pi, ps), τ):=Φ]> M) ∗
      isMember pi ps τ Φ.
    Proof.
      intros Hlkp. unfold isPromiseMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc _ (gmapUR _ _) (promise_unfold <$> M)).
        apply (alloc_singleton_local_update _ ((pi, ps), τ)
          (promise_unfold Φ)).
        by rewrite /= lookup_fmap Hlkp. done. }
      iModIntro. iFrame. by rewrite fmap_insert.
    Qed.

    Lemma claim_membership M pi ps τ Φ :
      isPromiseMap M ∗ isMember pi ps τ Φ -∗
      ∃ Φ',
      ⌜ M !! ((pi, ps), τ) = Some Φ' ⌝ ∗
      (promise_unfold Φ' ≡ promise_unfold Φ).
    Proof.
      rewrite /isPromiseMap /isMember.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "[HM #HpM]". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! ((pi, ps), τ)).
      iSpecialize ("HpM" $! ((pi, ps), τ)).
      rewrite lookup_fmap lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! _)=> [Φ'|] /=; [|
      case: (M' !! _)=> [Φ'|] /=; by iExFalso].
      iExists Φ'. iSplit; first done.
      case: (M' !! _)=> [Ψ'|] //=.
      iRewrite "HM" in "HpM". rewrite option_validI agree_validI.
      iRewrite -"HpM" in "HM". by rewrite agree_idemp.
    Qed.

    Lemma promise_unfold_equiv (Φ' Φ : val → val → iProp Σ) :
      promise_unfold Φ' ≡ promise_unfold Φ -∗
      ▷ ∀ y1 y2, (Φ' y1 y2 ≡ Φ y1 y2 : iProp Σ).
    Proof.
      rewrite /promise_unfold.
      rewrite agree_equivI. iIntros "Heq". iNext. iIntros (y1 y2).
      iDestruct (discrete_fun_equivI with "Heq") as "Heq".
      iSpecialize ("Heq" $! y1).
      iDestruct (discrete_fun_equivI with "Heq") as "Heq".
      by iSpecialize ("Heq" $! y2).
    Qed.

    Lemma promiseSt_impl_pointsto coop await q pi ps τ Φ :
      promiseSt coop await q pi ps τ Φ -∗ ∃ v, pi ↦ v.
    Proof. by iIntros "[[% [% (_&_&?&_)]]|[% [H _]]]"; auto. Qed.

    Lemma promiseSt_non_duplicable coop await q pi ps ps' τ τ' Φ Φ' :
      promiseSt coop await q pi ps τ Φ -∗
      promiseSt coop await q pi ps' τ' Φ' -∗
      False.
    Proof.
      iIntros "Hp Hp'".
      iPoseProof (promiseSt_impl_pointsto with "Hp")  as "[%v  Hp]".
      iPoseProof (promiseSt_impl_pointsto with "Hp'")  as "[%v'  Hp']".
      by iDestruct (pointsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma promiseSt_proper' coop await q pi ps τ Φ Φ' :
      (Φ ≡ Φ') -∗
      promiseSt coop await q pi ps τ Φ -∗
      promiseSt coop await q pi ps τ Φ'.
    Proof. by iIntros "HΦ Hp"; iRewrite -"HΦ". Qed.

    Lemma update_promiseInv coop await q pi ps τ Φ :
      promiseInv coop await q ∗
      promiseSt coop await q pi ps τ Φ ==∗
      promiseInv coop await q ∗ isMember pi ps τ Φ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! ((pi, ps), τ)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (promiseSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_promise_map M pi ps τ Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. 
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_promiseInv_raw coop await q pi ps τ Φ' M :
      let Inv : iProp Σ :=
        ([∗ map] args ↦ Φ ∈ M,
          let pi := args.1.1 in let ps := args.1.2 in let τ := args.2 in
          promiseSt coop await q pi ps τ Φ)%I
      in
      M !! ((pi, ps), τ) = Some Φ' →
      Inv -∗
      (promiseSt coop await q pi ps τ Φ' -∗ Inv) ∗
      promiseSt coop await q pi ps τ Φ'.
    Proof.
      intros R Hlkp. rewrite /R.
      iIntros "HInv".
      iDestruct (big_sepM_delete _ _ ((pi, ps), τ) with "HInv")
        as "[HpSt HInv]"; first done.
      iFrame. iIntros "HpSt".
      by rewrite (big_opM_delete _ _ _ _ Hlkp); iFrame.
    Qed.

    Lemma lookup_promiseInv coop await q pi ps τ Φ :
      promiseInv coop await q -∗ isMember pi ps τ Φ -∗
      ▷ ((promiseSt coop await q pi ps τ Φ -∗ promiseInv coop await q) ∗
          promiseSt coop await q pi ps τ Φ
        ).
    Proof.
      iIntros "HpInv Hmem". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M pi ps τ Φ with "[$]") as
        "[%Φ' [%Hlkp #Heq]]".
      iPoseProof (promise_unfold_equiv with "Heq") as "#Heq'". iNext.
      iPoseProof (lookup_promiseInv_raw with "HInv") as "[Hclose HpSt]"; first done.
      iSplitL "Hclose HM".
      - iIntros "HpSt". iFrame. iApply "Hclose".
        iApply (promiseSt_proper' _ _ q pi ps τ Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (y1).
        rewrite discrete_fun_equivI. iIntros (y2).
        by iRewrite ("Heq'" $! y1 y2).
      - iApply (promiseSt_proper' _ _ q pi ps τ Φ' Φ with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (y1).
        by rewrite discrete_fun_equivI.
    Qed.

  End promise_preds.

End predicates.


(* ========================================================================== *)
(** Theory. *)

Section theory.
  Context `{!blazeGS Σ, !promiseGS Σ}.
  Context `{!QueueLib Σ}.

  Program Definition ASYNC (coop await : label) (COOP : iThy Σ) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (task1 task2 : val) Φ,
    ⌜ e1 = (do: coop (InjLV task1))%E ⌝ ∗
    ⌜ e2 = (async_specV await task2)%E ⌝ ∗
    ▷ BREL task1 #() ≤ task2 #() <| [(([coop], [await]), COOP)] |> {{ y1; y2, □ Φ y1 y2 }} ∗
    □ ∀ (pi : loc) (ps : loc * loc), isPromise pi ps Φ -∗ Q #pi (#ps.1, #ps.2)%V
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition AWAIT (coop await : label) : iThy Σ :=
  λ e1 e2, (λne Q,
    ∃ pi ps Φ,
    isPromise pi ps Φ ∗
    ⌜ e1 = (do: coop (InjRV #pi))%E ⌝ ∗
    ⌜ e2 = (await_specV await (#ps.1, #ps.2)%V)%E ⌝ ∗
    □ ∀ (y1 y2 : val), □ Φ y1 y2 -∗ Q y1 y2
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition COOP_pre coop await : iThy Σ → iThy Σ := λ COOP,
    iThySum (ASYNC coop await COOP) (AWAIT coop await).

  Local Instance COOP_pre_contractive coop await :
    Contractive (COOP_pre coop await).
  Proof.
    rewrite /COOP_pre => n COOP COOP' Hdist e1 e2 Q /=.
    repeat (f_contractive || f_equiv). by apply Hdist.
  Qed.

  Definition COOP_def coop await := fixpoint (COOP_pre coop await).
  Definition COOP_aux coop await : seal (COOP_def coop await).
  Proof. by eexists. Qed.
  Definition COOP coop await := (COOP_aux coop await).(unseal).

  Definition COOP_eq coop await :
    COOP coop await = COOP_def coop await
  := (COOP_aux coop await).(seal_eq).
  Global Lemma COOP_unfold coop await e1 e2 Q :
    COOP coop await e1 e2 Q ⊣⊢ COOP_pre coop await (COOP coop await) e1 e2 Q.
  Proof.
    rewrite COOP_eq /COOP_def.
    apply (fixpoint_unfold (COOP_pre coop await) e1 e2 Q).
  Qed.

End theory.


(* ========================================================================== *)
(** Verification. *)

Section verification.
  Context `{!blazeGS Σ, !promiseGS Σ}.
  Context `{!QueueLib Σ}.

  Section handler_refinement.

    Lemma next_refines (coop await : label) (q v : val) l' l :
      promiseInv coop await q -∗
      queue_inv coop await q (l' ++ l.1, l.2) -∗
      BREL next_tmpl q ≤ v <| [([coop], [await], iThyBot)] |> {{ _; _,
        queue_inv coop await q ([], l.1 ++ l.2)
      }}.
    Proof.
      iIntros "HInv (Hq & Hl2 & Hl1)". rewrite /next_tmpl //=.
      iApply (queue_empty_spec with "Hq"). iIntros "!> Hq".
      destruct (rev_case (l' ++ l.1)) as [Heq|[l'' [((k1', j'), k') Heq]]].
      - rewrite Heq //=. brel_pures_l. iModIntro. iFrame.
        by destruct (app_eq_nil _ _ Heq) as [-> ->]; simpl.
      - rewrite Heq !fmap_app.
        rewrite length_app length_cons length_nil Nat.add_1_r.
        brel_pure_l.
        iApply (queue_take_spec with "Hq"). iIntros "!> Hq".
        rewrite big_sepL_app.
        iDestruct "Hl1" as "[Hl1 [Hk1' _]]".
        iDestruct "Hk1'" as "[%e2 [Hj Hk1']]".
        rewrite ready_unfold /ready_pre.
        iSpecialize ("Hk1'" $! (l'', l.2) with "HInv [Hq Hl1 Hl2]").
        { iNext. by iFrame. }
        iApply (brel_logical_fork with "Hj [Hk1']").
        { simpl. by iApply "Hk1'". }
        iIntros (??) "[Hq Hl] Hj". iApply brel_value.
        iFrame. rewrite !big_sepL_app //=.
        iDestruct "Hl" as "[[Hl Hl2] $]". iFrame.
        destruct (rev_case l.1) as [->|[t [((k1, j), k) Ht]]]; first done.
        rewrite Ht.
        rewrite Ht app_assoc //= in Heq.
        destruct (app_inj_tail _ _ _ _ Heq) as [Hl' ->].
        rewrite big_sepL_app //=.
        iSplitR "Hj"; [|by iFrame].
        rewrite -Hl' big_sepL_app.
        by iDestruct "Hl" as "[_ $]".
    Qed.

    Lemma run_refines (coop await : label) (q : val) pi ps τ Φ (e1 e2 : expr) :
      token τ -∗ isMember pi ps τ Φ -∗
      BREL e1 ≤ e2 <| [(([coop], [await]), COOP coop await)] |> {{ y1; y2, □ Φ y1 y2 }} -∗
      ready coop await q
        (coop_handler coop q #pi e1)
        (await_handler_tmpl await (#ps.1, #ps.2)%V e2).
    Proof.
      rewrite !ready_unfold /ready_pre.
      iLöb as "IH" forall (pi ps τ Φ e1 e2).
      iIntros "Hτ #Hmem He12 %l HpromiseInv Hpre_run".
      rewrite {-1}/coop_handler /coop_handler_tmpl {-1}/await_handler_tmpl.
      iApply (brel_exhaustion' OS with "He12"); try done. iSplit.

      (* Value case. *)
      - iIntros (??) "#HΦ".
        brel_pure_l.
        iDestruct (lookup_promiseInv with "HpromiseInv Hmem") as
          "[Hclose HpromiseSt]".
        brel_pures_l.
        brel_pures_r.
        iDestruct "HpromiseSt" as
          "[[%y1 [%y2 (_&Hτ'&Hpi&_)]]|[%k12s (Hpi&Hps1&Hps2&Hk12s)]]"; first
        by iDestruct (claim_uniqueness with "[Hτ Hτ']") as "Habsurd"; iFrame.
        iApply (brel_load_l with "Hpi"). iIntros "!> Hpi".
        iApply (brel_acquire_r with "Hps1"). iIntros "Hps1".
        brel_pures_r.
        iApply (brel_load_r with "Hps2"). iIntros "Hps2".
        brel_pures_l.
        brel_pures_r.
        iApply (brel_store_r with "Hps2"). iIntros "Hps2". brel_pures_r.
        iApply (brel_release_r with "Hps1"). iIntros "Hps1". brel_pures_r.
        iApply (brel_bind' [_] []).
        { by iApply (traversable_to_iThy_bot [([coop], [await], iThyBot)]). }

        (* List iteration. *)
        iApply (brel_wand with "[Hpre_run Hk12s Hpi Hps1 Hps2 Hτ Hclose]").
        { iClear "IH".
          (* framed resources: *)
          set R : iProp Σ := (
            token τ ∗ pi ↦ InjRV (list_to_val k12s.*1) ∗
            ps.1 ↦ₛ #0 ∗ ps.2 ↦ₛ InjLV v2 ∗
            (promiseSt coop await q pi ps τ Φ -∗ promiseInv coop await q)
          )%I.
          (* invariant: *)
          set I : list (val * val) → list (val * val) → iProp Σ := (λ _k12s_l k12s_r,
            R ∗
            ∃ l',
            queue_inv_pre (ready coop await) q (l' ++ l.1, l.2) ∗
            [∗ list] args ∈ k12s_r, waiting coop await q Φ args.1 args.2
          )%I.
          iApply (brel_list_iter I with "[] [Hpre_run Hk12s Hpi Hps1 Hps2 Hτ Hclose]");
          last by (iFrame; iExists []; iFrame).
          iIntros "!> %k12s_l %k1 %k2 %k12s_r".
          iIntros "[HR [%l' [[Hq [Hl2 Hl1]] [Hk12 Hk12s_r]]]]".
          brel_pures_r. iApply brel_fork_r. iIntros (i) "Hi".
          brel_pures_l. iApply (queue_add_spec with "Hq"). iIntros "!> Hq".
          iApply brel_value. iSplitL "HR"; [by iFrame|].
          iExists (((λ: <>, k1 v1)%V, i, []) :: l'). iFrame.
          rewrite !big_sepL_app. iDestruct "Hl1" as "[$ $]".
          iSpecialize ("Hk12" with "HΦ").
          rewrite !ready_unfold /ready_pre. clear l'.
          iIntros (l') "HInv Hpre_run". simpl. brel_pures_l.
          by iApply ("Hk12" with "HInv Hpre_run").
        }

        iIntros "!>" (??) "[(Hτ & Hpi & Hps1 & Hps2 & Hclose)
          [%l' [[Hq [Hl2 Hl1]] _]]]".
        brel_pures_l.
        iApply (brel_store_l with "Hpi"). iIntros "!> Hpi". brel_pures_l.
        iDestruct ("Hclose" with "[Hpi Hps1 Hps2 Hτ]") as "HInv".
        { iLeft. by iFrame. }
        iApply (brel_wand with "[Hq Hl2 Hl1 HInv]").
        { iApply (next_refines _ _ _ _ l' l with "HInv"). by iFrame. }
        by auto.

      (* Effect case. *)
      - clear e1 e2.
        iIntros "%k1 %k2 %e1 %e2 %Q %Hk1 %Hk2 HCOOP Hk".
        rewrite COOP_unfold /COOP_pre //=.
        iDestruct "HCOOP" as
          "[[% [% [%Φ' (->&->&Htask&#HQ)]]]
           |[%pi' [%ps' [%Φ' (#Hmem'&->&->&#HQ)]]]]".
        + brel_pures_l. { by apply neutral_ectx; set_solver. }
          rewrite /(async_specV await).
          brel_pures_r. brel_pures_r.
          iApply brel_alloc_r. iIntros (ps'2) "Hps'2".
          rewrite fill_app.
          iApply brel_new_lock_r. iIntros (ps'1) "Hps'1".
          rewrite fill_app.
          brel_pures_r. brel_pures_r.
          iApply brel_fork_r. iIntros (i) "Hi".
          iApply brel_alloc_l. iIntros (pi') "!> Hpi' _". brel_pures_l.
          iDestruct "Hpre_run" as "(Hq&Hl2&Hl1)".
          iApply (queue_add_spec with "Hq"). iIntros "!> Hq".
          brel_pures_l.
          iDestruct "HpromiseInv" as "[%M [HM HInv]]".
          iApply fupd_brel.
          iMod forge_token as "[%τ' Hτ']".
          iAssert (⌜ M !! ((pi', (ps'1, ps'2)), τ') = None⌝)%I with "[HInv Hpi']"
            as %Hlkp_None.
          { case_eq (M !! ((pi', (ps'1, ps'2)), τ')); [|done].
            intros Φ'' Hlkp_Some.
            iPoseProof (lookup_promiseInv_raw with "HInv") as "[_ HpSt]"; first done.
            iPoseProof (promiseSt_impl_pointsto with "HpSt") as "[% Hpi'']".
            by iDestruct (pointsto_ne with "Hpi' Hpi''") as "%Hneq".
          }
          iMod (update_promise_map M pi' (ps'1, ps'2) τ' Φ' with "HM")
            as "[HM #Hmem']"; first done. iModIntro.
          iSpecialize ("HQ" with "[Hmem']"). { iExists τ'. by iFrame. }
          iSpecialize ("Hk" with "HQ"). iClear "HQ".
          iPoseProof ("IH" with "Hτ' Hmem' Htask") as "IH'".
          do 2 brel_pures_r.
          iApply (brel_thread_swap _ _ _ [] with "Hi"). iIntros (j k) "Hj".
          iSpecialize ("IH'" $! (((_, j, k) :: l.1), l.2)
            with "[HM HInv Hpi' Hps'1 Hps'2]").
          { iNext. iExists (<[_:=_]> M). iFrame.
            rewrite big_opM_insert; last done.
            iFrame. iRight. iExists []. by iFrame.
          }
          iSpecialize ("IH'" with "[Hq Hl1 Hl2 Hj Hτ Hk]").
          { iNext. iFrame. rewrite ready_unfold /ready_pre.
            iIntros (l') "HInv Hl'". simpl. brel_pures_l.
            by iApply ("IH" with "Hτ Hmem Hk HInv Hl'").
          }
          iClear "IH". simpl.
          rewrite /coop_run /coop_handler_tmpl.
          do 3 brel_pure_l.
          iApply (brel_wand with "IH'").
          iIntros (??) "!> [Hq Hl']". simpl. iFrame.
          iDestruct "Hl'" as "[[[% Hj] Hl'] _]". by iFrame.
        + brel_pure_l. { by apply neutral_ectx; set_solver. }
          iDestruct "Hmem'" as "[%τ' Hmem'']".
          iDestruct (lookup_promiseInv with "HpromiseInv Hmem''") as
            "[Hclose HpromiseSt]".
          brel_pure_l.
          iDestruct "HpromiseSt" as
            "[[%y1 [%y2 (#HΦ' & Hτ' & Hpi' & Hps'1 & Hps'2)]]
             |[%k12s (Hpi' & Hps'1 & Hps'2 & Hk12s)]]".
          * iSpecialize ("HQ" with "HΦ'").
            iSpecialize ("Hk" with "HQ"). iClear "HQ".
            brel_pures_l. rewrite /await_specV. brel_pures_r.
            { by apply neutral_ectx; set_solver. }
            iApply (brel_load_l with "Hpi'"). iIntros "!> Hpi'". brel_pures_l.
            iApply (brel_acquire_r with "Hps'1"). iIntros "Hps'1". brel_pures_r.
            iApply (brel_load_r with "Hps'2"). iIntros "Hps'2". brel_pures_r.
            iApply (brel_release_r with "Hps'1"). iIntros "Hps'1". brel_pures_r.
            iSpecialize ("Hclose" with "[Hpi' Hps'1 Hps'2 Hτ']").
            { iLeft. by iFrame. }
            by iApply ("IH" with "Hτ Hmem Hk Hclose Hpre_run").
          * brel_pures_l. rewrite /await_specV. brel_pures_r.
            { by apply neutral_ectx; set_solver. }
            iApply (brel_load_l with "Hpi'"). iIntros "!> Hpi'". brel_pures_l.
            iApply (brel_acquire_r with "Hps'1"). iIntros "Hps'1". brel_pures_r.
            iApply (brel_load_r with "Hps'2"). iIntros "Hps'2". brel_pures_r.
            iApply (brel_store_l with "Hpi'"). iIntros "!> Hpi'". brel_pures_l.
            iApply (brel_store_r with "Hps'2"). iIntros "Hps'2".
            iApply (brel_release_r with "Hps'1"). iIntros "Hps'1".
            iDestruct "Hpre_run" as "[Hq [Hl2 Hl1]]".
            iDestruct ("Hclose" with "[Hpi' Hps'1 Hps'2 Hk12s Hτ Hk]") as "HInv".
            { iRight. iExists ((_, _) :: k12s). iFrame.
              iIntros (y1 y2) "#HΦ'".
              iSpecialize ("HQ" with "HΦ'"). iClear "HΦ'".
              iSpecialize ("Hk" with "HQ"). iClear "HQ".
              rewrite ready_unfold /ready_pre. iIntros (l'').
              iIntros "HInv Hl''".
              brel_pure_l. brel_pure_r.
              by iApply ("IH" with "Hτ Hmem Hk HInv Hl''").
            }
            iApply (brel_wand with "[Hq Hl2 Hl1 HInv]").
            { iApply (next_refines _ _ _ _ [] l with "HInv"). by iFrame. }
            by auto.
    Qed.

  End handler_refinement.

End verification.



(* ========================================================================== *)
(** * Closed specification and proof. *)

Section closed_implementation_and_specification.
  Context `{!blazeGS Σ, !promiseGpreS Σ}.
  Context `{QueueLib Σ}.

  Section implementation.

    Definition async_impl (coop : eff_val) : expr :=
      (λ: "e", do: coop (InjL "e"))%E.
    Definition await_impl (coop : eff_val) : expr :=
      (λ: "p", do: coop (InjR "p"))%E.

    Definition run_coop₁ : val := λ: "main₁",
      effect "coop"
      let: "q" := queue_create #() in
      let: "run" := rec: "run" "p" "task" :=
        handle: "task" #() with
        | effect "coop" "request", rec "k" as multi =>
            match: "request" with
              (* Async: *) InjL "task'" =>
                let: "p'" := ref (Waiting list_nil) in
                queue_add "q" (λ: <>, "k" "p'");;
                "run" "p'" "task'"
            | (* Await: *) InjR "p'" =>
                match: !"p'" with
                  (* Done: *) InjL "v" =>
                    "k" "v"
                | (* Waiting: *) InjR "ks" =>
                    "p'" <- Waiting (list_cons "k" "ks");;
                    next_tmpl "q"
                end
            end
        | return "y" =>
            match: !"p" with
              (* Done: *) InjL <> => #() #() (* absurd *)
            | (* Waiting: *) InjR "ks" =>
                list_iter (λ: "k", queue_add "q" (λ: <>, "k" "y")) "ks"
            end;;
            "p" <- Done "y";;
            next_tmpl "q"
        end
      in
      let: "p" := ref (Waiting list_nil) in
      "run" "p" (λ: <>, "main₁" (async_impl "coop") (await_impl "coop")).

    Definition async_spec (await : eff_val) : expr := (λ: "e",
      let: "p" := (new_lock #(), ref (Waiting list_nil)) in
      Fork (await_handler_tmpl await "p" ("e" #()));;
      "p"
    )%E.
    Definition await_spec (await : eff_val) : expr :=
      (λ: "p", do: await "p")%E.

    Definition run_coop₂ : val := λ: "main₂",
      effect "await"
      let: "p" := (new_lock #(), ref (Waiting list_nil)) in
      await_handler_tmpl "await" "p" ("main₂" (async_spec "await") (await_spec "await")).

  End implementation.

  Section specification.

    Class CoopLibRelSpec (async₁ async₂ await₁ await₂ : val) (L : iLblThy Σ) := {
      is_promise : val → val → (val → val → iProp Σ) → iProp Σ;

      is_promise_Persistent p₁ p₂ Φ : Persistent (is_promise p₁ p₂ Φ);

      brel_async (task₁ task₂ : val) Φ :
        ▷ BREL task₁ #() ≤ task₂ #() <|L|> {{v₁; v₂, □ Φ v₁ v₂}} -∗
        BREL async₁ task₁ ≤ async₂ task₂ <|L|> {{ p₁; p₂, is_promise p₁ p₂ Φ }};

      brel_await p₁ p₂ Φ :
        is_promise p₁ p₂ Φ -∗
        BREL await₁ p₁ ≤ await₂ p₂ <|L|> {{v₁; v₂, □ Φ v₁ v₂ }};
    }.

  End specification.

  Section closed_proof.

    (* There exists an instance of [promiseGS] with sufficient
       initial resources to prove [promiseInv] holds. *)
    Lemma promiseInv_init :
      ⊢ |==> ∃ _ : promiseGS Σ, ∀ coop_lbl await_lbl q, promiseInv coop_lbl await_lbl q.
    Proof.
      iMod (own_alloc (● (∅ : gmap ((loc * (loc * loc)) * gname) _))) as (γ) "HI";
        first by rewrite auth_auth_valid.
      iModIntro. iExists {| promise_inG := _; promise_map := γ; |}.
      iIntros (???). iExists ∅. rewrite /isPromiseMap fmap_empty. by iFrame.
    Qed.

    (* The functions [async(_impl/_spec)] and [await(_impl/_spec)] and the
       relational theory [COOP] satisfy the relational spec [CoopLibRelSpec]. *)
    Local Program Instance coop_lib_rel_spec (coop_lbl await_lbl : label) `{!promiseGS Σ} :
      CoopLibRelSpec
        (async_implV coop_lbl)
        (async_specV await_lbl)
        (await_implV coop_lbl)
        (await_specV await_lbl)
        [([coop_lbl], [await_lbl], COOP coop_lbl await_lbl)]  := {

      is_promise := λ v₁ v₂ Φ, (∃ (p₁ : loc) (p₂ : (loc * loc)),
        ⌜ v₁ = #p₁ ⌝ ∗ ⌜ v₂ = (#p₂.1, #p₂.2)%V ⌝ ∗ isPromise p₁ p₂ Φ)%I;

    }.

    (* brel_async. *)
    Next Obligation.
      iIntros (??????) "Htask".
      rewrite /async_implV. do 2 brel_pure_l.
      iApply brel_introduction'. { by apply elem_of_list_singleton. }
      iExists (do: coop_lbl (InjLV task₁))%E, (async_specV await_lbl task₂), [], [], _.
      iSplit; [done|]. iSplit; [iPureIntro; apply _|].
      iSplit; [done|]. iSplit; [iPureIntro; apply _|].
      iSplit; [|by iIntros "!> %% Hs"; simpl; iApply "Hs"].
      rewrite COOP_unfold. iLeft. iExists task₁, task₂, _.
      iSplit; [done|]. iSplit; [done|]. iFrame. iIntros "!> %% Hp".
      iApply brel_value. by eauto.
    Qed.

    (* brel_await. *)
    Next Obligation.
      iIntros (??????) "[%p₁' [%p₂' (-> & -> & #Hp)]]".
      destruct p₂' as (p₂_lock, p₂_status).
      rewrite /await_implV. do 2 brel_pure_l.
      iApply brel_introduction'. { by apply elem_of_list_singleton. }
      iExists (do: coop_lbl (InjRV #p₁'))%E, (await_specV await_lbl _), [], [], _.
      iSplit; [done|]. iSplit; [iPureIntro; apply _|].
      iSplit; [done|]. iSplit; [iPureIntro; apply _|].
      iSplit; [|by iIntros "!> %% Hs"; simpl; iApply "Hs"].
      rewrite COOP_unfold. iRight. iExists p₁', (p₂_lock, p₂_status), _.
      iSplit; [iApply "Hp"|].
      iSplit; [done|]. iSplit; [done|]. iIntros "!> %% #HΦ".
      by iApply brel_value.
    Qed.

    Lemma run_refinement (main₁ main₂ : val) :
      (∀ async₁ async₂ await₁ await₂ L (H: CoopLibRelSpec async₁ async₂ await₁ await₂ L),
       BREL main₁ async₁ await₁ ≤ main₂ async₂ await₂ <|L|> {{_; _, True}}
      ) -∗
      BREL run_coop₁ main₁ ≤ run_coop₂ main₂ <|[]|> {{_; _, True}}.
    Proof.
      iIntros "Hmain". rewrite /run_coop₁ /run_coop₂.
      brel_pures_l. brel_pures_r.
      iApply brel_effect_l. iIntros (coop_lbl) "!> Hcoop !>".
      iApply brel_effect_r. iIntros (await_lbl) "Hawait !>".
      iApply brel_new_theory.
      iApply (brel_add_label_l with "Hcoop").
      iApply (brel_add_label_r with "Hawait").
      iApply queue_create_spec. iIntros "!>" (q) "Hq".
      brel_pures_l.
      iApply brel_alloc_r. iIntros (p₂_status) "Hstatus".
      iApply brel_new_lock_r. iIntros (p₂_lock) "Hlock".
      brel_pures_r.
      iApply brel_alloc_l. iIntros (p₁) "!> Hp₁ _".
      do 2 brel_pure_l.
      iApply fupd_brel.
      iMod promiseInv_init as "[% HpromiseInv]".
      iSpecialize ("HpromiseInv" $! coop_lbl await_lbl q).
      iMod forge_token as (τ) "Hτ".
      iMod (update_promiseInv _ _ _ p₁ (p₂_lock, p₂_status) _ (λ _ _, True%I)
        with "[HpromiseInv Hstatus Hlock Hp₁]") as "[HpromiseInv Hmember]".
      { iSplitL "HpromiseInv"; [by iApply "HpromiseInv"|].
        iRight. iExists []. by iFrame.
      }
      iPoseProof (run_refines with "Hτ Hmember [Hmain]") as "Hrun".
      { iSpecialize ("Hmain" $! _ _ _ _ _ (coop_lib_rel_spec coop_lbl await_lbl)).
        iApply (brel_wand with "Hmain"). by auto.
      }
      iEval (rewrite ready_unfold /ready_pre) in "Hrun".
      iSpecialize ("Hrun" $! ([], []) with "HpromiseInv [Hq]").
      { iNext. iFrame. by iSplit. }
      iModIntro.
      do 7 brel_pure_l.
      iApply (brel_wand with "Hrun"). by auto.
    Qed.

  End closed_proof.

End closed_implementation_and_specification.
