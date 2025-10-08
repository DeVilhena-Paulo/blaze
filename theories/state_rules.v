(* state_rules.v *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.program_logic Require Import weakestpre lifting.

From blaze Require Import syntax notation semantics iris_instantiation lifting tactics.

Class stateGpreS Σ := {
  stateGpreS_invG :: invGpreS Σ;
  stateGpreS_heapG :: gen_heapGpreS loc (option val) Σ;
  stateGpreS_labelG :: ghost_mapG Σ label unit;
}.

Definition stateΣ : gFunctors :=
  #[ invΣ; gen_heapΣ loc (option val); ghost_mapΣ label unit ].

Instance subG_stateGpreS {Σ} : subG stateΣ Σ → stateGpreS Σ.
Proof. solve_inG. Qed.

Class stateGS (Σ : gFunctors) := StateGS {
  stateGS_invGS :: invGS Σ;
  state_heapGS :: gen_heapGS loc (option val) Σ;
  state_labelG :: ghost_mapG Σ label unit;
  state_label_gname : gname;
}.

Definition past_labels (l : label) : list label :=
  imap (λ l' _, Label l') (replicate (label_car l)%nat ()).

Definition to_labels (l : label) : gmap label () :=
  let kv_pair l := (l, ()) in
  list_to_map (kv_pair <$> past_labels l).


Section past_labels.

  Lemma past_labels_succ l :
    past_labels (label_succ l) = past_labels l ++ [l].
  Proof.
    rewrite /past_labels /label_succ.
    destruct l as [n].
    rewrite replicate_S_end.
    by rewrite imap_app //= length_replicate Nat.add_0_r.
  Qed.

  Lemma NoDup_past_labels l : NoDup (past_labels l).
  Proof.
    destruct l as [n].
    induction n as [|n IH].
    - rewrite /past_labels //=.
      by apply NoDup_nil.
    - rewrite (past_labels_succ (Label n)).
      rewrite NoDup_app.
      split; [done|].
      split; [|apply NoDup_singleton].
      intros l Hl.
      rewrite elem_of_list_lookup in Hl.
      destruct Hl as [i Hl].
      rewrite list_lookup_imap_Some in Hl.
      destruct Hl as [() [Hi ->]].
      rewrite lookup_replicate in Hi.
      destruct Hi as [_ Hi]. simpl in Hi.
      rewrite elem_of_list_singleton.
      inversion 1.
      apply (Nat.lt_irrefl n).
      by rewrite H1 in Hi.
  Qed.

  Lemma lookup_past_labels_Some l i :
    i < label_car l → past_labels l !! i = Some (Label i).
  Proof.
    rewrite /past_labels list_lookup_imap_Some.
    intros Hi. exists (). split; [|done].
    rewrite lookup_replicate. by split.
  Qed.

  Lemma lookup_past_labels_None l i :
    i ≥ label_car l → past_labels l !! i = None.
  Proof.
    intros Hi.
    apply lookup_ge_None_2.
    by rewrite length_imap length_replicate.
  Qed.

  Lemma elem_of_past_labels l l' :
    label_car l < label_car l' → l ∈ past_labels l'.
  Proof.
    intros Hl.
    rewrite elem_of_list_lookup.
    exists (label_car l).
    destruct l as [n].
    by apply lookup_past_labels_Some.
  Qed.

  Lemma not_elem_of_past_labels l l' :
    label_car l ≥ label_car l' → l ∉ past_labels l'.
  Proof.
    rewrite elem_of_list_lookup.
    intros Hl [i Hlkp].
    case (le_gt_dec (label_car l') i).
    - intros Hl'.
      rewrite (lookup_past_labels_None l' i) in Hlkp; [|done].
      by inversion Hlkp.
    - intros Hl'.
      rewrite (lookup_past_labels_Some l' i) in Hlkp; [|done].
      inversion Hlkp.
      simplify_eq.
      simpl in Hl.
      apply (Nat.lt_irrefl i).
      by apply (Nat.lt_le_trans _ (label_car l')).
  Qed.

End past_labels.


Section to_labels.

  Local Open Scope nat_scope.

  Lemma lookup_to_labels_None l l' :
    label_car l' ≤ label_car l →
    (to_labels l') !! l = None.
  Proof.
    intros Hl.
    rewrite /to_labels.
    rewrite -not_elem_of_list_to_map.
    rewrite -list_fmap_compose.
    rewrite elem_of_list_fmap.
    intros [l'' [Heq Hin]].
    simpl in Heq.
    rewrite -Heq in Hin.
    by apply (not_elem_of_past_labels l l').
  Qed.

  Lemma lookup_to_labels_Some l l' :
    label_car l < label_car l' →
    (to_labels l') !! l = Some ().
  Proof.
    intros Hl.
    rewrite /to_labels.
    apply (elem_of_list_to_map_1 (_ <$> past_labels l') l).
    - rewrite -list_fmap_compose //=.
      by apply NoDup_fmap_2; [intros ??|apply NoDup_past_labels].
    - rewrite elem_of_list_fmap.
      exists l. split; [done|].
      by apply elem_of_past_labels.
  Qed.

  Lemma to_labels_succ l :
    to_labels (label_succ l) = <[l := ()]> (to_labels l).
  Proof.
    rewrite /to_labels past_labels_succ fmap_app list_to_map_app //=.
    rewrite insert_empty map_union_comm.
    - by rewrite -insert_union_singleton_l.
    - rewrite map_disjoint_singleton_r.
      by apply lookup_to_labels_None.
  Qed.

End to_labels.


Global Program Instance stateGS_irisGS `{!stateGS Σ} : irisGS lambda_blaze Σ := {
  iris_invGS := stateGS_invGS;
  state_interp σ _ _ _ := (gen_heap_interp σ.(heap) ∗ ghost_map_auth state_label_gname 1%Qp (to_labels (next_label σ)))%I;
  fork_post _ := True%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  by iIntros (??????) "/= $".
Qed.

Local Definition pointsto_def `{!stateGS Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Local Definition is_label_def `{stateGS Σ} (dq : dfrac) (l : label) : iProp Σ :=
  ghost_map_elem state_label_gname l dq ().
Local Definition is_label_aux : seal (@is_label_def). Proof. by eexists. Qed.
Definition is_label := is_label_aux.(unseal).
Local Definition is_label_eq : @is_label = @is_label_def := is_label_aux.(seal_eq).
Global Arguments is_label {Σ _}.

Definition unshot `{stateGS Σ} r := pointsto r (DfracOwn 1) #true.


Section lifting.
Context `{!stateGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

(** Effect allocation *)

Global Instance is_label_timeless dq l : Timeless (is_label dq l).
Proof. rewrite is_label_eq. apply _. Qed.

Global Instance is_label_fractional l : Fractional (λ q, is_label (DfracOwn q) l)%I.
Proof. rewrite is_label_eq. apply _. Qed.

Global Instance is_label_as_fractional l q :
  AsFractional (is_label (DfracOwn q) l) (λ q, is_label (DfracOwn q) l)%I q.
Proof. rewrite is_label_eq. apply _. Qed.

Global Instance is_label_persistent l : Persistent (is_label DfracDiscarded l).
Proof. rewrite is_label_eq. apply _. Qed.

Global Instance is_label_combine_sep_gives dq1 dq2 l :
  CombineSepGives (is_label dq1 l) (is_label dq2 l) ⌜ ✓ (dq1 ⋅ dq2) ⌝.
Proof.
  rewrite is_label_eq /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? _]. eauto.
Qed.

Lemma is_label_combine dq1 dq2 l :
  is_label dq1 l -∗ is_label dq2 l -∗ is_label (dq1 ⋅ dq2) l.
Proof.
  rewrite is_label_eq.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$".
Qed.

Global Instance is_label_combine_as dq1 dq2 l :
  CombineSepAs (is_label dq1 l) (is_label dq2 l) (is_label (dq1 ⋅ dq2) l) | 60.
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (is_label_combine with "H1 H2") as "$".
Qed.

Lemma is_label_valid dq l : is_label dq l -∗ ⌜ ✓ dq ⌝.
Proof. rewrite is_label_eq. apply ghost_map_elem_valid. Qed.

Lemma is_label_valid_2 dq1 dq2 l :
  is_label dq1 l -∗ is_label dq2 l -∗ ⌜ ✓ (dq1 ⋅ dq2) ⌝.
Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

Lemma is_label_frac_ne dq1 dq2 l1 l2 :
  ¬ ✓(dq1 ⋅ dq2) → is_label dq1 l1 -∗ is_label dq2 l2 -∗ ⌜ l1 ≠ l2 ⌝.
Proof. rewrite is_label_eq. apply ghost_map_elem_frac_ne. Qed.

Lemma is_label_ne dq2 l1 l2 :
  is_label (DfracOwn 1) l1 -∗ is_label dq2 l2 -∗ ⌜ l1 ≠ l2 ⌝.
Proof. rewrite is_label_eq. apply ghost_map_elem_ne. Qed.

Lemma is_label_persist dq l : is_label dq l ==∗ is_label DfracDiscarded l.
Proof. rewrite is_label_eq. apply ghost_map_elem_persist. Qed.

Global Instance frame_is_label p l q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p
    (is_label (DfracOwn q1) l)
    (is_label (DfracOwn q2) l)
    (is_label (DfracOwn q) l) | 5.
Proof. apply: frame_fractional. Qed.

Lemma wp_effect E Φ s k e :
  ▷ (∀ l, is_label (DfracOwn 1) l ={E}=∗ WP fill k (lbl_subst s l e) @ E {{ Φ }}) -∗
  WP fill k (Effect s e) @ E {{ Φ }}.
Proof.
  iIntros "HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels]".
  iModIntro. iSplit.
  { iPureIntro. exists (lbl_subst s (next_label σ) e).
    exists (state_upd_next_label label_succ σ), [].
    by apply EffectS. }
  iIntros (e₂ σ₂ efs Hstep') "!> Hns". inv_base_step.
  iMod (ghost_map_insert (next_label σ) () with "Hlabels") as "[Hlabels Hl]".
  { by apply lookup_to_labels_None. }
  rewrite is_label_eq. iMod ("HΦ" with "Hl") as "HΦ".
  iModIntro. rewrite to_labels_succ. by iFrame.
Qed.

Lemma wp_effect' E Φ s e :
  ▷ (∀ l, is_label (DfracOwn 1) l ={E}=∗ WP lbl_subst s l e @ E {{ Φ }}) -∗
  WP Effect s e @ E {{ Φ }}.
Proof. by iApply (wp_effect E Φ s []). Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val] (and sealing). *)

Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_as_fractional l q v :
  AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
Proof. rewrite pointsto_unseal. apply _. Qed.

Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
  CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  rewrite pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? [=->]]. eauto.
Qed.

Lemma pointsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  rewrite pointsto_unseal.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$" gives %[_ [= ->]].
Qed.

Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
  CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
  (* higher cost than the Fractional instance, which kicks in for #qs *)
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
Qed.

Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. rewrite pointsto_unseal. apply pointsto_valid. Qed.
Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[? [= ?]]. done. Qed.
Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[_ [= ?]]. done. Qed.

Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_frac_ne. Qed.
Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_ne. Qed.

Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. rewrite pointsto_unseal. apply pointsto_persist. Qed.
Lemma pointsto_unpersist l v : l ↦□ v ==∗ ∃ q, l ↦{#q} v.
Proof. rewrite pointsto_unseal. apply pointsto_unpersist. Qed.

Global Instance frame_pointsto p l v q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
Proof. apply: frame_fractional. Qed.

Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs IH] forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_pointsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.pointsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n IH] forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton pointsto_unseal.
  iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_fork K E e Φ :
  ▷ WP e @ ⊤ {{ fork_post }} -∗
  ▷ WP fill K #() @ E {{ Φ }} -∗
  WP fill K (Fork e) @ E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_fill_base_step; first done.
  iIntros (σ1 ns κ κs nt) "Hσ". iModIntro.
  iSplit. { iPureIntro. exists #(), σ1, [e]. apply ForkS. }
  iIntros (e2 σ2 efs Hstep). iIntros "!> Hcred !>". inv_base_step. iFrame.
Qed.

Lemma wp_allocN K E Φ (n : Z) v :
  (0 < n)%Z →
  ▷ (∀ l,
      ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) -∗
      WP fill K #l @ E {{ Φ }}) -∗
  WP fill K (AllocN #n v) @ E {{ Φ }}.
Proof.
  iIntros (?) "HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>". iSplit.
  { iPureIntro. set (l := Loc.fresh (dom σ.(heap))).
    exists #l, (state_init_heap l n v σ), [].
    by apply base_step_alloc_fresh. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hheap")
    as "(Hheap & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite length_replicate Z2Nat.id; auto with lia. }
  iModIntro. iSplit; first done. iFrame.
  iApply "HΦ". iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.

Lemma wp_alloc K E Φ v :
  ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ WP fill K #l @ E {{ Φ }}) -∗
  WP fill K (ref v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ". iApply wp_allocN; first lia.
  iIntros "!> /=" (l) "[[Hl Hm] _]". rewrite Loc.add_0.
  iApply ("HΦ" with "Hl Hm").
Qed.

Lemma wp_load K E Φ l dq v :
  ▷ l ↦{dq} v -∗
  ▷ (l ↦{dq} v -∗ WP fill K v @ E {{ Φ }}) -∗
  WP fill K (! #l) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as "%Hl". iSplit.
  { iPureIntro. exists v, σ, []. by apply LoadS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iFrame. iModIntro. iSplit; first done.
  iApply ("HΦ" with "Hl").
Qed.

Lemma wp_store K E Φ l v w :
  ▷ l ↦ v -∗
  ▷ (l ↦ w -∗ WP fill K #() @ E {{ Φ }}) -∗
  WP fill K (#l <- w) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists #(), (state_upd_heap <[ l := Some w ]> σ), [].
    by eapply StoreS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some w) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_xchg K E Φ l v w :
  ▷ l ↦ v -∗
  ▷ (l ↦ w -∗ WP fill K v @ E {{ Φ }}) -∗
  WP fill K (Xchg #l w) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists v, (state_upd_heap <[ l := Some w ]> σ), [].
    by eapply XchgS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some w) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_free K E Φ l v :
  ▷ l ↦ v -∗
  ▷ WP fill K #() @ E {{ Φ }} -∗
  WP fill K (Free #l) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists #(), (state_upd_heap <[ l := None ]> σ), [].
    by eapply FreeS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ None with "Hheap Hl") as "[$ Hl]".
  by iFrame.
Qed.

Lemma wp_faa K E Φ l (n m : Z) :
  ▷ l ↦ #n -∗
  ▷ (l ↦ #(n + m) -∗ WP fill K #n @ E {{ Φ }}) -∗
  WP fill K (FAA #l #m) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists #n, (state_upd_heap <[ l := Some #(n + m) ]> σ), [].
    by eapply FaaS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some #(n + m)) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail K E Φ l v1 v2 w :
  w ≠ v1 →
  vals_compare_safe w v1 →
  ▷ l ↦ w -∗
  ▷ (l ↦ w -∗ WP fill K (w, #false)%V @ E {{ Φ }}) -∗
  WP fill K (CmpXchg #l v1 v2) @ E {{ Φ }}.
Proof.
  iIntros (??) ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists (w, #false)%V, σ, [].
    by apply CmpXchgS; last rewrite bool_decide_eq_false_2. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  rewrite bool_decide_eq_false_2 //.
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc K E Φ l v1 v2 w :
  w = v1 →
  vals_compare_safe w v1 →
  ▷ l ↦ w -∗
  ▷ (l ↦ v2 -∗ WP fill K (w, #true)%V @ E {{ Φ }}) -∗
  WP fill K (CmpXchg #l v1 v2) @ E {{ Φ }}.
Proof.
  iIntros (-> ?) ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists (v1, #true)%V, (state_upd_heap <[l := Some v2]> σ), [].
    by apply CmpXchgS; last rewrite bool_decide_eq_true_2. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  rewrite bool_decide_eq_true_2 //.
  iMod (gen_heap_update  _ _ _ (Some v2) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_handle_os k k' E Φ hs (l : label) (v : val) (h ret : expr) :
  let c := match hs with Deep => HandleCtx hs OS l h ret :: k' | Shallow => k' end in
  l ∉ ectx_labels k' →
  (▷ ∀ r, unshot r -∗ WP fill k (App (App h v) (ContV r c)) @ E {{ Φ }}) -∗
  WP fill k (Handle hs OS (EffLabel l) (fill k' (Do (EffLabel l) (Val v))) h ret) @ E {{ Φ }}.
Proof.
  iIntros (c HNeutral) "Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>". iSplit.
  { iPureIntro. set (r := Loc.fresh (dom σ.(heap))).
    exists (App (App h v) (ContV r c)), (state_upd_heap <[r:=Some $ LitV $ LitBool true]> σ), [].
    by apply base_step_handle_os_eff. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  - iMod (gen_heap_alloc σ.(heap) r (Some #true) with "Hheap") as "(Hheap & Hr & Hm)"; first done.
    iModIntro. iSplit; first done. iFrame. rewrite to_of_eff in H10.
    injection H10 as -> ->.
    iApply "Hwp".
    iPoseProof (heap_array_to_seq_pointsto r #true 1 with "[Hr]") as "[Hr _]".
    { by rewrite //= map_union_empty big_sepM_singleton //=. }
    by rewrite //= Loc.add_0.
  - specialize (of_eff_not_val l v k') as Habsurd.
    by rewrite /of_eff -H3 in Habsurd.
Qed.

Lemma wp_cont k E Φ r k' v :
  ▷ unshot r -∗
  ▷ WP fill k (fill k' v) @ E {{ Φ }} -∗
  WP fill k (App (ContV r k') v) @ E {{ Φ }}.
Proof.
  iIntros ">Hr Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "[Hheap Hlabels] !>".
  rewrite /unshot pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hr") as "%Hr". iSplit.
  { iPureIntro.
    exists (fill k' v), (state_upd_heap <[r:=Some #false]> σ), [].
    by apply ContS. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some #false) with "Hheap Hr") as "[$ Hr]".
  by iFrame.
Qed.

End lifting.
