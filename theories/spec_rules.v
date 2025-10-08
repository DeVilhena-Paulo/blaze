(* spec_rules.v *)

From iris.algebra Require Import auth excl gmap agree list dfrac dfrac_agree numbers.
From iris.algebra.lib Require Import gmap_view.
From iris.bi Require Export fractional.
From iris.base_logic Require Export invariants ghost_map gen_heap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From iris.heap_lang Require Export locations.

From blaze Require Import syntax notation semantics iris_instantiation state_rules.

Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmra := gmapUR nat (exclR exprO).
Definition heapUR (L V : Type) `{Countable L} : ucmra :=
  gmapUR L (dfrac_agreeR (optionO (leibnizO V))).

Definition to_tpool (tp : list expr) : tpoolUR :=
  map_seq 0 (Excl <$> tp).

Definition to_heap (σ : state) : heapUR loc val :=
  fmap (to_frac_agree 1) (heap σ).

Class cfgGpreS Σ := {
  spec_GpreS_label_inG :: ghost_mapG Σ label unit;
  spec_GpreS_tpool_inG :: inG Σ (authR tpoolUR);
  spec_GpreS_heap_inG  :: inG Σ (authR (heapUR loc val));
}.

Definition cfgΣ : gFunctors :=
  #[ GFunctor (authR tpoolUR) ; GFunctor (authR (heapUR loc val)); ghost_mapΣ label unit ].

Instance subG_cfgGpreS {Σ} : subG cfgΣ Σ → cfgGpreS Σ.
Proof. solve_inG. Qed.

Class cfgGS (Σ : gFunctors) := CfgGS {
  spec_label_inG :: ghost_mapG Σ label unit;
  spec_tpool_inG :: inG Σ (authUR tpoolUR);
  spec_heap_inG  :: inG Σ (authUR (heapUR loc val));
  spec_label_gname : gname;
  spec_tpool_gname : gname;
  spec_heap_gname : gname;
}.

Section spec_definitions.
  Context `{!invGS Σ, !cfgGS Σ}.

  Local Definition spec_label_def (dq : dfrac) (l : label) : iProp Σ :=
    ghost_map_elem spec_label_gname l dq ().
  Local Definition spec_label_aux : seal (@spec_label_def). Proof using . by eexists. Qed.
  Definition spec_label := spec_label_aux.(unseal).
  Local Definition spec_label_eq : @spec_label = @spec_label_def := spec_label_aux.(seal_eq).

  Local Definition heapS_pointsto_def (l : loc) (dq : dfrac) (v: val) : iProp Σ :=
    own spec_heap_gname (◯ {[ l := to_dfrac_agree dq (Some v) ]}).
  Local Definition heapS_pointsto_aux : seal (@heapS_pointsto_def). by eexists. Qed.
  Definition heapS_pointsto := heapS_pointsto_aux.(unseal).
  Local Definition heapS_pointsto_eq : @heapS_pointsto = @heapS_pointsto_def := heapS_pointsto_aux.(seal_eq).

  Local Definition tpool_pointsto_def (j : nat) (e : expr) : iProp Σ :=
    own spec_tpool_gname (◯ {[ j := Excl e ]}).
  Local Definition tpool_pointsto_aux : seal (@tpool_pointsto_def). by eexists. Qed.
  Definition tpool_pointsto := tpool_pointsto_aux.(unseal).
  Local Definition tpool_pointsto_eq : @tpool_pointsto = @tpool_pointsto_def := tpool_pointsto_aux.(seal_eq).

  Definition spec_inv (ρ : cfg lambda_blaze) : iProp Σ :=
    ∃ tp σ,
      ⌜ rtc erased_step ρ (tp, σ) ⌝ ∗
      own spec_tpool_gname (● to_tpool tp) ∗
      own spec_heap_gname (● to_heap σ) ∗
      ghost_map_auth spec_label_gname 1%Qp (to_labels σ.(next_label)).
  Definition spec_ctx : iProp Σ :=
    ∃ ρ, inv specN (spec_inv ρ).

  Global Instance spec_label_persistent l : Persistent (spec_label DfracDiscarded l).
  Proof. rewrite spec_label_eq. apply _. Qed.

  Global Instance spec_label_timeless dq l : Timeless (spec_label dq l).
  Proof. rewrite spec_label_eq. apply _. Qed.
  Global Instance tpool_pointsto_timeless j e : Timeless (tpool_pointsto j e).
  Proof. rewrite tpool_pointsto_eq. apply _. Qed.
  Global Instance heapS_pointsto_timeless l dq v : Timeless (heapS_pointsto l dq v).
  Proof. rewrite heapS_pointsto_eq. apply _. Qed.
End spec_definitions.

Notation "l ↦ₛ dq v" := (heapS_pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ₛ dq  v") : bi_scope.
Notation "j ⤇ e" := (tpool_pointsto j e)
  (at level 20, format "j  ⤇  e") : bi_scope.

Definition unshotₛ `{cfgGS Σ} (r : loc) := heapS_pointsto r (DfracOwn 1) #true.


Section to_tpool.
  Context `{!cfgGS Σ}.

  Implicit Types tp : list expr.
  Implicit Types σ : state.

  (** Conversion to tpools and back *)
  Lemma to_tpool_valid tp : ✓ to_tpool tp.
  Proof.
    rewrite /to_tpool. intros ?. rewrite lookup_map_seq_0 list_lookup_fmap.
    by destruct (tp !! i).
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof. by rewrite /to_tpool lookup_map_seq_0 list_lookup_fmap. Qed.
  Lemma tpool_lookup_Some tp j e :
    to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Local Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j := e]> tp) = <[j := Excl e]> (to_tpool tp).
  Proof.
    intros ?. rewrite /to_tpool insert_map_seq_0.
    - by rewrite list_fmap_insert.
    - by rewrite length_fmap.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j := e]> tp) = <[j := Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.

  Lemma to_tpool_singleton e : to_tpool [e] = {[ 0 := Excl e ]}.
  Proof. by rewrite /to_tpool map_seq_singleton. Qed.

  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp := Excl e]>(to_tpool tp).
  Proof. by rewrite /to_tpool fmap_app map_seq_snoc length_fmap. Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included_l [ex [/leibniz_equiv_iff]].
    by rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included /leibniz_equiv_iff ->].
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.
End to_tpool.

Section to_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : state.

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros i. rewrite /to_heap lookup_fmap. by destruct (heap σ !! i) eqn:Hi; rewrite Hi. Qed.

  Lemma lookup_to_heap_None σ l : heap σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma to_heap_insert l ov σ :
    to_heap (state_upd_heap <[l:=ov]> σ) = <[l:= to_frac_agree 1 ov]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_heap σ → heap σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
End to_heap.

Section spec_label.
  Context `{!cfgGS Σ}.

  Lemma Excl_expr_included (e e' : expr) : Excl' e ≼ Excl' e' → e = e'.
  Proof. by rewrite Excl_included; apply leibniz_equiv. Qed.

  Global Instance spec_label_fractional l : Fractional (λ q, spec_label (DfracOwn q) l)%I.
  Proof. rewrite spec_label_eq. apply _. Qed.

  Global Instance spec_label_as_fractional l q :
    AsFractional (spec_label (DfracOwn q) l) (λ q', spec_label (DfracOwn q') l)%I q.
  Proof. rewrite spec_label_eq. apply _. Qed.

  Global Instance frame_spec_label p l q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (spec_label (DfracOwn q1) l) (spec_label (DfracOwn q2) l) (spec_label (DfracOwn q) l) | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance spec_label_combine_sep_gives dq1 dq2 l :
    CombineSepGives (spec_label dq1 l) (spec_label dq2 l) ⌜ ✓ (dq1 ⋅ dq2) ⌝.
  Proof.
    rewrite spec_label_eq /CombineSepGives. iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[? _]. eauto.
  Qed.

  Lemma spec_label_combine dq1 dq2 l :
    spec_label dq1 l -∗ spec_label dq2 l -∗ spec_label (dq1 ⋅ dq2) l.
  Proof.
    rewrite spec_label_eq.
    iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$".
  Qed.

  Global Instance spec_label_combine_as dq1 dq2 l :
    CombineSepAs (spec_label dq1 l) (spec_label dq2 l) (spec_label (dq1 ⋅ dq2) l) | 60.
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (spec_label_combine with "H1 H2") as "$".
  Qed.

  Lemma spec_label_valid dq l : spec_label dq l -∗ ⌜ ✓ dq ⌝.
  Proof. rewrite spec_label_eq. apply ghost_map_elem_valid. Qed.

  Lemma spec_label_valid_2 dq1 dq2 l :
    spec_label dq1 l -∗ spec_label dq2 l -∗ ⌜ ✓ (dq1 ⋅ dq2) ⌝.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  Lemma spec_label_frac_ne dq1 dq2 l1 l2 :
    ¬ ✓(dq1 ⋅ dq2) → spec_label dq1 l1 -∗ spec_label dq2 l2 -∗ ⌜ l1 ≠ l2 ⌝.
  Proof. rewrite spec_label_eq. apply ghost_map_elem_frac_ne. Qed.

  Lemma spec_label_ne dq2 l1 l2 :
    spec_label (DfracOwn 1) l1 -∗ spec_label dq2 l2 -∗ ⌜ l1 ≠ l2 ⌝.
  Proof. rewrite spec_label_eq. apply ghost_map_elem_ne. Qed.

  Lemma spec_label_persist dq l : spec_label dq l ==∗ spec_label DfracDiscarded l.
  Proof. rewrite spec_label_eq. apply ghost_map_elem_persist. Qed.
End spec_label.

Lemma spec_init `{!invGS Σ, !cfgGpreS Σ} e σ E :
  ↑specN ⊆ E →
  ⊢ |={E}=> ∃ (_ : cfgGS Σ),
      inv specN (spec_inv ([e], σ)) ∗
      0 ⤇ e.
Proof.
  intros ?.
  iMod (own_alloc (● to_tpool [e] ⋅ ◯ to_tpool [e])) as (γtp) "[Htp Hj]".
  { apply auth_both_valid_discrete. split=>//. apply to_tpool_valid. }
  set (heap := to_heap σ).
  iMod (own_alloc (● heap)) as (γheap) "Hheap".
  { apply auth_auth_valid. apply to_heap_valid. }
  iMod (ghost_map_alloc (to_labels σ.(next_label))) as (γlabels) "[Hlabels _]".

  set (Hcfg := CfgGS _ _ _ _ γlabels γtp γheap). iExists Hcfg.
  iEval (rewrite to_tpool_singleton) in "Hj".
  rewrite tpool_pointsto_eq. iFrame.
  iApply (inv_alloc specN _ (spec_inv ([e], σ))).
  iExists [e], σ. by iFrame.
Qed.

Lemma spec_adequacy E e σ e' `{!invGS Σ, !cfgGS Σ} :
  ↑specN ⊆ E →
  inv specN (spec_inv ([e], σ)) -∗
  0 ⤇ e' ={E}=∗
  ∃ efs σ',
    ⌜rtc erased_step ([e], σ) (e' :: efs, σ')⌝.
Proof.
  iIntros (?) "#Hinv Hj".
  iInv specN as (efs σ') ">(%Hstep & Htp & Hheap & Hlabels)" "Hclose".
  rewrite tpool_pointsto_eq /tpool_pointsto_def.
  iCombine "Htp Hj" gives
    %[Hv%tpool_singleton_included _]%auth_both_valid_discrete.
  destruct efs as [|? efs]; simplify_eq/=.
  iMod ("Hclose" with "[$Htp $Hheap $Hlabels //]") as "_". eauto 10.
Qed.

Section cfg.
  Context `{!invGS Σ, cfgGS Σ}.
  Implicit Types tp : list expr.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Local Hint Resolve tpool_lookup : core.
  Local Hint Resolve tpool_lookup_Some : core.
  Local Hint Resolve to_tpool_insert : core.
  Local Hint Resolve to_tpool_insert' : core.
  Local Hint Resolve tpool_singleton_included : core.

  Global Instance pointstoS_timeless l dq v : Timeless (l ↦ₛ {dq} v).
  Proof. apply _. Qed.

  Lemma pointstoS_agree l dq1 dq2 v1 v2 : l ↦ₛ{dq1} v1 -∗ l ↦ₛ{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply entails_wand, wand_intro_r.
    rewrite heapS_pointsto_eq -own_op own_valid uPred.discrete_valid. f_equiv.
    rewrite auth_frag_op_valid singleton_op singleton_valid dfrac_agree_op_valid_L.
    by intros [_ [=]].
  Qed.

  Lemma pointstoS_combine l dq1 dq2 v1 v2 :
    l ↦ₛ{dq1} v1 -∗ l ↦ₛ{dq2} v2 -∗ l ↦ₛ{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (pointstoS_agree with "Hl1 Hl2") as %->.
    rewrite heapS_pointsto_eq. iCombine "Hl1 Hl2" as "Hl".
    rewrite -dfrac_agree_op. by iFrame.
  Qed.

  Global Instance pointstoS_fractional l v : Fractional (λ q, l ↦ₛ{#q} v)%I.
  Proof.
    intros p q. rewrite heapS_pointsto_eq -own_op -auth_frag_op.
    by rewrite singleton_op -pair_op agree_idemp.
  Qed.

  Lemma pointstoS_split l q1 q2 (v : val) :
    l ↦ₛ{# q1 ⋅ q2} v -∗ (l ↦ₛ{# q1} v ∗ l ↦ₛ{# q2} v).
  Proof. by iIntros "Hl"; iPoseProof (pointstoS_fractional with "Hl") as "[$ $]". Qed.

  Lemma pointstoS_valid l dq v : l ↦ₛ{dq} v -∗ ✓ dq.
  Proof.
    rewrite heapS_pointsto_eq /heapS_pointsto_def own_valid !discrete_valid auth_frag_valid singleton_valid.
    apply entails_wand, pure_mono. by intros [? _].
  Qed.

  Lemma pointstoS_valid_2 l dq1 dq2 v1 v2 :
    l ↦ₛ{dq1} v1 -∗ l ↦ₛ{dq2} v2 -∗ ✓ (dq1 ⋅ dq2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (pointstoS_combine with "H1 H2") as "[Hl ->]".
    by iApply (pointstoS_valid l _ v2).
  Qed.

  Global Instance pointstoS_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦ₛ{dq1} v1) (l ↦ₛ{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]". iSplit.
    - iDestruct (pointstoS_valid_2 with "H1 H2") as %?; auto.
    - iDestruct (pointstoS_agree with "H1 H2") as %?; auto.
  Qed.

  Global Instance pointstoS_combine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦ₛ {dq1} v1) (l ↦ₛ {dq2} v2) (l ↦ₛ {dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (pointstoS_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma prim_step_insert K es j e σ e' σ' efs :
    es !! j = Some (fill K e) →
    prim_step e σ e' σ' efs →
    erased_step (es, σ) (<[j:=fill K e']> es ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle es j (fill K e)) //.
    rewrite insert_app_r_alt length_take_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. exists [].
    eapply step_atomic; eauto. by eapply Ectx_prim_step'.
  Qed.

  Lemma base_step_insert K es j e σ e' σ' efs :
    es !! j = Some (fill K e) →
    base_step e σ e' σ' efs →
    erased_step (es, σ) (<[j:=fill K e']> es ++ efs, σ').
  Proof.
    intros. eapply prim_step_insert; first done. by apply base_prim_step.
  Qed.

  Lemma prim_step_insert_no_fork K es j e σ e' σ' :
    es !! j = Some (fill K e) →
    prim_step e σ e' σ' [] →
    erased_step (es, σ) (<[j := fill K e']> es, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply prim_step_insert. Qed.

  Lemma base_step_insert_no_fork K es j e σ e' σ' :
    es !! j = Some (fill K e) →
    base_step e σ e' σ' [] →
    erased_step (es, σ) (<[j := fill K e']> es, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply base_step_insert. Qed.

  Lemma do_pure_steps E j K e e' n :
    ↑specN ⊆ E →
    nsteps pure_step n e e' →
    spec_ctx -∗
    j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof.
    iIntros (? He) "#Hinv Hj". iDestruct "Hinv" as (ρ) "Hspec".
    rewrite tpool_pointsto_eq /tpool_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update, (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K e']> tp), σ.
    rewrite to_tpool_insert' //.
    iFrame. iPureIntro.
    apply rtc_nsteps in Hrtc; destruct Hrtc as [m Hrtc].
    apply (rtc_nsteps_2 (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Htpj He.
    induction n as [|n IH] => e1 e3 Htpj He1.
    - inversion He1; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in He1 as (e2 & He1 & He2).
      specialize (IH _ _ Htpj He1).
      eapply nsteps_r; eauto.
      replace
        (<[j := fill K e3]> tp) with
        (<[j := fill K e3]> (<[j := fill K e2]> tp))
          by apply list_insert_insert.
      destruct He2 as [Hsafe Hdeter].
      specialize (Hsafe σ). destruct Hsafe as (e'' & σ' & efs & Hsafe).
      specialize (Hdeter σ [] e'' σ' efs Hsafe).
      destruct Hdeter as (_ & <- & <- & ->).
      inv Hsafe; simpl in *.
      rewrite -!fill_app.
      eapply base_step_insert_no_fork; eauto.
      apply list_lookup_insert. apply lookup_lt_is_Some; eauto.
  Qed.

  Lemma step_alloc_label E j K s e :
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Effect s e) ={E}=∗ ∃ (l : label), j ⤇ fill K (lbl_subst s l e) ∗ spec_label (DfracOwn 1) l.
  Proof.
    iIntros (?) "#Hinv Hj". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite tpool_pointsto_eq /tpool_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    set (l := σ.(next_label)).
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update, (exclusive_local_update _ (Excl (fill K (lbl_subst s l e)))). }
    iMod (ghost_map_insert l with "Hlabels") as "[Hlabels Hl]".
    { by apply lookup_to_labels_None. }
    iExists l. rewrite spec_label_eq. iFrame "Hj Hl".
    iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K (lbl_subst s l e)]> tp), (state_upd_next_label label_succ σ).
    rewrite to_tpool_insert' // to_labels_succ. iFrame.
    iPureIntro. eapply rtc_r, base_step_insert_no_fork; eauto.
    by apply EffectS.
  Qed.

  Lemma step_alloc E j K e v:
    IntoVal e v →
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Alloc e) ={E}=∗ ∃ l, j ⤇ fill K #l ∗ l ↦ₛ v.
  Proof.
    iIntros (<- ?) "#Hinv Hj". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite tpool_pointsto_eq /tpool_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    set (l := Loc.fresh (dom (heap σ))).
    assert (heap σ !! l = None).
    { apply not_elem_of_dom. rewrite -(Loc.add_0 l). apply Loc.fresh_fresh. lia. }
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update, (exclusive_local_update _ (Excl (fill K (Val #l)))). }
    iMod (own_update with "Hheap") as "[Hheap Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ l (to_frac_agree 1 (Some v))); last done.
      by apply lookup_to_heap_None. }
    iExists l. rewrite heapS_pointsto_eq. iFrame "Hj Hl".
    iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K (Val #l)]> tp), (state_init_heap l 1 v σ).
    iSplit; last first.
    { rewrite state_init_heap_singleton to_heap_insert to_tpool_insert' //. iFrame. }
    iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto.
    apply base_step_alloc_fresh. lia.
  Qed.

  Lemma step_load E j K l q v:
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (! #l) -∗
    l ↦ₛ{q} v ={E}=∗
    j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq /tpool_pointsto_def heapS_pointsto_eq /heapS_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[?%heap_singleton_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K v))). }
    iFrame "Hj Hl".
    iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K v]> tp), σ.
    rewrite to_tpool_insert' //. iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto.
    econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' e v:
    IntoVal e v →
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Store #l e) -∗
    l ↦ₛ v' ={E}=∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<- ?) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hheap Hl") as "[Hheap Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 (Some v))); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K #()]> tp), (state_upd_heap <[l := Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_xchg E j K l v' e v:
    IntoVal e v →
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Xchg #l e) -∗
    l ↦ₛ v' ={E}=∗ j ⤇ fill K v' ∗ l ↦ₛ v.
  Proof.
    iIntros (<- ?) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K v'))). }
    iMod (own_update_2 with "Hheap Hl") as "[Hheap Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 (Some v))); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K v']> tp), (state_upd_heap <[l := Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_free E j K l v:
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Free #l) -∗
    l ↦ₛ v ={E}=∗ j ⤇ fill K #().
  Proof.
    iIntros (?) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hheap Hl") as "[Hheap Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 None)); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K #()]> tp), (state_upd_heap <[l := None]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_cmpxchg_fail E j K l q v' e1 v1 e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    ↑specN ⊆ E →
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    spec_ctx -∗ j ⤇ fill K (CmpXchg #l e1 e2) -∗ l ↦ₛ{q} v'
    ={E}=∗ j ⤇ fill K (v', #false)%V ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (<- <- ???) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    assert (j < length tp) by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (v', #false)%V))). }
    iFrame "Hj Hl". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K (v', #false)%V]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r; first done.
    eapply base_step_insert_no_fork; eauto.
    by eapply (CmpXchgS l v1 v2 v' σ false); last rewrite bool_decide_eq_false_2.
  Qed.

  Lemma step_cmpxchg_suc E j K l e1 v1 v1' e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    ↑specN ⊆ E →
    vals_compare_safe v1 v1' →
    v1 = v1' →
    spec_ctx -∗ j ⤇ fill K (CmpXchg #l e1 e2) -∗ l ↦ₛ v1'
    ={E}=∗ j ⤇ fill K (v1, #true)%V ∗ l ↦ₛ v2.
  Proof.
    iIntros (<- <- ? ? <-) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (v1, #true)%V))). }
    assert (j < length tp) by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Hheap Hl") as "[Hheap Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 (Some v2))); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iMod ("Hclose" with "[-]"); last done.
    iNext. iExists (<[j := fill K (v1, #true)%V]> tp), (state_upd_heap <[l := Some v2]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame.
    iPureIntro.
    eapply rtc_r; first done.
    eapply base_step_insert_no_fork; eauto.
    by eapply (CmpXchgS l v1 v2 v1 σ true); last rewrite bool_decide_eq_true_2.
  Qed.

  Lemma step_faa E j K l e2 (m k : Z) :
    IntoVal e2 #k →
    ↑specN ⊆ E →
    spec_ctx -∗ j ⤇ fill K (FAA #l e2) -∗ l ↦ₛ #m
    ={E}=∗ j ⤇ fill K #m ∗ l ↦ₛ #(m + k).
  Proof.
    iIntros (<- ?) "#Hinv Hj Hl". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx tpool_pointsto_eq heapS_pointsto_eq.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hl" gives
      %[Hl%heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #m))). }
    iMod (own_update_2 with "Hheap Hl") as "[Hheap Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 (Some #(m + k)))); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iMod ("Hclose" with "[-]"); last done.
    iNext. iExists (<[j := fill K #m]> tp), (state_upd_heap <[l := Some #(m + k)]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_fork E j K e :
    ↑specN ⊆ E →
    spec_ctx -∗
    j ⤇ fill K (Fork e) ={E}=∗ ∃ j', j ⤇ fill K #() ∗ j' ⤇ e.
  Proof.
    iIntros (?) "#Hinv Hj". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite tpool_pointsto_eq /tpool_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    assert (j < length tp) by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update with "Htp") as "[Htp Hfork]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ (length tp) (Excl e)); last done.
      rewrite lookup_insert_ne ?tpool_lookup; last lia.
      by rewrite lookup_ge_None_2. }
    iExists (length tp). iFrame "Hj Hfork".
    iMod ("Hclose" with "[-]") as "_"; last done. iNext.
    iExists (<[j := fill K #()]> tp ++ [e]), σ.
    rewrite to_tpool_snoc length_insert to_tpool_insert //.
    iFrame. iPureIntro.
    eapply rtc_r, base_step_insert; eauto. econstructor; eauto.
  Qed.

  Lemma step_handle_os E j K K' hs (l : label) (e : expr) (v : val) (h ret : expr) :
    let C := match hs with Deep => HandleCtx hs OS l h ret :: K' | Shallow => K' end in
    IntoVal e v →
    ↑specN ⊆ E →
    l ∉ ectx_labels K' →
    spec_ctx -∗
    j ⤇ fill K (Handle hs OS (EffLabel l) (fill K' (Do (EffLabel l) e)) h ret) ={E}=∗ ∃ (r : loc),
    j ⤇ fill K (App (App h v) (ContV r C)) ∗ unshotₛ r.
  Proof.
    iIntros (? <- ? ?) "#Hinv Hj". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite tpool_pointsto_eq /tpool_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    set (r := Loc.fresh (dom (heap σ))).
    assert (heap σ !! r = None).
    { apply not_elem_of_dom. rewrite -(Loc.add_0 r). apply Loc.fresh_fresh. lia. }
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update, (exclusive_local_update _ (Excl (fill K _))). }
    iMod (own_update with "Hheap") as "[Hheap Hr]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ r (to_frac_agree 1 (Some #true))); last done.
      by apply lookup_to_heap_None. }
    iExists r. rewrite /unshotₛ heapS_pointsto_eq. iFrame "Hj Hr".
    iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K (App (App h v) (ContV r C))]> tp), (state_upd_heap <[r:=Some #true]>σ).
    iSplit; last first.
    { rewrite to_heap_insert to_tpool_insert' //. iFrame. }
    iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto.
    by apply base_step_handle_os_eff.
  Qed.

  Lemma step_cont E j K K' (e : expr) (v : val) (r : loc) :
    IntoVal e v →
    ↑specN ⊆ E →
    spec_ctx -∗
    unshotₛ r -∗
    j ⤇ fill K (App (ContV r K') e) ={E}=∗
    j ⤇ fill K (fill K' v).
  Proof.
    iIntros (<- ?) "#Hinv Hr Hj". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /unshotₛ /spec_ctx tpool_pointsto_eq /tpool_pointsto_def.
    rewrite heapS_pointsto_eq /heapS_pointsto_def.
    iInv specN as (tp σ) ">(%Hrtc & Htp & Hheap & Hlabels)" "Hclose".
    iCombine "Htp Hj" gives
      %[Htpj%tpool_singleton_included' _]%auth_both_valid_discrete.
    iCombine "Hheap Hr" gives
      %[?%heap_singleton_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Htp Hj") as "[Htp Hj]".
    { by eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K _))). }
    iMod (own_update_2 with "Hheap Hr") as "[Hheap _]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (to_frac_agree 1 (Some #false))); last done.
      by rewrite /to_heap lookup_fmap H1. }
    iFrame "Hj". iMod ("Hclose" with "[-]") as "_"; last done.
    iNext. iExists (<[j := fill K (fill K' v)]> tp), (state_upd_heap <[r := Some #false]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    eapply rtc_r, base_step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

End cfg.
