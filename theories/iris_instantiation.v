From iris.program_logic Require Import language.
From blaze Require Import syntax notation semantics tactics.


(* ========================================================================== *)
(** * Language. *)

(* Reduction relation in the Iris format. *)
(* To prove that [lambda_blaze] is a language, we must define a reduction
   relation that fits the format formalized by Iris. *)
Definition prim_step' e1 σ1 (obs : list unit) e2 σ2 (efs : list expr) :=
  match obs with _ :: _ => False | [] =>
    prim_step e1 σ1 e2 σ2 efs
  end.

(* [lambda_blaze] satisfies the record type [LanguageMixin]. *)
Lemma lambda_blaze_mixin : LanguageMixin of_val to_val prim_step'.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val.
  { intros ??. destruct e=>//=. by inversion 1. }
  unfold prim_step'.
  intros e σ obs e' σ' efs.
  case obs; [|done];
  induction 1 as [K e1' e2' -> ? ?].
  case K as [|f K].
  - revert H0. apply val_base_stuck.
  - apply fill_frame_val.
Qed.

(* [lambda_blaze] is a language in the Iris sense. *)
Canonical Structure lambda_blaze : language := Language lambda_blaze_mixin.


(* ========================================================================== *)
(** * Pure Steps. *)

Section pure_steps.

  Definition base_reducible (e : expr) (σ : state) :=
    ∃ e' σ' efs, base_step e σ e' σ' efs.
  Definition base_irreducible (e : expr) (σ : state) :=
    ∀ e' σ' efs, ¬base_step e σ e' σ' efs.
  Definition base_stuck (e : expr) (σ : state) :=
    to_val e = None ∧ base_irreducible e σ.

  Record pure_base_step (e1 e2 : expr) := {
    pure_base_step_safe σ1 : base_reducible e1 σ1;
    pure_base_step_det σ1 e2' σ2 efs :
      base_step e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma step_by_val_aux k1 k2 e1 e2 σ2 e3 σ3 efs :
    fill k1 e1 = fill k2 e2 →
    to_val e1 = None →
    to_eff e1 = None →
    base_step e2 σ2 e3 σ3 efs →
    ∃ k1', k2 = k1 ++ k1'.
  Proof.
    revert k2; induction k1 as [|f1 k1];
    intros k2 Hfill Hval Heff Hstep.
    - by exists k2.
    - case_eq k2; [|intros f2 k2']; intros Heq.
      + rewrite Heq in Hfill. simpl in *.
        rewrite -Hfill in Hstep.
        destruct f1=>//=; inv_base_step;
        try match goal with
        | Hnone : to_val ?e = None,
          Hfill : Val _ = fill ?k ?e |- _ =>
            by specialize (fill_not_val k1 _ Hnone); rewrite -Hfill
        end.
        * by rewrite (fill_not_eff k1 _ Hval Heff) in H10.
        * specialize (fill_not_eff k1 _ Hval Heff). by rewrite H11.
      + have Hval': to_val e2 = None.
        { case_eq (to_val e2); [|done]; intros v2 Heq'.
          rewrite (of_to_val _ _ Heq') in Hstep.
          by inversion Hstep.
        }
        rewrite Heq //= in Hfill.
        have H1: to_val (fill k1 e1) = None. { by apply fill_not_val. }
        have H2: to_val (fill k2' e2) = None. { by apply fill_not_val. }
        specialize (fill_frame_no_val_inj f1 f2 _ _ H1 H2 Hfill).
        intros ->.
        specialize (fill_frame_inj _ _ _ Hfill) as Heq'.
        destruct (IHk1 k2' Heq' Hval Heff Hstep) as [k1' ->].
        by exists k1'.
  Qed.

  Lemma step_by_val k1 k2 e1 e2 σ2 e3 σ3 efs :
    fill k1 e1 = fill k2 e2 →
    to_val e1 = None →
    not_eff e1 →
    base_step e2 σ2 e3 σ3 efs →
    ∃ k1', k2 = k1 ++ k1'.
  Proof.
    intros Hfill Hval [Heff|[l [v [k [Heff Hl]]]]].
    { by apply (step_by_val_aux k1 k2 e1 e2). }
    revert k2 Hfill Hval l v k Heff Hl.
    induction k1 as [|f1 k1];
    intros k2 Hfill Hval l v k Heff Hl Hstep; [by exists k2|].
    destruct k2 as [|f2 k2].
    - simpl in *. rewrite -Hfill in Hstep.
      destruct f1=>//=; inv_base_step;
      try match goal with
      | Hnone : to_val ?e = None,
        Hfill : Val _ = fill ?k ?e |- _ =>
          by specialize (fill_not_val k1 _ Hnone); rewrite -Hfill
      end.
      + rewrite (to_eff_fill l k1 k _ v Heff) in H10.
        injection H10 as -> -> <-. exfalso. apply H9.
        rewrite ectx_labels_app. set_solver.
      + specialize (to_eff_fill l k1 k _ v Heff). rewrite H11.
        injection 1 as -> -> ->.
        exfalso. apply H10.
        rewrite ectx_labels_app. set_solver.

    - have Hval': to_val e2 = None.
      { case_eq (to_val e2); [|done]; intros v2 Heq'.
        rewrite (of_to_val _ _ Heq') in Hstep.
        by inversion Hstep.
      }
      simpl in *.
      have He1: to_val (fill k1 e1) = None. { by apply fill_not_val. }
      have He2: to_val (fill k2 e2) = None. { by apply fill_not_val. }
      specialize (fill_frame_no_val_inj f1 f2 _ _ He1 He2 Hfill).
      intros ->.
      specialize (fill_frame_inj _ _ _ Hfill) as Heq'.
      destruct (IHk1 k2 Heq' Hval _ _ _ Heff Hl Hstep) as [k1' ->].
      by exists k1'.
  Qed.

  Lemma base_ctx_step_val k e σ1 e2 σ2 efs :
    base_step (fill k e) σ1 e2 σ2 efs →
    (* value: *) is_Some (to_val e) ∨
    (* unhandled effect: *) (∃ l v k', to_eff e = Some (l, v, k') ∧ l ∉ ectx_labels k') ∨
    k = [].
  Proof.
    revert e2; induction k as [|f k IH]; [by auto|]; intros e2 Hstep.
    simpl in *.
    destruct f=>//=; inv_base_step;
    try match goal with
        | Hfill : Val ?v = fill ?k ?e |- _ =>
            by left; edestruct (fill_val k e v) as [_ ->]; [rewrite -Hfill|]
        end.
    - case_eq (to_val e); [by eauto|]; intros Hval.
      destruct (to_eff e) as [((l', v'), k'')|] eqn:He.
      { rewrite (to_eff_fill l' _ k'' _ v') in H10; last done.
        injection H10 as -> -> <-. right; left.
        exists l, v, k''. split; [done|].
        rewrite ectx_labels_app in H9. set_solver.
      }
      by rewrite (fill_not_eff k e Hval He) in H10.
    - case_eq (to_val e); [by eauto|]; intros Hval.
      rename H11 into Heq.
      destruct (to_eff e) as [((l', v'), k'')|] eqn:He.
      { rewrite (to_eff_fill l' _ k'' _ v') in Heq; last done.
        injection Heq as -> -> <-. right; left.
        exists l, v, k''. split; [done|].
        rewrite ectx_labels_app in H10. set_solver.
      }
      by rewrite (fill_not_eff k e Hval He) in Heq.
  Qed.

  Lemma eff_not_prim_step l v k e2 σ1 σ2 efs :
    l ∉ ectx_labels k →
    ¬ prim_step (of_eff l v k) σ1 e2 σ2 efs.
  Proof.
    intros Hk Hstep.
    have Heff: is_Some (to_eff (do: l v)). { by rewrite to_eff_eff. }
    destruct (Ectx_prim_step_eff_inv l v [] k (do: l v)%E _ _ _ _ Hk eq_refl Hstep) as [? [Hstep' ?]].
    inversion Hstep'.
    destruct k0=>//=; simpl in H0, H1; simplify_eq.
    - by inversion H2.
    - destruct f=>//=. inversion H0.
      have Hval: to_val (fill k0 e1') = Some v. { by rewrite -H3. }
      destruct (fill_val k0 e1' v Hval) as [-> ->]. simplify_eq.
      by inversion H2.
  Qed.

  Lemma eff_irreducible l v k σ :
    l ∉ ectx_labels k →
    irreducible (of_eff l v k) σ.
  Proof.
    intros Hk. rewrite -not_reducible /reducible //=.
    intros (κ&e2&σ2&efs&Hstep'). revert Hstep'.
    case κ; last auto. simpl in *.
    by apply eff_not_prim_step.
  Qed.

  Lemma eff_irreducible' l v k e σ :
    l ∉ ectx_labels k → to_eff e = Some (l, v, k) → irreducible e σ.
  Proof.
    intros Hl He. rewrite -(of_to_eff _ _ _ _ He). by apply eff_irreducible.
  Qed.

  Lemma reducible_not_eff e σ :
    reducible e σ →
    to_eff e = None ∨ ∃ l v k, to_eff e = Some (l, v, k) ∧ l ∈ ectx_labels k.
  Proof.
    intros Hred.
    destruct (to_eff e) as [((l, v), k)|] eqn:He; last by left.
    case (decide (l ∈ ectx_labels k)).
    + right. by eauto.
    + intros Hnot_in. exfalso.
      cut (irreducible e σ). { rewrite -not_reducible. by auto. }
      by apply (eff_irreducible' l v k).
  Qed.

  Lemma base_reducible_reducible e σ :
    base_reducible e σ → reducible e σ.
  Proof. intros (e' & σ' & efs & Hstep). exists [], e', σ', efs. by apply base_prim_step. Qed.

  Lemma reducible_fill K e σ :
    reducible e σ → reducible (fill K e) σ.
  Proof.
    intros ([|??] & e' & σ' & efs & ?); last done.
    exists [], (fill K e'), σ', efs.
    by apply Ectx_prim_step'.
  Qed.

  Lemma reducible_fill_inv K e σ :
    to_val e = None →
    to_eff e = None →
    reducible (fill K e) σ → reducible e σ.
  Proof.
    intros ?? ([|??] & e' & σ' & efs & H); last done.
    apply Ectx_prim_step_inv in H as (e'' & Hstep & He'); [|done..].
    by exists [], e'', σ', efs.
  Qed.

  Lemma pure_step_fill_frame f e1 e2 :
    pure_step e1 e2 →
    pure_step (fill_frame f e1) (fill_frame f e2).
  Proof.
    intros [Hred Hstep]. split; simpl in *.
    - unfold reducible_no_obs in *. simpl in *.
      intros σ1. destruct (Hred σ1) as (e2'& σ2 & efs & Hstep').
      exists (fill_frame f e2'), σ2, efs.
      by apply Frame_prim_step'.
    - intros ????? Hstep'.
      destruct κ; [|done].
      simpl in *.
      have not_val: to_val e1 = None.
      { by apply (reducible_not_val _ σ1), reducible_no_obs_reducible. }
      have not_eff: to_eff e1 = None ∨ ∃ l v k, to_eff e1 = Some (l, v, k) ∧ l ∈ ectx_labels k.
      { by apply (reducible_not_eff _ σ1), reducible_no_obs_reducible. }
      destruct not_eff as [not_eff|[l [v [k [eff Hl]]]]].
      + destruct (Frame_prim_step_inv f _ _ _ _ _ not_val not_eff Hstep') as [e'' [He'' ->]].
        have Hprim_step': prim_step' e1 σ1 [] e'' σ2 efs; [done|].
        by destruct (Hstep σ1 [] e'' σ2 efs Hprim_step') as (_&->&->&->).
      + destruct (Frame_prim_step_eff_inv' _ _ _ _ _ _ _ _ _ Hl eff Hstep') as [e'' [He'' ->]].
        have Hprim_step': prim_step' e1 σ1 [] e'' σ2 efs; [done|].
        by destruct (Hstep σ1 [] e'' σ2 efs Hprim_step') as (_&->&->&->).
  Qed.

  Lemma pure_step_fill k e1 e2 :
    pure_step e1 e2 →
    pure_step (fill k e1) (fill k e2).
  Proof.
    induction k as [|f k]; [done|]; intros Hstep.
    by apply pure_step_fill_frame, IHk.
  Qed.

  Lemma pure_step_nsteps_fill k n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (fill k e1) (fill k e2).
  Proof. eauto using nsteps_congruence, pure_step_fill. Qed.

  Lemma rtc_pure_step_fill k e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (fill k e1) (fill k e2).
  Proof. eauto using rtc_congruence, pure_step_fill. Qed.

  Lemma pure_exec_fill k φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill k e1) (fill k e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_fill. Qed.

  Lemma pure_step_prim_step (e1 e2 : expr) :
    pure_step e1 e2 → ∀ σ, prim_step e1 σ e2 σ [].
  Proof.
    rename e2 into e3.
    intros [Hsafe Hdet] σ. simpl in *.
    destruct (Hsafe σ) as (e2&σ2&efs&Hstep). simpl in *.
    specialize (Hdet σ [] e2 σ2 efs). simpl in *.
    by destruct (Hdet Hstep) as (_&->&->&->).
  Qed.

  Lemma pure_exec_erased_step (e1 e2 : expr) σ φ n :
    φ →
    PureExec φ n e1 e2 →
    rtc erased_step ([e1], σ) ([e2], σ).
  Proof.
    revert e1 e2; induction n as [|n IH]; intros e1 e3.
    - intros Hφ Hpure. specialize (Hpure Hφ). by inversion Hpure.
    - intros Hφ Hpure. specialize (Hpure Hφ).
      destruct (nsteps_inv_r n _ _ Hpure) as [e2 [He12 He23]].
      transitivity ([e2], σ).
      + apply IH; [done|]. by intros ?.
      + apply rtc_once. exists [].
        apply (step_atomic e2 σ e3 σ [] [] []); try done. simpl.
        by apply pure_step_prim_step.
  Qed.

  Lemma pure_prim_stepI e1 e2 :
    (∀ σ, base_step e1 σ e2 σ []) →
    (∀ σ1 e2' σ2 efs, prim_step e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []) →
    pure_step e1 e2.
  Proof.
    intros Hbase_step Hstep_det. constructor; simpl.
    - intros σ1. unfold reducible_no_obs. exists e2, σ1, [].
      by apply base_prim_step, Hbase_step.
    - intros ????? Hprim_step. destruct κ=>//=.
      split; first done.
      by eapply Hstep_det.
  Qed.

  Lemma base_reducible_prim_step_ctx k e1 σ1 e2 σ2 efs :
    base_reducible e1 σ1 →
    prim_step (fill k e1) σ1 e2 σ2 efs →
    ∃ e2', e2 = fill k e2' ∧ base_step e1 σ1 e2' σ2 efs.
  Proof.
    intros (e2''&σ2''&efs''&Hstep_k) [k' e1' e2' Hk_e1 -> Hstep].
    edestruct (step_by_val k) as [k'' Heq].
    { by apply Hk_e1. }
    { eauto using val_base_stuck. }
    { apply (reducible_not_eff _ σ1).
      by exists [], e2'', σ2'', efs''; apply base_prim_step.
    }
    { by apply Hstep. }
    rewrite Heq fill_app in Hk_e1; simplify_eq.
    exists (fill k'' e2'). rewrite fill_app; split; first done.
    apply base_ctx_step_val in Hstep_k as [[v Heq]|[[l [v [k' [Heq Hnot_in]]]] | ->]];
    simplify_eq; last done.
    { by apply val_base_stuck in Hstep; simplify_eq. }
    { cut (reducible e1' σ1).
      - intros Hred. exfalso.
        destruct (reducible_not_eff e1' _ Hred) as [Heq'|[l' [v' [k''' [Heq' Hin]]]]];
        rewrite Heq' in Heq; first done.
        by injection Heq as -> -> ->.
      - by exists [], e2', σ2, efs; apply base_prim_step.
    }
  Qed.

  Lemma base_reducible_prim_step e1 σ1 e2 σ2 efs :
    base_reducible e1 σ1 →
    prim_step e1 σ1 e2 σ2 efs →
    base_step e1 σ1 e2 σ2 efs.
  Proof.
    intros.
    edestruct (base_reducible_prim_step_ctx []) as (?&?&?); eauto.
    by simplify_eq.
  Qed.

  Lemma pure_base_step_pure_step e1 e2 : pure_base_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & efs & Hbase_step).
      eexists e2', σ2, efs. by apply base_prim_step.
    - intros σ1 ? e2' σ2 ?.
      destruct κ=>//=.
      intros ?%base_reducible_prim_step; last eauto.
      by edestruct Hp2 as (-> & -> & ->); [apply H|].
  Qed.

  Definition base_atomic (a : atomicity) (e : expr) : Prop :=
    ∀ σ e' σ' efs,
    base_step e σ e' σ' efs →
    if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Definition sub_redexes_are_values (e : expr) :=
    ∀ k e', e = fill k e' → to_val e' = None → k = [].

  Lemma ectx_language_atomic a e :
    base_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' κ σ' efs. destruct κ=>//=.
    intros [k e1' e2' -> -> Hstep].
    assert (k = []) as ->.
    { by eauto 10 using val_base_stuck. }
    { simpl. simpl in *. by eapply Hatomic_step. }
  Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ f e', e = fill_frame f e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub k e' ->. destruct k as [|f k]; try done.
    intros []%eq_None_not_Some.
    destruct (Hsub f (fill k e')) as [v Heq]; first done.
    by destruct (fill_val _ _ _ Heq) as [-> ->].
  Qed.

End pure_steps.
