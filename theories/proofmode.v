From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import coq_tactics reduction.
From blaze Require Export logic class_instances tactics.
From iris.prelude Require Import options.

(** A special version of TCSimpl which also simplies [fill (K1 ++ K2) e] *)
Class TCSimplExpr (e e' : expr) := TCSimplExpr_TCSimpl : TCSimpl e e'.
Global Hint Extern 0 (TCSimplExpr _ _) =>
  repeat rewrite (fill_app _ _ _); notypeclasses refine TCSimpl_TCEq : typeclass_instances.
Global Hint Mode TCSimplExpr - - : typeclass_instances.

Lemma TCSimplExpr_eq (e e' : expr) : TCSimplExpr e e' ↔ e = e'.
Proof. apply TCSimpl_eq. Qed.

Inductive IntoCtx (e : expr) (P : expr → Prop) (k : ectx) : Prop :=
  Mk_IntoCtx (e' : expr) (_ : e = fill k e') (_ : P e').
Existing Class IntoCtx.
Global Hint Mode IntoCtx ! ! - : typeclass_instances.

Class DoPureStep (φ : Prop) (e e' : expr) : Prop :=
  { do_pure_step : φ → pure_step e e' }.
Global Hint Mode DoPureStep - ! - : typeclass_instances.

Class DoPureSteps (φ : Prop) (n : nat) (e e' : expr) : Prop :=
  { do_pure_steps : φ → nsteps pure_step n e e' }.
Global Hint Mode DoPureSteps - - ! - : typeclass_instances.

Inductive DoPureStepsIntoCtx (φ : Prop) (e : expr) (P : expr → Prop) (n : nat) (k : ectx) : Prop :=
  Mk_DoPureStepsIntoCtx (e'  : expr) (_ : DoPureSteps φ n e e') (_ : IntoCtx e' P k).
Existing Class DoPureStepsIntoCtx.
Global Hint Mode DoPureStepsIntoCtx - ! ! - - : typeclass_instances.

Class MakeAnd (P Q PQ : Prop) := make_and : P ∧ Q ↔ PQ.
Global Hint Mode MakeAnd ! ! - : typeclass_instances.

Global Instance make_and_true_l P : MakeAnd True P P.
Proof. rewrite /MakeAnd. tauto. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. rewrite /MakeAnd. tauto. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

(** [IntoCtx] instances *)
Global Instance into_ctx_nil e P :
  P e → IntoCtx e P [] | 0.
Proof. intros H. by exists e. Qed.

Local Ltac solve_into_ctx :=
  let e := fresh "e" in
  intros [e -> ?]; by exists e.

Global Instance into_ctx_app_r e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (App e1 e2) P (AppRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_app_l e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (App e1 (Val v2)) P (AppLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_unop op e P K :
  IntoCtx e P K →
  IntoCtx (UnOp op e) P (UnOpCtx op :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_binop_l op e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (BinOp op e1 (Val v2)) P (BinOpLCtx op v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_binop_r op e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (BinOp op e1 e2) P (BinOpRCtx op e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_if e1 e2 e3 P K :
  IntoCtx e1 P K →
  IntoCtx (If e1 e2 e3) P (IfCtx e2 e3 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_pairl e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (Pair e1 (Val v2)) P (PairLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_pairr e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (Pair e1 e2) P (PairRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_fst e P K :
  IntoCtx e P K →
  IntoCtx (Fst e) P (FstCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_snd e P K :
  IntoCtx e P K →
  IntoCtx (Snd e) P (SndCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_injl e P K :
  IntoCtx e P K →
  IntoCtx (InjL e) P (InjLCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_injr e P K :
  IntoCtx e P K →
  IntoCtx (InjR e) P (InjRCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_case e0 e1 e2 P K :
  IntoCtx e0 P K →
  IntoCtx (Case e0 e1 e2) P (CaseCtx e1 e2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_allocnl e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (AllocN e1 (Val v2)) P (AllocNLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_allocnr e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (AllocN e1 e2) P (AllocNRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_free e P K :
  IntoCtx e P K →
  IntoCtx (Free e) P (FreeCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_load e P K :
  IntoCtx e P K →
  IntoCtx (Load e) P (LoadCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_storel e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (Store e1 (Val v2)) P (StoreLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_storer e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (Store e1 e2) P (StoreRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_xchgl e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (Xchg e1 (Val v2)) P (XchgLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_xchgr e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (Xchg e1 e2) P (XchgRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_cmpxchgl e0 v1 v2 P K :
  IntoCtx e0 P K →
  IntoCtx (CmpXchg e0 (Val v1) (Val v2)) P (CmpXchgLCtx v1 v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_cmpxchgm e0 e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (CmpXchg e0 e1 (Val v2)) P (CmpXchgMCtx e0 v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_cmpxchgr e0 e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (CmpXchg e0 e1 e2) P (CmpXchgRCtx e0 e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_faal e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (FAA e1 (Val v2)) P (FaaLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_faar e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (FAA e1 e2) P (FaaRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_do e l P K :
  IntoCtx e P K →
  IntoCtx (Do (EffLabel l) e) P (DoCtx l :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_handle_ctx hs m e1 e2 e3 l P K :
  IntoCtx e1 P K →
  IntoCtx (Handle hs m (EffLabel l) e1 e2 e3) P (HandleCtx hs m l e2 e3 :: K).
Proof. solve_into_ctx. Qed.

Class MakeApp {A} (k1 k2 l : list A) := make_app : l = k1 ++ k2.
Global Hint Mode MakeApp ! ! ! - : typeclass_instances.

Global Instance make_app_nil_l {A} (l : list A) : MakeApp [] l l.
Proof. by rewrite /MakeApp. Qed.
Global Instance make_app_nil_r {A} (l : list A) : MakeApp l [] l.
Proof. by rewrite /MakeApp app_nil_r. Qed.
Global Instance make_app_default {A} (l1 l2 : list A) : MakeApp l1 l2 (l1 ++ l2) | 100.
Proof. by rewrite /MakeApp. Qed.

Lemma into_ctx_fill e K1 K2 K P :
  IntoCtx e P K2 →
  MakeApp K1 K2 K →
  IntoCtx (fill K1 e) P K.
Proof. intros [? -> ?] ->. exists e'; auto using fill_app. Qed.
Global Hint Extern 10 (IntoCtx (fill _ _) _ _) =>
  notypeclasses refine (into_ctx_fill _ _ _ _ _ _ _) : typeclass_instances.

Lemma tc_eq_fill K e1 e2 :
  IntoCtx e2 (TCEq e1) K →
  TCEq (fill K e1) e2.
Proof. by intros [? -> ->]. Qed.
Global Hint Extern 10 (TCEq (fill _ _) _) =>
  notypeclasses refine (tc_eq_fill _ _ _ _) : typeclass_instances.

(** [PureStep] instances *)
Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
Local Ltac solve_do_pure_step_with tac :=
  constructor; tac; apply pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].
Local Ltac solve_do_pure_step := solve_do_pure_step_with ltac:(intros _).

Global Instance do_pure_step_rec f x e :
  DoPureStep True (Rec f x e) (Val (RecV f x e)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_pair v1 v2 :
  DoPureStep True (Pair (Val v1) (Val v2)) (PairV v1 v2).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_injl v :
  DoPureStep True (InjL (Val v)) (InjLV v).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_injr v :
  DoPureStep True (InjR (Val v)) (InjRV v).
Proof. solve_do_pure_step. Qed.

(** [do_pure_step_app] is not an [Instance], but a [Hint Extern] to enable
syntactic matching instead of unification-based matching. This is important
because it would otherwise unfold definitions. For example, when considering
[wp (swap ...) Φ] where [Definition swap := RecV ...], it should *not* unfold
[swap] to as to preserve abstraction barriers. *)
Lemma do_pure_step_app f x e v e' :
  TCSimpl (val_subst' x v (val_subst' f (RecV f x e) e)) e' →
  DoPureStep True (App (Val (RecV f x e)) (Val v)) e'.
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.
Global Hint Extern 1 (DoPureStep _ (App (Val (RecV _ _ _)) (Val _)) _) =>
  notypeclasses refine (do_pure_step_app _ _ _ _ _ _) : typeclass_instances.

Global Instance do_pure_step_unop op v w :
  TCSimpl (un_op_eval op v) (Some w) →
  DoPureStep True (UnOp op (Val v)) (Val w).
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.

Global Instance do_pure_step_binop op v1 v2 w :
  TCSimpl (bin_op_eval op v1 v2) (Some w) →
  DoPureStep True (BinOp op (Val v1) (Val v2)) (Val w).
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.

Global Hint Extern 1 (TCSimpl (un_op_eval ?op ?v) _) =>
  lazymatch goal with
  | H : un_op_eval op v = _ |- _ => rewrite H
  end : typeclass_instances.

Global Hint Extern 1 (TCSimpl (bin_op_eval ?op ?v1 ?v2) _) =>
  lazymatch goal with
  | H : bin_op_eval op v1 v2 = _ |- _ => rewrite H
  end : typeclass_instances.

Global Instance do_pure_step_if_true e2 e3 :
  DoPureStep True (If (Val $ LitV $ LitBool true) e2 e3) e2.
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_if_false e2 e3 :
  DoPureStep True (If (Val $ LitV $ LitBool false) e2 e3) e3.
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_fst v1 v2 :
  DoPureStep True (Fst (PairV v1 v2)) (Val v1).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_snd v1 v2 :
  DoPureStep True (Snd (PairV v1 v2)) (Val v2).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_case_injl v1 e2 e3 :
  DoPureStep True (Case (InjLV v1) e2 e3) (App e2 (Val v1)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_case_injr v1 e2 e3 :
  DoPureStep True (Case (InjRV v1) e2 e3) (App e3 (Val v1)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_kont k v :
  DoPureStep True (App (Val $ KontV k) (Val v)) (fill k (Val v)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_handle_ms_eff hs l k e v h r :
  let k' :=
    match hs with Deep => HandleCtx hs MS l h r :: k | Shallow => k end
  in
  IntoCtx e (TCEq (Do (EffLabel l) (Val v))) k →
  DoPureStep (l ∉ ectx_labels k)
    (Handle hs MS (EffLabel l) e h r)
    (App (App h (Val v)) (Val $ KontV k')).
Proof.
  intros ? [? -> <-]. unfold k'.
  constructor. intros Hneutral. apply pure_base_step_pure_step. constructor.
  - intros. do 3 eexists. by apply HandleMSEffS, to_of_eff.
  - intros. inv_base_step.
    + rewrite to_of_eff in H10. by inversion H10.
    + specialize (fill_not_val k (do: l v) eq_refl). by rewrite -H4.
Qed.

Global Instance do_pure_step_handle_ret hs m l v h r :
  DoPureStep True (Handle hs m (EffLabel l) (Val v) h r) (App r (Val v)).
Proof.
  constructor. intros _.
  apply pure_base_step_pure_step; constructor.
  - intros; subst. do 3 eexists. by apply HandleRetS.
  - intros; subst. by inv_base_step.
Qed.

Global Instance do_pure_steps_0 e : DoPureSteps True 0 e e | 100.
Proof. do 2 constructor. Qed.

Global Instance do_pure_steps_S n K e1 e2 e2' e3 φ1 φ2 φ :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep φ1 e1' e2') K) →
  TCSimplExpr (fill K e2') e2 →
  DoPureSteps φ2 n e2 e3 →
  MakeAnd φ1 φ2 φ →
  DoPureSteps φ (S n) e1 e3.
Proof.
  intros [[? -> [?]]] <-%TCSimplExpr_eq [?] Hφ.
  split. intros [Hφ1 Hφ2]%Hφ. econstructor; last auto.
  apply pure_step_fill; auto.
Qed.

Global Instance do_pure_steps_into_ctx_0 e P K :
  IntoCtx e P K → DoPureStepsIntoCtx True e P 0 K | 0.
Proof. exists e; apply _. Qed.

Global Instance do_pure_steps_into_ctx_S e1 e2 e2' P n K K' φ1 φ2 φ :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep φ1 e1' e2') K') →
  TCSimplExpr (fill K' e2') e2 →
  DoPureStepsIntoCtx φ2 e2 P n K →
  MakeAnd φ1 φ2 φ →
  DoPureStepsIntoCtx φ e1 P (S n) K | 100.
Proof.
  intros [[e1' -> [?]]] <-%TCSimplExpr_eq [e3 [?] ?] Hφ.
  exists e3; last done. split. intros [Hφ1 Hφ2]%Hφ.
  econstructor; last auto. apply pure_step_fill; auto.
Qed.

Class FinalizeBEWP `{!blazeGS Σ} (e1 e2 : expr) (L : iLblThy Σ) (R : val -d> val -d> iProp Σ) (P : iProp Σ) : Prop :=
  { finalize_bewp : P ⊢ BEWP e1 ≤ e2 <|L|> {{R}} }.
Global Hint Mode FinalizeBEWP + + ! + ! ! - : typeclass_instances.

(** There are three ways to finalize a SIM.
    First of all, if both expressions are a value
    and the postcondition already contains a update,
    we can just prove the postcondition. *)
Lemma finalize_bewp_value `{!blazeGS Σ} L R e1 e2 v1 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 →
  FinalizeBEWP e1 e2 L R (R v1 v2).
Proof. intros <- <-. constructor. apply bewp_value. Qed.
Global Hint Extern 0 (FinalizeBEWP _ _ _ (λ _ _, |==> _)%I _) =>
  notypeclasses refine (finalize_bewp_value _ _ _ _ _ _ _ _) : typeclass_instances.

(** Second, if both expressions are a value
    but the postcondition does NOT already contain an update,
    we introduce it. *)
Global Instance finalize_bewp_value_upd `{!blazeGS Σ} L R e1 e2 v1 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 →
  FinalizeBEWP e1 e2 L R (|==> R v1 v2) | 1.
Proof. intros <- <-. constructor. rewrite -fupd_bewp -bewp_value. by iIntros "?". Qed.

(** Finally, if the expressions aren't both a value,
    we simplify them both. *)
Global Instance finalize_bewp_simpl `{!blazeGS Σ} L R e1 e2 e1' e2' :
  TCSimplExpr e1 e1' → TCSimplExpr e2 e2' →
  FinalizeBEWP e1 e2 L R (bewp e1' e2' L R) | 2.
Proof. intros ->%TCSimplExpr_eq ->%TCSimplExpr_eq. by constructor. Qed.

(** [NormalizeBEWP] transforms a goal [P] into another goal of the form [bewp (fill K1 e1) (fill K2 e2) L R]
    by performing pure steps. This typeclass is used by [iApply]/[iAssumption] to first perform
    some pure steps, and automatically pick to right evaluation context to apply the lemma.

    Note that [normalize_bewp_step] only performs pure steps without side-conditions,
    so in some situations it's still needed to first perform the pure steps using [bewp_pures]. *)
Class NormalizeBEWP `{!blazeGS Σ} (P : iProp Σ) (K1 K2 : ectx) (e1 e2 : expr) (L : iLblThy Σ) (R : val -d> val -d> iProp Σ) :=
  { normalize_bewp : BEWP fill K1 e1 ≤ fill K2 e2 <|L|> {{R}} ⊢ P }.
Global Hint Mode NormalizeBEWP + + ! - - - - - - : typeclass_instances.

Global Instance normalize_bewp_here `{!blazeGS Σ} e1 e2 L R :
  NormalizeBEWP (bewp e1 e2 L R) [] [] e1 e2 L R | 0.
Proof. by split. Qed.

Global Instance normalize_bewp_value `{!blazeGS Σ} v1 v2 K1 K2 e1 e2 e1' e2' L R R' :
  IntoVal e1' v1 → IntoVal e2' v2 →
  NormalizeBEWP (R v1 v2) K1 K2 e1 e2 L R' →
  NormalizeBEWP (bewp e1' e2' L R) K1 K2 e1 e2 L R' | 1.
Proof.
  intros Hₜ Hₛ [HR]. split. by rewrite HR -Hₜ -Hₛ -bewp_value.
Qed.

(** We only perform pure steps without a side-condition here. We could let [NormalizeBEWP]
    also generate side-conditions, but [IntoWand]/[FromAssumption] currently lack the ability
    to handle pure side-conditions. *)
Global Instance normalize_bewp_step `{!blazeGS Σ} n1 n2 e1 e1' e2 e2' K1 K2 L R :
  DoPureStepsIntoCtx True e1 (TCEq e1') n1 K1 →
  DoPureStepsIntoCtx True e2 (TCEq e2') n2 K2 →
  NormalizeBEWP (bewp e1 e2 L R) K1 K2 e1' e2' L R | 10.
Proof.
  intros [? H1 [? -> <-]] [? H2 [? -> <-]]. split.
  assert (PureExec True n1 e1 (fill K1 e1')).
  { intros _. by apply H1. }
  assert (PureExec True n2 e2 (fill K2 e2')).
  { intros _. by apply H2. }
  rewrite -bewp_pure_step_later // -bewp_pure_step_r //.
  rewrite -bi.laterN_intro. apply bi.wand_intro_r, bi.sep_elim_l. tc_solve.
Qed.

Global Instance from_assumption_bewp `{!blazeGS Σ} p K1 K2 e1 e2 e1' e2' L R R' :
  NormalizeBEWP (bewp e1 e2 L R) K1 K2 e1' e2' L R' →
  FromAssumption p (bewp (fill K1 e1') (fill K2 e2') L R') (bewp e1 e2 L R) | 2.
Proof.
  intros [HR].
  rewrite /FromAssumption bi.intuitionistically_if_elim. by rewrite HR.
Qed.

Global Instance into_wand_bewp `{!blazeGS Σ} p e1 e2 K1 K2 e1' e2' L R R' S Q :
  NormalizeBEWP (bewp e1 e2 L R) K1 K2 e1' e2' L R' →
  TCSimpl (□ (∀ v1 v2, S v1 v2 -∗ R' v1 v2))%I Q →
  IntoWand p false (bewp (fill K1 e1') (fill K2 e2') L S) Q (bewp e1 e2 L R) | 1.
Proof.
  intros [Hbewp] <-%TCSimpl_eq.
  rewrite /IntoWand /= bi.intuitionistically_if_elim.
  rewrite -Hbewp. iIntros "H ?".
  by iApply (bewp_wand with "H").
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/458 *)
Global Instance into_wand_wand_bewp `{!blazeGS Σ} p q e1 e2 K1 K2 e1' e2' P P' Q L R R' :
  NormalizeBEWP (bewp e1 e2 L R) K1 K2 e1' e2' L R' →
  FromAssumption q P P' →
  TCSimpl P Q →
  IntoWand p q (P' -∗ BEWP fill K1 e1' ≤ fill K2 e2' <|L|> {{R'}}) Q (bewp e1 e2 L R).
Proof.
  rewrite /FromAssumption /IntoWand.
  intros [Hbewp] ? <-%TCSimpl_eq.
  rewrite bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by rewrite Hbewp.
Qed.

Class IsAppRec (v1 v2 : val) (f x : binder) (e' : expr) (e : expr) := {
  is_app_rec_val : v1 = RecV f x e';
  is_app_rec_expr : e = App (Val v1) (Val v2);
}.
Global Hint Mode IsAppRec - - - - - ! : typeclass_instances.
Global Instance is_app_rec v1 v2 f x e :
  TCEq v1 (RecV f x e) →
  IsAppRec v1 v2 f x e (App (Val v1) (Val v2)).
Proof. rewrite TCEq_eq=> ->. by constructor. Qed.

Section bewp_lemmas.
  Context `{!blazeGS Σ}.

  Lemma tac_bewp_pure_l {Δ Δ' eₜ eₜ' eₛ L R Q φ} n :
    DoPureSteps φ n eₜ eₜ' →
    φ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    FinalizeBEWP eₜ' eₛ L R Q →
    envs_entails Δ' Q →
    envs_entails Δ (bewp eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[Hsteps] Hφ HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ {HQ HΔ HΔ'}.
    assert (PureExec φ n eₜ eₜ') by by rewrite /PureExec.
    rewrite -bewp_pure_step_later //.
    apply bi.laterN_mono. auto.
  Qed.

  Lemma tac_bewp_pure_r {Δ eₜ eₛ eₛ' L R Q φ} n :
    DoPureSteps φ n eₛ eₛ' →
    φ →
    FinalizeBEWP eₜ eₛ' L R Q →
    envs_entails Δ Q →
    envs_entails Δ (bewp eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[Hsteps] Hφ [HQ] HΔ.
    rewrite HΔ HQ.
    assert (PureExec φ n eₛ eₛ') by by rewrite /PureExec.
    by apply: bewp_pure_step_r.
  Qed.

  Lemma tac_bewp_rec_l {Δ Δ' eₜ eₜ' v1 v2 f x eₛ K L R Q} :
    IntoCtx eₜ (IsAppRec v1 v2 f x eₜ') K →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    FinalizeBEWP (fill K (val_subst' x v2 (val_subst' f v1 eₜ'))) eₛ L R Q →
    envs_entails Δ' Q →
    envs_entails Δ (bewp eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[? -> [-> ->]] HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ /=.
    assert (PureExec True 1 (fill K ((rec: f x := eₜ')%V v2)) (fill K (val_subst' x v2 (val_subst' f (rec: f x := eₜ') eₜ')))).
    { apply pure_exec_fill. apply _. }
    rewrite -bewp_pure_step_later //.
    apply bi.later_mono. auto.
  Qed.

  Lemma tac_bewp_rec_r {Δ eₜ v1 v2 f x eₛ eₛ' K L R Q} :
    IntoCtx eₛ (IsAppRec v1 v2 f x eₛ') K →
    FinalizeBEWP eₜ (fill K (val_subst' x v2 (val_subst' f v1 eₛ'))) L R Q →
    envs_entails Δ Q →
    envs_entails Δ (bewp eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[? -> [-> ->]] [HQ] HΔ.
    rewrite HΔ HQ /=.
    assert (PureExec True 1 (fill K ((rec: f x := eₛ')%V v2)) (fill K (val_subst' x v2 (val_subst' f (rec: f x := eₛ') eₛ')))).
    { apply pure_exec_fill. apply _. }
    by eapply bewp_pure_step_r.
  Qed.
End bewp_lemmas.

Tactic Notation "bewp_pures_l" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (bewp _ _ _ _) =>
    notypeclasses refine (tac_bewp_pure_l n _ _ _ _ _);
      [ tc_solve || fail 1 "bewp_pures_l: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* into later *)
      | tc_solve (* simpl *)
      | pm_prettify ]
  | |- _ => fail "bewp_pures_l: goal not a `bewp`"
  end.
Tactic Notation "bewp_pure_l" := bewp_pures_l 1.
Tactic Notation "bewp_pures_l" := bewp_pures_l (S _).

Tactic Notation "bewp_pures_r" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (bewp _ _ _ _) =>
    notypeclasses refine (tac_bewp_pure_r n _ _ _ _);
      [ tc_solve || fail 1 "bewp_pures_r: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail "bewp_pures_r: goal not a `bewp`"
  end.
Tactic Notation "bewp_pure_r" := bewp_pures_r 1.
Tactic Notation "bewp_pures_r" := bewp_pures_r (S _).

Tactic Notation "bewp_rec_l" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (bewp _ _ _ _) =>
    notypeclasses refine (tac_bewp_rec_l _ _ _ _);
      [ tc_solve || fail 1 "bewp_rec_l: no beta reduction step can be performed"
      | tc_solve (* into laters *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "bewp_rec_l: goal not a `bewp`"
  end.

Tactic Notation "bewp_rec_r" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (bewp _ _ _ _) =>
    notypeclasses refine (tac_bewp_rec_r _ _ _);
      [ tc_solve || fail 1 "bewp_rec_r: no beta reduction step can be performed"
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "bewp_rec_r: goal not a `bewp`"
  end.

Class FinalizeEWP `{!blazeGS Σ} (e1 e2 : expr) (X : iThy Σ) (R : val -d> val -d> iProp Σ) (P : iProp Σ) : Prop :=
  { finalize_ewp : P ⊢ EWP e1 ≤ e2 <|X|> {{R}} }.
Global Hint Mode FinalizeEWP + + ! + ! ! - : typeclass_instances.

(** There are three ways to finalize a SIM.
    First of all, if both expressions are a value
    and the postcondition already contains a update,
    we can just prove the postcondition. *)
Lemma finalize_ewp_value `{!blazeGS Σ} X R e1 e2 v1 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 →
  FinalizeEWP e1 e2 X R (R v1 v2).
Proof. intros <- <-. constructor. iApply ewp_value. Qed.
Global Hint Extern 0 (FinalizeEWP _ _ _ (λ _ _, |==> _)%I _) =>
  notypeclasses refine (finalize_ewp_value _ _ _ _ _ _ _ _) : typeclass_instances.

(** Second, if both expressions are a value
    but the postcondition does NOT already contain an update,
    we introduce it. *)
Global Instance finalize_ewp_value_upd `{!blazeGS Σ} X R e1 e2 v1 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 →
  FinalizeEWP e1 e2 X R (|==> R v1 v2) | 1.
Proof. intros <- <-. constructor. rewrite -fupd_ewp -ewp_value. by iIntros "?". Qed.

(** Finally, if the expressions aren't both a value,
    we simplify them both. *)
Global Instance finalize_ewp_simpl `{!blazeGS Σ} X R e1 e2 e1' e2' :
  TCSimplExpr e1 e1' → TCSimplExpr e2 e2' →
  FinalizeEWP e1 e2 X R (ewp ⊤ e1' e2' X R) | 2.
Proof. intros ->%TCSimplExpr_eq ->%TCSimplExpr_eq. by constructor. Qed.

(** [NormalizeEWP] transforms a goal [P] into another goal of the form [ewp (fill K1 e1) (fill K2 e2) X R]
    by performing pure steps. This typeclass is used by [iApply]/[iAssumption] to first perform
    some pure steps, and automatically pick to right evaluation context to apply the lemma.

    Note that [normalize_ewp_step] only performs pure steps without side-conditions,
    so in some situations it's still needed to first perform the pure steps using [ewp_pures]. *)
Class NormalizeEWP `{!blazeGS Σ} (P : iProp Σ) (K1 K2 : ectx) (e1 e2 : expr) (X : iThy Σ) (R : val -d> val -d> iProp Σ) :=
  { normalize_ewp : EWP fill K1 e1 ≤ fill K2 e2 <|X|> {{R}} ⊢ P }.
Global Hint Mode NormalizeEWP + + ! - - - - - - : typeclass_instances.

Global Instance normalize_ewp_here `{!blazeGS Σ} e1 e2 X R :
  NormalizeEWP (ewp ⊤ e1 e2 X R) [] [] e1 e2 X R | 0.
Proof. by split. Qed.

Global Instance normalize_ewp_value `{!blazeGS Σ} v1 v2 K1 K2 e1 e2 e1' e2' X R R' :
  IntoVal e1' v1 → IntoVal e2' v2 →
  NormalizeEWP (R v1 v2) K1 K2 e1 e2 X R' →
  NormalizeEWP (ewp ⊤ e1' e2' X R) K1 K2 e1 e2 X R' | 1.
Proof.
  intros Hₜ Hₛ [HR]. split. by rewrite HR -Hₜ -Hₛ -ewp_value.
Qed.

(** We only perform pure steps without a side-condition here. We could let [NormalizeEWP]
    also generate side-conditions, but [IntoWand]/[FromAssumption] currently lack the ability
    to handle pure side-conditions. *)
Global Instance normalize_ewp_step `{!blazeGS Σ} n1 n2 e1 e1' e2 e2' K1 K2 X R :
  DoPureStepsIntoCtx True e1 (TCEq e1') n1 K1 →
  DoPureStepsIntoCtx True e2 (TCEq e2') n2 K2 →
  NormalizeEWP (ewp ⊤ e1 e2 X R) K1 K2 e1' e2' X R | 10.
Proof.
  intros [? H1 [? -> <-]] [? H2 [? -> <-]]. split.
  assert (PureExec True n1 e1 (fill K1 e1')).
  { intros _. by apply H1. }
  assert (PureExec True n2 e2 (fill K2 e2')).
  { intros _. by apply H2. }
  rewrite -ewp_pure_step_l' // -ewp_pure_step_r' //.
  rewrite -bi.laterN_intro. apply bi.wand_intro_r, bi.sep_elim_l. tc_solve.
Qed.

Global Instance from_assumption_ewp `{!blazeGS Σ} p K1 K2 e1 e2 e1' e2' X R R' :
  NormalizeEWP (ewp ⊤ e1 e2 X R) K1 K2 e1' e2' X R' →
  FromAssumption p (ewp ⊤ (fill K1 e1') (fill K2 e2') X R') (ewp ⊤ e1 e2 X R) | 2.
Proof.
  intros [HR].
  rewrite /FromAssumption bi.intuitionistically_if_elim. by rewrite HR.
Qed.

Global Instance into_wand_ewp `{!blazeGS Σ} p e1 e2 K1 K2 e1' e2' X R R' S Q :
  NormalizeEWP (ewp ⊤ e1 e2 X R) K1 K2 e1' e2' X R' →
  TCSimpl (□ (∀ v1 v2, S v1 v2 -∗ R' v1 v2))%I Q →
  IntoWand p false (ewp ⊤ (fill K1 e1') (fill K2 e2') X S) Q (ewp ⊤ e1 e2 X R) | 1.
Proof.
  intros [Hewp] <-%TCSimpl_eq.
  rewrite /IntoWand /= bi.intuitionistically_if_elim.
  rewrite -Hewp. iIntros "H ?".
  by iApply (ewp_wand with "H").
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/458 *)
Global Instance into_wand_wand_ewp `{!blazeGS Σ} p q e1 e2 K1 K2 e1' e2' P P' Q X R R' :
  NormalizeEWP (ewp ⊤ e1 e2 X R) K1 K2 e1' e2' X R' →
  FromAssumption q P P' →
  TCSimpl P Q →
  IntoWand p q (P' -∗ EWP fill K1 e1' ≤ fill K2 e2' <|X|> {{R'}}) Q (ewp ⊤ e1 e2 X R).
Proof.
  rewrite /FromAssumption /IntoWand.
  intros [Hewp] ? <-%TCSimpl_eq.
  rewrite bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by rewrite Hewp.
Qed.


Section ewp_lemmas.
  Context `{!blazeGS Σ}.

  Lemma tac_ewp_pure_l {Δ Δ' eₜ eₜ' eₛ X R Q φ} n :
    DoPureSteps φ n eₜ eₜ' →
    φ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    FinalizeEWP eₜ' eₛ X R Q →
    envs_entails Δ' Q →
    envs_entails Δ (ewp ⊤ eₜ eₛ X R).
  Proof.
    rewrite envs_entails_unseal=> -[Hsteps] Hφ HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ {HQ HΔ HΔ'}.
    assert (PureExec φ n eₜ eₜ') by by rewrite /PureExec.
    rewrite -ewp_pure_step_l' //.
    apply bi.laterN_mono. auto.
  Qed.

  Lemma tac_ewp_pure_r {Δ eₜ eₛ eₛ' X R Q φ} n :
    DoPureSteps φ n eₛ eₛ' →
    φ →
    FinalizeEWP eₜ eₛ' X R Q →
    envs_entails Δ Q →
    envs_entails Δ (ewp ⊤ eₜ eₛ X R).
  Proof.
    rewrite envs_entails_unseal=> -[Hsteps] Hφ [HQ] HΔ.
    rewrite HΔ HQ.
    assert (PureExec φ n eₛ eₛ') by by rewrite /PureExec.
    by apply: ewp_pure_step_r'.
  Qed.

  Lemma tac_ewp_rec_l {Δ Δ' eₜ eₜ' v1 v2 f x eₛ K L R Q} :
    IntoCtx eₜ (IsAppRec v1 v2 f x eₜ') K →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    FinalizeEWP (fill K (val_subst' x v2 (val_subst' f v1 eₜ'))) eₛ L R Q →
    envs_entails Δ' Q →
    envs_entails Δ (ewp ⊤ eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[? -> [-> ->]] HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ /=.
    assert (PureExec True 1 (fill K ((rec: f x := eₜ')%V v2)) (fill K (val_subst' x v2 (val_subst' f (rec: f x := eₜ') eₜ')))).
    { apply pure_exec_fill. apply _. }
    rewrite -ewp_pure_step_l' //.
    apply bi.later_mono. auto.
  Qed.

  Lemma tac_ewp_rec_r {Δ eₜ v1 v2 f x eₛ eₛ' K L R Q} :
    IntoCtx eₛ (IsAppRec v1 v2 f x eₛ') K →
    FinalizeEWP eₜ (fill K (val_subst' x v2 (val_subst' f v1 eₛ'))) L R Q →
    envs_entails Δ Q →
    envs_entails Δ (ewp ⊤ eₜ eₛ L R).
  Proof.
    rewrite envs_entails_unseal=> -[? -> [-> ->]] [HQ] HΔ.
    rewrite HΔ HQ /=.
    assert (PureExec True 1 (fill K ((rec: f x := eₛ')%V v2)) (fill K (val_subst' x v2 (val_subst' f (rec: f x := eₛ') eₛ')))).
    { apply pure_exec_fill. apply _. }
    by eapply ewp_pure_step_r'.
  Qed.
End ewp_lemmas.

Tactic Notation "ewp_pures_l" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (ewp _ _ _ _ _) =>
    notypeclasses refine (tac_ewp_pure_l n _ _ _ _ _);
      [ tc_solve || fail 1 "ewp_pures_l: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* into later *)
      | tc_solve (* simpl *)
      | pm_prettify ]
  | |- _ => fail "ewp_pures_l: goal not a `ewp`"
  end.
Tactic Notation "ewp_pure_l" := ewp_pures_l 1.
Tactic Notation "ewp_pures_l" := ewp_pures_l (S _).

Tactic Notation "ewp_pures_r" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (ewp _ _ _ _ _) =>
    notypeclasses refine (tac_ewp_pure_r n _ _ _ _);
      [ tc_solve || fail 1 "ewp_pures_r: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail "ewp_pures_r: goal not a `ewp`"
  end.
Tactic Notation "ewp_pure_r" := ewp_pures_r 1.
Tactic Notation "ewp_pures_r" := ewp_pures_r (S _).

Tactic Notation "ewp_rec_l" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (ewp _ _ _ _ _) =>
    notypeclasses refine (tac_ewp_rec_l _ _ _ _);
      [ tc_solve || fail 1 "ewp_rec_l: no beta reduction step can be performed"
      | tc_solve (* into laters *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "ewp_rec_l: goal not a `ewp`"
  end.

Tactic Notation "ewp_rec_r" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (ewp _ _ _ _ _) =>
    notypeclasses refine (tac_ewp_rec_r _ _ _);
      [ tc_solve || fail 1 "ewp_rec_r: no beta reduction step can be performed"
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "ewp_rec_r: goal not a `ewp`"
  end.

Class FinalizeWP `{!blazeGS Σ} (e : expr) (R : val -d> iProp Σ) (P : iProp Σ) : Prop :=
  { finalize_wp : P ⊢ WP e {{R}} }.
Global Hint Mode FinalizeWP + + ! ! - : typeclass_instances.

(** There are three ways to finalize a SIM.
    First of all, if both expressions are a value
    and the postcondition already contains a update,
    we can just prove the postcondition. *)
Lemma finalize_wp_value `{!blazeGS Σ} R e v :
  IntoVal e v →
  FinalizeWP e R (R v).
Proof. intros <-. constructor. iApply wp_value. Qed.
Global Hint Extern 0 (FinalizeWP _ _ _ (λ _ _, |==> _)%I _) =>
  notypeclasses refine (finalize_wp_value _ _ _ _ _ _ _ _) : typeclass_instances.

(** Second, if both expressions are a value
    but the postcondition does NOT already contain an update,
    we introduce it. *)
Global Instance finalize_wp_value_upd `{!blazeGS Σ} R e v :
  IntoVal e v →
  FinalizeWP e R (|==> R v) | 1.
Proof. intros <-. constructor. rewrite -fupd_wp -wp_value. by iIntros "?". Qed.

(** Finally, if the expressions aren't both a value,
    we simplify them both. *)
Global Instance finalize_wp_simpl `{!blazeGS Σ} R e e' :
  TCSimplExpr e e' → FinalizeWP e R (WP e' {{R}})%I | 2.
Proof. intros ->%TCSimplExpr_eq. by constructor. Qed.

(** [NormalizeWP] transforms a goal [P] into another goal of the form [wp (fill K1 e1) (fill K2 e2) X R]
    by performing pure steps. This typeclass is used by [iApply]/[iAssumption] to first perform
    some pure steps, and automatically pick to right evaluation context to apply the lemma.

    Note that [normalize_wp_step] only performs pure steps without side-conditions,
    so in some situations it's still needed to first perform the pure steps using [wp_pures]. *)
Class NormalizeWP `{!blazeGS Σ} (P : iProp Σ) (K : ectx) (e : expr) (R : val -d> iProp Σ) :=
  { normalize_wp : WP fill K e {{R}} ⊢ P }.
Global Hint Mode NormalizeWP + + ! - - - : typeclass_instances.

Global Instance normalize_wp_here `{!blazeGS Σ} e R :
  NormalizeWP (WP e {{R}})%I [] e R | 0.
Proof. by split. Qed.

Global Instance normalize_wp_value `{!blazeGS Σ} v K e e' R R' :
  IntoVal e' v →
  NormalizeWP (R v) K e R' →
  NormalizeWP (WP e' {{R}})%I K e R' | 1.
Proof.
  intros Hₜ [HR]. split. by rewrite HR -Hₜ  -wp_value.
Qed.

(** We only perform pure steps without a side-condition here. We could let [NormalizeWP]
    also generate side-conditions, but [IntoWand]/[FromAssumption] currently lack the ability
    to handle pure side-conditions. *)
Global Instance normalize_wp_step `{!blazeGS Σ} n e e' K R :
  DoPureStepsIntoCtx True e (TCEq e') n K →
  NormalizeWP (WP e {{R}})%I K e' R | 10.
Proof.
  intros [? H [? -> <-]]. split.
  assert (PureExec True n e (fill K e')).
  { intros _. by apply H. }
  rewrite -wp_pure_step_later //.
  rewrite -bi.laterN_intro. apply bi.wand_intro_r, bi.sep_elim_l. tc_solve.
Qed.

Global Instance from_assumption_wp `{!blazeGS Σ} p K e e' R R' :
  NormalizeWP (WP e {{R}})%I K e' R' →
  FromAssumption p (WP (fill K e') {{R'}})%I (WP e {{R}})%I | 2.
Proof.
  intros [HR].
  rewrite /FromAssumption bi.intuitionistically_if_elim. by rewrite HR.
Qed.

Global Instance into_wand_wp `{!blazeGS Σ} p e K e' R R' S Q :
  NormalizeWP (WP e {{R}})%I K e' R' →
  TCSimpl (∀ v, S v -∗ R' v)%I Q →
  IntoWand p false (WP (fill K e') {{S}})%I Q (WP e {{R}})%I | 1.
Proof.
  intros [Hwp] <-%TCSimpl_eq.
  rewrite /IntoWand /= bi.intuitionistically_if_elim.
  rewrite -Hwp. iIntros "H ?".
  by iApply (wp_wand with "H").
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/458 *)
Global Instance into_wand_wand_wp `{!blazeGS Σ} p q e K e' P P' Q R R' :
  NormalizeWP (WP e {{R}})%I K e' R' →
  FromAssumption q P P' →
  TCSimpl P Q →
  IntoWand p q (P' -∗ WP fill K e' {{R'}})%I Q (WP e {{R}})%I.
Proof.
  rewrite /FromAssumption /IntoWand.
  intros [Hwp] ? <-%TCSimpl_eq.
  rewrite bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by rewrite Hwp.
Qed.


Section wp_lemmas.
  Context `{!blazeGS Σ}.

  Lemma tac_wp_pure {Δ Δ' e e' R Q φ} n :
    DoPureSteps φ n e e' →
    φ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    FinalizeWP e' R Q →
    envs_entails Δ' Q →
    envs_entails Δ (WP e {{R}})%I.
  Proof.
    rewrite envs_entails_unseal=> -[Hsteps] Hφ HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ {HQ HΔ HΔ'}.
    assert (PureExec φ n e e') by by rewrite /PureExec.
    rewrite -wp_pure_step_later //.
    apply bi.laterN_mono. auto.
  Qed.

  Lemma tac_wp_rec {Δ Δ' e' v1 v2 f x e K R Q} :
    IntoCtx e (IsAppRec v1 v2 f x e') K →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    FinalizeWP (fill K (val_subst' x v2 (val_subst' f v1 e'))) R Q →
    envs_entails Δ' Q →
    envs_entails Δ (WP e {{R}})%I.
  Proof.
    rewrite envs_entails_unseal=> -[? -> [-> ->]] HΔ [HQ] HΔ'.
    rewrite into_laterN_env_sound HΔ' HQ /=.
    assert (PureExec True 1 (fill K ((rec: f x := e')%V v2)) (fill K (val_subst' x v2 (val_subst' f (rec: f x := e') e')))).
    { apply pure_exec_fill. apply _. }
    rewrite -wp_pure_step_later //.
    apply bi.later_mono. auto.
  Qed.

End wp_lemmas.

Tactic Notation "wp_pures" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ _ _) =>
    notypeclasses refine (tac_wp_pure n _ _ _ _ _);
      [ tc_solve || fail 1 "wp_pures: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* into later *)
      | tc_solve (* simpl *)
      | pm_prettify ]
  | |- _ => fail "wp_pures: goal not a `wp`"
  end.
Tactic Notation "wp_pure" := wp_pures 1.
Tactic Notation "wp_pures" := wp_pures (S _).

Tactic Notation "wp_rec" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ _ _) =>
    notypeclasses refine (tac_wp_rec _ _ _ _);
      [ tc_solve || fail 1 "wp_rec: no beta reduction step can be performed"
      | tc_solve (* into laters *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "wp_rec: goal not a `wp`"
  end.
