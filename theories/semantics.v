(* semantics.v *)

From blaze Require Import stdpp_ext.
From blaze Require Import syntax.
From stdpp Require Import gmap.

(* ========================================================================= *)
(** * Preliminary Definitions. *)

(* ------------------------------------------------------------------------- *)
(** Values. *)

Notation of_val := Val (only parsing).
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.


(* ------------------------------------------------------------------------- *)
(** Frames & Evaluation Contexts. *)

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | AppLCtx v2 =>
      App e (of_val v2)
  | AppRCtx e1 =>
      App e1 e
  | DoCtx l =>
      Do (EffLabel l) e
  | HandleCtx hs m l e2 e3 =>
      Handle hs m (EffLabel l) e e2 e3
  | UnOpCtx op =>
      UnOp op e
  | BinOpLCtx op v2 =>
      BinOp op e (of_val v2)
  | BinOpRCtx op e1 =>
      BinOp op e1 e
  | IfCtx e1 e2 =>
      If e e1 e2
  | PairLCtx v2 =>
      Pair e (of_val v2)
  | PairRCtx e1 =>
      Pair e1 e
  | FstCtx =>
      Fst e
  | SndCtx =>
      Snd e
  | InjLCtx =>
      InjL e
  | InjRCtx =>
      InjR e
  | CaseCtx e1 e2 =>
      Case e e1 e2
  | AllocNLCtx v2 =>
      AllocN e (of_val v2)
  | AllocNRCtx e1 =>
      AllocN e1 e
  | FreeCtx =>
      Free e
  | LoadCtx =>
      Load e
  | StoreLCtx v2 =>
      Store e (of_val v2)
  | StoreRCtx e1 =>
      Store e1 e
  | CmpXchgLCtx v1 v2 =>
      CmpXchg e (of_val v1) (of_val v2)
  | CmpXchgMCtx e0 v2 =>
      CmpXchg e0 e (of_val v2)
  | CmpXchgRCtx e0 e1 =>
      CmpXchg e0 e1 e
  | XchgLCtx v2 =>
      Xchg e (of_val v2)
  | XchgRCtx e1 =>
      Xchg e1 e
  | FaaLCtx v2 =>
      FAA e (of_val v2)
  | FaaRCtx e1 =>
      FAA e1 e
  end.

Fixpoint fill (k : ectx) (e : expr) : expr :=
  match k with [] => e | f :: k => fill_frame f (fill k e) end.

Definition get_frame (e : expr) : option (frame * expr) :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Effect _ _ | Fork _
  | Do (EffName _) _
  | Handle _ _ (EffName _) _ _ _ => None

  | App e1 e2 =>
      match to_val e2 with
      | None    => Some (AppRCtx e1, e2)
      | Some v2 => Some (AppLCtx v2, e1)
      end

  | Do (EffLabel l') e' =>
      Some (DoCtx l', e')

  | Handle hs m (EffLabel l') e1 e2 e3 =>
      Some (HandleCtx hs m l' e2 e3, e1)

  | UnOp op e =>
      Some (UnOpCtx op, e)

  | BinOp op e1 e2 =>
      match to_val e2 with
      | None    => Some (BinOpRCtx op e1, e2)
      | Some v2 => Some (BinOpLCtx op v2, e1)
      end

  | If e0 e1 e2 =>
      Some (IfCtx e1 e2, e0)

  | Pair e1 e2 =>
      match to_val e2 with
      | None    => Some (PairRCtx e1, e2)
      | Some v2 => Some (PairLCtx v2, e1)
      end

  | Fst e =>
      Some (FstCtx, e)

  | Snd e =>
      Some (SndCtx, e)

  | InjL e =>
      Some (InjLCtx, e)

  | InjR e =>
      Some (InjRCtx, e)

  | Case e0 e1 e2 =>
      Some (CaseCtx e1 e2, e0)

  | AllocN e1 e2 =>
      match to_val e2 with
      | None    => Some (AllocNRCtx e1, e2)
      | Some v2 => Some (AllocNLCtx v2, e1)
      end

  | Load e =>
      Some (LoadCtx, e)

  | Free e =>
      Some (FreeCtx, e)

  | Store e1 e2 =>
      match to_val e2 with
      | None    => Some (StoreRCtx e1, e2)
      | Some v2 => Some (StoreLCtx v2, e1)
      end

  | CmpXchg e0 e1 e2 =>
      match to_val e2 with
      | None => Some (CmpXchgRCtx e0 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None    => Some (CmpXchgMCtx e0 v2, e1)
          | Some v1 => Some (CmpXchgLCtx v1 v2, e0)
          end
      end

  | Xchg e1 e2 =>
      match to_val e2 with
      | None    => Some (XchgRCtx e1, e2)
      | Some v2 => Some (XchgLCtx v2, e1)
      end

  | FAA e1 e2 =>
      match to_val e2 with
      | None    => Some (FaaRCtx e1, e2)
      | Some v2 => Some (FaaLCtx v2, e1)
      end
  end.

Definition sub_expr e e' := ∃ f, Some (f, e) = get_frame e'.

Lemma sub_expr_wf : well_founded sub_expr.
Proof.
  intros e.
  induction e; apply Acc_intro=>y [f' HSome]; simpl in HSome;
  by (repeat match goal with
   | _ : Some _ = match ?e with | _ => _ end |- _ => destruct e
   | H : Some _ = Some _ |- _ => injection H as -> ->
   end).
Qed.

Definition sub_expr_intro f e e' : Some (f, e) = get_frame e' → sub_expr e e' :=
  λ H, @ex_intro frame (λ f, Some (f, e) = get_frame e') f H.

Fixpoint get_ectx (e : expr) : ectx * expr :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Effect _ _ | Fork _
  | Do (EffName _) _
  | Handle _ _ (EffName _) _ _ _ => ([], e)

  | App e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (AppRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (AppLCtx v2 :: k, e')
      end

  | Do (EffLabel l') e =>
      let (k, e') := get_ectx e in (DoCtx l' :: k, e')

  | Handle hs m (EffLabel l') e1 e2 e3 =>
      let (k, e') := get_ectx e1 in (HandleCtx hs m l' e2 e3 :: k, e')

  | UnOp op e =>
      let (k, e') := get_ectx e in (UnOpCtx op :: k, e')

  | BinOp op e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (BinOpRCtx op e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (BinOpLCtx op v2 :: k, e')
      end

  | If e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (IfCtx e1 e2 :: k, e')

  | Pair e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (PairRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (PairLCtx v2 :: k, e')
      end

  | Fst e =>
      let (k, e') := get_ectx e in (FstCtx :: k, e')

  | Snd e =>
      let (k, e') := get_ectx e in (SndCtx :: k, e')

  | InjL e =>
      let (k, e') := get_ectx e in (InjLCtx :: k, e')

  | InjR e =>
      let (k, e') := get_ectx e in (InjRCtx :: k, e')

  | Case e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (CaseCtx e1 e2 :: k, e')

  | AllocN e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (AllocNRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (AllocNLCtx v2 :: k, e')
      end

  | Load e =>
      let (k, e') := get_ectx e in (LoadCtx :: k, e')

  | Free e =>
      let (k, e') := get_ectx e in (FreeCtx :: k, e')

  | Store e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (StoreRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (StoreLCtx v2 :: k, e')
      end

  | CmpXchg e0 e1 e2 =>
      match to_val e2 with
      | None => let (k, e') := get_ectx e2 in (CmpXchgRCtx e0 e1 :: k, e')
      | Some v2 =>
          match to_val e1 with
          | None    => let (k, e') := get_ectx e1 in (CmpXchgMCtx e0 v2 :: k, e')
          | Some v1 => let (k, e') := get_ectx e0 in (CmpXchgLCtx v1 v2 :: k, e')
          end
      end

  | Xchg e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (XchgRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (XchgLCtx v2 :: k, e')
      end

  | FAA e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (FaaRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (FaaLCtx v2 :: k, e')
      end
  end.


(* ------------------------------------------------------------------------- *)
(** Neutral Contexts. *)

Definition frame_label (f : frame) : option label :=
  match f with HandleCtx _ _ l _ _ => Some l | _ => None end.

Definition ectx_labels (k : ectx) : list label :=
  omap frame_label k.

Lemma ectx_labels_app k k' : ectx_labels (k ++ k') = ectx_labels k ++ ectx_labels k'.
Proof. by apply omap_app. Qed.

Lemma ectx_labels_cons f k :
  ectx_labels (f :: k) =
  (option_rect (λ _, list label) (λ l, [l]) [] (frame_label f)) ++ ectx_labels k.
Proof. rewrite (ectx_labels_app [f]). f_equiv. by destruct f=>//. Qed.

Lemma Permutation_ectx_labels k k' : k ≡ₚ k' → ectx_labels k ≡ₚ ectx_labels k'.
Proof. by apply omap_Permutation. Qed.

Class NeutralFrame (ls : list label) (f : frame) := {
  neutral_frame : option_rect (λ _, Prop) (λ l, l ∉ ls) True (frame_label f)
}.

Class NeutralEctx (ls : list label) (k : ectx) := {
  neutral_ectx : ∀ l, l ∈ ls → l ∉ ectx_labels k
}.

Instance NeutralEctx_nil ls : NeutralEctx ls [].
Proof. constructor. intros ? _. by apply not_elem_of_nil. Qed.

Lemma NeutralEctx_cons ls f k :
  NeutralFrame ls f →
  NeutralEctx ls k →
  NeutralEctx ls (f :: k).
Proof.
  intros Hf Hk. constructor. intros l Hin_ls. simpl.
  destruct f=>//=; try (by apply Hk);
  rewrite not_elem_of_cons; split; try (by apply Hk).
  specialize neutral_frame; simpl. set_solver.
Qed.

Instance AppRCtx_NeutralEctx ls (e1 : expr) k :
  NeutralEctx ls k → NeutralEctx ls (AppRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AppLCtx_NeutralEctx ls (v2 : val) k :
  NeutralEctx ls k → NeutralEctx ls (AppLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance DoCtx_NeutralEctx (ls : list label) (l' : label) k :
  NeutralEctx ls k →  NeutralEctx ls (DoCtx l' :: k).
Proof. by intros ?; apply NeutralEctx_cons. Qed.

Instance HandleCtx_NeutralEctx hs m (ls : list label) (l' : label) (e2 e3 : expr) k :
  l' ∉ ls →
  NeutralEctx ls k → 
  NeutralEctx ls (HandleCtx hs m l' e2 e3 :: k).
Proof. by intros ?; apply NeutralEctx_cons. Qed.

Instance UnOpCtx_NeutralEctx ls op k : NeutralEctx ls k → NeutralEctx ls (UnOpCtx op :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance BinOpLCtx_NeutralEctx ls op v2 k : NeutralEctx ls k → NeutralEctx ls (BinOpLCtx op v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance BinOpRCtx_NeutralEctx ls op e1 k : NeutralEctx ls k → NeutralEctx ls (BinOpRCtx op e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance IfCtx_NeutralEctx ls e1 e2 k : NeutralEctx ls k → NeutralEctx ls (IfCtx e1 e2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance PairLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (PairLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance PairRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (PairRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance FstCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (FstCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance SndCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (SndCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance InjLCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (InjLCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance InjRCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (InjRCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance CaseCtx_NeutralEctx ls e1 e2 k : NeutralEctx ls k → NeutralEctx ls (CaseCtx e1 e2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AllocNLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (AllocNLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AllocNRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (AllocNRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance FreeCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (FreeCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance LoadCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (LoadCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance StoreLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (StoreLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance StoreRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (StoreRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance CmpXchgLCtx_NeutralEctx ls v1 v2 k : NeutralEctx ls k → NeutralEctx ls (CmpXchgLCtx v1 v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance CmpXchgMCtx_NeutralEctx ls e0 v2 k : NeutralEctx ls k → NeutralEctx ls (CmpXchgMCtx e0 v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance CmpXchgRCtx_NeutralEctx ls e0 e1 k : NeutralEctx ls k → NeutralEctx ls (CmpXchgRCtx e0 e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance XchgLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (XchgLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance XchgRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (XchgRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance FaaLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (FaaLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance FaaRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (FaaRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance NeutralEctx_dec ls k : Decision (NeutralEctx ls k).
Proof.
  case (Forall_dec (λ l, l ∉ ectx_labels k) ls); [left|right].
  - constructor. by apply Forall_forall.
  - intros Habsurd. apply n. rewrite Forall_forall. by apply neutral_ectx.
Qed.

Lemma Permutation_NeutralEctx ls k k' :
  k ≡ₚ k' →
  NeutralEctx ls k →
  NeutralEctx ls k'.
Proof.
  intros Hperm Hneutral. constructor; intros ? Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls).
  apply (elem_of_Permutation_proper _ (ectx_labels k) (ectx_labels k')); [|done].
  by apply Permutation_ectx_labels.
Qed.

Lemma NeutralEctx_app ls k k' :
  NeutralEctx ls k → NeutralEctx ls k' → NeutralEctx ls (k ++ k').
Proof.
  intros??; constructor; intros l Hin_ls Hin_app.
  rewrite ectx_labels_app in Hin_app.
  rewrite elem_of_app in Hin_app.
  destruct Hin_app as [Hin_k|Hin_k'].
  - by apply (neutral_ectx l Hin_ls Hin_k).
  - by apply (neutral_ectx l Hin_ls Hin_k').
Qed.

Lemma NeutralEctx_app_l ls k k' : NeutralEctx ls (k ++ k') → NeutralEctx ls k.
Proof.
  intros ?Hneutral. constructor. intros l Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls). rewrite ectx_labels_app elem_of_app. by left.
Qed.

Lemma NeutralEctx_app_r ls k k' : NeutralEctx ls (k ++ k') → NeutralEctx ls k'.
Proof.
  intros ?Hneutral. constructor. intros l Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls). rewrite ectx_labels_app elem_of_app. by right.
Qed.

Lemma NeutralEctx_cons_inv ls f k :
  NeutralEctx ls (f :: k) → NeutralFrame ls f ∧ NeutralEctx ls k.
Proof.
  intros Hneutral. split; [|by apply (NeutralEctx_app_r _ [f])].
  specialize (NeutralEctx_app_l _ [f] _ Hneutral) as Hf.
  destruct f=>//=; simpl; constructor; intros Hin_ls. clear Hneutral.
  by apply (neutral_ectx l Hin_ls), elem_of_list_singleton.
Qed.

Lemma NeutralEctx_ectx_labels_iff ls k :
  NeutralEctx ls k ↔ (∀ l, l ∈ ls → l ∈ ectx_labels k → False).
Proof. by split; intros ?; [apply neutral_ectx|constructor]. Qed.

Lemma NeutralEctx_ectx_labels_singleton l k : NeutralEctx [l] k ↔ l ∉ ectx_labels k.
Proof. by rewrite NeutralEctx_ectx_labels_iff; set_solver. Qed.

Instance NeutralFrame_label_cons_inv_1 l ls f :
  NeutralFrame (l :: ls) f → NeutralFrame [l] f.
Proof.
  intros Hk. constructor. specialize neutral_frame.
  destruct (frame_label f); set_solver.
Qed.

Instance NeutralFrame_label_cons_inv_2 l ls f :
  NeutralFrame (l :: ls) f → NeutralFrame ls f.
Proof.
  intros Hk. constructor. specialize neutral_frame.
  destruct (frame_label f); set_solver.
Qed.

Instance NeutralEctx_label_cons_inv_1 l ls k :
  NeutralEctx (l :: ls) k → NeutralEctx [l] k.
Proof.
  intros Hk. constructor. intros l'.
  rewrite elem_of_list_singleton. intros ->.
  apply neutral_ectx. rewrite elem_of_cons. by left.
Qed.

Instance NeutralEctx_label_cons_inv_2 l ls k :
  NeutralEctx (l :: ls) k → NeutralEctx ls k.
Proof.
  intros Hk. constructor. intros l' Hin_ls.
  apply neutral_ectx. rewrite elem_of_cons. by right.
Qed.


(* ------------------------------------------------------------------------- *)
(** Effects. *)

Definition to_eff (e : expr) : option (label * val * ectx) :=
  match get_ectx e with
  | (k, Val v) =>
      match reverse k with
      | DoCtx l :: k' => Some (l, v, reverse k')
      | _ => None
      end
  | _ =>
      None
  end.

Definition of_eff (l : label) (v : val) (k : ectx) :=
  fill k (Do (EffLabel l) (Val v)).

Definition not_eff (e : expr) : Prop :=
  to_eff e = None ∨ ∃ l v k, to_eff e = Some (l, v, k) ∧ l ∈ ectx_labels k.

Global Instance not_eff_dec e : Decision (not_eff e).
Proof.
  destruct (to_eff e) as [((l, v), k)|] eqn:He; [|by left; left].
  case (decide (l ∈ ectx_labels k)); [intro Hin|intro Hnot_in]; [left|right].
  - right; rewrite He //=. by eauto.
  - intros [He'|[? [? [? [He' ?]]]]]; rewrite He' in He; [done|].
    by injection He as -> -> ->.
Qed.


(* ------------------------------------------------------------------------- *)
(** Properties. *)

(* -------------------------------------------------------------------------- *)
(* [to_val]. *)

Lemma of_to_val e v : to_val e = Some v → e = of_val v.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? [=]. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill_frame]. *)

Instance fill_frame_inj f : Inj (=) (=) (fill_frame f).
Proof. induction f; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_frame_val f e : to_val (fill_frame f e) = None.
Proof. induction f; simplify_option_eq; eauto. Qed.

Lemma fill_frame_no_val_inj f1 f2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_frame f1 e1 = fill_frame f2 e2 → f1 = f2.
Proof. revert f1. induction f2, f1; naive_solver eauto with f_equal. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill]. *)

Instance fill_inj k : Inj (=) (=) (fill k).
Proof. induction k; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_app k k' e : fill (k ++ k') e = fill k (fill k' e).
Proof. by induction k as [|f k]; simpl; [|rewrite IHk]. Qed.

Lemma fill_val k e v : to_val (fill k e) = Some v → k = [] ∧ e = Val v.
Proof.
  destruct k as [|f k].
  - by intro H; rewrite -(of_to_val _ _ H).
  - by destruct f; naive_solver.
Qed.

Lemma fill_inv k e : get_frame (fill k e) = None → k = [].
Proof.
  induction k as [|f k] =>//=.
  destruct f =>//=; by repeat destruct (to_val _).
Qed.

Lemma fill_inv' k e e' : fill k e = e' → get_frame e' = None → k = [] ∧ e = e'.
Proof. intros <- Hget_frame. by rewrite (fill_inv _ _ Hget_frame). Qed.

Lemma fill_val_inv k e v : fill k e = Val v → k = [] ∧ e = Val v.
Proof. intros ?. by apply fill_inv'. Qed.

Lemma fill_not_val k e : to_val e = None → to_val (fill k e) = None.
Proof. induction k as [|f k]; eauto. intros ?; by apply fill_frame_val. Qed.


(* ------------------------------------------------------------------------- *)
(* [get_frame & get_ectx]. *)

Lemma get_ectx_alt (e : expr) :
  get_ectx e = match get_frame e with None => ([], e) | Some (f, e) =>
                 let (k, e') := get_ectx e in (f :: k, e')
               end.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the cases where we have a L and R context *)
      by repeat destruct (to_val _)
    ].
  - (* Do*) destruct n=>//=; injection 1 as Hf He; by rewrite Hf He.
  - (* Handle *) destruct n=>//=; injection 1 as Hf He; by rewrite Hf He.
Qed.

Lemma get_frame_Some e f e' :
  get_frame e = Some (f , e') → e = fill_frame f e'.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the simple cases like [Fst] *)
      by inversion 1 |
      (* Solve the cases where we have a L and R context *)
      repeat (destruct (to_val _) eqn:H; [apply of_to_val in H as ->|]); by inv 1
    ].
  - (* Do *) destruct n=>//. by inversion 1.
  - (* Handle *) destruct n=>//. by inversion 1.
Qed.

Lemma get_ectx_spec e e' k : get_ectx e = (k, e') → e = fill k e'.
Proof.
  revert e' k.
  induction (sub_expr_wf e).
  intros e' k'.
  rename x into e, H0 into IH, H into Hacc.
  rewrite get_ectx_alt.
  destruct (get_frame e) as [(f, e'')|] eqn:Hget_frame; last
  by injection 1 as <- <-.
  destruct (get_ectx e'') as (k'', e''') eqn:He''.
  injection 1 as <- <-. simpl. rewrite -(IH e''); last done.
  - by apply get_frame_Some.
  - by exists f.
Qed.

Lemma get_frame_fill_frame f e :
  to_val e = None →
  get_frame (fill_frame f e) = Some (f, e).
Proof. by intros He; destruct f=>//=; rewrite He. Qed.

Lemma get_ectx_fill_frame e e' f k :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill_frame f e) = (f :: k, e').
Proof.
  intros Hval He.
  rewrite get_ectx_alt get_frame_fill_frame; [|done].
  by rewrite -He.
Qed.

Lemma get_ectx_fill e e' k k' :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill k' e) = (k' ++ k, e').
Proof.
  revert e e' k; induction k'; intros ??? Hval Hget_ectx.
  - by rewrite -Hget_ectx.
  - simpl. rewrite (get_ectx_fill_frame _ e' _ (k' ++ k)); first done.
    + by apply fill_not_val.
    + symmetry. by apply IHk'.
Qed.

Lemma get_ectx_fill' e1 e1' e2 k k' :
  to_val e1 = None →
  e2 = fill k' e1 →
  (k, e1') = get_ectx e1 →
  get_ectx e2 = (k' ++ k, e1').
Proof. intros ? ->. by apply get_ectx_fill. Qed.


(* ------------------------------------------------------------------------- *)
(* [to_eff]. *)

Lemma to_eff_eff l v : to_eff (Do (EffLabel l) (Val v)) = Some (l, v, []).
Proof. by rewrite /to_eff //= reverse_nil. Qed.

Lemma to_eff_get_ectx e l v k :
  to_eff e = Some (l, v, k) → get_ectx e = (k ++ [DoCtx l], Val v).
Proof.
  rewrite /to_eff.
  destruct (get_ectx e) as [k' e'] eqn:Hget_ectx.
  destruct (to_val e') as [v'|] eqn:Hval.
  - rewrite (of_to_val _ _ Hval).
    destruct k' as [|f k'' _] eqn:Hk using rev_ind; [done|].
    rewrite reverse_app //= reverse_involutive.
    destruct f=>//=. by injection 1 as -> -> ->.
  - by destruct e'=>//.
Qed.

Lemma to_eff_get_ectx' e l v k :
  get_ectx e = (k ++ [DoCtx l], Val v) → to_eff e = Some (l, v, k).
Proof. intros He. by rewrite /to_eff He reverse_app //= reverse_involutive. Qed.

Lemma to_eff_get_ectx_iff e l v k :
  to_eff e = Some (l, v, k) ↔ get_ectx e = (k ++ [DoCtx l], Val v).
Proof. by split; [apply to_eff_get_ectx|apply to_eff_get_ectx']. Qed.

Lemma of_to_eff e l v k : to_eff e = Some (l, v, k) → of_eff l v k = e.
Proof.
  intros He. rewrite to_eff_get_ectx_iff in He.
  by rewrite (get_ectx_spec _ _ _ He) fill_app //=.
Qed.

Lemma to_eff_not_val e : is_Some (to_eff e) → to_val e = None.
Proof.
  intros [((l, v), k) He]. rewrite -(of_to_eff _ _ _ _ He).
  destruct k as [|f k]; [done|].
  by destruct f=>//=.
Qed.

Lemma of_eff_inj l1 v1 k1 l2 v2 k2 :
  of_eff l1 v1 k1 = of_eff l2 v2 k2 → l1 = l2 ∧ v1 = v2 ∧ k1 = k2.
Proof.
  revert k1 k2; induction k1; intros k2.
  - unfold of_eff. simpl.
    destruct k2=>//=.
    + inversion 1. by auto.
    + destruct f=>//=; inversion 1.
      destruct k2=>//=; destruct f=>//=.
  - destruct a=>//=; destruct k2=>//=;
    try destruct f=>//=;
    rewrite /of_eff //=; inv 1;
      try solve [
        match goal with
        | H : fill _ _ = fill _ _ |- _ => by apply IHk1 in H as (-> & -> & ->)
        | H : fill _ _ = Val _ |- _ => apply fill_val_inv in H as [_ [=]]
        | H : Val _ = fill _ _ |- _ => apply sym_eq, fill_val_inv in H as [_ [=]]
        end
      ].
Qed.

(* ------------------------------------------------------------------------- *)
(* [fill] & [to_eff]. *)

Lemma to_eff_fill_frame l f k e v :
  to_eff e = Some (l, v, k) →
  to_eff (fill_frame f e) = Some (l, v, f :: k).
Proof.
  intros He. rewrite /to_eff.
  rewrite to_eff_get_ectx_iff in He.
  rewrite (get_ectx_fill_frame _ (Val v) _ (k ++ [DoCtx l])); last done.
  - by rewrite reverse_cons reverse_app //= reverse_app reverse_involutive //=. 
  - apply to_eff_not_val. exists (l, v, k).
    by rewrite to_eff_get_ectx_iff.
Qed.

Lemma to_eff_fill l k k' e v :
  to_eff e = Some (l, v, k') → to_eff (fill k e) = Some (l, v, k ++ k').
Proof.
  induction k as [|f k]; [done|].
  intros He; simpl.
  apply to_eff_fill_frame.
  by apply IHk.
Qed.

Lemma fill_not_eff k e :
  to_val e = None →
  to_eff e = None →
  to_eff (fill k e) = None.
Proof.
  intros He.
  rewrite /to_eff.
  destruct (get_ectx e) as (k', e') eqn:Hget_ectx.
  rewrite (get_ectx_fill _ e' k'); try done.
  destruct k' as [|f k'] using rev_ind.
  - destruct e'=>//. exfalso.
    specialize (get_ectx_spec _ _ _ Hget_ectx).
    by destruct e=>//.
  - rewrite !reverse_app //=.
    destruct e'=>//. by destruct f=>//.
Qed.

Lemma to_of_eff l v k : to_eff (of_eff l v k) = Some (l, v, k).
Proof.
  specialize (to_eff_fill l k [] (Do (EffLabel l) (Val v)) v) as Heq.
  rewrite app_nil_r in Heq.
  by apply Heq.
Qed.

Lemma of_eff_not_val l v k : to_val (of_eff l v k) = None.
Proof. apply to_eff_not_val. by rewrite to_of_eff. Qed.

Lemma to_eff_of_eff' l k v :
  l ∉ ectx_labels k →
  to_eff (of_eff l v k) = Some (l, v, k).
Proof. intros Hnot_in_k. by apply to_of_eff. Qed.


(* -------------------------------------------------------------------------- *)
(** Substitution. *)

Fixpoint val_subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if decide (x = y) then Val v else Var y
  | Effect s e =>
      Effect s (val_subst x v e)
  | Do n e =>
      Do n (val_subst x v e)
  | Handle s m n e1 e2 e3 =>
      Handle s m n (val_subst x v e1) (val_subst x v e2) (val_subst x v e3)
  | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then val_subst x v e else e
  | App e1 e2 =>
      App (val_subst x v e1) (val_subst x v e2)
  | UnOp op e =>
      UnOp op (val_subst x v e)
  | BinOp op e1 e2 =>
      BinOp op (val_subst x v e1) (val_subst x v e2)
  | If e0 e1 e2 =>
      If (val_subst x v e0) (val_subst x v e1) (val_subst x v e2)
  | Pair e1 e2 =>
      Pair (val_subst x v e1) (val_subst x v e2)
  | Fst e =>
      Fst (val_subst x v e)
  | Snd e =>
      Snd (val_subst x v e)
  | InjL e =>
      InjL (val_subst x v e)
  | InjR e =>
      InjR (val_subst x v e)
  | Case e0 e1 e2 =>
      Case (val_subst x v e0) (val_subst x v e1) (val_subst x v e2)
  | AllocN e1 e2 =>
      AllocN (val_subst x v e1) (val_subst x v e2)
  | Free e =>
      Free (val_subst x v e)
  | Load e =>
      Load (val_subst x v e)
  | Store e1 e2 =>
      Store (val_subst x v e1) (val_subst x v e2)
  | CmpXchg e0 e1 e2 =>
      CmpXchg (val_subst x v e0) (val_subst x v e1) (val_subst x v e2)
  | Xchg e1 e2 =>
      Xchg (val_subst x v e1) (val_subst x v e2)
  | FAA e1 e2 =>
      FAA (val_subst x v e1) (val_subst x v e2)
  | Fork e =>
      Fork (val_subst x v e)
  end.

Definition val_subst' (b : binder) (v : val) : expr → expr :=
  match b with BNamed x => val_subst x v | BAnon => id end.

Fixpoint lbl_subst (s : string) (l : label) (e : expr) : expr :=
  match e with
  | Val _ | Var _ =>
      e
  | Effect s' e' =>
      if decide (s = s') then e else Effect s' (lbl_subst s l e')

  | Do (EffLabel _ as n') e' =>
      Do n' (lbl_subst s l e')
  | Do (EffName s' as n') e' =>
      Do (if decide (s = s') then (EffLabel l) else n') (lbl_subst s l e')

  | Handle hs m (EffLabel _ as n') e1 e2 e3 =>
      Handle hs m n' (lbl_subst s l e1) (lbl_subst s l e2) (lbl_subst s l e3)
  | Handle hs m (EffName s' as n') e1 e2 e3 =>
      Handle hs m (if decide (s = s') then (EffLabel l) else n')
        (lbl_subst s l e1) (lbl_subst s l e2) (lbl_subst s l e3)

  | Rec f y e =>
      Rec f y $ lbl_subst s l e
  | App e1 e2 =>
      App (lbl_subst s l e1) (lbl_subst s l e2)
  | UnOp op e =>
      UnOp op (lbl_subst s l e)
  | BinOp op e1 e2 =>
      BinOp op (lbl_subst s l e1) (lbl_subst s l e2)
  | If e0 e1 e2 =>
      If (lbl_subst s l e0) (lbl_subst s l e1) (lbl_subst s l e2)
  | Pair e1 e2 =>
      Pair (lbl_subst s l e1) (lbl_subst s l e2)
  | Fst e =>
      Fst (lbl_subst s l e)
  | Snd e =>
      Snd (lbl_subst s l e)
  | InjL e =>
      InjL (lbl_subst s l e)
  | InjR e =>
      InjR (lbl_subst s l e)
  | Case e0 e1 e2 =>
      Case (lbl_subst s l e0) (lbl_subst s l e1) (lbl_subst s l e2)
  | AllocN e1 e2 =>
      AllocN (lbl_subst s l e1) (lbl_subst s l e2)
  | Free e =>
      Free (lbl_subst s l e)
  | Load e =>
      Load (lbl_subst s l e)
  | Store e1 e2 =>
      Store (lbl_subst s l e1) (lbl_subst s l e2)
  | CmpXchg e0 e1 e2 =>
      CmpXchg (lbl_subst s l e0) (lbl_subst s l e1) (lbl_subst s l e2)
  | Xchg e1 e2 =>
      Xchg (lbl_subst s l e1) (lbl_subst s l e2)
  | FAA e1 e2 =>
      FAA (lbl_subst s l e1) (lbl_subst s l e2)
  | Fork e =>
      Fork (lbl_subst s l e)
  end.

(* -------------------------------------------------------------------------- *)
(** Unboxed values. *)

Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => True
  | InjLV (LitV l) => True
  | InjRV (LitV l) => True
  | _ => False
  end.

Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(* ========================================================================== *)
(** * Reduction Relation. *)

(* Operations *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

(* Compute next label. *)
Definition label_succ : label → label := λ l,
  Label (S (label_car l))%nat.

Definition state_upd_next_label (f : label → label) (σ : state) : state :=
  {| next_label := f σ.(next_label); heap := σ.(heap) |}.
Global Arguments state_upd_next_label _ !_ /.

Definition state_upd_heap (f: gmap loc (option val) → gmap loc (option val)) (σ: state) : state :=
  {| heap := f σ.(heap); next_label := σ.(next_label) |}.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (option val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite Loc.add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite Loc.add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite Loc.add_0; eauto. }
    right. split.
    { rewrite -{1}(Loc.add_0 l). intros ?%(inj (Loc.add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite Loc.add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (option val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=Some v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

(* Heap-reduction relation. *)
Inductive base_step : expr → state → expr → state → list expr → Prop :=
  (* Lambda. *)
  | RecS f x e σ :
     base_step (Rec f x e) σ (Val $ RecV f x e) σ []

  (* Beta reduction. *)
  | BetaS f x e1 v2 e' σ :
     e' = val_subst' x v2 (val_subst' f (RecV f x e1) e1) →
     base_step (App (Val $ RecV f x e1) (Val v2)) σ e' σ []

  (* Invoking a one-shot continuation. *)
  | ContS k r w e' σ :
     σ.(heap) !! r = Some (Some (LitV $ LitBool true)) →
     e' = fill k (Val w) →
     base_step (App (Val (ContV r k)) (Val w))
               σ
               e'
               (state_upd_heap <[r:=Some (LitV $ LitBool false)]> σ) []

  (* Invoking a multi-shot continuation. *)
  | KontS k w e' σ :
     e' = fill k (Val w) →
     base_step (App (Val (KontV k)) (Val w)) σ e' σ []

  (* Effect. *)
  | EffectS s e e' σ σ' :
     σ' = state_upd_next_label label_succ σ →
     e' = lbl_subst s σ.(next_label) e →
     base_step (Effect s e) σ e' σ' []

  (* Capturing a multi-shot continuation. *)
  | HandleMSEffS hs l v k e1 e2 e3 σ :
     let k' :=
       match hs with Deep => (HandleCtx hs MS l e2 e3 :: k) | Shallow => k end
     in
     l ∉ ectx_labels k →
     to_eff e1 = Some (l, v, k) →
     base_step (Handle hs MS (EffLabel l) e1 e2 e3)    σ
               (App (App e2 (Val v)) (Val $ KontV k')) σ []

  (* Capturing a one-shot continuation. *)
  | HandleOSEffS hs l v k e1 e2 e3 r σ :
     let k' :=
       match hs with Deep => (HandleCtx hs OS l e2 e3 :: k) | Shallow => k end
     in
     σ.(heap) !! r = None →
     l ∉ ectx_labels k →
     to_eff e1 = Some (l, v, k) →
     base_step (Handle hs OS (EffLabel l) e1 e2 e3)
               σ
               (App (App e2 (Val v)) (Val $ ContV r k'))
               (state_upd_heap <[r:=Some (LitV $ LitBool $ true)]> σ) []

  (* Handle - Return branch. *)
  | HandleRetS hs m l v e2 e3 σ :
     base_step (Handle hs m (EffLabel l) (Val v) e2 e3) σ (App e3 (Val v)) σ []

  (* Operations *)
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     base_step (UnOp op (Val v)) σ (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     base_step (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  | IfTrueS e1 e2 σ :
     base_step (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
     base_step (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ []

  (* Products*)
  | PairS v1 v2 σ :
     base_step (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ []
  | FstS v1 v2 σ :
     base_step (Fst (Val $ PairV v1 v2)) σ (Val v1) σ []
  | SndS v1 v2 σ :
     base_step (Snd (Val $ PairV v1 v2)) σ (Val v2) σ []

  (* Sums *)
  | InjLS v σ :
     base_step (InjL $ Val v) σ (Val $ InjLV v) σ []
  | InjRS v σ :
     base_step (InjR $ Val v) σ (Val $ InjRV v) σ []
  | CaseLS v e1 e2 σ :
     base_step (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     base_step (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ []

  (* Heap *)
  | AllocNS n v σ l :
     (0 < n)%Z →
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) →
     base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) []
  | FreeS l v σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Free (Val $ LitV $ LitLoc l)) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=None]> σ) []
  | LoadS l v σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ []
  | StoreS l v w σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Store (Val $ LitV $ LitLoc l) (Val w)) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=Some w]> σ) []
  | XchgS l v1 v2 σ :
     σ.(heap) !! l = Some $ Some v1 →
     base_step (Xchg (Val $ LitV $ LitLoc l) (Val v2)) σ
               (Val v1) (state_upd_heap <[l:=Some v2]> σ) []
  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some $ Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     base_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=Some v2]> σ else σ) []
  | FaaS l i1 i2 σ :
     σ.(heap) !! l = Some $ Some (LitV (LitInt i1)) →
     base_step (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=Some $ LitV (LitInt (i1 + i2))]>σ) []
  (* Concurrency *)
  | ForkS e σ :
     base_step (Fork e) σ (Val $ LitV $ LitUnit) σ [e].

Lemma base_step_alloc_fresh v n σ :
  let l := Loc.fresh (dom σ.(heap)) in
  (0 < n)%Z →
  base_step (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ
            (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) [].
Proof.
  intros. apply AllocNS; first done.
  intros. apply not_elem_of_dom.
  by apply Loc.fresh_fresh.
Qed.

Lemma base_step_handle_os_eff hs l v k h ret σ :
  let r := Loc.fresh (dom σ.(heap)) in
  let c := match hs with Deep => HandleCtx hs OS l h ret :: k | Shallow => k end in
  l ∉ ectx_labels k →
  base_step (Handle hs OS (EffLabel l) (fill k (Do (EffLabel l) (Val v))) h ret)
            σ
            (App (App h (Val v)) (Val $ ContV r c))
            (state_upd_heap <[r := Some $ LitV $ LitBool true]> σ) [].
Proof.
  intros. apply HandleOSEffS; try done; last by apply to_of_eff.
  apply not_elem_of_dom.
  specialize (Loc.fresh_fresh (dom σ.(heap)) 0) as Hnot_in.
  rewrite Loc.add_0 in Hnot_in. by apply Hnot_in.
Qed.

(* Reduction relation. *)
(* [prim_step] is the closure of the head-reduction
   relation [base_step] over evaluation contexts. *)
Inductive prim_step (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
  | Ectx_prim_step (k : ectx) (e1' e2' : expr) :
     e1 = fill k e1' →
     e2 = fill k e2' →
     base_step e1' σ1 e2' σ2 efs →
     prim_step e1  σ1 e2  σ2 efs.


(* -------------------------------------------------------------------------- *)
(** Properties of [base_step] and [prim_step]. *)

Lemma Ectx_prim_step_2 k e1 e2 σ1 σ2 efs :
  base_step e1 σ1 e2 σ2 efs →
  prim_step (fill k e1) σ1 (fill k e2) σ2 efs.
Proof. intros ?. by apply (Ectx_prim_step _ _ _ _ _ k e1 e2). Qed.

Lemma base_prim_step e1 e2 σ1 σ2 efs :
  base_step e1 σ1 e2 σ2 efs → prim_step e1 σ1 e2 σ2 efs.
Proof. by apply (Ectx_prim_step_2 []). Qed.

(* Closure of [base_step] over evaluation frames. *)
Lemma Frame_prim_step f e1 e2 σ1 σ2 efs :
  base_step e1 σ1 e2 σ2 efs →
  prim_step (fill_frame f e1) σ1 (fill_frame f e2) σ2 efs.
Proof. by apply (Ectx_prim_step_2 [f]). Qed.

(* Closure of [prim_step] over evaluation frames. *)
Lemma Frame_prim_step' f e1 e2 σ1 σ2 efs :
  prim_step e1 σ1 e2 σ2 efs →
  prim_step (fill_frame f e1) σ1 (fill_frame f e2) σ2 efs.
Proof.
  inversion 1. simplify_eq.
  by apply (Ectx_prim_step_2 (f :: k)).
Qed.

(* Closure of [prim_step] over evaluation contexts. *)
Lemma Ectx_prim_step' k e1 e2 σ1 σ2 efs :
  prim_step e1 σ1 e2 σ2 efs →
  prim_step (fill k e1) σ1 (fill k e2) σ2 efs.
Proof.
  inversion 1. simplify_eq.
  rewrite -fill_app -fill_app.
  by apply (Ectx_prim_step_2 (k ++ k0)).
Qed.

(* If [e1] makes a head step to a value under some state [σ1],
   then any head step from [e1] under any other state [σ1']
   must necessarily be to a value. *)
Lemma base_step_to_val e1 σ1 e2 σ2 σ1' e2' σ2' efs :
  base_step e1 σ1  e2  σ2 efs →
  base_step e1 σ1' e2' σ2' efs →
  is_Some (to_val e2) →
  is_Some (to_val e2').
Proof.
  destruct 1; inversion 1; try naive_solver.
  intros [v' Hv'].
  rewrite (of_to_val _ _ Hv') in H0.
  revert H0 H8.
  destruct e=>//=.
  - by intros _ ->.
  - by case (decide (s = s1)); inversion 2.
  - by destruct n=>//=.
  - by destruct n=>//=.
Qed.

(* If [e1] can perform one step, then [e1] is not a value. *)
Lemma val_base_stuck e1 σ1 e2 σ2 efs : base_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; eauto. Qed.

Lemma Frame_prim_step_inv f e e₂ σ₁ σ₂ efs :
  to_val e = None →
  to_eff e = None →
  prim_step (fill_frame f e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill_frame f e'.
Proof.
  intros ?? Hstep.
  inversion Hstep. destruct k as [|f' k].
  - simpl in H1, H2, H3; simplify_eq.
    destruct f; inversion H3; try naive_solver;
    specialize H0; try by destruct (to_eff e).
  - simpl in H1, H2; simplify_eq.
    assert (e = fill k e1' ∧ f = f') as [-> ->].
    { assert (∀ v, (e1' = Val v → False)).
      { intros v ->; by specialize (val_base_stuck _ _ _ _ _ H3). }
      destruct f, f'; try naive_solver;
      try (simpl in H3; simplify_eq;
           by destruct k as [|f K]; try destruct f, K; try naive_solver).
    }
    exists (fill k e2'). split; [|done].
    by apply (Ectx_prim_step _ _ _ _ _ k e1' e2').
Qed.

(* if [fill_frame f (fill k (Do l v))] is reducible and [l ∉ f],
   then there must be a handler in [k] so that [fill k (Do l v)]
   is also reducible. *)
Lemma Frame_prim_step_eff_inv e l v k f e₂ σ₁ σ₂ efs :
  option_rect (λ _, Prop) (λ l', l' ≠ l) True (frame_label f) →
  to_eff e = Some (l, v, k) →
  prim_step (fill_frame f e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill_frame f e'.
Proof.
  intros Hf Heff Hstep.
  assert (Hval: to_val e = None). { by apply to_eff_not_val; eauto. }
  inversion Hstep. destruct k0 as [|f' k'].
  - simpl in H, H0, H1; simplify_eq.
    destruct f=>//=; inversion H1; simplify_eq; try done.
  - simpl in H, H0.
    assert (Hval': to_val (fill k' e1') = None).
    { apply fill_not_val. by destruct e1' =>//=; inversion H1. }
    destruct (fill_frame_no_val_inj _ _ _ _ Hval Hval' H).
    specialize (fill_frame_inj f _ _ H) as Heq. simplify_eq.
    exists (fill k' e2'). split; [|done].
    by apply (Ectx_prim_step _ _ _ _ _ k' e1' e2').
Qed.

Lemma Frame_prim_step_eff_inv' e l v k f e₂ σ₁ σ₂ efs :
  l ∈ ectx_labels k →
  to_eff e = Some (l, v, k) →
  prim_step (fill_frame f e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill_frame f e'.
Proof.
  intros Hk Heff Hstep.
  assert (Hval: to_val e = None). { by apply to_eff_not_val; eauto. }
  inversion Hstep. destruct k0 as [|f' k'].
  - simpl in H, H0, H1; simplify_eq.
    destruct f=>//=; inversion H1; simplify_eq; try done.
  - simpl in H, H0.
    assert (Hval': to_val (fill k' e1') = None).
    { apply fill_not_val. by destruct e1' =>//=; inversion H1. }
    destruct (fill_frame_no_val_inj _ _ _ _ Hval Hval' H).
    specialize (fill_frame_inj f _ _ H) as Heq. simplify_eq.
    exists (fill k' e2'). split; [|done].
    by apply (Ectx_prim_step _ _ _ _ _ k' e1' e2').
Qed.

Lemma Ectx_prim_step_inv k e e₂ σ₁ σ₂ efs :
  to_val e = None →
  to_eff e = None →
  prim_step (fill k e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill k e'.
Proof.
  intros ??. revert e₂. induction k as [|f k]; intro e₂.
  - simpl. intros Hstep. exists e₂. by split.
  - simpl. intros Hstep.
    have Hfill_not_eff: to_eff (fill k e) = None.
    { by apply fill_not_eff. }
    destruct (Frame_prim_step_inv f _ _ _ _ _ (fill_not_val k _ H)
                                              Hfill_not_eff Hstep)
      as [e' [He' ->]].
    destruct (IHk _ He') as [e'' [He'' ->]].
    by exists e''.
Qed.

Lemma Ectx_prim_step_eff_inv l v k' k e e₂ σ₁ σ₂ efs :
  l ∉ ectx_labels k →
  to_eff e = Some (l, v, k') →
  prim_step (fill k e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill k e'.
Proof.
  intros Hk Heff.
  revert e₂. induction k as [|f k]; intros e₂ Hstep.
  - simpl. exists e₂. by split.
  - simpl.
    have Hf: option_rect (λ _, Prop) (λ l', l' ≠ l) True (frame_label f).
    { rewrite ectx_labels_cons in Hk. by destruct f=>//=; set_solver. }
    have Hnot_in_k: l ∉ ectx_labels k.
    { rewrite ectx_labels_cons in Hk. set_solver. }
    have Hfill: to_eff (fill k e) = Some (l, v, k ++ k').
    { by rewrite (to_eff_fill l k k' _ v). }
    simpl in Hstep.
    destruct (Frame_prim_step_eff_inv _ _ _ _ _ _ _ _ _ Hf Hfill Hstep)
      as [e' [He' ->]].
    destruct (IHk Hnot_in_k _ He') as [e'' [He'' ->]].
    by exists e''.
Qed.

Lemma Ectx_prim_step_eff_inv' l v k' k e e₂ σ₁ σ₂ efs :
  l ∈ ectx_labels k' →
  to_eff e = Some (l, v, k') →
  prim_step (fill k e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill k e'.
Proof.
  intros Hk' Heff.
  revert e₂. induction k as [|f k]; intros e₂ Hstep; simpl.
  - exists e₂. by split.
  - have Hin_app: l ∈ ectx_labels (k ++ k'). { by rewrite ectx_labels_app; set_solver. }
    have Hfill: to_eff (fill k e) = Some (l, v, k ++ k'). { by rewrite (to_eff_fill l k k' _ v). }
    destruct (Frame_prim_step_eff_inv' (fill k e) _ _ (k ++ k') _ _ _ _ _ Hin_app Hfill Hstep)
      as [e' [He' ->]].
    destruct (IHk _ He') as [e'' [He'' ->]].
    by exists e''.
Qed.

Lemma Ectx_prim_step_not_val_not_eff_inv k e e₂ σ₁ σ₂ efs :
  to_val e = None →
  not_eff e →
  prim_step (fill k e) σ₁ e₂ σ₂ efs →
  ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill k e'.
Proof.
  intros Hval [Heff|[l [v [k' [Heff Hl]]]]].
  - by apply Ectx_prim_step_inv.
  - by apply (Ectx_prim_step_eff_inv' l v k').
Qed.

