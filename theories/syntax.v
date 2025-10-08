(* syntax.v *)

From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.

Set Default Proof Using "Type".


(* ========================================================================== *)
(** * Syntax. *)

Section eff_lang.

  Record label := Label { label_car : nat }.

  Inductive mode : Set := OS | MS.

  Inductive handler_semantics : Set := Deep | Shallow.

  Inductive eff_val : Set :=
    (* Effect name. *)
    | EffName (s : string)
    (* Effect label. *)
    | EffLabel (l : label).

  Inductive base_lit : Set :=
    | LitUnit | LitInt (n : Z) | LitBool (b : bool) | LitLoc (l : loc).

  Inductive un_op : Set :=
    | NegOp | MinusUnOp.
  Inductive bin_op : Set :=
    (* Arithmetic. *)
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp
    (* Bitwise. *)
    | AndOp | OrOp | XorOp
    (* Shifts. *)
    | ShiftLOp | ShiftROp
    (* Relations. *)
    | LeOp | LtOp | EqOp
    (* Pointer offset. *)
    | OffsetOp.

  Inductive expr :=
    (* Values. *)
    | Val (v : val)
    (* Effects. *)
    | Effect (s : string) (e : expr)
    | Do (n : eff_val) (e : expr)
    | Handle (hs : handler_semantics) (m : mode) (n : eff_val) (e1 e2 e3 : expr)
    (* Base λ-calculus. *)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    (* Base types and their operations. *)
    | UnOp (op : un_op) (e : expr)
    | BinOp (op : bin_op) (e1 e2 : expr)
    | If (e0 e1 e2 : expr)
    (* Products. *)
    | Pair (e1 e2 : expr)
    | Fst (e : expr)
    | Snd (e : expr)
    (* Sums. *)
    | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 : expr) (e1 : expr) (e2 : expr)
    (* Heap. *)
    | AllocN (e1 e2 : expr) (* Array length (positive number), initial value *)
    | Free (e : expr)
    | Load (e : expr)
    | Store (e1 : expr) (e2 : expr)
    | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
    | Xchg (e0 : expr) (e1 : expr) (* Exchange *)
    | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
    (* Concurrency. *)
    | Fork (e : expr)

  with val :=
    (* Literals. *)
    | LitV (l : base_lit)
    (* First-class functions. *)
    | RecV (f x : binder) (e : expr)
    (* One-shot continuations. *)
    | ContV (r : loc) (k : list frame)
    (* Multi-shot continuations. *)
    | KontV (k : list frame)
    (* Products *)
    | PairV (v1 v2 : val)
    (* Sums *)
    | InjLV (v : val)
    | InjRV (v : val)

  with frame :=
    (* Application (right-to-left evaluation order). *)
    | AppRCtx (e1 : expr) (* e1 [ ] *)
    | AppLCtx (v2 : val) (* [ ] v2 *)
    (* Effects. *)
    | DoCtx (l : label) (* Do l [ ] *)
    | HandleCtx (hs : handler_semantics)
                (m : mode) (l : label) (e2 e3 : expr) (* Handle hs m l [ ] e2 e3 *)
    (* Base types and their operations. *)
    | UnOpCtx (op : un_op) (* UnOp op [] *)
    | BinOpLCtx (op : bin_op) (v2 : val) (* BinOp op [ ] v2 *)
    | BinOpRCtx (op : bin_op) (e1 : expr) (* BinOp op e1 [ ] *)
    | IfCtx (e1 e2 : expr) (* If [ ] e1 e2 *)
    (* Products. *)
    | PairLCtx (v2 : val) (* Pair [ ] v2 *)
    | PairRCtx (e1 : expr) (* Pair e1 [ ] *)
    | FstCtx (* Fst [ ] *)
    | SndCtx (* Snd [ ] *)
    (* Sums. *)
    | InjLCtx (* InjL [ ] *)
    | InjRCtx (* InjR [ ] *)
    | CaseCtx (e1 : expr) (e2 : expr) (* Case [ ] e1 e2 *)
    (* Heap. *)
    | AllocNRCtx (e1 : expr) (* AllocN e1 [ ] *)
    | AllocNLCtx (v2 : val) (* AllocN [ ] v2 *)
    | FreeCtx (* Free [ ] *)
    | LoadCtx (* ![ ] *)
    | StoreRCtx (e1 : expr) (* e1 <- [ ]*)
    | StoreLCtx (v2 : val) (* [ ] <- v2 *)
    | CmpXchgRCtx (e0 : expr) (e1 : expr) (* CmpXchg e0 e1 [ ] *)
    | CmpXchgMCtx (e0 : expr) (v2 : val) (* CmpXchg e0 [ ] v2 *)
    | CmpXchgLCtx (v1 : val) (v2 : val) (* CmpXchg [ ] v1 v2 *)
    | XchgRCtx (e1 : expr) (* Xchg e1 [ ] *)
    | XchgLCtx (v2 : val) (* Xchg [ ] v2 *)
    | FaaRCtx (e1 : expr) (* Faa e1 [ ] *)
    | FaaLCtx (v2 : val). (* Faa [ ] v2 *)

  (* Evaluation contexts. *)
  Definition ectx := list frame.

  (* State. *)
  Record state : Type := {
    next_label : label;
    heap : gmap loc (option val)
  }.

End eff_lang.


(* ========================================================================== *)
(** * Induction Principle. *)

Section induction_principle.
  Variables (P : expr  → Type)
            (Q : val   → Type)
            (R : frame → Type)
            (S : ectx  → Type).

  Hypothesis
  (* Expressions. *)
    (* Values. *)
    (Val_case : ∀ v, Q v → P (Val v))
    (* Effects. *)
    (Effect_case : ∀ s e, P e → P (Effect s e))
    (Do_case : ∀ n e, P e → P (Do n e))
    (Handle_case : ∀ hs m n e1 e2 e3, P e1 → P e2 → P e3 → P (Handle hs m n e1 e2 e3))
    (* λ-calculus. *)
    (Var_case : ∀ b, P (Var b))
    (Rec_case : ∀ f x e, P e → P (Rec f x e))
    (App_case : ∀ e1 e2, P e1 → P e2 → P (App e1 e2))
    (* Base types and their operations *)
    (UnOp_case : ∀ op e, P e → P (UnOp op e))
    (BinOp_case : ∀ op e1 e2, P e1 → P e2 → P (BinOp op e1 e2))
    (If_case : ∀ e0 e1 e2, P e0 → P e1 → P e2 → P (If e0 e1 e2))
    (* Products *)
    (Pair_case : ∀ e1 e2, P e1 → P e2 → P (Pair e1 e2))
    (Fst_case : ∀ e, P e → P (Fst e))
    (Snd_case : ∀ e, P e → P (Snd e))
    (* Sums *)
    (InjL_case : ∀ e, P e → P (InjL e))
    (InjR_case : ∀ e, P e → P (InjR e))
    (Case_case : ∀ e0 e1 e2, P e0 → P e1 → P e2 → P (Case e0 e1 e2))
    (* Heap *)
    (AllocN_case : ∀ e1 e2, P e1 → P e2 → P (AllocN e1 e2))
    (Free_case : ∀ e, P e → P (Free e))
    (Load_case : ∀ e, P e → P (Load e))
    (Store_case : ∀ e1 e2, P e1 → P e2 → P (Store e1 e2))
    (CmpXchg_case : ∀ e0 e1 e2, P e0 → P e1 → P e2 → P (CmpXchg e0 e1 e2))
    (Xchg_case : ∀ e1 e2, P e1 → P e2 → P (Xchg e1 e2))
    (FAA_case : ∀ e1 e2, P e1 → P e2 → P (FAA e1 e2))
    (* Concurrency *)
    (Fork_case : ∀ e, P e → P (Fork e))

  (* Values. *)
    (* Base values. *)
    (LitV_case : ∀ l, Q (LitV l))
    (* First-class functions. *)
    (RecV_case : ∀ f x e, P e → Q (RecV f x e))
    (* One-shot continuations. *)
    (ContV_case : ∀ l k, S k → Q (ContV l k))
    (* Multi-shot continuations. *)
    (KontV_case : ∀ k, S k → Q (KontV k))
    (* Products *)
    (PairV_case : ∀ v1 v2, Q v1 → Q v2 → Q (PairV v1 v2))
    (* Sums *)
    (InjLV_case : ∀ v, Q v → Q (InjLV v))
    (InjRV_case : ∀ v, Q v → Q (InjRV v))

  (* Frames. *)
    (* Application. *)
    (AppLCtx_case : ∀ v2, Q v2 → R (AppLCtx v2))
    (AppRCtx_case : ∀ e1, P e1 → R (AppRCtx e1))
    (* Effects. *)
    (DoCtx_case : ∀ n, R (DoCtx n))
    (HandleCtx_case : ∀ hs m n e2 e3, P e2 → P e3 → R (HandleCtx hs m n e2 e3))
    (* Operations *)
    (UnOpCtx_case : ∀ op, R (UnOpCtx op))
    (BinOpLCtx_case : ∀ op v2, Q v2 → R (BinOpLCtx op v2))
    (BinOpRCtx_case : ∀ op e1, P e1 → R (BinOpRCtx op e1))
    (IfCtx_case : ∀ e1 e2, P e1 → P e2 → R (IfCtx e1 e2))
    (* Products *)
    (PairLCtx_case : ∀ v2, Q v2 → R (PairLCtx v2))
    (PairRCtx_case : ∀ e1, P e1 → R (PairRCtx e1))
    (FstCtx_case : R FstCtx)
    (SndCtx_case : R SndCtx)
    (* Sums *)
    (InjLCtx_case : R InjLCtx)
    (InjRCtx_case : R InjRCtx)
    (CaseCtx_case :∀ e1 e2, P e1 → P e2 → R (CaseCtx e1 e2))
    (* Heap *)
    (AllocNLCtx_case : ∀ v2, Q v2 → R (AllocNLCtx v2))
    (AllocNRCtx_case : ∀ e1, P e1 → R (AllocNRCtx e1))
    (FreeCtx_case : R FreeCtx)
    (LoadCtx_case : R LoadCtx)
    (StoreLCtx_case : ∀ v2, Q v2 → R (StoreLCtx v2))
    (StoreRCtx_case : ∀ e1, P e1 → R (StoreRCtx e1))
    (CmpXchgLCtx_case : ∀ v1 v2, Q v1 → Q v2 → R (CmpXchgLCtx v1 v2))
    (CmpXchgMCtx_case : ∀ e0 v2, P e0 → Q v2 → R (CmpXchgMCtx e0 v2))
    (CmpXchgRCtx_case : ∀ e0 e1, P e0 → P e1 → R (CmpXchgRCtx e0 e1))
    (XchgLCtx_case : ∀ v2, Q v2 → R (XchgLCtx v2))
    (XchgRCtx_case : ∀ e1, P e1 → R (XchgRCtx e1))
    (FaaLCtx_case : ∀ v2, Q v2 → R (FaaLCtx v2))
    (FaaRCtx_case : ∀ e1, P e1 → R (FaaRCtx e1))

  (* Evaluation contexts. *)
    (EmptyCtx_case : S [])
    (ConsCtx_case : ∀ (f : frame) (k : ectx), R f → S k → S (f :: k)).

  Definition expr_ind_pre
    (expr_ind : ∀ e, P e)
    (val_ind : ∀ v, Q v)
    (frame_ind : ∀ f, R f)
    : ∀ e, P e := λ e,
    match e with
    | Val v =>
        Val_case v (val_ind v)
    | Effect s e =>
        Effect_case s e (expr_ind e)
    | Do n e =>
        Do_case n e (expr_ind e)
    | Handle hs m n e1 e2 e3 =>
        Handle_case hs m n e1 e2 e3 (expr_ind e1) (expr_ind e2) (expr_ind e3)
    | Var b =>
        Var_case b
    | Rec f x e =>
        Rec_case f x e (expr_ind e)
    | App e1 e2 =>
        App_case e1 e2 (expr_ind e1) (expr_ind e2)
    | UnOp op e =>
        UnOp_case op e (expr_ind e)
    | BinOp op e1 e2 =>
        BinOp_case op e1 e2 (expr_ind e1) (expr_ind e2)
    | If e0 e1 e2 =>
        If_case e0 e1 e2 (expr_ind e0) (expr_ind e1) (expr_ind e2)
    | Pair e1 e2 =>
        Pair_case e1 e2 (expr_ind e1) (expr_ind e2)
    | Fst e =>
        Fst_case e (expr_ind e)
    | Snd e =>
        Snd_case e (expr_ind e)
    | InjL e =>
        InjL_case e (expr_ind e)
    | InjR e =>
        InjR_case e (expr_ind e)
    | Case e0 e1 e2 =>
        Case_case e0 e1 e2 (expr_ind e0) (expr_ind e1) (expr_ind e2)
    | AllocN e1 e2 =>
        AllocN_case e1 e2 (expr_ind e1) (expr_ind e2)
    | Free e =>
        Free_case e (expr_ind e)
    | Load e =>
        Load_case e (expr_ind e)
    | Store e1 e2 =>
        Store_case e1 e2 (expr_ind e1) (expr_ind e2)
    | CmpXchg e0 e1 e2 =>
        CmpXchg_case e0 e1 e2 (expr_ind e0) (expr_ind e1) (expr_ind e2)
    | Xchg e1 e2 =>
        Xchg_case e1 e2 (expr_ind e1) (expr_ind e2)
    | FAA e1 e2 =>
        FAA_case e1 e2 (expr_ind e1) (expr_ind e2)
    | Fork e =>
        Fork_case e (expr_ind e)
    end.

  Definition val_ind_pre
    (expr_ind  : ∀ e, P e)
    (val_ind : ∀ v, Q v)
    (frame_ind : ∀ f, R f)
    : ∀ v, Q v := λ v,
    match v with
    | LitV l =>
        LitV_case l
    | RecV f x e =>
        RecV_case f x e (expr_ind e)
    | ContV l k =>
        ContV_case l k (
          (fix ectx_ind k {struct k} : S k :=
            match k with
            | [] => EmptyCtx_case
            | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
          end) k)
    | KontV k =>
        KontV_case k (
          (fix ectx_ind k {struct k} : S k :=
            match k with
            | [] => EmptyCtx_case
            | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
          end) k)
    | PairV v1 v2 =>
        PairV_case v1 v2 (val_ind v1) (val_ind v2)
    | InjLV v =>
        InjLV_case v (val_ind v)
    | InjRV v =>
        InjRV_case v (val_ind v)
    end.

  Definition frame_ind_pre
    (expr_ind : ∀ e, P e)
    (val_ind : ∀ v, Q v)
    : ∀ f, R f := λ f,
    match f with
    | AppLCtx v2 =>
        AppLCtx_case v2 (val_ind v2)
    | AppRCtx e1 =>
        AppRCtx_case e1 (expr_ind e1)
    | DoCtx l =>
        DoCtx_case l
    | HandleCtx hs m n e2 e3 =>
        HandleCtx_case hs m n e2 e3 (expr_ind e2) (expr_ind e3)
    | UnOpCtx op =>
        UnOpCtx_case op
    | BinOpLCtx op v2 =>
        BinOpLCtx_case op v2 (val_ind v2)
    | BinOpRCtx op e1 =>
        BinOpRCtx_case op e1 (expr_ind e1)
    | IfCtx e1 e2 =>
        IfCtx_case e1 e2 (expr_ind e1) (expr_ind e2)
    | PairLCtx v2 =>
        PairLCtx_case v2 (val_ind v2)
    | PairRCtx e1 =>
        PairRCtx_case e1 (expr_ind e1)
    | FstCtx =>
        FstCtx_case
    | SndCtx =>
        SndCtx_case
    | InjLCtx =>
        InjLCtx_case
    | InjRCtx =>
        InjRCtx_case
    | CaseCtx e1 e2 =>
        CaseCtx_case e1 e2 (expr_ind e1) (expr_ind e2)
    | AllocNLCtx v2 =>
        AllocNLCtx_case v2 (val_ind v2)
    | AllocNRCtx e1 =>
        AllocNRCtx_case e1 (expr_ind e1)
    | FreeCtx =>
        FreeCtx_case
    | LoadCtx =>
        LoadCtx_case
    | StoreLCtx v2 =>
        StoreLCtx_case v2 (val_ind v2)
    | StoreRCtx e1 =>
        StoreRCtx_case e1 (expr_ind e1)
    | CmpXchgLCtx v1 v2 =>
        CmpXchgLCtx_case v1 v2 (val_ind v1) (val_ind v2)
    | CmpXchgMCtx e0 v2 =>
        CmpXchgMCtx_case e0 v2 (expr_ind e0) (val_ind v2)
    | CmpXchgRCtx e0 e1 =>
        CmpXchgRCtx_case e0 e1 (expr_ind e0) (expr_ind e1)
    | XchgLCtx v2 =>
        XchgLCtx_case v2 (val_ind v2)
    | XchgRCtx e1 =>
        XchgRCtx_case e1 (expr_ind e1)
    | FaaLCtx v2 =>
        FaaLCtx_case v2 (val_ind v2)
    | FaaRCtx e1 =>
        FaaRCtx_case e1 (expr_ind e1)
    end.

  Definition ectx_ind_pre
    (frame_ind : ∀ f, R f)
    (ectx_ind : ∀ k, S k)
    : ∀ k, S k := λ k,
    match k with
    | [] => EmptyCtx_case
    | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
    end.

  Definition expr_ind' : ∀ e, P e :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for expr_ind.

  Definition val_ind' : ∀ v, Q v :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for val_ind.

  Definition frame_ind' : ∀ f, R f :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for frame_ind.

  Definition ectx_ind' : ∀ k, S k :=
    fix ectx_ind k := ectx_ind_pre frame_ind' ectx_ind k.

End induction_principle.


(* ========================================================================== *)
(** * Properties. *)

(* -------------------------------------------------------------------------- *)
(** Decidable Equality. *)

(* We prove that [expr], [val], [frame], and [ectx] have decidable equality. *)

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.

Global Instance mode_eq_dec : EqDecision mode.
Proof. solve_decision. Defined.

Global Instance handler_semantics_eq_dec : EqDecision handler_semantics.
Proof. solve_decision. Defined.

Global Instance label_eq_dec : EqDecision label.
Proof. solve_decision. Defined.

Global Instance eff_val_eq_dec : EqDecision eff_val.
Proof. solve_decision. Defined.

Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.

Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.

Section eq_decidable.
  Notation eq_dec :=
    (λ (A : Type), λ (x : A), ∀ y, Decision (x = y)) (only parsing).

  Notation P := (eq_dec  expr) (only parsing).
  Notation Q := (eq_dec   val) (only parsing).
  Notation R := (eq_dec frame) (only parsing).
  Notation S := (eq_dec  ectx) (only parsing).

  (* Expressions. *)
  Definition eq_dec_Val_case v (Hv : Q v) : P (Val v).
    refine (λ e',
      match e' with
      | Val v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Do_case n e (He : P e) : P (Do n e).
    refine (λ e',
      match e' with
      | Do n' e' => cast_if_and (decide (n = n')) (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Effect_case s e (He : P e) : P (Effect s e).
    refine (λ e',
      match e' with
      | Effect s' e' => cast_if_and (decide (s = s')) (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Handle_case hs m n e1 e2 e3
    (He1: P e1) (He2 : P e2) (He3 : P e3) : P (Handle hs m n e1 e2 e3).
    refine (λ e',
      match e' with
      | Handle hs' m' n' e1' e2' e3' =>
          cast_if_and6
            (decide (hs = hs')) (decide (m = m')) (decide (n = n'))
            (He1 e1') (He2 e2') (He3 e3')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Var_case x : P (Var x).
    refine (λ e',
      match e' with
      | Var x' => cast_if (decide (x = x'))
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Rec_case f x e (He : P e) : P (Rec f x e).
    refine (λ e',
      match e' with
      | Rec f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_App_case e1 e2 (He1 : P e1) (He2 : P e2) : P (App e1 e2).
    refine (λ e',
      match e' with
      | App e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_UnOp_case op e (He : P e) : P (UnOp op e).
    refine (λ e',
      match e' with
      | UnOp op' e' => cast_if_and (decide (op = op')) (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_BinOp_case op e1 e2 (He1 : P e1) (He2 : P e2) : P (BinOp op e1 e2).
    refine (λ e',
      match e' with
      | BinOp op' e1' e2' => cast_if_and3 (decide (op = op')) (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_If_case e0 e1 e2 (He0 : P e0) (He1 : P e1) (He2 : P e2) : P (If e0 e1 e2).
    refine (λ e',
      match e' with
      | If e0' e1' e2' => cast_if_and3 (He0 e0') (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Pair_case e1 e2 (He1 : P e1) (He2 : P e2) : P (Pair e1 e2).
    refine (λ e',
      match e' with
      | Pair e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Fst_case e (He : P e) : P (Fst e).
    refine (λ e',
      match e' with
      | Fst e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Snd_case e (He : P e) : P (Snd e).
    refine (λ e',
      match e' with
      | Snd e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjL_case e (He : P e) : P (InjL e).
    refine (λ e',
      match e' with
      | InjL e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjR_case e (He : P e) : P (InjR e).
    refine (λ e',
      match e' with
      | InjR e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Case_case e0 e1 e2 (He0 : P e0) (He1 : P e1) (He2 : P e2) : P (Case e0 e1 e2).
    refine (λ e',
      match e' with
      | Case e0' e1' e2' => cast_if_and3 (He0 e0') (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_AllocN_case e1 e2 (He1 : P e1) (He2 : P e2) : P (AllocN e1 e2).
    refine (λ e',
      match e' with
      | AllocN e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Free_case e (He : P e) : P (Free e).
    refine (λ e',
      match e' with
      | Free e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Load_case e (He : P e) : P (Load e).
    refine (λ e',
      match e' with
      | Load e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Store_case e1 e2 (He1 : P e1) (He2 : P e2) : P (Store e1 e2).
    refine (λ e',
      match e' with
      | Store e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_CmpXchg_case e0 e1 e2 (He0 : P e0) (He1 : P e1) (He2 : P e2) : P (CmpXchg e0 e1 e2).
    refine (λ e',
      match e' with
      | CmpXchg e0' e1' e2' => cast_if_and3 (He0 e0') (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Xchg_case e1 e2 (He1 : P e1) (He2 : P e2) : P (Xchg e1 e2).
    refine (λ e',
      match e' with
      | Xchg e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_FAA_case e1 e2 (He1 : P e1) (He2 : P e2) : P (FAA e1 e2).
    refine (λ e',
      match e' with
      | FAA e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_Fork_case e (He : P e) : P (Fork e).
    refine (λ e',
      match e' with
      | Fork e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Defined.

  (* Values. *)
  Definition eq_dec_LitV_case l : Q (LitV l).
    refine (λ v',
      match v' with
      | LitV l' => cast_if (decide (l = l'))
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_RecV_case f x e (He : P e) : Q (RecV f x e).
    refine (λ v',
      match v' with
      | RecV f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (He e')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_ContV_case l k (Hk : S k) : Q (ContV l k).
    refine (λ v',
      match v' with
      | ContV l' k' => cast_if_and (decide (l = l')) (Hk k')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_KontV_case k (Hk : S k) : Q (KontV k).
    refine (λ v',
      match v' with
      | KontV k' => cast_if (Hk k')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_PairV_case v1 v2 (Hv1 : Q v1) (Hv2 : Q v2) : Q (PairV v1 v2).
    refine (λ v',
      match v' with
      | PairV v1' v2' => cast_if_and (Hv1 v1') (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjLV_case v (Hv : Q v) : Q (InjLV v).
    refine (λ v',
      match v' with
      | InjLV v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjRV_case v (Hv : Q v) : Q (InjRV v).
    refine (λ v',
      match v' with
      | InjRV v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Defined.

  (* Frames. *)
  Definition eq_dec_AppLCtx_case v2 (Hv2 : Q v2) : R (AppLCtx v2).
    refine (λ f',
      match f' with
      | AppLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_AppRCtx_case e1 (He1 : P e1) : R (AppRCtx e1).
    refine (λ f',
      match f' with
      | AppRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_DoCtx_case l : R (DoCtx l).
    refine (λ f',
      match f' with
      | DoCtx l' => cast_if (decide (l = l'))
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_HandleCtx_case hs m l e2 e3
    (He2 : P e2) (He3 : P e3) : R (HandleCtx hs m l e2 e3).
    refine (λ f',
      match f' with
      | HandleCtx hs' m' l' e2' e3' =>
          cast_if_and5
            (decide (hs = hs')) (decide (m = m')) (decide (l = l')) (He2 e2') (He3 e3')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_UnOpCtx_case op : R (UnOpCtx op).
    refine (λ f',
      match f' with
      | UnOpCtx op' => cast_if (decide (op = op'))
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_BinOpLCtx_case op v2 (Hv2 : Q v2) : R (BinOpLCtx op v2).
    refine (λ f',
      match f' with
      | BinOpLCtx op' v2' => cast_if_and (decide (op = op')) (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_BinOpRCtx_case op e1 (He1 : P e1) : R (BinOpRCtx op e1).
    refine (λ f',
      match f' with
      | BinOpRCtx op' e1' => cast_if_and (decide (op = op')) (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_IfCtx_case e1 e2 (He1 : P e1) (He2 : P e2) : R (IfCtx e1 e2).
    refine (λ f',
      match f' with
      | IfCtx e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_PairLCtx_case v2 (Hv2 : Q v2) : R (PairLCtx v2).
    refine (λ f',
      match f' with
      | PairLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_PairRCtx_case e1 (He1 : P e1) : R (PairRCtx e1).
    refine (λ f',
      match f' with
      | PairRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_FstCtx_case : R FstCtx.
    refine (λ f',
      match f' with
      | FstCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_SndCtx_case : R SndCtx.
    refine (λ f',
      match f' with
      | SndCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjLCtx_case : R InjLCtx.
    refine (λ f',
      match f' with
      | InjLCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_InjRCtx_case : R InjRCtx.
    refine (λ f',
      match f' with
      | InjRCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_CaseCtx_case e1 e2 (He1 : P e1) (He2 : P e2) : R (CaseCtx e1 e2).
    refine (λ f',
      match f' with
      | CaseCtx e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_AllocNLCtx_case v2 (Hv2 : Q v2) : R (AllocNLCtx v2).
    refine (λ f',
      match f' with
      | AllocNLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_AllocNRCtx_case e1 (He1 : P e1) : R (AllocNRCtx e1).
    refine (λ f',
      match f' with
      | AllocNRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_FreeCtx_case : R FreeCtx.
    refine (λ f',
      match f' with
      | FreeCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_LoadCtx_case : R LoadCtx.
    refine (λ f',
      match f' with
      | LoadCtx => left _
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_StoreLCtx_case v2 (Hv2 : Q v2) : R (StoreLCtx v2).
    refine (λ f',
      match f' with
      | StoreLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_StoreRCtx_case e1 (He1 : P e1) : R (StoreRCtx e1).
    refine (λ f',
      match f' with
      | StoreRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_CmpXchgLCtx_case v1 v2 (Hv1 : Q v1) (Hv2 : Q v2) : R (CmpXchgLCtx v1 v2).
    refine (λ f',
      match f' with
      | CmpXchgLCtx v1' v2' => cast_if_and (Hv1 v1') (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_CmpXchgMCtx_case e0 v2 (He0 : P e0) (Hv2 : Q v2) : R (CmpXchgMCtx e0 v2).
    refine (λ f',
      match f' with
      | CmpXchgMCtx e0' v2' => cast_if_and (He0 e0') (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_CmpXchgRCtx_case e0 e1 (He0 : P e0) (He1 : P e1) : R (CmpXchgRCtx e0 e1).
    refine (λ f',
      match f' with
      | CmpXchgRCtx e0' e1' => cast_if_and (He0 e0') (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_XchgLCtx_case v2 (Hv2 : Q v2) : R (XchgLCtx v2).
    refine (λ f',
      match f' with
      | XchgLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_XchgRCtx_case e1 (He1 : P e1) : R (XchgRCtx e1).
    refine (λ f',
      match f' with
      | XchgRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_FaaLCtx_case v2 (Hv2 : Q v2) : R (FaaLCtx v2).
    refine (λ f',
      match f' with
      | FaaLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Defined.

  Definition eq_dec_FaaRCtx_case e1 (He1 : P e1) : R (FaaRCtx e1).
    refine (λ f',
      match f' with
      | FaaRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Defined.

  (* Evaluation contexts. *)
  Definition eq_dec_EmptyCtx_case : S [].
    by refine (λ f', match f' with [] => left _ | _ => right _ end).
  Defined.

  Definition eq_dec_ConsCtx_case f k (Hf : R f) (Hk : S k) : S (f :: k).
    refine (λ f',
      match f' with
      | f' :: k' => cast_if_and (Hf f') (Hk k')
      | _ => right _
      end); congruence.
  Defined.


  Global Instance expr_eq_dec : EqDecision expr :=
    expr_ind' P Q R S
      (* Expressions. *)
      eq_dec_Val_case
      eq_dec_Effect_case eq_dec_Do_case eq_dec_Handle_case
      eq_dec_Var_case eq_dec_Rec_case eq_dec_App_case
      eq_dec_UnOp_case eq_dec_BinOp_case eq_dec_If_case
      eq_dec_Pair_case eq_dec_Fst_case eq_dec_Snd_case
      eq_dec_InjL_case eq_dec_InjR_case eq_dec_Case_case
      eq_dec_AllocN_case eq_dec_Free_case eq_dec_Load_case eq_dec_Store_case
      eq_dec_CmpXchg_case eq_dec_Xchg_case eq_dec_FAA_case eq_dec_Fork_case
      (* Values. *)
      eq_dec_LitV_case eq_dec_RecV_case eq_dec_ContV_case eq_dec_KontV_case
      eq_dec_PairV_case eq_dec_InjLV_case eq_dec_InjRV_case
      (* Frames. *)
      eq_dec_AppLCtx_case eq_dec_AppRCtx_case
      eq_dec_DoCtx_case eq_dec_HandleCtx_case
      eq_dec_UnOpCtx_case eq_dec_BinOpLCtx_case eq_dec_BinOpRCtx_case eq_dec_IfCtx_case
      eq_dec_PairLCtx_case eq_dec_PairRCtx_case eq_dec_FstCtx_case eq_dec_SndCtx_case
      eq_dec_InjLCtx_case eq_dec_InjRCtx_case eq_dec_CaseCtx_case
      eq_dec_AllocNLCtx_case eq_dec_AllocNRCtx_case eq_dec_FreeCtx_case eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case eq_dec_StoreRCtx_case
      eq_dec_CmpXchgLCtx_case eq_dec_CmpXchgMCtx_case eq_dec_CmpXchgRCtx_case
      eq_dec_XchgLCtx_case eq_dec_XchgRCtx_case eq_dec_FaaLCtx_case eq_dec_FaaRCtx_case
      (* Evaluation contexts. *)
      eq_dec_EmptyCtx_case eq_dec_ConsCtx_case.

  Global Instance val_eq_dec : EqDecision val :=
    val_ind' P Q R S
      (* Expressions. *)
      eq_dec_Val_case
      eq_dec_Effect_case eq_dec_Do_case eq_dec_Handle_case
      eq_dec_Var_case eq_dec_Rec_case eq_dec_App_case
      eq_dec_UnOp_case eq_dec_BinOp_case eq_dec_If_case
      eq_dec_Pair_case eq_dec_Fst_case eq_dec_Snd_case
      eq_dec_InjL_case eq_dec_InjR_case eq_dec_Case_case
      eq_dec_AllocN_case eq_dec_Free_case eq_dec_Load_case eq_dec_Store_case
      eq_dec_CmpXchg_case eq_dec_Xchg_case eq_dec_FAA_case eq_dec_Fork_case
      (* Values. *)
      eq_dec_LitV_case eq_dec_RecV_case eq_dec_ContV_case eq_dec_KontV_case
      eq_dec_PairV_case eq_dec_InjLV_case eq_dec_InjRV_case
      (* Frames. *)
      eq_dec_AppLCtx_case eq_dec_AppRCtx_case
      eq_dec_DoCtx_case eq_dec_HandleCtx_case
      eq_dec_UnOpCtx_case eq_dec_BinOpLCtx_case eq_dec_BinOpRCtx_case eq_dec_IfCtx_case
      eq_dec_PairLCtx_case eq_dec_PairRCtx_case eq_dec_FstCtx_case eq_dec_SndCtx_case
      eq_dec_InjLCtx_case eq_dec_InjRCtx_case eq_dec_CaseCtx_case
      eq_dec_AllocNLCtx_case eq_dec_AllocNRCtx_case eq_dec_FreeCtx_case eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case eq_dec_StoreRCtx_case
      eq_dec_CmpXchgLCtx_case eq_dec_CmpXchgMCtx_case eq_dec_CmpXchgRCtx_case
      eq_dec_XchgLCtx_case eq_dec_XchgRCtx_case eq_dec_FaaLCtx_case eq_dec_FaaRCtx_case
      (* Evaluation contexts. *)
      eq_dec_EmptyCtx_case eq_dec_ConsCtx_case.

  Global Instance frame_eq_dec : EqDecision frame :=
    frame_ind' P Q R S
      (* Expressions. *)
      eq_dec_Val_case
      eq_dec_Effect_case eq_dec_Do_case eq_dec_Handle_case
      eq_dec_Var_case eq_dec_Rec_case eq_dec_App_case
      eq_dec_UnOp_case eq_dec_BinOp_case eq_dec_If_case
      eq_dec_Pair_case eq_dec_Fst_case eq_dec_Snd_case
      eq_dec_InjL_case eq_dec_InjR_case eq_dec_Case_case
      eq_dec_AllocN_case eq_dec_Free_case eq_dec_Load_case eq_dec_Store_case
      eq_dec_CmpXchg_case eq_dec_Xchg_case eq_dec_FAA_case eq_dec_Fork_case
      (* Values. *)
      eq_dec_LitV_case eq_dec_RecV_case eq_dec_ContV_case eq_dec_KontV_case
      eq_dec_PairV_case eq_dec_InjLV_case eq_dec_InjRV_case
      (* Frames. *)
      eq_dec_AppLCtx_case eq_dec_AppRCtx_case
      eq_dec_DoCtx_case eq_dec_HandleCtx_case
      eq_dec_UnOpCtx_case eq_dec_BinOpLCtx_case eq_dec_BinOpRCtx_case eq_dec_IfCtx_case
      eq_dec_PairLCtx_case eq_dec_PairRCtx_case eq_dec_FstCtx_case eq_dec_SndCtx_case
      eq_dec_InjLCtx_case eq_dec_InjRCtx_case eq_dec_CaseCtx_case
      eq_dec_AllocNLCtx_case eq_dec_AllocNRCtx_case eq_dec_FreeCtx_case eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case eq_dec_StoreRCtx_case
      eq_dec_CmpXchgLCtx_case eq_dec_CmpXchgMCtx_case eq_dec_CmpXchgRCtx_case
      eq_dec_XchgLCtx_case eq_dec_XchgRCtx_case eq_dec_FaaLCtx_case eq_dec_FaaRCtx_case
      (* Evaluation contexts. *)
      eq_dec_EmptyCtx_case eq_dec_ConsCtx_case.

  Global Instance ectx_eq_dec : EqDecision ectx :=
    ectx_ind' P Q R S
      (* Expressions. *)
      eq_dec_Val_case
      eq_dec_Effect_case eq_dec_Do_case eq_dec_Handle_case
      eq_dec_Var_case eq_dec_Rec_case eq_dec_App_case
      eq_dec_UnOp_case eq_dec_BinOp_case eq_dec_If_case
      eq_dec_Pair_case eq_dec_Fst_case eq_dec_Snd_case
      eq_dec_InjL_case eq_dec_InjR_case eq_dec_Case_case
      eq_dec_AllocN_case eq_dec_Free_case eq_dec_Load_case eq_dec_Store_case
      eq_dec_CmpXchg_case eq_dec_Xchg_case eq_dec_FAA_case eq_dec_Fork_case
      (* Values. *)
      eq_dec_LitV_case eq_dec_RecV_case eq_dec_ContV_case eq_dec_KontV_case
      eq_dec_PairV_case eq_dec_InjLV_case eq_dec_InjRV_case
      (* Frames. *)
      eq_dec_AppLCtx_case eq_dec_AppRCtx_case
      eq_dec_DoCtx_case eq_dec_HandleCtx_case
      eq_dec_UnOpCtx_case eq_dec_BinOpLCtx_case eq_dec_BinOpRCtx_case eq_dec_IfCtx_case
      eq_dec_PairLCtx_case eq_dec_PairRCtx_case eq_dec_FstCtx_case eq_dec_SndCtx_case
      eq_dec_InjLCtx_case eq_dec_InjRCtx_case eq_dec_CaseCtx_case
      eq_dec_AllocNLCtx_case eq_dec_AllocNRCtx_case eq_dec_FreeCtx_case eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case eq_dec_StoreRCtx_case
      eq_dec_CmpXchgLCtx_case eq_dec_CmpXchgMCtx_case eq_dec_CmpXchgRCtx_case
      eq_dec_XchgLCtx_case eq_dec_XchgRCtx_case eq_dec_FaaLCtx_case eq_dec_FaaRCtx_case
      (* Evaluation contexts. *)
      eq_dec_EmptyCtx_case eq_dec_ConsCtx_case.

End eq_decidable.


(* -------------------------------------------------------------------------- *)
(** Inhabited. *)

Instance label_inhabited : Inhabited label := populate (Label 0%nat).
Instance state_inhabited : Inhabited state := populate {| next_label := inhabitant; heap := inhabitant |}.
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance frame_inhabited : Inhabited frame := populate (AppLCtx inhabitant).
Instance ectx_inhabited : Inhabited ectx := populate inhabitant.


(* -------------------------------------------------------------------------- *)
(** Countable. *)

(* We prove that [expr], [val], [frame] and [ectx] are _countable_. *)

Global Instance label_countable : Countable label.
Proof. by apply (inj_countable' label_car Label); intros []. Qed.

Global Instance eff_val_countable : Countable eff_val.
Proof.
  refine (inj_countable'
    ((* Encoding. *) λ n,
       match n with EffName s => inl s | EffLabel l => inr l end)
    ((* Decoding. *) λ n,
       match n with inl s => EffName s | inr l => EffLabel l end) _);
  by intros [].
Qed.

Global Instance mode_countable : Countable mode.
Proof.
  refine (inj_countable'
    ((* Encoding. *) λ m, match m with OS => true | MS => false end)
    ((* Decoding. *) λ b, match b with true => OS | false => MS end)
  _ );
  by intros [].
Qed.

Global Instance handler_semantics_countable : Countable handler_semantics.
Proof.
  refine (inj_countable'
    ((* Encoding. *) λ hs, match hs with Deep => true | Shallow => false end)
    ((* Decoding. *) λ b, match b with true => Deep | false => Shallow end)
  _ );
  by intros [].
Qed.

Global Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable'
    ((* Encoding: base_lit → (unit + nat) + (bool + loc). *) λ l,
       match l with
       | LitUnit => inl (inl ())
       | LitInt n => inl (inr n)
       | LitBool b => inr (inl b)
       | LitLoc l => inr (inr l)
       end)
    ((* Decoding. *) λ l,
       match l with
       | inl (inl ()) => LitUnit
       | inl (inr n) => LitInt n
       | inr (inl b) => LitBool b
       | inr (inr l) => LitLoc l
       end) _);
  by intros [].
Qed.

Global Instance un_op_countable : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.

Section countable.
  (* The set of generic trees. *)
  Notation gtree :=
    (gen_tree (bin_op + un_op + base_lit + string + binder + label + eff_val + mode + handler_semantics))
    (only parsing).

  Notation enc_handler_semantics hs :=
    (GenLeaf (inr hs)) (only parsing).
  Notation enc_mode m :=
    (GenLeaf (inl (inr m))) (only parsing).
  Notation enc_eff_val n :=
    (GenLeaf (inl (inl (inr n)))) (only parsing).
  Notation enc_label l :=
    (GenLeaf (inl (inl (inl (inr l))))) (only parsing).
  Notation enc_binder b :=
    (GenLeaf (inl (inl (inl (inl (inr b)))))) (only parsing).
  Notation enc_string s :=
    (GenLeaf (inl (inl (inl (inl (inl (inr s))))))) (only parsing).
  Notation enc_base_lit l :=
    (GenLeaf (inl (inl (inl (inl (inl (inl (inr l)))))))) (only parsing).
  Notation enc_un_op op :=
    (GenLeaf (inl (inl (inl (inl (inl (inl (inl (inr op))))))))) (only parsing).
  Notation enc_bin_op op :=
    (GenLeaf (inl (inl (inl (inl (inl (inl (inl (inl op))))))))) (only parsing).

  (* Encoding. *)

  (* Expressions. *)
  Definition encode_Val (v : val) (gv : gtree) : gtree :=
    GenNode 0 [gv].
  Definition encode_Effect (s : string) (e : expr) (ge : gtree) : gtree :=
    GenNode 1 [enc_string s; ge].
  Definition encode_Do (n : eff_val) (e : expr) (ge : gtree) : gtree :=
    GenNode 2 [enc_eff_val n; ge].
  Definition encode_Handle (hs : handler_semantics) (m : mode) (n : eff_val) (e1 e2 e3 : expr) (ge1 ge2 ge3 : gtree) : gtree :=
    GenNode 3 [enc_handler_semantics hs; enc_mode m; enc_eff_val n; ge1; ge2; ge3].
  Definition encode_Var (x : string) : gtree :=
    GenNode 4 [enc_string x].
  Definition encode_Rec (f x : binder) (e : expr) (ge : gtree) : gtree :=
    GenNode 5 [enc_binder f; enc_binder x; ge].
  Definition encode_App (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 6 [ge1; ge2].
  Definition encode_UnOp (op : un_op) (e : expr) (ge : gtree) : gtree :=
    GenNode 7 [enc_un_op op; ge].
  Definition encode_BinOp (op : bin_op) (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 8 [enc_bin_op op; ge1; ge2].
  Definition encode_If (e0 e1 e2 : expr) (ge0 ge1 ge2 : gtree) : gtree :=
    GenNode 9 [ge0; ge1; ge2].
  Definition encode_Pair (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 10 [ge1; ge2].
  Definition encode_Fst (e : expr) (ge : gtree) : gtree :=
    GenNode 11 [ge].
  Definition encode_Snd (e : expr) (ge : gtree) : gtree :=
    GenNode 12 [ge].
  Definition encode_InjL (e : expr) (ge : gtree) : gtree :=
    GenNode 13 [ge].
  Definition encode_InjR (e : expr) (ge : gtree) : gtree :=
    GenNode 14 [ge].
  Definition encode_Case (e0 e1 e2 : expr) (ge0 ge1 ge2 : gtree) : gtree :=
    GenNode 15 [ge0; ge1; ge2].
  Definition encode_AllocN (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 16 [ge1; ge2].
  Definition encode_Free (e : expr) (ge : gtree) : gtree :=
    GenNode 17 [ge].
  Definition encode_Load (e : expr) (ge : gtree) : gtree :=
    GenNode 18 [ge].
  Definition encode_Store (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 19 [ge1; ge2].
  Definition encode_CmpXchg (e0 e1 e2 : expr) (ge0 ge1 ge2 : gtree) : gtree :=
    GenNode 20 [ge0; ge1; ge2].
  Definition encode_Xchg (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 21 [ge1; ge2].
  Definition encode_FAA (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 22 [ge1; ge2].
  Definition encode_Fork (e : expr) (ge : gtree) : gtree :=
    GenNode 23 [ge].


  (* Values. *)
  Definition encode_LitV (l : base_lit) : gtree :=
    GenNode 0 [enc_base_lit l].
  Definition encode_RecV (f x : binder) (e : expr) (ge : gtree) : gtree :=
    GenNode 1 [enc_binder f; enc_binder x; ge].
  Definition encode_ContV (l : loc) (k : ectx) (gk : gtree) : gtree :=
    GenNode 2 [enc_base_lit (LitLoc l); gk].
  Definition encode_KontV (k : ectx) (gk : gtree) : gtree :=
    GenNode 3 [gk].
  Definition encode_PairV (v1 v2 : val) (gv1 gv2 : gtree) : gtree :=
    GenNode 4 [gv1; gv2].
  Definition encode_InjLV (v : val) (gv : gtree) : gtree :=
    GenNode 5 [gv].
  Definition encode_InjRV (v : val) (gv : gtree) : gtree :=
    GenNode 6 [gv].

  (* Frames. *)
  Definition encode_AppLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 0 [gv2].
  Definition encode_AppRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 1 [ge1].
  Definition encode_DoCtx (l : label) : gtree :=
    GenNode 2 [enc_label l].
  Definition encode_HandleCtx (hs : handler_semantics) (m : mode) (l : label) (e2 e3 : expr) (ge2 ge3 : gtree) : gtree :=
    GenNode 3 [enc_handler_semantics hs; enc_mode m; enc_label l; ge2; ge3].
  Definition encode_UnOpCtx (op : un_op) : gtree :=
    GenNode 4 [enc_un_op op].
  Definition encode_BinOpLCtx (op : bin_op) (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 5 [enc_bin_op op; gv2].
  Definition encode_BinOpRCtx (op : bin_op) (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 6 [enc_bin_op op; ge1].
  Definition encode_IfCtx (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 7 [ge1; ge2].
  Definition encode_PairLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 8 [gv2].
  Definition encode_PairRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 9 [ge1].
  Definition encode_FstCtx : gtree :=
    GenNode 10 [].
  Definition encode_SndCtx : gtree :=
    GenNode 11 [].
  Definition encode_InjLCtx : gtree :=
    GenNode 12 [].
  Definition encode_InjRCtx : gtree :=
    GenNode 13 [].
  Definition encode_CaseCtx (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 14 [ge1; ge2].
  Definition encode_AllocNLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 15 [gv2].
  Definition encode_AllocNRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 16 [ge1].
  Definition encode_FreeCtx : gtree :=
    GenNode 17 [].
  Definition encode_LoadCtx : gtree :=
    GenNode 18 [].
  Definition encode_StoreLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 19 [gv2].
  Definition encode_StoreRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 20 [ge1].
  Definition encode_CmpXchgLCtx (v1 v2 : val) (gv1 gv2 : gtree) : gtree :=
    GenNode 21 [gv1; gv2].
  Definition encode_CmpXchgMCtx (e0 : expr) (v2 : val) (ge0 gv2 : gtree) : gtree :=
    GenNode 22 [ge0; gv2].
  Definition encode_CmpXchgRCtx (e0 e1 : expr) (ge0 ge1 : gtree) : gtree :=
    GenNode 23 [ge0; ge1].
  Definition encode_XchgLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 24 [gv2].
  Definition encode_XchgRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 25 [ge1].
  Definition encode_FaaLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 26 [gv2].
  Definition encode_FaaRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 27 [ge1].

  (* Evaluation contexts. *)
  Definition encode_EmptyCtx : gtree :=
    GenNode 0 [].
  Definition encode_ConsCtx (f : frame) (k : ectx) (gf gk : gtree) :=
    GenNode 1 [gf; gk].

  Definition encode_expr : expr → gtree :=
    expr_ind' _ _ _ _
      (* Expressions. *)
      encode_Val
      encode_Effect encode_Do encode_Handle
      encode_Var encode_Rec encode_App
      encode_UnOp encode_BinOp encode_If
      encode_Pair encode_Fst encode_Snd
      encode_InjL encode_InjR encode_Case
      encode_AllocN encode_Free encode_Load encode_Store
      encode_CmpXchg encode_Xchg encode_FAA encode_Fork
      (* Values. *)
      encode_LitV encode_RecV encode_ContV encode_KontV
      encode_PairV encode_InjLV encode_InjRV
      (* Frames. *)
      encode_AppLCtx encode_AppRCtx
      encode_DoCtx encode_HandleCtx
      encode_UnOpCtx encode_BinOpLCtx encode_BinOpRCtx encode_IfCtx
      encode_PairLCtx encode_PairRCtx encode_FstCtx encode_SndCtx
      encode_InjLCtx encode_InjRCtx encode_CaseCtx
      encode_AllocNLCtx encode_AllocNRCtx encode_FreeCtx encode_LoadCtx
      encode_StoreLCtx encode_StoreRCtx encode_CmpXchgLCtx encode_CmpXchgMCtx
      encode_CmpXchgRCtx encode_XchgLCtx encode_XchgRCtx encode_FaaLCtx encode_FaaRCtx
      (* Evaluation contexts. *)
      encode_EmptyCtx encode_ConsCtx.

  Definition encode_val : val → gtree :=
    val_ind' _ _ _ _
      (* Expressions. *)
      encode_Val
      encode_Effect encode_Do encode_Handle
      encode_Var encode_Rec encode_App
      encode_UnOp encode_BinOp encode_If
      encode_Pair encode_Fst encode_Snd
      encode_InjL encode_InjR encode_Case
      encode_AllocN encode_Free encode_Load encode_Store
      encode_CmpXchg encode_Xchg encode_FAA encode_Fork
      (* Values. *)
      encode_LitV encode_RecV encode_ContV encode_KontV
      encode_PairV encode_InjLV encode_InjRV
      (* Frames. *)
      encode_AppLCtx encode_AppRCtx
      encode_DoCtx encode_HandleCtx
      encode_UnOpCtx encode_BinOpLCtx encode_BinOpRCtx encode_IfCtx
      encode_PairLCtx encode_PairRCtx encode_FstCtx encode_SndCtx
      encode_InjLCtx encode_InjRCtx encode_CaseCtx
      encode_AllocNLCtx encode_AllocNRCtx encode_FreeCtx encode_LoadCtx
      encode_StoreLCtx encode_StoreRCtx encode_CmpXchgLCtx encode_CmpXchgMCtx
      encode_CmpXchgRCtx encode_XchgLCtx encode_XchgRCtx encode_FaaLCtx encode_FaaRCtx
      (* Evaluation contexts. *)
      encode_EmptyCtx encode_ConsCtx.

  Definition encode_frame : frame → gtree :=
    frame_ind' _ _ _ _
      (* Expressions. *)
      encode_Val
      encode_Effect encode_Do encode_Handle
      encode_Var encode_Rec encode_App
      encode_UnOp encode_BinOp encode_If
      encode_Pair encode_Fst encode_Snd
      encode_InjL encode_InjR encode_Case
      encode_AllocN encode_Free encode_Load encode_Store
      encode_CmpXchg encode_Xchg encode_FAA encode_Fork
      (* Values. *)
      encode_LitV encode_RecV encode_ContV encode_KontV
      encode_PairV encode_InjLV encode_InjRV
      (* Frames. *)
      encode_AppLCtx encode_AppRCtx
      encode_DoCtx encode_HandleCtx
      encode_UnOpCtx encode_BinOpLCtx encode_BinOpRCtx encode_IfCtx
      encode_PairLCtx encode_PairRCtx encode_FstCtx encode_SndCtx
      encode_InjLCtx encode_InjRCtx encode_CaseCtx
      encode_AllocNLCtx encode_AllocNRCtx encode_FreeCtx encode_LoadCtx
      encode_StoreLCtx encode_StoreRCtx encode_CmpXchgLCtx encode_CmpXchgMCtx
      encode_CmpXchgRCtx encode_XchgLCtx encode_XchgRCtx encode_FaaLCtx encode_FaaRCtx
      (* Evaluation contexts. *)
      encode_EmptyCtx encode_ConsCtx.

  Definition encode_ectx : ectx → gtree :=
    ectx_ind' _ _ _ _
      (* Expressions. *)
      encode_Val
      encode_Effect encode_Do encode_Handle
      encode_Var encode_Rec encode_App
      encode_UnOp encode_BinOp encode_If
      encode_Pair encode_Fst encode_Snd
      encode_InjL encode_InjR encode_Case
      encode_AllocN encode_Free encode_Load encode_Store
      encode_CmpXchg encode_Xchg encode_FAA encode_Fork
      (* Values. *)
      encode_LitV encode_RecV encode_ContV encode_KontV
      encode_PairV encode_InjLV encode_InjRV
      (* Frames. *)
      encode_AppLCtx encode_AppRCtx
      encode_DoCtx encode_HandleCtx
      encode_UnOpCtx encode_BinOpLCtx encode_BinOpRCtx encode_IfCtx
      encode_PairLCtx encode_PairRCtx encode_FstCtx encode_SndCtx
      encode_InjLCtx encode_InjRCtx encode_CaseCtx
      encode_AllocNLCtx encode_AllocNRCtx encode_FreeCtx encode_LoadCtx
      encode_StoreLCtx encode_StoreRCtx encode_CmpXchgLCtx encode_CmpXchgMCtx
      encode_CmpXchgRCtx encode_XchgLCtx encode_XchgRCtx encode_FaaLCtx encode_FaaRCtx
      (* Evaluation contexts. *)
      encode_EmptyCtx encode_ConsCtx.

  (** Decoding. *)
  Definition decode_expr_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val)
    (decode_ectx : gtree → ectx)
    : gtree → expr := λ ge,
    match ge with
    | GenNode 0 [gv] =>
        Val (decode_val gv)
    | GenNode 1 [enc_string s; ge] =>
        Effect s (decode_expr ge)
    | GenNode 2 [enc_eff_val n; ge] =>
        Do n (decode_expr ge)
    | GenNode 3 [enc_handler_semantics hs; enc_mode m; enc_eff_val n; ge1; ge2; ge3] =>
        Handle hs m n (decode_expr ge1) (decode_expr ge2) (decode_expr ge3)
    | GenNode 4 [enc_string x] =>
        Var x
    | GenNode 5 [enc_binder f; enc_binder x; ge] =>
        Rec f x (decode_expr ge)
    | GenNode 6 [ge1; ge2] =>
        App (decode_expr ge1) (decode_expr ge2)
    | GenNode 7 [enc_un_op op; ge] =>
        UnOp op (decode_expr ge)
    | GenNode 8 [enc_bin_op op; ge1; ge2] =>
        BinOp op (decode_expr ge1) (decode_expr ge2)
    | GenNode 9 [ge0; ge1; ge2] =>
        If (decode_expr ge0) (decode_expr ge1) (decode_expr ge2)
    | GenNode 10 [ge1; ge2] =>
        Pair (decode_expr ge1) (decode_expr ge2)
    | GenNode 11 [ge] =>
        Fst (decode_expr ge)
    | GenNode 12 [ge] =>
        Snd (decode_expr ge)
    | GenNode 13 [ge] =>
        InjL (decode_expr ge)
    | GenNode 14 [ge] =>
        InjR (decode_expr ge)
    | GenNode 15 [ge0; ge1; ge2] =>
        Case (decode_expr ge0) (decode_expr ge1) (decode_expr ge2)
    | GenNode 16 [ge1; ge2] =>
        AllocN (decode_expr ge1) (decode_expr ge2)
    | GenNode 17 [ge] =>
        Free (decode_expr ge)
    | GenNode 18 [ge] =>
        Load (decode_expr ge)
    | GenNode 19 [ge1; ge2] =>
        Store (decode_expr ge1) (decode_expr ge2)
    | GenNode 20 [ge0; ge1; ge2] =>
        CmpXchg (decode_expr ge0) (decode_expr ge1) (decode_expr ge2)
    | GenNode 21 [ge1; ge2] =>
        Xchg (decode_expr ge1) (decode_expr ge2)
    | GenNode 22 [ge1; ge2] =>
        FAA (decode_expr ge1) (decode_expr ge2)
    | GenNode 23 [ge] =>
        Fork (decode_expr ge)
    | _ =>
        inhabitant
    end.

  Definition decode_val_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val)
    (decode_ectx : gtree → ectx)
    : gtree → val := λ gv,
    match gv with
    | GenNode 0 [enc_base_lit l] =>
        LitV l
    | GenNode 1 [enc_binder f; enc_binder x; ge] =>
        RecV f x (decode_expr ge)
    | GenNode 2 [enc_base_lit (LitLoc l); gk] =>
        ContV l (decode_ectx gk)
    | GenNode 3 [gk] =>
        KontV (decode_ectx gk)
    | GenNode 4 [gv1; gv2] =>
        PairV (decode_val gv1) (decode_val gv2)
    | GenNode 5 [gv] =>
        InjLV (decode_val gv)
    | GenNode 6 [gv] =>
        InjRV (decode_val gv)
    | _ =>
        inhabitant
    end.

  Definition decode_frame_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val)
    : gtree → frame := λ gf,
    match gf with
    | GenNode 0 [gv2] =>
        AppLCtx (decode_val gv2)
    | GenNode 1 [ge1] =>
        AppRCtx (decode_expr ge1)
    | GenNode 2 [enc_label l] =>
        DoCtx l
    | GenNode 3 [enc_handler_semantics hs; enc_mode m; enc_label l; ge2; ge3] =>
        HandleCtx hs m l (decode_expr ge2) (decode_expr ge3)
    | GenNode 4 [enc_un_op op] =>
        UnOpCtx op
    | GenNode 5 [enc_bin_op op; gv2] =>
        BinOpLCtx op (decode_val gv2)
    | GenNode 6 [enc_bin_op op; ge1] =>
        BinOpRCtx op (decode_expr ge1)
    | GenNode 7 [ge1; ge2] =>
        IfCtx (decode_expr ge1) (decode_expr ge2)
    | GenNode 8 [gv2] =>
        PairLCtx (decode_val gv2)
    | GenNode 9 [ge1] =>
        PairRCtx (decode_expr ge1)
    | GenNode 10 [] =>
        FstCtx
    | GenNode 11 [] =>
        SndCtx
    | GenNode 12 [] =>
        InjLCtx
    | GenNode 13 [] =>
        InjRCtx
    | GenNode 14 [ge1; ge2] =>
        CaseCtx (decode_expr ge1) (decode_expr ge2)
    | GenNode 15 [gv2] =>
        AllocNLCtx (decode_val gv2)
    | GenNode 16 [ge1] =>
        AllocNRCtx (decode_expr ge1)
    | GenNode 17 [] =>
        FreeCtx
    | GenNode 18 [] =>
        LoadCtx
    | GenNode 19 [gv2] =>
        StoreLCtx (decode_val gv2)
    | GenNode 20 [ge1] =>
        StoreRCtx (decode_expr ge1)
    | GenNode 21 [gv1; gv2] =>
        CmpXchgLCtx (decode_val gv1) (decode_val gv2)
    | GenNode 22 [ge0; gv2] =>
        CmpXchgMCtx (decode_expr ge0) (decode_val gv2)
    | GenNode 23 [ge0; ge1] =>
        CmpXchgRCtx (decode_expr ge0) (decode_expr ge1)
    | GenNode 24 [gv2] =>
        XchgLCtx (decode_val gv2)
    | GenNode 25 [ge1] =>
        XchgRCtx (decode_expr ge1)
    | GenNode 26 [gv2] =>
        FaaLCtx (decode_val gv2)
    | GenNode 27 [ge1] =>
        FaaRCtx (decode_expr ge1)
    | _ =>
        inhabitant
    end.

  Definition decode_ectx_pre
    (decode_frame : gtree → frame)
    (decode_ectx : gtree → ectx)
    : gtree → ectx := λ gk,
    match gk with
    | GenNode 0 [] =>
        []
    | GenNode 1 [gf; gk] =>
        (decode_frame gf) :: (decode_ectx gk)
    | _ =>
        []
    end.

  Definition decode_expr :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_expr.

  Definition decode_val :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_val.

  Definition decode_frame :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_frame.

  Definition decode_ectx :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_ectx.

  Notation P := (λ e, decode_expr  (encode_expr  e) = e) (only parsing).
  Notation Q := (λ v, decode_val   (encode_val   v) = v) (only parsing).
  Notation R := (λ f, decode_frame (encode_frame f) = f) (only parsing).
  Notation S := (λ k, decode_ectx  (encode_ectx  k) = k) (only parsing).

  Global Instance expr_countable : Countable expr.
  Proof.
    refine (inj_countable' encode_expr decode_expr _).
    apply (expr_ind' P Q R S); repeat intros ?; simpl;
    repeat match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end; done.
  Qed.

  Global Instance val_countable : Countable val.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ v,
         Val v)
      ((* Decoding. *) λ e,
         match e with Val v => v | _ => inhabitant end) _);
    by intros [].
  Qed.

  Global Instance frame_countable : Countable frame.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ f,
         KontV [f])
      ((* Decoding. *) λ v,
         match v with KontV [f] => f | _ => inhabitant end) _);
    by intros [].
  Qed.

  Global Instance ectx_countable : Countable ectx.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ k,
         KontV k)
      ((* Decoding. *) λ v,
         match v with KontV k => k | _ => [] end) _);
    by intros [].
  Qed.

End countable.


(* -------------------------------------------------------------------------- *)
(** OFEs. *)

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure exprO := leibnizO expr.
Canonical Structure labelO := leibnizO label.
Canonical Structure valO := leibnizO val.
Canonical Structure frameO := leibnizO frame.
Canonical Structure ectxO := leibnizO ectx.
