(* stdpp_ext.v *)

From stdpp Require Import list.


(* ------------------------------------------------------------------------- *)
(* Basic. *)

Lemma cons_as_app {A} x (xs : list A) : x :: xs = [x] ++ xs.
Proof. done. Qed.


(* ------------------------------------------------------------------------- *)
(* reverse. *)

Lemma reverse_eq_nil {A} (l : list A) : reverse l = [] → l = [].
Proof.
  intros Heq. rewrite <-reverse_nil in Heq.
  by rewrite <-(reverse_involutive l), <-(reverse_involutive []), Heq.
Qed.

Lemma rev_case {A} (l : list A) : (l = []) + {xs & {x & l = xs ++ [x]%list}}.
Proof.
  case_eq (reverse l).
  - intros Heq. left. by apply reverse_eq_nil.
  - intros x xs Heq. right. exists (reverse xs), x.
    specialize (f_equal reverse Heq) as Heq'.
    by rewrite reverse_involutive, reverse_cons in Heq'.
Qed.


(* ------------------------------------------------------------------------- *)
(* reverse & omap. *)

Lemma reverse_omap {A B} (f : A → option B) xs :
  reverse (omap f xs) = omap f (reverse xs).
Proof.
  induction xs as [|x xs IH]; [done|].
  rewrite reverse_cons, omap_app.
  rewrite cons_as_app, omap_app, reverse_app, IH.
  by simpl; destruct (f x).
Qed.


(* ------------------------------------------------------------------------- *)
(* list_omap. *)

Lemma list_omap_nil {A B} (f : A → option B) :
  omap f [] = [].
Proof. done. Qed.

Lemma list_omap_cons {A B} (f : A → option B) x xs :
  omap f (x :: xs) =
    match f x with
    | None => omap f xs
    | Some y => y :: omap f xs
    end.
Proof. done. Qed.

Lemma list_omap_app {A B} (f : A → option B) (l r : list A) :
  omap f (l ++ r) = (omap f l) ++ (omap f r).
Proof.
  induction l as [|x l]; [done|]; simpl.
  unfold omap in IHl. rewrite IHl.
  by case (f x).
Qed.

Lemma elem_of_list_omap_1 {A B} f (l : list A) x (y : B) :
  x ∈ l → f x = Some y → y ∈ omap f l.
Proof. intros ??. rewrite elem_of_list_omap. by exists x. Qed.


(* ------------------------------------------------------------------------- *)
(* submseteq. *)

Lemma concat_submseteq {A} (xss yss : list (list A)) :
  xss ⊆+ yss → concat xss ⊆+ concat yss.
Proof.
  induction 1; first done.
  - by apply submseteq_app.
  - simpl. rewrite !app_assoc. apply submseteq_app; [|done].
    rewrite submseteq_app_r. exists x, y. split; [|split]; try done.
    apply Permutation_app_comm.
  - by apply (submseteq_app []); [apply submseteq_nil_l|].
  - by transitivity (concat l2).
Qed.

Lemma submseteq_NoDup {A} (xs ys : list A) : xs ⊆+ ys → NoDup ys → NoDup xs.
Proof.
  induction 1 as [|? l1 ?? IH| |???? IH|]; first done.
  - rewrite !NoDup_cons.
    intros [Hnotin Hl2]. split; [|by apply IH].
    intros Hin. by apply Hnotin, (elem_of_submseteq l1).
  - rewrite !NoDup_ListNoDup.
    by apply Permutation_NoDup, Permutation_swap.
  - rewrite !NoDup_cons. intros [_ Hl2]. by apply IH.
  - intros Hl3. by auto.
Qed.
