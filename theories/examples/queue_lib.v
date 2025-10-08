(* queue_lib.v *)

From blaze Require Import logic.

Class QueueLib Σ `{!blazeGS Σ} := {
  queue_create : val;
  queue_add    : val;
  queue_take   : val;
  queue_empty  : val;

  is_queue : val -d> list val -d> iPropO Σ;

  queue_create_spec L R k1 e2 :
    ▷ (∀ q, is_queue q [] -∗ BEWP fill k1 q ≤ e2 <|L|> {{R}}) -∗
    BEWP fill k1 (queue_create #()) ≤ e2 <|L|> {{R}};

  queue_add_spec L R k1 q v vs e2 :
    ▷ is_queue q vs -∗
    ▷ (is_queue q (v :: vs) -∗ BEWP fill k1 #() ≤ e2 <|L|> {{R}}) -∗
    BEWP fill k1 (queue_add q v) ≤ e2 <|L|> {{R}};

  queue_take_spec L R k1 q v vs e2 :
    ▷ is_queue q (vs ++ [v]) -∗
    ▷ (is_queue q vs -∗ BEWP fill k1 v ≤ e2 <|L|> {{R}}) -∗
    BEWP fill k1 (queue_take q) ≤ e2 <|L|> {{R}};

  queue_empty_spec L R k1 q vs e2 :
    ▷ is_queue q vs -∗
    ▷ (is_queue q vs -∗
       BEWP fill k1 #(bool_decide (length vs = 0%nat)) ≤ e2 <|L|> {{R}}
      ) -∗
    BEWP fill k1 (queue_empty q) ≤ e2 <|L|> {{R}};
}.
