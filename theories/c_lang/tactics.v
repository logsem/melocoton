From stdpp Require Import fin_maps.
From melocoton.c_interface Require Import defs.
From melocoton.c_lang Require Export lang_instantiation.
From melocoton.language Require Export language.
From iris.prelude Require Import options.
Import C_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | Let ?x ?e1 ?e2                  => add_item (LetCtx x e2) K e1
    | Load ?e                         => add_item LoadCtx K e
    | Store (Val ?v1) ?e2             => add_item (StoreRCtx v1) K e2
    | Store ?e1 ?e2                   => add_item (StoreLCtx e2) K e1
    | Malloc ?e                       => add_item (MallocCtx) K e
    | Free (Val ?v1) ?e2              => add_item (FreeRCtx v1) K e2
    | Free ?e1 ?e2                    => add_item (FreeLCtx e2) K e1
    | UnOp ?op ?e                     => add_item (UnOpCtx op) K e
    | BinOp ?op (Val ?v) ?e           => add_item (BinOpRCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpLCtx op e2) K e1
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | FunCall (Val ?vf) ?ea           => list_add_item (FunCallRCtx vf) (FunCall (Val vf)) (@nil val) (@None expr) (@nil expr) ea K
    | FunCall ?ef ?ea                 => add_item (FunCallLCtx ea) K ef
    | _                               => tac K e
    end
  with add_item Ki K e := go (Ki :: K) e
  with go_list ff ff2 ea_start ea_start_rev ea_mid ea_end ea_end_rev K :=
    match ea_start with
    | cons ?eah ?ear => go_list ff ff2 ear (eah :: ea_start_rev) ea_mid ea_end ea_end_rev K
    | nil => match ea_end with
      cons ?eah ?ear => go_list ff ff2 (@nil val) ea_start_rev ea_mid ear (eah :: ea_end_rev) K
      | nil => match ea_mid with
         | None => tac K (ff2 (map Val ea_start_rev))
         | Some ?e => go (ff ea_start_rev ea_end_rev :: K) e end end end
  with list_add_item ff ff2 ea_start ea_mid ea_end ea_rem K :=
    match ea_rem with
    | nil => go_list ff ff2 ea_start (@nil val) ea_mid ea_end (@nil expr) K
    | cons ?eah ?ear => match ea_mid with
          | Some ?ee => list_add_item ff ff2 ea_start (@Some expr ee) (eah :: ea_end) ear K
          | None => match eah with
                | (Val ?vv) => list_add_item ff ff2 (vv :: ea_start) (@None expr) (@nil expr) ear K
                | _ => list_add_item ff ff2 ea_start (@Some expr eah) (@nil expr) ear K end end
    end
  in
  go (@nil ectx_item) e.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : @head_step _ ?e _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.
Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _ _) => eexists _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step _ (Malloc _) _ _ _) => apply alloc_fresh : head_step.
