From stdpp Require Import fin_maps.
From melocoton.ml_toy_lang Require Export lang.
From iris.prelude Require Import options.
Import ml_toy_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (AppLCtx v) K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) K e2
    | Fst ?e                          => add_item FstCtx K e
    | Snd ?e                          => add_item SndCtx K e
    | InjL ?e                         => add_item InjLCtx K e
    | InjR ?e                         => add_item InjRCtx K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) K e2
    | Free ?e                         => add_item FreeCtx K e
    | Load ?e                         => add_item LoadCtx K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) K e2
    | Extern ?s ?ea                   => list_add_item (ExternCtx s) (Extern s) (@nil val) (@None expr) (@nil expr) ea K
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
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : head_step.
Global Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : head_step.
