From stdpp Require Import fin_maps.
From melocoton.c_toy_lang Require Export tactics iris.lang_instantiation.
From iris.prelude Require Import options.
Import C_lang.

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
  | H : @bogo_head_step _ _ _ _ _ _ _ |- _ => destruct (@bogo_head_step_elim' _ _ _ _ _ _ _ H) as (? & ? & ?); subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : head_step.
Global Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 1 (bogo_head_step _ _ _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step _ (Malloc _) _ _ _) => apply alloc_fresh : head_step.