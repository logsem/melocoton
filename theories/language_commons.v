From stdpp Require Import relations strings gmap.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import ofe.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

(** Classifying expressions into values and calls. *)
Inductive mixin_expr_class {val} :=
| ExprVal (v : val) : mixin_expr_class
| ExprCall (fn_name : string) (arg : list val) : mixin_expr_class.

Notation protocol val Σ :=
  (string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ).
