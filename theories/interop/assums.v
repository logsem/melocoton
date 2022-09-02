From Coq Require Import ZArith.
From stdpp Require Export binders.
From stdpp Require Import base gmap.

(* temporary file. To be replaced by Require Imports of the operational
   semantics of toyML and toyC.

   Right now, we axiomatize for both languages the parts of the semantics that
   we use for defining the wrapping semantics *)

(* toyML *)

Module ML_lang.

Parameter loc : Set.
Context `{EqDecision loc, Countable loc}.
Parameter expr : Type.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit
  | LitLoc (l : loc).

Inductive val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Definition store : Type := gmap loc (list val).
Implicit Type ℓ : loc.
Implicit Type σ : store.

Parameter prog : Type.
Parameter ectx : Type.
Parameter head_step : prog → expr → store → expr → store → Prop.

End ML_lang.
