From Coq Require Import ZArith.
From stdpp Require Export binders.
From stdpp Require Import base gmap.

(* temporary file. To be replaced by Require Imports of the operational
   semantics of toyML and toyC.

   Right now, we axiomatize for both languages the parts of the semantics that
   we use for defining the wrapping semantics *)

(* toyML *)

Parameter loc : Set.
Context `{EqDecision loc, Countable loc}.
Parameter exprML : Type.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit
  | LitLoc (l : loc).

Inductive val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : exprML)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Definition store : Type := gmap loc (list val).
Implicit Type ℓ : loc.
Implicit Type σ : store.

Parameter progML : Type.
Parameter ectxML : Type.
Parameter head_step_ML : progML → exprML → store → exprML → store → Prop.

(* toyC *)

Definition addr : Type := Z.
Definition word : Type := Z.
Definition memory : Type := gmap addr word.

Parameter exprC : Type.
Definition progC : Type := gmap string (list string * exprC).
Parameter ectxC : Type.
Parameter head_step_C : progC → exprC → memory → exprC → memory → Prop.
Parameter exprC_of_call : string → list word → exprC.
Parameter fillC : ectxC → exprC → exprC.
Parameter apply_func_C : string → list word → exprC.
Parameter to_val_C : exprC → option word.
Parameter to_call_C : exprC → option (string * list word).
Parameter of_val_C : word → exprC.
