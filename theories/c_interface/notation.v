From melocoton.c_interface Require Export defs.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

(* No scope, does not conflict and scope is often not inferred properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").
Notation "& f" := (LitV (LitFunPtr f)) (at level 8, format "& f").
