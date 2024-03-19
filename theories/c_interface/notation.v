From melocoton.c_interface Require Export defs.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

(* # has no scope for historical reasons, but does conflict with the same
   notation on the ML side. Unfortunately, guessing the scope using type
   information is often insufficient because type inference does not flow in the
   direction we would want. So we keep this global for now, and use #C whenever
   we need to be explicit. *)
Notation "# l" := (LitV l%Z%CV%stdpp) (at level 8, format "# l").
Notation "#C l" := (LitV l%Z%CV%stdpp) (at level 8, format "#C  l").

Notation "& f" := (LitV (LitFunPtr f)) (at level 8, format "& f").
