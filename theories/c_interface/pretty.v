From stdpp Require Export pretty.
From melocoton.c_interface Require Import defs.
From iris.prelude Require Import options.

(** * Pretty printing for C values *)

Global Instance pretty_loc : Pretty loc :=
  λ l, pretty l.(loc_car).

Global Instance pretty_base_lit : Pretty base_lit :=
  λ l, match l with
       | LitInt z => pretty z
       | LitLoc l => "(loc " +:+ pretty l +:+ ")"
       | LitFunPtr p => "(& " +:+ p +:+ ")"
       end.

Global Instance pretty_val : Pretty val :=
  fix go v :=
    match v with
    | LitV l => pretty l
    end.
