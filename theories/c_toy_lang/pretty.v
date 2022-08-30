From stdpp Require Export pretty.

From melocoton.c_toy_lang Require Import lang.
From iris.prelude Require Import options.

(** * Pretty printing for HeapLang values *)

Global Instance pretty_loc : Pretty loc :=
  λ l, pretty l.(loc_car).

Global Instance pretty_base_lit : Pretty base_lit :=
  λ l, match l with
       | LitInt z => pretty z
       | LitLoc l => "(loc " +:+ pretty l +:+ ")"
       | LitFunPtr p => "(& " +:+ p +:+ ")"
       end.

Global Instance pretty_binder : Pretty binder :=
  λ b, match b with
       | BNamed x => x
       | BAnon => "<>"
       end.

(** Note that this instance does not print function bodies and is thus not
injective (unlike most `pretty` instances). *)
Global Instance pretty_val : Pretty val :=
  fix go v :=
    match v with
    | LitV l => pretty l
    end.

Global Instance pretty_un_op : Pretty un_op :=
  λ op, match op with
        | BitwiseNotOp => "~"
        | NegOp => "-"
        | NotOp => "!"
        | Ptr2Int => "`ptr2int`"
        | Int2Ptr => "`int2ptr`"
        end.

Global Instance pretty_bin_op : Pretty bin_op :=
  λ op, match op with
        | PlusOp => "+"
        | MinusOp => "-"
        | MultOp => "*"
        | QuotOp => "`quot`"
        | RemOp => "`rem`"
        | AndOp => "&"
        | OrOp => "|"
        | XorOp => "`xor`"
        | ShiftLOp => "<<"
        | ShiftROp => ">>"
        | LeOp => "≤"
        | LtOp => "<"
        | EqOp => "="
        | PtrOffsetOp => "+ₗ"
        | PtrDiffOp => "-ₗ"
        end .
