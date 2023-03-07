From stdpp Require Export pretty.
From melocoton.c_interface Require Export pretty.
From melocoton.c_lang Require Import lang.
From iris.prelude Require Import options.

Global Instance pretty_binder : Pretty binder :=
  λ b, match b with
       | BNamed x => x
       | BAnon => "<>"
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
