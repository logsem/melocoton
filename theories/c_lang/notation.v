From melocoton.c_interface Require Export notation.
From melocoton.c_lang Require Export lang.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (Seq (Val $ LitV LitUnit) (Val $ LitV LitUnit)).

Notation "* e" := (Load e%CE) (at level 9, right associativity) : c_expr_scope.
Notation "'malloc' '(' e ')'" := (Malloc e%CE) (at level 10) : c_expr_scope.
Notation "'free' '(' e1 ',' e2 ')'" := (Free e1%CE e2%CE) (at level 10) : c_expr_scope.
Notation "- e" := (UnOp NegOp e%CE) : c_expr_scope.
Notation "! e" := (UnOp NotOp e%CE) (at level 9, right associativity) : c_expr_scope.
Notation "~ e" := (UnOp BitwiseNotOp e%CE) (at level 75, right associativity) : c_expr_scope.
Notation "'p2i' e" := (UnOp Ptr2Int e%CE) (at level 75, right associativity) : c_expr_scope.
Notation "'i2p' e" := (UnOp Int2Ptr e%CE) (at level 75, right associativity) : c_expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 +ₗ e2" := (BinOp PtrOffsetOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 -ₗ e2" := (BinOp PtrDiffOp e1%CE e2%CE) (at level 50) : c_expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%CE e2%CE) : c_expr_scope.
Notation "e1 'band' e2" := (BinOp AndOp e1%CE e2%CE) (at level 49) : c_expr_scope.
Notation "e1 'bor' e2" := (BinOp OrOp e1%CE e2%CE) (at level 48) : c_expr_scope.
Notation "e1 'bxor' e2" := (BinOp XorOp e1%CE e2%CE) (at level 47) : c_expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%CE e2%CE) : c_expr_scope.
Notation "e1 ≠ e2" := (UnOp NotOp (BinOp EqOp e1%CE e2%CE)) : c_expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%CE e2%CE) (at level 80, e2 at level 78) : c_expr_scope.


Notation "'if:' e1 'then' e2 'else' e3" := (If e1%CE e2%CE e3%CE)
  (at level 200, e1, e2, e3 at level 200) : c_expr_scope.

Notation "'while:' e1 'do' e2" := (While e1%CE e2%CE)
  (at level 200, e1, e2 at level 200) : c_expr_scope.

Notation "'call:' ff 'with' '(' e1 , .. , en ')'" := (FunCall ff%CE (@cons expr e1%CE .. (@cons expr en%CE nil) ..))
  (at level 70) : c_expr_scope.

Notation "'call:' ff 'with' '(' ')'" := (FunCall ff%CE nil)
  (at level 70) : c_expr_scope.

Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%CE e2%CE)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : c_expr_scope.
Notation "e1 ;; e2" := (Let BAnon e1%CE e2%CE)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : c_expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%CE e2%CE (LitV (LitInt 0))) (only parsing) : c_expr_scope.
Notation "e1 || e2" :=
  (If e1%CE (LitV (LitInt 1)) e2%CE) (only parsing) : c_expr_scope.
