From melocoton.c_toy_lang Require Export lang.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (Seq (Val $ LitV LitUnit) (Val $ LitV LitUnit)).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").
Notation "& f" := (LitV (LitFunPtr f)) (at level 8, format "& f").

Notation "* e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'malloc' '(' e ')'" := (Malloc e%E) (at level 10) : expr_scope.
Notation "'free' '(' e1 ',' e2 ')'" := (Free e1%E e2%E) (at level 10) : expr_scope.
Notation "- e" := (UnOp NegOp e%E) : expr_scope.
Notation "! e" := (UnOp NotOp e%E) (at level 9, right associativity) : expr_scope.
Notation "~ e" := (UnOp BitwiseNotOp e%E) (at level 75, right associativity) : expr_scope.
Notation "'p2i' e" := (UnOp Ptr2Int e%E) (at level 75, right associativity) : expr_scope.
Notation "'i2p' e" := (UnOp Int2Ptr e%E) (at level 75, right associativity) : expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp PtrOffsetOp e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 -ₗ e2" := (BinOp PtrDiffOp e1%E e2%E) (at level 50) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%E e2%E) : expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%E e2%E) : expr_scope.
Notation "e1 'band' e2" := (BinOp AndOp e1%E e2%E) (at level 49) : expr_scope.
Notation "e1 'bor' e2" := (BinOp OrOp e1%E e2%E) (at level 48) : expr_scope.
Notation "e1 'bxor' e2" := (BinOp XorOp e1%E e2%E) (at level 47) : expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

Notation "'while:' e1 'do' e2" := (While e1%E e2%E)
  (at level 200, e1, e2 at level 200) : expr_scope.

Notation "'call:' ff 'with' '(' e1 , .. , en ')'" := (FunCall ff%E (cons e1%E .. (cons en%E nil) ..))
  (at level 200, ff, e1, en at level 99) : expr_scope.

Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%E e2%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Let BAnon e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (LitV (LitInt 0))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (LitV (LitInt 1)) e2%E) (only parsing) : expr_scope. (*

(** Notations for option *)
Notation NONE := (InjL (LitV LitUnit)) (only parsing).
Notation NONEV := (InjLV (LitV LitUnit)) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

Notation ResolveProph e1 e2 := (Resolve Skip e1 e2) (only parsing).
Notation "'resolve_proph:' p 'to:' v" := (ResolveProph p v) (at level 100) : expr_scope. *)
