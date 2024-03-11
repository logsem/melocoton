From melocoton.ml_lang Require Export lang.
From iris.prelude Require Import options.
Import ML_lang.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation Alloc e := (AllocN (Val $ LitV $ LitInt 1) e) (only parsing).
Notation Load e := (LoadN e (Val $ LitV $ LitInt 0)) (only parsing).
Notation Store e e' := (StoreN e (Val $ LitV $ LitInt 0) e') (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).

(* # has no scope for historical reasons, but does conflict with the same
   notation on the C side. Unfortunately, guessing the scope using type
   information is often insufficient because type inference does not flow in the
   direction we would want. So we keep this global for now, and use #ML whenever
   we need to be explicit. *)
Notation "# l" := (LitV l%Z%MLV%stdpp) (at level 8, format "# l").
Notation "#ML l" := (LitV l%Z%MLV%stdpp) (at level 8, format "#ML l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : ml_expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : ml_val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>
    lots of stuff bla bla bla bla bla bla bla bla
  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : ml_expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : ml_expr_scope.

Notation "()" := LitUnit : ml_val_scope.
Notation "! e" := (Load e%MLE) (at level 9, right associativity) : ml_expr_scope.
Notation "'ref' e" := (Alloc e%MLE) (at level 10) : ml_expr_scope.
Notation "- e" := (UnOp MinusUnOp e%MLE) : ml_expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%MLE e2%MLE) : ml_expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%MLE e2%MLE) : ml_expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%MLE e2%MLE)) : ml_expr_scope.

Notation "~ e" := (UnOp NegOp e%MLE) (at level 75, right associativity) : ml_expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%MLE e2%MLE) (at level 80, e2 at level 78) : ml_expr_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%MLE)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : ml_expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%MLE)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : ml_val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%MLE e2%MLE e3%MLE)
  (at level 200, e1, e2, e3 at level 200) : ml_expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%MLE) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : ml_expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%MLE) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : ml_val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%binder e%MLE)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : ml_expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%MLE) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : ml_expr_scope.

Notation "λ: x , e" := (LamV x%binder e%MLE)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : ml_val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%MLE) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : ml_val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%MLE e1%MLE)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : ml_expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%MLE e1%MLE)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : ml_expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%MLE e2%MLE (LitV (LitBool false))) (only parsing) : ml_expr_scope.
Notation "e1 || e2" :=
  (If e1%MLE (LitV (LitBool true)) e2%MLE) (only parsing) : ml_expr_scope.

(** Notations for option *)
Notation NONE := (InjL (LitV LitUnit)) (only parsing).
Notation NONEV := (InjLV (LitV LitUnit)) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : ml_expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : ml_expr_scope.

Notation "'extern:' s 'with' '(' e1 , .. , en ')'" := (Extern s (@cons expr e1%MLE .. (@cons expr en%MLE nil) ..))
  (at level 70) : ml_expr_scope.

Notation "'extern:' s 'with' '(' ')'" := (Extern s nil)
  (at level 70) : ml_expr_scope.


Definition TLam e := ((λ: <>, e%MLE)%MLE).
Definition TLamV v := ((λ: <>, v%MLE)%MLV).
Definition TApp e1 := (App e1%MLE (#())%MLV).
Definition IdFunc e := (((λ: "x", "x"%MLE)%MLV e%MLE)%MLE).
Definition Roll e := (IdFunc e%MLE).
Definition RollV (v:val) := (v%MLV).
Definition Unroll e := (IdFunc e%MLE).
Definition Pack (e:expr) := (e%MLE).
Definition PackV (v:val) := (v%MLV).
Definition UnpackIn x e1 e2 := (Let x e1 e2).

Notation "Λ: <> , e" := (TLam e%MLE)
  (at level 200, e at level 200,
   format "'[' 'Λ:'  '<>' ,  '/  ' e ']'") : ml_expr_scope.
Notation "roll: e" := (Roll e%MLE)
  (at level 200, e at level 200,
   format "'[' 'roll:' '/  ' e ']'") : ml_expr_scope.
Notation "unroll: e" := (Unroll e%MLE)
  (at level 200, e at level 200,
   format "'[' 'unroll:' '/  ' e ']'") : ml_expr_scope.
Notation "pack: e" := (Pack e%MLE)
  (at level 200, e at level 200,
   format "'[' 'pack:' '/  ' e ']'") : ml_expr_scope.
Notation "'unpack:' x := e1 'in' e2" := (UnpackIn x%binder e1%MLE e2%MLE)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : ml_expr_scope.
