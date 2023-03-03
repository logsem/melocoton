From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require ectxi_language.
From melocoton Require Import commons.
From melocoton.ml_toy_lang Require Export locoff.
From iris.prelude Require Import options.

(** heap_lang.  A fairly simple language used for common Iris examples.

Noteworthy design choices:

- This is a right-to-left evaluated language, like CakeML and OCaml.  The reason
  for this is that it makes curried functions usable: Given a WP for [f a b], we
  know that any effects [f] might have to not matter until after *both* [a] and
  [b] are evaluated.  With left-to-right evaluation, that triple is basically
  useless unless the user let-expands [b].

- Even after deallocating a location, the heap remembers that these locations
  were previously allocated and makes sure they do not get reused. This is
  necessary to ensure soundness of the [meta] feature provided by [gen_heap].
  Also, unlike in languages like C, allocated and deallocated "blocks" do not
  have to match up: you can allocate a large array of locations and then
  deallocate a hole out of it in the middle.
*)

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module ML_lang.

(** Expressions and vals. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit
  | LitLoc (l : loc) .
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30/-4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *).

Unset Elimination Schemes.

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | LoadN (e1 : expr) (e2 : expr) (* location, offset *)
  | StoreN (e1 : expr) (e2 : expr) (e3 : expr) (* location, offset, value *)
  | Length (e : expr)
  (* Call to a (possibly external) module function *)
  | Extern (s : string) (ea : list expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).


Scheme val_ind := Induction for val Sort Prop.
Scheme val_rec := Induction for val Sort Type.

Definition expr_ind (P : expr → Prop) 
  (f : ∀ v : val, P (Val v))
  (f0 : ∀ x : string, P (Var x)) 
  (f1 : ∀ (f1 x : binder) (e : expr), P e → P (Rec f1 x e)) 
  (f2 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (App e1 e2)) 
  (f3 : ∀ (op : un_op) (e : expr), P e → P (UnOp op e)) 
  (f4 : ∀ (op : bin_op) (e1 : expr),
          P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2)) 
  (f5 : ∀ e0 : expr,
          P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2)) 
  (f6 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Pair e1 e2)) 
  (f7 : ∀ e : expr, P e → P (Fst e)) (f8 : ∀ e : expr, P e → P (Snd e)) 
  (f9 : ∀ e : expr, P e → P (InjL e)) (f10 : ∀ e : expr, P e → P (InjR e)) 
  (f11 : ∀ e0 : expr,
           P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Case e0 e1 e2)) 
  (f12 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (AllocN e1 e2))
  (f14 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (LoadN e1 e2))
  (f15 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → ∀ e3 : expr, P e3 → P (StoreN e1 e2 e3))
  (f16 : ∀ e : expr, P e → P (Length e))
  (f17 : ∀ (s : string) (ea : list expr), Forall P ea → P (Extern s ea))
  :=
  fix F (e : expr) : P e :=
    match e as e0 return (P e0) with
    | Val v => f v
    | Var x => f0 x
    | Rec f17 x e0 => f1 f17 x e0 (F e0)
    | App e1 e2 => f2 e1 (F e1) e2 (F e2)
    | UnOp op e0 => f3 op e0 (F e0)
    | BinOp op e1 e2 => f4 op e1 (F e1) e2 (F e2)
    | If e0 e1 e2 => f5 e0 (F e0) e1 (F e1) e2 (F e2)
    | Pair e1 e2 => f6 e1 (F e1) e2 (F e2)
    | Fst e0 => f7 e0 (F e0)
    | Snd e0 => f8 e0 (F e0)
    | InjL e0 => f9 e0 (F e0)
    | InjR e0 => f10 e0 (F e0)
    | Case e0 e1 e2 => f11 e0 (F e0) e1 (F e1) e2 (F e2)
    | AllocN e1 e2 => f12 e1 (F e1) e2 (F e2)
    | LoadN e0 e1 => f14 e0 (F e0) e1 (F e1)
    | StoreN e1 e2 e3 => f15 e1 (F e1) e2 (F e2) e3 (F e3)
    | Length e => f16 e (F e)
    | Extern s ea => f17 s ea (Forall_true P ea F)
    end.

Set Elimination Schemes.



Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition of_class_ML (e : mixin_expr_class) : expr :=
  match e with
  | ExprVal v => Val v
  | ExprCall vf vl => Extern vf (map Val vl)
  end.

#[local] Notation omap f x := (match x with Some v => f v | None => None end).

Fixpoint unmap_val el :=
  match el with
  | Val v :: er => omap (fun vr => Some (v::vr)) (unmap_val er)
  | [] => Some nil
  | _ => None
  end.

Definition to_class_ML (e : expr) : option mixin_expr_class :=
  match e with
  | Val v => Some (ExprVal v)
  | Extern vf el => omap (fun l => Some (ExprCall vf l)) (unmap_val el)
  | _ => None
  end.

Lemma map_unmap_val l : unmap_val (map Val l) = Some l.
Proof.
  induction l.
  - easy.
  - cbn. rewrite IHl. easy.
Qed.

Lemma to_of_class_ML e : to_class_ML (of_class_ML e) = Some e.
Proof.
  destruct e.
  - easy.
  - cbn. rewrite map_unmap_val. easy.
Qed.

Lemma unmap_val_map le lv : unmap_val le = Some lv → map Val lv = le.
Proof.
  induction le in lv|-*.
  - intros H. injection H. intros <-. easy.
  - cbn. destruct a. 2-18:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Lemma of_to_class_ML e c : to_class_ML e = Some c → of_class_ML c = e.
Proof.
  destruct e; cbn; try congruence.
  - intros H. injection H. intros <-. easy.
  - destruct unmap_val eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply unmap_val_map.
Qed.

Local Notation to_val e :=
  (match to_class_ML e with Some (ExprVal v) => Some v | _ => None end).

(** Unboxed values are
  * locations
  * integers
  * booleans
  * unit

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV _ => True
  | _ => False
  end.

Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

Local Notation state := (gmap loc (option (list val))).

(** Equality and other typeclass stuff *)
Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  unshelve refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | LoadN e1 e2, LoadN e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | StoreN e1 e2 e3, StoreN e1' e2' e3' =>
        cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
     | Length e, Length e' =>
        cast_if (decide (e = e'))
     | Extern x e, Extern x' e' => 
        let gol := (fix gol (l1 l2 : list expr) {struct l1} : Decision (l1 = l2) :=
                       match l1, l2 with
                       | nil, nil => left eq_refl
                       | xl::xr, xl'::xr' => cast_if_and (decide (xl = xl')) (decide (xr = xr'))
                       | _, _ => right _
                       end)
        in cast_if_and (decide (x = x')) (@decide (e = e') (gol _ _))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear gol); try (clear go gov); abstract intuition congruence.
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof.
  unshelve refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | LoadN e1 e2, LoadN e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | StoreN e1 e2 e3, StoreN e1' e2' e3' =>
        cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
     | Length e, Length e' =>
        cast_if (decide (e = e'))
     | Extern x e, Extern x' e' => 
        let gol := (fix gol (l1 l2 : list expr) {struct l1} : Decision (l1 = l2) :=
                       match l1, l2 with
                       | nil, nil => left eq_refl
                       | xl::xr, xl'::xr' => cast_if_and (decide (xl = xl')) (decide (xr = xr'))
                       | _, _ => right _
                       end)
        in cast_if_and (decide (x = x')) (@decide (e = e') (gol _ _))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for gov); try (clear gol); try (clear go gov); abstract intuition congruence.
Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitBool b => (inl (inr b))
  | LitUnit => (inr (inl ()))
  | LitLoc l => (inr (inr l))
  end) (λ l, match l with
  | (inl (inl n)) => LitInt n
  | (inl (inr b)) => LitBool b
  | (inr (inl ())) => LitUnit
  | (inr (inr l)) => LitLoc l
  end) _); by intros [].
Qed.
Global Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | _ => EqOp
  end) _); by intros [].
Qed.
Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | AllocN e1 e2 => GenNode 13 [go e1; go e2]
     | LoadN e1 e2 => GenNode 15 [go e1; go e2]
     | StoreN e1 e2 e3 => GenNode 16 [go e1; go e2; go e3]
     | Length e => GenNode 17 [go e]
     | Extern s el => GenNode 18 (GenLeaf (inl (inl s)) :: map go el)
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 13 [e1; e2] => AllocN (go e1) (go e2)
     | GenNode 15 [e1; e2] => LoadN (go e1) (go e2)
     | GenNode 16 [e1; e2; e3] => StoreN (go e1) (go e2) (go e3)
     | GenNode 17 [e] => Length (go e)
     | GenNode 18 (GenLeaf (inl (inl s)) :: ea) => Extern s (map go ea)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v| | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|try done..].
   unfold map; by induction ea as [|ex er ->]; simpl; f_equal.
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val (λ e, to_val e) _); auto using to_of_class_ML. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate inhabitant.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | LoadNLCtx (v2 : val)
  | LoadNRCtx (e1 : expr)
  | StoreNLLCtx (v2 : val) (v3 : val)
  | StoreNLRCtx (e1 : expr) (v3 : val)
  | StoreNRRCtx (e1 : expr) (e2 : expr)
  | LengthCtx
  | ExternCtx (s : string) (va : list val) (ve : list expr).

(** Contextual closure will only reduce [e] in [Resolve e (Val _) (Val _)] if
the local context of [e] is non-empty. As a consequence, the first argument of
[Resolve] is not completely evaluated (down to a value) by contextual closure:
no head steps (i.e., surface reductions) are taken. This means that contextual
closure will reduce [Resolve (CmpXchg #l #n (#n + #1)) #p #v] into [Resolve
(CmpXchg #l #n #(n+1)) #p #v], but it cannot context-step any further. *)

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | LoadNLCtx v2 => LoadN e (Val v2)
  | LoadNRCtx e1 => LoadN e1 e
  | StoreNLLCtx v2 v3 => StoreN e (Val v2) (Val v3)
  | StoreNLRCtx e1 v3 => StoreN e1 e (Val v3)
  | StoreNRRCtx e1 e2 => StoreN e1 e2 e
  | LengthCtx => Length e
  | ExternCtx s va ve => Extern s (map of_val va ++ [e] ++ ve)
  end.

Notation delete_binder g b := (binder_delete b g).

Definition ectx := list ectx_item.
Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.
Definition comp_ectx (K K' : ectx) : ectx := K' ++ K.

Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

(** Substitution *)
Fixpoint subst_all (g : gmap string val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => match g !! y with None => Var y | Some k => Val k end
  | Rec f y e =>
     Rec f y (subst_all (delete_binder (delete_binder g y) f) e)
  | App e1 e2 => App (subst_all g e1) (subst_all g e2)
  | UnOp op e => UnOp op (subst_all g e)
  | BinOp op e1 e2 => BinOp op (subst_all g e1) (subst_all g e2)
  | If e0 e1 e2 => If (subst_all g e0) (subst_all g e1) (subst_all g e2)
  | Pair e1 e2 => Pair (subst_all g e1) (subst_all g e2)
  | Fst e => Fst (subst_all g e)
  | Snd e => Snd (subst_all g e)
  | InjL e => InjL (subst_all g e)
  | InjR e => InjR (subst_all g e)
  | Case e0 e1 e2 => Case (subst_all g e0) (subst_all g e1) (subst_all g e2)
  | AllocN e1 e2 => AllocN (subst_all g e1) (subst_all g e2)
  | LoadN e1 e2 => LoadN (subst_all g e1) (subst_all g e2)
  | StoreN e1 e2 e3 => StoreN (subst_all g e1) (subst_all g e2) (subst_all g e3)
  | Length e => Length (subst_all g e)
  | Extern s ea => Extern s (map (subst_all g) ea)
  end.

Definition subst (x : string) (v : val) (e : expr) : expr :=
  subst_all {[x:=v]} e.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc (option (list val)) → gmap loc (option (list val))) (σ: state) : state := f σ.
Global Arguments state_upd_heap _ !_ /.

Inductive ml_function := MlFun (b : list binder) (e : expr).
Class ml_program := prog : gmap string ml_function.

(* Note that this way, a function where all arguments have the same name (say x), that returns x, returns the first argument *)
Fixpoint zip_args (an : list binder) (av : list val) : option (gmap string val) := match an, av with
  nil, nil => Some ∅
| (BNamed ax::ar), (vx::vr) => option_map (<[ax:=vx]>) (zip_args ar vr)
| (BAnon::ar), (vx::vr) => zip_args ar vr
| _, _ => None end.

Definition apply_function (f:ml_function) (av : list val) := match f with MlFun an e =>
    match (zip_args an av) with Some σ => Some (subst_all σ e) | _ => None end end.

Inductive head_step (p : ml_program) : expr → state → expr → state → Prop :=
  | RecS f x e σ :
     head_step p (Rec f x e) σ (Val $ RecV f x e) σ
  | PairS v1 v2 σ :
     head_step p (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
  | InjLS v σ :
     head_step p (InjL $ Val v) σ (Val $ InjLV v) σ
  | InjRS v σ :
     head_step p (InjR $ Val v) σ (Val $ InjRV v) σ
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step p (App (Val $ RecV f x e1) (Val v2)) σ e' σ
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step p (UnOp op (Val v)) σ (Val v') σ
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step p (BinOp op (Val v1) (Val v2)) σ (Val v') σ
  | IfTrueS e1 e2 σ :
     head_step p (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
  | IfFalseS e1 e2 σ :
     head_step p (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
  | FstS v1 v2 σ :
     head_step p (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
  | SndS v1 v2 σ :
     head_step p (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
  | CaseLS v e1 e2 σ :
     head_step p (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
  | CaseRS v e1 e2 σ :
     head_step p (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
  | AllocNS n v σ l :
     (0 ≤ n)%Z →
     l ∉ dom σ →
     head_step p (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
                 (Val $ LitV $ LitLoc l) (<[l := Some (replicate (Z.to_nat n) v)]> σ)
  | LoadNS l i v σ :
     σ !! Locoff l i = Some v →
     head_step p (LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i)) σ
                 (of_val v) σ
  | StoreNS l i v w σ :
     σ !! Locoff l i = Some v →
     head_step p (StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w)) σ
                 (Val $ LitV LitUnit) (<[Locoff l i := w]> σ)
  (* Silently diverge in case of out-of-bound accesses. We want to distinguish
     OOB accesses from other failures (which are UB), so that we can prove a
     type safety result. In a more realistic language we could have a dedicated
     failure state for OOB, or a mechanism for exceptions/panics... *)
  | LoadNOobS l i σ :
     σ !! Locoff l i = None →
     head_step p (LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i)) σ
                 (LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i)) σ
  | StoreNOobS l i w σ :
     σ !! Locoff l i = None →
     head_step p (StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w)) σ
                 (StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w)) σ
  | LengthS l vs σ :
    σ !! l = Some (Some vs) →
    head_step p (Length (Val $ LitV $ LitLoc l)) σ
                (Val $ LitV $ LitInt (length vs)) σ
  | ExternS s va args res e σ :
     (p : gmap string ml_function) !! s = Some (MlFun args e) →
     apply_function (MlFun args e) va = Some res →
     head_step p (Extern s (map Val va)) σ res σ.


(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma val_head_stuck p e1 σ1 e2 σ2 :
  head_step p e1 σ1 e2 σ2 → to_val e1 = None.
Proof.
  inversion 1; simplify_eq; try done.
  cbn. repeat (case_match; simplify_eq); done.
Qed.

Lemma head_ctx_step_val p Ki e σ1 e2 σ2 :
  head_step p (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
Proof.
  revert e2. induction Ki; try by (inversion_clear 1; simplify_option_eq; eauto).
  intros e2. inversion 1; subst. enough (exists k, Val k = e ∧ In k va0) as (k & <- & _) by easy.
  apply in_map_iff. rewrite H1. apply in_or_app. right. now left.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; try naive_solver eauto with f_equal.
  - intros H1 H2 H3. cbn in H3. injection H3. intros H4 ->.
    edestruct (list_eq_sliced _ _ _ _ _ _ (fun x => is_Some (to_val x)) H4) as (Heq & -> & ->).
    + by intros k [k' [<- Hk']]%in_map_iff.
    + by intros k [k' [<- Hk']]%in_map_iff.
    + by rewrite H1.
    + by rewrite H2.
    + f_equal. apply (map_inj Val). 2:easy. congruence.
Qed.


Lemma alloc_fresh p v n σ :
  let l := fresh_locs (dom σ) in
  (0 ≤ n)%Z →
  head_step p (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ
              (Val $ LitV $ LitLoc l) (<[l := Some (replicate (Z.to_nat n) v)]> σ).
Proof.
  intros.
  apply AllocNS; first done.
  intros.
  pose proof (fresh_locs_fresh (dom σ) 0 ltac:(reflexivity)) as Hfresh.
  by rewrite loc_add_0 in Hfresh.
Qed.

End ML_lang.
Export ML_lang.
