From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From melocoton Require Import stdpp_extra language_commons.
From melocoton.ml_lang Require Export locoff.
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

(* Engineering note: definitions and lemmas defined as [Local] correspond to
   fields of [LanguageMixin] that thus get re-exported as generic functions on a
   [language]. We define them as local to avoid the ml_lang-specific name
   clashing with the generic name, and always pick the generic name.
*)

Declare Scope ml_expr_scope.
Declare Scope ml_val_scope.
Delimit Scope ml_expr_scope with MLE.
Delimit Scope ml_val_scope with MLV.

Module ML_lang.

(** Expressions and vals. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit
  | LitBoxedInt (n : Z) (* Int32.t, Int64.t and Nativeint.t *)
  | LitLoc (l : loc)
  | LitForeign (id : nat).
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
  (* Exception *)
  | Raise (e : expr)
  | Try (e r : expr)
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
  (f12 : ∀ e : expr, P e → P (Raise e))
  (f13 : ∀ e : expr, P e → ∀ r : expr, P r → P (Try e r))
  (f14 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (AllocN e1 e2))
  (f15 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (LoadN e1 e2))
  (f16 : ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → ∀ e3 : expr, P e3 → P (StoreN e1 e2 e3))
  (f17 : ∀ e : expr, P e → P (Length e))
  (f18 : ∀ (s : string) (ea : list expr), Forall P ea → P (Extern s ea))
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
    | Raise e => f12 e (F e)
    | Try e r => f13 e (F e) r (F r)
    | AllocN e1 e2 => f14 e1 (F e1) e2 (F e2)
    | LoadN e0 e1 => f15 e0 (F e0) e1 (F e1)
    | StoreN e1 e2 e3 => f16 e1 (F e1) e2 (F e2) e3 (F e3)
    | Length e => f17 e (F e)
    | Extern s ea => f18 s ea (Forall_true P ea F)
    end.

Set Elimination Schemes.

(** Boilerplate used to implement the [language] interface *)

Bind Scope ml_expr_scope with expr.
Bind Scope ml_val_scope with val.

Notation of_val := Val (only parsing).

Local Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Local Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. done. Qed.
Local Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e; inversion 1; done. Qed.

Local Definition of_outcome (o : outcome val) :=
  match o with
  | OVal v => Val v
  | OExn v => Raise (Val v)
  end.

Local Definition to_outcome (e : expr) :=
  match e with
  | Val v => Some (OVal v)
  | Raise (Val v) => Some (OExn v)
  | _ => None
  end.

Local Lemma to_of_outcome o : to_outcome (of_outcome o) = Some o.
Proof. destruct o; try done. Qed.
Local Lemma of_to_outcome e o : to_outcome e = Some o → of_outcome o = e.
Proof. destruct e; inversion 1; try done. destruct e; inversion H1; try done. Qed.

Lemma comp_val_in_out e : to_outcome e = None → to_val e = None.
Proof. destruct e; eauto. cbn. congruence. Qed.

(** Helpers to define the semantics of equality on values [EqOp].

    We take some extra care when defining the behavior of [EqOp] on ML values.
    - We wish to ensure that it coincides with equality of block-level values as
      observed through the FFI;
    - However ML values and block-level values have different representations:
      for instance two ML pairs (1, 2), while equal as ML values, could be
      different when viewed as block-level values because they could be allocated
      as two blocks with different addresses.

    The solution is to carefully restrict the semantics of [EqOp] so that it
    only specifies cases where ML-equality and FFI-equality coincide. In other
    cases [EqOp] will simply get stuck. (Alternatively, we could make it return
    any boolean non-deterministically, but that would not be much more useful.)

    We thus classify ML values as either:
    - Int-like values that are represented as integers by the FFI:
      integers, booleans, unit.
    - Other (non int-like) values that are represented as pointers to a block
      by the FFI (locations, closures, pairs, variants).

    We only allow comparing values of different shapes when they can be
    distinguished by the FFI according to their representation. For instance,
    comparing an integer and a boolean is disallowed since they end up
    represented the same by the FFI (e.g. in ML we have [LitInt 0 ≠ LitBool
    false], but they both end up represented as 0 by the FFI).

    Furthermore, we restrict ourselves to comparing "immediate" values, i.e.
    we don't allow recursively comparing structured values such as pairs or
    variants.
*)

(** [val_is_intlike v] holds if [v] is represented as an integer by the FFI *)
Definition val_is_intlike (v : val) : Prop :=
  match v with
  | LitV (LitInt _) | LitV (LitBool _) | LitV LitUnit => True
  | _ => False
  end.

Global Instance val_is_intlike_dec v : Decision (val_is_intlike v).
Proof.
  destruct v as [ v | | | |];
    try (right; intros HH; by inversion HH).
  destruct v; try by (right; intros HH; inversion HH).
  all: by left.
Defined.

(** [vals_compare_safe v1 v2] holds if testing [EqOp v1 v2] is fine. *)
Inductive vals_compare_safe : val → val → Prop :=
(* if one value is "int-like" and not the other, then both equality on ML and
   FFI values will agree on the fact that they are different... *)
| vals_compare_intlike_pointerlike v1 v2 :
  (  val_is_intlike v1 ∧ ¬ val_is_intlike v2) ∨
  (¬ val_is_intlike v1 ∧   val_is_intlike v2) →
  vals_compare_safe v1 v2
(* in all other cases, we only allow testing of int-like values of the same
   ML syntactic category *)
| vals_compare_boxedint n1 n2 :
  vals_compare_safe (LitV (LitBoxedInt n1)) (LitV (LitBoxedInt n2))
| vals_compare_int n1 n2 :
  vals_compare_safe (LitV (LitInt n1)) (LitV (LitInt n2))
| vals_compare_bool b1 b2 :
  vals_compare_safe (LitV (LitBool b1)) (LitV (LitBool b2))
| vals_compare_unit :
  vals_compare_safe (LitV LitUnit) (LitV LitUnit)
| vals_compare_loc l1 l2 :
  vals_compare_safe (LitV (LitLoc l1)) (LitV (LitLoc l2)).

Global Hint Resolve vals_compare_int : core.
Global Hint Resolve vals_compare_boxedint : core.
Global Hint Resolve vals_compare_bool : core.
Global Hint Resolve vals_compare_unit : core.
Global Hint Resolve vals_compare_loc : core.

(** The semantics for [EqOp] needs to decide whether [vals_compare_safe] holds
    of two given values, so we prove that it is a decidable property. *)
Global Instance vals_compare_safe_dec v1 v2 : Decision (vals_compare_safe v1 v2).
Proof.
  destruct (decide (val_is_intlike v1)) as [Hi1|Hni1];
  destruct (decide (val_is_intlike v2)) as [Hi2|Hni2];
    try (left; eapply vals_compare_intlike_pointerlike; by eauto).
  { destruct v1 as [l1| | | | ]; try by inversion Hi1.
    destruct v2 as [l2| | | | ]; try by inversion Hi2.
    destruct l1; try (by inversion Hi1);
    destruct l2; try (by inversion Hi2).
    all: try (left; by constructor).
    all: right; intros HH; inversion HH; naive_solver. }
  { destruct v1 as [l1| | | | ]; destruct v2 as [l2| | | |];
       try (right; intros HH; inversion HH; naive_solver).
    destruct l1; try (exfalso; apply Hni1; by constructor).
    3: right; intros HH; inversion HH; naive_solver.
    1: { destruct l2; try (exfalso; apply Hni2; by constructor).
    2, 3: right; intros HH; inversion HH; naive_solver.
    left; naive_solver. }
    destruct l2; try (exfalso; apply Hni2; by constructor).
    1, 3: right; intros HH; inversion HH; naive_solver.
    left; eapply vals_compare_loc. }
Defined.

Local Notation state := (gmap loc (option (list val))).

(** Equality and other typeclass facts (countable,...) *)
Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(* Global Instance of_outcome_inj : Inj (=) (=) of_outcome. *)
(* Proof. intros ?? H. destruct x, y; cbn in *; congruence. Qed. *)

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
     | Raise e, Raise e' => cast_if (decide (e = e'))
     | Try e r, Try e' r' => cast_if_and (decide (e = e')) (decide (r = r'))
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
     | Raise e, Raise e' => cast_if (decide (e = e'))
     | Try e r, Try e' r' => cast_if_and (decide (e = e')) (decide (r = r'))
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
  | LitBoxedInt n => inr (inr n)
  | LitInt n => inl (inl (inl n))
  | LitBool b => inl (inl (inr b))
  | LitUnit => inl (inr (inl ()))
  | LitLoc l => inl (inr (inr l))
  | LitForeign n => inr (inl n)
  end) (λ l, match l with
  | inl (inl (inl n)) => LitInt n
  | inl (inl (inr b)) => LitBool b
  | inl (inr (inl ())) => LitUnit
  | inl (inr (inr l)) => LitLoc l
  | inr (inl n) => LitForeign n
  | inr (inr n) => LitBoxedInt n
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
     | Raise e => GenNode 12 [go e]
     | Try e r => GenNode 13 [go e; go r]
     | AllocN e1 e2 => GenNode 14 [go e1; go e2]
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
     | GenNode 12 [e] => Raise (go e)
     | GenNode 13 [e; r] => Try (go e) (go r)
     | GenNode 14 [e1; e2] => AllocN (go e1) (go e2)
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
 - destruct e as [v| | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|try done..].
   unfold map; by induction ea as [|ex er ->]; simpl; f_equal.
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val (λ e, to_val e) _); auto using to_of_val. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate inhabitant.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO `{SI: indexT} := leibnizO state.
Canonical Structure locO `{SI: indexT} := leibnizO loc.
Canonical Structure valO `{SI: indexT} := leibnizO val.
Canonical Structure exprO `{SI: indexT} := leibnizO expr.

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
  | RaiseCtx
  | TryCtx (r : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | LoadNLCtx (v2 : val)
  | LoadNRCtx (e1 : expr)
  | StoreNLLCtx (v2 : val) (v3 : val)
  | StoreNLRCtx (e1 : expr) (v3 : val)
  | StoreNRRCtx (e1 : expr) (e2 : expr)
  | LengthCtx
  | ExternCtx (s : string) (va : list val) (ve : list expr).

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
  | RaiseCtx => Raise e
  | TryCtx r => Try e r
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

Definition is_try Ki :=
  match Ki with
  | TryCtx _ => true
  | _ => false
  end.

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
  | Raise e => Raise (subst_all g e)
  | Try e r => Try (subst_all g e) (subst_all g r)
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

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) (lit : Z → base_lit) : option base_lit :=
  match op with
  | PlusOp => Some $ lit (n1 + n2)
  | MinusOp => Some $ lit (n1 - n2)
  | MultOp => Some $ lit (n1 * n2)
  | QuotOp => Some $ lit (n1 `quot` n2)
  | RemOp => Some $ lit (n1 `rem` n2)
  | AndOp => Some $ lit (Z.land n1 n2)
  | OrOp => Some $ lit (Z.lor n1 n2)
  | XorOp => Some $ lit (Z.lxor n1 n2)
  | ShiftLOp => Some $ lit (n1 ≪ n2)
  | ShiftROp => Some $ lit (n1 ≫ n2)
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
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2 LitInt
    | LitV (LitBoxedInt n1), LitV (LitBoxedInt n2) => LitV <$> bin_op_eval_int op n1 n2 LitBoxedInt
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc (option (list val)) → gmap loc (option (list val))) (σ: state) : state := f σ.
Global Arguments state_upd_heap _ !_ /.

Inductive ml_function := MlFun (b : list binder) (e : expr).

(* Note that this way, a function where all arguments have the same name (say x), that returns x, returns the first argument *)
Fixpoint zip_args (an : list binder) (av : list val) : option (gmap string val) := match an, av with
  nil, nil => Some ∅
| (BNamed ax::ar), (vx::vr) => option_map (<[ax:=vx]>) (zip_args ar vr)
| (BAnon::ar), (vx::vr) => zip_args ar vr
| _, _ => None end.

Definition apply_function (f:ml_function) (av : list val) := match f with MlFun an e =>
    match (zip_args an av) with Some σ => Some (subst_all σ e) | _ => None end end.

Inductive head_step (p : gmap string ml_function) : expr → state → expr → state → Prop :=
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
  | TryS v r σ :
      head_step p (Try (Val v) r) σ (Val v) σ
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
  (* Silently diverge in case of out-of-bound accesses (or negative alloc size).
     We want to distinguish OOB accesses from other failures (which are UB),
     so that we can prove a type safety result. In a more realistic language
     we could have a dedicated failure state for OOB, or a mechanism for
     exceptions/panics... *)
  | AllocNWrongSizeS n v σ :
    (n < 0)%Z →
    head_step p (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
                (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
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
     p !! s = Some (MlFun args e) →
     apply_function (MlFun args e) va = Some res →
     head_step p (Extern s (map Val va)) σ res σ.

Definition head_reducible (p : gmap _ _) (e : expr) (σ : state) :=
  ∃ e' σ', head_step p e σ e' σ'.

Inductive prim_step p : expr → state → expr → state → Prop :=
  | Prim_step K e1 e2 σ1 σ2 e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step p e1' σ1 e2' σ2 → prim_step p e1 σ1 e2 σ2
  | Prim_step_raise K Ki e1 e2 σ1 v :
      e1 = fill (Ki :: K) (Raise (Val v)) → e2 = fill K (Raise (Val v)) →
      ¬is_try Ki → prim_step p e1 σ1 e2 σ1
  | Prim_step_try K e1 e2 σ1 r v :
      e1 = fill (TryCtx r :: K) (Raise (Val v)) → e2 = fill K (App r (Val v)) →
      prim_step p e1 σ1 e2 σ1.

(** External calls *)

Local Definition of_call fn (vs: list val) : expr :=
   Extern fn (map Val vs).

Local Definition is_call e fn vs K :=
  e = fill K (of_call fn vs).

(** Basic properties about the language *)

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

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_comp_item k K e : fill (k :: K) e = fill K (fill_item k e).
Proof. reflexivity. Qed.

Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof.
  intros e1 e2.
  induction K as [|Ki K IH] in e1, e2 |- *; rewrite /Inj; first done.
  rewrite !fill_comp_item. by intros ?%IH%fill_item_inj.
Qed.

Lemma val_head_stuck p e1 σ1 e2 σ2 :
  head_step p e1 σ1 e2 σ2 → to_val e1 = None.
Proof.
  inversion 1; simplify_eq; try done.
Qed.

Lemma outcome_head_stuck p e1 σ1 e2 σ2 :
  head_step p e1 σ1 e2 σ2 → to_outcome e1 = None.
Proof.
  inversion 1; simplify_eq; try done.
Qed.

Lemma head_ctx_item_step_val p Ki e σ1 e2 σ2 :
  head_step p (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
Proof.
  revert e2. induction Ki; try by (inversion_clear 1; simplify_option_eq; eauto).
  intros e2. inversion 1; subst. enough (exists k, Val k = e ∧ In k va0) as (k & <- & _) by easy.
  apply in_map_iff. rewrite H1. apply in_or_app. right. now left.
Qed.

Lemma head_ctx_item_step_outcome p Ki e σ1 e2 σ2 :
  head_step p (fill_item Ki e) σ1 e2 σ2 → is_Some (to_outcome e).
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

Lemma fill_item_no_outcome_inj Ki1 Ki2 e1 e2 :
  to_outcome e1 = None → to_outcome e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  intros Ho1 Ho2 Hf. eapply fill_item_no_val_inj;
  eauto; now apply comp_val_in_out.
Qed.

Lemma prim_step_inv p e1 e2 σ1 σ2 :
  prim_step p e1 σ1 e2 σ2 →
  (∃ K e1' e2', e1 = fill K e1' ∧ e2 = fill K e2' ∧ head_step p e1' σ1 e2' σ2) ∨
  (∃ K Ki v, e1 = fill (Ki :: K) (Raise (Val v)) ∧
             e2 = fill K (Raise (Val v)) ∧ ¬ is_try Ki ∧ σ1 = σ2) ∨
  (∃ K r v, e1 = fill (TryCtx r :: K) (Raise (Val v)) ∧
            e2 = fill K (App r (Val v)) ∧ σ1 = σ2).
Proof.
  inversion 1; subst.
  { left; do 3 eexists; eauto. }
  { right; left; do 5 eexists; eauto. }
  { repeat right; do 5 eexists; eauto. }
Qed.

Lemma head_prim_step p e1 σ1 e2 σ2 :
  head_step p e1 σ1 e2 σ2 → prim_step p e1 σ1 e2 σ2.
Proof. apply Prim_step with []; by rewrite ?fill_empty. Qed.

Local Lemma fill_outcome_val (K : list ectx_item) (e: expr) :
  (∃v, to_outcome (fill K e) = Some (OVal v)) → to_outcome (fill K e) = to_outcome e.
Proof.
  intros [v Hv]. revert v Hv. induction K as [|k1 K] using rev_ind; intros v Hv.
  1: done.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; try congruence.
  rewrite fill_app. simpl. destruct (fill K e); try congruence.
Qed.

Lemma fill_val (K : list ectx_item) (e: expr) :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros Hv. revert Hv. induction K as [|k1 K] using rev_ind; intros Hv.
  1: done.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; destruct Hv; try congruence.
Qed.

Local Lemma fill_val_2 (K : list ectx_item) (e: expr) v :
  fill K e = Val v → is_Some (to_val e).
Proof. intros HH. eapply (fill_val K). rewrite HH//. Qed.

Lemma fill_outcome (K : list ectx_item) (e: expr) :
  is_Some (to_outcome (fill K e)) → is_Some (to_outcome e).
Proof.
  intros Hv. revert Hv. induction K as [|k1 K] using rev_ind; intros Hv.
  1: done.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; destruct Hv; try congruence.
  apply IHK. destruct (fill K e); cbn; try congruence.
  eexists; eauto.
Qed.

Local Lemma fill_outcome_3 (K : list ectx_item) (e: expr) o :
  fill K e = of_outcome o → is_Some (to_outcome e).
Proof.
  intros HH. eapply (fill_outcome K).
  rewrite HH//. exists o. now apply to_of_outcome.
Qed.

Lemma to_outcome_of_call fn vs : to_outcome (of_call fn vs) = None.
Proof. rewrite /to_outcome /of_call //. Qed.

Local Lemma fill_call_val e K fn vs :
  fill K e = of_call fn vs → K = [] ∨ is_Some (to_val e).
Proof.
  revert e. destruct K as [|k1 K] using rev_ind; intros *; cbn; first by left.
  rewrite fill_app/=.
  destruct k1; (try by inversion 1); [].
  rewrite /of_call /=. inversion 1; subst.
  assert (In (fill K e) (map Val vs)) as [vv [Hvv' Hvv]]%in_map_iff.
  { rewrite -H2; apply in_app_iff; right; now left. }
  right. symmetry in Hvv'. now apply fill_val_2 in Hvv'.
Qed.

Local Lemma fill_call e K fn vs :
  fill K e = of_call fn vs → K = [] ∨ is_Some (to_outcome e).
Proof.
  intros H. apply fill_call_val in H as [H | H]; eauto.
  right. destruct e; destruct H as [v' H]; simpl in *; try congruence.
  eauto.
Qed.

Lemma fill_raise e K v : fill K e = Raise (Val v) → K = [] ∨ is_Some (to_outcome e).
Proof.
  revert e. destruct K as [|Ki K] using rev_ind; intros *; cbn; first by left.
  rewrite fill_app/=.
  destruct Ki; (try by inversion 1).
  cbn. inversion 1. right.
  now apply (fill_outcome_3 K e (OVal v)).
Qed.

Local Lemma fill_comp e K1 K2 :
  fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. rewrite /fill /comp_ectx foldl_app//. Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof.
  intros HH. destruct (to_val (fill K e)) eqn:Heq; try done.
  destruct (fill_val K e); try done. congruence.
Qed.

Lemma fill_not_outcome K e : to_outcome e = None → to_outcome (fill K e) = None.
Proof.
  intros HH. destruct (to_outcome (fill K e)) eqn:Heq; try done.
  destruct (fill_outcome K e); try done. congruence.
Qed.

Local Lemma outcome_prim_step p o σ1 e2 σ2:
  prim_step p (of_outcome o) σ1 e2 σ2 → False.
Proof.
  inversion 1; subst; symmetry in H0.
  { eapply outcome_head_stuck in H2.
    apply fill_outcome_3 in H0; destruct H0; congruence. }
  1: destruct Ki.
  all:(simpl in H0; apply fill_outcome_3 in H0;
       simpl in H0; destruct H0; congruence).
Qed.

Lemma head_ctx_step_val p K e σ1 e2 σ2 :
  head_step p (fill K e) σ1 e2 σ2 → K = [] ∨ is_Some (to_val e).
Proof.
  destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
  rewrite fill_app /=.
  intros [v' ?]%head_ctx_item_step_val%fill_val. right. exists v'.
  by repeat (case_match; simplify_eq).
Qed.

Lemma head_ctx_step_outcome p K e σ1 e2 σ2 :
  head_step p (fill K e) σ1 e2 σ2 → K = [] ∨ is_Some (to_outcome e).
Proof.
  destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
  rewrite fill_app /=.
  intros [v' ?]%head_ctx_item_step_outcome%fill_outcome. right. exists v'.
  by repeat (case_match; simplify_eq).
Qed.

Lemma fill_prefix_val : ∀ K K' e1 e1',
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  to_val e1' = None →
  ∃ K'', K' = comp_ectx K K'' ∨ K = comp_ectx K' K''.
Proof.
  intros * Hfill Hred Hredr; revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hredr. eexists. rewrite /comp_ectx app_nil_r; eauto. }
  rewrite !fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill; now apply fill_not_val. }
  simplify_eq. destruct (IH K') as [K'' [-> | ->]]; auto;
  rewrite /comp_ectx -app_assoc; eauto.
Qed.

Lemma fill_prefix_val_out : ∀ K K' e1 v,
  fill K e1 = fill K' (Raise (Val v)) →
  to_outcome e1 = None →
  ∃ K'', K' = comp_ectx K K''.
Proof.
  intros * Hfill Hout.
  assert (to_val e1 = None) as Hval by now eapply comp_val_in_out in Hout.
  assert (to_val (Raise (Val v)) = None) as Hval' by eauto.
  destruct (fill_prefix_val K K' e1 (Raise (Val v)) Hfill Hval Hval') as [K'' [-> | ->]]; eauto.
  rewrite -fill_comp in Hfill. apply fill_inj in Hfill; subst.
  apply fill_raise in Hfill. destruct Hfill; subst.
  - exists []; now cbn.
  - destruct H. congruence.
Qed.

Lemma fill_prefix : ∀ K K' e1 e1',
  fill K e1 = fill K' e1' →
  to_outcome e1 = None →
  to_outcome e1' = None →
  ∃ K'', K' = comp_ectx K K'' ∨ K = comp_ectx K' K''.
Proof.
  intros * Hfill Hv1 Hv2. eapply (fill_prefix_val); eauto;
  now apply comp_val_in_out.
Qed.

Lemma step_by_val  : ∀ p K K' e1 e1' σ1 e2 σ2,
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step p e1' σ1 e2 σ2 →
  ∃ K'', K' = comp_ectx K K''.
Proof.
  intros * Hfill Hval Hstep.
  assert (to_val e1' = None) as Hval'.
  { eapply val_head_stuck; eapply Hstep. }
  destruct (fill_prefix_val K K' e1 e1' Hfill Hval Hval') as [K'' [-> | ->]]; eauto.
  rewrite -fill_comp in Hfill. apply fill_inj in Hfill; subst.
  apply head_ctx_step_val in Hstep as [-> | [x Htv]].
  - now exists [].
  - now rewrite Htv in Hval.
Qed.

Lemma step_by_outcome : ∀ p K K' e1 e1' σ1 e2 σ2,
  fill K e1 = fill K' e1' →
  to_outcome e1 = None →
  head_step p e1' σ1 e2 σ2 →
  ∃ K'', K' = comp_ectx K K''.
Proof.
  intros * Hfill Hval Hstep.
  assert (to_outcome e1' = None) as Hval'.
  { eapply outcome_head_stuck; eapply Hstep. }
  destruct (fill_prefix K K' e1 e1' Hfill Hval Hval') as [K'' [-> | ->]]; eauto.
  rewrite -fill_comp in Hfill. apply fill_inj in Hfill; subst.
  apply head_ctx_step_outcome in Hstep as [-> | [x Htv]].
  - now exists [].
  - now rewrite Htv in Hval.
Qed.

Lemma fill_call_raise fn vs K K' v :
  ¬ fill K (of_call fn vs) = fill K' (Raise (Val v)).
Proof.
  intros * Hctx.
  assert (to_val (Extern fn (map Val vs)) = None ∧
          to_val (Raise (Val v)) = None ) as [Hve Hvr] by eauto.
  destruct (fill_prefix_val K K' _ _ Hctx Hve Hvr) as [K'' [Heq | Heq]];
  rewrite Heq in Hctx; rewrite -fill_comp in Hctx; apply fill_inj in Hctx.
  - symmetry in Hctx.
    destruct (fill_call_val (Raise (Val v)) K'' fn vs Hctx) as [->|Hval].
    + rewrite /of_call /= in Hctx. congruence.
    + destruct Hval as [x Hval]. congruence.
  - destruct (fill_raise (of_call fn vs) K'' v Hctx) as [->|Hval].
    + rewrite /of_call /= in Hctx. congruence.
    + unfold of_call in Hval. destruct Hval as [x Hval]. now cbn in Hval.
Qed.

Lemma call_head_step (p: gmap string ml_function) f vs σ1 e2 σ2 :
  head_step p (of_call f vs) σ1 e2 σ2 ↔
  ∃ (fn : ml_function),
    p !! f = Some fn ∧ Some e2 = apply_function fn vs ∧ σ2 = σ1.
Proof.
  split.
  - intros H. inversion H; subst. inversion H; subst.
    repeat econstructor; [apply H2|]. simplify_eq. congruence.
  - intros ([args ee] & H1 & H2 & ->). econstructor; eauto.
Qed.

Lemma prim_step_call_inv (p: gmap _ _) K f vs e' σ σ' :
  prim_step p (fill K (of_call f vs)) σ e' σ' →
  ∃ er fn, Some er = apply_function fn vs ∧ p !! f = Some fn ∧ e' = fill K er ∧ σ' = σ.
Proof.
  intros [(K' & e1 & e2 & Hctx & -> & Hstep) |
         [(K' & Ki & v  & Hctx & -> & _) |
          (K' & r  & v  & Hctx & Hf)]]%prim_step_inv;
  try now apply fill_call_raise in Hctx.
  { eapply step_by_outcome in Hstep as H'; eauto.
    destruct H' as [K'' ->].
    rewrite -fill_comp in Hctx. eapply fill_inj in Hctx.
    destruct (fill_call e1 K'' f vs) as [->|Ho]; eauto.
    - cbn in *; subst. apply call_head_step in Hstep as (?&?&?&?); simplify_eq.
      do 2 eexists. split_and!; eauto.
    - eapply outcome_head_stuck in Hstep. destruct Ho; congruence. }
Qed.

Local Lemma call_prim_step (p: gmap _ _) f vs K e σ1 e' σ2 :
  is_call e f vs K →
  prim_step p e σ1 e' σ2 ↔
  ∃ (fn : ml_function) (e2 : expr),
    p !! f = Some fn ∧ Some e2 = apply_function fn vs ∧ e' = fill K e2 ∧ σ2 = σ1.
Proof.
  unfold is_call. intros Hcall. split.
  { subst. intros HH%prim_step_call_inv. naive_solver. }
  { intros (fn & e2 & ? & ? & ? & ?); simplify_eq. econstructor; [done..|].
    apply call_head_step. eauto. }
Qed.

Local Lemma is_outcome_not_call e :
  is_Some (to_outcome e) → (∀ f vs C, ¬ is_call e f vs C).
Proof.
  destruct e; try by inversion 1. all: intros Hs *;
  unfold is_call; intros H.
  { assert (of_outcome (OVal v) = Val v) as He by easy.
    rewrite -He in H. symmetry in H.
    apply fill_outcome_3 in H. rewrite to_outcome_of_call in H.
    now destruct H. }
  { destruct Hs as [x Hs]. cbn in Hs. destruct e; try congruence.
    assert (of_outcome (OExn v) = Raise (Val v)) as He by easy.
    rewrite -He in H. symmetry in H.
    apply fill_outcome_3 in H. rewrite to_outcome_of_call in H.
    now destruct H. }
Qed.

Local Lemma is_call_in_cont e K1 K2 fn vs :
  is_call e fn vs K2 →
  is_call (fill K1 e) fn vs (comp_ectx K1 K2).
Proof. unfold is_call. rewrite -fill_comp. naive_solver. Qed.

Local Lemma is_call_of_call_inv fn vs fn' vs' K :
  is_call (of_call fn vs) fn' vs' K →
  fn' = fn ∧ vs' = vs ∧ K = [].
Proof.
  intros *. unfold is_call. intros HH.
  pose proof (fill_call _ _ _ _ (eq_sym HH)) as [?|?]; subst; cbn in *.
  * inversion HH; subst. apply stdpp_extra.map_inj in H1; eauto.
    intros *; by inversion 1.
  * by inversion H.
Qed.

Local Lemma prim_step_fill p K e σ e' σ' :
  prim_step p e σ e' σ' →
  prim_step p (fill K e) σ (fill K e') σ'.
Proof.
  intros [(K' & e1 & e2 & -> & -> & ?) |
         [(K' & Ki & v  & -> & -> & ? & ->) |
          (K' & r  & v  & -> & -> & ->)]]%prim_step_inv;
  rewrite !fill_comp; by econstructor.
Qed.

Local Lemma fill_step_inv K p e1' σ1 e2 σ2 :
  to_outcome e1' = None → prim_step p (fill K e1') σ1 e2 σ2 →
  ∃ e2', e2 = fill K e2' ∧ prim_step p e1' σ1 e2' σ2.
Proof.
  intros H1. inversion 1; simplify_eq.
  { destruct (step_by_outcome _ _ _ _ _ _ _ _ H0 H1 H3) as (K'' & ->).
    rewrite <- fill_comp in *.
    apply fill_inj in H0; simplify_eq. eexists. split; eauto.
    by econstructor. }
  { assert (to_val e1' = None ∧ to_val (Raise (Val v)) = None ) as [Hve Hvr]
    by (split; eauto; now apply comp_val_in_out).
    destruct (fill_prefix_val K _ _ _ H0 Hve Hvr) as [K'' [Heq | Heq]];
    rewrite Heq in H0; rewrite -fill_comp in H0; apply fill_inj in H0.
    - unfold comp_ectx in Heq. destruct K''.
      + cbn in *. subst. cbn in H1; congruence.
      + simpl in Heq. inversion Heq. rewrite fill_app.
        exists (fill K'' (Raise (Val v))).
        split; eauto. subst. eapply Prim_step_raise; eauto.
    - destruct (fill_raise e1' K'' v H0) as [Hs | Hs].
      + subst; cbn in *; subst. cbn in *; congruence.
      + destruct Hs as [o Hs]; subst; congruence. }
  { assert (to_val e1' = None ∧ to_val (Raise (Val v)) = None ) as [Hve Hvr]
    by (split; eauto; now apply comp_val_in_out).
    destruct (fill_prefix_val K _ _ _ H0 Hve Hvr) as [K'' [Heq | Heq]];
    rewrite Heq in H0; rewrite -fill_comp in H0; apply fill_inj in H0.
    - unfold comp_ectx in Heq. destruct K''.
      + cbn in *. subst. cbn in *; congruence.
      + simpl in Heq. inversion Heq. rewrite fill_app.
        exists (fill K'' (App r (Val v))).
        split; eauto. subst. eapply Prim_step_try; eauto.
    - destruct (fill_raise e1' K'' v H0) as [Hs | Hs].
      + subst; cbn in *; subst. cbn in *; congruence.
      + destruct Hs as [o Hs]; subst; congruence. }
Qed.

Local Lemma head_reducible_prim_step_ctx p K e1 σ1 e2 σ2 :
  head_reducible p e1 σ1 →
  prim_step p (fill K e1) σ1 e2 σ2 →
  ∃ e2', e2 = fill K e2' ∧ head_step p e1 σ1 e2' σ2.
Proof.
  intros (e2''&σ2''&HhstepK)
         [(K' & e1' & e2' & HKe1 & -> & Hstep) |
         [(K' & Ki  & v   & HKe1 & -> & Ht & ->) |
          (K' & r   & v   & HKe1 & -> & ->)]]%prim_step_inv.
  { edestruct (step_by_outcome p K) as [K'' ?];
    eauto using outcome_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_outcome in HhstepK as [?|[v ?]]; simplify_eq.
    - by rewrite //=.
    - apply outcome_head_stuck in Hstep; simplify_eq. }
  { edestruct (fill_prefix_val _ _ _ _ HKe1);
    eauto using val_head_stuck; simplify_eq/=.
    destruct H as [Heq | Heq].
    - rewrite -fill_comp_item in HKe1. rewrite Heq in HKe1.
      rewrite fill_app in HKe1. apply fill_inj in HKe1. subst.
      assert (x = [] ∨ is_Some (to_val (Raise (Val v)))) as [-> | [o Ho]]
      by (eapply head_ctx_step_val; apply HhstepK); simpl in *; try congruence.
      inversion HhstepK.
    - subst. rewrite fill_app in HKe1. simpl in *.
      apply fill_inj, fill_item_inj in HKe1.
      destruct (fill_raise e1 x v HKe1) as [-> | [o Ho]]; simpl in *; subst.
      + inversion HhstepK.
      + apply outcome_head_stuck in HhstepK. subst; congruence. }
  { edestruct (fill_prefix_val _ _ _ _ HKe1);
    eauto using val_head_stuck.
    destruct H as [Heq | Heq].
    - rewrite Heq in HKe1.
      rewrite fill_app in HKe1. apply fill_inj in HKe1. subst.
      assert (x = [] ∨ is_Some (to_val (Raise (Val v)))) as [-> | [o Ho]]
      by (eapply head_ctx_step_val; apply HhstepK); simpl in *; try congruence.
      inversion HhstepK.
    - subst. rewrite fill_app in HKe1. simpl in *.
      apply fill_inj in HKe1. inversion HKe1.
      destruct (fill_raise e1 x v H0) as [-> | [o Ho]]; simpl in *; subst.
      + inversion HhstepK.
      + apply outcome_head_stuck in HhstepK. subst; congruence. }
Qed.

Lemma head_reducible_prim_step p e1 σ1 e2 σ2 :
  head_reducible p e1 σ1 →
  prim_step p e1 σ1 e2 σ2 →
  head_step p e1 σ1 e2 σ2.
Proof.
  intros.
  edestruct (head_reducible_prim_step_ctx p []) as (?&?&?);
    rewrite ?fill_empty; eauto.
  by simplify_eq.
Qed.

#[local] Notation omap f x := (match x with Some v => f v | None => None end).

Fixpoint unmap_val el :=
  match el with
  | Val v :: er => omap (fun vr => Some (v::vr)) (unmap_val er)
  | [] => Some nil
  | _ => None
  end.

Local Definition to_call_head (e : expr) :=
  match e with
  | Extern fn el => omap (λ vs, Some (fn, vs)) (unmap_val el)
  | _ => None
  end.

Lemma map_unmap_val l : unmap_val (map Val l) = Some l.
Proof.
  induction l.
  - easy.
  - cbn. rewrite IHl. easy.
Qed.

Lemma unmap_val_map le lv : unmap_val le = Some lv → map Val lv = le.
Proof.
  induction le in lv|-*.
  - intros H. injection H. intros <-. easy.
  - cbn. destruct a. 2-20:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Local Lemma prim_step_call_dec p e σ e' σ' :
  prim_step p e σ e' σ' →
  (∃ fn vs K, is_call e fn vs K) ∨ (∀ fn vs K, ¬ is_call e fn vs K).
Proof.
  intros [(K' & e1' & e2' & HKe1 & -> & Hstep) |
         [(K' & Ki  & v   & HKe1 & -> & Ht & ->) |
          (K' & r   & v   & HKe1 & -> & ->)]]%prim_step_inv; subst;
  try (right; intros fn vs K Hcall%eq_sym; now apply fill_call_raise in Hcall).
  destruct (to_outcome e1') eqn:Hval.
  { exfalso. apply outcome_head_stuck in Hstep. congruence. }

  destruct (to_call_head e1') as [[fn vs]|] eqn:Hcall.
  { assert (∃ fn vs, e1' = of_call fn vs) as (fn' & vs' & ?).
    { unfold to_call_head in Hcall. repeat case_match; simplify_eq.
      eapply unmap_val_map in H0. subst; eauto. } subst.
      apply call_head_step in Hstep as (?&?&?&?); simplify_eq.
      unfold is_call. eauto. }

  right. unfold is_call, of_call.
  intros fn vs K'' Hcall'%eq_sym.
  pose proof Hcall' as Hcall''.
  eapply step_by_outcome in Hcall'' as (?&?); eauto; subst.
  rewrite -fill_comp in Hcall'. apply fill_inj in Hcall'.
  symmetry in Hcall'. pose proof Hcall' as Hcall''.
  apply fill_call in Hcall'' as [|]; cbn in *; subst.
  - cbn in Hcall'; subst. rewrite /= map_unmap_val // in Hcall.
  - destruct H; congruence. 
Qed.

Local Lemma prim_step_no_call p1 p2 e σ e' σ' :
  (∀ f vs K, ¬ is_call e f vs K) →
  prim_step p1 e σ e' σ' →
  prim_step p2 e σ e' σ'.
Proof.
  intros Hncall.
  intros [(K' & e1' & e2' & HKe1 & -> & Hstep) |
         [(K' & Ki  & v   & HKe1 & -> & Ht & ->) |
          (K' & r   & v   & HKe1 & -> & ->)]]%prim_step_inv; subst.
  { inversion Hstep; subst.
    all: try repeat (econstructor; eauto).
    exfalso. eapply Hncall. done. }
  { apply (Prim_step_raise p2 K' Ki _ _ _ v); eauto. }
  { apply (Prim_step_try p2 K' _ _ _ r v); eauto. }
Qed.

End ML_lang.
Export ML_lang.
