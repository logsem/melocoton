From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton Require Import stdpp_extra language_commons.
From melocoton.c_interface Require Import defs.

(* Engineering note: definitions and lemmas defined as [Local] correspond to
   fields of [LanguageMixin] that thus get re-exported as generic functions on a
   [language]. We define them as local to avoid the ml_lang-specific name
   clashing with the generic name, and always pick the generic name.
*)

Declare Scope c_expr_scope.
Delimit Scope c_expr_scope with CE.

Module C_lang.

Inductive un_op : Set :=
  | NegOp | NotOp | BitwiseNotOp | Ptr2Int | Int2Ptr .
Inductive bin_op : Set :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30/-4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | PtrOffsetOp | PtrDiffOp.

Unset Elimination Schemes.
Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Exception propagation *)
  | Raise (v : val)
  (* Substitution *)
  | Var (x : string)
  | Let (x : binder) (e1 e2 : expr)
  (* Memory *)
  | Load (e : expr)
  | Store (e0 e1 : expr) (* e0 <- e1 *)
  | Malloc (e1 : expr)
  | Free (e0 e1 : expr) (* e1 is size *)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  (* Control flow *)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  | FunCall (e0 : expr) (ee : list expr).
Set Elimination Schemes.

Definition expr_rect (P : expr → Type) :
    (∀ v : val, P (Val v))
  → (∀ x : string, P (Var x))
  → (∀ v : val, P (Raise v))
  → (∀ (x : binder) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (Let x e1 e2))
  → (∀ e : expr, P e → P (Load e))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Store e0 e1))
  → (∀ e1 : expr, P e1 → P (Malloc e1))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Free e0 e1))
  → (∀ (op : un_op) (e : expr), P e → P (UnOp op e))
  → (∀ (op : bin_op) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (While e0 e1))
  → (∀ e0 : expr, P e0 → ∀ ee : list expr, (forall ei, In2 ei ee -> P ei) -> P (FunCall e0 ee))
  → ∀ e : expr, P e.
Proof.
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Raise v => H3 v
     | Let x0 e3 e4 => H4 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H5 e1 (IH e1)
     | Store e2 e3 => H6 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H7 e0 (IH e0)
     | Free e2 e3 => H8 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H9 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H10 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H11 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H12 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H13 e1 (IH e1) ee0 
          ((fix IHl (ll:list expr) {struct ll} : forall (x:expr) (i:In2 x ll), P x :=
            match ll as ll0 return forall (x:expr) (i:In2 x ll0), P x
            with nil => fun x i => False_rect _ i 
            | ex::er => fun x i => match i with 
                                     inl H1 => match H1 in (_ = xe) return P xe with eq_refl => IH ex end
                                   | inr H2 => IHl er x H2 end end) ee0)
     end).
Defined.

Definition expr_ind (P : expr → Prop) :
    (∀ v : val, P (Val v))
  → (∀ x : string, P (Var x))
  → (∀ v : val, P (Raise v))
  → (∀ (x : binder) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (Let x e1 e2))
  → (∀ e : expr, P e → P (Load e))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Store e0 e1))
  → (∀ e1 : expr, P e1 → P (Malloc e1))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Free e0 e1))
  → (∀ (op : un_op) (e : expr), P e → P (UnOp op e))
  → (∀ (op : bin_op) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (While e0 e1))
  → (∀ e0 : expr, P e0 → ∀ ee : list expr, (forall ei, In ei ee -> P ei) -> P (FunCall e0 ee))
  → ∀ e : expr, P e.
Proof.
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Raise v => H3 v
     | Let x0 e3 e4 => H4 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H5 e1 (IH e1)
     | Store e2 e3 => H6 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H7 e0 (IH e0)
     | Free e2 e3 => H8 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H9 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H10 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H11 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H12 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H13 e1 (IH e1) ee0 
          ((fix IHl (ll:list expr) {struct ll} : forall (x:expr) (i:In x ll), P x :=
            match ll as ll0 return forall (x:expr) (i:In x ll0), P x
            with nil => fun x i => False_rect _ i 
            | ex::er => fun x i => match i with 
                                     or_introl H1 => match H1 in (_ = xe) return P xe with eq_refl => IH ex end
                                   | or_intror H2 => IHl er x H2 end end) ee0)
     end).
Qed.


Definition expr_val_ind (P : expr → Prop) (Pv : val → Prop):
    (∀ v : val, P (Val v))
  → (∀ x : string, P (Var x))
  → (∀ v : val, P (Raise v))
  → (∀ (x : binder) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (Let x e1 e2))
  → (∀ e : expr, P e → P (Load e))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Store e0 e1))
  → (∀ e1 : expr, P e1 → P (Malloc e1))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Free e0 e1))
  → (∀ (op : un_op) (e : expr), P e → P (UnOp op e))
  → (∀ (op : bin_op) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (While e0 e1))
  → (∀ e0 : expr, P e0 → ∀ ee : list expr, (forall ei, In ei ee -> P ei) -> P (FunCall e0 ee))
  → ∀ e : expr, P e.
Proof.
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Raise v => H3 v
     | Let x0 e3 e4 => H4 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H5 e1 (IH e1)
     | Store e2 e3 => H6 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H7 e0 (IH e0)
     | Free e2 e3 => H8 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H9 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H10 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H11 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H12 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H13 e1 (IH e1) ee0 
          ((fix IHl (ll:list expr) {struct ll} : forall (x:expr) (i:In x ll), P x :=
            match ll as ll0 return forall (x:expr) (i:In x ll0), P x
            with nil => fun x i => False_rect _ i 
            | ex::er => fun x i => match i with 
                                     or_introl H1 => match H1 in (_ = xe) return P xe with eq_refl => IH ex end
                                   | or_intror H2 => IHl er x H2 end end) ee0)
     end).
Qed.

Definition expr_rec (P : expr → Set) :
    (∀ v : val, P (Val v))
  → (∀ x : string, P (Var x))
  → (∀ v : val, P (Raise v))
  → (∀ (x : binder) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (Let x e1 e2))
  → (∀ e : expr, P e → P (Load e))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Store e0 e1))
  → (∀ e1 : expr, P e1 → P (Malloc e1))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (Free e0 e1))
  → (∀ (op : un_op) (e : expr), P e → P (UnOp op e))
  → (∀ (op : bin_op) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
  → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → P (While e0 e1))
  → (∀ e0 : expr, P e0 → ∀ ee : list expr, (forall ei, In2 ei ee -> P ei) -> P (FunCall e0 ee))
  → ∀ e : expr, P e.
Proof.
  apply expr_rect.
Defined.

Bind Scope c_expr_scope with expr.

Inductive function := Fun (b : list binder) (e : expr).

Definition arity (F : function) := match F with Fun b e => length b end.

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
  | OExn v => Raise v
  end.

Local Definition to_outcome (e : expr) :=
  match e with
  | Val v => Some (OVal v)
  | Raise v => Some (OExn v)
  | _ => None
  end.

Local Lemma to_of_outcome o : to_outcome (of_outcome o) = Some o.
Proof. destruct o; try done. Qed.
Local Lemma of_to_outcome e o : to_outcome e = Some o → of_outcome o = e.
Proof. destruct e; inversion 1; try done. Qed.

Lemma comp_val_in_out e : to_outcome e = None → to_val e = None.
Proof. destruct e; eauto. cbn. congruence. Qed.

(** Equality and other typeclass stuff *)
Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance of_outcome_inj : Inj (=) (=) of_outcome.
Proof. intros ??. destruct x, y; cbn; congruence. Qed.

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
     | Raise v, Raise v' => cast_if (decide (v = v'))
     | Let x e1 e2, Let x' e1' e2' =>
        cast_if_and3 (decide (x = x')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Malloc e, Malloc e' => cast_if (decide (e = e'))
     | Free e1 e2, Free e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | While e1 e2, While e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | FunCall x el, FunCall x' el' => 
        let gol := (fix gol (l1 l2 : list expr) {struct l1} : Decision (l1 = l2) :=
                       match l1, l2 with
                       | nil, nil => left eq_refl
                       | xl::xr, xl'::xr' => cast_if_and (decide (xl = xl')) (decide (xr = xr'))
                       | _, _ => right _
                       end)
        in cast_if_and (decide (x = x')) (@decide (el = el') (gol _ _))
     | _, _ => right _
     end); try (clear gol); (clear go; abstract intuition congruence).
Defined.

Global Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | NotOp => 1 | BitwiseNotOp => 2 | Ptr2Int => 3 | Int2Ptr => 4 end)
  (λ n, match n with 0 => NegOp | 1 => NotOp | 2 => BitwiseNotOp | 3 => Ptr2Int | _ => Int2Ptr end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | PtrOffsetOp => 13 | PtrDiffOp => 14 
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | 13 => PtrOffsetOp | _ => PtrDiffOp
  end) _); by intros [].
Qed.

Global Instance expr_countable : Countable expr.
Proof. (* string + binder + un_op + bin_op + val *)
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [GenLeaf (inr (inr (inr (inr v))))]
     | Var x => GenLeaf (inl x)
     | Raise v => GenNode 1 [GenLeaf (inr (inr (inr (inr v))))]
     | Let x e1 e2 => GenNode 2 [GenLeaf (inr (inl x)); go e1; go e2]
     | Load e => GenNode 3 [go e]
     | Store e1 e2 => GenNode 4 [go e1; go e2]
     | Malloc e => GenNode 5 [go e]
     | Free e1 e2 => GenNode 6 [go e1; go e2]
     | UnOp op e => GenNode 7 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 8 [GenLeaf (inr (inr (inr (inl op)))); go e1; go e2]
     | If e0 e1 e2 => GenNode 9 [go e0; go e1; go e2]
     | While e1 e2 => GenNode 10 [go e1; go e2]
     | FunCall ef ea => GenNode 11 (go ef :: map go ea)
     end).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [GenLeaf (inr (inr (inr (inr v))))] => Val v
     | GenLeaf (inl x) => Var x
     | GenNode 1 [GenLeaf (inr (inr (inr (inr v))))] => Raise v
     | GenNode 2 [GenLeaf (inr (inl x)); e1; e2] => Let x (go e1) (go e2)
     | GenNode 3 [e] => Load (go e)
     | GenNode 4 [e1; e2] => Store (go e1) (go e2)
     | GenNode 5 [e] => Malloc (go e)
     | GenNode 6 [e1; e2] => Free (go e1) (go e2)
     | GenNode 7 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 8 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 9 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 10 [e1; e2] => While (go e1) (go e2)
     | GenNode 11 (ef :: ea) => FunCall (go ef) (map go ea)
     | _ => Val $ LitV (LitInt 0) (* dummy *)
     end).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ ).
 destruct e as [ | | | | | | | | | | | |ef ee]; simpl; f_equal.
 1-17: done.
 all: unfold map; by induction ee as [|ex er ->]; simpl; f_equal.
Qed.

Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure locO {SI:indexT} := leibnizO loc.
Canonical Structure exprO {SI:indexT} := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  | LetCtx (x : binder) (e2 : expr)
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | MallocCtx
  | FreeLCtx (e2 : expr)
  | FreeRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | IfCtx (e1 e2 : expr)
  | FunCallLCtx (ea : list expr)
  | FunCallRCtx (vf : val) (va : list val) (ve : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | LetCtx x e2 => Let x e e2
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (of_val v1) e
  | MallocCtx => Malloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | UnOpCtx op => UnOp op e
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | BinOpLCtx op e2 => BinOp op e e2
  | IfCtx e1 e2 => If e e1 e2
  | FunCallLCtx ea => FunCall e ea
  | FunCallRCtx vf va ve => FunCall (of_val vf) (map of_val va ++ [e] ++ ve)
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
  | Raise _ => e
  | Var y => match g !! y with None => Var y | Some k => Val k end
  | Let (BNamed s) e1 e2 => Let (BNamed s) (subst_all g e1) $ subst_all (delete s g) e2
  | Let (BAnon) e1 e2 => Let (BAnon) (subst_all g e1) $ subst_all g e2
  | Load e => Load (subst_all g e)
  | Store e1 e2 => Store (subst_all g e1) (subst_all g e2)
  | Malloc e => Malloc (subst_all g e)
  | Free e1 e2 => Free (subst_all g e1) (subst_all g e2)
  | UnOp op e => UnOp op (subst_all g e)
  | BinOp op e1 e2 => BinOp op (subst_all g e1) (subst_all g e2)
  | If e0 e1 e2 => If (subst_all g e0) (subst_all g e1) (subst_all g e2)
  | While e1 e2 => While (subst_all g e1) (subst_all g e2)
  | FunCall ef ea => FunCall (subst_all g ef) (map (subst_all g) ea)
  end.

Definition subst (x : string) (v : val) (e : expr) : expr :=
  subst_all {[x:=v]} e.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | NotOp, LitV (LitInt 0) => Some $ LitV $ LitInt 1
  | NotOp, LitV (LitInt _) => Some $ LitV $ LitInt 0
  | BitwiseNotOp, LitV (LitInt n) => Some $ LitV $ LitInt $ Z.lnot $ n
  | Int2Ptr, LitV (LitInt n) => Some $ LitV $ LitLoc $ Loc $ n
  | Ptr2Int, LitV (LitLoc (Loc n)) => Some $ LitV $ LitInt n
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option base_lit :=
  match op, v1, v2 with
  | PlusOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 + n2)
  | MinusOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 - n2)
  | MultOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 * n2)
  | QuotOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 `quot` n2)
  | RemOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 `rem` n2)
  | AndOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (Z.land n1 n2)
  | OrOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (Z.lor n1 n2)
  | XorOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 ≪ n2)
  | ShiftROp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitInt (n1 ≫ n2)
  | LeOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp, LitV (LitInt n1), LitV (LitInt n2) => Some $ LitBool (bool_decide (n1 = n2))
  | LeOp, LitV (LitLoc (Loc n1)), LitV (LitLoc (Loc n2)) => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp, LitV (LitLoc (Loc n1)), LitV (LitLoc (Loc n2)) => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp, LitV (LitLoc (Loc n1)), LitV (LitLoc (Loc n2)) => Some $ LitBool (bool_decide (n1 = n2))
  | EqOp, LitV (LitFunPtr n1), LitV (LitFunPtr n2) => Some $ LitBool (bool_decide (n1 = n2))
  | EqOp, LitV LitNull,       LitV (LitLoc _)    => Some $ LitBool false
  | EqOp, LitV LitNull,       LitV (LitFunPtr _) => Some $ LitBool false
  | EqOp, LitV (LitLoc _),    LitV LitNull       => Some $ LitBool false
  | EqOp, LitV (LitFunPtr _), LitV LitNull       => Some $ LitBool false
  | EqOp, LitV LitNull,       LitV LitNull       => Some $ LitBool true
  | PtrOffsetOp, LitV (LitLoc l1), LitV (LitInt n2) => Some $ LitLoc $ loc_add l1 n2
  | PtrOffsetOp, LitV (LitInt n1), LitV (LitLoc l2) => Some $ LitLoc $ loc_add l2 n1
  | PtrDiffOp, LitV (LitLoc (Loc n1)), LitV (LitLoc (Loc n2)) => Some $ LitInt $ (n1 - n2)
  | _, _, _ => None
  end%Z.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : heap_cell) (σ : c_state) : c_state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=v]> σ.
Proof.
  rewrite /state_init_heap /= /state_upd_heap.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Definition asTruth (v:val) : bool := match v with
  | LitV (LitInt 0) => false
  | LitV (LitInt _) => true
  | LitV (LitLoc (Loc 0)) => false
  | LitV (LitLoc (Loc _)) => true
  | LitV (LitFunPtr p) => true
  | LitV (LitNull) => false end.

(* Note that this way, a function where all arguments have the same name (say x), that returns x, returns the first argument *)
Fixpoint zip_args (an : list binder) (av : list val) : option (gmap string val) := match an, av with
  nil, nil => Some ∅
| (BNamed ax::ar), (vx::vr) => option_map (<[ax:=vx]>) (zip_args ar vr)
| (BAnon::ar), (vx::vr) => zip_args ar vr
| _, _ => None end.

Definition apply_function (f:function) (av : list val) := match f with Fun an e =>
    match (zip_args an av) with Some σ => Some (subst_all σ e) | _ => None end end.

Inductive head_step (p : gmap string function) : expr → c_state → expr → c_state → Prop :=
  | LetS x v1 e2 ee σ :
     ee = subst' x v1 e2 ->
     head_step p (Let x (Val v1) e2) σ ee σ
  | LoadS l v σ :
     σ !! l = Some $ Storing v →
     head_step p (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
  | StoreS l k w σ :
     σ !! l = Some $ (Some k) →
     head_step p (Store (Val $ LitV $ LitLoc l) (Val w)) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=Storing w]> σ)
  | MallocS n σ l :
     (0 < n)%Z →
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ !! (l +ₗ i) = None) →
     head_step p (Malloc (Val $ LitV $ LitInt n)) σ
               (Val $ LitV $ LitLoc l) (state_init_heap l n Uninitialized σ)
  | FreeS l n σ :
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → ∃ v, σ !! (l +ₗ i) = Some $ Some v) →
     head_step p (Free (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt n)) σ
               (Val $ LitV LitUnit) (state_init_heap l n Deallocated σ)
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step p (UnOp op (Val v)) σ (Val v') σ
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step p (BinOp op (Val v1) (Val v2)) σ (Val (LitV v')) σ
  | IfTrueS v0 e1 e2 σ :
     asTruth v0 = true →
     head_step p (If (Val v0) e1 e2) σ e1 σ
  | IfFalseS v0 e1 e2 σ :
     asTruth v0 = false →
     head_step p (If (Val v0) e1 e2) σ e2 σ
  | WhileS e1 e2 σ :
     head_step p (While e1 e2) σ (If e1 (Let BAnon e2 (While e1 e2)) (Val $ LitV $ LitInt 0)) σ
  | FunCallS s va args res e σ :
     p !! s = Some (Fun args e) →
     apply_function (Fun args e) va = Some res →
     head_step p (FunCall (Val $ LitV $ LitFunPtr s) (map Val va)) σ res σ.

Definition head_reducible (p : gmap _ _) (e : expr) (σ : c_state) :=
  ∃ e' σ', head_step p e σ e' σ'.

Inductive prim_step p : expr → c_state → expr → c_state → Prop :=
  | Prim_step K e1 e2 σ1 σ2 e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step p e1' σ1 e2' σ2 → prim_step p e1 σ1 e2 σ2
  | Prim_step_raise K Ki e1 e2 σ1 σ2 v :
      e1 = fill (Ki :: K) (Raise v) → e2 = fill K (Raise v) →
      prim_step p e1 σ1 e2 σ2.

(** External calls *)

Local Definition of_call fn (vs: list val) : expr :=
   FunCall (Val $ LitV $ LitFunPtr fn) (map Val vs).

Local Definition is_call e fn vs K :=
  e = fill K (of_call fn vs).

(** Basic properties about the language *)

Lemma alloc_fresh p n σ :
  let l := fresh_locs (dom σ) in
  (0 < n)%Z →
  head_step p (Malloc ((Val $ LitV $ LitInt $ n))) σ
            (Val $ LitV $ LitLoc l) (state_init_heap l n Uninitialized σ).
Proof.
  intros.
  apply MallocS; first done.
  intros. apply not_elem_of_dom.
  by apply fresh_locs_fresh.
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
Proof. revert e2. induction Ki. 1-12: inversion_clear 1; simplify_option_eq; eauto.
       - inversion 1. enough (exists k, Val k = e ∧ In k va0) as (k & <- & _) by easy.
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
  (∃ K Ki v, e1 = fill (Ki :: K) (Raise v) ∧
             e2 = fill K (Raise v)).
Proof. inversion 1; subst; [left | right]; do 3 eexists; eauto. Qed.

Lemma head_prim_step p e1 σ1 e2 σ2 :
  head_step p e1 σ1 e2 σ2 → prim_step p e1 σ1 e2 σ2.
Proof. apply Prim_step with []; by rewrite ?fill_empty. Qed.

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

Local Lemma fill_outcome (K : list ectx_item) (e: expr) :
  is_Some (to_outcome (fill K e)) → to_outcome (fill K e) = to_outcome e.
Proof.
  intros [v Hv]. revert v Hv. induction K as [|k1 K] using rev_ind; intros v Hv.
  1: done.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; try congruence.
Qed.

Lemma fill_outcome2 (K : list ectx_item) (e: expr) :
  is_Some (to_outcome (fill K e)) → is_Some (to_outcome e).
Proof.
  intros H. assert (is_Some (to_outcome (fill K e))) as [x Heq] by done.
  apply fill_outcome in H. rewrite Heq in H; done.
Qed.

Local Lemma fill_outcome_3 (K : list ectx_item) (e: expr) o :
  fill K e = (of_outcome o) → is_Some (to_outcome e).
Proof.
  intros HH. eapply (fill_outcome2 K).
  rewrite HH//. exists o. now apply to_of_outcome.
Qed.

Local Lemma fill_outcome_val (K : list ectx_item) (e: expr) :
  (∃v, to_outcome (fill K e) = Some (OVal v)) → to_outcome (fill K e) = to_outcome e.
Proof.
  intros [v Hv]. revert v Hv. induction K as [|k1 K] using rev_ind; intros v Hv.
  1: done.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; try congruence.
Qed.

Lemma to_outcome_of_call fn vs : to_outcome (of_call fn vs) = None.
Proof. rewrite /to_outcome /of_call //. Qed.

Local Lemma fill_call_val e K fn vs :
  fill K e = of_call fn vs → K = [] ∨ is_Some (to_val e).
Proof.
  revert e. destruct K as [|k1 K] using rev_ind; intros *; cbn; first by left.
  rewrite fill_app/=.
  destruct k1; (try by inversion 1); [|].
  + destruct (fill K e) eqn:Heq; cbn; (try by inversion 1); [].
    apply fill_val_2 in Heq; eauto.
  + destruct vf. destruct l; cbn; (try by inversion 1); []. inversion 1; simplify_eq.
    clear H.
  assert (In (fill K e) (map Val vs)) as [vv [Hvv' Hvv]]%in_map_iff.
  { rewrite -H2; apply in_app_iff; right; now left. }
  symmetry in Hvv'.
  apply fill_val_2 in Hvv' as [? ?]. eauto.
Qed.

Local Lemma fill_call e K fn vs :
  fill K e = of_call fn vs → K = [] ∨ is_Some (to_outcome e).
Proof.
  intros H. apply fill_call_val in H as [H | H]; eauto.
  right. destruct e; destruct H as [v' H]; simpl in *; try congruence.
  eauto.
Qed.

Lemma fill_raise e K v : fill K e = Raise v → K = [] ∨ is_Some (to_outcome e).
Proof.
  revert e. destruct K as [|Ki K] using rev_ind; intros *; cbn; first by left.
  rewrite fill_app/=.
  destruct Ki; (try by inversion 1).
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
  inversion 1; subst.
  { symmetry in H0. eapply fill_outcome_3 in H0 as [? ?].
    eapply outcome_head_stuck in H2. congruence. }
  destruct Ki;
  symmetry in H0; simpl in *; apply fill_outcome_3 in H0 as [o' Ho];
  simpl in *; congruence.
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
  intros [v' ?]%head_ctx_item_step_outcome%fill_outcome2. right. exists v'.
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

Lemma fill_prefix : ∀ K K' e1 e1',
  fill K e1 = fill K' e1' →
  to_outcome e1 = None →
  to_outcome e1' = None →
  ∃ K'', K' = comp_ectx K K'' ∨ K = comp_ectx K' K''.
Proof.
  intros * Hfill Hv1 Hv2. eapply (fill_prefix_val); eauto;
  now apply comp_val_in_out.
Qed.

Lemma step_by_outcome  : ∀ p K K' e1 e1' σ1 e2 σ2,
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
  ¬ fill K (of_call fn vs) = fill K' (Raise v).
Proof.
  intros * Hctx.
  assert (to_val (of_call fn vs) = None ∧
          to_val (Raise v) = None ) as [Hve Hvr] by eauto.
  destruct (fill_prefix_val K K' _ _ Hctx Hve Hvr) as [K'' [Heq | Heq]];
  rewrite Heq in Hctx; rewrite -fill_comp in Hctx; apply fill_inj in Hctx.
  - symmetry in Hctx.
    destruct (fill_call_val (Raise v) K'' fn vs Hctx) as [->|Hval].
    + rewrite /of_call /= in Hctx. congruence.
    + destruct Hval as [x Hval]. congruence.
  - destruct (fill_raise (of_call fn vs) K'' v Hctx) as [->|Hval].
    + rewrite /of_call /= in Hctx. congruence.
    + unfold of_call in Hval. destruct Hval as [x Hval]. now cbn in Hval.
Qed.

Lemma call_head_step (p: gmap string function) f vs σ1 e2 σ2 :
  head_step p (of_call f vs) σ1 e2 σ2 ↔
  ∃ (fn : function),
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
          (K' & Ki & v  & Hctx & ->)]%prim_step_inv;
  try now apply fill_call_raise in Hctx.
  eapply step_by_outcome in Hstep as H'; eauto.
  destruct H' as [K'' Hctx']; subst K'.
  rewrite -fill_comp in Hctx. eapply fill_inj in Hctx.
  destruct (fill_call e1 K'' f vs) as [->|Hval]; auto.
  - cbn in *; subst. apply call_head_step in Hstep as (?&?&?&?); simplify_eq.
    do 2 eexists. split_and!; eauto.
  - eapply outcome_head_stuck in Hstep. destruct Hval; congruence.
Qed.

Local Lemma call_prim_step (p: gmap _ _) f vs K e σ1 e' σ2 :
  is_call e f vs K →
  prim_step p e σ1 e' σ2 ↔
  ∃ (fn : function) (e2 : expr),
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
  { destruct Hs as [x Hs]. cbn in Hs.
    assert (of_outcome (OExn v) = Raise v) as He by easy.
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
  intros [(K' & e1 & e2 & -> & -> & Hstep) |
          (K' & Ki & v  & -> & ->)]%prim_step_inv;
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
  { assert (to_val e1' = None ∧ to_val (Raise v) = None ) as [Hve Hvr]
    by (split; eauto; now apply comp_val_in_out).
    destruct (fill_prefix_val K _ _ _ H0 Hve Hvr) as [K'' [Heq | Heq]];
    rewrite Heq in H0; rewrite -fill_comp in H0; apply fill_inj in H0.
    - unfold comp_ectx in Heq. destruct K''.
      + cbn in *. subst. cbn in H1; congruence.
      + simpl in Heq. inversion Heq. rewrite fill_app.
        exists (fill K'' (Raise v)).
        split; eauto. subst. eapply Prim_step_raise; eauto.
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
          (K' & Ki  & v   & HKe1 & ->)]%prim_step_inv.
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
      assert (x = [] ∨ is_Some (to_val (Raise v))) as [-> | [o Ho]]
      by (eapply head_ctx_step_val; apply HhstepK); simpl in *; try congruence.
      inversion HhstepK.
    - subst. rewrite fill_app in HKe1. simpl in *.
      apply fill_inj, fill_item_inj in HKe1.
      destruct (fill_raise e1 x v HKe1) as [-> | [o Ho]]; simpl in *; subst.
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
  | FunCall (Val (LitV (LitFunPtr fn))) el => omap (λ vs, Some (fn, vs)) (unmap_val el)
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
  - cbn. destruct a. 2-13:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Local Lemma prim_step_call_dec p e σ e' σ' :
  prim_step p e σ e' σ' →
  (∃ fn vs K, is_call e fn vs K) ∨ (∀ fn vs K, ¬ is_call e fn vs K).
Proof.
  intros [(K' & e1' & e2' & HKe1 & -> & Hstep) |
          (K' & Ki  & v   & HKe1 & ->)]%prim_step_inv; subst;
  try (right; intros fn vs K Hcall%eq_sym; now apply fill_call_raise in Hcall).
  destruct (to_outcome e1') eqn:Hval.
  { exfalso. apply outcome_head_stuck in Hstep. congruence. }

  destruct (to_call_head e1') as [[fn vs]|] eqn:Hcall.
  { assert (∃ fn vs, e1' = of_call fn vs) as (fn' & vs' & ?).
    { unfold to_call_head in Hcall. repeat case_match; simplify_eq.
      eapply unmap_val_map in H3. subst; eauto. } subst.
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
          (K' & Ki  & v   & HKe1 & ->)]%prim_step_inv; subst.
  { inversion Hstep; subst.
    all: try repeat (econstructor; eauto).
    exfalso. eapply Hncall. done. }
  { apply (Prim_step_raise p2 K' Ki _ _ _ _ v); eauto. }
Qed.

End C_lang.

(* Prefer C_lang names over ectx_language names. *)
Export C_lang.
