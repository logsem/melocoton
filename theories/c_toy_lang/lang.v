From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.


Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module C_lang.
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitLoc (l : loc) | LitFunPtr (x : string).
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

Inductive val :=
  | LitV (l : base_lit).

Unset Elimination Schemes.
Inductive expr :=
  (* Values *)
  | Val (v : val)
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

Fixpoint In2 {A} (a : A) (l : list A) : Type := match l with nil => False | b :: m => sum (b = a) (In2 a m) end.

Lemma In2_In {A} (a:A) l : In2 a l -> In a l.
Proof.
  induction l.
  - easy.
  - intros [Hl|Hr]; [now left | right]. apply IHl, Hr.
Qed.

Definition expr_rect (P : expr → Type) :
    (∀ v : val, P (Val v))
  → (∀ x : string, P (Var x))
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
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Let x0 e3 e4 => H3 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H4 e1 (IH e1)
     | Store e2 e3 => H5 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H6 e0 (IH e0)
     | Free e2 e3 => H7 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H8 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H9 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H10 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H11 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H12 e1 (IH e1) ee0 
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
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Let x0 e3 e4 => H3 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H4 e1 (IH e1)
     | Store e2 e3 => H5 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H6 e0 (IH e0)
     | Free e2 e3 => H7 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H8 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H9 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H10 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H11 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H12 e1 (IH e1) ee0 
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
  refine (fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 => _).
  refine (fix IH e {struct e} : P e := _).
  refine (match e as e0 return (P e0) with
     | Val v => H1 v
     | Var x => H2 x
     | Let x0 e3 e4 => H3 x0 e3 (IH e3) e4 (IH e4)
     | Load e1 => H4 e1 (IH e1)
     | Store e2 e3 => H5 e2 (IH e2) e3 (IH e3)
     | Malloc e0 => H6 e0 (IH e0)
     | Free e2 e3 => H7 e2 (IH e2) e3 (IH e3)
     | UnOp op0 e1 => H8 op0 e1 (IH e1)
     | BinOp op0 e3 e4 => H9 op0 e3 (IH e3) e4 (IH e4)
     | If e3 e4 e5 =>  H10 e3 (IH e3) e4 (IH e4) e5 (IH e5)
     | While e2 e3 => H11 e2 (IH e2) e3 (IH e3)
     | FunCall e1 ee0 => H12 e1 (IH e1) ee0 
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

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Inductive function := Fun (b : list binder) (e : expr).

Definition arity (F : function) := match F with Fun b e => length b end.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.


(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  unshelve refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
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

Notation heap_cell := (option (option val)).
Notation Deallocated := (None : heap_cell).
Notation Uninitialized := (Some None : heap_cell).
Notation Storing v := (Some (Some v) : heap_cell).

(** The state: heaps of heap_cells. *)
(*Record state : Type := {
  heap: gmap loc heap_cell
}.*)
Local Notation state := (gmap loc heap_cell).

Class program := prog : gmap string function.


Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitLoc l => (inl (inr l))
  | LitFunPtr p => (inr p)
  end) (λ l, match l with
  | inl (inl n) => LitInt n
  | inl (inr l) => LitLoc l
  | inr p => LitFunPtr p
  end) _); by intros [].
Qed.
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
Global Instance val_countable : Countable val.
Proof. 
  set (enc := fun e => match e with LitV l => l end).
  set (dec := LitV).
  refine (inj_countable' enc dec _).
  by intros [].
Qed.

Global Instance expr_countable : Countable expr.
Proof. (* string + binder + un_op + bin_op + val *)
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [GenLeaf (inr (inr (inr (inr v))))]
     | Var x => GenLeaf (inl x)
     | Let x e1 e2 => GenNode 1 [GenLeaf (inr (inl x)); go e1; go e2]
     | Load e => GenNode 2 [go e]
     | Store e1 e2 => GenNode 3 [go e1; go e2]
     | Malloc e => GenNode 4 [go e]
     | Free e1 e2 => GenNode 5 [go e1; go e2]
     | UnOp op e => GenNode 6 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 7 [GenLeaf (inr (inr (inr (inl op)))); go e1; go e2]
     | If e0 e1 e2 => GenNode 8 [go e0; go e1; go e2]
     | While e1 e2 => GenNode 9 [go e1; go e2]
     | FunCall ef ea => GenNode 10 (go ef :: map go ea)
     end).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [GenLeaf (inr (inr (inr (inr v))))] => Val v
     | GenLeaf (inl x) => Var x
     | GenNode 1 [GenLeaf (inr (inl x)); e1; e2] => Let x (go e1) (go e2)
     | GenNode 2 [e] => Load (go e)
     | GenNode 3 [e1; e2] => Store (go e1) (go e2)
     | GenNode 4 [e] => Malloc (go e)
     | GenNode 5 [e1; e2] => Free (go e1) (go e2)
     | GenNode 6 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 7 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 8 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 9 [e1; e2] => While (go e1) (go e2)
     | GenNode 10 (ef :: ea) => FunCall (go ef) (map go ea)
     | _ => Val $ LitV (LitInt 0) (* dummy *)
     end).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ ).
 destruct e as [ | | | | | | | | | | |ef ee]; simpl; f_equal.
 1-17: done.
 all: unfold map; by induction ee as [|ex er ->]; simpl; f_equal.
Qed.


Global Instance state_inhabited : Inhabited state :=
  populate inhabitant.
Global Instance val_inhabited : Inhabited val := populate (LitV (LitInt 0)).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

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

(** Substitution *)
Fixpoint subst_all (g : gmap string val) (e : expr)  : expr :=
  match e with
  | Val _ => e
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

Definition LitBool (b : bool) : base_lit := LitInt (if b then 1%Z else 0%Z).
Definition LitUnit : base_lit := LitInt 0.

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
  | PtrOffsetOp, LitV (LitLoc (Loc n1)), LitV (LitInt n2) => Some $ LitLoc $ Loc $ (n1 + n2)
  | PtrOffsetOp, LitV (LitInt n1), LitV (LitLoc (Loc n2)) => Some $ LitLoc $ Loc $ (n1 + n2)
  | PtrDiffOp, LitV (LitLoc (Loc n1)), LitV (LitLoc (Loc n2)) => Some $ LitInt $ (n1 - n2)
  | _, _, _ => None
  end%Z.

  Definition vals_compare_safe v1 v2 := match v1, v2 with
    LitInt _, LitInt _ => True
  | LitLoc _, LitLoc _ => True
  | LitFunPtr _, LitFunPtr _ => True
  | _,_ => False end.

Definition state_upd_heap (f: gmap loc heap_cell → gmap loc heap_cell) (σ: state) : state :=
  f σ.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list heap_cell) : gmap loc heap_cell :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some ow.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j  & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc heap_cell) (l : loc) (vs : list _) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : heap_cell) (σ : state) : state :=
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
  | LitV (LitFunPtr p) => true end.

(* Note that this way, a function where all arguments have the same name (say x), that returns x, returns the first argument *)
Fixpoint zip_args (an : list binder) (av : list val) : option (gmap string val) := match an, av with
  nil, nil => Some ∅
| (BNamed ax::ar), (vx::vr) => option_map (<[ax:=vx]>) (zip_args ar vr)
| (BAnon::ar), (vx::vr) => zip_args ar vr
| _, _ => None end.

Definition apply_function (f:function) (av : list val) := match f with Fun an e =>
    match (zip_args an av) with Some σ => Some (subst_all σ e) | _ => None end end.

Inductive head_step (p : program) : expr → state → expr → state → Prop :=
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
     head_step p (While e1 e2) σ (If e1 (Let BAnon e1 (While e1 e2)) (Val $ LitV $ LitInt 0)) σ
  | FunCallS s va args res e σ :
     (p : gmap string function) !! s = Some (Fun args e) →
     apply_function (Fun args e) va = Some res →
     head_step p (FunCall (Val $ LitV $ LitFunPtr s) (map Val va)) σ res σ.


(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck p e1 σ1 e2 σ2 : head_step p e1 σ1 e2 σ2 → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val p Ki e σ1 e2 σ2 :
  head_step p (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
Proof. revert e2. induction Ki. 1-12: inversion_clear 1; simplify_option_eq; eauto.
       - inversion 1. enough (exists k, Val k = e ∧ In k va0) as (k & <- & _) by easy.
         apply in_map_iff. rewrite H1. apply in_or_app. right. now left.
Qed.

Lemma list_eq_sliced {X} (L1 L2 R1 R2 : list X) (M1 M2 : X) (P : X -> Prop) :
  L1 ++ M1 :: R1 = L2 ++ M2 :: R2 ->
  (forall x, In x L1 -> P x) -> (forall x, In x L2 -> P x) -> ~ P M1 -> ~P M2 ->
  L1 = L2 /\ M1 = M2 /\ R1 = R2.
Proof.
  revert L2. induction L1 as [|L1L L1R IH]; intros L2 Heq HL1 HL2 HM1 HM2; destruct L2 as [|L2L L2R].
  - cbn in Heq; repeat split; congruence.
  - cbn in Heq. exfalso. apply HM1. apply HL2. left. congruence.
  - cbn in Heq. exfalso. apply HM2. apply HL1. left. congruence.
  - cbn in Heq. destruct (IH L2R) as (-> & -> & ->).
    + congruence.
    + intros x Hx. apply HL1. now right.
    + intros x Hx. apply HL2. now right.
    + easy.
    + easy.
    + repeat split. congruence.
Qed.

Lemma map_inj {X Y} (f : X -> Y) : (forall x y, f x = f y -> x = y)
  -> forall Lx Ly, map f Lx = map f Ly -> Lx = Ly.
Proof.
  intros Hinj. intros Lx. induction Lx as [|x xr IHx].
  - intros [|y yr]. 1:easy. cbn. congruence.
  - intros [|y yr]. 1:cbn; congruence. cbn. intros Heq. f_equal.
    + apply Hinj. congruence.
    + apply IHx. congruence.
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

End C_lang.

(* Prefer C_lang names over ectx_language names. *)
Export C_lang.










