From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.c_toy_lang Require Import lang_instantiation.
From melocoton.language Require Import language.
From melocoton.c_toy_lang Require Import lang.
From melocoton.interop Require Import assums basics wrapperstate.

Inductive ml_or_c (A B: Type) : Type :=
  | ML : A → ml_or_c A B
  | C : B → ml_or_c A B.

Arguments ML {A B}.
Arguments C {A B}.

Section wrappersem.

Inductive wrapper_func_kind : Type :=
  FuncInternal | FuncExternal.

Definition func : Type :=
  wrapper_func_kind * C_lang.function.

(* the wrapped C program accepts incoming function calls with ML values as
   arguments, and produces an ML value as output. *)
(* we don't have callbacks yet, so there's no "make an external call"
   expression: the wrapped C program can only be called into, not make "external
   calls" to ML yet. *)
Inductive expr : Type :=
  | WrapExprV (v : val)
  | WrapExprCall (fn_name : string) (args : list val)
  | WrapRunExternalFunction (fn : C_lang.function) (args : list val)
  | WrapExprC (ec : C_lang.expr).

Definition apply_func (fn : func) (args : list val) : option expr :=
  let '(fnkind, fn) := fn in
  match fnkind with
  | FuncInternal => None
  | FuncExternal => Some (WrapRunExternalFunction fn args)
  end.

Definition of_class (c : mixin_expr_class val) : expr :=
  match c with
  | ExprVal v => WrapExprV v
  | ExprCall fn_name args => WrapExprCall fn_name args
  end.

Definition to_class (e : expr) : option (mixin_expr_class val) :=
  match e with
  | WrapExprV v => Some (ExprVal v)
  | WrapExprCall fn_name args => Some (ExprCall fn_name args)
  | _ => None
  end.

(* wrapper evaluation contexts should become nontrivial when we add callbacks *)
Definition ectx : Type := unit.
Definition fill : ectx → expr → expr := λ _ e, e.

Definition state : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     ML or executing the wrapped C program. *)
  ml_or_c
    (wrapstateML * store)
    (wrapstateC * memory).

Definition private_state : Type :=
  (* without callbacks we only need ML-related private state *)
  wrapstateML.

Local Notation prog := (gmap string func).

Definition proj_prog_C (P : prog) : gmap string C_lang.function :=
  fmap (λ '(_, fn), fn) P.

Definition wrapper_step_mrel (P : prog) : multirelation (expr * state) :=
  λ '(e, ρ) φ,
    (* step in the underlying wrapped C program *)
    (∀ ec ρc mem ec' mem',
       e = WrapExprC ec →
       ρ = C (ρc, mem) →
       C_lang.head_step (proj_prog_C P) ec mem ec' mem' →
       φ (WrapExprC ec', C (ρc, mem')))
    ∨
    (* administrative step for resolving a call from ML *)
    (∀ fn_name args fn,
       e = WrapExprCall fn_name args →
       P !! fn_name = Some (FuncExternal, fn) →
       φ (WrapRunExternalFunction fn args, ρ))
    ∨
    (* incoming call of a C function from ML *)
    (∀ fn vs ρml σ,
       e = WrapRunExternalFunction fn vs →
       ρ = ML (ρml, σ) →
       ∃ χ ζ privσ lvs,
         is_store χ ζ privσ σ ∧
         ML_change_lstore (χML ρml) (ζML ρml) ζ ∧
         ML_extends_lloc_map (ζML ρml) (χML ρml) χ ∧
         Forall2 (is_val χ ζ) vs lvs ∧
         ∀ ws ec mem ρc,
           (∀ γ (a:addr) v,
              (rootsML ρml) !! a = Some v →
              reachable ζ [v] γ →
              γ ∈ dom (θC ρc)) →
           Forall2 (repr_lval (θC ρc)) lvs ws →
           C_lang.apply_function fn ws = Some ec →
           repr (θC ρc) (rootsML ρml) (privmemML ρml) mem →
           χC ρc = χ →
           ζC ρc = ζ →
           rootsC ρc = dom (rootsML ρml) →
           privσC ρc = privσ →
           φ (WrapExprC ec, C (ρc, mem)))
    ∨
    (* wrapped C function returning to ML *)
    (∀ ec w ρc mem,
       e = WrapExprC ec →
       C_lang.to_val ec = Some w →
       ρ = C (ρc, mem) →
       ∃ σ lv v ρml,
         freeze_lstore (ζC ρc) (ζML ρml) ∧
         (χC ρc) ⊆ (χML ρml) ∧
         is_store (χML ρml) (ζML ρml) (privσC ρc) σ ∧
         repr_lval (θC ρc) lv w ∧
         is_val (χML ρml) (ζML ρml) v lv ∧
         dom (rootsML ρml) = rootsC ρc ∧
         repr (θC ρc) (rootsML ρml) (privmemML ρml) mem ∧
         φ (WrapExprV v, ML (ρml, σ)))
    ∨
    (* call from C to the "alloc" primitive *)
    (∀ K ec tgnum tg sz ρc mem,
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("alloc", [LitV (LitInt tgnum); LitV (LitInt sz)]) →
       ρ = C (ρc, mem) →
       tgnum = tag_as_int tg →
       (0 < sz)%Z →
       ∃ roots privmem,
         dom roots = rootsC ρc ∧
         repr (θC ρc) roots privmem mem ∧
         ∀ γ a mem' ρc',
           γ ∉ dom (ζC ρc) →
           ζC ρc' = {[ γ := (Mut, tg, List.repeat (Lint 0) (Z.to_nat sz)) ]} ∪ (ζC ρc) →
           repr (θC ρc') roots privmem mem' →
           (θC ρc') !! γ = Some a →
           (∀ a v γ,
              roots !! a = Some v →
              reachable (ζC ρc) [v] γ →
              γ ∈ dom (θC ρc')) →
           χC ρc' = χC ρc →
           rootsC ρc' = rootsC ρc →
           privσC ρc' = privσC ρc →
           φ (WrapExprC (language.fill K (C_lang.of_val (LitV (LitLoc a)))), C (ρc', mem')))
    ∨
    (* call to "registerroot" *)
    (∀ K ec a ρc mem,
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("registerroot", [LitV (LitLoc a)]) →
       ρ = C (ρc, mem) →
       a ∉ rootsC ρc →
       ∀ ρc',
         rootsC ρc' = {[ a ]} ∪ rootsC ρc →
         χC ρc' = χC ρc →
         ζC ρc' = ζC ρc →
         θC ρc' = θC ρc →
         privσC ρc' = privσC ρc →
         φ (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), C (ρc', mem)))
    ∨
    (* call to "unregisterroot" *)
    (∀ K ec a ρc mem,
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("unregisterroot", [LitV (LitLoc a)]) →
       ρ = C (ρc, mem) →
       a ∈ rootsC ρc →
       ∀ ρc',
         rootsC ρc' = rootsC ρc ∖ {[ a ]} →
         χC ρc' = χC ρc →
         ζC ρc' = ζC ρc →
         θC ρc' = θC ρc →
         privσC ρc' = privσC ρc →
         φ (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), C (ρc', mem)))
    ∨
    (* call to "modify" *)
    (∀ K ec w i w' ρc mem γ lv blk blk',
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("modify", [w; LitV (LitInt i); w']) →
       ρ = C (ρc, mem) →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some blk →
       repr_lval (θC ρc) lv w' →
       modify_block blk (Z.to_nat i) lv blk' →
       ∀ ρc',
         χC ρc' = χC ρc →
         ζC ρc' = <[ γ := blk' ]> (ζC ρc) →
         θC ρc' = θC ρc →
         rootsC ρc' = rootsC ρc →
         privσC ρc' = privσC ρc →
         φ (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), C (ρc', mem)))
    ∨
    (* call to "readfield" *)
    (∀ K ec w i ρc mem γ mut tag lvs lv w',
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("readfield", [w; LitV (LitInt i)]) →
       ρ = C (ρc, mem) →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (mut, tag, lvs) →
       lvs !! (Z.to_nat i) = Some lv →
       repr_lval (θC ρc) lv w' →
       φ (WrapExprC (language.fill K (C_lang.of_val w')), C (ρc, mem)))
    ∨
    (* call to "val2int" *)
    (∀ K ec ρc mem w x,
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("val2int", [w]) →
       ρ = C (ρc, mem) →
       repr_lval (θC ρc) (Lint x) w →
       φ (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt x)))), (C (ρc, mem))))
    ∨
    (* call to "int2val" *)
    (∀ K ec ρc mem x w,
       e = WrapExprC (language.fill K ec) →
       to_call ec = Some ("int2val", [LitV (LitInt x)]) →
       ρ = C (ρc, mem) →
       repr_lval (θC ρc) (Lint x) w →
       φ (WrapExprC (language.fill K (C_lang.of_val w)), (C (ρc, mem)))).

Program Definition wrapper_step (P : prog) : umrel (expr * state) :=
  {| mrel := wrapper_step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] φ ψ H Hφψ.
  destruct_or! H; naive_solver.
Qed.

End wrappersem.
