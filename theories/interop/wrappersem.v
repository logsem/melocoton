From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.c_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.ml_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.ml_toy_lang Require Import lang.
From melocoton.c_toy_lang Require Import lang.
From melocoton.interop Require Import basics wrapperstate.

Section wrappersem.

(* the wrapped C program accepts incoming function calls with ML values as
   arguments, and produces an ML value as output. *)
(* we don't have callbacks yet, so there's no "make an external call"
   expression: the wrapped C program can only be called into, not make "external
   calls" to ML yet. *)
Inductive expr : Type :=
  | WrapExprV (v : val)
  | WrapExprCall (fn_name : string) (args : list val)
  | WrapRunFunction (fn : C_lang.function) (args : list val)
  | WrapExprC (ec : C_lang.expr).

Definition apply_func (fn : C_lang.function) (args : list val) : option expr :=
  Some (WrapRunFunction fn args).

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

(* wrapper evaluation contexts should become more interesting when we add callbacks *)
Definition ectx : Type := unit.
Definition fill : ectx → expr → expr := λ _ e, e.

Inductive state : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     ML or executing the wrapped C program. *)
  | MLState (ρml : wrapstateML) (σ : store)
  | CState (ρc : wrapstateC) (mem : memory).

Definition private_state : Type :=
  (* without callbacks we only need ML-related private state *)
  wrapstateML.

Local Notation public_state := store.

Inductive split_state : state → public_state → private_state → Prop :=
  | WrapSplitSt ρml σ :
    split_state (MLState ρml σ) σ ρml.

Local Notation prog := (gmap string C_lang.function).

Implicit Types X : expr * state → Prop.
Inductive wrapper_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* step in the underlying wrapped C program *)
  | StepCS ec ρc mem ec' mem' X :
    C_lang.head_step p ec mem ec' mem' →
    X (WrapExprC ec', CState ρc mem') →
    wrapper_step_mrel p (WrapExprC ec, CState ρc mem) X
  (* administrative step for resolving a call from ML *)
  | ExprCallS fn_name args fn ρ X :
    p !! fn_name = Some fn →
    X (WrapRunFunction fn args, ρ) →
    wrapper_step_mrel p (WrapExprCall fn_name args, ρ) X
  (* incoming call of a C function from ML *)
  | RunFunctionS fn vs ρml σ X :
    (∀ χ ζ privσ lvs,
       is_store χ ζ privσ σ →
       ML_change_lstore (χML ρml) (ζML ρml) ζ →
       ML_extends_lloc_map (ζML ρml) (χML ρml) χ →
       Forall2 (is_val χ ζ) vs lvs →
       ∃ ws ec mem ρc,
         (∀ γ (a:addr) v,
            (rootsML ρml) !! a = Some v →
            reachable ζ [v] γ →
            γ ∈ dom (θC ρc)) ∧
         Forall2 (repr_lval (θC ρc)) lvs ws ∧
         C_lang.apply_function fn ws = Some ec ∧
         repr (θC ρc) (rootsML ρml) (privmemML ρml) mem ∧
         χC ρc = χ ∧
         ζC ρc = ζ ∧
         rootsC ρc = dom (rootsML ρml) ∧
         privσC ρc = privσ ∧
         X (WrapExprC ec, CState ρc mem)) →
    wrapper_step_mrel p (WrapRunFunction fn vs, MLState ρml σ) X
  (* wrapped C function returning to ML *)
  (* Note: I believe that the "freezing step" does properly forbid freezing a
     mutable block that has already been passed to the outside world --- but
     seeing why is not obvious. I expect it to work through the combination of:
     - sharing a logical block as a mutable value requires registering it in χ
     - χ only always grows monotonically
     - an immutable block cannot be represented as a ML-level heap-allocated value
       (see definition of is_store)
     - thus: trying to freeze a mutable block means that we would have to
       unregister it from χ in order for [is_store ...] to hold. But χ must only
       grow. Qed...
  *)
  | RetS ec w ρc mem X :
    C_lang.to_val ec = Some w →
    (∀ σ lv v ρml,
       freeze_lstore (ζC ρc) (ζML ρml) →
       (χC ρc) ⊆ (χML ρml) →
       is_store (χML ρml) (ζML ρml) (privσC ρc) σ →
       repr_lval (θC ρc) lv w →
       is_val (χML ρml) (ζML ρml) v lv →
       dom (rootsML ρml) = rootsC ρc →
       repr (θC ρc) (rootsML ρml) (privmemML ρml) mem →
       X (WrapExprV v, MLState ρml σ)) →
    wrapper_step_mrel p (WrapExprC ec, CState ρc mem) X
  (* call from C to the "alloc" primitive *)
  | PrimAllocS K ec tgnum tg sz ρc mem X :
    language.to_call ec = Some ("alloc", [LitV (LitInt tgnum); LitV (LitInt sz)]) →
    tgnum = tag_as_int tg →
    (0 < sz)%Z →
    (∀ roots privmem,
       dom roots = rootsC ρc →
       repr (θC ρc) roots privmem mem →
       ∃ γ a mem' ρc',
         γ ∉ dom (ζC ρc) ∧
         ζC ρc' = {[ γ := (Mut, tg, List.repeat (Lint 0) (Z.to_nat sz)) ]} ∪ (ζC ρc) ∧
         repr (θC ρc') roots privmem mem' ∧
         (θC ρc') !! γ = Some a ∧
         (∀ a v γ,
            roots !! a = Some v →
            reachable (ζC ρc) [v] γ →
            γ ∈ dom (θC ρc')) ∧
         χC ρc' = χC ρc ∧
         rootsC ρc' = rootsC ρc ∧
         privσC ρc' = privσC ρc ∧
         X (WrapExprC (language.fill K (C_lang.of_val (C_lang.LitV (C_lang.LitLoc a)))), CState ρc' mem')) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "registerroot" *)
  | PrimRegisterrootS K ec a ρc mem ρc' X :
    language.to_call ec = Some ("registerroot", [LitV (LitLoc a)]) →
    a ∉ rootsC ρc →
    rootsC ρc' = {[ a ]} ∪ rootsC ρc →
    χC ρc' = χC ρc →
    ζC ρc' = ζC ρc →
    θC ρc' = θC ρc →
    privσC ρc' = privσC ρc →
    X (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "unregisterroot" *)
  | PrimUnregisterrootS K ec a ρc mem ρc' X :
    language.to_call ec = Some ("unregisterroot", [LitV (LitLoc a)]) →
    a ∈ rootsC ρc →
    rootsC ρc' = rootsC ρc ∖ {[ a ]} →
    χC ρc' = χC ρc →
    ζC ρc' = ζC ρc →
    θC ρc' = θC ρc →
    privσC ρc' = privσC ρc →
    X (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "modify" *)
  | PrimModifyS K ec w i w' ρc mem γ lv blk blk' ρc' X :
    language.to_call ec = Some ("modify", [w; LitV (LitInt i); w']) →
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some blk →
    repr_lval (θC ρc) lv w' →
    modify_block blk (Z.to_nat i) lv blk' →
    χC ρc' = χC ρc →
    ζC ρc' = <[ γ := blk' ]> (ζC ρc) →
    θC ρc' = θC ρc →
    rootsC ρc' = rootsC ρc →
    privσC ρc' = privσC ρc →
    X (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "readfield" *)
  | PrimReadfieldS K ec w i ρc mem γ mut tag lvs lv w' X :
    language.to_call ec = Some ("readfield", [w; LitV (LitInt i)]) →
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (mut, tag, lvs) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    X (WrapExprC (language.fill K (C_lang.of_val w')), CState ρc mem) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "val2int" *)
  | PrimVal2intS K ec ρc mem w x X :
    language.to_call ec = Some ("val2int", [w]) →
    repr_lval (θC ρc) (Lint x) w →
    X (WrapExprC (language.fill K (C_lang.of_val (LitV (LitInt x)))), (CState ρc mem)) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X
  (* call to "int2val" *)
  | PrimInt2valS K ec ρc mem x w X :
    language.to_call ec = Some ("int2val", [LitV (LitInt x)]) →
    repr_lval (θC ρc) (Lint x) w →
    X (WrapExprC (language.fill K (C_lang.of_val w)), (CState ρc mem)) →
    wrapper_step_mrel p (WrapExprC (language.fill K ec), CState ρc mem) X.

Program Definition wrapper_step (P : prog) : umrel (expr * state) :=
  {| mrel := wrapper_step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepCS
  | eapply ExprCallS
  | eapply RunFunctionS
  | eapply RetS
  | eapply PrimAllocS
  | eapply PrimRegisterrootS
  | eapply PrimUnregisterrootS
  | eapply PrimModifyS
  | eapply PrimReadfieldS
  | eapply PrimVal2intS
  | eapply PrimInt2valS
  ]; naive_solver.
Qed.

Lemma wrap_mlanguage_mixin :
  MlanguageMixin (val:=ML_lang.val) of_class to_class tt (λ _ _, tt) fill
    split_state apply_func wrapper_step.
Proof using.
  constructor.
  - intros c. destruct c; reflexivity.
  - intros e c. destruct e; cbn. all: inversion 1; cbn; auto.
  - intros p v st X. cbn. inversion 1; subst; naive_solver.
  - intros p fname v st X. split.
    + cbn. inversion 1; subst; naive_solver.
    + intros (fn & e & ? & Hfn & ?). cbn. unfold apply_func in Hfn.
      simplify_eq. econstructor; eauto.
  - intros ? [] ? ? ?. rewrite /fill /=. eauto.
  - eauto.
  - eauto.
  - intros [] ? ?. by unfold fill.
  - intros [] ? ?. eauto.
  - intros ? ?. eexists (MLState _ _). constructor.
  - intros p [] [] ? ? ? ?. naive_solver.
  - intros ? []. naive_solver.
Qed.

Canonical Structure wrap_lang : mlanguage val public_state :=
  Mlanguage wrap_mlanguage_mixin.

End wrappersem.
