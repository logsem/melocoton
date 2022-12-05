From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.c_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.ml_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.ml_toy_lang Require Import lang.
From melocoton.c_toy_lang Require Import lang.
From melocoton.interop Require Import basics linking wrapperstate.

Module Wrap.
Section wrappersem.

(* the wrapped C program accepts incoming function calls with ML values as
   arguments, and produces an ML value as output. *)
(* we don't have callbacks yet, so there's no "make an external call"
   expression: the wrapped C program can only be called into, not make "external
   calls" to ML yet. *)
Inductive expr : Type :=
  | ExprV (v : val)
  | ExprCall (fn_name : string) (args : list val)
  | RunFunction (fn : C_lang.function) (args : list val)
  | ExprC (ec : C_lang.expr).

Definition apply_func (fn : C_lang.function) (args : list val) : option expr :=
  Some (RunFunction fn args).

Definition of_class (c : mixin_expr_class val) : expr :=
  match c with
  | ExprVal v => ExprV v
  | commons.ExprCall fn_name args => ExprCall fn_name args
  end.

Definition to_class (e : expr) : option (mixin_expr_class val) :=
  match e with
  | ExprV v => Some (ExprVal v)
  | ExprCall fn_name args => Some (commons.ExprCall fn_name args)
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
Inductive step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Step in the underlying wrapped C program. *)
  | StepCS ec ρc mem ec' mem' X :
    C_lang.head_step p ec mem ec' mem' →
    X (ExprC ec', CState ρc mem') →
    step_mrel p (ExprC ec, CState ρc mem) X
  (* Administrative step for resolving a call from ML. *)
  | ExprCallS fn_name args fn ρ X :
    p !! fn_name = Some fn →
    X (RunFunction fn args, ρ) →
    step_mrel p (ExprCall fn_name args, ρ) X
  (* Incoming call of a C function from ML. *)
  | RunFunctionS fn vs ρml σ ζ lvs ws ec mem ρc X :
    (* Demonically get a new extended map (χC ρc) (new γs must be fresh). *)
    lloc_map_mono (ζML ρml) (χML ρml) (χC ρc) →
    (* The extended (χC ρc) binds γs for all locations ℓ in σ; these γs make up
       the domain of a map ζ (whose contents are also chosen demonically). In
       other words, here ζ has exactly one block for each location in σ. *)
    is_store_blocks (χC ρc) σ ζ →
    (* We take the new lstore (ζC ρc) to be the old lstore + ζ (the translation
       of σ into a lstore). (ζML ρml) will typically contain immutable blocks or
       mutable blocks allocated in C but not yet shared with the ML code. *)
    ζC ρc = ζML ρml ∪ ζ →
    (* Taken together, the contents of the new lloc_map (χC ρc) and new lstore
       (ζC ρc) must corresponds to the contents of σ. (This further constraints
       the demonic choice of ζ.) *)
    is_store (χC ρc) (ζC ρc) σ →
    (* Demonically pick block-level values lvs that represent the arguments vs. *)
    Forall2 (is_val χ (ζC ρc)) vs lvs →
    (* Demonically pick a addr_map (θC ρc) satisfying the GC_correct property. *)
    GC_correct (ζC ρc) (θC ρc) →
    (* Rooted values must additionally be live in (θC ρc). *)
    roots_are_live (θC ρc) (rootsML ρml) →
    (* Pick C-level words that are live and represent the arguments of the
       function. (repr_lval on a location entails that it is live.) *)
    Forall2 (repr_lval (θC ρc)) lvs ws →
    (* Pick C memory (mem) that represents the roots (through θC ρc) + the
       remaining private C memory. *)
    repr (θC ρc) (rootsML ρml) (privmemML ρml) mem →
    (* Apply the C function; the result is a C expression ec. *)
    C_lang.apply_function fn ws = Some ec →
    rootsC ρc = dom (rootsML ρml) →
    X (ExprC ec, CState ρc mem) →
    step_mrel p (RunFunction fn vs, MLState ρml σ) X
  (* Wrapped C function returning to ML. *)
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
    (∀ σ lv v ζ ζσ ρml,
       (* Angelically allow freezing some blocks in (ζC ρc); the result is ζ.
          This allows allocating a fresh block, mutating it, then changing it
          into an immutable block that represents an immutable ML value. *)
       freeze_lstore (ζC ρc) ζ →
       (* Angelically extend (χC ρc) into (χML ρml). This makes it possible to
          expose newly created blocks to locations in the ML store. *)
       lloc_map_mono ζ (χC ρc) (χML ρml) →
       (* Split the "current" lstore ζ into (ζML ρml) (the new lstore) and a
          part ζσ that is going to be converted into the ML store σ. *)
       ζ = ζML ρml ∪ ζσ →
       (* Angelically pick an ML store σ where each location corresponds to a
          block in ζσ. *)
       is_store_blocks (χML ρml) σ ζσ →
       (* The contents of the new σ must correspond to the contents of ζ. *)
       is_store (χML ρml) ζ σ →
       (* Angelically pick a block-level return value lv that corresponds to the
          C value w. *)
       repr_lval (θC ρc) lv w →
       (* Angelically pick a ML return value v that corresponds to the
          block-level value lv. *)
       is_val (χML ρml) ζ v lv →
       (* Split the C memory mem into the memory for the roots and the rest
          ("private" C memory). *)
       repr (θC ρc) (rootsML ρml) (privmemML ρml) mem →
       dom (rootsML ρml) = rootsC ρc →
       X (ExprV v, MLState ρml σ)) →
    step_mrel p (ExprC ec, CState ρc mem) X
  (* call from C to the "alloc" primitive *)
  | PrimAllocS K ec tgnum tg sz roots ρc privmem mem γ a mem' ρc' X :
    language.to_call ec = Some ("alloc", [LitV (LitInt tgnum); LitV (LitInt sz)]) →
    tgnum = tag_as_int tg →
    (0 ≤ sz)%Z →
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    γ ∉ dom (ζC ρc) →
    ζC ρc' = {[ γ := (Mut, tg, List.repeat (Lint 0) (Z.to_nat sz)) ]} ∪ (ζC ρc) →
    repr (θC ρc') roots privmem mem' →
    GC_correct (ζC ρc') (θC ρc') →
    (θC ρc') !! γ = Some a →
    roots_are_live (θC ρc') roots →
    χC ρc' = χC ρc →
    rootsC ρc' = rootsC ρc →
    X (ExprC (language.fill K (C_lang.of_val (C_lang.LitV (C_lang.LitLoc a)))), CState ρc' mem') →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
  (* call to "registerroot" *)
  | PrimRegisterrootS K ec a ρc mem ρc' X :
    language.to_call ec = Some ("registerroot", [LitV (LitLoc a)]) →
    a ∉ rootsC ρc →
    rootsC ρc' = {[ a ]} ∪ rootsC ρc →
    χC ρc' = χC ρc →
    ζC ρc' = ζC ρc →
    θC ρc' = θC ρc →
    X (ExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
  (* call to "unregisterroot" *)
  | PrimUnregisterrootS K ec a ρc mem ρc' X :
    language.to_call ec = Some ("unregisterroot", [LitV (LitLoc a)]) →
    a ∈ rootsC ρc →
    rootsC ρc' = rootsC ρc ∖ {[ a ]} →
    χC ρc' = χC ρc →
    ζC ρc' = ζC ρc →
    θC ρc' = θC ρc →
    X (ExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
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
    X (ExprC (language.fill K (C_lang.of_val (LitV (LitInt 0)))), CState ρc' mem) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
  (* call to "readfield" *)
  | PrimReadfieldS K ec w i ρc mem γ mut tag lvs lv w' X :
    language.to_call ec = Some ("readfield", [w; LitV (LitInt i)]) →
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (mut, tag, lvs) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    X (ExprC (language.fill K (C_lang.of_val w')), CState ρc mem) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
  (* call to "val2int" *)
  | PrimVal2intS K ec ρc mem w x X :
    language.to_call ec = Some ("val2int", [w]) →
    repr_lval (θC ρc) (Lint x) w →
    X (ExprC (language.fill K (C_lang.of_val (LitV (LitInt x)))), (CState ρc mem)) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X
  (* call to "int2val" *)
  | PrimInt2valS K ec ρc mem x w X :
    language.to_call ec = Some ("int2val", [LitV (LitInt x)]) →
    repr_lval (θC ρc) (Lint x) w →
    X (ExprC (language.fill K (C_lang.of_val w)), (CState ρc mem)) →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X.

Program Definition step (P : prog) : umrel (expr * state) :=
  {| mrel := step_mrel P |}.
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

Lemma mlanguage_mixin :
  MlanguageMixin (val:=ML_lang.val) of_class to_class tt (λ _ _, tt) fill
    apply_func step.
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
  - intros p [] [] ? ? ? ?. naive_solver.
  - intros ? []. naive_solver.
Qed.

End wrappersem.
End Wrap.

Canonical Structure wrap_lang : mlanguage val :=
  Mlanguage Wrap.mlanguage_mixin.

Global Program Instance wrap_linkable : linkable wrap_lang store := {
  private_state := Wrap.private_state;
  split_state := Wrap.split_state;
}.
Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.
