From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export multirelations language_commons.

Section mlanguage_mixin.
  Context {expr val func state ectx : Type}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (to_call : string → list val → expr).
  Context (is_call : expr → string → list val → ectx → Prop).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).

  (** A program is a map from function names to function bodies. *)
  Local Notation mixin_prog := (gmap string func).

  Context (apply_func : func → list val → option expr).
  Context (prim_step : mixin_prog → umrel (expr * state)).

  Record MlanguageMixin := {
    (** Expression and values *)
    mixin_to_of_val c : to_val (of_val c) = Some c;
    mixin_of_to_val e c : to_val e = Some c → of_val c = e;

    (** Reduction behavior of the special classes of expressions *)
    (** mixin_val_prim_step is not an iff because the backward direction is trivial *)
    mixin_val_prim_step p v σ :
      prim_step p (of_val v, σ) (λ _, False);
    mixin_call_prim_step p e f vs K σ X :
      is_call e f vs K →
        prim_step p (e, σ) X ↔
        (∃ (fn : func) (e2 : expr),
          p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ X (fill K e2, σ));

    mixin_is_val_not_call e : is_Some (to_val e) → (∀ f vs K, ¬ is_call e f vs K);
    mixin_is_call_in_ctx e K1 K2 s vv :
      is_call e s vv K2 → is_call (fill K1 e) s vv (comp_ectx K1 K2);
    mixin_to_call_is_call fn vs : is_call (to_call fn vs) fn vs empty_ectx;
    mixin_is_call_to_call e fn vs K : is_call e fn vs K → e = fill K (to_call fn vs);
    mixin_is_call_to_call_inv fn vs fn' vs' K :
      is_call (to_call fn vs) fn' vs' K →
      fn' = fn ∧ vs' = vs ∧ K = empty_ectx;

    mixin_resume_val e K : is_Some (to_val (fill K e)) → is_Some (to_val e);
    mixin_resume_compose e K1 K2 :
      fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_resume_empty e :
      fill empty_ectx e = e;

    mixin_prim_step_resume p K e σ X :
      to_val e = None →
      prim_step p (e, σ) X →
      prim_step p (fill K e, σ) (λ '(e2, σ2),
        ∃ e', e2 = fill K e' ∧ X (e', σ2));

    (* Just a meta-theorem to ensure that there are no cases left to cover.
       Not used in proofs. *)
    mixin_prim_step_no_NB p e σ X :
      to_val e = None →
      prim_step p (e, σ) X →
      ∃ e' σ', X (e', σ');
  }.
End mlanguage_mixin.

Arguments mixin_expr_class : clear implicits.
Global Notation mixin_prog func := (gmap string func).

Structure mlanguage {val : Type} := Mlanguage {
  expr : Type;
  func : Type;
  state : Type;
  ectx : Type;

  of_val : val → expr;
  to_val : expr → option val;

  to_call : string → list val → expr;
  is_call : expr → string → list val → ectx → Prop;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;

  apply_func : func → list val → option expr;
  prim_step : (gmap string func) → umrel (expr * state);


  mlanguage_mixin :
    MlanguageMixin (val:=val) of_val to_val to_call is_call empty_ectx
      comp_ectx fill apply_func prim_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments mlanguage : clear implicits.
Arguments Mlanguage {_ expr _ _ _ _ _ _ _ _ _ fill apply_func prim_step}.
Arguments of_val {_} _ _.
Arguments to_val {_ _} _.
Arguments to_call {_} _ _.
Arguments is_call {_ _}.
Arguments empty_ectx {_ _}.
Arguments comp_ectx {_ _}.
Arguments fill {_ _}.
Arguments apply_func {_ _}.
Arguments prim_step {_ _}.
Notation prog Λ := (mixin_prog Λ.(func)).
(* From an ectx_language, we can construct a mlanguage. *)
Section mlanguage.
  Context {val : Type}.
  Context {public_state : Type}.
  Context {Λ : mlanguage val}.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.
  Implicit Types X : expr Λ * state Λ → Prop.

  Lemma to_of_val c : to_val (of_val Λ c) = Some c.
  Proof. apply mlanguage_mixin. Qed.
  Lemma of_to_val e c : to_val e = Some c → of_val Λ c = e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma of_val_inj k1 k2 : of_val Λ k1 = of_val Λ k2 → k1 = k2.
  Proof.
    intros H. enough (Some k1 = Some k2) by congruence.
    rewrite <- !to_of_val. rewrite H. done.
  Qed.
  Lemma val_prim_step p v σ :
    prim_step p (of_val Λ v, σ) (λ _, False).
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_prim_step p e f vs K σ X :
      is_call e f vs K →
        prim_step p (e, σ) X ↔
        (∃ (fn : func Λ) e2,
          p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ X (fill K e2, σ)).
  Proof. apply mlanguage_mixin. Qed.

  Definition not_is_call e : Prop := ¬ ∃ f vs K, is_call e f vs K.
  Definition not_is_ext_call (p : prog Λ) e : Prop := ¬ ∃ f vs K, is_call e f vs K ∧ p !! f = None.

  Lemma is_val_not_call e : is_Some (to_val e) → (∀ f vs K, ¬ is_call e f vs K).
  Proof. apply mlanguage_mixin. Qed.

  Lemma is_val_not_call_2 e f vs K : is_call e f vs K → to_val e = None.
  Proof.
    intros H; destruct (to_val e) eqn:Heq; try done.
    exfalso; apply mk_is_Some in Heq.
    eapply is_val_not_call in Heq. done.
  Qed.

  Lemma is_call_in_ctx e K1 K2 s vv :
      is_call e s vv K2 → is_call (fill K1 e) s vv (comp_ectx K1 K2).
  Proof. apply mlanguage_mixin. Qed.

  Lemma to_call_is_call fn vs : is_call (to_call Λ fn vs) fn vs empty_ectx.
  Proof. apply mlanguage_mixin. Qed.
  Lemma is_call_to_call e fn vs K : is_call e fn vs K → e = fill K (to_call Λ fn vs).
  Proof. apply mlanguage_mixin. Qed.
  Lemma is_call_to_call_inv fn vs fn' vs' K :
    is_call (to_call Λ fn vs) fn' vs' K →
    fn' = fn ∧ vs' = vs ∧ K = empty_ectx.
  Proof. apply mlanguage_mixin. Qed.

  Lemma resume_val e K : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply mlanguage_mixin. Qed.

  Lemma resume_not_val e K : to_val e = None → to_val (fill K e) = None.
  Proof.
    intros Heq; destruct (to_val (fill K e)) as [v|] eqn:Heq2; last done.
    eapply mk_is_Some in Heq2. apply resume_val in Heq2. rewrite Heq in Heq2.
    by destruct Heq2.
  Qed.

  Lemma resume_compose e K1 K2 :
    fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply mlanguage_mixin. Qed.
  Lemma resume_empty e :
      fill empty_ectx e = e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma prim_step_resume p K e σ X :
    to_val e = None →
    prim_step p (e, σ) X →
    prim_step p (fill K e, σ) (λ '(e2, σ2), ∃ e', e2 = fill K e' ∧ X (e', σ2)).
  Proof. apply mlanguage_mixin. Qed.

  (* There is no NB *)
  Lemma prim_step_no_NB p e σ X : to_val e = None → prim_step p (e,σ) X → ∃ e' σ', X (e', σ').
  Proof. apply mlanguage_mixin. Qed.

  Class IntoVal (e : expr Λ) (v : val) :=
    into_val : of_val Λ v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val Λ v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val Λ <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  (* Non-values must step to a set. By prim_step_no_NB, this set is not empty. *)
  Definition safe p (e : expr Λ) (σ : state Λ) (Φ : val → Prop) := match to_val e with
    Some v => Φ v
  | None => ∃ X, prim_step p (e,σ) X end.

End mlanguage.

(* discrete OFE instance for expr *)
Definition exprO `{SI: indexT} {val} {Λ : mlanguage val} := leibnizO (expr Λ).
Global Instance expr_equiv `{SI: indexT} {val} {Λ : mlanguage val} : Equiv (expr Λ). apply exprO. Defined.

Notation mlang_prog Λ := (gmap string Λ.(func)).

Class linkable {val} (Λ : mlanguage val) (public_state : Type) := Linkable {
  private_state : Type;
  split_state : Λ.(state) → public_state → private_state → Prop
}.
