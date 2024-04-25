From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export multirelations language_commons.

Section mlanguage_mixin.
  Context {expr val func state ectx : Type}.

  Context (of_outcome : outcome val → expr).
  Context (to_outcome : expr → option (outcome val)).

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
    (** Expression and outcomes *)
    mixin_to_of_outcome o : to_outcome (of_outcome o) = Some o;
    mixin_of_to_outcome e o : to_outcome e = Some o → of_outcome o = e;

    (** Reduction behavior of the special classes of expressions *)
    (** mixin_outcome_prim_step is not an iff because the backward direction is trivial *)
    mixin_outcome_prim_step p v σ :
      prim_step p (of_outcome v, σ) (λ _, False);
    mixin_call_prim_step p e f vs K σ X :
      is_call e f vs K →
        prim_step p (e, σ) X ↔
        (∃ (fn : func) (e2 : expr),
          p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ X (fill K e2, σ));

    mixin_is_outcome_not_call e : is_Some (to_outcome e) → (∀ f vs K, ¬ is_call e f vs K);
    mixin_is_call_in_ctx e K1 K2 s vv :
      is_call e s vv K2 → is_call (fill K1 e) s vv (comp_ectx K1 K2);
    mixin_to_call_is_call fn vs : is_call (to_call fn vs) fn vs empty_ectx;
    mixin_is_call_to_call e fn vs K : is_call e fn vs K → e = fill K (to_call fn vs);
    mixin_is_call_to_call_inv fn vs fn' vs' K :
      is_call (to_call fn vs) fn' vs' K →
      fn' = fn ∧ vs' = vs ∧ K = empty_ectx;

    mixin_resume_outcome e K :
      is_Some (to_outcome (fill K e)) →
      to_outcome (fill K e) = to_outcome e;
    mixin_resume_compose e K1 K2 :
      fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_resume_empty e :
      fill empty_ectx e = e;

    mixin_prim_step_resume p K e σ X :
      to_outcome e = None →
      prim_step p (e, σ) X →
      prim_step p (fill K e, σ) (λ '(e2, σ2),
        ∃ e', e2 = fill K e' ∧ X (e', σ2));

    (* Just a meta-theorem to ensure that there are no cases left to cover.
       Not used in proofs. *)
    mixin_prim_step_no_NB p e σ X :
      to_outcome e = None →
      prim_step p (e, σ) X →
      ∃ e' σ', X (e', σ');
  }.
End mlanguage_mixin.

Global Notation mixin_prog func := (gmap string func).

Structure mlanguage {val : Type} := Mlanguage {
  expr : Type;
  func : Type;
  state : Type;
  ectx : Type;

  of_outcome : outcome val → expr;
  to_outcome : expr → option (outcome val);

  to_call : string → list val → expr;
  is_call : expr → string → list val → ectx → Prop;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;

  apply_func : func → list val → option expr;
  prim_step : (gmap string func) → umrel (expr * state);


  mlanguage_mixin :
    MlanguageMixin (val:=val) of_outcome to_outcome to_call is_call empty_ectx
      comp_ectx fill apply_func prim_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments mlanguage : clear implicits.
Arguments Mlanguage {_ expr _ _ _ _ _ _ _ _ _ fill apply_func prim_step}.
Arguments of_outcome {_} _ _.
Arguments to_outcome {_ _} _.
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

  Lemma to_of_outcome o : to_outcome (of_outcome Λ o) = Some o.
  Proof. apply mlanguage_mixin. Qed.
  Lemma of_to_outcome e o : to_outcome e = Some o → of_outcome Λ o = e.
  Proof. apply mlanguage_mixin. Qed.

  Definition of_val Λ v := of_outcome Λ (OVal v).
  Definition to_val e : option val :=
    match to_outcome e with
    | Some (OVal v) => Some v
    | _ => None
    end.

  Lemma of_outcome_of_val v : of_outcome Λ (OVal v) = of_val Λ v.
  Proof. easy. Qed.
  Lemma to_outcome_of_val v : to_outcome (of_val Λ v) = Some (OVal v).
  Proof. rewrite /of_val to_of_outcome //. Qed.

  Lemma to_of_val v : to_val (of_val Λ v) = Some v.
  Proof. rewrite /to_val to_of_outcome //. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val Λ v = e.
  Proof.
    unfold to_val, of_val.
    destruct (to_outcome e) eqn:Heq; try destruct o; try congruence.
    inversion 1; subst. now apply of_to_outcome in Heq. 
  Qed.

  Lemma of_outcome_inj k1 k2 : of_outcome Λ k1 = of_outcome Λ k2 → k1 = k2.
  Proof.
    intros H. enough (Some k1 = Some k2) by congruence.
    rewrite <- !to_of_outcome. rewrite H. done.
  Qed.

  Lemma of_val_inj k1 k2 : of_val Λ k1 = of_val Λ k2 → k1 = k2.
  Proof.
    intros H. enough (Some k1 = Some k2) by congruence.
    rewrite <- !to_of_val. rewrite H. done.
  Qed.

  Lemma outcome_prim_step p o σ :
    prim_step p (of_outcome Λ o, σ) (λ _, False).
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_prim_step p e f vs K σ X :
      is_call e f vs K →
        prim_step p (e, σ) X ↔
        (∃ (fn : func Λ) e2,
          p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ X (fill K e2, σ)).
  Proof. apply mlanguage_mixin. Qed.

  Definition not_is_call e : Prop := ¬ ∃ f vs K, is_call e f vs K.
  Definition not_is_ext_call (p : prog Λ) e : Prop := ¬ ∃ f vs K, is_call e f vs K ∧ p !! f = None.

  Lemma is_outcome_not_call e : is_Some (to_outcome e) → (∀ f vs K, ¬ is_call e f vs K).
  Proof. apply mlanguage_mixin. Qed.

  Lemma is_outcome_not_call_2 e f vs K : is_call e f vs K → to_outcome e = None.
  Proof.
    intros H; destruct (to_outcome e) eqn:Heq; try done.
    exfalso; apply mk_is_Some in Heq.
    eapply is_outcome_not_call in Heq. done.
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

  Lemma resume_outcome e K :
    is_Some (to_outcome (fill K e)) → to_outcome (fill K e) = to_outcome e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma resume_outcome_2 e K : is_Some (to_outcome (fill K e)) → is_Some (to_outcome e).
  Proof.
    intros H. assert (is_Some (to_outcome (fill K e))) as [x Heq] by done.
    apply resume_outcome in H. rewrite Heq in H; done.
  Qed.

  Lemma resume_not_outcome e K : to_outcome e = None → to_outcome (fill K e) = None.
  Proof.
    intros Heq; destruct (to_outcome (fill K e)) as [v|] eqn:Heq2; last done.
    eapply mk_is_Some in Heq2. apply resume_outcome_2 in Heq2; rewrite Heq in Heq2.
    by destruct Heq2.
  Qed.

  Lemma resume_compose e K1 K2 :
    fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply mlanguage_mixin. Qed.
  Lemma resume_empty e :
      fill empty_ectx e = e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma prim_step_resume p K e σ X :
    to_outcome e = None →
    prim_step p (e, σ) X →
    prim_step p (fill K e, σ) (λ '(e2, σ2), ∃ e', e2 = fill K e' ∧ X (e', σ2)).
  Proof. apply mlanguage_mixin. Qed.

  (* There is no NB *)
  Lemma prim_step_no_NB p e σ X : to_outcome e = None → prim_step p (e,σ) X → ∃ e' σ', X (e', σ').
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
  Definition safe p (e : expr Λ) (σ : state Λ) (Φ : outcome val → Prop) := match to_outcome e with
    Some o => Φ o
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
