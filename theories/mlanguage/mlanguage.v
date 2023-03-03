From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export multirelations commons.

Section mlanguage_mixin.
  Context {expr val func state cont : Type}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (is_call : expr → string → list val → cont → Prop).
  Context (resume_with : cont → expr → expr).
  Context (compose_cont : cont → cont → cont).

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
    mixin_val_prim_step p v σ X :
      prim_step p (of_val v, σ) X → False;
    mixin_call_prim_step p e f vs C σ X :
      is_call e f vs C →
        prim_step p (e, σ) X ↔
        (∀ (fn : func) (e2 : expr),
          p !! f = Some fn → Some e2 = apply_func fn vs → X (resume_with C e2, σ));

    mixin_not_is_call e : is_Some (to_val e) → (∀ f vs C, ¬ is_call e f vs C);
    mixin_is_call_in_cont e C1 C2 s vv :
      is_call e s vv C2 → is_call (resume_with C1 e) s vv (compose_cont C1 C2);
    mixin_is_call_in_cont_inv e C1 C2 s vv :
      to_val e = None → is_call (resume_with C1 e) s vv C2 →
      ∃ C', is_call e s vv C' ∧ C2 = compose_cont C1 C';

    mixin_resume_val e C : is_Some (to_val (resume_with C e)) → is_Some (to_val e);
    mixin_resume_compose e C1 C2 :
      resume_with C1 (resume_with C2 e) = resume_with (compose_cont C1 C2) e;

    mixin_is_call_unique e s1 s2 f1 f2 C1 C2 :
      is_call e s1 f1 C1 →
      is_call e s2 f2 C2 →
      s1 = s2 ∧ f1 = f2 ∧ C1 = C2;

    mixin_prim_step_resume p C e σ X :
      to_val e = None →
      prim_step p (resume_with C e, σ) X →
      prim_step p (e, σ) (λ '(e2, σ2), X (resume_with C e2, σ2));

    (* Just a meta-theorem to ensure that there are no cases left to cover.
       Not used in proofs. *)
    mixin_prim_step_total p e σ :
      to_val e = None →
      prim_step p (e, σ) (λ _, True)
  }.
End mlanguage_mixin.

Arguments mixin_expr_class : clear implicits.
Global Notation mixin_prog func := (gmap string func).

Structure mlanguage {val : Type} := Mlanguage {
  expr : Type;
  func : Type;
  state : Type;
  cont : Type;

  of_val : val → expr;
  to_val : expr → option val;

  is_call : expr → string → list val → cont → Prop;
  resume_with : cont → expr → expr;
  compose_cont : cont → cont → cont;

  apply_func : func → list val → option expr;
  prim_step : (gmap string func) → umrel (expr * state);


  mlanguage_mixin :
    MlanguageMixin (val:=val) of_val to_val is_call resume_with compose_cont
      apply_func prim_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments mlanguage : clear implicits.
Arguments Mlanguage {_ expr _ _ _ _ _ _ resume_with _ apply_func prim_step}.
Arguments of_val {_} _ _.
Arguments to_val {_ _} _.
Arguments is_call {_ _}.
Arguments resume_with {_ _}.
Arguments compose_cont {_ _}.
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
  Implicit Types K : cont Λ.
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
  Lemma val_prim_step p v σ X :
    prim_step p (of_val Λ v, σ) X → False.
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_prim_step p e f vs C σ X :
      is_call e f vs C →
        prim_step p (e, σ) X ↔
        (∀ (fn : func Λ) e2,
          p !! f = Some fn → Some e2 = apply_func fn vs → X (resume_with C e2, σ)).
  Proof. apply mlanguage_mixin. Qed.

  Lemma not_is_call e : is_Some (to_val e) → (∀ f vs C, ¬ is_call e f vs C).
  Proof. apply mlanguage_mixin. Qed.

  Lemma not_is_call_2 e f vs C : is_call e f vs C → to_val e = None.
  Proof.
    intros H; destruct (to_val e) eqn:Heq; try done.
    exfalso; apply mk_is_Some in Heq.
    eapply not_is_call in Heq. done.
  Qed.

  Lemma is_call_in_cont e C1 C2 s vv :
      is_call e s vv C2 → is_call (resume_with C1 e) s vv (compose_cont C1 C2).
  Proof. apply mlanguage_mixin. Qed.

  Lemma is_call_in_cont_inv e C1 C2 s vv :
      to_val e = None → is_call (resume_with C1 e) s vv C2 →
      ∃ C', is_call e s vv C' ∧ C2 = compose_cont C1 C'.
  Proof. apply mlanguage_mixin. Qed.

  Lemma resume_val e C : is_Some (to_val (resume_with C e)) → is_Some (to_val e).
  Proof. apply mlanguage_mixin. Qed.

  Lemma resume_not_val e C : to_val e = None → to_val (resume_with C e) = None.
  Proof.
    intros Heq; destruct (to_val (resume_with C e)) as [v|] eqn:Heq2; last done.
    eapply mk_is_Some in Heq2. apply resume_val in Heq2. rewrite Heq in Heq2.
    by destruct Heq2.
  Qed.

  Lemma resume_compose e C1 C2 :
      resume_with C1 (resume_with C2 e) = resume_with (compose_cont C1 C2) e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma is_call_unique e s1 s2 f1 f2 C1 C2 :
      is_call e s1 f1 C1 →
      is_call e s2 f2 C2 →
      s1 = s2 ∧ f1 = f2 ∧ C1 = C2.
  Proof. apply mlanguage_mixin. Qed.

  Lemma prim_step_resume p C e σ X :
      to_val e = None →
      prim_step p (resume_with C e, σ) X →
      prim_step p (e, σ) (λ '(e2, σ2), X (resume_with C e2, σ2)).
  Proof. apply mlanguage_mixin. Qed.

  (* There is no NB *)
  Lemma prim_step_is_total p e σ : to_val e = None → prim_step p (e,σ) (λ _, True).
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

End mlanguage.

(* discrete OFE instance for expr *)
Definition exprO {val} {Λ : mlanguage val} := leibnizO (expr Λ).
Global Instance expr_equiv {val} {Λ : mlanguage val} : Equiv (expr Λ). apply exprO. Defined.


Class linkable {val} (Λ : mlanguage val) (public_state : Type) := Linkable {
  private_state : Type;
  split_state : Λ.(state) → public_state → private_state → Prop
}.
