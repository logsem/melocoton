From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export language_commons.

Section language_mixin.
  Context {expr val func ectx state : Type}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (of_call : string → list val → expr).
  Context (is_call : expr → string → list val → ectx → Prop).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).

  (** A program is a map from function names to function bodies. *)
  Local Notation mixin_prog := (gmap string func).

  Context (apply_func : func → list val → option expr).
  Context (prim_step : mixin_prog → expr → state → expr → state → Prop).

  Record LanguageMixin := {
    mixin_to_of_val c : to_val (of_val c) = Some c;
    mixin_of_to_val e c : to_val e = Some c → of_val c = e;

    (** Reduction behavior of the special classes of expressions *)
    mixin_val_prim_step p v σ1 e2 σ2 :
      prim_step p (of_val v) σ1 e2 σ2 → False;
    mixin_call_prim_step p f vs K e σ1 e' σ2 :
      is_call e f vs K →
      prim_step p e σ1 e' σ2 ↔
      ∃ (fn : func) (e2 : expr),
        p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ e' = fill K e2 ∧ σ2 = σ1;

    (** Same-language linking requires those *)
    mixin_prim_step_call_dec p e σ e' σ' :
      prim_step p e σ e' σ' →
      (∃ fn vs K, is_call e fn vs K) ∨ (∀ fn vs K, ¬ is_call e fn vs K);
    mixin_prim_step_no_call p1 p2 e σ e' σ' :
      (∀ f vs K, ¬ is_call e f vs K) →
      prim_step p1 e σ e' σ' →
      prim_step p2 e σ e' σ';

    mixin_is_val_not_call e : is_Some (to_val e) → (∀ f vs K, ¬ is_call e f vs K);
    mixin_is_call_in_ctx e K1 K2 fn vs :
      is_call e fn vs K2 → is_call (fill K1 e) fn vs (comp_ectx K1 K2);
    mixin_of_call_is_call fn vs : is_call (of_call fn vs) fn vs empty_ectx;
    mixin_is_call_of_call e fn vs K : is_call e fn vs K → e = fill K (of_call fn vs);
    mixin_is_call_of_call_inv fn vs fn' vs' K :
      is_call (of_call fn vs) fn' vs' K →
      fn' = fn ∧ vs' = vs ∧ K = empty_ectx;

    mixin_fill_val e K : is_Some (to_val (fill K e)) → is_Some (to_val e);
    mixin_fill_comp e K1 K2 :
      fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_empty e :
      fill empty_ectx e = e;

    (** Those are key for proving [wp_bind] *)
    mixin_prim_step_fill p K e σ e' σ' :
      prim_step p e σ e' σ' →
      prim_step p (fill K e) σ (fill K e') σ';
    mixin_fill_step_inv p K e1' σ1 e2 σ2 :
      to_val e1' = None → prim_step p (fill K e1') σ1 e2 σ2 →
      ∃ e2', e2 = fill K e2' ∧ prim_step p e1' σ1 e2' σ2;
  }.
End language_mixin.

Global Notation mixin_prog func := (gmap string func).

Structure language {val : Type} := Language {
  expr : Type;
  func : Type;
  ectx : Type;
  state : Type;

  of_val : val → expr;
  to_val : expr → option val;
  of_call : string → list val → expr;
  is_call : expr → string → list val → ectx → Prop;

  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  apply_func : func → list val → option expr;
  prim_step : mixin_prog func → expr → state → expr → state → Prop;

  language_mixin :
    LanguageMixin of_val to_val of_call is_call  empty_ectx comp_ectx fill
      apply_func prim_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments language : clear implicits.
Arguments Language {_ expr _ _ _ _ _ _ _ _ _ _ apply_func prim_step}.
Arguments of_val {_} _ _.
Arguments to_val {_ _} _.
Arguments of_call {_} _ _.
Arguments is_call {_ _}.
Arguments empty_ectx {_ _}.
Arguments comp_ectx {_ _} _ _.
Arguments fill {_ _} _ _.
Arguments apply_func {_ _}.
Arguments prim_step {_ _} _ _ _ _ _.

(* A [Definition] throws off Coq's "old" ("tactic") unification engine *)
Notation prog Λ := (mixin_prog Λ.(func)).

(* From an ectx_language, we can construct a language. *)
Section language.
  Context {val : Type}.
  Context {Λ : language val}.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.

  Lemma to_of_val v : to_val (of_val Λ v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val Λ v = e.
  Proof. apply language_mixin. Qed.

  Lemma of_val_inj v1 v2 : of_val Λ v1 = of_val Λ v2 → v1 = v2.
  Proof.
    intros H. enough (Some v1 = Some v2) by congruence.
    rewrite <- !to_of_val. rewrite H. done.
  Qed.

  Lemma val_prim_step p v σ1 e2 σ2 :
    prim_step p (of_val Λ v) σ1 e2 σ2 → False.
  Proof. apply language_mixin. Qed.
  Lemma call_prim_step p fn vs K e σ1 e' σ2 :
    is_call e fn vs K →
    prim_step p e σ1 e' σ2 ↔
    ∃ (f : func Λ) e2, p !! fn = Some f ∧ Some e2 = apply_func f vs ∧ e' = fill K e2 ∧ σ2 = σ1.
  Proof. apply language_mixin. Qed.
  Lemma prim_step_call_dec p e σ e' σ' :
    prim_step p e σ e' σ' →
    (∃ fn vs K, is_call e fn vs K) ∨ (∀ fn vs K, ¬ is_call e fn vs K).
  Proof. apply language_mixin. Qed.
  Lemma prim_step_no_call p1 p2 e σ e' σ' :
    (∀ f vs K, ¬ is_call e f vs K) →
    prim_step p1 e σ e' σ' →
    prim_step p2 e σ e' σ'.
  Proof. apply language_mixin. Qed.

  Lemma is_val_not_call e : is_Some (to_val e) → (∀ f vs C, ¬ is_call e f vs C).
  Proof. apply language_mixin. Qed.
  Lemma is_val_not_call_2 e f vs C : is_call e f vs C → to_val e = None.
  Proof.
    intros H; destruct (to_val e) eqn:Heq; try done.
    exfalso; apply mk_is_Some in Heq.
    eapply is_val_not_call in Heq. done.
  Qed.

  Lemma is_call_in_ctx e K1 K2 fn vs :
    is_call e fn vs K2 → is_call (fill K1 e) fn vs (comp_ectx K1 K2).
  Proof. apply language_mixin. Qed.

  Lemma of_call_is_call fn vs : is_call (of_call Λ fn vs) fn vs empty_ectx.
  Proof. apply language_mixin. Qed.
  Lemma is_call_of_call e fn vs K : is_call e fn vs K → e = fill K (of_call Λ fn vs).
  Proof. apply language_mixin. Qed.
  Lemma is_call_of_call_inv fn vs fn' vs' K :
    is_call (of_call Λ fn vs) fn' vs' K →
    fn' = fn ∧ vs' = vs ∧ K = empty_ectx.
  Proof. apply language_mixin. Qed.

  Lemma fill_val e K : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply language_mixin. Qed.
  Lemma fill_val_2 K e v : fill K e = of_val Λ v → is_Some (to_val e).
  Proof. intros HH. eapply (fill_val _ K). rewrite HH to_of_val//. Qed.

  Lemma fill_not_val e K : to_val e = None → to_val (fill K e) = None.
  Proof.
    intros Heq; destruct (to_val (fill K e)) as [v|] eqn:Heq2; last done.
    eapply mk_is_Some in Heq2. apply fill_val in Heq2. rewrite Heq in Heq2.
    by destruct Heq2.
  Qed.

  Lemma fill_comp e K1 K2 :
    fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply language_mixin. Qed.
  Lemma fill_empty e :
    fill empty_ectx e = e.
  Proof. apply language_mixin. Qed.

  Lemma val_stuck p e σ e' σ' : prim_step p e σ e' σ' → to_val e = None.
  Proof.
    intros Hstep. destruct (to_val e) eqn:HH; eauto. apply of_to_val in HH; subst.
    by apply val_prim_step in Hstep.
  Qed.

  Lemma prim_step_fill p K e σ e' σ' :
    prim_step p e σ e' σ' →
    prim_step p (fill K e) σ (fill K e') σ'.
  Proof. apply language_mixin. Qed.

  Definition reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ', prim_step p e σ e' σ'.

  Lemma reducible_not_val p e σ : reducible p e σ → to_val e = None.
  Proof. intros (?&?&?); eauto using val_stuck. Qed.

  Lemma reducible_fill p e σ K : reducible p e σ → reducible p (fill K e) σ.
  Proof.
    intros HH. pose proof (reducible_not_val _ _ _ HH).
    destruct HH as (e' & σ' & Hs).
    eexists (fill K e'), σ'. eapply prim_step_fill; eauto.
  Qed.

  Lemma reducible_mono p1 p2 e σ : p1 ⊆ p2 → reducible p1 e σ → reducible p2 e σ.
  Proof.
    intros Hsub (?&?&Hstep).
    pose proof Hstep as Hstep'. apply prim_step_call_dec in Hstep'.
    destruct Hstep' as [(?&?&?&Hcall)|Hncall].
    { eapply call_prim_step in Hstep; last done. destruct Hstep as (?&?&?&?&?&?); simplify_eq.
      eexists _, _. eapply call_prim_step; eauto. eexists _, _. split_and!; eauto.
      eapply lookup_weaken; eauto. }
    { eapply prim_step_no_call in Hstep; eauto. by eexists _, _. }
  Qed.

  Lemma fill_step_inv K p e1' σ1 e2 σ2 :
    to_val e1' = None → prim_step p (fill K e1') σ1 e2 σ2 →
    ∃ e2', e2 = fill K e2' ∧ prim_step p e1' σ1 e2' σ2.
  Proof. apply language_mixin. Qed.

  Inductive rtc_step (p : prog Λ) : expr Λ → state Λ → expr Λ → state Λ → Prop :=
    rtc_refl e σ : rtc_step p e σ e σ
  | rtc_plus e σ e' σ' ex σx : prim_step p e σ e' σ' → rtc_step p e' σ' ex σx → rtc_step p e σ ex σx.

  Definition safe p (e : expr Λ) (σ : state Λ) (Φ : val → Prop) := match to_val e with
    Some v => Φ v
  | None => reducible p e σ end.

  Record pure_step (p : language.prog Λ) (e1 e2 : expr Λ) := {
    pure_step_safe σ1 : reducible p e1 σ1;
    pure_step_det σ1 e2' σ2 :
      prim_step p e1 σ1 e2' σ2 → σ2 = σ1 ∧ e2' = e2
  }.

  Class PureExec (φ : Prop) (n : nat)  (p : language.prog Λ) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps (pure_step p) n e1 e2.

End language.

(* discrete OFE instance for expr and thread_id *)
Definition exprO `{indexT} {val} {Λ : language val} := leibnizO (expr Λ).
Global Instance expr_equiv `{indexT} {val} {Λ : language val} : Equiv (expr Λ). apply exprO. Defined.

Notation lang_prog Λ := (gmap string Λ.(func)).
