From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language.
From iris.algebra Require Import stepindex.

Section ToMlang.
  Context {val : Type}.
  Context (Λ : language val).

  Local Notation prog := (gmap string Λ.(func)).
  Local Notation expr_state := ((Λ.(expr) * Λ.(state)))%type.

  Inductive prim_step_mrel : prog → expr_state → (expr_state → Prop) → Prop :=
  | LiftStep p e1 σ1 (X : _ → Prop) :
      (to_outcome e1 = None → reducible p e1 σ1) →
      (∀ e2 σ2, prim_step p e1 σ1 e2 σ2 → X (e2, σ2)) →
      prim_step_mrel p (e1, σ1) X.

  Program Definition prim_step (p : prog) : umrel (expr_state) :=
    {| mrel := prim_step_mrel p |}.
  Next Obligation.
    intros p. intros [e1 σ1] X Y Hstep HXY. inversion Hstep; subst.
    - eapply (LiftStep p e1 σ1); first done.
      intros ? ? HH; specialize (H4 _ _ HH); eauto.
  Qed.

  Notation ectx := Λ.(ectx).

  Lemma language_mlanguage_mixin :
    MlanguageMixin (val:=val) (of_outcome Λ) to_outcome Λ.(of_call) Λ.(is_call) empty_ectx
      Λ.(comp_ectx) Λ.(fill) Λ.(apply_func) prim_step.
  Proof using.
    constructor.
    - apply to_of_outcome.
    - apply of_to_outcome.
    - intros p v σ. constructor.
      + rewrite to_of_outcome. inversion 1.
      + apply outcome_prim_step.
    - intros p e f vs C σ X Hcall. split; intros H.
      + inversion H; simplify_eq.
        destruct H3 as (?&?&Hstep).
        { destruct (to_outcome e) eqn:HH; auto.
          eapply is_outcome_not_call in Hcall; by eauto. }
        pose proof Hstep as Hstep2.
        eapply call_prim_step in Hstep as (?&?&?&?&?&?); eauto; simplify_eq.
        do 2 eexists. repeat split; eauto.
      + destruct H as (fn&?&?&?&?). constructor.
        * intros _. rewrite (is_call_of_call e f vs C) //.
          eapply reducible_fill. do 2 eexists. eapply call_prim_step.
          1: eapply of_call_is_call. do 2 eexists; eauto.
        * intros *. pose proof (is_call_of_call e f vs C Hcall).
          intros Hstep. rewrite call_prim_step in Hstep; eauto.
          destruct Hstep as (?&?&?&?&?&?); simplify_eq. congruence.
    - eapply is_outcome_not_call.
    - eapply is_call_in_ctx.
    - eapply of_call_is_call.
    - eapply is_call_of_call.
    - eapply is_call_of_call_inv.
    - intros e K H. apply fill_outcome_val, H.
    - eapply fill_outcome.
    - eapply fill_comp.
    - eapply fill_empty.
    - intros p C e σ X Hnv. inversion 1; simplify_eq. econstructor.
      { intros ?. eapply reducible_fill; eauto. }
      intros e2 σ2 Hstep. eapply fill_step_inv in Hstep as (?&?&?); eauto.
    - intros p e σ ? H. inversion 1; simplify_eq.
      destruct H4 as (?&?&?); eauto.
  Qed.

  Definition lang_to_mlang : mlanguage val :=
    Mlanguage language_mlanguage_mixin.

  Inductive lang_to_mlang_split_state : Λ.(state) → Λ.(state) → unit → Prop :=
    split_state_refl σ : lang_to_mlang_split_state σ σ ().

  Global Program Instance lang_to_mlang_linkable `{SI:indexT} : linkable lang_to_mlang Λ.(state) := {
    linking.private_state := unit;
    linking.split_state := lang_to_mlang_split_state;
  }.

End ToMlang.
