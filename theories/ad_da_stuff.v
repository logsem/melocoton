From iris Require Import prelude.
From Coq.Logic Require Import Classical.

Lemma not_forall_exists {P:Type} {Q:P→Prop} : (¬ (∀ (p:P), Q p)) ↔ (∃ (p:P), ¬ Q p).
Proof. split; try firstorder.
       destruct (classic (∃ p, ¬ Q p)); try done.
      exfalso. eapply H. intros p. destruct (classic (Q p)); try done.
      exfalso. eapply H0. by eexists.
Qed.

Section Foo.
  Context (T:Type).
  Definition mrel := T → (T → Prop) → Prop.

  Context (stepAD stepDA : mrel).
  Implicit Type X Y : T → Prop.
  Definition upclosed (M : mrel) := forall x X1 X2, (forall y, X1 y → X2 y) → M x X1 → M x X2.
  Unset Elimination Schemes.
  Inductive rtc_stepAD : mrel :=
  | rtc_AD_refl x X : X x → rtc_stepAD x X
  | rtc_AD_trns x X :
      (∀ X', stepAD x X' → ∃ x', X' x' ∧ rtc_stepAD x' X) →
      rtc_stepAD x X.

  Lemma rtc_stepAD_ind (P : T → (T → Prop) → Prop) :
    (∀ (x : T) X, X x → P x X)
  → (∀ (x : T) X, 
        (∀ X', stepAD x X' → ∃ x' : T, X' x' ∧ rtc_stepAD x' X ∧ P x' X)
      → P x X)
  →  ∀ (t : T) (P0 : T → Prop), rtc_stepAD t P0 → P t P0.
  Proof.
    intros Hrefl Htrns.
    fix IH 3. intros ? ? [x X|x X Hrec].
    - by eapply Hrefl.
    - eapply Htrns. intros X' HX'. destruct (Hrec X' HX') as (x' & HXx' & Hrtc).
      eauto.
  Qed.


  Inductive rtc_stepDA : mrel :=
  | rtc_DA_refl x X : X x → rtc_stepDA x X
  | rtc_DA_trns x X :
      (∃ X', stepDA x X' ∧ ∀ x', X' x' → rtc_stepDA x' X) →
      rtc_stepDA x X.

  Lemma rtc_stepDA_ind (P : T → (T → Prop) → Prop) :
    (∀ (x : T) X, X x → P x X)
  → (∀ (x : T) X, (∃ X', stepDA x X' ∧ (∀ x' : T, X' x' → rtc_stepDA x' X ∧ P x' X)) → P x X)
  →  ∀ (t : T) (P0 : T → Prop), rtc_stepDA t P0 → P t P0.
  Proof.
    intros Hrefl Htrns.
    fix IH 3. intros ? ? [x X|x X Hrec].
    - by eapply Hrefl.
    - eapply Htrns. destruct (Hrec) as (x' & HXx' & Hrtc).
      exists x'. split; first done. intros X' HX'. specialize (Hrtc X' HX').
      split; first done. by eapply IH.
  Qed.
  
Set Elimination Schemes.


  Lemma comp_step_AD s S U :
    rtc_stepAD s S →
    (∀ s', S s' → rtc_stepAD s' U) →
    rtc_stepAD s U.
  Proof.
    induction 1; intros HH.
    - by eapply HH.
    - eapply rtc_AD_trns.
      intros X' HX'. specialize (H X' HX') as H2.
      destruct H2 as (x' & HXx' & Hstep1 & IH).
      exists x'. split; first done. eapply IH. done.
  Qed.


  Lemma comp_step_DA s S U :
    rtc_stepDA s S →
    (∀ s', S s' → rtc_stepDA s' U) →
    rtc_stepDA s U.
  Proof.
    induction 1 as [s S|s S IH] in U|-*; intros HH.
    - eauto.
    - eapply rtc_DA_trns.
      destruct IH as (X' & Hstep1 & H).
      exists X'; split; first done.
      intros x' HXx'. eapply H; try done.
  Qed.

  Definition safe_AD s :=
    ∀ S, rtc_stepAD s S → ∃ s', S s'.
  Definition safe_AD_steps s :=
    ∀ S, rtc_stepAD s S → ∃ s', S s' ∧ ∃ P, stepAD s' P. (* avoid upclosedness *)

  Definition safe_DA s :=
    ∀ S, rtc_stepDA s S → ∃ s', S s'.
  Definition safe_DA_steps s :=
    ∀ S, rtc_stepDA s S → ∃ s', S s' ∧ ¬ stepDA s' (λ _, False).


  Lemma safe_AD_steps_eq s : safe_AD s → safe_AD_steps s.
  Proof.
    intros H S HS.
    destruct (classic (∃ s', S s' ∧ ∃ P, stepAD s' P)); try done.
    assert (∀ s', ¬ S s' ∨ ¬ ∃ P, stepAD s' P) as Hs.
    { intros s'. eapply not_and_or. intros [HH HHL]. eapply H0. by eexists. }
    eapply H.
    eapply comp_step_AD. 1: done.
    intros s' Hs'. eapply rtc_AD_trns.
    intros X' HX'. exfalso.
    destruct (Hs s'); try tauto.
    eapply H1. by eexists.
  Qed.

  Lemma safe_DA_steps_eq s : safe_DA s → safe_DA_steps s.
  Proof.
    intros H S HS.
    destruct (classic (∃ s', S s' ∧ ¬ stepDA s' (λ _, False))); try done.
    assert (∀ s', ¬ S s' ∨ ¬¬stepDA s' (λ _, False)) as Hs.
    { intros s'. eapply not_and_or. intros HH. eapply H0. by eexists. }
    eapply H.
    eapply comp_step_DA. 1: done.
    intros s' Hs'. eapply rtc_DA_trns.
    destruct (Hs s'); try tauto.
    eexists; split. 1: eapply NNPP, H1. tauto.
  Qed.

End Foo.
Section Bar.
  Context (T:Type).

  Context (stepAD : mrel T).
  Definition stepDA : mrel T := fun s S =>
    ∀ S', stepAD s S' → ∃ s', S' s' ∧ S s'.

  Lemma rtc_equiv s S : (rtc_stepAD T stepAD s S) ↔ (rtc_stepDA T stepDA s S).
  Proof. split.
  - induction 1.
    1: by econstructor.
    eapply rtc_DA_trns.
    exists (fun x' => rtc_stepAD T stepAD x' X ∧ rtc_stepDA T stepDA x' X).
    split; first done.
    intros x' [Hx Hy]. done.
  - induction 1.
    1: by econstructor.
    eapply rtc_AD_trns. intros X' Hstep.
    destruct H as (X2' & HstepDA & Hrec).
    specialize (HstepDA _ Hstep) as (s' & HXs' & HX2').
    destruct (Hrec _ HX2') as (_ & Huse2).
    exists s'. split; done.
  Qed.

End Bar.
Section Baz.
  Context (T:Type).

  Context (stepDA : mrel T).
  Definition stepAD : mrel T := fun s S =>
    ∀ S', stepDA s S' → ∃ s', S' s' ∧ S s'.

  Lemma rtc_equiv_other s S : (rtc_stepAD T stepAD s S) ↔ (rtc_stepDA T stepDA s S).
  Proof. split.
  - induction 1.
    1: by econstructor.
    eapply rtc_DA_trns.
    destruct (classic (∃ X', stepDA x X' ∧ (∀ x', X' x' → rtc_stepDA T stepDA x' X))) as [[X' HC]|HC]; first by eexists.
    exfalso; destruct (H (λ x', ¬rtc_stepDA T stepDA x' X)) as (?&?&?&?); last tauto.
    intros K HK. destruct (classic (∃ s', K s' ∧ ¬ rtc_stepDA T stepDA s' X)); try done.
    exfalso. eapply HC. exists K. split; try done.
    intros x' Hx'1. destruct (classic (rtc_stepDA T stepDA x' X)); try done.
    exfalso; eapply H0; eauto.
  - induction 1.
    1: by econstructor.
    eapply rtc_AD_trns. intros X' Hstep.
    destruct H as (X2' & HstepDA & Hrec).
    specialize (Hstep _ HstepDA) as (s' & HX2' & HXs').
    destruct (Hrec _ HX2') as (_ & Huse2).
    exists s'. split; done.
  Qed.

End Baz.

