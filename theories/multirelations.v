From Coq Require Import Program Lia.
From stdpp Require Import base.

Notation multirelation A :=
  (A → (A → Prop) → Prop).

Definition upclosed {A} (M : multirelation A) :=
  ∀ x (X Y : A → Prop), M x X → (∀ x', X x' → Y x') → M x Y.

Structure umrel A := {
  mrel : A → (A → Prop) → Prop;
  umrel_upclosed : upclosed mrel;
}.

Arguments umrel : clear implicits.
Arguments mrel {A}.
Coercion mrel : umrel >-> Funclass.

Module umrel.

Program Definition union {A} (M N : umrel A) : umrel A :=
  {| mrel := λ x X, M x X ∨ N x X |}.
Next Obligation.
  intros * ? X Y [H1|H1] H2; [left|right]; eapply umrel_upclosed; eauto.
Qed.

Program Definition inter {A} (M N : umrel A) : umrel A :=
  {| mrel := λ x X, M x X ∧ N x X |}.
Next Obligation.
  intros * a X Y [H1 H2] H3. split; eapply umrel_upclosed; eauto.
Qed.

Program Definition seq {A} (M N : umrel A) : umrel A :=
  {| mrel := λ x X, ∃ Y, M x Y ∧ ∀ y, Y y → N y X |}.
Next Obligation.
  intros * a X Y [Y' [? ?]] ?. exists Y'. split; auto.
  intros. eapply umrel_upclosed; eauto.
Qed.

Notation "M ;;; N" := (seq M N) (at level 15, format "M  ;;;  N").

Lemma unfold_seq A (M N : umrel A) x X :
  (M ;;; N) x X = ∃ Y, M x Y ∧ ∀ y, Y y → N y X.
Proof. reflexivity. Qed.

Definition equiv {A} (M N : umrel A) :=
  ∀ x X, M x X ↔ N x X.

Lemma seq_assoc A (M N O : umrel A) :
  equiv ((M ;;; N) ;;; O) (M ;;; (N ;;; O)).
Proof.
  intros a X. split.
  { intros [Y [[XM [HM HN]] HO]]. cbn.
    exists XM. split; [auto|]. intros b HB.
    exists Y. split; auto. }
  { intros [Y [HM HNO]]. cbn. cbn in HNO.
    exists (λ c, O c X). split; [| auto].
    exists Y. split; [auto|]. intros b Hb.
    specialize (HNO b Hb) as [Z [? ?]].
    eapply umrel_upclosed; eauto. }
Qed.

Lemma inter_seq_l A (M N P : umrel A) :
  equiv (inter M N ;;; P) (inter (M ;;; P) (N ;;; P)).
Proof.
  intros a X. split.
  { unfold inter, seq; cbn. intros [? ((? & ?) & ?)].
    split; eauto. }
  { unfold inter, seq; cbn. intros [[Y1 [? ?]] [Y2 [? ?]]].
    exists (λ b, Y1 b ∨ Y2 b). split; [split|].
    - eapply umrel_upclosed; eauto.
    - eapply umrel_upclosed; eauto.
    - intros ? [?|?]; eauto. }
Qed.

Lemma union_seq_l A (M N P : umrel A) :
  equiv (union M N ;;; P) (union (M ;;; P) (N ;;; P)).
Proof.
  intros a X. split.
  { unfold union, seq; cbn. intros [? [[?|?] ?]]; [left|right]; eauto. }
  { unfold union, seq; cbn. intros [[? [? ?]] | [? [? ?]]]; eauto. }
Qed.

Program Definition id (A : Type) : umrel A :=
  {| mrel := λ x X, X x |}.
Next Obligation. intros a X Y. eauto. Qed.

Fixpoint repeat {A} (M : umrel A) (n : nat) : umrel A :=
  match n with
  | 0 => id A
  | S n => M ;;; repeat M n
  end.

Lemma repeat_once A (M : umrel A) x X : M x X → repeat M 1 x X.
Proof. cbn. eauto. Qed.

Lemma repeat_congruence A B (f : A → B) (M : umrel A) (M' : umrel B) n x X :
  (∀ x X, M x X → M' (f x) (λ y, ∃ x', y = f x' ∧ X x')) ->
  repeat M n x X ->
  repeat M' n (f x) (λ y, ∃ x', y = f x' ∧ X x').
Proof.
  revert x X. induction n.
  { intros x X Hcongr. cbn. eauto. }
  { intros x X Hcongr. cbn. intros (Y & HxY & HY).
    pose proof (Hcongr _ _ HxY) as Hcongr'.
    eexists. split; [eassumption|]. cbn.
    intros y (x' & -> & Hx'). specialize (HY _ Hx'). specialize (IHn x' X).
    eapply umrel_upclosed; eauto. }
Qed.

Program Definition repeats {A} (M : umrel A) : umrel A :=
  {| mrel := λ x X, ∃ n, repeat M n x X |}.
Next Obligation.
  intros * a X Y [n Hn]. revert Hn. induction n.
  - cbn. intros ? ?. exists 0. cbn. eauto.
  - cbn. intros [? [? ?]] ?. exists (S n). cbn.
    eexists. split; eauto. intros. eapply umrel_upclosed; eauto.
Qed.

Inductive star_mrel {A} (M : umrel A) : A → (A → Prop) → Prop :=
  | star_refl x (X : A → Prop) :
    X x → star_mrel M x X
  | star_step x Y X :
    M x Y →
    (∀ y, Y y → star_mrel M y X) →
    star_mrel M x X.

Program Definition star {A} (M : umrel A) : umrel A :=
  {| mrel := star_mrel M |}.
Next Obligation.
  intros *. unfold upclosed. intros x X X'. induction 1.
  { intros HH. eapply star_refl. eauto. }
  { intros HH. eapply star_step; eauto. }
Qed.

Lemma star_transitive {A} (M : umrel A) x Y X :
  star M x Y →
  (∀ y, Y y → star M y X) →
  star M x X.
Proof.
  intros HH. revert X. induction HH as [| ? ? ? ? ? IH].
  - eauto.
  - intros ? ?. eapply star_step; eauto. intros. eapply IH; eauto.
Qed.

Lemma star_of_repeats A (x : A) X (M : umrel A) :
  repeats M x X → star M x X.
Proof.
  intros [n Hrepeat].
  revert x X Hrepeat. induction n; simpl; intros * HH.
  - eapply star_refl. eauto.
  - destruct HH as (Y & ? & HH). eapply star_step; eauto.
    intros y Hy. specialize (HH y Hy). eapply IHn; eauto.
Qed.

Lemma not_repeats_of_star :
  ¬ (∀ A (M : umrel A) (x : A) X, star M x X → repeats M x X).
Proof.
  Inductive counter_ex_state := Start | Loop (n: nat) | End.
  intros H.
  specialize (H counter_ex_state).
  pose (rel := λ st (X : _ → Prop),
          (st = Start → ∀ n, X (Loop n)) ∧
          (st = Loop 0 → X End) ∧
          (∀ n, st = Loop (S n) → X (Loop n))).

  assert (relu: upclosed rel).
  { unfold upclosed, rel. intros st X X' (Hst & He & Hm) HX.
    repeat split; eauto. }
  pose (r := {| mrel := rel; umrel_upclosed := relu |}).

  assert (star r Start (λ st, st = End)) as Hstar.
  { eapply (star_step _ _ (λ st, ∃ n, st = Loop n)).
    { repeat split; eauto. congruence. }
    intros st' (n & ->). induction n.
    { eapply (star_step _ _ (λ st, st = End)).
      { repeat split; eauto; congruence. }
      intros ? ->. eapply star_refl. eauto. }
    { eapply (star_step _ _ (λ st, st = Loop n)).
      { repeat split; eauto; congruence. }
      intros ? ->. eauto. } }

  specialize (H r _ _ Hstar) as [n Hnsteps].
  destruct n as [| n]; [congruence|]. simpl in Hnsteps.
  destruct Hnsteps as (X1 & (HX1 & _ & _) & HH).
  specialize (HX1 eq_refl (S n)). (* key step! *)
  specialize (HH _ HX1). clear HX1 X1.
  induction n; simpl in HH; [congruence|].
  destruct HH as (X & HX & HH).
  destruct HX as (_ & _ & HX). specialize (HX _ eq_refl).
  specialize (HH _ HX). eauto.
Qed.

Unset Elimination Schemes.
Inductive star_mrel_AD {A} (M : umrel A) : A → (A → Prop) → Prop :=
  | star_refl_AD x (X : A → Prop) :
    X x → star_mrel_AD M x X
  | star_step_AD x X :
    (∀ Y, M x Y → ∃ y, Y y ∧ star_mrel_AD M y X) →
    star_mrel_AD M x X.
Lemma star_mrel_AD_ind {A:Type} (M : umrel A) (P : A → (A → Prop) → Prop) : 
  (∀ x(X:A→Prop), X x → P x X) →
  (∀ x X, (∀ Y, M x Y → ∃ y, Y y ∧ star_mrel_AD M y X ∧ P y X) → P x X) →
  ∀ y Y, star_mrel_AD M y Y → P y Y.
Proof.
  intros Hrefl Hstep. fix IH 3.
  intros y Y [x X|x X H]; clear y Y.
  1: eapply Hrefl, H.
  eapply (Hstep x X).
  intros Y HY. destruct (H Y HY) as (y&Hy&Hmrel).
  exists y. split. 2:split.
  1: apply Hy.
  1: apply Hmrel.
  now eapply IH.
Qed.

Program Definition star_AD {A} (M : umrel A) : umrel A :=
  {| mrel := star_mrel_AD M |}.
Next Obligation.
  intros *. unfold upclosed. intros x X X'. induction 1.
  { intros HH. eapply star_refl_AD. eauto. }
  { intros HH. eapply star_step_AD. intros Y HY.
    destruct (H Y HY) as (y&Hy&Hmrel&HIH).
    exists y; split. 1: apply Hy.
    eapply HIH. apply HH. }
Qed.

Lemma star_AD_transitive {A} (M : umrel A) x Y X :
  star_AD M x Y →
  (∀ y, Y y → star_AD M y X) →
  star_AD M x X.
Proof.
  intros HH Hcont. induction HH as [z Z H|z Z IH].
  - eapply Hcont, H.
  - eapply star_step_AD. intros Y HY.
    destruct (IH Y HY) as (y&Hy&Hmrel&HIH).
    exists y. split. 1: apply Hy. now eapply HIH.
Qed.
Set Elimination Schemes.

CoInductive trace_mrel {A} (M : umrel A) : A → (A → Prop) → Prop :=
| trace_refl x (X : A → Prop) :
  X x → trace_mrel M x X
| trace_step x Y (X : A → Prop) :
  M x Y →
  (∀ y, Y y → trace_mrel M y X) →
  trace_mrel M x X.

Program Definition trace {A} (M : umrel A) : umrel A :=
  {| mrel := trace_mrel M |}.
Next Obligation.
  intros *. unfold upclosed. cofix IH.
  intros x X X'. inversion 1; subst.
  { intros HH. eapply trace_refl. apply HH; assumption. }
  { intros HH. eapply trace_step.
    { eassumption. }
    { intros y Hy. eapply IH; clear IH; eauto. } }
Qed.

End umrel.

Arguments mrel : simpl never.
