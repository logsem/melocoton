From Coq Require Import Program.
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

Program Definition star {A} (M : umrel A) : umrel A :=
  {| mrel := λ x X, ∃ n, repeat M n x X |}.
Next Obligation.
  intros * a X Y [n Hn]. revert Hn. induction n.
  - cbn. intros ? ?. exists 0. cbn. eauto.
  - cbn. intros [? [? ?]] ?. exists (S n). cbn.
    eexists. split; eauto. intros. eapply umrel_upclosed; eauto.
Qed.

End umrel.

Arguments mrel : simpl never.
