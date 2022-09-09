From Coq Require Import Program.

Definition mrel A B : Type :=
  A -> (B -> Prop) -> Prop.

Definition upclosed {A B} (M: mrel A B) :=
  forall a (X Y: B -> Prop),
    M a X ->
    (forall b, X b -> Y b) ->
    M a Y.

Record umrel A B := {
  rel :> mrel A B;
  umrel_upclosed : upclosed rel;
}.

Arguments mrel : clear implicits.
Arguments umrel : clear implicits.
Arguments rel {A B}.
Notation "A ->> B" := (umrel A B) (at level 100).

Program Definition union {A B} (M N: A ->> B) : A ->> B :=
  {| rel := fun a X => rel M a X \/ rel N a X |}.
Next Obligation.
  intros a X Y [H1|H1] H2; [left|right]; eapply umrel_upclosed; eauto.
Qed.

Program Definition inter {A B} (M N: A ->> B) : A ->> B :=
  {| rel := fun a X => rel M a X /\ rel N a X |}.
Next Obligation.
  intros a X Y [H1 H2] H3. split; eapply umrel_upclosed; eauto.
Qed.

Program Definition seq {A B C} (M: A ->> B) (N: B ->> C) : A ->> C :=
  {| rel :=
     fun a X =>
       exists Y, rel M a Y /\
         forall y, Y y -> rel N y X |}.
Next Obligation.
  intros a X Y [Y' [? ?]] ?. exists Y'. split; auto.
  intros. eapply umrel_upclosed; eauto.
Qed.

Notation "M ;;; N" := (seq M N) (at level 10, format "M  ;;;  N").

Definition equiv {A B} (M N: A ->> B) :=
  forall a X, rel M a X <-> rel N a X.

Lemma seq_assoc {A B C D} (M: A ->> B) (N: B ->> C) (O: C ->> D) :
  equiv ((M ;;; N) ;;; O) (M ;;; (N ;;; O)).
Proof.
  intros a X. split.
  { intros [Y [[XM [HM HN]] HO]]. cbn.
    exists XM. split; [auto|]. intros b HB.
    exists Y. split; auto. }
  { intros [Y [HM HNO]]. cbn. cbn in HNO.
    exists (fun (c:C) => rel O c X). split; [| auto].
    exists Y. split; [auto|]. intros b Hb.
    specialize (HNO b Hb) as [Z [? ?]].
    eapply umrel_upclosed; eauto. }
Qed.

Lemma inter_seq_l {A B C} (M N: A ->> B) (P: B ->> C) :
  equiv ((inter M N) ;;; P) (inter (M ;;; P) (N ;;; P)).
Proof.
  intros a X. split.
  { unfold inter, seq; cbn. intros [? ((? & ?) & ?)].
    split; eauto. }
  { unfold inter, seq; cbn. intros [[Y1 [? ?]] [Y2 [? ?]]].
    exists (fun b => Y1 b \/ Y2 b). split; [split|].
    - eapply umrel_upclosed; eauto.
    - eapply umrel_upclosed; eauto.
    - intros ? [?|?]; eauto. }
Qed.

Lemma union_seq_l {A B C} (M N: A ->> B) (P: B ->> C) :
  equiv ((union M N) ;;; P) (union (M ;;; P) (N ;;; P)).
Proof.
  intros a X. split.
  { unfold union, seq; cbn. intros [? [[?|?] ?]]; [left|right]; eauto. }
  { unfold union, seq; cbn. intros [[? [? ?]] | [? [? ?]]]; eauto. }
Qed.

Program Definition id (A: Type) : A ->> A :=
  {| rel := fun a X => X a |}.
Next Obligation. intros a X Y. eauto. Qed.

Fixpoint repeat {A} (M: A ->> A) (n: nat) : A ->> A :=
  match n with
  | 0 => id A
  | S n => seq M (repeat M n)
  end.

Lemma repeat_once {A} (M: A ->> A) x X : rel M x X -> rel (repeat M 1) x X.
Proof. cbn. eauto. Qed.

Lemma repeat_congruence {A B} (f : A -> B) (M: A ->> A) (M': B ->> B) n x X :
  (forall x X, rel M x X -> rel M' (f x) (fun y => exists x', y = f x' /\ X x')) ->
  rel (repeat M n) x X ->
  rel (repeat M' n) (f x) (fun y => exists x', y = f x' /\ X x').
Proof.
  revert x X. induction n.
  { intros x X Hcongr. cbn. eauto. }
  { intros x X Hcongr. cbn. intros (Y & HxY & HY).
    pose proof (Hcongr _ _ HxY) as Hcongr'.
    eexists. split; [eassumption|]. cbn.
    intros y (x' & -> & Hx'). specialize (HY _ Hx'). specialize (IHn x' X).
    eapply multirelations.umrel_upclosed; eauto. }
Qed.

Program Definition star {A} (M: A ->> A): A ->> A :=
  {| rel := fun a X => exists n, rel (repeat M n) a X |}.
Next Obligation.
  intros a X Y [n Hn]. revert Hn. induction n.
  - cbn. intros ? ?. exists 0. cbn. eauto.
  - cbn. intros [? [? ?]] ?. exists (S n). cbn.
    eexists. split; eauto. intros. eapply umrel_upclosed; eauto.
Qed.

Arguments rel : simpl never.
