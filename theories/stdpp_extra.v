From Coq Require Import ssreflect.
From stdpp Require Import relations strings gmap.

Definition gmap_inj `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v → m !! k2 = Some v → k1 = k2.

Lemma gmap_inj_extend `{Countable K} {V} (m : gmap K V) k v :
  gmap_inj m →
  k ∉ dom m →
  (∀ k' v', m !! k' = Some v' → v ≠ v') →
  gmap_inj (<[k:=v]> m).
Proof.
  intros Hinj Hk Hv k1 k2 v' Hk1 Hk2.
  destruct (decide (k = k1)) as [<-|]; destruct (decide (k = k2)) as [<-|];
    auto.
  { rewrite lookup_insert in Hk1. rewrite lookup_insert_ne // in Hk2.
    simplify_eq. exfalso. by apply Hv in Hk2. }
  { rewrite lookup_insert_ne // in Hk1. rewrite lookup_insert in Hk2.
    simplify_eq. exfalso. by apply Hv in Hk1. }
  { rewrite lookup_insert_ne // in Hk1. rewrite lookup_insert_ne // in Hk2.
    eapply Hinj; eauto. }
Qed.

Ltac exploit_gmap_inj :=
  progress repeat match goal with
  | Hinj : gmap_inj ?m,
    H1 : ?m !! _ = Some ?v,
    H2 : ?m !! _ = Some ?v |- _ =>
    pose proof (Hinj _ _ _ H1 H2); subst; clear H2
  end.

Definition codom {A B : Type} `{Countable A} `{Countable B}: gmap A B → gset B := map_to_set (fun a b => b).

Lemma codom_spec {A B : Type} `{Countable A} `{Countable B} (m : gmap A B) v : v ∈ codom m <-> exists k, m !! k = Some v.
Proof.
  split.
  - intros (k&?&Hl&->)%elem_of_map_to_set. by eexists.
  - intros (k&Hk); eapply elem_of_map_to_set; by eexists _,_.
Qed.

Lemma codom_spec_2 {A B : Type} `{Countable A} `{Countable B} (m : gmap A B) k v : m !! k = Some v → v ∈ codom m.
Proof.
  intros HH. apply codom_spec. by eexists.
Qed.

Lemma list_insert_lookup_inv  A (vs:list A) (i:nat) v k : k ∈ <[ i := v ]> vs → k = v ∨ k ∈ vs.
Proof.
  induction vs as [|vh vs IH] in i|-*.
  - intros []%elem_of_nil.
  - destruct i; cbn.
    + intros [<- | Hvs]%elem_of_cons; first by left. by do 2 right.
    + intros [<- | Hvs]%elem_of_cons; first (right; by left).
      destruct (IH _ Hvs) as [-> | Hr]; first by left.
      by do 2 right.
Qed.

Fixpoint In2 {A} (a : A) (l : list A) : Type :=
  match l with
  | [] => False
  | b :: m => sum (b = a) (In2 a m)
  end.

Lemma In2_In {A} (a:A) l : In2 a l -> In a l.
Proof.
  induction l.
  - easy.
  - intros [Hl|Hr]; [now left | right]. apply IHl, Hr.
Qed.

Lemma list_eq_sliced {X} (L1 L2 R1 R2 : list X) (M1 M2 : X) (P : X -> Prop) :
  L1 ++ M1 :: R1 = L2 ++ M2 :: R2 ->
  (forall x, In x L1 -> P x) -> (forall x, In x L2 -> P x) -> ~ P M1 -> ~P M2 ->
  L1 = L2 /\ M1 = M2 /\ R1 = R2.
Proof.
  revert L2. induction L1 as [|L1L L1R IH]; intros L2 Heq HL1 HL2 HM1 HM2; destruct L2 as [|L2L L2R].
  - cbn in Heq; repeat split; congruence.
  - cbn in Heq. exfalso. apply HM1. apply HL2. left. congruence.
  - cbn in Heq. exfalso. apply HM2. apply HL1. left. congruence.
  - cbn in Heq. destruct (IH L2R) as (-> & -> & ->).
    + congruence.
    + intros x Hx. apply HL1. now right.
    + intros x Hx. apply HL2. now right.
    + easy.
    + easy.
    + repeat split. congruence.
Qed.

Lemma map_inj {X Y} (f : X -> Y) : (forall x y, f x = f y -> x = y)
  -> forall Lx Ly, map f Lx = map f Ly -> Lx = Ly.
Proof.
  intros Hinj. intros Lx. induction Lx as [|x xr IHx].
  - intros [|y yr]. 1:easy. cbn. congruence.
  - intros [|y yr]. 1:cbn; congruence. cbn. intros Heq. f_equal.
    + apply Hinj. congruence.
    + apply IHx. congruence.
Qed.
