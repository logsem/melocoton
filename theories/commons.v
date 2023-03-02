From stdpp Require Import relations strings gmap.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import ofe.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

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
  repeat match goal with
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

Section language_commons.
  Context {val : Type}.
  (** Classifying expressions into values and calls. *)
  Inductive mixin_expr_class :=
  | ExprVal (v : val) : mixin_expr_class
  | ExprCall (fn_name : string) (arg : list val) : mixin_expr_class.
End language_commons.

Lemma excl_auth_eq A `{inG Σ (excl_authR (leibnizO A))} γ (x y: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) -∗ ⌜x = y⌝.
Proof.
  iIntros "H1 H2". iDestruct (own_op with "[$H1 $H2]") as "H".
  iDestruct (own_valid with "H") as %HH%excl_auth_agree. done.
Qed.

Lemma excl_auth_upd `{!inG Σ (excl_authR (leibnizO A))} γ (x y z: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) ==∗
  own γ (◯E (z:leibnizO A)) ∗ own γ (●E (z:leibnizO A)).
Proof.
  iIntros "H1 H2".
  iDestruct (own_update_2 with "H1 H2") as ">[? ?]".
  1: by apply excl_auth_update. iModIntro. iFrame.
Qed.

Lemma excl_auth_alloc A `{inG Σ (excl_authR (leibnizO A))} (x: A):
  ⊢ |==> ∃ γ, own γ (◯E (x:leibnizO A)) ∗ own γ (●E (x:leibnizO A)).
Proof.
  iIntros.
  iMod (own_alloc (●E (x:leibnizO A) ⋅ ◯E (x:leibnizO A))) as (γ) "[? ?]".
  1: by apply excl_auth_valid. iModIntro. iExists _. iFrame.
Qed.
