From stdpp Require Import relations strings gmap.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import ofe.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

(** Classifying expressions into values and calls. *)

Inductive mixin_expr_class {val} :=
| ExprVal (v : val) : mixin_expr_class
| ExprCall (fn_name : string) (arg : list val) : mixin_expr_class.

(** Protocols *)

Notation protocol val Σ :=
  (string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ).

(* ⊥ *)
Global Instance protocol_bottom val Σ : Bottom (protocol val Σ) :=
  (λ _ _ _, False%I).

(* ⊤ *)
Global Instance protocol_top val Σ : Top (protocol val Σ) :=
  (λ _ _ _, True%I).

(* Protocol subsumption. Ψ1 ⊑ Ψ2 means intuitively that
   Ψ1 is less permissive than Ψ2. *)
Definition proto_refines {val Σ} (Ψ1 Ψ2 : protocol val Σ) :=
  ∀ s vs Φ, Ψ1 s vs Φ -∗ Ψ2 s vs Φ.

Global Instance proto_refines_sqsubseteq val Σ : SqSubsetEq (protocol val Σ) :=
  proto_refines.

Lemma proto_refines_bot_l val Σ (Ψ : protocol val Σ) : ⊥ ⊑ Ψ.
Proof. by iIntros (? ? ?) "?". Qed.
Lemma proto_refines_top_r val Σ (Ψ : protocol val Σ) : Ψ ⊑ ⊤.
Proof. by iIntros (? ? ?) "?". Qed.

Global Instance proto_refines_reflexive val Σ :
  Reflexive (sqsubseteq : relation (protocol val Σ)).
Proof. by iIntros (Ψ ? ? ?). Qed.

Global Instance proto_refines_transitive val Σ :
  Transitive (sqsubseteq : relation (protocol val Σ)).
Proof.
  iIntros (Ψ Ψ' Ψ'' H1 H2 ? ? ?) "H".
  iApply H2. iApply H1. done.
Qed.

(* Restricting a protocol by excluding a set of function names. *)
Definition proto_except {val Σ}
  (Ψ : protocol val Σ) (except : gset string) : protocol val Σ
:=
  (λ s vs Φ, ⌜s ∉ except⌝ ∗ Ψ s vs Φ)%I.

Notation "Ψ 'except' fns" := (proto_except Ψ fns) (at level 10).

Lemma proto_except_refines val Σ (Ψ : protocol val Σ) (fns : gset string) :
  Ψ except fns ⊑ Ψ.
Proof. by iIntros (? ? ?) "[_ H]". Qed.

(* Restricting a protocol on a set of function names. *)
Definition proto_on {val Σ}
  (Ψ : protocol val Σ) (on : gset string) : protocol val Σ
:=
  (λ s vs Φ, ⌜s ∈ on⌝ ∗ Ψ s vs Φ)%I.

Notation "Ψ 'on' fns" := (proto_on Ψ fns) (at level 10).

Lemma proto_on_refines val Σ (Ψ : protocol val Σ) (fns : gset string) :
  Ψ on fns ⊑ Ψ.
Proof. by iIntros (? ? ?) "[_ H]". Qed.

(* We can also define a meet and join operation on protocols. *)

(* "Meet" operation on protocols. *)
Definition proto_meet {val Σ} (Ψ1 Ψ2 : protocol val Σ) : protocol val Σ :=
  (λ s vs Φ, Ψ1 s vs Φ ∧ Ψ2 s vs Φ)%I.

Global Instance proto_meet_meet val Σ : Meet (protocol val Σ) :=
  proto_meet.

Lemma proto_refines_meet_l val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊓ Ψ2 ⊑ Ψ1.
Proof. iIntros (? ? ?) "H". by iApply bi.and_elim_l. Qed.

Lemma proto_refines_meet_r val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊓ Ψ2 ⊑ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.and_elim_r. Qed.

(* "Join" operation en protocols. *)
Definition proto_join {val Σ} (Ψ1 Ψ2 : protocol val Σ) : protocol val Σ :=
  (λ s vs Φ, Ψ1 s vs Φ ∨ Ψ2 s vs Φ)%I.

Global Instance proto_join_join val Σ : Join (protocol val Σ) :=
  proto_join.

Lemma proto_refines_join_l val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊑ Ψ1 ⊔ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.or_intro_l. Qed.

Lemma proto_refines_join_r val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ2 ⊑ Ψ1 ⊔ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.or_intro_r. Qed.

Lemma proto_join_mono val Σ (Ψ1 Ψ1' Ψ2 Ψ2' : protocol val Σ) :
  Ψ1 ⊑ Ψ1' → Ψ2 ⊑ Ψ2' → Ψ1 ⊔ Ψ2 ⊑ Ψ1' ⊔ Ψ2'.
Proof.
  iIntros (Hre1 Hre2 ? ? ?) "H".
  iApply (bi.or_elim with "H"); iIntros "H".
  { iApply bi.or_intro_l. by iApply Hre1. }
  { iApply bi.or_intro_r. by iApply Hre2. }
Qed.
