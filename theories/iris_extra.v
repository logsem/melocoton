From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import own.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

Section Extra.
Context `{SI: indexT}.
Context {Σ : gFunctors}.

Lemma big_sepM_of_pairs {A B} `{Countable A, Countable (A * B)} (m: gmap A B) (Φ : A → B → iProp Σ):
  ([∗ set] p ∈ map_to_set pair m, Φ p.1 p.2) -∗
  ([∗ map] k↦v ∈ m, Φ k v).
Proof.
  induction m using map_ind; first by eauto.
  iIntros "Hs". iApply big_sepM_insert; first done.
  rewrite map_to_set_insert_L//.
  iDestruct (big_sepS_insert with "Hs") as "($&Hs)".
  { intros ?%elem_of_map_to_set_pair. congruence. }
  iApply (IHm with "Hs").
Qed.

End Extra.
