From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import own ghost_var.
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

Lemma ghost_var_split_halves {A} {_: ghost_varG Σ A} γ (a: A) :
  ghost_var γ 1 a -∗ ghost_var γ (1/2) a ∗ ghost_var γ (1/2) a.
Proof.
  rewrite -{1}Qp.half_half.
  iIntros "H". iDestruct (ghost_var_split with "H") as "[$ $]".
Qed.

Lemma ghost_var_join_halves {A} {_: ghost_varG Σ A} γ (a b: A) :
  ghost_var γ (1/2) a -∗ ghost_var γ (1/2) b -∗ ghost_var γ 1 a ∗ ⌜a = b⌝.
Proof.
  iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %<-.
  iSplit; last done. rewrite -{3}Qp.half_half.
  iApply (fractional.fractional_merge _ _ (λ q, ghost_var γ q a) with "H1 H2").
Qed.

End Extra.
