From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var gen_heap.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props iris_extra.
From melocoton.interop Require Export basics basics_resources.
From melocoton.c_interface Require Import defs resources.

Section ROOTS.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_C Σ}.
Context `{!wrapperBasicsG Σ}.

Definition ROOTS (θ : addr_map) (roots_m : roots_map) : iProp Σ :=
  ∃ (memr: memory),
    "GCrootspto" ∷ ([∗ map] a↦w ∈ memr, a O↦C w)
  ∗ "%Hreprroots" ∷ ⌜repr_roots θ roots_m memr⌝
  (* NOTE: it does not seem necessary to include [roots_are_live] here,
     but at the same time, it is convenient to do so... *)
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝.

Lemma ROOTS_live θ roots_m :
  ROOTS θ roots_m -∗
  ⌜roots_are_live θ roots_m⌝.
Proof. by iNamed 1. Qed.

Lemma ROOTS_valid θ roots_m mem :
  ROOTS θ roots_m -∗
  gen_heap_interp mem -∗
  ⌜∃ privmem, repr_mem θ roots_m privmem mem⌝.
Proof.
  iNamed 1. iIntros "Hmem".
  iDestruct (gen_heap_valid_big with "Hmem GCrootspto") as %(privmem & -> & Hdisj).
  iPureIntro. do 2 eexists; split_and!; eauto.
Qed.

Lemma ROOTS_pto_notin θ roots_m a w :
  ROOTS θ roots_m -∗
  a ↦C w -∗
  ⌜a ∉ dom roots_m⌝.
Proof.
  iIntros "Hr Hpto %H". iNamed "Hr". apply elem_of_dom in H as [? H].
  edestruct repr_roots_lookup as (w' & ? & ?); eauto; simplify_eq.
  iDestruct (big_sepM_lookup with "GCrootspto") as "Hpto'"; first done.
  by iPoseProof (resources.mapsto_ne with "Hpto Hpto'") as "%HH".
Qed.

Lemma ROOTS_empty θ : ⊢ ROOTS θ ∅.
Proof.
  rewrite /ROOTS /named. iExists ∅. rewrite big_sepM_empty.
  iPureIntro; split_and!; eauto.
  - apply repr_roots_empty.
  - apply roots_are_live_empty.
Qed.

Lemma ROOTS_update_θ θ θ' roots_m privmem mem mem' :
  roots_are_live θ' roots_m →
  repr_mem θ roots_m privmem mem →
  repr_mem θ' roots_m privmem mem' →
  ROOTS θ roots_m -∗
  gen_heap_interp mem
  ==∗
  ROOTS θ' roots_m ∗
  gen_heap_interp mem'.
Proof.
  intros Hlive (memr & Hrepr & Hdisj & ->) (memr' & Hrepr' & Hdisj' & ->).
  iNamed 1. iIntros "Hmem".
  pose proof (repr_roots_inj_2 _ _ _ _ Hrepr Hreprroots) as <-.
  iMod (gen_heap_update_big memr memr' with "GCrootspto Hmem") as "[GCrootspto $]"; auto.
  { rewrite -(repr_roots_dom _ _ _ Hreprroots) -(repr_roots_dom _ _ _ Hrepr')//. }
  iModIntro. rewrite /ROOTS /named. iExists _. by iFrame.
Qed.

Lemma ROOTS_insert θ roots_m a lv w :
  repr_lval θ lv w →
  ROOTS θ roots_m -∗
  a O↦C (Storing w) -∗
  ROOTS θ (<[a := lv]> roots_m).
Proof.
  iIntros (Hrepr) "Hr Hpto". iDestruct (ROOTS_pto_notin with "Hr Hpto") as %Hdom.
  iNamed "Hr".
  iDestruct (big_sepM_insert with "[$GCrootspto $Hpto]") as "GCrootspto".
  { apply not_elem_of_dom. erewrite <- repr_roots_dom; eauto. }
  rewrite /ROOTS /named. iExists _. iFrame. iPureIntro. split.
  - eapply repr_roots_insert; eauto.
  - eapply roots_are_live_insert; eauto.
Qed.

Lemma ROOTS_delete θ roots_m a lv :
  roots_m !! a = Some lv →
  ROOTS θ roots_m -∗
  ∃ w, ROOTS θ (delete a roots_m) ∗ a O↦C (Storing w) ∗ ⌜repr_lval θ lv w⌝.
Proof.
  intros Hr. iNamed 1.
  edestruct repr_roots_lookup as (w & Hw & ?); eauto.
  iDestruct (big_sepM_delete with "GCrootspto") as "[Hpto Hptos]"; first done.
  iExists _.  iFrame "Hpto". iSplit; last done. rewrite /ROOTS /named.
  iExists _. iFrame. iPureIntro. split.
  - by eapply repr_roots_delete.
  - by eapply roots_are_live_delete.
Qed.

End ROOTS.
