From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Import basics basics_resources gctoken hybrid_ghost_heap roots.

Section UpdateLaws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperGCtokG Σ}.

Lemma ml_to_mut θ ℓ vs :
  ⊢ GC θ ∗ ℓ ↦∗ vs ==∗
    GC θ ∗ ∃ lvs γ, γ ↦mut (TagDefault, lvs) ∗ γ ~ℓ~ ℓ ∗ lvs ~~∗ vs.
Proof using.
  iIntros "(HGC & Hl)". iNamed "HGC".
  iDestruct (hgh_pointsto_has_lloc with "GCHGH Hl") as (γ) "#Hsim".
  iMod (hgh_ml_to_mut with "GCHGH Hl Hsim") as (lvs) "(GCHGH & Hγ & #Hblk)".
  iModIntro. iSplitR "Hγ".
  2: { iExists lvs, γ. iFrame "Hsim Hblk Hγ"; eauto. }
  rewrite /GC /named. repeat iExists _. iFrame; eauto.
Qed.

Lemma mut_to_ml γ vs lvs θ :
  ⊢ GC θ ∗ γ ↦mut (TagDefault, lvs) ∗ lvs ~~∗ vs ==∗
    GC θ ∗ ∃ ℓ, ℓ ↦∗ vs ∗ γ ~ℓ~ ℓ.
Proof using.
  iIntros "(HGC & Hl & #Hblk)". iNamed "HGC".
  iDestruct (lstore_own_vblock_M_as_mut with "Hl") as "([Hl _] & (%ℓ & #Hlℓ))".
  iMod (hgh_mut_to_ml with "GCHGH Hl Hlℓ Hblk") as "(HGH & Hℓ)".
  iModIntro. iSplitR "Hℓ"; last iExists ℓ; eauto.
  rewrite /GC /named. repeat iExists _. iFrame; eauto.
Qed.

Lemma freeze_to_mut γ lvs θ :
  ⊢ GC θ ∗ γ ↦fresh lvs ==∗
    GC θ ∗ γ ↦mut lvs.
Proof using.
  iIntros "(HGC & Hγ)". iNamed "HGC".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "([Hmtζ _] & Hmtfresh)".
  iMod (hgh_expose_lloc with "GCHGH Hmtfresh") as (ℓ) "(% & GCHGH & Hmtmut)".
  iModIntro. iSplitR "Hmtζ Hmtmut"; last by iFrame; eauto.
  rewrite /GC /named. repeat iExists _. iFrame; eauto.
Qed.

Lemma freeze_to_immut γ lvs θ :
  ⊢ GC θ ∗ γ ↦fresh lvs ==∗
    GC θ ∗ γ ↦imm lvs.
Proof using.
  iIntros "(HGC & Hγ)". iNamed "HGC".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "([Hmtζ _] & Hmtfresh)".
  assert (freeze_block (Bvblock (Mut, lvs)) (Bvblock (Immut, lvs))) as Hfreeze.
    { econstructor. }
  iMod (hgh_freeze_block _ _ _ _ _ _ Hfreeze with "GCHGH Hmtζ Hmtfresh") as "(GCHGH & Hmtζ & Hmtfresh)".
  iModIntro. iSplitR "Hmtζ Hmtfresh"; last by iFrame; eauto.
  rewrite /GC /named. repeat iExists _. iFrame; eauto.
Qed.

Lemma freeze_foreign_to_immut γ θ b :
  ⊢ GC θ ∗ γ ↦foreign[Mut] b ==∗
    GC θ ∗ γ ↦foreign[Immut] b.
Proof.
  iIntros "(HGC & [Hγ1 Hγ2])". iNamed "HGC".
  assert (freeze_block (Bforeign (Mut, Some b)) (Bforeign (Immut, Some b))) as Hfreeze.
    { econstructor. }
  iMod (hgh_freeze_block _ _ _ _ _ _ Hfreeze with "GCHGH Hγ1 Hγ2") as "(GCHGH & Hmtζ & Hmtfresh)".
  iModIntro. iSplitR "Hmtζ Hmtfresh"; last by iFrame; eauto.
  rewrite /GC /named. repeat iExists _. iFrame; eauto.
Qed.

Lemma update_root θ (l:loc) v E :
  GC θ ∗ l ↦roots v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
    (∀ v' w', l ↦C w' ∗ ⌜repr_lval θ v' w'⌝ ={E}=∗ GC θ ∗ l ↦roots v').
Proof using.
  iIntros "(HGC & Hroot)".
  iNamed "HGC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroot") as "%Hl".
  iDestruct (ROOTS_delete _ _ l with "GCROOTS") as (w) "(GCROOTS & Hpto & %Hrepr)"; first done.
  iExists _. iFrame "Hpto". iSplit; first done.
  iIntros (v' w') "(Hpto & %Hrepr')".
  iDestruct (ROOTS_insert with "GCROOTS Hpto") as "GCROOTS"; first done.
  rewrite insert_delete_insert.
  iMod (ghost_map_update with "GCrootsm Hroot") as "(GCrootsm&$)".
  iModIntro. rewrite /GC /named. repeat iExists _. iFrame.
  iPureIntro; split_and!; eauto.
  rewrite dom_insert_L. apply elem_of_dom_2 in Hl. set_solver.
Qed.

Lemma access_root θ (l:loc) dq v :
  GC θ ∗ l ↦roots{dq} v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
      (l ↦C w -∗ GC θ ∗ l ↦roots{dq} v).
Proof using.
  iIntros "(HGC & Hroot)". iNamed "HGC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroot") as "%Hl".
  iDestruct (ROOTS_delete _ _ l with "GCROOTS") as (w) "(GCROOTS & Hpto & %Hrepr)"; first done.
  iExists _. iFrame "Hpto Hroot". iSplit; first done.
  iIntros "Hpto".
  iDestruct (ROOTS_insert with "GCROOTS Hpto") as "GCROOTS"; first done.
  rewrite insert_delete// /GC /named. repeat iExists _. iFrame.
  iPureIntro; split_and!; eauto.
Qed.

End UpdateLaws.
