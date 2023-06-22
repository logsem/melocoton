From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props stdpp_extra.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Import basics basics_resources gctoken.

Section UpdateLaws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperGCtokG Σ}.

Lemma GC_make_dirty θ dirty dirty' :
  dirty ⊆ dirty' →
  GC θ dirty ⊢ GC θ dirty'.
Proof.
  iIntros (Hd) "H". iNamed "H".
  do 5 iExists _. iFrame "GCζ GCχ GCθ GCroots GCinit HSI_GC".
  iSplit; last done.
  iNamed "HSI_block_level".
  iExists _; iFrame "GCχauth GCζauth GCσMLv".
  repeat iSplit; try done.
  iApply GC_per_loc_make_dirty; done.
Qed.

Lemma ml_to_mut θ dirty ℓ vs :
  ⊢ GC θ dirty ∗ ℓ ↦∗ vs ==∗
    ∃ lvs γ, GC θ (dirty ∖ {[γ]}) ∗ γ ↦mut (TagDefault, lvs) ∗ γ ~ℓ~ ℓ ∗ lvs ~~∗ vs.
Proof using.
  iIntros "(HGC & Hl)". iNamed "HGC". iNamed "HSI_block_level".
  iDestruct (gen_heap_valid with "GCσMLv Hl") as %Hlσ.
  destruct (Hstore ℓ) as (γ & Hχγ%lloc_map_pubs_lookup_Some); first by eapply elem_of_dom_2.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "GC_per_loc") as "((%vs'&%tg&%lvs&[(Hℓ&_)|[(%Hℓσ&Hγ&#Hsim&->)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&->&%Hsum)|[(%Hne1&%Hne2)|(%Hne1&%Hne2)]]]])&GC_per_loc)".
  1: by iPoseProof (gen_heap.mapsto_ne with "Hl Hℓ") as "%Hbot".
  3: by simplify_eq.
  3: by simplify_eq.
  2: { iPoseProof (gen_heap.mapsto_ne with "Hl Hmapsℓ") as "%Hf". done. }
  simplify_eq.
  iMod (gen_heap_update _ _ _ None with "GCσMLv Hl") as "[GCσMLv Hl]".
  iDestruct "Hγ" as "(Hγ1&(%ℓ'&#Hγ2))".
  iPoseProof (lstore_own_elem_of with "GCζauth Hγ1") as "%Hγζ".
  iPoseProof (GC_per_loc_modify_σ with "GC_per_loc") as "GC_per_loc".
  1: by eapply lloc_map_pubs_inj, expose_llocs_inj. 1: done.
  iPoseProof (GC_per_loc_remove_dirty with "GC_per_loc") as "GC_per_loc".
  1: eapply lookup_delete.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "[$GC_per_loc Hl]") as "GC_per_loc".
  { iExists vs, TagDefault, lvs. iLeft. by iFrame. }
  iPoseProof (lloc_own_pub_of with "GCχauth Hγ2") as "%Hγℓ".
  apply lloc_map_pubs_lookup_Some in Hγℓ; simplify_eq.
  iModIntro.
  iExists _, _. iFrame "Hγ1 Hsim Hγ2".
  iSplitR "Hγ2"; last by iExists _.
  rewrite /GC /SI_block_level /named.
  iExists ζ, ζ_future, χ, χ_future, roots_s. iFrame "GCζ GCχ GCθ GCroots GCinit GCχauth HSI_GC". iSplit; last done.
  iExists (<[ℓ:=None]> σMLvirt). iFrame.
  iPureIntro. split_and!; try done.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma mut_to_ml γ vs lvs θ dirty :
  ⊢ GC θ dirty ∗ γ ↦mut (TagDefault, lvs) ∗ lvs ~~∗ vs ==∗
    GC θ (dirty ∖ {[γ]}) ∗ ∃ ℓ, ℓ ↦∗ vs ∗ γ ~ℓ~ ℓ.
Proof using.
  iIntros "(HGC & Hl & #Hsim)".
  iDestruct (lstore_own_vblock_M_as_mut with "Hl") as "(Hl & (%ℓ & #Hlℓ))".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lstore_own_mut_of with "GCζauth Hl") as "(%Hγζ&#_)".
  iPoseProof (lloc_own_pub_of with "GCχauth Hlℓ") as "%Hχγ".
  apply lloc_map_pubs_lookup_Some in Hχγ.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "GC_per_loc") as "((%vs'&%tg&%lvs'&[(Hℓ&%Hγζ')|[(%Hℓσ&(Hγ&_)&_)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsimm&->&%Hsum)|[(%Hne1&%Hne2)|(Hne1&%Hne2)]]]])&GC_per_loc)".
  2: iDestruct "Hl" as "(Hl&_)"; by iPoseProof (ghost_map_elem_ne with "Hl Hγ") as "%Hne".
  3: simplify_eq.
  3: simplify_eq.
  2: { iDestruct "Hl" as "(Hl&_)". iDestruct "Hmapsγ" as "(Hmapsγ&_)".
       iPoseProof (ghost_map_elem_ne with "Hl Hmapsγ") as "%Hf". done. }
  iDestruct (gen_heap_valid with "GCσMLv Hℓ") as %Hℓσ.
  iMod (gen_heap_update _ _ _ (Some vs) with "GCσMLv Hℓ") as "[GCσMLv Hℓ]".
  iPoseProof (GC_per_loc_modify_σ with "GC_per_loc") as "GC_per_loc".
  1: by eapply lloc_map_pubs_inj, expose_llocs_inj. 1: done.
  iPoseProof (GC_per_loc_remove_dirty with "GC_per_loc") as "GC_per_loc".
  1: eapply lookup_delete.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "[$GC_per_loc Hl]") as "GC_per_loc".
  { iExists vs, TagDefault, lvs. iRight; iLeft. rewrite lookup_insert. repeat iSplit; try done.
    1: by iApply lstore_own_mut_to_elem. by iExists _. }
  iModIntro.
  iSplitR "Hℓ".
  2: iExists _; iFrame "Hℓ Hlℓ".
  rewrite /GC /SI_block_level /named.
  iExists ζ, ζ_future, χ, χ_future, roots_s. iFrame. iSplit; last done.
  iExists (<[ℓ:=_]> σMLvirt). iFrame.
  iPureIntro. split_and!; try done.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma freeze_to_mut γ lvs θ dirty :
  ⊢ GC θ dirty ∗ γ ↦fresh lvs ==∗
    GC θ dirty ∗ γ ↦mut lvs.
Proof using.
  iIntros "(HGC & Hγ)".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "(Hmtζ & Hmtfresh)".
  iNamed "HGC". iNamed "HSI_block_level".
  iDestruct (lstore_own_mut_of with "GCζauth Hmtζ") as %[Hζγ _].
  pose (fresh_locs (lloc_map_pub_locs χ_future)) as ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χ_future).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χ_future) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σMLvirt).
  { intros Hℓ.
    destruct (Hstore _ Hℓ) as (γ'&Hγ'). by apply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  iDestruct (lloc_own_priv_of with "GCχauth Hmtfresh") as %Hχγ.
  iMod (lloc_own_expose _ _ ℓ with "GCχauth Hmtfresh") as "[GCχvirt #Hℓγ]".
  iMod (gen_heap_alloc _ ℓ None with "GCσMLv") as "(GCσMLv & HℓNone & Hmeta)".
  1: by eapply not_elem_of_dom_1.
  destruct lvs as [tg lvs].
  iPoseProof (GC_per_loc_insert _ _ _ _ ℓ with "GC_per_loc") as "GC_per_loc".
  1: { intros γ' Hγ'%lloc_map_pubs_lookup_Some. apply elem_of_lloc_map_pub_locs_1 in Hγ'. apply H, Hγ'. }
  iPoseProof (big_sepM_insert _ _ γ ℓ with "[$GC_per_loc HℓNone]") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; eauto.
  1: iExists nil, tg, lvs; iLeft; by iFrame.
  iModIntro. iSplitR "Hℓγ Hmtζ".
  2: { iApply lstore_own_vblock_M_as_mut. iFrame "Hmtζ". eauto. }
  rewrite /GC /SI_block_level /named.
  iExists ζ, ζ_future, χ, (<[γ:=LlocPublic ℓ]> χ_future), roots_s.
  iFrame "GCζ GCχ GCθ GCroots GCinit GCχvirt HSI_GC". iSplit; last first.
  { iSplit; first done.
    iPureIntro. eapply expose_llocs_trans; first eassumption.
    eapply expose_llocs_insert; eauto. }
  iExists (<[ℓ:=None]> σMLvirt). rewrite lloc_map_pubs_insert_pub.
  iFrame. iPureIntro; split_and!; eauto.
  + rewrite dom_insert. set_solver.
  + intros ℓ'. rewrite !dom_insert_L elem_of_union elem_of_singleton.
    intros [<-|Hℓ']. 1: by exists γ; simplify_map_eq.
    specialize (Hstore _ Hℓ') as (γ'&?). exists γ'.
    rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma freeze_to_immut γ lvs θ dirty :
  ⊢ GC θ dirty ∗ γ ↦fresh lvs ==∗
    GC θ dirty ∗ γ ↦imm lvs.
Proof using.
  iIntros "(HGC & Hγ)".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "(Hmtζ & Hmtfresh)".
  iNamed "HGC". iNamed "HSI_block_level". iNamed "HSI_GC".
  iDestruct (lstore_own_mut_of with "GCζauth Hmtζ") as %[Hζγ _].
  iDestruct (lloc_own_priv_of with "GCχauth Hmtfresh") as %Hχγ.
  iMod (lstore_own_update _ _ _ (Bvblock (Immut, lvs)) with "GCζauth Hmtζ") as "(GCζauth & Hmtζ)".
  iDestruct (lstore_own_elem_to_immut with "Hmtζ") as "Hmtζ"; first done.
  iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; right; left; eapply Hχγ.
  iModIntro.
  iSplitR "Hmtζ"; last by iApply lstore_own_vblock_I_as_imm.
  rewrite /GC /SI_block_level /SI_GC /named.
  iExists ζ, (<[γ:=(Bvblock (Immut, lvs))]> ζ_future), χ, χ_future, roots_s.
  iFrame "GCζ GCχ GCθ GCroots GCinit GCχauth GCζauth".
  iSplitL "GCσMLv GC_per_loc".
  { iExists σMLvirt.
    iFrame; iPureIntro; split_and!; eauto. by rewrite dom_insert_lookup_L. }
  iSplit.
  { iExists roots_m. iFrame. iPureIntro; split_and!; eauto.
    eapply GC_correct_freeze_lloc; eauto. }
  iPureIntro; split_and; eauto.
  eapply freeze_lstore_freeze_lloc; eauto.
Qed.

Lemma update_root θ dirty (l:loc) v E :
  GC θ dirty ∗ l ↦roots v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
    (∀ v' w', l ↦C w' ∗ ⌜repr_lval θ v' w'⌝ ={E}=∗ GC θ dirty ∗ l ↦roots v').
Proof using.
  iIntros "(HGC & Hroots)".
  iNamed "HGC". iNamed "HSI_GC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroots") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iExists _. iFrame "Hown". iSplit; first done. iIntros (v' w') "(Hown' & %Hrepr')".
  iMod (ghost_map_update with "GCrootsm Hroots") as "(GCrootsm&Hroots)".
  iModIntro. iFrame "Hroots". do 5 iExists _. iFrame.
  iSplit; last done.
  rewrite /SI_GC /named. iExists _. iFrame. rewrite dom_insert_lookup_L; last done.
  iSplit.
  { iPoseProof (big_sepM_insert_delete) as "(_&HR)"; iApply "HR"; iClear "HR";
    iFrame; iExists _; by iFrame. }
  { iPureIntro; split_and!; eauto.
    intros l' γ [[-> ->]|[Hne HH]]%lookup_insert_Some.
    2: by eapply Hrootslive.
    inv_repr_lval. by eapply elem_of_dom_2. }
Qed.

Lemma access_root θ dirty (l:loc) dq v :
  GC θ dirty ∗ l ↦roots{dq} v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
      (l ↦C w -∗ GC θ dirty ∗ l ↦roots{dq} v).
Proof using.
  iIntros "(HGC & Hroot)".
  iNamed "HGC". iNamed "HSI_GC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroot") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&HR)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iExists _. iFrame "Hown". iSplit; first done. iIntros "Hown". iFrame "Hroot".
  do 5 iExists _. iFrame.
  iSplit; last done.
  rewrite /SI_GC /named. iExists _. iFrame "GCrootsm".
  rewrite /GC /named.
  iPoseProof ("HR" with "[Hown Hrp]") as "Hrootsm"; iClear "HR".
  { iFrame. iExists w; by iFrame. }
  iFrame. eauto.
Qed.

Lemma lloc_own_pub_inj θ dirty γ1 γ2 ℓ1 ℓ2 :
    γ1 ~ℓ~ ℓ1
 -∗ γ2 ~ℓ~ ℓ2
 -∗ GC θ dirty
 -∗ GC θ dirty ∗ ⌜γ1 = γ2 ↔ ℓ1 = ℓ2⌝.
Proof.
  iIntros "#Hsim1 #Hsim2 HGC". iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lloc_own_pub_of with "[$] Hsim1") as "%HH1".
  iPoseProof (lloc_own_pub_of with "[$] Hsim2") as "%HH2".
  iSplit.
  1: (repeat iExists _; iFrame; try done; iSplit; first repeat iExists _; iFrame; done).
  iPureIntro; split; intros ->.
  - by simplify_eq.
  - apply expose_llocs_inj in Hχfuture.
    by eapply Hχfuture.
Qed.

Lemma lloc_own_foreign_inj θ dirty γ1 γ2 fid1 fid2 :
    γ1 ~foreign~ fid1
 -∗ γ2 ~foreign~ fid2
 -∗ GC θ dirty
 -∗ GC θ dirty ∗ ⌜γ1 = γ2 ↔ fid1 = fid2⌝.
Proof.
  iIntros "#Hsim1 #Hsim2 HGC". iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lloc_own_foreign_of with "[$] Hsim1") as "%HH1".
  iPoseProof (lloc_own_foreign_of with "[$] Hsim2") as "%HH2".
  iSplit.
  1: (repeat iExists _; iFrame; try done; iSplit; first repeat iExists _; iFrame; done).
  iPureIntro; split; intros ->.
  - by simplify_eq.
  - destruct Hχfuture as [_ [H _]]. by eapply H.
Qed.



End UpdateLaws.
