From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Import basics basics_resources gctoken.

Section UpdateLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGCtokGS Σ}.

Lemma ml_to_mut θ ℓ vs :
  ⊢ GC θ ∗ ℓ ↦∗ vs ==∗
    GC θ ∗ ∃ lvs γ, γ ↦mut (TagDefault, lvs) ∗ γ ~ℓ~ ℓ ∗ lvs ~~∗ vs.
Proof using.
  iIntros "(HGC & Hl)". iNamed "HGC".
  iDestruct (gen_heap_valid with "GCσMLv Hl") as %Hlσ.
  edestruct is_store_blocks_has_loc as (ll & Hlχ & Hllζ);
    [apply Hstore_blocks|apply Hlσ|..].
  iMod (gen_heap_update _ _ _ None with "GCσMLv Hl") as "[GCσMLv Hl]".
  apply elem_of_dom in Hllζ. destruct Hllζ as [bb Hζσll].
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. by apply lookup_union_Some_l. }
  unfold is_store in Hstore.
  specialize (Hstore ℓ vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: by iApply (block_sim_arr_of_auth with "GCχvirt GCζvirt").
  iAssert (ll ~ℓ~ ℓ) as "#Hraw".
  1: by iApply (lloc_own_auth_get_pub with "GCχvirt").
  iMod (lstore_own_insert _ ll (Bvblock (Mut, _)) with "GCζvirt") as "(GCζvirt & Hzz)".
  1: { eapply map_disjoint_Some_l; done. }
  iDestruct (lstore_own_elem_to_mut with "Hzz") as "Hzz"; first done.
  iModIntro.
  assert (ζvirt !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iSplitR "Hzz".
  { rewrite /GC /named.
    iExists ζ, ζfreeze, (delete ll ζσ), (<[ll:=(Bvblock (Mut, (TagDefault, lvs)))]> ζvirt).
    iExists χ, χvirt, (<[ℓ:=None]> σMLvirt), roots_s, roots_m. iFrame.
    iSplitL "GCσdom".
    { iApply (dom_auth_dom with "GCσdom").
      rewrite dom_insert_L. eapply elem_of_dom_2 in Hlσ. set_solver. }
    iSplit.
    { rewrite (pub_locs_in_lstore_insert_lstore_pub _ _ _ ℓ) //.
      iApply big_sepM_insert; eauto. by iFrame. }
    iPureIntro. split_and!; eauto.
    - symmetry. subst. by apply union_delete_insert.
    - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
      apply map_disjoint_delete_l. done.
    - eapply is_store_blocks_discard_loc; eauto.
    - intros γ [bl [[<-  <- ]|[? ?]]%lookup_insert_Some]%elem_of_dom.
      1: by eapply elem_of_dom_2.
      apply Hother_blocks; by eapply elem_of_dom_2.
    - eapply is_store_discard_loc; eauto. }
  { iExists lvs, ll. iFrame "Hraw Hblock ∗". eauto. }
Qed.

Lemma mut_to_ml γ vs lvs θ :
  ⊢ GC θ ∗ γ ↦mut (TagDefault, lvs) ∗ lvs ~~∗ vs ==∗
    GC θ ∗ ∃ ℓ, ℓ ↦∗ vs ∗ γ ~ℓ~ ℓ.
Proof using.
  iIntros "(HGC & (Hl & (%ℓ & #Hlℓ)) & #Hsim)". iNamed "HGC".
  iDestruct (block_sim_arr_auth_is_val with "GCχvirt GCζvirt Hsim") as %Hsim;
    try done.
  iPoseProof (lloc_own_pub_of with "GCχvirt Hlℓ") as "%Hχℓ".
  unfold is_store in Hstore.
  iDestruct (lstore_own_mut_of with "GCζvirt Hl") as %[Hζl _].
  iDestruct (big_sepM_delete _ _ _ ℓ with "GCχNone") as "[Hℓ GCχNone]".
  { eapply map_filter_lookup_Some. rewrite lloc_map_pubs_lookup_Some.
    split; eauto. by eapply elem_of_dom_2. }
  iDestruct (gen_heap_valid with "GCσMLv Hℓ") as "%Hlσ".
  iMod (gen_heap_update _ _ _ (Some vs) with "GCσMLv Hℓ") as "[GCσMLv Hℓ]".
  iMod (lstore_own_delete with "GCζvirt Hl") as "GCζvirt".
  iModIntro. iSplitR "Hℓ".
  { rewrite /GC /named.
    iExists ζ, ζfreeze, (<[γ:=(Bvblock (Mut, (TagDefault, lvs)))]> ζσ), (delete γ ζvirt).
    iExists χ, χvirt, (<[ℓ := Some vs]> σMLvirt), roots_s, roots_m. iFrame.
    iSplitL "GCσdom".
    { iApply (dom_auth_dom with "GCσdom").
      rewrite dom_insert_L; eapply elem_of_dom_2 in Hlσ; set_solver. }
    iSplit; first by rewrite pub_locs_in_lstore_delete_lstore //.
    iPureIntro; split_and!; eauto.
  + erewrite (union_insert_delete ζσ ζvirt). 2: eapply map_disjoint_Some_r. all: eauto.
  + apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    apply map_disjoint_delete_r. done.
  + eapply is_store_blocks_restore_loc; eauto.
  + intros γ' [blk [Hne Hblk]%lookup_delete_Some]%elem_of_dom. eapply Hother_blocks.
    by eapply elem_of_dom_2.
  + eapply is_store_restore_loc; eauto.
    { rewrite Hfreezeeq. eapply lookup_union_Some_r; eauto. }
    by constructor. }
  { iExists _. eauto. }
Qed.

Lemma freeze_to_mut γ lvs θ :
  ⊢ GC θ ∗ γ ↦fresh lvs ==∗
    GC θ ∗ γ ↦mut lvs.
Proof using.
  iIntros "(HGC & (Hmtζ & Hmtfresh))". iNamed "HGC".
  iDestruct (lstore_own_mut_of with "GCζvirt Hmtζ") as %[Hζγ _].
  pose (fresh_locs (lloc_map_pub_locs χvirt)) as ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χvirt).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χvirt) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σMLvirt).
  { intros Hℓ. destruct Hstore_blocks as [H1 _].
    destruct (H1 _ Hℓ) as (γ'&Hγ'). by apply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  iDestruct (lloc_own_priv_of with "GCχvirt Hmtfresh") as %Hχvirtγ.
  iMod (lloc_own_expose with "GCχvirt Hmtfresh") as "[GCχvirt #Hℓγ]".
  iMod (gen_heap_alloc _ ℓ None with "GCσMLv") as "(GCσMLv & HℓNone & Hmeta)".
  1: by eapply not_elem_of_dom_1.
  iPoseProof (big_sepM_insert _ _ γ ℓ with "[$GCχNone $HℓNone]") as "GCχNone".
  { eapply map_filter_lookup_None. left. eapply lloc_map_pubs_lookup_None; eauto. }
  iMod (dom_auth_extend _ (<[ ℓ := None ]> σMLvirt) with "GCσdom []") as "GCσdom".
  1: iPureIntro; rewrite dom_insert_L; set_solver.
  iModIntro. iSplitR "Hℓγ Hmtζ".
  2: { iFrame "Hmtζ". eauto. }
  rewrite /GC /named.
  iExists ζ, ζfreeze, ζσ, ζvirt.
  iExists χ, (<[γ:=LlocPublic ℓ]> χvirt), (<[ℓ:=None]> σMLvirt), roots_s, roots_m.
  iFrame. iSplit.
  { rewrite pub_locs_in_lstore_insert_pub //. by eapply elem_of_dom_2. }
  iPureIntro; split_and!; eauto.
  + eapply is_store_blocks_expose_lloc; eauto.
  + intros γ' Hγ'. rewrite dom_insert_L. eapply elem_of_union; right.
    by apply Hother_blocks.
  + eapply is_store_expose_lloc; eauto.
  + eapply expose_llocs_trans; first eassumption.
    eapply expose_llocs_insert; eauto.
Qed.

Lemma freeze_to_immut γ lvs θ :
  ⊢ GC θ ∗ γ ↦fresh lvs ==∗
    GC θ ∗ γ ↦imm lvs.
Proof using.
  iIntros "(HGC & (Hmtζ & Hmtfresh))". iNamed "HGC".
  iDestruct (lstore_own_mut_of with "GCζvirt Hmtζ") as %[Hζγ _].
  iDestruct (lloc_own_priv_of with "GCχvirt Hmtfresh") as %Hχvirtγ.
  iMod (lstore_own_update _ _ _ (Bvblock (Immut, lvs)) with "GCζvirt Hmtζ") as "(GCζvirt & Hmtζ)".
  iDestruct (lstore_own_elem_to_immut with "Hmtζ") as "Hmtζ"; first done.
  iModIntro. iFrame "Hmtζ". rewrite /GC /named.
  iExists ζ, (<[γ:=(Bvblock (Immut, lvs))]> ζfreeze), ζσ, (<[γ:=(Bvblock (Immut, lvs))]> ζvirt).
  iExists χ, χvirt, σMLvirt, roots_s, roots_m. iFrame.
  assert (Hζγ': ζfreeze !! γ = Some (Bvblock (Mut, lvs))).
  { subst. rewrite lookup_union_r; eauto. by eapply map_disjoint_Some_l. }
  iSplit.
  { rewrite pub_locs_in_lstore_insert_existing; eauto. by eapply elem_of_dom_2. }
  iPureIntro; split_and!; eauto.
  + eapply freeze_lstore_freeze_lloc; eauto.
  + subst. rewrite insert_union_r. 1: done. eapply map_disjoint_Some_l; done.
  + apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  + intros γ' [bl [[<-  <- ]|[? ?]]%lookup_insert_Some]%elem_of_dom.
      1: by eapply elem_of_dom_2.
      apply Hother_blocks; by eapply elem_of_dom_2.
  + eapply is_store_freeze_lloc; eauto.
  + eapply GC_correct_freeze_lloc; eauto.
Qed.

Lemma update_root θ (l:loc) v E :
  GC θ ∗ l ↦roots v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
    (∀ v' w', l ↦C w' ∗ ⌜repr_lval θ v' w'⌝ ={E}=∗ GC θ ∗ l ↦roots v').
Proof using.
  iIntros "(HGC & Hroots)".
  iNamed "HGC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroots") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iExists _. iFrame "Hown". iSplit; first done. iIntros (v' w') "(Hown' & %Hrepr')".
  iMod (ghost_map_update with "GCrootsm Hroots") as "(GCrootsm&Hroots)".
  iModIntro. iFrame "Hroots". do 9 iExists _; rewrite /named. iFrame.
  rewrite dom_insert_lookup_L; last done.
  iSplit.
  { iPoseProof (big_sepM_insert_delete) as "(_&HR)"; iApply "HR"; iClear "HR".
    iFrame. iExists _. by iFrame. }
  { iPureIntro; split_and!; eauto.
    intros l' γ [[-> ->]|[Hne HH]]%lookup_insert_Some.
    2: by eapply Hrootslive.
    inv_repr_lval. by eapply elem_of_dom_2. }
Qed.

Lemma access_root θ (l:loc) dq v :
  GC θ ∗ l ↦roots{dq} v -∗
  ∃ w, l ↦C w ∗ ⌜repr_lval θ v w⌝ ∗
      (l ↦C w -∗ GC θ ∗ l ↦roots{dq} v).
Proof using.
  iIntros "(HGC & Hroot)". iNamed "HGC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroot") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&HR)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iExists _. iFrame "Hown". iSplit; first done. iIntros "Hown". iFrame "Hroot".
  rewrite /GC /named. do 9 iExists _.
  iPoseProof ("HR" with "[Hown Hrp]") as "Hrootsm"; iClear "HR".
  { iFrame. iExists w; by iFrame. }
  iFrame. eauto.
Qed.

End UpdateLaws.
