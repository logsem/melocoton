From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import state lang.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.ml_toy_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import basics basics_resources weakestpre wp_block_sim.
Import Wrap.

Section UpdateLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Context (σ : Wrap.state).

Lemma ml_to_mut θ l vs: ⊢ (GC θ ∗ l ↦∗ vs ==∗ GC θ ∗ ∃ b γ, γ ↦mut (TagDefault,b) ∗ block_sim_raw l γ ∗ block_sim_arr vs b)%I.
Proof.
  iIntros "(HGC & Hl)". iNamed "HGC".
  iDestruct (gen_heap_valid with "GCσMLv Hl") as %Hlσ.
  edestruct is_store_blocks_has_loc as (ll & Hlχ & Hllζ);
    [apply Hstore_blocks|apply Hlσ|..].
  iMod (gen_heap_update _ _ _ None with "GCσMLv Hl") as "[GCσMLv Hl]".
  apply elem_of_dom in Hllζ. destruct Hllζ as [bb Hζσll].
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. by apply lookup_union_Some_l. }
  unfold is_store in Hstore.
  specialize (Hstore l vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: by iApply (block_sim_arr_of_ghost_state with "GCχvirt GCζvirt").
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: by iApply (lloc_own_auth_get_pub with "GCχvirt").
  iMod (lstore_own_insert _ _ ll (Bvblock (Mut, _)) with "GCζvirt") as "(GCζvirt & Hzz)".
  1: { eapply map_disjoint_Some_l; done. }
  iDestruct (lstore_own_elem_to_mut with "Hzz") as "Hzz"; first done.
  iModIntro.
  assert (ζvirt !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iSplitR "Hzz".
  { rewrite /GC /named.
    iExists ζ, ζfreeze, (delete ll ζσ), (<[ll:=(Bvblock (Mut, (TagDefault, lvs)))]> ζvirt).
    iExists χ, χvirt, (<[l:=None]> σMLvirt), roots_s, roots_m. iFrame.
    iSplitL "GCσdom".
    { iApply (dom_auth_dom with "GCσdom").
      rewrite dom_insert_L. eapply elem_of_dom_2 in Hlσ. set_solver. }
    iSplit.
    { rewrite (pub_locs_in_lstore_insert_lstore_pub _ _ _ l) //.
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
  { iExists lvs, ll. eauto. }
Qed.

Lemma mut_to_ml γ vs b θ: ⊢ (GC θ ∗ γ ↦mut (TagDefault,b) ∗ block_sim_arr vs b ==∗ GC θ ∗ ∃ l, l ↦∗ vs ∗ block_sim_raw l γ)%I.
Proof.
  iIntros "(HGC & (Hl & (%ℓ & #Hlℓ)) & #Hsim)". iNamed "HGC".
  iDestruct (block_sim_arr_to_ghost_state with "GCχvirt GCζvirt [] [] [] [] Hsim") as %Hsim.
  1-4: iPureIntro; done.
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
    iExists ζ, ζfreeze, (<[γ:=(Bvblock (Mut, (TagDefault, b)))]> ζσ), (delete γ ζvirt).
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

Lemma freeze_to_mut γ bb θ: ⊢ (GC θ ∗ γ ↦fresh bb ==∗ GC θ ∗ γ ↦mut bb)%I.
Proof.
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
  iModIntro. iSplitR "Hℓγ Hmtζ"; last by eauto.
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

Lemma freeze_to_immut γ bb θ: ⊢ (GC θ ∗ γ ↦fresh bb ==∗ GC θ ∗ γ ↦imm bb)%I.
Proof.
  iIntros "(HGC & (Hmtζ & Hmtfresh))". iNamed "HGC".
  iDestruct (lstore_own_mut_of with "GCζvirt Hmtζ") as %[Hζγ _].
  iDestruct (lloc_own_priv_of with "GCχvirt Hmtfresh") as %Hχvirtγ.
  iMod (lstore_own_update _ _ _ _ (Bvblock (Immut,bb)) with "GCζvirt Hmtζ") as "(GCζvirt & Hmtζ)".
  iDestruct (lstore_own_elem_to_immut with "Hmtζ") as "Hmtζ"; first done.
  iModIntro. iFrame "Hmtζ". rewrite /GC /named.
  iExists ζ, (<[γ:=(Bvblock (Immut, bb))]> ζfreeze), ζσ, (<[γ:=(Bvblock (Immut, bb))]> ζvirt).
  iExists χ, χvirt, σMLvirt, roots_s, roots_m. iFrame.
  assert (Hζγ': ζfreeze !! γ = Some (Bvblock (Mut, bb))).
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

End UpdateLaws.
