From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim.
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
Notation SI := (weakestpre.state_interp σ).

Lemma ml_to_mut θ l vs: ⊢ (GC θ ∗ l ↦∗ vs ∗ SI ==∗ SI ∗ GC θ ∗ ∃ b γ, γ ↦mut{DfracOwn 1} (TagDefault,b) ∗ block_sim_raw l γ ∗ block_sim_arr vs b)%I.
Proof.
  iIntros "(HGC & Hl & Hσ)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iDestruct (gen_heap_valid with "HAσMLv Hl") as %Hlσ.
  edestruct is_store_blocks_has_loc as (ll & Hlχ & Hllζ);
    [apply Hstore_blocks|apply Hlσ|..].
  iMod (gen_heap_update _ _ _ None with "HAσMLv Hl") as "[HAσMLv Hl]".
  apply elem_of_dom in Hllζ. destruct Hllζ as [bb Hζσll].
  iMod (ghost_map_insert _ bb with "HAζbl") as "(HAζbl & Hzz)".
  1: { eapply map_disjoint_Some_l; done. }
  iModIntro. iFrame "HGC".
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. by apply lookup_union_Some_l. }
  unfold is_store in Hstore.
  specialize (Hstore l vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: by iApply (block_sim_arr_of_ghost_state with "HAχvirt HAζpers").
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: by iApply (lloc_own_auth_get_pub with "HAχvirt").
  assert (ζrest !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iSplitR "Hzz". 1: iSplitL "HσC HnC".
  + iExists _. iFrame.
  + unfold C_state_interp, named. iExists (ζfreeze), (delete ll ζσ), (<[ll:=(Mut, (TagDefault, lvs))]> ζrest).
    iExists χvirt, (<[l:=None]> σMLvirt). iFrame.
    iSplitL "HAnMLv HAσdom".
    1: { iExists _; iFrame. iApply (dom_auth_dom with "HAσdom").
         rewrite dom_insert_L. eapply elem_of_dom_2 in Hlσ. set_solver. }
    iSplitL.
    { rewrite (pub_locs_in_lstore_insert_lstore_pub _ _ _ l) //.
      iApply big_sepM_insert; [| by iFrame].
      apply map_filter_lookup_None. right. intros ? ?%lloc_map_pubs_lookup_Some ?.
      simplify_map_eq. by apply not_elem_of_dom in HζllNone. }
    iSplitL.
    { rewrite lstore_immut_blocks_insert_mut //. }
    iPureIntro. split_and!.
    all: eauto.
    - symmetry. subst. by apply union_delete_insert.
    - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
      apply map_disjoint_delete_l. done.
    - eapply is_store_blocks_discard_loc; eauto.
    - eapply is_store_discard_loc; eauto.
  + iExists lvs, ll. cbn. iFrame. iFrame "Hblock Hraw".
    iExists _; iApply "Hraw".
Qed.

Lemma mut_to_ml γ vs b θ: ⊢ (SI ∗ GC θ ∗ γ ↦mut{DfracOwn 1} (TagDefault,b) ∗ block_sim_arr vs b ==∗ SI ∗ GC θ ∗ ∃ l, l ↦∗ vs ∗ block_sim_raw l γ)%I.
Proof.
  iIntros "(Hσ & HGC & (Hl & (%ℓ & #Hlℓ)) & #Hsim)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iPoseProof (block_sim_arr_to_ghost_state with "HAχvirt HAζbl [] [] [] [] Hsim ") as "%Hsim".
  1-4: iPureIntro; done.
  iPoseProof (lloc_own_pub_of with "HAχvirt Hlℓ") as "%Hχℓ".
  unfold is_store in Hstore.
  iPoseProof (ghost_map_lookup with "HAζbl Hl") as "%Hζl".
  iDestruct (big_sepM_delete _ _ _ ℓ with "HAχNone") as "[Hℓ HAχNone]".
  { eapply map_filter_lookup_Some. rewrite lloc_map_pubs_lookup_Some.
    split; eauto. by eapply elem_of_dom_2. }
  iDestruct (gen_heap_valid with "HAσMLv Hℓ") as "%Hlσ".
  iMod (gen_heap_update _ _ _ (Some vs) with "HAσMLv Hℓ") as "[HAσMLv Hℓ]".
  iMod (ghost_map_delete with "HAζbl Hl") as "HAζbl".
  iModIntro. iFrame "HGC". iSplitR "Hℓ". 2: iExists ℓ; iFrame; done.
  cbn. iSplitL "HσC HnC".
  1: iExists _; iFrame.
  unfold C_state_interp, named.
  iExists ζfreeze, (<[γ:=(Mut, (TagDefault, b))]>ζσ), (delete γ ζrest).
  iExists χvirt, (<[ ℓ := Some vs ]> σMLvirt).
  iFrame.
  iSplitL "HAnMLv HAσdom". 2: iSplitL. 3: iSplitL. 4: iPureIntro; split_and!; eauto.
  + iExists _; iFrame. iApply (dom_auth_dom with "HAσdom"); erewrite dom_insert_L; eapply elem_of_dom_2 in Hlσ; set_solver.
  + rewrite pub_locs_in_lstore_delete_lstore //.
  + rewrite /lstore_immut_blocks map_filter_delete_not //. naive_solver.
  + erewrite (union_insert_delete ζσ ζrest). 2: eapply map_disjoint_Some_r. all: eauto.
  + apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    apply map_disjoint_delete_r. done.
  + eapply is_store_blocks_restore_loc; eauto.
  + eapply is_store_restore_loc; eauto.
    { rewrite Hfreezeeq. eapply lookup_union_Some_r; eauto. }
    by constructor.
Qed.

Lemma freeze_to_mut γ bb θ: ⊢ (SI ∗ GC θ ∗ γ ↦fresh{DfracOwn 1} bb ==∗ SI ∗ GC θ ∗ γ ↦mut{DfracOwn 1} bb)%I.
Proof.
  iIntros "(Hσ & HGC & (Hmtζ & Hmtfresh))".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iPoseProof (ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  pose (fresh_locs (lloc_map_pub_locs χvirt)) as ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χvirt).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χvirt) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σMLvirt).
  { intros Hℓ. destruct Hstore_blocks as [H1 _].
    destruct (H1 _ Hℓ) as (γ'&Hγ'). by apply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  iDestruct (lloc_own_priv_of with "HAχvirt Hmtfresh") as %Hχvirtγ.
  iMod (lloc_own_expose with "HAχvirt Hmtfresh") as "[HAχvirt #Hℓγ]".
  iMod (gen_heap_alloc _ ℓ None with "HAσMLv") as "(HAσMLv & HℓNone & Hmeta)".
  1: by eapply not_elem_of_dom_1.
  iPoseProof (big_sepM_insert _ _ γ ℓ with "[$HAχNone $HℓNone]") as "HAχNone".
  { eapply map_filter_lookup_None. left. eapply lloc_map_pubs_lookup_None; eauto. }
  iMod (dom_auth_extend _ (<[ ℓ := None ]> σMLvirt) with "HAσdom []") as "HAσdom".
  1: iPureIntro; rewrite dom_insert_L; set_solver.
  iModIntro.
  iFrame "HGC".
  iSplitR "Hℓγ Hmtζ".
  2: { iFrame. iExists ℓ. iApply "Hℓγ". }
  cbn. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  unfold C_state_interp, named.
  iExists ζfreeze, ζσ, ζrest.
  iExists (<[γ:=LlocPublic ℓ]> χvirt), (<[ ℓ := None ]> σMLvirt).
  iFrame. iFrame "HAζpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; iFrame.
  + rewrite pub_locs_in_lstore_insert_pub //. by eapply elem_of_dom_2.
  + eapply is_store_blocks_expose_lloc; eauto.
  + eapply is_store_expose_lloc; eauto.
  + eapply expose_llocs_trans; first eassumption.
    eapply expose_llocs_insert; eauto.
  + intros ℓ' γ' HH. destruct (decide (γ=γ')) as [<-|]; simplify_map_eq.
    - rewrite dom_union_L elem_of_union. right. by eapply elem_of_dom_2.
    - by eapply Hfreezeχ.
Qed.

Lemma freeze_to_immut γ bb θ: ⊢ (SI ∗ GC θ ∗ γ ↦fresh{DfracOwn 1} bb ==∗ SI ∗ GC θ ∗ γ ↦imm bb)%I.
Proof.
  iIntros "(Hσ & HGC & (Hmtζ & Hmtfresh))".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iPoseProof (ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  iDestruct (lloc_own_priv_of with "HAχvirt Hmtfresh") as %Hχvirtγ.
  iMod ((ghost_map_update (Immut,bb)) with "HAζbl Hmtζ") as "(HAζbl & Hmtζ)".
  iMod (ghost_map_elem_persist with "Hmtζ") as "#Hmtζ".
  iDestruct (big_sepM_insert with "[$HAζpers $Hmtζ]") as "#HAζpers2".
  { eapply map_filter_lookup_None. right. intros ? ?. by simplify_map_eq. }
  rewrite -lstore_immut_blocks_insert_immut //.
  iModIntro.
  iFrame "HGC".
  iSplitL.
  2: done.
  cbn. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  unfold C_state_interp, named.
  assert (Hζγ': ζfreeze !! γ = Some (Mut, bb)).
  { subst. rewrite lookup_union_r; eauto. by eapply map_disjoint_Some_l. }
  iExists (<[γ:=(Immut, bb)]> ζfreeze), ζσ, (<[γ:=(Immut, bb)]> ζrest).
  iExists χvirt, σMLvirt.
  iFrame. iFrame "HAζpers2".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + rewrite pub_locs_in_lstore_insert_existing; eauto. by eapply elem_of_dom_2.
  + eapply freeze_lstore_freeze_lloc; eauto.
  + subst. rewrite insert_union_r. 1: done. eapply map_disjoint_Some_l; done.
  + apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  + eapply is_store_freeze_lloc; eauto.
  + intros x y H. rewrite dom_insert_L. apply elem_of_union; right. by eapply Hfreezeχ.
  + eapply GC_correct_freeze_lloc; eauto.
Qed.
End UpdateLaws.
