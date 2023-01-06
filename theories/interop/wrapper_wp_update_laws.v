From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
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
  1: by iApply (block_sim_arr_of_ghost_state with "HAχbij HAζpers").
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: iApply (gset_bij_own_elem_get with "HAχbij"); by eapply elem_of_map_to_set_pair.
  assert (ζrest !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iSplitR "Hzz". 1: iSplitL "HσC HnC".
  + iExists _. iFrame.
  + unfold C_state_interp, named. iExists (ζfreeze), (delete ll ζσ), (<[ll:=(Mut, (TagDefault, lvs))]> ζrest).
    iExists χvirt, fresh, (<[l:=None]> σMLvirt). iFrame.
    iSplitL "HAnMLv HAσdom HAσsafe".
    1: { iExists _; iFrame. iSplitL "HAσdom".
         + iApply (dom_auth_dom with "HAσdom"). rewrite dom_insert_L. eapply elem_of_dom_2 in Hlσ. set_solver.
         + iApply (big_sepM_insert_override_2 with "HAσsafe"); first done; by iIntros "_". }
    iSplitL. 
    { rewrite dom_insert_L.
      iApply (big_sepM_insert_inj with "[] [] [] [Hl] HAχNone"); eauto.
      iPureIntro. by apply not_elem_of_dom_2. }
    iSplitL.
    { iApply big_sepM_insert; eauto.
      iFrame "HAζpers". cbn; iIntros "%Hne"; congruence. }
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
  iPoseProof (block_sim_arr_to_ghost_state with "HAχbij HAζbl [] [] [] [] Hsim ") as "%Hsim".
  1-4: iPureIntro; done.
  iPoseProof (@gset_bij_elem_of with "HAχbij Hlℓ") as "%Hχℓ".
  unfold is_store in Hstore.
  iPoseProof (@ghost_map_lookup with "HAζbl Hl") as "%Hζl".
  apply elem_of_map_to_set_pair in Hχℓ.
  iPoseProof (big_sepM_delete_S with "[] [] HAχNone") as "(Hℓ & HAχNone)"; eauto.
  1: iPureIntro; eapply elem_of_dom_2; done.
  iPoseProof ("Hℓ" $! Hχℓ) as "Hℓ".
  iDestruct (gen_heap_valid with "HAσMLv Hℓ") as "%Hlσ".
  iMod (gen_heap_update _ _ _ (Some vs) with "HAσMLv Hℓ") as "[HAσMLv Hℓ]".
  iMod (ghost_map_delete with "HAζbl Hl") as "HAζbl".
  iMod (val_arr_safe_to_ghost_state with "[#] HAσdom") as "(HAσdom & H1)".
  { iPureIntro. eapply Forall2_Forall_l; first exact Hsim. eapply Forall_forall; intros k1 v1 x.
    eapply is_val_is_safe_on_heap. destruct Hstore_blocks; set_solver. }
  iModIntro. iFrame "HGC". iSplitR "Hℓ". 2: iExists ℓ; iFrame; done.
  cbn. iSplitL "HσC HnC".
  1: iExists _; iFrame.
  unfold C_state_interp, named.
  iExists ζfreeze, (<[γ:=(Mut, (TagDefault, b))]>ζσ), (delete γ ζrest).
  iExists χvirt, fresh, (<[ ℓ := Some vs ]> σMLvirt).
  iFrame.
  iSplitL "HAnMLv HAσdom HAσsafe H1". 2: iSplitL. 3: iSplitL. 4: iPureIntro; split_and!; eauto.
  + iExists _; iFrame. iSplitL "HAσdom"; first (iApply (dom_auth_dom with "HAσdom"); erewrite dom_insert_L; eapply elem_of_dom_2 in Hlσ; set_solver).
    iApply (big_sepM_insert_override_2 with "HAσsafe [H1]"); first done; by iIntros "_".
  + by rewrite dom_delete_L.
  + iPoseProof big_sepM_delete as "(HH & _)"; last iPoseProof ("HH" with "HAζpers") as "(_ & HAζpers2)"; done.
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
  iPoseProof (@ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  iPoseProof (@ghost_map_lookup with "HAfresh Hmtfresh") as "%Hfreshγ".
  pose (fresh_locs (dom χvirt)) as ℓ.
  assert (ℓ ∉ dom χvirt) as Hℓdom.
  1: { epose proof (fresh_locs_fresh (dom χvirt) 0) as Hfresh.
       unfold loc_add in Hfresh. rewrite Z.add_0_r in Hfresh. apply Hfresh. lia. }
  iMod (gset_bij_own_extend with "HAχbij") as "(HAχbij & Hℓγ)".
  1: intros γ' Hγ'%elem_of_map_to_set_pair; apply Hℓdom; by eapply elem_of_dom_2.
  1: intros ℓ' Hℓ'%elem_of_map_to_set_pair; apply (Hfreshχ _ _ Hℓ'); by eapply elem_of_dom.
  iMod (gen_heap_alloc _ ℓ None with "HAσMLv") as "(HAσMLv & HℓNone & Hmeta)".
  1: eapply not_elem_of_dom_1. by destruct Hstore_blocks as [-> _].
  iPoseProof (big_sepM_insert_M _ _ _ ℓ γ with "[] [HℓNone] HAχNone") as "HAχNone"; eauto.
  1: iPureIntro; by eapply not_elem_of_dom_1.
  iMod (ghost_map_delete with "HAfresh Hmtfresh") as "HAfresh".
  iMod (dom_auth_extend _ (<[ ℓ := None ]> σMLvirt) with "HAσdom []") as "HAσdom".
  1: iPureIntro; rewrite dom_insert_L; set_solver.
  iModIntro.
  iFrame "HGC".
  iSplitR "Hℓγ Hmtζ".
  2: { iFrame. iExists ℓ. iApply "Hℓγ". }
  cbn. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  unfold C_state_interp, named.
  iExists ζfreeze, ζσ, ζrest.
  iExists (<[ℓ:=γ]> χvirt), (delete γ fresh), (<[ ℓ := None ]> σMLvirt).
  iFrame. iFrame "HAζpers".
  iSplitL "HAnMLv HAσsafe". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; iFrame. iApply (big_sepM_insert_2 with "[] HAσsafe"); done.
  + rewrite map_to_set_insert_L //. by eapply not_elem_of_dom.
  + eapply is_store_blocks_expose_lloc; eauto.
  + eapply is_store_expose_lloc; eauto.
  + destruct Hχvirt as [H1 H2]. split.
    - etransitivity; first done.
      eapply insert_subseteq. eapply not_elem_of_dom; done.
    - eapply gmap_inj_extend; eauto. intros ? ? ? <-. eapply Hfreshχ; eauto.
      by eapply elem_of_dom_2.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. rewrite dom_union_L; apply elem_of_union; right. by eapply elem_of_dom.
    - rewrite lookup_insert_ne in Hxy; last done. by eapply Hfreezeχ.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. intros H%elem_of_dom. rewrite lookup_delete in H. destruct H; congruence.
    - rewrite lookup_insert_ne in Hxy; last done. intros H%elem_of_dom. destruct H as [xx [Hx1 Hx2]%lookup_delete_Some]. eapply Hfreshχ; first done.
      by eapply elem_of_dom.
Qed.

Lemma freeze_to_immut γ bb θ: ⊢ (SI ∗ GC θ ∗ γ ↦fresh{DfracOwn 1} bb ==∗ SI ∗ GC θ ∗ γ ↦imm bb)%I.
Proof.
  iIntros "(Hσ & HGC & (Hmtζ & Hmtfresh))". 
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iPoseProof (@ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  iPoseProof (@ghost_map_lookup with "HAfresh Hmtfresh") as "%Hfreshγ".
  iMod ((ghost_map_update (Immut,bb)) with "HAζbl Hmtζ") as "(HAζbl & Hmtζ)".
  iMod (ghost_map_elem_persist with "Hmtζ") as "#Hmtζ".
  iMod (ghost_map_delete with "HAfresh Hmtfresh") as "HAfresh".
  iPoseProof (big_sepM_insert_override_2 with "HAζpers []") as "#HAζpers2"; first done.
  1: iIntros "_ _"; iApply "Hmtζ".
  iClear "HAζpers". iRename "HAζpers2" into "HAζpers".
  iModIntro.
  iFrame "HGC".
  iSplitL.
  2: done.
  cbn. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  unfold C_state_interp, named.
  assert (Hζγ': ζfreeze !! γ = Some (Mut, bb)).
  { subst. rewrite lookup_union_r; eauto. by eapply map_disjoint_Some_l. }
  iExists (<[γ:=(Immut, bb)]> ζfreeze), ζσ, (<[γ:=(Immut, bb)]> ζrest).
  iExists χvirt, (delete γ fresh), σMLvirt.
  iFrame. iFrame "HAζpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
    intros ? ->%elem_of_singleton. by eapply elem_of_dom.
  + eapply freeze_lstore_freeze_lloc; eauto.
  + subst. rewrite insert_union_r. 1: done. eapply map_disjoint_Some_l; done.
  + apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  + eapply is_store_freeze_lloc; eauto.
    intros ? ? ? <-. eapply Hfreshχ; eauto. by eapply elem_of_dom_2.
  + intros x y H. rewrite dom_insert_L. apply elem_of_union; right. by eapply Hfreezeχ.
  + intros x y H1 H2. rewrite dom_delete_L in H2. apply elem_of_difference in H2.
    destruct H2; eapply Hfreshχ; done.
  + eapply GC_correct_freeze_lloc; eauto.
Qed.
End UpdateLaws.





















