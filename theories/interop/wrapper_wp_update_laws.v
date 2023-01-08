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

(* todo: lemmas to help manipulate is_store_blocks? *)

Context (σ : Wrap.state).
Notation SI := (weakestpre.state_interp σ).

Lemma ml_to_mut θ l vs: ⊢ (GC θ ∗ l ↦∗ vs ∗ SI ==∗ SI ∗ GC θ ∗ ∃ b γ, γ ↦mut{DfracOwn 1} (TagDefault,b) ∗ block_sim_raw l γ ∗ block_sim_arr vs b)%I.
Proof.
  iIntros "(HGC & Hl & Hσ)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "SIC".
  iDestruct (gen_heap_valid with "HAσMLv Hl") as %Hlσ.
  destruct (χvirt !! l) as [ll|] eqn:Hlχ.
  2: { exfalso. 
       apply not_elem_of_dom_2 in Hlχ.
       apply elem_of_dom_2 in Hlσ.
       destruct Hstore_blocks as [Hdom Hstore_blocks]. unfold lloc_map in Hdom.
       rewrite <- Hdom in Hlχ.
       by apply Hlχ. }
  iMod (gen_heap_update _ _ _ None with "HAσMLv Hl") as "[HAσMLv Hl]".
  assert (ll ∈ dom ζσ) as Hllζ.
  1: { destruct Hstore_blocks as [Hdom Hstore_blocks]. apply Hstore_blocks. exists l, vs. split; try done. }
  apply elem_of_dom in Hllζ. destruct Hllζ as [bb Hζσll].
  iMod (ghost_map_insert _ bb with "HAζbl") as "(HAζbl & Hzz)".
  1: { eapply map_disjoint_Some_l; done. }
  iModIntro. iFrame "HGC".
  unfold is_store in Hstore.
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. by apply lookup_union_Some_l. }
  specialize (Hstore l vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: by iApply (block_sim_arr_of_ghost_state with "HAχbij HAζpers").
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: iApply (gset_bij_own_elem_get with "HAχbij"); by eapply elem_of_map_to_set_pair.
  assert (ζrest !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iAssert (⌜gset_bijective (map_to_set pair χvirt)⌝)%I as "%Hbij".
  1: { by iDestruct (gset_bij_own_valid with "HAχbij") as %[? ?]. }
  iSplitR "Hzz". 1: iSplitL "HσC HnC".
  + iExists _. iFrame.
  + unfold C_state_interp, named. iExists (ζfreeze), (delete ll ζσ), (<[ll:=(Mut, (TagDefault, lvs))]> ζrest).
    iExists χvirt, fresh, (<[l:=None]> σMLvirt). iFrame.
    iSplitL "HAnMLv HAσdom HAσsafe".
    1: { iExists _; iFrame. iSplitL "HAσdom".
         + iApply (dom_auth_dom with "HAσdom"). rewrite dom_insert_L. eapply elem_of_dom_2 in Hlσ. set_solver.
         + iApply (big_sepM_insert_override_2 with "HAσsafe"); first done; by iIntros "_". }
    iSplitL. 
    1: { rewrite dom_insert_L.
         iApply (big_sepM_insert_inj with "[] [] [] [Hl] HAχNone"). 4: iApply "Hl".
         all: iPureIntro.
         + intros k v1 v2 H1 H2. eapply gset_bijective_eq_iff. 1: done. 1-2: eapply elem_of_map_to_set_pair; done. done.
         + by apply not_elem_of_dom_2.
         + done. }
    iSplitL.
    1: { iApply big_sepM_insert.
         + done.
         + iSplit. 2: iApply "HAζpers". cbn; iIntros "%Hne"; congruence. }
    iPureIntro. split_and!.
    all: eauto.
    - symmetry. subst. by apply union_delete_insert.
    - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
      apply map_disjoint_delete_l. done.
    - destruct Hstore_blocks as [HL HR]. split.
      1: rewrite dom_insert_lookup_L; try done.
      intros ll'. destruct (decide (ll' = ll)); try subst ll'; split.
      * intros [x Hx]%elem_of_dom. rewrite lookup_delete in Hx. done.
      * intros (ℓ & Vs & HH1 & HH2).
        enough (l = ℓ) as <-. 2: eapply gset_bijective_eq_iff. 2: apply Hbij.
        2-3: by apply elem_of_map_to_set_pair. 2: done.
        rewrite lookup_insert in HH2. done.
      * intros [x Hx]%elem_of_dom. rewrite lookup_delete_ne in Hx. 2:done. 
        destruct (HR ll') as [(ℓ & Vs & HH1 & HH2) _].  1: by apply elem_of_dom.
        exists ℓ, Vs. split; first done.
        rewrite lookup_insert_ne; try done. intros Hn.
        eapply (gset_bijective_eq_iff _ _ _ _ _ Hbij) in Hn. 1: apply n; symmetry; apply Hn. 
        all: by apply elem_of_map_to_set_pair.
      * intros (ℓ & Vs & HH1 & HH2). apply elem_of_dom. rewrite lookup_delete_ne; last done.
        apply elem_of_dom.
        destruct (HR ll') as [_ Hdom]. apply Hdom.
        exists ℓ, Vs; split; try done.
        rewrite lookup_insert_ne in HH2; try done. intros Hn.
        eapply (gset_bijective_eq_iff _ _ _ _ _ Hbij) in Hn. 1: apply n; symmetry; apply Hn. 
        all: by apply elem_of_map_to_set_pair.
    - intros ℓ Vs γ blk HH1 HH2 HH3. eapply Hstore; try done. destruct (decide (ℓ = l)).
      1: subst ℓ; rewrite lookup_insert in HH1; done.
      rewrite lookup_insert_ne in HH1; try done.
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
  iAssert (⌜gset_bijective (map_to_set pair χvirt)⌝)%I as "%Hbij".
  1: { by iDestruct (gset_bij_own_valid with "HAχbij") as %[? ?]. }
  assert (gmap_inj χvirt) as Hinj.
  1: { intros k v1 v2 Hv1 Hv2. eapply Hbij. all: apply elem_of_map_to_set_pair; done. }
  unfold is_store_blocks in Hstore_blocks.
  unfold is_store in Hstore.
  iPoseProof (@ghost_map_lookup with "HAζbl Hl") as "%Hζl".
  apply elem_of_map_to_set_pair in Hχℓ.
  iPoseProof (big_sepM_delete_S with "[] [] HAχNone") as "(Hℓ & HAχNone)".
  1: done.
  1: iPureIntro; eapply elem_of_dom_2; done.
  iPoseProof ("Hℓ" $! Hχℓ) as "Hℓ".
  iDestruct (gen_heap_valid with "HAσMLv Hℓ") as "%Hlσ".
  iMod (gen_heap_update _ _ _ (Some vs) with "HAσMLv Hℓ") as "[HAσMLv Hℓ]".
  iMod (ghost_map_delete with "HAζbl Hl") as "HAζbl".
  iModIntro. iFrame "HGC". iSplitR "Hℓ". 2: iExists ℓ; iFrame; done.
  cbn. iSplitL "HσC HnC".
  1: iExists _; iFrame.
  unfold C_state_interp, named.
  iExists ζfreeze, (<[γ:=(Mut, (TagDefault, b))]>ζσ), (delete γ ζrest).
  iExists χvirt, fresh, (<[ ℓ := Some vs ]> σMLvirt).
  iFrame.
  iSplitL "HAnMLv". 2: iSplitL. 3: iSplitL. 4: iPureIntro; split_and!; eauto.
  + iExists _; done.
  + rewrite dom_delete_L. iFrame.
  + iPoseProof big_sepM_delete as "(HH & _)"; last iPoseProof ("HH" with "HAζpers") as "(_ & HAζpers2)"; done.
  + erewrite (union_insert_delete ζσ ζrest). 2: eapply map_disjoint_Some_r. 2: apply Hfreezedj. all: done.
  + apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    apply map_disjoint_delete_r. done.
  + destruct Hstore_blocks as [Hsl Hsr]. split. 2: intros γ'; destruct (Hsr γ') as [Hsrl Hsrr]; split.
    * rewrite <- Hsl. apply dom_insert_lookup_L. done.
    * intros Hin. rewrite dom_insert_L in Hin. apply elem_of_union in Hin. destruct Hin as [->%elem_of_singleton|Hin2].
      - exists ℓ, vs. split; try done. by rewrite lookup_insert.
      - destruct (Hsrl Hin2) as (ℓ2 & Vs & H1 & H2); exists ℓ2, Vs; split; try done.
        rewrite lookup_insert_ne; first done; congruence.
    * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ2 = ℓ)) as [->|Hne].
      - rewrite Hχℓ in H1. injection H1; intros ->. rewrite dom_insert_L. apply elem_of_union; left. by apply elem_of_singleton.
      - rewrite dom_insert_L. apply elem_of_union; right. apply Hsrr. eexists _, _; split; try done. rewrite lookup_insert_ne in H2; done.
  + intros ℓ1 vs1 γ1 bl1 Hs1 Hs2 Hs3. destruct (decide (ℓ = ℓ1)) as [<- | Hne].
    * rewrite Hχℓ in Hs2. rewrite lookup_insert in Hs1. rewrite Hfreezeeq in Hs3.
      injection Hs2; intros ->.
      injection Hs1; intros ->.
      apply lookup_union_Some_inv_r in Hs3.
      2: eapply map_disjoint_Some_r; done.
      rewrite Hζl in Hs3. injection Hs3; intros <-. econstructor. done.
    * rewrite lookup_insert_ne in Hs1; last done. eapply Hstore; done.
Qed.

Lemma is_val_mono χ χL ζ ζL x y : χ ⊆ χL -> ζ ⊆ ζL -> is_val χ ζ x y → is_val χL ζL x y.
Proof.
  intros H1 H2; induction 1 in χL,ζL,H1,H2|-*; econstructor; eauto.
  all: eapply lookup_weaken; done.
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
  1: eapply not_elem_of_dom_1; by destruct Hstore_blocks as [-> _].
  iPoseProof (big_sepM_insert_M _ _ _ ℓ γ with "[] [HℓNone] HAχNone") as "HAχNone".
  1: iPureIntro; by eapply not_elem_of_dom_1.
  1: iIntros "_"; done.
  iMod (ghost_map_delete with "HAfresh Hmtfresh") as "HAfresh".
  iModIntro.
  iFrame "HGC".
  iSplitR "Hℓγ Hmtζ".
  2: { iFrame. iExists ℓ. iApply "Hℓγ". }
  cbn. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  unfold C_state_interp, named. unfold lstore.
  iExists ζfreeze, ζσ, ζrest.
  iExists (<[ℓ:=γ]> χvirt), (delete γ fresh), (<[ ℓ := None ]> σMLvirt).
  iFrame. iFrame "HAζpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + rewrite map_to_set_insert_L. iFrame. by eapply not_elem_of_dom.
  + destruct Hstore_blocks as [Hsl Hsr]; split.
    - rewrite ! dom_insert_L. rewrite Hsl; done.
    - intros γ1; destruct (Hsr γ1) as [Hsrl Hsrr]; split.
      * intros Hin. destruct (Hsrl Hin) as (ℓ1 & Vs & H1 & H2).
        exists ℓ1, Vs. destruct (decide (ℓ1 = ℓ)) as [-> | Hn].
        2: rewrite ! lookup_insert_ne; try done.
        exfalso. apply Hℓdom. by eapply elem_of_dom.
      * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ = ℓ2)) as [<- | Hn].
        1: rewrite lookup_insert in H2; congruence.
        apply Hsrr. exists ℓ2, Vs.
         rewrite lookup_insert_ne in H1; last done.  rewrite lookup_insert_ne in H2; done.
  + intros ℓ1 vs γ1 blk H1 H2 H3. destruct (decide (ℓ = ℓ1)) as [<- | Hn].
    1: rewrite lookup_insert in H1; congruence.
    rewrite lookup_insert_ne in H1; last done. rewrite lookup_insert_ne in H2; last done.
    specialize (Hstore _ _ _ _ H1 H2 H3).
    inversion Hstore; subst.
    econstructor. eapply Forall2_impl; first apply H.
    intros x y Hval. eapply is_val_mono; last done; eauto.
    apply insert_subseteq. by eapply not_elem_of_dom.
  + destruct Hχvirt as [H1 H2]. split.
    - etransitivity; first done.
      eapply insert_subseteq. eapply not_elem_of_dom; done.
    - intros k1 k2 v Hk1 Hk2.
      destruct (decide (k1 = ℓ)) as [-> | Hne1]; destruct (decide (k2 = ℓ)) as [-> | Hne2].
      1: congruence.
      all: rewrite ?lookup_insert in Hk1,Hk2.
      all: rewrite ?lookup_insert_ne in Hk1,Hk2; try done.
      1-2: exfalso; eapply Hfreshχ; first done; eapply elem_of_dom_2 in Hfreshγ; congruence.
      eapply H2; done.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. rewrite dom_union_L; apply elem_of_union; right. by eapply elem_of_dom.
    - rewrite lookup_insert_ne in Hxy; last done. by eapply Hfreezeχ.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. intros H%elem_of_dom. rewrite lookup_delete in H. destruct H; congruence.
    - rewrite lookup_insert_ne in Hxy; last done. intros H%elem_of_dom. destruct H as [xx [Hx1 Hx2]%lookup_delete_Some]. eapply Hfreshχ; first done.
      by eapply elem_of_dom.
Qed.

Lemma is_val_insert_immut χ ζ γ bb bb2 x y : ζ !! γ = Some bb2 → mutability bb2 = Mut → is_val χ ζ x y → is_val χ (<[γ := bb]> ζ) x y.
Proof.
  intros H1 H2; induction 1; econstructor; eauto.
  all: rewrite lookup_insert_ne; first done.
  all: intros ->; destruct bb2 as [mut ?]; cbn in *.
  all: subst mut; rewrite H1 in H; congruence.
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
  iExists (<[γ:=(Immut, bb)]> ζfreeze), ζσ, (<[γ:=(Immut, bb)]> ζrest).
  iExists χvirt, (delete γ fresh), σMLvirt.
  iFrame. iFrame "HAζpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
    intros ? ->%elem_of_singleton. by eapply elem_of_dom.
  + destruct Hfreezeρ as [HL HR]. split.
    - rewrite HL. rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
      intros ? ->%elem_of_singleton. subst. rewrite dom_union_L. rewrite elem_of_union. right. eapply elem_of_dom; done.
    - intros γ1 b1 b2 H1 H2. destruct (decide (γ = γ1)) as [<- |H3].
      * rewrite lookup_insert in H2. injection H2; intros <-.
        assert (ζfreeze !! γ = Some (Mut, bb)) as H4.
        1: subst; apply lookup_union_Some_r; done.
        specialize (HR γ b1 (Mut, bb) H1 H4).
        inversion HR; subst; econstructor.
      * rewrite lookup_insert_ne in H2; last done. by eapply HR.
  + subst. rewrite insert_union_r. 1: done. eapply map_disjoint_Some_l; done.
  + apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  + intros l vs γ1 bb' H1 H2 H3. destruct (decide (γ = γ1)) as [<- | H4].
    * exfalso; eapply Hfreshχ; try done. by eapply elem_of_dom.
    * rewrite lookup_insert_ne in H3; last done.
      specialize (Hstore _ _ _ _ H1 H2 H3).
      inversion Hstore. subst vs0 bb'.
      econstructor. eapply Forall2_impl; first done.
      intros x y H5.
      eapply is_val_insert_immut; last done.
      1: subst; rewrite lookup_union_r; first done. 2:done.
      eapply map_disjoint_Some_l; done.
  + intros x y H. rewrite dom_insert_L. apply elem_of_union; right. by eapply Hfreezeχ.
  + intros x y H1 H2. rewrite dom_delete_L in H2. apply elem_of_difference in H2.
    destruct H2; eapply Hfreshχ; done.
  + destruct HGCOK as [H1 H2]; split; first done.
    intros γ1 Hγ. destruct (H2 γ1 Hγ) as (m & tgt & vs & Hfreeze & Hlloc).
    destruct (decide (γ1 = γ)) as [-> | H3].
    * setoid_rewrite lookup_insert. destruct bb. do 3 eexists; split; first done.
      intros γ' H4. eapply Hlloc. subst. eapply lookup_union_Some_r in Hζγ.
      2: done. rewrite Hfreeze in Hζγ. congruence.
    * setoid_rewrite lookup_insert_ne; last done. do 3 eexists; done.
Qed.
End UpdateLaws.





















