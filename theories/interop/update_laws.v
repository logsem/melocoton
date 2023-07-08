From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props stdpp_extra.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Import basics basics_resources basics_constructions gctoken.

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

Lemma ml_to_mut θ dirty qp ℓ vs :
  ⊢ GC θ dirty ∗ ℓ ↦∗{# qp} vs ==∗
    ∃ lvs γ fid, GC θ (dirty ∪ {[γ]}) ∗ γ ↦mut{DfracOwn qp} (TagDefault, lvs) ∗ γ ~ℓ~ ℓ @ fid ∗ lvs ~~∗ vs.
Proof using.
  iIntros "(HGC & Hl)". iNamed "HGC". iNamed "HSI_block_level".
  iDestruct (pgm_lookup with "GCσMLv Hl") as %Hlσ.
  destruct (Hstore ℓ) as (fid & γ & Hχγ); first by eapply elem_of_dom_2.
  eapply lloc_map_pubs_lookup_Some_2 in Hχγ. clear fid.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "GC_per_loc") as "(HH&GC_per_loc)".
  iAssert (|==> ∃ lvs w',
      per_location_invariant ζ_future (<[ ℓ := w' ]> σMLvirt) (dirty ∪ {[γ]}) γ ℓ
    ∗ γ ↦mut{DfracOwn qp} (TagDefault, lvs)
    ∗ lvs ~~∗ vs
    ∗ state_interp (<[ ℓ := w' ]> σMLvirt)
    ∗ lstore_own_auth ζ_future
    ∗ lloc_own_auth χ_future)%I with "[HH GCσMLv Hl GCζauth GCχauth]" as "Hmod".
  { iDestruct "HH" as "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&(Hγ&#Hγsim)&#Hsim&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|(%Hne1&%Hne2)]]])".
    1: by iPoseProof (pgm_elem_ne with "Hℓ Hl") as "%Hbot".
    3: by rewrite Hne1 in Hlσ.
    - iDestruct (pgm_elem_valid with "Hl") as "%Hlt".
      edestruct dfrac_valid_own as [HL _]. apply HL in Hlt; clear HL.
      apply Qp.le_lteq in Hlt. destruct Hlt as [Hlt|Hlt]; simplify_eq.
      + apply Qp.lt_sum in Hlt as (qr&Hqr).
        rewrite Hqr. iDestruct "Hγ" as "(Hγ1&Hγ2)".
        iModIntro. iExists lvs, vs. rewrite insert_id; last done. cbn in *; simplify_eq. iFrame. iFrame "Hsim Hγsim".
        iExists _, _. iRight. iRight. iLeft. iExists _, _. iFrame.
        iFrame "Hsim". iPureIntro; split_and!; try done. set_solver.
      + iPoseProof (big_sepL2_length with "Hsim") as "%Hlen".
        iDestruct (block_sim_arr_find_canon with "GCχauth GCζauth Hsim") as "(%vs''&#Hcanon)"; first done.
        iPoseProof (big_sepL2_length with "Hcanon") as "%Hlencanon".
        iMod (pgm_update (D:=MLHeapPGMData) vs'' with "GCσMLv Hl") as "(GCσMLv&Hl)". 2: done.
        1: cbn in *; simplify_eq; congruence.
        iDestruct (lstore_own_elem_of with "GCζauth Hγ") as "%HH". cbn in *; simplify_eq.
        iModIntro. iExists lvs, vs''. cbn. iFrame "Hγ Hsim GCζauth GCχauth Hγsim".
        iSplitR "GCσMLv". 2: iApply "GCσMLv".
        iExists  vs'', lvs. iLeft. iFrame. iFrame "Hcanon".
        iPureIntro. done.
    - iPoseProof (pgm_elem_agree with "Hmapsℓ Hl") as "%Heq"; simplify_eq.
      iPoseProof (big_sepL2_length with "Hsim") as "%Hlen".
      iCombine "Hmapsℓ Hl" as "Hℓ". iDestruct (pgm_elem_valid with "Hℓ") as "%Hlt".
      edestruct dfrac_valid_own as [HL _]. apply HL in Hlt; clear HL.
      apply Qp.le_lteq in Hlt. destruct Hlt as [Hlt|Hlt]; simplify_eq.
      + apply Qp.lt_sum in Hlt as (qr&Hqr).
        assert (r = qp+qr)%Qp as Hr; last simplify_eq.
        { rewrite Hqr in Hsum. eapply Qp.add_inj_r. by rewrite Qp.add_assoc. }
        iDestruct "Hmapsγ" as "((Hmapsγ1&Hmapsγ2)&#Hsim2)".
        iExists lvs, vs. rewrite insert_id; last done.
        iFrame "Hsim GCζauth GCσMLv GCχauth Hmapsγ1 Hsim2".
        iModIntro. iExists _, _. iRight. iRight. iLeft. iExists _, _.
        iFrame. iFrame "Hsim". iPureIntro; split_and!; try done.
        set_solver.
      + assert (r = qp)%Qp as Hr; last simplify_eq.
        { rewrite -Hlt in Hsum. by eapply Qp.add_inj_r. }
        iDestruct (block_sim_arr_find_canon with "GCχauth GCζauth Hsim") as "(%vs''&#Hcanon)"; first done.
        iPoseProof (big_sepL2_length with "Hcanon") as "%Hlencanon".
        rewrite Hlt. iMod (pgm_update (D:=MLHeapPGMData) vs'' with "GCσMLv Hℓ") as "(GCσMLv&Hl)". 2: done.
        1: cbn in *; simplify_eq; congruence.
        iDestruct "Hmapsγ" as "(Hγ&#Hsimγ)".
        iDestruct (lstore_own_elem_of with "GCζauth Hγ") as "%HH".
        iModIntro. iExists lvs, vs''. iFrame "Hγ Hsimγ Hsim GCζauth GCχauth". iSplitR "GCσMLv"; last iApply "GCσMLv".
        iExists _, _. iLeft. iFrame. iFrame "Hcanon". done. }
  iMod "Hmod" as "(%lvs&%w'&Hperloc&Hf1&#Hf2&GCσMLv&GCζauth&GCχauth)".
  apply lloc_map_pubs_lookup_Some_1 in Hχγ as (fid & Hχγ2).
  iPoseProof (lloc_own_auth_get_pub with "[$]") as "#Hf3"; first done.
  iExists lvs, γ, fid. iFrame "Hf2 Hf1 Hf3".
  iModIntro. do 5 iExists _.
  iFrame "GCζ GCχ GCθ GCroots GCinit GCχauth HSI_GC". iSplit; last done.
  iExists (<[ℓ:=w']> σMLvirt). iFrame.
  repeat iSplit; try done.
  - iApply big_sepM_delete; first eauto.
    iFrame. iApply GC_per_loc_insert; last iApply GC_per_loc_make_dirty; last done.
    + intros γ' [Hne Hlu]%lookup_delete_Some. eapply Hne, lloc_map_pubs_inj.
      1: apply Hχfuture. all: eauto.
    + set_solver.
  - iPureIntro. rewrite dom_insert_L. intros ℓ' [Hin%elem_of_singleton|Hin]%elem_of_union.
    2: by apply Hstore.
    simplify_eq; by repeat eexists.
Qed.

Lemma mut_to_ml_store γ vs lvs θ dirty :
  ⊢ GC θ dirty ∗ γ ↦mut (TagDefault, lvs) ∗ lvs ~~∗ vs ==∗
    GC θ dirty ∗ ∃ fid ℓ, ℓ ↦∗ vs ∗ γ ~ℓ~ ℓ @ fid.
Proof using.
  iIntros "(HGC & Hl & #Hsim)".
  iDestruct (lstore_own_vblock_M_as_mut with "Hl") as "(Hl & (%fid & %ℓ & #Hlℓ))".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lstore_own_mut_of with "GCζauth Hl") as "(%Hγζ&#_)".
  iPoseProof (lloc_own_pub_of with "GCχauth Hlℓ") as "%Hχγ".
  apply lloc_map_pubs_lookup_Some_2 in Hχγ.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "GC_per_loc") as "((%vs'&%lvs'&[(Hℓ&%Hγζ'&#Hcanon)|[(%Hℓσ&(Hγ&_)&_)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsimm&%Hsum)|(%Hne1&%Hne2)]]])&GC_per_loc)".
  2: iDestruct "Hl" as "(Hl&_)"; by iPoseProof (pgm_elem_ne with "Hl Hγ") as "%Hne".
  3: simplify_eq.
  2: { iDestruct "Hl" as "(Hl&_)". iDestruct "Hmapsγ" as "(Hmapsγ&_)".
       iPoseProof (pgm_elem_ne with "Hl Hmapsγ") as "%Hf". done. }
  iDestruct (pgm_lookup with "GCσMLv Hℓ") as %Hℓσ.
  iPoseProof (big_sepL2_length with "Hsim") as "%Hlen1".
  iDestruct (big_sepL2_length with "Hcanon") as %Hlencanon.
  iMod (pgm_update (D:=MLHeapPGMData) vs with "GCσMLv Hℓ") as "[GCσMLv Hℓ]".
  1: cbn; simplify_eq; congruence. 1: done.
  iPoseProof (GC_per_loc_modify_σ with "GC_per_loc") as "GC_per_loc".
  1: by eapply lloc_map_pubs_inj, expose_llocs_inj. 1: done.
  iPoseProof (pgm_elem_to_pers with "Hℓ") as "#Hℓlen".
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ with "[$GC_per_loc Hl]") as "GC_per_loc".
  { iExists vs, lvs. iRight; iLeft. rewrite lookup_insert. repeat iSplit; try done.
    1: by iApply lstore_own_mut_to_elem. 1: by do 2 iExists _. 1: by rewrite -Hlen1. }
  iModIntro.
  iSplitR "Hℓ".
  2: iExists _, _; iFrame "Hℓ Hlℓ".
  rewrite /GC /SI_block_level /named.
  iExists ζ, ζ_future, χ, χ_future, roots_s. iFrame. iSplit; last done.
  iExists (<[ℓ:=_]> σMLvirt). iFrame.
  iPureIntro. split_and!; try done.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma mut_to_ml θ dirty qp γ lvs :
  ⊢ GC θ dirty ∗ γ ↦mut{DfracOwn qp} (TagDefault, lvs) ==∗
    GC θ (dirty ∪ {[ γ ]}) ∗ ∃ fid ℓ vs, ℓ ↦∗{# qp} vs ∗ γ ~ℓ~ ℓ @ fid ∗ lvs ~~∗ vs.
Proof using.
  iIntros "(HGC & (Hγ&%fid&%ℓ&#Hsimγ))". iNamed "HGC". iNamed "HSI_block_level".
  iDestruct (lstore_own_elem_of with "GCζauth Hγ") as %Hγζ.
  iDestruct (lloc_own_pub_of with "GCχauth Hsimγ") as %Hχγ.
  apply lloc_map_pubs_lookup_Some_2 in Hχγ as Hχγ'.
  iPoseProof (big_sepM_delete _ _ _ _ Hχγ' with "GC_per_loc") as "(HH&GC_per_loc)".
  iAssert (|==> ∃ vs w',
      per_location_invariant ζ_future (<[ ℓ := w']> σMLvirt) (dirty ∪ {[ γ ]}) γ ℓ
    ∗ ℓ↦∗{#qp} vs
    ∗ lvs ~~∗ vs
    ∗ state_interp (<[ ℓ := w']> σMLvirt)
    ∗ lstore_own_auth ζ_future)%I with "[HH GCσMLv Hγ GCζauth]" as "Hmod".
  { iDestruct "HH" as "(%vs'&%lvs'&[(Hℓ&%Hζfut&Hcanon)|[(%Hℓσ&(Hγ'&#Hγsim)&#Hsim&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|(%Hne1&%Hne2)]]])"; cbn.
    4: by simplify_eq.
    2: by iPoseProof (pgm_elem_ne with "Hγ' Hγ") as "%Hbot".
    - iDestruct (pgm_lookup with "GCσMLv Hℓ") as "%Helem".
      iDestruct (pgm_elem_valid with "Hγ") as "%Hlt".
      iPoseProof (pgm_elem_to_pers with "Hℓ") as "#Hℓlen".
      simplify_eq.
      iPoseProof (big_sepL2_length with "Hcanon") as "%Hlen1".
      iExists vs', vs'.
      rewrite !insert_id; last done.
      edestruct dfrac_valid_own as [HL _]. apply HL in Hlt; clear HL.
      iPoseProof (block_canon_arr_to_block_sim_arr with "Hcanon") as "#Hsim".
      apply Qp.le_lteq in Hlt. destruct Hlt as [Hlt|Hlt].
      + simplify_eq. apply Qp.lt_sum in Hlt as (qr&Hqr).
        rewrite Hqr. iDestruct "Hℓ" as "(Hℓ1&Hℓ2)".
        iModIntro. iFrame. iFrame "Hsim".
        iExists _, _. iRight. iRight. iLeft. iExists _, _. iFrame.
        repeat iSplit; try done; try by repeat iExists _. 2: iPureIntro; set_solver.
        by rewrite Qp.add_comm.
      + subst qp. iModIntro. iFrame "Hℓ GCσMLv Hsim GCζauth".
        iExists _, _. iRight. iLeft. iFrame.
        repeat iSplit; try done. 1: by do 2 iExists _. by rewrite -Hlen1.
    - iDestruct "Hmapsγ" as "(Hγ'&_)". cbn.
      iPoseProof (pgm_elem_agree with "Hγ Hγ'") as "%Heq"; simplify_eq.
      iCombine "Hγ Hγ'" as "Hγ".
      iDestruct (pgm_elem_valid with "Hγ") as "%Hlt".
      iPoseProof (big_sepL2_length with "Hsim") as "%Hlen1".
      iDestruct (pgm_lookup with "GCσMLv Hmapsℓ") as "%Helemℓ".
      iPoseProof (pgm_elem_to_pers with "Hmapsℓ") as "#Hℓlen".
      edestruct dfrac_valid_own as [HL _]. apply HL in Hlt; clear HL.
      apply Qp.le_lteq in Hlt. destruct Hlt as [Hlt|Hlt]; simplify_eq.
      + apply Qp.lt_sum in Hlt as (qr&Hqr).
        rewrite (Qp.add_comm _ r) in Hqr. rewrite Qp.add_comm in Hsum.
        assert (q = qp+qr)%Qp as Hr; last simplify_eq.
        { rewrite Hqr in Hsum. eapply Qp.add_inj_r. by rewrite Qp.add_assoc. }
        iDestruct "Hmapsℓ" as "(Hmapsℓ1&Hmapsℓ2)".
        iExists _, _. rewrite insert_id; last done.
        iFrame "Hsim GCζauth GCσMLv Hmapsℓ1".
        iModIntro. iExists _, _. iRight. iRight. iLeft. iExists _, _.
        iFrame. iFrame "Hsim". iSplit; first by do 2 iExists _. iPureIntro; split_and!; try done.
        2: set_solver. 
        by rewrite (Qp.add_comm _ r) Qp.add_comm -Qp.add_assoc.
      + assert (q = qp)%Qp as Hr; last simplify_eq.
        { rewrite -Hlt in Hsum. by eapply Qp.add_inj_l. }
        rewrite Hlt.
        iModIntro. iExists _, _. rewrite insert_id; last done.
        iFrame "Hmapsℓ GCσMLv Hsim GCζauth".
        iExists _, _. iRight. iLeft. iFrame. repeat iSplit; try done.
        1: by do 2 iExists _. by rewrite -Hlen1. }
  iMod "Hmod" as "(%vs&%w'&Hperloc&Hf1&#Hf2&GCσMLv&GCζauth)".
  iPoseProof (lloc_own_auth_get_pub with "[$]") as "#Hf3"; first done.
  iSplitR "Hf1 Hf2 Hf3".
  2: iExists _, _, _; by iFrame "Hf2 Hf1 Hf3".
  iModIntro. do 5 iExists _.
  iFrame "GCζ GCχ GCθ GCroots GCinit GCχauth HSI_GC". iSplit; last done.
  iExists (<[ℓ:=w']> σMLvirt). iFrame.
  repeat iSplit; try done.
  - iApply big_sepM_delete; first done.
    iFrame. iApply GC_per_loc_insert; last iApply GC_per_loc_make_dirty; last done.
    + intros γ' [Hne Hlu]%lookup_delete_Some. eapply Hne, lloc_map_pubs_inj.
      1: apply Hχfuture. all: done.
    + set_solver.
  - iPureIntro. rewrite dom_insert_L. intros ℓ' [Hin%elem_of_singleton|Hin]%elem_of_union.
    2: by apply Hstore.
    simplify_eq; by do 2 eexists.
Qed.

Lemma GC_confront_lloc θ dirty γ (blk:basics.block) : 
    GC θ dirty
 -∗ lstore_own_elem γ (DfracOwn 1) blk
 -∗ GC θ (dirty ∖ {[ γ ]}) ∗ lstore_own_elem γ (DfracOwn 1) blk.
Proof.
  iIntros "HGC Hγ".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lstore_own_elem_of with "GCζauth Hγ") as "%Hγζ".
  destruct (lloc_map_pubs χ_future !! γ) as [ℓ|] eqn:Hχ.
  - iPoseProof (big_sepM_delete with "GC_per_loc") as "(HH&GC_per_loc)"; first done.
    iAssert (per_location_invariant ζ_future σMLvirt (dirty ∖ {[γ]}) γ ℓ 
            ∗ lstore_own_elem γ (DfracOwn 1) blk
            ∗ lstore_own_auth ζ_future )%I with "[HH Hγ GCζauth]" as "(HH&Hγ&GCζauth)".
    { unfold lstore_own_elem.
      iDestruct "HH" as "(%vs'&%lvs'&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&(Hγ'&#Hγsim)&#Hsim&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|HH]]])".
      - simplify_eq. cbn. iFrame "GCζauth Hγ".
        iExists _, _. iLeft. iFrame. done.
      - destruct (mutability blk) eqn:Heqmut.
        1: iPoseProof (pgm_elem_ne with "Hγ Hγ'") as "%Heq"; done.
        iPoseProof (lstore_own_elem_of with "GCζauth Hγ'") as "%Hγ'ζ".
        by simplify_eq.
      - iDestruct "Hmapsγ" as "(Hγ'&_)".
       destruct (mutability blk) eqn:Heqmut.
        1: iPoseProof (pgm_elem_ne with "Hγ Hγ'") as "%Heq"; done.
        iPoseProof (lstore_own_elem_of with "GCζauth Hγ'") as "%Hγ'ζ".
        by simplify_eq.
      - iFrame. iExists vs', lvs'. done. }
    iSplitR "Hγ".
    2: iFrame.
    do 5 iExists _. iFrameNamed.
    iExists _. iFrameNamed.
    iApply big_sepM_delete; first done.
    iFrame "HH".
    iApply GC_per_loc_remove_dirty; try done.
    apply lookup_delete.
  - iSplitR "Hγ".
    2: iFrame.
    do 5 iExists _. iFrameNamed.
    iExists _. iFrameNamed.
    by iApply GC_per_loc_remove_dirty.
Qed.

Lemma GC_confront_MLloc θ dirty γ ℓ fid vs : 
    GC θ dirty
 -∗ ℓ ↦∗ vs
 -∗ γ ~ℓ~ ℓ @ fid
 -∗ GC θ (dirty ∖ {[ γ ]}) ∗ ℓ ↦∗ vs.
Proof.
  iIntros "HGC Hℓ #Hsim".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (pgm_lookup with "GCσMLv Hℓ") as "%Hℓσ".
  iPoseProof (lloc_own_pub_of with "GCχauth Hsim") as "%Hγℓ".
  apply lloc_map_pubs_lookup_Some_2 in Hγℓ as Hmappubs.
  iPoseProof (big_sepM_delete with "GC_per_loc") as "(HH&GC_per_loc)"; first done.
  iAssert (per_location_invariant ζ_future σMLvirt (dirty ∖ {[γ]}) γ ℓ 
          ∗ ℓ ↦∗ vs)%I with "[HH Hℓ]" as "(HH&Hℓ)".
  { iDestruct "HH" as "(%vs'&%lvs'&[(Hℓ'&%HH&Hcanon)|[HH|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim'&%Hsum&%Hdirty)|HH]]])"; cbn.
    - iPoseProof (pgm_elem_ne with "Hℓ Hℓ'") as "%Heq". done.
    - iFrame. iExists vs', lvs'. iRight. iLeft. done.
    - iPoseProof (pgm_elem_ne with "Hℓ Hmapsℓ") as "%Heq". done. 
    - iFrame. iExists vs', lvs'. done. }
  iFrame "Hℓ".
  do 5 iExists _. iFrameNamed.
  iExists _. iFrameNamed.
  iApply big_sepM_delete; first done.
  iFrame "HH".
  iApply GC_per_loc_remove_dirty; try done.
  apply lookup_delete.
Qed.

Lemma GC_confront_both θ dirty q1 γ blk q2 ℓ fid vs : 
    GC θ dirty
 -∗ lstore_own_elem γ (q1) blk
 -∗ ℓ ↦∗{q2} vs
 -∗ γ ~ℓ~ ℓ @ fid
 -∗ ∃ lvs', GC θ dirty ∗ lstore_own_mut γ (q1) blk ∗ ℓ ↦∗{q2} vs ∗ lvs' ~~∗ vs ∗ ⌜blk = Bvblock (Mut, (TagDefault, lvs'))⌝.
Proof.
  iIntros "HGC Hγ Hℓ #Hsim".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (pgm_lookup with "GCσMLv Hℓ") as "%Hℓσ".
  iPoseProof (lstore_own_elem_of with "GCζauth Hγ") as "%Hγζ".
  iPoseProof (lloc_own_pub_of with "GCχauth Hsim") as "%Hγℓ".
  apply lloc_map_pubs_lookup_Some_2 in Hγℓ as Hmappubs.
  iPoseProof (big_sepM_delete with "GC_per_loc") as "(HH&GC_per_loc)"; first done.
  iAssert (∃ lvs', lvs' ~~∗ vs ∗ ⌜blk = Bvblock (Mut, (TagDefault, lvs'))⌝)%I as "#(%lvs&Hsimvs&->)".
  { iDestruct "HH" as "(%vs'&%lvs'&[(Hℓ'&%HH&Hcanon)|[(%Hℓσ'&(Hγ'&#Hγsim)&#Hsim'&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim'&%Hsum&%Hdirty)|(%HH1&%HH2)]]])"; cbn.
    - iPoseProof (pgm_elem_ne with "Hℓ' Hℓ") as "%Heq". done.
    - unfold lstore_own_elem; destruct (mutability blk);
      by iPoseProof (@pgm_elem_ne with "Hγ' Hγ") as "%Heq".
    - iPoseProof (pgm_elem_agree with "Hmapsℓ Hℓ") as "%Heq1"; simplify_eq.
      iDestruct "Hmapsγ" as "(Hmapsγ&_)". cbn.
      unfold lstore_own_elem; destruct (mutability blk) eqn:Heq;
      iPoseProof (@pgm_elem_agree with "Hmapsγ Hγ") as "%Heq2"; simplify_eq.
      iExists _; iFrame "Hsim'". done.
    - by simplify_eq. }
  iExists _.
  iFrame "Hsimvs Hγ Hℓ". iSplit; last done.
  do 5 iExists _. iFrameNamed.
  iExists _. iFrameNamed.
  iApply big_sepM_delete; first done; iFrame.
Qed.

Lemma GC_confront_length_head θ dirty γ head ℓ fid vlen : 
    GC θ dirty
 -∗ γ ↦head head
 -∗ ℓ ↦Mlen vlen
 -∗ γ ~ℓ~ ℓ @ fid
 -∗ ⌜head = Hvblock TagDefault vlen⌝.
Proof.
  iIntros "HGC Hγ #Hℓ #Hsim".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (pgm_lookup_pers with "GCσMLv Hℓ") as "(%vs&->&%Hℓσ)".
  iPoseProof (lstore_own_head_of with "GCζauth Hγ") as "(%b&%Hγζ&%Hhead)".
  iPoseProof (lloc_own_pub_of with "GCχauth Hsim") as "%Hγℓ".
  apply lloc_map_pubs_lookup_Some_2 in Hγℓ as Hmappubs.
  iPoseProof (big_sepM_delete with "GC_per_loc") as "(HH&GC_per_loc)"; first done.
  iDestruct "HH" as "(%vs'&%lvs'&[(Hℓ'&%Hζf&Hcanon)|[(%Hℓσ'&(Hγ'&#Hγsim)&#Hsim'&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim'&%Hsum&%Hdirty)|(%HH1&%HH2)]]])".
  - iPoseProof (pgm_lookup with "GCσMLv Hℓ'") as "%Heq".
    simplify_eq. cbn. by iDestruct (big_sepL2_length with "Hcanon") as %->.
  - iDestruct (lstore_own_elem_of with "GCζauth Hγ'") as %Heq. cbn in *.
    simplify_eq.
    iDestruct (big_sepL2_length with "Hsim'") as %Hlen. by rewrite Hlen.
  - iPoseProof (pgm_elem_pers_agree with "Hmapsℓ Hℓ") as "<-"; simplify_eq.
    iDestruct "Hmapsγ" as "(Hmapsγ&_)". cbn.
    iPoseProof (@pgm_elem_pers_agree with "Hmapsγ Hγ") as "%Heq2".
    rewrite -Heq2.
    iPoseProof (big_sepL2_length with "Hsim'") as "->".
    done.
  - by simplify_eq.
Qed. 

Lemma GC_confront_foreign θ dirty γ fid : 
    GC θ dirty
 -∗ γ ~foreign~ fid
 -∗ GC θ (dirty ∖ {[ γ ]}).
Proof.
  iIntros "HGC #Hfgn".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lloc_own_foreign_of with "GCχauth Hfgn") as "%Hγℓ".
  iPoseProof (GC_per_loc_remove_dirty with "GC_per_loc") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; right; eexists; right; done.
  do 5 iExists _. iFrameNamed.
  iExists _. iFrameNamed.
Qed.

Lemma GC_confront_private θ dirty γ fid dq : 
    GC θ dirty
 -∗ γ ~ℓ~/{dq} @ fid
 -∗ GC θ (dirty ∖ {[ γ ]}) ∗ γ ~ℓ~/{dq} @ fid.
Proof.
  iIntros "HGC Hpriv".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lloc_own_priv_of with "GCχauth Hpriv") as "%Hγℓ".
  iPoseProof (GC_per_loc_remove_dirty with "GC_per_loc") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; do 1 right; eexists; by left.
  iFrame "Hpriv".
  do 5 iExists _. iFrameNamed.
  iExists _. iFrameNamed.
Qed.

Lemma freeze_to_mut γ lvs θ dirty vs :
  ⊢ GC θ dirty ∗ γ ↦fresh (TagDefault, lvs) ∗ block_canon_arr lvs vs ==∗
    GC θ (dirty ∪ {[γ]}) ∗ γ ↦mut (TagDefault, lvs).
Proof using.
  iIntros "(HGC & Hγ & #Hcanon)".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "(Hmtζ & %fid & Hmtfresh)".
  iNamed "HGC". iNamed "HSI_block_level".
  iDestruct (lstore_own_mut_of with "GCζauth Hmtζ") as %[Hζγ _].
  pose (fresh_locs (lloc_map_pub_locs χ_future)) as ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χ_future).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χ_future) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σMLvirt).
  { intros Hℓ.
    destruct (Hstore _ Hℓ) as (γ'&fid'&Hγ'). by eapply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  iDestruct (lloc_own_priv_of with "GCχauth Hmtfresh") as %Hχγ.
  iMod (lloc_own_expose _ _ ℓ with "GCχauth Hmtfresh") as "[GCχvirt #Hℓγ]".
  1: done.
  iMod (pgm_insert (D:=MLHeapPGMData) ℓ vs with "GCσMLv") as "(GCσMLv & HℓNone)".
  1: by eapply not_elem_of_dom_1. 1: done.
  iPoseProof (pgm_elem_to_pers with "HℓNone") as "#Hℓlen".
  iPoseProof (GC_per_loc_insert _ _ _ _ ℓ with "GC_per_loc") as "GC_per_loc".
  1: { intros γ' (fid'&Hγ')%lloc_map_pubs_lookup_Some. apply elem_of_lloc_map_pub_locs_1 in Hγ'. apply H, Hγ'. }
  iPoseProof (GC_per_loc_make_dirty _ _ _ _ (dirty ∪ {[γ]}) with "GC_per_loc") as "GC_per_loc".
  1: set_solver.
  iPoseProof (big_sepM_insert _ _ γ ℓ with "[$GC_per_loc HℓNone]") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; eauto.
  1: { iExists _, lvs; iLeft; iFrame. iFrame "Hcanon". done. } 
  iModIntro. iSplitR "Hℓγ Hmtζ".
  2: { iApply lstore_own_vblock_M_as_mut. iFrame "Hmtζ". eauto. }
  rewrite /GC /SI_block_level /named.
  iExists ζ, ζ_future, χ, (<[γ:=LlocPublic fid ℓ]> χ_future), roots_s.
  iFrame "GCζ GCχ GCθ GCroots GCinit GCχvirt HSI_GC". iSplit; last first.
  { iSplit; first done.
    iPureIntro. eapply expose_llocs_trans; first eassumption.
    eapply expose_llocs_insert; eauto. }
  iExists (<[ℓ:= _]> σMLvirt). rewrite lloc_map_pubs_insert_pub.
  iFrame. iPureIntro; split_and!; eauto.
  + rewrite dom_insert. set_solver.
  + intros ℓ'. rewrite !dom_insert_L elem_of_union elem_of_singleton.
    intros [<-|Hℓ']. 1: by exists fid, γ; simplify_map_eq.
    specialize (Hstore _ Hℓ') as (γ'&fid'&?). exists γ', fid'.
    rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma freeze_to_immut γ lvs θ dirty :
  ⊢ GC θ dirty ∗ γ ↦fresh lvs ==∗
    GC θ dirty ∗ γ ↦imm lvs.
Proof using.
  iIntros "(HGC & Hγ)".
  iDestruct (lstore_own_vblock_F_as_mut with "Hγ") as "(Hmtζ & %fid & Hmtfresh)".
  iNamed "HGC". iNamed "HSI_block_level". iNamed "HSI_GC".
  iDestruct (lstore_own_mut_of with "GCζauth Hmtζ") as %[Hζγ _].
  iDestruct (lloc_own_priv_of with "GCχauth Hmtfresh") as %Hχγ.
  iMod (lstore_own_update _ _ _ (Bvblock (Immut, lvs)) with "GCζauth Hmtζ") as "(GCζauth & Hmtζ)".
  1: by destruct lvs.
  iDestruct (lstore_own_elem_to_immut with "Hmtζ") as "Hmtζ"; first done.
  iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
  1: eapply lloc_map_pubs_lookup_None; right; eexists; left; eapply Hχγ.
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

Lemma GC_lloc_to_fid θ dirty γ dq (blk:basics.block) : 
    GC θ dirty
 -∗ lstore_own_elem γ dq blk
 -∗ (∃ fid, γ ~@~ fid).
Proof.
  iIntros "HGC Hγ".
  iNamed "HGC". iNamed "HSI_block_level".
  iPoseProof (lstore_own_elem_of with "GCζauth Hγ") as "%Hγζ".
  assert (γ ∈ dom χ_future) as (vis&Hγχ)%elem_of_dom by by eapply elem_of_dom_2, elem_of_weaken in Hγζ.
  iExists _. by iApply lloc_own_auth_get_fid.
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



End UpdateLaws.
