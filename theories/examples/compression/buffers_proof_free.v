From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From melocoton.examples.compression Require Import buffers_specs buffers_laws buffers_code.

Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.


  Lemma buf_free_correct Ψ :
    prims_proto Ψ ||- buf_lib_prog :: wrap_proto (buf_free_spec_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done.
    iIntros (Φ'') "HΦ".
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(Hsim&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wγ&?&Hlγ&_&?); simplify_eq.
    cbn. wp_call_direct.

    iMod (bufToC with "HGC Hbuf Hsim") as "(HGC&HBuf1&%&%&->)".
    iNamed "HBuf1". iNamed "Hbuf".
    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγaux1 wγaux1) "(HGC&_&%Heq1&%Hreprγaux1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (vγfgn1 wγfgn1) "(HGC&_&%Heq1&%Hreprγfgn1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγref1 wγref1) "(HGC&_&%Heq1&%Hreprγref1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (vv wcap) "(HGC&_&%Heq1&%Hreprwcap)". change (Z.to_nat 0) with 0 in Heq1; cbn in Heq1; simplify_eq.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_pure _; first by destruct ℓ. do 2 wp_pure _.
    replace (length vcontent) with 
      (length (map (option_map (λ z : Z, #z)) vcontent)) by by rewrite map_length.
    wp_apply (wp_free_array with "Hℓbuf"). iIntros "_".
    wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγaux2 wγaux2) "(HGC&_&%Heq1&%Hreprγaux2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (vγfgn2 wγfgn2) "(HGC&_&%Heq1&%Hreprγfgn2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγref2 wγref2) "(HGC&_&%Heq1&%Hreprγref2)". cbv in Heq1; simplify_eq.
    cbn. wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (wnum) "(HGC&%Hreprm1)".
    wp_apply (wp_modify with "[$HGC $Hγusedref]"); [done..|].
    change (Z.to_nat 0) with 0. cbn.
    iIntros "(HGC&Hγusedref)". wp_pure _.
    iApply (wp_post_mono _ _ _
      (λ o, ∃ w, ⌜o = OVal w⌝ ∗ GC θ ∗ ⌜repr_lval θ (Lint 0) w⌝)%I with "[HGC]").
    { wp_apply (wp_int2val with "HGC"); try done.
      iIntros (w) "?". iExists w. iFrame. done. }
    iIntros (o) "(%w&->&HGC&%Hwunit)".
    iMod (mut_to_ml _ [ #ML (-1)%Z ] _ with "[$HGC $Hγusedref]") as "(HGC&%ℓML'&Hγusedref&#Hsim')". 1: cbn; iFrame; done.

    iAssert (⌜ℓML' = ℓML⌝ ∧ ⌜γfgn = γ⌝)%I as "(-> & ->)".
    { iDestruct "Hsim" as "(%γ2&%&%&%&Hγbuf2&(%&%&Hsim2)&(%&%&%&%&Hγaux2&%&%))". simplify_eq.
      unfold lstore_own_vblock, lstore_own_elem; cbn.
      iDestruct "Hγbuf" as "(Hγbuf&_)".
      iDestruct "Hγbuf2" as "(Hγbuf2&_)".
      iDestruct "Hγaux" as "(Hγaux&_)".
      iDestruct "Hγaux2" as "(Hγaux2&_)".
      iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
      iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
      iPoseProof (lloc_own_pub_inj with "Hsim' Hsim2") as "%Heq2"; simplify_eq.
      iPureIntro; split; [by eapply Heq2 | done].
    }
    iModIntro.
    iApply "HΦ".
    iApply ("Return" $! _ (OVal (#ML ()))%MLV (OVal (Lint 0)) with "HGC [-] [//] [//]").
    iApply ("HCont" with "[//] Hγusedref [$]").
  Qed.

End Proofs.
