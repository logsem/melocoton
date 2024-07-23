From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
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


  Lemma buf_get_correct Ψ :
    prims_proto Ψ ||- buf_lib_prog :: wrap_proto (buf_get_spec_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done.
    iIntros (Φ'') "HΦ".
    destruct lvs as [|lvb [|lvi [|??]]]; first done.
    all: cbn; iDestruct "Hsim" as "(Hsimb&H)"; try done.
    all: cbn; iDestruct "H" as "(->&H)"; try done.
    destruct ws as [|wb [|wl [|??]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wγ&?&Hlγ&Hrepr&?); simplify_eq.
    eapply Forall2_cons_inv_l in Hrepr as (wi&?&Hli&Hrepr&?); simplify_eq.
    cbn. wp_call_direct.

    iMod (bufToC with "HGC Hbuf Hsimb") as "(HGC&HBuf1&%&%&->)".
    iNamed "HBuf1". iNamed "Hbuf".
    iDestruct "HContent" as "(HContent&%Heqres)".
    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγaux1 wγaux1) "(HGC&_&%Heq1&%Hreprγaux1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (vγfgn1 wγfgn1) "(HGC&_&%Heq1&%Hreprγfgn1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.

    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_load_offset with "Hℓbuf").
    { change (map ?a ?b) with (@fmap _ list_fmap _ _ a b). rewrite list_lookup_fmap Heqres.
      cbn; done. }
    iIntros "Hℓbuf".
    iApply (wp_post_mono _ _ _
      (λ o : outcome word,
       (∃ w : word, ⌜o = OVal w⌝ ∗ GC θ ∗ ⌜repr_lval θ (Lint res) w⌝)%I) with "[HGC]").
    { wp_apply (wp_int2val with "HGC"); try done. iIntros (w) "[HGC %Hr]".
      iExists w. iFrame. iSplit; done. }
    iIntros (o) "(%w&->&HGC&%Hww)".
    iMod (bufToML_fixed with "HGC [Hγusedref HContent Hγfgnpto Hℓbuf] Hsimb") as "(HGC&HBuffer)"; last first.
    { iModIntro. iApply "HΦ".
      iApply ("Return" $! _ _ (OVal (Lint res)) with "HGC Hfc (HCont HBuffer) [//] [//]"). }
    { do 5 iExists _. iSplit; first done. iFrameNamed.
      do 1 iExists _. iFrameNamed. done. }
  Qed.

End Proofs.
