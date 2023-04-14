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
From melocoton.examples.compression Require Import buffers_specs buffers_laws buffers_code compression_specs.

Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Notation combspec Ψ := (buffy_library_spec ⊔ prims_proto Ψ).

  Lemma prims_proto_refines_combspec Ψ : prims_proto Ψ ⊑ combspec Ψ.
  Proof using.
    iIntros (s vv Φ) "H". by iRight.
  Qed.

  Local Ltac mdone := match goal with
    [ |- ?p ⊑ combspec ?Ψ ] => eapply proto_refines_transitive; [|apply prims_proto_refines_combspec]; done
    | _ => done end.

  Lemma wrap_max_len_correct Ψ :
    combspec Ψ ||- buf_lib_prog :: wrap_proto (wrap_max_len_spec_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. wp_call_direct.

    wp_apply (wp_val2int with "HGC"); [mdone..|].
    iIntros "HGC".
    wp_extern.
    iModIntro. iLeft. iLeft. iLeft. iExists _. unfold named.
    iSplit; first done.
    iSplit; first done. iNext. wp_finish.
    wp_apply (wp_int2val with "HGC"); [mdone..|].
    iIntros (w) "(HGC&%Hrepr)".
    iApply "HΦ". iApply ("Cont" with "HGC HCont [//] [//]").
  Qed.

  Lemma wrap_compress_correct Ψ :
    combspec Ψ ||- buf_lib_prog :: wrap_proto (wrap_compress_spec_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    destruct lvs as [|lv1 [|lv2 [|??]]]; first done.
    all: cbn; iDestruct "Hsim" as "(Hsim1&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsim2&Hsim)"; try done.
    destruct ws as [|w1 [|w2 [|??]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons in Hrepr as (Hrepr1&Hrepr).
    eapply Forall2_cons in Hrepr as (Hrepr2&Hrepr).
    cbn. wp_call_direct.

    iMod (bufToC with "HGC HBuf1 Hsim1") as "(HGC&HBuf1&%&%&->)".
    iNamed "HBuf1". iNamed "Hbuf".
    iMod (bufToC with "HGC HBuf2 Hsim2") as "(HGC&HBuf2&%&%&->)".
    iDestruct "HBuf2" as "(%γ2&%γref2&%γaux2&%γfgn2&%used2&%fid2&->&#Hγbuf2&Hγusedref2&#Hγaux2&Hbuf2)".
    unfold named.
    iDestruct "Hbuf2" as "(%vcontent2&Hγfgnpto2&#Hγfgnsim2&Hℓbuf2&HContent2&->)". unfold named.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [mdone..|].
    iIntros (vγaux1 wγaux1) "(HGC&_&%Heq1&%Hreprγaux1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [mdone..|].
    iIntros (vγfgn1 wγfgn1) "(HGC&_&%Heq1&%Hreprγfgn1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [mdone..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [mdone..|].
    iIntros (vγaux2 wγaux2) "(HGC&_&%Heq1&%Hreprγaux2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux2]"); [mdone..|].
    iIntros (vγfgn2 wγfgn2) "(HGC&_&%Heq1&%Hreprγfgn2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto2]"); [mdone..|].
    iIntros "(HGC&Hγfgnpto2)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [mdone..|].
    iIntros (vγref1 wγref1) "(HGC&_&%Heq1&%Hreprγref1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγusedref]"); [mdone..|].
    iIntros (vv wused) "(HGC&Hγusedref&%Heq1&%Hreprwused)". change (Z.to_nat 0) with 0 in Heq1; cbn in Heq1; simplify_eq.
    wp_apply (wp_val2int with "HGC"); [mdone..|].
    iIntros "HGC". wp_pure _.
    wp_apply wp_Malloc; [mdone..|]. change (Z.to_nat 1) with 1. cbn.
    iIntros (ℓcap2) "(Hℓcap2&_)". rewrite loc_add_0.
    wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [mdone..|].
    iIntros (vγaux2' wγaux2') "(HGC&_&%Heq1&%Hreprγaux2')". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux2]"); [mdone..|].
    iIntros (vv wcap) "(HGC&_&%Heq1&%Hreprcap2)". change (Z.to_nat 0) with 0 in Heq1; cbn in Heq1; simplify_eq.
    wp_apply (wp_val2int with "HGC"); [mdone..|].
    iIntros "HGC".
    wp_apply (wp_store with "Hℓcap2"). iIntros "Hℓcap2".
    wp_pure _.
    iDestruct "HContent" as "(->&<-&HContent)".
    rewrite map_app.
    iPoseProof (array_app with "Hℓbuf") as "(Hℓbuf&Hℓbufuninit)".
    wp_extern.
    iModIntro. iLeft. iLeft. iRight. do 6 iExists _. unfold named.
    iSplit; first done.
    iSplit; first done.
    iFrame "Hℓbuf Hℓbuf2". rewrite !map_length !map_map.
    iSplit; first (iPureIntro; lia).
    iSplit; first done. iFrame "Hℓcap2".
    iNext.
    iIntros (bout vout vrest vov Hbufout).
    iIntros "-> %Hvov %Hlen Hℓbuf2 Hℓbuf Hℓcap2". wp_finish.
      apply map_eq_app in Hvov as (zvov&zvrest&->&<-&<-).
      unfold isBuffer in Hbufout. subst vout.
      rewrite !map_length in Hlen. rewrite !map_length.

      wp_pure _.
      wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [mdone..|].
      iIntros (vγref2 wγref2) "(HGC&_&%Heq1&%Hreprγref2)". cbv in Heq1; simplify_eq.
      wp_apply (wp_load with "Hℓcap2"). iIntros "Hℓcap2".
      wp_apply (wp_int2val with "HGC"); [mdone..|].
      iIntros (w0) "(HGC&%Hrepr0)".
      wp_apply (wp_modify with "[$HGC $Hγusedref2]"); [mdone..|].
      iIntros "(HGC&Hγusedref2)". wp_pure _.
      wp_apply (wp_free with "Hℓcap2"). iIntros "_".
      do 2 wp_pure _.
      rewrite bool_decide_decide; destruct decide; try done.
      wp_pure _. iApply (wp_post_mono with "[HGC]").
      1: wp_apply (wp_int2val with "HGC"); [mdone..|iIntros (w) "H"; iAccu].
      iIntros (ww1) "(HGC&%Hreprw1)".
      iMod (bufToML_fixed with "HGC [Hγusedref Hγfgnpto Hℓbuf Hℓbufuninit HContent] Hsim1") as "(HGC&HBuf1)"; last first.
      1: iMod (bufToML_fixed with "HGC [Hγusedref2 Hγfgnpto2 Hℓbuf2 HContent2] Hsim2") as "(HGC&HBuf2)"; last first.
      1: iApply "HΦ".
      1: iApply ("Cont" $! _ (ML_lang.LitV true) with "HGC (HCont HBuf1 HBuf2) [//] [//]").
      { iExists _, _, _, _, _, _. unfold named.
        iSplit; first done.
        change (Z.to_nat 0) with 0; cbn.
        iFrame "Hγbuf2 Hγaux2 Hγusedref2".
        iExists _. unfold named.
        iFrame "Hγfgnpto2 Hγfgnsim2".
        iSplitL "Hℓbuf2"; last first.
        - iSplit.
          1: iExists _, zvrest, _.
          1: repeat (iSplit; first done); iApply "HContent2".
          iPureIntro. rewrite !app_length !map_length Hlen //.
        - rewrite !map_app !map_map. cbn. done.
      }
      { iExists _, _, _, _, _, _. unfold named.
        iSplit; first done.
        iFrame "Hγbuf Hγaux Hγusedref".
        iExists _. unfold named.
        iFrame "Hγfgnpto Hγfgnsim". iSplitR "HContent".
        2: { iSplit; [iSplit; [|iSplit]|]. 3: iApply "HContent".
             all: done. }
        rewrite map_app. iApply array_app. rewrite !map_length. rewrite !map_map. iFrame. }
  Qed.

End Proofs.
