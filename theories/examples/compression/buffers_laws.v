From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
From melocoton.interop Require Import lang update_laws weakestpre.
From melocoton.language Require Import weakestpre progenv.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.examples.compression Require Import buffers_specs.


Section Specs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Lemma bufToML lv ℓbuf Pb c θ roots:
      GC θ roots
   -∗ isBufferRecord lv ℓbuf Pb c
  ==∗ GC θ roots ∗ ∃ v, isBufferRecordML v ℓbuf Pb c ∗ lv ~~ v.
  Proof.
    iIntros "HGC H". iNamed "H". iNamed "Hbuf".
    iMod (mut_to_ml_store _ ([ML_lang.LitV used]) with "[$HGC $Hγusedref]") as "(HGC&(%fidℓ&%ℓML&HℓbufML&#HγML))".
    1: by cbn.
    iModIntro. iFrame "HGC".
    iExists _. iSplitL.
    { iExists ℓML, _, fid, γfgn. unfold named.
      iSplit; first done. iFrame "HℓbufML".
      iExists vcontent.
      unfold named. by iFrame "Hγfgnpto Hℓbuf Hγfgnsim HContent". }
    { cbn. iExists _, _, _. iSplitL; first done.
      iFrame "Hγbuf".
      iSplitL; first (iExists _, _; iSplit; done).
      iExists _, _, _. iSplit; first done.
      iFrame "Hγaux". iSplit; first done.
      iExists _; iSplit; first done. by iPoseProof (pgm_elem_to_pers with "Hγfgnsim") as "$". }
  Qed.

  Lemma bufToC v ℓbuf Pb c lv θ roots:
      GC θ roots
   -∗ isBufferRecordML v ℓbuf Pb c
   -∗ lv ~~ v
  ==∗ ∃ fidℓ (ℓML:loc) fid γ, GC θ (roots ∪ {[γ]}) ∗ isBufferRecord lv ℓbuf Pb c ∗ ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))%MLV⌝ ∗ γ ~ℓ~ ℓML @ fidℓ.
  Proof.
    iIntros "HGC H Hsim". iNamed "H". iNamed "Hbuf".
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&%fidℓ&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iPoseProof (pgm_elem_to_pers with "Hγfgnsim") as "#Hγfgnsim'".
    iDestruct (lloc_own_fid_inj with "Hγfgnsim2 Hγfgnsim'") as %[_ Heq].
    specialize (Heq eq_refl); simplify_eq.
    iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(%ℓvs&%γref2&%fid2'&HGC&Hγusedref&#Hsim2&#Hγrefsim)".
    iDestruct (lloc_own_pub_inj_2 with "Hsim2 Hsim []") as "%Hiff". 1: by iLeft.
    subst γref2.
    iModIntro. do 4 iExists _.
    iFrame "HGC Hsim". iSplit; last done.
    iExists _, _, _, _, _, _. unfold named.
    iSplit; first done.
    iFrame "Hγbuf". iFrame "Hγaux".
    iSplitL "Hγusedref".
    { destruct ℓvs as [|ℓvs [|??]]; cbn; try done.
      all: iDestruct "Hγrefsim" as "[-> ?]"; try done. }
    { cbn. iExists _. unfold named. iFrame "Hγfgnpto Hγfgnsim Hℓbuf HContent".
      iPureIntro; done. }
  Qed.

  Lemma bufToC_fixed ℓbuf Pb (c:nat) (ℓML:loc) fidℓ γ fid lv θ roots :
      GC θ roots
   -∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
   -∗ γ ~ℓ~ ℓML @ fidℓ
  ==∗ GC θ (roots ∪ {[γ]}) ∗ isBufferRecord lv ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim #Hsim2".
    iMod (bufToC with "HGC H Hsim") as "(%fidℓ2&%ℓML1&%fid1&%γ1&HGC&$&%Href&#Hsimm)". simplify_eq.
    iModIntro.
    iDestruct (lloc_own_pub_inj_2 with "Hsim2 Hsimm []") as %<-. 1: by iLeft. done.
  Qed.

  Lemma bufToML_fixed lv ℓbuf Pb c (ℓML:loc) fidℓ γ fid θ roots :
      GC θ roots
   -∗ isBufferRecord lv ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
   -∗ γ ~ℓ~ ℓML @ fidℓ
  ==∗ GC θ (roots ∖ {[γ]}) ∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim #Hsimgam".
    iMod (bufToML with "HGC H") as "(HGC&%&HML&#Hsim2)".
    iNamed "HML". rename γ into γinp.
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&%fidref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iDestruct "Hsim2" as "#(%γ2&%&%&%HHH&Hγbuf2&(%γref2&%fidref2&->&Hsim2)&%γaux2&%&%&->&Hγaux2&->&%γfgn3&->&Hγfgnsim3)".
    simplify_eq.
    unfold lstore_own_vblock, lstore_own_elem; cbn.
    iDestruct "Hγbuf" as "(Hγbuf&_)".
    iDestruct "Hγbuf2" as "(Hγbuf2&_)".
    iDestruct "Hγaux" as "(Hγaux&_)".
    iDestruct "Hγaux2" as "(Hγaux2&_)".
    iPoseProof (pgm_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
    iPoseProof (pgm_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
    iDestruct (lloc_own_fid_inj with "Hγfgnsim2 Hγfgnsim3") as %[Heq1 _]; specialize (Heq1 eq_refl); simplify_eq.
    iDestruct (lloc_own_pub_inj_1 with "Hsim Hsim2 [//]") as %(Heq2&Heq2b); simplify_eq.
    iDestruct (lloc_own_pub_inj_2 with "Hsimgam Hsim []") as %Heq3; first by iLeft. simplify_eq.
    iPoseProof (GC_confront_MLloc with "HGC HℓbufML Hsim2") as "($&HℓbufML)".
    iModIntro.
    repeat iExists _. iSplit; first done. iFrame.
  Qed.

End Specs.

Section LemmasThatShouldBeInStdPP.

  Lemma map_replicate {A B : Type} (f : A → B) (v:A) n : map f (replicate n v) = replicate n (f v).
  Proof.
    induction n as [|n IH]; cbn; firstorder congruence.
  Qed.

  Lemma map_insert {A B : Type} (vpre : A) (f : A → B) (k : nat) (v : B) lst :
    v = f vpre →
    k < length lst →
    <[ k := v ]> (map f lst) = map f (<[ k := vpre ]> lst).
  Proof.
    intros Hv.
    induction lst as [|lh lr IH] in k|-*.
    1: cbn; lia.
    destruct k as [|k].
    - intros _. cbn. by subst v.
    - cbn. intros H%Nat.succ_lt_mono. by rewrite IH.
  Qed.

End LemmasThatShouldBeInStdPP.
