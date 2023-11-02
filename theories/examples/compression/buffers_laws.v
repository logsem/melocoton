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

  Lemma bufToML lv ℓbuf Pb c θ:
      GC θ
   -∗ isBufferRecord lv ℓbuf Pb c
  ==∗ GC θ ∗ ∃ v, isBufferRecordML v ℓbuf Pb c ∗ lv ~~ v.
  Proof.
    iIntros "HGC H". iNamed "H". iNamed "Hbuf".
    iMod (mut_to_ml _ ([ML_lang.LitV used]) with "[$HGC $Hγusedref]") as "(HGC&(%ℓML&HℓbufML&#HγML))".
    1: by cbn.
    iModIntro. iFrame "HGC".
    iExists _. iSplitL.
    { iExists ℓML, _, γfgn. unfold named.
      iSplit; first done. iFrame "HℓbufML".
      iExists vcontent.
      unfold named. by iFrame "Hγfgnpto Hℓbuf HContent". }
    { cbn. iExists _, _, _. iSplitL; first done.
      iFrame "Hγbuf".
      iSplitL; first (iExists _; iSplit; done).
      iExists _, _, _. iSplit; first done.
      iFrame "Hγaux". iSplit; done. }
  Qed.

  Lemma bufToC v ℓbuf Pb c lv θ:
      GC θ
   -∗ isBufferRecordML v ℓbuf Pb c
   -∗ lv ~~ v
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c ∗ ∃ (ℓML:loc) γ, ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ)))%MLV⌝.
  Proof.
    iIntros "HGC H Hsim". iNamed "H". iNamed "Hbuf".
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&->)".
    iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&(%ℓvs&%γref2&Hγusedref&#Hsim2&#Hγrefsim))".
    iPoseProof (lloc_own_pub_inj with "Hsim2 Hsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iModIntro. iFrame "HGC". iSplit; last by repeat iExists _. 
    iExists _, _, _, _, _. unfold named.
    iSplit; first done.
    iFrame "Hγbuf". iFrame "Hγaux".
    iSplitL "Hγusedref".
    { destruct ℓvs as [|ℓvs [|??]]; cbn; try done.
      all: iDestruct "Hγrefsim" as "[-> ?]"; try done. }
    { cbn. iExists _. unfold named. iFrame "Hγfgnpto Hℓbuf HContent".
      iPureIntro; done. }
  Qed.

  Lemma bufToC_fixed ℓbuf Pb (c:nat) ℓML γ lv θ:
      GC θ
   -∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ))) ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ)))
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToC with "HGC H Hsim") as "($&$&%ℓML1&%fid1&%Href)". done.
  Qed.

  Lemma bufToML_fixed lv ℓbuf Pb c (ℓML:loc) γ θ:
      GC θ
   -∗ isBufferRecord lv ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ)))
  ==∗ GC θ ∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ))) ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToML with "HGC H") as "(HGC&%&HML&#Hsim2)".
    iAssert (⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign γ)))%MLV⌝)%I as "->"; last by iFrame.
    iNamed "HML".
    cbn.
    iDestruct "Hsim" as "#(%γ1&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&->)".
    iDestruct "Hsim2" as "#(%γ2&%&%&%HHH&Hγbuf2&(%γref2&->&Hsim2)&%γaux2&%&%&->&Hγaux2&->&->)".
    simplify_eq.
    unfold lstore_own_vblock, lstore_own_elem; cbn.
    iDestruct "Hγbuf" as "(Hγbuf&_)".
    iDestruct "Hγbuf2" as "(Hγbuf2&_)".
    iDestruct "Hγaux" as "(Hγaux&_)".
    iDestruct "Hγaux2" as "(Hγaux2&_)".
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
    iPoseProof (lloc_own_pub_inj with "Hsim Hsim2 HGC") as "(HGC&%Heq2)"; simplify_eq.
    iPureIntro. f_equal; repeat f_equal.
    - symmetry; by eapply Heq2.
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
