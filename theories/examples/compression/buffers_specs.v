From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
From melocoton.interop Require Import lang weakestpre.
From melocoton.language Require Import weakestpre progenv.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.examples.compression Require Import compression_defs.


(** our code differs from the original in the paper as follows:

The paper has a record
------------------
|used_ref|cap|blk|
------------------
  ↓
------
|used|
------
where used_ref is a reference/mutable field

Since we don't have records, only two-value pairs, our value looks as follows (aux_ref is supposed to be another pair)
------------------
|used_ref|aux_ref|
------------------
  ↓          ↓
------   ---------
|used|   |cap|blk|
------   ---------

Additionally, we do not CAMLparam/CAMLlocal variables that
* are integers
* don't have to survive an allocation

Finally, note that the Store_field(&Field(x,y,z)) is syntactic sugar -- no addresses are being taken.
In general, our toy version of C does not have local variables, nor the notion of "taking an address".
Instead, everything that needs to be mutable must be heap-allocated (and preferably freed at the end).
*)

Definition buf_alloc_name := "buf_alloc".
Definition buf_upd_name := "buf_upd".
Definition buf_free_name := "buf_free".
Definition wrap_max_len_name := "wrap_max_len".
Definition wrap_compress_name := "wrap_compress".

Section Specs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition isBufferForeignBlock (γ : lloc) (ℓbuf : loc) (Pb : list (option Z) → iProp Σ) cap fid : iProp Σ := 
      ∃ vcontent, 
        "Hγfgnpto" ∷ γ ↦foreign (#ℓbuf)%CV
      ∗ "#Hγfgnsim" ∷ γ ~foreign~ fid
      ∗ "Hℓbuf" ∷ ℓbuf ↦C∗ (map (option_map (λ (z:Z), #z)) vcontent)
      ∗ "HContent" ∷ Pb vcontent
      ∗ "->" ∷ ⌜cap = length vcontent⌝.

  Lemma isBufferForeignBlock_ext γ ℓbuf Pb1 Pb2 cap fid :
     (∀ lst, (Pb1 lst -∗ Pb2 lst))
  -∗ isBufferForeignBlock γ ℓbuf Pb1 cap fid
  -∗ isBufferForeignBlock γ ℓbuf Pb2 cap fid.
  Proof.
    iIntros "Hiff Hbuf". iNamed "Hbuf".
    iExists vcontent; unfold named; iFrame.
    iFrame "Hγfgnsim". iSplit; last done.
    by iApply "Hiff".
  Qed.

  Definition isBufferRecord (lv : lval) (ℓbuf : loc) (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (γ γref γaux γfgn : lloc) (used : nat) fid,
        "->" ∷ ⌜lv = Lloc γ⌝
      ∗ "#Hγbuf" ∷ γ ↦imm (TagDefault, [Lloc γref; Lloc γaux])
      ∗ "Hγusedref" ∷ γref ↦mut (TagDefault, [Lint used])
      ∗ "#Hγaux" ∷ γaux ↦imm (TagDefault, [Lint cap; Lloc γfgn])
      ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap fid.

  Definition isBufferRecordML (v : MLval) (ℓbuf : loc)  (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (ℓML:loc) (used fid:nat) γfgn, 
      "->" ∷ ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV cap, ML_lang.LitV (LitForeign fid)))%MLV⌝ 
    ∗ "HℓbufML" ∷ ℓML ↦M ML_lang.LitV used
    ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap fid.


  Lemma isBufferRecordML_ext v ℓbuf Pb1 Pb2 cap :
     (∀ z lst, (Pb1 z lst -∗ Pb2 z lst))
  -∗ isBufferRecordML v ℓbuf Pb1 cap
  -∗ isBufferRecordML v ℓbuf Pb2 cap.
  Proof.
    iIntros "Hiff Hbuf". iNamed "Hbuf".
    iExists ℓML, used, fid, γfgn; unfold named; iFrame.
    iSplit; first done.
    iApply (isBufferForeignBlock_ext with "[Hiff] Hbuf").
    iApply "Hiff".
  Qed.

(*

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
    { iExists ℓML, _, fid, γfgn. unfold named.
      iSplit; first done. iFrame "HℓbufML".
      iExists vcontent.
      unfold named. by iFrame "Hγfgnpto Hℓbuf Hγfgnsim HContent". }
    { cbn. iExists _, _, _. iSplitL; first done.
      iFrame "Hγbuf".
      iSplitL; first (iExists _; iSplit; done).
      iExists _, _, _. iSplit; first done.
      iFrame "Hγaux". iSplit; first done.
      iExists _; iSplit; done. }
  Qed.

  Lemma bufToC v ℓbuf Pb c lv θ:
      GC θ
   -∗ isBufferRecordML v ℓbuf Pb c
   -∗ lv ~~ v
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c ∗ ∃ (ℓML:loc) fid, ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))%MLV⌝.
  Proof.
    iIntros "HGC H Hsim". iNamed "H". iNamed "Hbuf".
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&(%ℓvs&%γref2&Hγusedref&#Hsim2&#Hγrefsim))".
    iPoseProof (lloc_own_pub_inj with "Hsim2 Hsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iModIntro. iFrame "HGC". iSplit; last by repeat iExists _. 
    iExists _, _, _, _, _, _. unfold named.
    iSplit; first done.
    iFrame "Hγbuf". iFrame "Hγaux".
    iSplitL "Hγusedref".
    { destruct ℓvs as [|ℓvs [|??]]; cbn; try done.
      all: iDestruct "Hγrefsim" as "[-> ?]"; try done. }
    { cbn. iExists _. unfold named. iFrame "Hγfgnpto Hγfgnsim Hℓbuf HContent".
      iPureIntro; done. }
  Qed.

  Lemma bufToC_fixed ℓbuf Pb (c:nat) ℓML fid lv θ:
      GC θ
   -∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToC with "HGC H Hsim") as "($&$&%ℓML1&%fid1&%Href)". done.
  Qed.

  Lemma bufToML_fixed lv ℓbuf Pb c (ℓML:loc) fid θ:
      GC θ
   -∗ isBufferRecord lv ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
  ==∗ GC θ ∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToML with "HGC H") as "(HGC&%&HML&#Hsim2)".
    iAssert (⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))%MLV⌝)%I as "->"; last by iFrame.
    iNamed "HML".
    cbn.
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iDestruct "Hsim2" as "#(%γ2&%&%&%HHH&Hγbuf2&(%γref2&->&Hsim2)&%γaux2&%&%&->&Hγaux2&->&%γfgn3&->&Hγfgnsim3)".
    simplify_eq.
    unfold lstore_own_vblock, lstore_own_elem; cbn.
    iDestruct "Hγbuf" as "(Hγbuf&_)".
    iDestruct "Hγbuf2" as "(Hγbuf2&_)".
    iDestruct "Hγaux" as "(Hγaux&_)".
    iDestruct "Hγaux2" as "(Hγaux2&_)".
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
    iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim3 HGC") as "(HGC&%Heq1)"; simplify_eq.
    iPoseProof (lloc_own_pub_inj with "Hsim Hsim2 HGC") as "(HGC&%Heq2)"; simplify_eq.
    iPureIntro. f_equal; repeat f_equal.
    - symmetry; by eapply Heq2.
    - symmetry; by eapply Heq1.
  Qed.
*)

  Import melocoton.ml_lang.notation.
  Definition buf_alloc_res_buffer z cap (b : list (option Z)) : iProp Σ := ⌜cap = 0⌝ ∗ ⌜b = replicate (Z.to_nat z) None⌝.
  Definition buf_alloc_spec_ML s vv Φ : iProp Σ :=
    ∃ (z:Z),
      "%Hb1" ∷ ⌜(0 < z)%Z⌝
    ∗ "->" ∷ ⌜s = buf_alloc_name⌝
    ∗ "->" ∷ ⌜vv = [ #z ]⌝
    ∗ "HCont" ∷ ▷ (∀ v ℓbuf, isBufferRecordML v ℓbuf (buf_alloc_res_buffer z) (Z.to_nat z) -∗ meta_token ℓbuf ⊤ -∗ Φ v).

  Definition buf_alloc1_spec idx vnew Pbold cap (b : list (option Z)) : iProp Σ :=
    ∃ bold (capold:nat) , ⌜b = <[ Z.to_nat idx := Some vnew ]> bold⌝ ∗ ⌜cap = max capold (Z.to_nat (idx+1))⌝ ∗ Pbold capold bold.
  Definition buf_update_spec_ML (protoCB : (protocol ML_lang.val Σ)) s vv Φ: iProp Σ :=
    ∃ (Ψ Ψframe : Z → iProp Σ) (Φz : Z → Z → iProp Σ) (i j : Z) ℓbuf (cap:nat) (Pb : Z → nat → _ → iProp Σ) vbuf b1 b2 (F : ML_lang.expr),
      "->" ∷ ⌜s = buf_upd_name⌝
    ∗ "->" ∷ ⌜vv = [ #i; #j; (RecV b1 b2 F); vbuf ]⌝
    ∗ "%Hb1" ∷ ⌜0%Z ≤ i⌝%Z
    ∗ "%Hb2" ∷ ⌜i ≤ j+1⌝%Z
    ∗ "%Hb3" ∷ ⌜j < cap⌝%Z
    ∗ "#HMerge" ∷ (□ ∀ z vnew, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j+1⌝%Z -∗ Ψframe z -∗ Φz z vnew -∗
          isBufferRecordML vbuf ℓbuf (buf_alloc1_spec z vnew (Pb z)) cap ==∗ Ψ (z+1)%Z)
    ∗ "#HWP" ∷ (□ ▷ ∀ z, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j⌝%Z -∗ Ψ z -∗ 
              WP (RecV b1 b2 F) #z at ⟨ ∅, protoCB ⟩
              {{res, ∃ (znew:Z), ⌜res = #znew⌝ ∗ Φz z znew ∗ Ψframe (z)%Z
                               ∗ isBufferRecordML vbuf ℓbuf (Pb (z)%Z) cap}})
    ∗ "Hframe" ∷ Ψframe i
    ∗ "Hrecord" ∷ isBufferRecordML vbuf ℓbuf (Pb i) cap
    ∗ "HMergeInitial" ∷ (Ψframe i ∗ isBufferRecordML vbuf ℓbuf (Pb i) cap ==∗ Ψ i)
    ∗ "HCont" ∷ ▷ (Ψ (j+1)%Z -∗ Φ #()).

  Definition wrap_max_len_spec_ML s vv Φ : iProp Σ :=
    ∃ (n:nat),
      "->" ∷ ⌜s = wrap_max_len_name⌝
    ∗ "->" ∷ ⌜vv = [ #n ]⌝
    ∗ "HCont" ∷ ▷ Φ #(buffer_max_len n).

  Definition wrap_compress_spec_ML s vv Φ : iProp Σ :=
    ∃ v1 v2 ℓ1 ℓ2 (vcompress:buffer) vrest1 Pb1 Pb2 cap1 cap2,
      "->" ∷ ⌜s = wrap_compress_name⌝
    ∗ "->" ∷ ⌜vv = [ v1 ; v2 ]⌝
    ∗ "%Hcap" ∷ ⌜buffer_max_len (length vcompress) ≤ cap2⌝
    ∗ "HBuf1" ∷ isBufferRecordML v1 ℓ1 (λ z vb, ⌜vb = map Some vcompress ++ vrest1⌝ ∗ ⌜length vcompress = z⌝ ∗ Pb1 z vb) cap1
    ∗ "HBuf2" ∷ isBufferRecordML v2 ℓ2 Pb2 cap2
    ∗ "HCont" ∷ ▷   ( isBufferRecordML v1 ℓ1 (λ z vb, ⌜vb = map Some vcompress ++ vrest1⌝ ∗ ⌜length vcompress = z⌝ ∗ Pb1 z vb) cap1
                   -∗ isBufferRecordML v2 ℓ2 (λ z vb, ∃ vov vrest zold, ⌜vb = map Some (compress_buffer vcompress) ++ vrest⌝  
                                                      ∗ ⌜length (compress_buffer vcompress) = z⌝ ∗ ⌜length vov = z⌝
                                                      ∗ Pb2 zold (vov ++ vrest)) cap2
                   -∗ Φ #true).

  Definition buf_free_spec_ML s vv Φ : iProp Σ :=
    ∃ v ℓ Pb cap,
      "->" ∷ ⌜s = buf_free_name⌝
    ∗ "->" ∷ ⌜vv = [ v ]⌝
    ∗ "Hbuf" ∷ isBufferRecordML v ℓ Pb cap
    ∗ "HCont" ∷ ▷   ( ∀ (ℓML:loc) fid γfgn, ⌜v = (# ℓML, (# cap, # (LitForeign fid)))%MLV⌝ -∗
                                            γfgn ~foreign~ fid -∗ ℓML ↦M #(-1) -∗
                                            γfgn ↦foreign (C_intf.LitV LitNull) -∗ Φ #()).

  Definition buf_library_spec_ML_pre : (protocol ML_lang.val Σ) -d> (protocol ML_lang.val Σ) := λ (protoCB : (protocol ML_lang.val Σ)),
    buf_alloc_spec_ML ⊔ buf_update_spec_ML protoCB ⊔ buf_free_spec_ML ⊔ wrap_compress_spec_ML ⊔ wrap_max_len_spec_ML.

  Global Instance buf_library_spec_ML_contractive : Contractive buf_library_spec_ML_pre.
  Proof.
    rewrite /buf_library_spec_ML_pre /= => n pp1 pp2 Hpp.
    do 4 f_equiv.
    unfold buf_update_spec_ML, named.
    do 35 first [intros ?|f_equiv]. f_contractive.
    do 5 first [intros ?|f_equiv].
    eapply wp_ne_proto. done.
  Qed.

  Lemma buf_library_spec_ML_pre_mono Ψ1 Ψ2 : Ψ1 ⊑ Ψ2 →
    buf_library_spec_ML_pre Ψ1 ⊑ buf_library_spec_ML_pre Ψ2.
  Proof.
    iIntros (HΨ s vv Φ) "[[[[H|H]|H]|H]|H]".
    - do 4 iLeft. done.
    - do 3 iLeft; iRight. iNamed "H". unfold buf_update_spec_ML.
      iExists Ψ, Ψframe, Φz, i, j, ℓbuf.
      iExists cap, Pb, vbuf, b1, b2, F.
      iFrame "HCont HMergeInitial Hrecord Hframe HMerge".
      repeat (iSplit; first done).
      iIntros "!> !> %z HH1 HH2 HH3".
      iSpecialize ("HWP" $! z with "HH1 HH2 HH3").
      iApply (wp_strong_mono with "HWP"). 1-2: done. by iIntros (v) "$".
    - do 2 iLeft; by iRight.
    - do 1 iLeft; by iRight.
    - do 0 iLeft; by iRight.
  Qed.

End Specs.

