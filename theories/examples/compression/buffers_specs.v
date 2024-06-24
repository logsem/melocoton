From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre.
From melocoton.language Require Import weakestpre progenv.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.examples.compression Require Import compression_defs.


(** our code differs from the original in the paper as follows:

The paper has a record
<<
------------------
|used_ref|cap|blk|
------------------
  ↓
------
|used|
------
>>
where used_ref is a reference/mutable field

Since we don't have records, only two-value pairs, our value looks as follows (aux_ref is supposed to be another pair)
<<
------------------
|used_ref|aux_ref|
------------------
  ↓          ↓
------   ---------
|used|   |cap|blk|
------   ---------
>>
Additionally, we do not CAMLparam/CAMLlocal variables that
- are integers
- don't have to survive an allocation

Finally, note that the Store_field(&Field(x,y,z)) is syntactic sugar -- no addresses are being taken.

In general, our toy version of C does not have local variables, nor the notion of "taking an address".
Instead, everything that needs to be mutable must be heap-allocated (and preferably freed at the end).
*)

Definition buf_alloc_name := "buf_alloc".
Definition buf_upd_name := "buf_upd".
Definition buf_free_name := "buf_free".
Definition buf_get_name := "buf_get".
Definition wrap_max_len_name := "wrap_max_len".
Definition wrap_compress_name := "wrap_compress".

Section Specs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition isBufferForeignBlock (γ : lloc) (ℓbuf : loc) (Pb : list (option Z) → iProp Σ) cap : iProp Σ :=
      ∃ vcontent, 
        "Hγfgnpto" ∷ γ ↦foreign[Mut] (#ℓbuf)%CV
      ∗ "Hℓbuf" ∷ ℓbuf I↦C∗ (map (option_map (λ (z:Z), #z)) vcontent)
      ∗ "HContent" ∷ Pb vcontent
      ∗ "->" ∷ ⌜cap = length vcontent⌝.

  Lemma isBufferForeignBlock_ext γ ℓbuf Pb1 Pb2 cap :
     (∀ lst, ⌜length lst = cap⌝ -∗ (Pb1 lst -∗ Pb2 lst))
  -∗ isBufferForeignBlock γ ℓbuf Pb1 cap
  -∗ isBufferForeignBlock γ ℓbuf Pb2 cap.
  Proof.
    iIntros "Hiff Hbuf". iNamed "Hbuf".
    iExists vcontent; unfold named; iFrame.
    iSplit; last done.
    by iApply "Hiff".
  Qed.

  Definition isBufferRecord (lv : lval) (ℓbuf : loc) (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (γ γref γaux γfgn : lloc) (used : nat),
        "->" ∷ ⌜lv = Lloc γ⌝
      ∗ "#Hγbuf" ∷ γ ↦imm (TagDefault, [Lloc γref; Lloc γaux])
      ∗ "Hγusedref" ∷ γref ↦mut (TagDefault, [Lint used])
      ∗ "#Hγaux" ∷ γaux ↦imm (TagDefault, [Lint cap; Lloc γfgn])
      ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap.

  Definition isBufferRecordML (v : MLval) (ℓbuf : loc)  (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (ℓML:loc) (used:nat) γfgn,
      "->" ∷ ⌜v = (#ML ℓML, (#ML cap, #ML (LitForeign γfgn)))%MLV⌝
    ∗ "HℓbufML" ∷ ℓML ↦M (#ML used)
    ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap.


  Lemma isBufferRecordML_ext v ℓbuf Pb1 Pb2 cap :
     (∀ z lst, ⌜length lst = cap⌝ -∗ (Pb1 z lst -∗ Pb2 z lst))
  -∗ isBufferRecordML v ℓbuf Pb1 cap
  -∗ isBufferRecordML v ℓbuf Pb2 cap.
  Proof.
    iIntros "Hiff Hbuf". iNamed "Hbuf".
    iExists ℓML, used, γfgn; unfold named; iFrame.
    iSplit; first done.
    iApply (isBufferForeignBlock_ext with "[Hiff] Hbuf").
    iApply "Hiff".
  Qed.

  Import melocoton.ml_lang.notation.
  Definition buf_alloc_res_buffer z cap (b : list (option Z)) : iProp Σ := ⌜cap = 0⌝ ∗ ⌜b = replicate (Z.to_nat z) None⌝.
  Definition buf_alloc_spec_ML s vv Φ : iProp Σ :=
    ∃ (z:Z),
      "%Hb1" ∷ ⌜(0 < z)%Z⌝
    ∗ "->" ∷ ⌜s = buf_alloc_name⌝
    ∗ "->" ∷ ⌜vv = [ #z ]⌝
    ∗ "HCont" ∷ ▷ (∀ v ℓbuf, isBufferRecordML v ℓbuf (buf_alloc_res_buffer z) (Z.to_nat z) -∗ Φ (OVal v)).

  Definition buf_alloc1_spec idx vnew Pbold cap (b : list (option Z)) : iProp Σ :=
    ∃ bold (capold:nat) , ⌜b = <[ Z.to_nat idx := Some vnew ]> bold⌝ ∗ ⌜cap = max capold (Z.to_nat (idx+1))⌝ ∗ Pbold capold bold.
  Definition buf_update_spec_ML (protoCB : (protocol ML_lang.val Σ)) s vv Φ: iProp Σ :=
    ∃ (Ψ Ψframe : Z → iProp Σ) (Φz : Z → Z → iProp Σ) (i j : Z) ℓbuf (cap:nat) (Pb : Z → nat → _ → iProp Σ) vbuf b1 b2 (F : ML_lang.expr),
      "->" ∷ ⌜s = buf_upd_name⌝
    ∗ "->" ∷ ⌜vv = [ #i; #j; (RecV b1 b2 F); vbuf ]⌝
    ∗ "%Hb1" ∷ ⌜0%Z ≤ i⌝%Z
    ∗ "%Hb2" ∷ ⌜i ≤ j+1⌝%Z
    ∗ "%Hb3" ∷ ⌜j < cap⌝%Z
    ∗ "#HMerge" ∷ (□ ∀ z vnew, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j⌝%Z -∗ Ψframe (z+1)%Z -∗ Φz z vnew -∗
          isBufferRecordML vbuf ℓbuf (buf_alloc1_spec z vnew (Pb z)) cap ==∗ Ψ (z+1)%Z)
    ∗ "#HWP" ∷ (□ ▷ ∀ z, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j⌝%Z -∗ Ψ z -∗ 
              WP (RecV b1 b2 F) #z at ⟨ ∅, protoCB ⟩
              {{res, ∃ (znew:Z), ⌜res = OVal #znew⌝ ∗ Φz z znew ∗ Ψframe (z+1)%Z
                               ∗ isBufferRecordML vbuf ℓbuf (Pb (z)%Z) cap}})
    ∗ "Hframe" ∷ Ψframe i
    ∗ "Hrecord" ∷ isBufferRecordML vbuf ℓbuf (Pb i) cap
    ∗ "HMergeInitial" ∷ (Ψframe i ∗ isBufferRecordML vbuf ℓbuf (Pb i) cap ==∗ Ψ i)
    ∗ "HCont" ∷ ▷ (Ψ (j+1)%Z -∗ Φ (OVal #())).

  Definition wrap_max_len_spec_ML s vv Φ : iProp Σ :=
    ∃ (n:nat),
      "->" ∷ ⌜s = wrap_max_len_name⌝
    ∗ "->" ∷ ⌜vv = [ #n ]⌝
    ∗ "HCont" ∷ ▷ Φ (OVal #(buffer_max_len n)).

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
                   -∗ Φ (OVal #true)).

  Definition buf_free_spec_ML s vv Φ : iProp Σ :=
    ∃ v ℓ Pb cap,
      "->" ∷ ⌜s = buf_free_name⌝
    ∗ "->" ∷ ⌜vv = [ v ]⌝
    ∗ "Hbuf" ∷ isBufferRecordML v ℓ Pb cap
    ∗ "HCont" ∷ ▷   ( ∀ (ℓML:loc) γfgn, ⌜v = (# ℓML, (# cap, # (LitForeign γfgn)))%MLV⌝ -∗
                                         ℓML ↦M #(-1) -∗
                                         γfgn ↦foreign[Mut] (#C LitNull) -∗ Φ (OVal #())).

  Definition buf_get_spec_ML s vv Φ : iProp Σ :=
    ∃ v ℓ Pb cap (idx:nat) (res:Z),
      "->" ∷ ⌜s = buf_get_name⌝
    ∗ "->" ∷ ⌜vv = [ v; #idx ]⌝
    ∗ "Hbuf" ∷ isBufferRecordML v ℓ (λ a b, Pb a b ∗ ⌜b !! idx = Some (Some res)⌝) cap
    ∗ "%Hcap" ∷ ⌜idx < cap⌝
    ∗ "HCont" ∷ ▷ (isBufferRecordML v ℓ (λ a b, Pb a b ∗ ⌜b !! idx = Some (Some res)⌝) cap -∗
                          Φ (OVal #res)).

  Definition buf_library_spec_ML_pre : (protocol ML_lang.val Σ) -d> (protocol ML_lang.val Σ) := λ (protoCB : (protocol ML_lang.val Σ)),
    buf_alloc_spec_ML ⊔ buf_update_spec_ML protoCB ⊔ buf_free_spec_ML ⊔ wrap_compress_spec_ML ⊔ wrap_max_len_spec_ML ⊔ buf_get_spec_ML.

  Global Instance buf_library_spec_ML_contractive : Contractive buf_library_spec_ML_pre.
  Proof.
    rewrite /buf_library_spec_ML_pre /= => n pp1 pp2 Hpp.
    do 5 f_equiv.
    unfold buf_update_spec_ML, named.
    do 35 first [intros ?|f_equiv]. f_contractive.
    do 5 first [intros ?|f_equiv].
    eapply wp_ne_proto. done.
  Qed.

  Lemma buf_library_spec_ML_pre_mono Ψ1 Ψ2 : Ψ1 ⊑ Ψ2 →
    buf_library_spec_ML_pre Ψ1 ⊑ buf_library_spec_ML_pre Ψ2.
  Proof.
    iIntros (HΨ s vv Φ) "[[[[[H|H]|H]|H]|H]|H]".
    - do 5 iLeft. done.
    - do 4 iLeft; iRight. iNamed "H". unfold buf_update_spec_ML.
      iExists Ψ, Ψframe, Φz, i, j, ℓbuf.
      iExists cap, Pb, vbuf, b1, b2, F.
      iFrame "HCont HMergeInitial Hrecord Hframe HMerge".
      repeat (iSplit; first done).
      iIntros "!> !> %z HH1 HH2 HH3".
      iSpecialize ("HWP" $! z with "HH1 HH2 HH3").
      iApply (wp_strong_mono with "HWP"). 1-2: done. by iIntros (v) "$".
    - do 3 iLeft; by iRight.
    - do 2 iLeft; by iRight.
    - do 1 iLeft; by iRight.
    - do 0 iLeft; by iRight.
  Qed.

End Specs.

