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

  Lemma buf_alloc_correct E1 E2 Ψ :
    prims_proto E1 Ψ ||- buf_lib_prog @ E2 :: wrap_proto buf_alloc_spec_ML.
  Proof using.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    cbn. unfold progwp. solve_lookup_fixed.
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed.
    iSplit; first done. iNext.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbk) "(HGC&Hℓbk)"; wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbf) "(HGC&Hℓbf)"; wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbf2) "(HGC&Hℓbf2)". wp_finish.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γbk wbk) "(HGC&Hγbk&%Hbk'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros "(HGC&Hℓbk)". wp_pures.
    wp_apply (load_from_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros (w) "(Hℓbk&HGC&%Hbk'1b)".
    wp_apply (wp_val2int with "HGC"); [try done..|].
    1: by eapply repr_lval_lint.
    iIntros "HGC".
    wp_apply (wp_Malloc); [try done..|].
    iIntros (ℓbts) "(Hbts&Hstuff)".
    wp_apply (wp_write_foreign with "[$HGC $Hγbk]"); [try done..|].
    iIntros "(HGC&Hγbk)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ2 γbf wbf) "(HGC&Hγbf&%Hbf'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros "(HGC&Hℓbf)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ3 γbf2 wbf2) "(HGC&Hγbf2&%Hbf2'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros "(HGC&Hℓbf2)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ4 γbfref wbfref) "(HGC&Hγbfref&%Hbfref'1)".
    wp_pure _.
    wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (wunit) "(HGC&%Hwunit)".
    wp_apply (wp_modify with "[$HGC $Hγbfref]"); [done..|].
    iIntros "(HGC&Hγbfref)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4) "(Hℓbf&HGC&%Hbf'4)".
    wp_apply (wp_modify with "[$HGC $Hγbf]"); [done..|].
    iIntros "(HGC&Hγbf)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4') "(Hℓbf&HGC&%Hbf'4')".
    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4) "(Hℓbf2&HGC&%Hbf2'4)".
    wp_apply (wp_modify with "[$HGC $Hγbf]"); [done..|].
    iIntros "(HGC&Hγbf)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4') "(Hℓbf2&HGC&%Hbf2'4')".
    wp_apply (wp_modify with "[$HGC $Hγbf2]"); [try done..|].
    1: by eapply repr_lval_lint.
    iIntros "(HGC&Hγbf2)".
    wp_pure _.

    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4'') "(Hℓbf2&HGC&%Hbf2'4'')".
    wp_apply (load_from_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros (wbk'4') "(Hℓbk&HGC&%Hbk'4')".
    wp_apply (wp_modify with "[$HGC $Hγbf2]"); [done..|].
    iIntros "(HGC&Hγbf2)".
    wp_pure _.

    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4'') "(Hℓbf&HGC&%Hbf'4'')". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbk]"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf]"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf2]"); [done..|].
    iIntros "HGC". wp_pure _.
    change (Z.to_nat 0) with 0.
    change (Z.to_nat 1) with 1.
    change (Z.to_nat 2) with 2.
    cbn.
    iMod (freeze_to_immut with "[$HGC $Hγbf]") as "(HGC&Hγbf)".
    iMod (freeze_to_immut with "[$HGC $Hγbf2]") as "(HGC&Hγbf2)".
    iMod (freeze_to_mut with "[$HGC $Hγbfref]") as "(HGC&Hγbfref)".

    iPoseProof "Hγbk" as "((Hγbk&%Hγbk)&%fid&#Hfid)".

    assert (∃ k, Z.of_nat k = z) as (ncap&<-) by (exists (Z.to_nat z); lia).
    rewrite !Nat2Z.id.
    iAssert (isBufferRecord (Lloc γbf) ℓbts (buf_alloc_res_buffer ncap) ncap) with "[Hγbk Hγbf Hγbf2 Hγbfref Hbts]" as "Hbuffer".
    { iExists γbf, γbfref, γbf2, γbk, 0, fid. unfold named. iFrame.
      iSplit; first done.
      iExists (replicate ncap None). unfold named, lstore_own_foreign.
      rewrite map_replicate; cbn.
      iFrame. iFrame "Hfid". iSplit; first (iSplit; first done; by iExists fid).
      iPureIntro; split_and!.
      1: done.
      1: f_equal; lia.
      cbn. by rewrite replicate_length. }
    iMod (bufToML with "HGC Hbuffer") as "(HGC&%vv&Hbuffer&#Hsim)".
    iAssert (meta_token ℓbts ⊤) with "[Hstuff]" as "Hmeta".
    { destruct ncap as [|ncap]; first lia.
      cbn. rewrite loc_add_0. iDestruct "Hstuff" as "($&_)". }
    iModIntro. iApply ("Cont" with "HGC (HCont Hbuffer Hmeta) Hsim [//]").
  Qed.

End Proofs.