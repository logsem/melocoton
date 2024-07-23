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
From melocoton.examples.compression Require Import buffers_specs buffers_code buffers_laws.

Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Lemma buf_upd_correct Ψcb :
    prims_proto Ψcb ||- buf_lib_prog :: wrap_proto (buf_update_spec_ML Ψcb).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done.
    iIntros (Φ'') "HΦ".
    destruct lvs as [|lvi [|lvj [| lvF [| lvbuf [|??]]]]]; try done.
    all: cbn; iDestruct "Hsim" as "(->&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(->&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "((%γF&->&HγF)&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsim&?)"; try done.
    destruct ws as [|wi [|wj [|wF [|wbuf [|??]]]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons in Hrepr as (Hrepri&Hrepr).
    eapply Forall2_cons in Hrepr as (Hreprj&Hrepr).
    eapply Forall2_cons in Hrepr as (HreprF&Hrepr).
    eapply Forall2_cons in Hrepr as (Hreprbuf&_).
    cbn. wp_call_direct.
    wp_apply (wp_initlocalroot with "[$HGC $Hfc]"); eauto.
    iIntros (f) "(HGC&Hfc&Hlr)". wp_pures.

    wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
    iIntros (ℓF) "(HGC&HℓF&Hfc&Hlr)". wp_pures.
    wp_apply (store_to_local_root with "[$HGC $HℓF $Hlr]"); [done..|].
    iIntros "(HGC&HℓF&Hlr)". wp_pures.

    wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
    iIntros (ℓbf) "(HGC&Hℓbf&Hfc&Hlr)". wp_pures.
    wp_apply (store_to_local_root with "[$HGC $Hℓbf $Hlr]"); [done..|].
    iIntros "(HGC&Hℓbf&Hlr)". wp_pures.

    iMod (bufToC with "HGC Hrecord Hsim") as "(HGC&Hrecord&%&%&->)".
    iNamed "Hrecord". iNamed "Hbuf".

    wp_apply (load_from_local_root with "[$HGC $Hlr $Hℓbf]"); [done..|].
    iIntros (wγ1) "(Hℓbf&HGC&Hlr&%Hwγ1)".
    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (? wγaux1) "(HGC&_&%Heq&%Hγaux'1)"; cbv in Heq; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (? wγfgn1) "(HGC&_&%Heq&%Hγfgn'1)"; cbv in Heq; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_Malloc); [done..|].
    change (Z.to_nat 1) with 1; cbn [replicate].
    iIntros (ℓi) "Hℓi". wp_pure _.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC".
    wp_apply (wp_store with "[Hℓi]").
    { iNext. cbn. rewrite loc_add_0. iDestruct "Hℓi" as "[$ _]". }
    iIntros "Hℓi". wp_pure _.

    iMod (bufToML_fixed (Lloc γ0) ℓbuf (Pb i) (length vcontent)
         with "HGC [Hγusedref Hℓbuf HContent Hγfgnpto] Hsim") as "(HGC&HBufML)".
    { iExists _, _, _, _, _. unfold named. iSplit; first done.
      iFrame "Hγusedref Hγbuf Hγaux".
      iExists _. unfold named. by iFrame "Hγfgnpto Hℓbuf HContent". }
    iMod ("HMergeInitial" with "[$Hframe $HBufML]") as "HΨ".
    wp_bind (While _ _).

    repeat match goal with [H : repr_lval _ _ ?x |- _] => clear H; try clear x end.

    iRevert (Hb1 Hb2); iIntros "#Hb1 #Hb2".
    revert Hb3.
    generalize (length vcontent) as vcontent_length. intros vcontent_length Hb3.
    clear vcontent.

    wp_apply (wp_wand _ _ _
      (λ _, ∃ θ, ℓF ↦roots[f] Lloc γF
               ∗ ℓbf ↦roots[f] Lloc γ0
               ∗ GC θ ∗ current_fc (f::fc) ∗ Ψ (j + 1)%Z
               ∗ ℓi ↦C{DfracOwn 1} #(j + 1))%I
              with "[HℓF Hℓbf Hℓi HGC Hfc Hlr HΨ]").
    { iRevert "HMerge HWP Hb1 Hb2". iLöb as "IH" forall (i θ).
      iIntros "#HMerge #HWP %Hb1 %Hb2".
      wp_pure _.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pure _.
      rewrite bool_decide_decide. destruct decide; last first.
      { wp_pures. iModIntro.
        assert (i=j+1)%Z as -> by lia. iExists _. iFrame. }
      wp_pures.

      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (load_from_local_root with "[$HGC $HℓF $Hlr]").
      iIntros (wγF) "(HℓF&HGC&Hlr&%HwγF)".
      cbn; wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi".
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (wi) "(HGC&%Hwi)".
      wp_apply (wp_callback _ _ _ _ _ _ _ _ _ _ _ _ (#ML i) with "[$HGC $HγF $Hfc HΨ]"); [done..| |].
      { cbn. iSplit; first done.
        iNext. by iApply ("HWP" with "[] [] HΨ"). } cbn.
      cbn.
      iIntros (θ' vret lvret wret) "(HGC&(%zret&%Ho&HΦz&HΨframe&HBuffer)&Hv&%Hzrep)".
      inversion Ho. subst. destruct lvret. inversion Hzrep; subst.
      cbn. iRevert "Hv". iIntros "%Hv". subst.
      wp_apply (wp_val2int with "HGC"); try done.
      iIntros "HGC".
      iDestruct "HBuffer" as "(%ℓML0&%&%&%Heq&HℓbufML&Hbuf)". simplify_eq. unfold named.
      iNamed "Hbuf".
      assert (∃ (ni:nat), Z.of_nat ni = i) as (ni&<-) by (exists (Z.to_nat i); lia).
      cbn. wp_apply (wp_store_offset with "Hℓbuf").
      1: rewrite map_length; lia.
      iIntros "Hℓbuf". erewrite (map_insert (Some zret)); [|done|lia].

      wp_pure _.
      wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
      iIntros (wbf1) "(Hℓbf&HGC&%Hwbf1)".
      wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
      iIntros (vγref wγref) "(HGC&_&%Heq&%Hvwγref)". cbv in Heq. simplify_eq.

      iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&%&%&HℓbufML&#Hsim2&HHsim2)".
      destruct lvs as [|? [|??]].
      1: cbn; done.
      all: iDestruct "HHsim2" as "(->&HHr)"; try done. iClear "HHr".

      iAssert (⌜γfgn0 = γfgn⌝ ∗ ⌜γ = γref⌝)%I as "(->&->)".
      { iDestruct "Hsim" as "(%γ2&%&%&%&Hγbuf2&(%γref2&->&Hsim3)&%γaux2&%&%&->&Hγaux2&->&->)".
        simplify_eq.
        unfold lstore_own_vblock, lstore_own_elem; cbn.
        iDestruct "Hγbuf" as "(Hγbuf&_)".
        iDestruct "Hγbuf2" as "(Hγbuf2&_)".
        iDestruct "Hγaux" as "(Hγaux&_)".
        iDestruct "Hγaux2" as "(Hγaux2&_)".
        iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
        iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
        iPoseProof (lloc_own_pub_inj with "Hsim3 Hsim2") as "%Heq2"; simplify_eq.
        iPureIntro. split_and!; first done.
        symmetry. by eapply Heq2. }

      wp_apply (wp_readfield with "[$HGC $HℓbufML]"); [done..|].
      iIntros (vγbuf wγbuf) "(HGC&HℓbufML&%Heq&%Hvwγbuf)". change (Z.to_nat 0) with 0 in Heq. cbn in Heq. simplify_eq.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      cbn; wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". do 2 wp_pure _.
      wp_bind (If _ _ _).
      iApply (wp_wand _ _ _ (λ _, _ ∗ γref ↦mut (TagDefault, [Lint (max used0 (Z.to_nat (ni+1)))%Z]))%I with "[HGC Hℓi Hℓbf HℓbufML]").
      { rewrite bool_decide_decide. destruct decide; last first.
        { do 2 wp_pure _. rewrite max_l; last lia.
          iFrame "HℓbufML". iModIntro. iAccu. }
        { wp_pure _.
          wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
          iIntros (wbf2) "(Hℓbf&HGC&%Hwbf2)".
          wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
          iIntros (vγref2 wγref2) "(HGC&_&%Heq&%Hvwγref2)". cbv in Heq. simplify_eq.
          cbn; wp_apply (wp_load with "Hℓi").
          iIntros "Hℓi". wp_pure _.
          wp_apply (wp_int2val with "HGC"); [done..|].
          iIntros (vnp1) "(HGC&%Hnp1)".
          wp_apply (wp_modify with "[$HGC $HℓbufML]"); [done..|].
          iIntros "(HGC&HℓbufML)". iFrame "HGC Hℓbf Hℓi".
          rewrite max_r; last lia. change (Z.to_nat 0) with 0; cbn.
          rewrite Z2Nat.id; last lia. done. }
      }
      iIntros (vv) "((HGC&Hℓi&Hℓbf)&HℓbufML)". cbn. destruct vv. wp_pure _.
      wp_apply (wp_load with "Hℓi"). iIntros "Hℓi". wp_pure _.
      wp_apply (wp_store with "Hℓi"). iIntros "Hℓi". wp_pure _.
      iMod (mut_to_ml _ [ #ML (_:Z)] with "[$HGC $HℓbufML]") as "(HGC&%ℓML2&HℓbufML&Hsimℓ2)". 1: cbn; iFrame; done.
      iPoseProof (lloc_own_pub_inj with "Hsim2 Hsimℓ2") as "%Heq3"; simplify_eq.
      replace ℓML2 with ℓML0 by by eapply Heq3.
      iMod ("HMerge" with "[] [] HΨframe HΦz [Hγfgnpto HContent Hℓbuf HℓbufML]") as "HH". 1-2: iPureIntro; lia.
      { iExists _, _, _. unfold named. iSplit; first done. iFrame "HℓbufML".
        iExists _. unfold named. iFrame "Hγfgnpto Hℓbuf".
        rewrite insert_length. iSplit; last done.
        iExists vcontent, _. iFrame "HContent". iPureIntro. rewrite Nat2Z.id. split; first done.
        reflexivity. }
      iApply ("IH" with "HℓF Hℓbf Hℓi HGC HH").
      - iIntros "!> %z1 %z2 %HH1 %HH2". iApply "HMerge".
        all: iPureIntro; lia.
      - iIntros "!> %z1 %HH1 %HH2". iApply "HWP".
        all: iPureIntro; lia.
      - iPureIntro; lia.
      - iPureIntro; lia.
    }
    iIntros (vvv) "(%θ' & HℓF & Hℓbf & HGC & HΨ & Hℓi)".
    destruct vvv. wp_pure _.
    wp_apply (wp_free with "Hℓi"). iIntros "_".
    wp_pure _.
    wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (v0) "(HGC&%Hrepr)".
    wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $HℓF]"); [done..|].
    iIntros "HGC"; wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf]"); [done..|].
    iIntros "HGC"; wp_pure _.
    iModIntro. iApply "HΦ".
    iApply ("Return" $! _ _ (OVal (Lint 0)) with "HGC (HCont HΨ) [//] [//]").
  Qed.

End Proofs.
