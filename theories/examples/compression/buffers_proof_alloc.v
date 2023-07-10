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

  Definition isRefGamma γ lv : iProp Σ :=
    ∃ γ1 γref γaux, ⌜lv = Lloc γ1⌝ ∗ γ1 ↦imm (TagDefault, [Lloc γref; Lloc γaux]) ∗ ⌜γ = γref⌝.
  Lemma buf_alloc_spec_C θ roots (n: nat) (wcap: word) Ψ :
    (0 < n)%Z →
    repr_lval θ (Lint n) wcap →
    {{{ GC θ roots }}}
         call: &buffers_specs.buf_alloc_name with (wcap)
      at ⟨buf_lib_prog, prims_proto Ψ⟩
    {{{ w' θ' lv ℓ γ, RET w';
       GC θ' (roots ∪ {[γ]}) ∗ isBufferRecord lv ℓ (buf_alloc_res_buffer n) n ∗
       ⌜repr_lval θ' lv w'⌝ ∗ isRefGamma γ lv }}}%CE.
  Proof.
    cbn. iIntros (Hb1 Hlval Φ) "HGC HΦ". wp_call_direct.
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
    iIntros (ℓbts) "Hbts".
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
    iMod (freeze_to_immut with "[$HGC $Hγbf]") as "(HGC&#Hγbf)".
    iMod (freeze_to_immut with "[$HGC $Hγbf2]") as "(HGC&#Hγbf2)".
    iMod (freeze_to_mut _ _ _ _ [_] with "[$HGC $Hγbfref]") as "(HGC&Hγbfref)".
    1: cbn; iSplit; done.

    iPoseProof "Hγbk" as "((Hγbk&%Hγbk)&%fidblk&#Hfidblk)".

    iAssert (isBufferRecord (Lloc γbf) ℓbts (buf_alloc_res_buffer n) n) with "[Hγbk Hγbf Hγbf2 Hγbfref Hbts]" as "Hbuffer".
    { iExists γbf, γbfref, γbf2, γbk, 0, fidblk. unfold named. iFrame. iFrame "Hγbf Hγbf2".
      iSplit; first done.
      iExists (replicate n None). unfold named, lstore_own_foreign.
      rewrite map_replicate; cbn.
      iFrame. iFrame "Hfidblk". iSplit; first (iSplit; first done; by iExists fidblk).
      rewrite (_: Z.to_nat n = n); last lia. iFrame.
      iPureIntro; split_and!.
      1: done.
      1: f_equal; lia.
      cbn. by rewrite replicate_length. }
    
    iModIntro. iApply "HΦ". iFrame.
    iSplit; first eauto.
    iExists _, _, _. iFrame "Hγbf". done.
  Qed.

  Lemma buf_alloc_correct Ψ :
    prims_proto Ψ ||- buf_lib_prog :: wrap_proto buf_alloc_spec_ML.
  Proof using.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done.
    iIntros (Φ'') "HΦ". cbn.
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. iApply wp_fupd.
    iApply (buf_alloc_spec_C _ _ (Z.to_nat z) with "HGC"); first lia.
    { rewrite -(_: z = Z.to_nat z) //; lia. }
    iIntros "!>" (w' θ' lv ℓ γ) "(HGC & Hbuf & % & Hisgam)".
    iNamed "Hbuf".
    iDestruct "Hisgam" as (γk1 γk2 γk3) "(%HH1&#HH2&->)". simplify_eq.
    iPoseProof (@pgm_elem_agree with "[] []") as "%Heq".
    1: iDestruct "Hγbuf" as "(HH&_)"; iApply "HH".
    1: iDestruct "HH2" as "(HH&_)"; iApply "HH".
    iDestruct "Hγusedref" as "(Helem&%fidℓ&%ℓ2&#HHsim)". simplify_eq.
    iAssert (γfgn ~foreign~ fid) as "#Hfgn".
    { iNamed "Hbuf". done. }
    iPoseProof (pgm_elem_to_pers with "Hfgn") as "#fgnfid".
    iMod (bufToML_fixed with "HGC [Hbuf Helem] [] HHsim") as "(HGC&Hbuffer)".
    - repeat iExists _. iSplit; first done. iFrame "Hγbuf Hγaux Helem Hbuf".
      by repeat iExists _.
    - repeat progress (try iSplit; try done; try iExists _).
    - iModIntro. iApply "HΦ".
      rewrite -(_: z = Z.to_nat z); last lia.
      assert ((∅ ∪ {[γk2]}) ∖ {[γk2]} = ∅) as -> by set_solver.
      iApply ("Cont" with "HGC (HCont Hbuffer) [] [//]").
      repeat progress (try iSplit; try done; try iExists _).
  Qed.

End Proofs.
