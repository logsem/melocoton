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
From melocoton.examples.compression Require Import buffers_specs buffers_laws compression_defs.


Section MLclient.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Import melocoton.ml_lang.notation melocoton.ml_lang.lang_instantiation
         melocoton.ml_lang.primitive_laws melocoton.ml_lang.proofmode.

  Context (Ψ : (protocol ML_lang.val Σ)).

  Definition ML_client_env : prog_environ ML_lang Σ := {|
    penv_prog  := ∅ ;
    penv_proto := buf_library_spec_ML_pre Ψ |}.

  Definition ML_client_code : MLval := 
    λ: "vbuf",
      let: "len"  := Length "vbuf" in
      if: "len" = #0 then #false else (
      let: "inp"  := extern: buf_alloc_name with ("len") in
      let: "outp" := extern: buf_alloc_name with (extern: wrap_max_len_name with ("len")) in
      let: <>     := extern: buf_upd_name with (#0, "len" - #1, λ: "i", LoadN "vbuf" "i", "inp") in
      let: <>     := extern: wrap_compress_name with ("inp", "outp") in
      let: "shrn" := ! (Fst "outp") < ! (Fst "inp") in
      let: <>     := extern: buf_free_name with ("inp") in
      let: <>     := extern: buf_free_name with ("outp") in
      "shrn").

  Definition is_compressible (zz : buffer) :=
    let P := length (compress_buffer zz) < length zz
    in decide P.



  Lemma ML_client_spec ℓ dq (zz : buffer) :
    {{{ ℓ ↦∗{dq} map (λ (x:Z), #x) zz }}}
      ML_client_code #ℓ at ML_client_env
    {{{ RETV #(if is_compressible zz then true else false); ℓ ↦∗{dq} map (λ (x:Z), #x) zz }}}.
  Proof.
    iIntros (Φ) "Hℓ Cont".
    unfold ML_client_code, ML_client_env. wp_pures.
    wp_apply (wp_length with "Hℓ"); iIntros "Hℓ". wp_pures.
    rewrite map_length bool_decide_decide.
    destruct decide as [Heq|Heq].
    1: { injection Heq; intros Heq'. wp_pures. destruct zz as [|??]; cbn in *; try lia. iModIntro. iApply ("Cont" with "Hℓ"). }
    assert (length zz ≠ 0) as Heq'.
    1: { intros Heq2. apply Heq. by rewrite Heq2. }

    wp_pure _. wp_extern. iModIntro. cbn. do 5 iLeft.
    iExists (length zz). iSplit; first (iPureIntro; lia).
    iSplit; first done. iSplit; first done.
    iNext. iIntros (vin ℓinbuf) "Hinbuf". wp_finish.
    wp_pures.

    wp_extern. iModIntro. iLeft. iRight.
    iExists _.
    iSplit; first done. iSplit; first done.
    iNext. wp_pures.

    wp_extern. iModIntro. do 5 iLeft.
    iExists _. iSplit.
    2: iSplit; first done. 2: iSplit; first done.
    1: iPureIntro; lia.
    iNext. iIntros (vout ℓoutbuf) "Houtbuf". wp_finish.
    wp_pures.

    wp_extern. iModIntro. do 4 iLeft; iRight.

    pose (λ (idx:Z) (used:nat) (b : list (option Z)), 
        ∃ zpre zopost zzpost, ⌜b = map Some zpre ++ zopost⌝ ∗ ⌜length zopost = length zzpost⌝ ∗ 
        ⌜zz = zpre ++ zzpost⌝ ∗ ⌜Z.of_nat used = idx⌝ ∗ ⌜Z.of_nat (length zpre) = idx⌝ : iProp Σ)%I as Hbufatidx.

    pose (λ (idx:Z), isBufferRecordML vin ℓinbuf (Hbufatidx idx) (length zz) ∗ (ℓ ↦∗{dq} map (λ x : Z, #x) zz))%I as Ψ'.
    pose (λ (idx:Z), (ℓ ↦∗{dq} map (λ x : Z, #x) zz))%I as Ψframe.
    pose (λ (idx:Z) (z:Z), ∃ n, ⌜Z.of_nat n = idx⌝ ∗ ⌜zz !! n = Some z⌝ : iProp Σ)%I as Φz.
    iExists Ψ', Ψframe, Φz, _, _, _, _. iExists Hbufatidx, _, _, _, _. unfold named.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first (iPureIntro; lia).
    iPoseProof (isBufferRecordML_ext with "[] Hinbuf") as "Hinbuf".
    2: iFrame "Hinbuf Hℓ".
    { iIntros (z lst Heqz) "(->&->)". iExists nil, _, _. cbn. repeat (iSplit; first done). iSplit. 2: iSplit; first done. 2: done.
      rewrite replicate_length. iPureIntro; lia. }
    iSplit; first (iPureIntro; lia).
    iSplit; last iSplit; last iSplitR.
    all: unfold Ψframe, Φz, Ψ'; rewrite !Nat2Z.id.
    { iIntros "!> %z %vnew %Hz0 %Hzlen Hframe (%n&<-&%Hz) HBuffer".
      iModIntro. iFrame "Hframe". iApply (isBufferRecordML_ext with "[] HBuffer").
      iIntros (z lst _). unfold buf_alloc1_spec, Hbufatidx.
      iIntros "(%bold&%capold&->&->&%zpre&%zopost&%zzpost&->&%Hzzlen&->&%Heq1&%Heq2)".
      apply Nat2Z.inj' in Heq2. subst n.
      destruct zzpost as [|vnew' zzpost].
      { exfalso. rewrite app_nil_r in Hz. apply lookup_lt_Some in Hz. lia. }
      rewrite lookup_app_r in Hz; last lia. 
      rewrite Nat.sub_diag in Hz. cbn in Hz. simplify_eq.
      destruct zopost as [|zoh zopost]; first done.
      iExists (zpre ++ [vnew]), zopost, zzpost.
      rewrite !Nat2Z.id !map_app -!app_assoc /=.
      iPureIntro; split_and!; try done.
      - replace (length zpre) with (length (map Some zpre) + 0) by (rewrite map_length; lia).
        rewrite insert_app_r. done.
      - cbn in Hzzlen; lia.
      - lia.
      - rewrite app_length /=; lia.
    }
    { iIntros "!> !> %z %Hz0 %Hzlen (Hbuf&Hℓ)".
      assert (exists zvres, zz !! (Z.to_nat z) = Some zvres) as [zvres Heqq].
      1: apply lookup_lt_is_Some_2; lia.
      wp_pures. wp_apply (wp_loadN with "Hℓ"). 1: lia.
      1: change (map ?f zz) with (fmap f zz); rewrite list_lookup_fmap Heqq /= //.
      iIntros "Hℓ". iExists _.
      iSplit; first done. iFrame.
      iExists (Z.to_nat z). iSplit; first (iPureIntro; lia).
      done.
    }
    { by iIntros "($&$)". }
    iIntros "!> (Hinbuf&Hℓ)". wp_finish.
    wp_pures.

    iPoseProof (isBufferRecordML_ext _ _ _ (λ z b, ⌜z = length zz⌝ ∗ ⌜b = map Some zz⌝)%I with "[] Hinbuf") as "Hinbuf".
    { iIntros (z lst _) "(%zpre&%zopost&%zzpost&->&%Hlenpost&->&%HH&%Hlenpre)".
      assert (z = length (zpre ++ zzpost)) as -> by lia. iSplit; first done.
      rewrite app_length in Hlenpre. assert (length zzpost = 0) as Hlen0 by lia.
      destruct zzpost; last done. destruct zopost; last done.
      by rewrite !app_nil_r. }

    wp_extern. iModIntro. do 2 iLeft. iRight.
    iExists _, _, _, _, zz, nil, (λ _ _, True)%I. do 3 iExists _. unfold named.
    iSplit; first done.
    iSplit; first done.
    iFrame "Houtbuf". iSplit; first (cbn; iPureIntro; lia).
    iSplitL "Hinbuf".
    { iApply (isBufferRecordML_ext with "[] Hinbuf").
      iIntros (z lst _) "(->&->)". rewrite app_nil_r. done. }
    iIntros "!> Hinbuf Houtbuf".
    wp_pures.

    iNamed "Hinbuf".
    iDestruct "Houtbuf" as "(%ℓMLout & %used2 & %γfgn2 & -> & HℓbufMLout & Hbuf2)".
    unfold named. wp_pures.
    wp_apply (wp_load with "HℓbufML").
    iIntros "HℓbufML". wp_pures.
    wp_apply (wp_load with "HℓbufMLout").
    iIntros "HℓbufMLout". wp_pures.
    iAssert (⌜used = length zz⌝)%I as "->".
    { iNamed "Hbuf". unfold named. iDestruct "HContent" as "(_&%&_)"; done. }
    iAssert (⌜used2 = length (compress_buffer zz)⌝)%I as "->".
    { iNamed "Hbuf2". unfold named. iDestruct "HContent" as "(%&%&%&_&%&_)"; done. }

    wp_extern. do 3 iLeft. iRight.
    iModIntro. iExists _, _, (λ _ _, _)%I, _.
    do 2 (iSplit; first done).
    iSplitL "Hbuf HℓbufML".
    { do 3 iExists _. iSplit; first done. iFrame. }
    iIntros "!> % % _ _ _". wp_pures.

    wp_extern. do 3 iLeft. iRight.
    iModIntro. iExists _, _, (λ _ _, _)%I, _.
    do 2 (iSplit; first done).
    iSplitL "Hbuf2 HℓbufMLout".
    { do 3 iExists _. iSplit; first done. iFrame. }
    iIntros "!> % % _ _ _". wp_pures.
    unfold is_compressible. rewrite bool_decide_decide.
    repeat destruct decide; cbn in *; try lia.
    all: iApply ("Cont" with "Hℓ").
  Qed.

  Definition ML_client_applied_code : expr := if: ML_client_code (AllocN #256 #0) then #1 else #0.
  Lemma ML_client_applied_spec :
    ⊢ WP
      ML_client_applied_code at ML_client_env
    {{ v, ⌜∃ (x:Z), v = OVal #x ∧ x = 1%Z⌝ }}.
  Proof.
    unfold ML_client_applied_code.
    wp_apply (wp_allocN); [done..|].
    iIntros (ℓ) "(Hℓ&_)".
    wp_apply (ML_client_spec _ _ (replicate 256 (0:Z)) with "Hℓ").
    iIntros "_". wp_pures. iPureIntro. by eexists.
  Qed.

End MLclient.
