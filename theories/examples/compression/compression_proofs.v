From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props language_commons.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.c_lang Require Import notation proofmode.
From melocoton.c_interop Require Import notation.
From melocoton.examples.compression Require Import compression_defs compression_specs.

Definition buffy_max_len_code (inlen:expr) : expr := (BinOp MultOp inlen (#2))%CE.
Definition buffy_compress_rec_name : string := "buffy_compress_rec".
Definition buffy_compress_rec_code (inbuf inlen outbuf:expr) := (
  if: inlen ≤ #0 then #0 else
  if: inlen = #1
    then ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 )
    else if: ( *inbuf = #0) && ( *(inbuf +ₗ #1) = #0 )
      then ( outbuf <- #0 ;; #1 + call: &buffy_compress_rec_name with (inbuf +ₗ #2, inlen - #2, outbuf +ₗ #1) )
      else ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 + call: &buffy_compress_rec_name with (inbuf +ₗ #1, inlen - #1, outbuf +ₗ #2) ) )%CE.
Definition buffy_compress_code (inbuf inlen outbuf outlenp:expr) := (
  if: *outlenp < call: &buffy_max_len_name with (inlen) then #1 else
    (outlenp <- call: &buffy_compress_rec_name with (inbuf, inlen, outbuf)) ;; #0 )%CE.

Definition buffy_env : gmap string function := 
  <[buffy_max_len_name      := Fun [BNamed "len"] (buffy_max_len_code "len")]> (
  <[buffy_compress_rec_name := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"] (buffy_compress_rec_code "inbuf" "inlen" "outbuf")]> (
  <[buffy_compress_name     := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"; BNamed "outlenp"]
                                   (buffy_compress_code "inbuf" "inlen" "outbuf" "outlenp")]>
  ∅)).


Section CProofs.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.
Context (p : lang_prog C_lang).
Context (Hp : buffy_env ⊆ p).
Context (Ψ : (string -d> list val -d> (outcome val -d> iPropO Σ) -d> iPropO Σ)).

Lemma buffy_max_len_correct :
    Ψ ||- p :: buffy_max_len_spec.
Proof using Hp.
  iIntros (s vs Φ) "H". iNamed "H". iSplit.
  { iPureIntro. apply elem_of_dom. eexists.
    eapply lookup_weaken; last exact Hp. done. }
  iIntros (Φ') "HΦ".
  iApply wp_call.
  { cbn. eapply lookup_weaken; last done; done. }
  { done. }
  iNext.
  wp_pures. iModIntro. unfold buffer_max_len.
  replace (Z.of_nat (Nat.mul 2 n)) with ((Z.mul n 2))%Z by lia.
  iApply "HΦ". iApply "Hcont".
Qed.

Lemma buffy_compress_rec_spec ℓin ℓout vin bin vspace :
   isBuffer vin bin →
   length vspace ≥ buffer_max_len (length bin) →
(⊢  ℓin  I↦C∗ vin
 -∗ ℓout I↦C∗ vspace -∗
    WP (call: &buffy_compress_rec_name with (Val #ℓin, Val #(length bin), Val #ℓout))%CE at ⟨ p , Ψ ⟩
    {{ v', ∃ bout vout vrest voverwritten,
             ⌜isBuffer vout bout⌝
           ∗ ⌜bout = compress_buffer bin⌝
           ∗ ⌜v' = OVal #(length vout)⌝
           ∗ ⌜vspace = voverwritten ++ vrest⌝
           ∗ ⌜length voverwritten = length vout⌝
           ∗ ℓout I↦C∗ (vout ++ vrest)
           ∗ ℓin  I↦C∗ vin }})%I.
Proof using Hp.
  iIntros (HBuffer Hlength) "Hℓin Hℓout".
  iLöb as "IH" forall (ℓin ℓout vin bin vspace HBuffer Hlength).
  wp_pures. wp_pure _.
  1: split; first (eapply lookup_weaken, Hp); done.
  wp_pures.
  destruct bin as [|bfst bin].
  { cbn. rewrite bool_decide_decide. destruct decide; last lia.
    wp_pures. iModIntro.
    iExists [], [], vspace, []. iFrame. iPureIntro. split_and!; try done. }
  cbn. rewrite bool_decide_decide. destruct decide; first lia.
  wp_pures.
  destruct bin as [|bsnd bin]; cbn; rewrite bool_decide_decide; destruct decide; try lia.
  { iClear "IH". wp_pures. unfold isBuffer in *. subst vin. cbn.
    iDestruct "Hℓin" as "(Hℓin&_)". cbn in Hlength.
    destruct vspace as [|vs1 [|vs2 vsrest]]; cbn in Hlength; try lia.
    cbn. iDestruct "Hℓout" as "(Hℓout1&Hℓout2&Hℓoutr)".
    rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓout1"); iIntros "Hℓout1"; wp_pures.
    wp_apply (wp_load with "Hℓin"); iIntros "Hℓin".
    wp_apply (wp_store with "Hℓout2"); iIntros "Hℓout2"; wp_pures.
    iModIntro. iExists [1%Z; bfst], _, vsrest, [_; _].
    iSplit; first done. cbn. rewrite !loc_add_0. iFrame. iPureIntro.
    split_and!; try done.
    1: by repeat case_match. }
  wp_pures. unfold isBuffer in HBuffer. subst vin.
  cbn in Hlength. rewrite !Nat.add_succ_r in Hlength. cbn.
  iDestruct "Hℓin" as "(Hℓin0&Hℓin1&HℓinR)". rewrite !loc_add_0.
  destruct (decide (bfst = 0 ∧ bsnd = 0)%Z) as [[-> ->]|Hnn].
  { wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
    wp_apply (wp_load with "Hℓin1"); iIntros "Hℓin1"; wp_pures.
    destruct vspace as [|vsp1 vspr]; first (cbn in *; lia).
    cbn. iDestruct "Hℓout" as "(Hℓou0&HℓouR)". rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓou0"); iIntros "Hℓou0"; wp_pures.
    wp_pures. replace (Z.of_nat (S (S (length bin))) - 2)%Z with (Z.of_nat (length bin)) by lia.
    wp_bind (FunCall _ _); wp_apply (wp_wand with "[HℓinR HℓouR]").
    { iApply ("IH" with "[] [] [HℓinR]"); iClear "IH". 1: done.
      2: { unfold array. iApply (big_sepL_wand with "HℓinR").
           iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (2 + k)%Z by lia. done. }
      2: { unfold array. iApply (big_sepL_wand with "HℓouR").
           iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S k)) with (1 + k)%Z by lia. done. }
      iPureIntro. cbn in *. lia. }
    { cbn. iClear "IH". unfold isBuffer.
      iIntros (v) "(%bout&%vout&%vrest&%vov&->&->&->&->&%Hlen&HℓouR&HℓinR)".
      wp_pures. iModIntro.
      iExists (0%Z :: compress_buffer bin), _, vrest, (vsp1 :: vov).
      iSplit; first done. iFrame.
      repeat iSplit; try iPureIntro.
      - done.
      - cbn. do 3 f_equal. lia.
      - done.
      - cbn. by rewrite Hlen.
      - unfold array. iApply (big_sepL_wand with "HℓinR").
        iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (2 + k)%Z by lia. done.
    }
  }
  { wp_bind (if: _ then _ else #0)%CE.
    iApply (wp_wand _ _ _ (λ v, ⌜v = OVal #0⌝ ∗ ℓin ↦C #bfst ∗ (ℓin +ₗ 1) ↦C #bsnd)%I with "[Hℓin0 Hℓin1]").
    { wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
      rewrite bool_decide_decide. destruct decide.
      { wp_pures.
        wp_apply (wp_load with "Hℓin1"); iIntros "Hℓin1"; wp_pures.
        rewrite bool_decide_decide. destruct decide; try lia.
        iModIntro. iFrame. done. }
      { wp_pures. iModIntro. iFrame. done. }
    }
    iIntros (?) "(->&Hℓin0&Hℓin1)". wp_pures.
    destruct vspace as [|vsp1 [|vsp2 vspr]]; try (cbn in *; lia).
    cbn. iDestruct "Hℓout" as "(Hℓou0&Hℓou1&HℓouR)". rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓou0"); iIntros "Hℓou0"; wp_pures.
    wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
    wp_apply (wp_store with "Hℓou1"); iIntros "Hℓou1"; wp_pures.
    wp_pures. replace (Z.of_nat (S (S (length bin))) - 1)%Z with (Z.of_nat (S (length bin))) by lia.
    wp_bind (FunCall _ _); iApply (wp_wand with "[Hℓin1 HℓinR HℓouR]").
    { change (S (length bin)) with (length (bsnd :: bin)).
      iApply ("IH" with "[] [] [Hℓin1 HℓinR]"); iClear "IH". 1: done.
      2: { unfold array. cbn. rewrite !loc_add_assoc. iFrame.
           iApply (big_sepL_wand with "HℓinR").
           iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (1 + (S k))%Z by lia. done. }
      2: { unfold array. iApply (big_sepL_wand with "HℓouR").
           iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (2 + k)%Z by lia. done. }
      iPureIntro. cbn in *. lia. }
    { cbn. iClear "IH". unfold isBuffer.
      iIntros (v) "(%bout&%vout&%vrest&%vov&->&->&->&->&%Hlen&HℓouR&Hℓin1&HℓinR)".
      wp_pures. iModIntro.
      iExists (1%Z :: bfst :: compress_buffer (bsnd :: bin)), _, vrest, (vsp1 :: vsp2 :: vov).
      iSplit; first done.
      repeat iSplit; try iPureIntro. 5: cbn; iFrame.
      - do 4 (cbn in *; case_match; try (exfalso; by eapply Hnn); simplify_eq; try congruence).
      - cbn. do 2 f_equal. rewrite -Hlen.
        replace (Z.of_nat (S (S (length vov)))) with (2 + (length vov))%Z by lia.
        by done.
      - done.
      - cbn. rewrite Hlen. done.
      - rewrite !loc_add_0. iFrame "Hℓou0 Hℓin1". iSplitL "HℓouR".
        + unfold array. iApply (big_sepL_wand with "HℓouR").
          iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
          replace (Z.of_nat (S (S k))) with (2 + k)%Z by lia. done. 
        + unfold array. iApply (big_sepL_wand with "HℓinR").
          iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (1 + (S k))%Z by lia. done.
    }
  }
Qed.


Lemma buffy_compress_correct_ok :
    Ψ ||- p :: buffy_compress_spec_ok.
Proof using Hp.
  iIntros (s vs Φ) "H". iNamed "H".
  iSplit.
  { iPureIntro. eapply elem_of_dom_2, lookup_weaken; last done; done. }
  iIntros (Φ') "HΦ". iApply wp_call.
  { cbn. eapply lookup_weaken; last done; done. }
  { done. }
  iNext.
  wp_pures.
  wp_apply (wp_load with "Hℓlen"); iIntros "Hℓlen".
  wp_progwp. 1: apply buffy_max_len_correct.
  iModIntro. iExists _; unfold named.
  iSplit; first done.
  iSplit; first done. iNext. wp_finish.
  wp_pures. rewrite bool_decide_decide. destruct decide; cbn in *; try lia.
  wp_pure _. wp_bind (FunCall _ _).
  iApply (wp_wand with "[Hℓin Hℓout]").
  1: by iApply (buffy_compress_rec_spec with "[Hℓin]").
  cbn.
  iIntros (v) "(%bout&%vout&%vrest&%vov&HH1&HH2&->&HH3&%Hlen&HℓouR&HℓinR)".
  wp_apply (wp_store with "Hℓlen"); iIntros "Hℓlen".
  wp_pures. iModIntro.
  iApply "HΦ". iApply ("HCont" with "[$] [$] [$] [//] [$] [$] [$]").
Qed.


Lemma buffy_compress_correct_fail :
    Ψ ||- p :: buffy_compress_spec_fail.
Proof using Hp.
  iIntros (s vs Φ) "H". iNamed "H".
  iSplit.
  { iPureIntro. eapply elem_of_dom_2, lookup_weaken; last done; done. }
  iIntros (Φ') "HΦ". iApply wp_call.
  { cbn. eapply lookup_weaken; last done; done. }
  { done. }
  iNext.
  wp_pures.
  wp_apply (wp_load with "Hℓlen"); iIntros "Hℓlen".
  wp_progwp. 1: apply buffy_max_len_correct.
  iModIntro. iExists _; unfold named.
  iSplit; first done.
  iSplit; first done. iNext. wp_finish.
  wp_pures. rewrite bool_decide_decide. destruct decide; cbn in *; try lia.
  wp_pures. iModIntro.
  iApply "HΦ". iApply ("HCont" with "[$]").
Qed.

Lemma buffy_library_correct :
    Ψ ||- p :: buffy_library_spec.
Proof using Hp.
  iIntros (s vv Φ) "[[H|H]|H]".
  - by iApply buffy_max_len_correct.
  - by iApply buffy_compress_correct_ok.
  - by iApply buffy_compress_correct_fail.
Qed.


(* XXX use sealing *)
Opaque isBuffer.

End CProofs.

