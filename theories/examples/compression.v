From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.c_lang Require notation proofmode.

Section SemBuffers.
(* Of course, snappy is more complicated than this ..*)
Definition buffer := list Z.

Fixpoint compress_buffer (b:buffer) : buffer := (match b with
| 0 :: 0 :: xs => 0 :: compress_buffer xs
| x :: xs => 1 :: x :: compress_buffer xs
| nil => nil end)%Z.

Definition buffer_max_len (n : nat) := 2 * n.

Fixpoint decompress_buffer (b:buffer) : option buffer := (match b with
| 0 :: xs => option_map (λ x, 0 :: 0 :: x) (decompress_buffer xs)
| 1 :: 0 :: 1 :: 0 :: xs => None
| 1 :: 0 :: 0 :: xs => None
| 1 :: x :: xs => option_map (cons x) (decompress_buffer xs)
| nil => Some nil
| _ => None end)%Z.

Lemma decompress_compress b : decompress_buffer (compress_buffer b) = Some b.
Proof.
  induction b using (induction_ltof1 _ (@length _)); unfold ltof in *.
  destruct x as [|b1 [|b2 br]].
  - done.
  - cbn. by case_match.
  - cbn. repeat (case_match; try done).
    all: cbn; rewrite H; last (cbn; lia); try done.
Qed.

Lemma decompress_to_nil b : decompress_buffer b = Some nil → b = nil.
Proof.
  destruct b; try done; cbn.
  repeat (cbn in *; unfold option_map in *; case_match; simplify_eq; try done).
Qed.

Lemma compress_decompress b b2 : decompress_buffer b = Some b2 → compress_buffer b2 = b.
Proof. revert b2.
  induction b using (induction_ltof1 _ (@length _)); unfold ltof in *; intros bb Hb.
  destruct x as [|b1 br].
  - cbn in *. by simplify_eq.
  - repeat (cbn in *; case_match; simplify_eq; try done); unfold option_map in *.
    + case_match; last done.
      simplify_eq. eapply H in H0; last (cbn; lia). subst br; done.
    + case_match; last done. simplify_eq. eapply H in H0; last (cbn; lia).
      destruct b; first done. cbn in *; repeat (case_match; simplify_eq); done.
    + destruct (decompress_buffer l) eqn:Heq; cbn in *; last done. simplify_eq.
      eapply H in Heq; last (cbn; lia). subst l. cbn. done.
    + destruct (decompress_buffer l) eqn:Heq; cbn in *; last done. simplify_eq.
      eapply H in Heq; last (cbn; lia). subst l. cbn. done.
    + case_match; last done. simplify_eq.
      eapply H in H0; last (cbn; lia). subst l. cbn. done.
    + case_match; last done. simplify_eq.
      eapply H in H0; last (cbn; lia). subst l. cbn. done.
Qed.

Lemma max_len_correct b : length (compress_buffer b) ≤ buffer_max_len (length b).
Proof.
  induction b using (induction_ltof1 _ (@length _)); unfold ltof in *.
  destruct x as [|b1 [|b2 br]].
  - cbn in *; lia.
  - cbn. by case_match.
  - cbn. repeat (case_match; try (first [done | cbn in *; lia])).
    all: cbn in *; repeat (first [eapply le_n_S | erewrite Nat.add_succ_r]); etransitivity; first eapply H; cbn in *; lia.
Qed.

Lemma max_len_tight n : ∃ b, length b = n ∧ length (compress_buffer b) = buffer_max_len n.
Proof.
  induction n as [|n (b&IH1&IH2)].
  - exists []. done.
  - exists (1 :: b)%Z. cbn; split_and!; try done; try lia.
    rewrite IH2. unfold buffer_max_len. lia.
Qed.

Lemma compression_makes_shorter n : ∃ b, length b ≥ n ∧ length (compress_buffer b) < length b.
Proof.
  exists (repeat 0%Z (2*(S n))).
  rewrite repeat_length. split; first lia.
  induction n as [|n IH].
  - cbn. lia.
  - cbn. rewrite -!Nat.succ_lt_mono. cbn -[repeat] in IH. etransitivity.
    1: erewrite Nat.add_succ_r; exact IH. lia.
Qed.

End SemBuffers.

Section CBuffers.
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.

Definition isBuffer (vl : list (option val)) (b : buffer) := vl = map (λ x:Z, Some (#x)) b.

Definition buffy_max_len_name : string := "buffy_max_compressed_length".
Definition buffy_max_len_code (inlen:expr) : expr := (BinOp MultOp inlen (#2))%CE.

Definition buffy_compress_rec_name : string := "buffy_compress_rec".
Definition buffy_compress_rec_code (inbuf inlen outbuf:expr) := (
  if: inlen ≤ #0 then #0 else
  if: inlen = #1
    then ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 )
    else if: ( *inbuf = #0) && ( *(inbuf +ₗ #1) = #0 )
      then ( outbuf <- #0 ;; #1 + call: &buffy_compress_rec_name with (inbuf +ₗ #2, inlen - #2, outbuf +ₗ #1) )
      else ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 + call: &buffy_compress_rec_name with (inbuf +ₗ #1, inlen - #1, outbuf +ₗ #2) ) )%CE.

Definition buffy_compress_name : string := "buffy_compress".
Definition buffy_compress_code (inbuf inlen outbuf outlenp:expr) := (
  if: *outlenp < call: &buffy_max_len_name with (inlen) then #1 else
    (outlenp <- call: &buffy_compress_rec_name with (inbuf, inlen, outbuf)) ;; #0 )%CE.

Definition buffy_env : gmap string function := 
  <[buffy_max_len_name      := Fun [BNamed "len"] (buffy_max_len_code "len")]> (
  <[buffy_compress_rec_name := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"] (buffy_compress_rec_code "inbuf" "inlen" "outbuf")]> (
  <[buffy_compress_name     := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"; BNamed "outlenp"]
                                   (buffy_compress_code "inbuf" "inlen" "outbuf" "outlenp")]>
  ∅)).

Definition buffy_prog_env : prog_environ C_lang Σ := {|
  penv_prog := buffy_env ;
  penv_proto := λ _ _ _, False
|}%I.

Lemma buffy_max_len_spec E n (v:val) :
  v = #(Z.of_nat n) →
 (⊢ WP (call: &buffy_max_len_name with (Val v))%CE @ buffy_prog_env; E {{λ v', ⌜v' = #(Z.of_nat (buffer_max_len n))⌝}})%I.
Proof.
  iIntros (->). wp_pures. iModIntro. iPureIntro. do 2 f_equal. cbn. lia.
Qed.

Lemma ptr_offset_add (ℓ:loc) (z:Z) : bin_op_eval PtrOffsetOp #ℓ #z = Some (LitLoc (loc_add ℓ z)).
Proof.
  destruct ℓ; done.
Qed.

Lemma buffy_compress_rec_spec E ℓin ℓout vin bin vspace :
   isBuffer vin bin →
   length vspace ≥ buffer_max_len (length bin) →
(⊢  ℓin  ↦C∗ vin
 -∗ ℓout ↦C∗ vspace -∗
    WP (call: &buffy_compress_rec_name with (Val #ℓin, Val #(length bin), Val #ℓout))%CE @ buffy_prog_env; E
    {{ v', ∃ bout vout vrest,
             ⌜isBuffer vout bout⌝
           ∗ ⌜bout = compress_buffer bin⌝
           ∗ ⌜v' = #(length vout)⌝
           ∗ (∃ voverwritten, ⌜vspace = voverwritten ++ vrest⌝)
           ∗ ℓout ↦C∗ (vout ++ vrest)
           ∗ ℓin  ↦C∗ vin }})%I.
Proof.
  iIntros (HBuffer Hlength) "Hℓin Hℓout".
  iLöb as "IH" forall (ℓin ℓout vin bin vspace HBuffer Hlength).
  wp_pures.
  destruct bin as [|bfst bin].
  { cbn. rewrite bool_decide_decide. destruct decide; last lia.
    wp_pures. iModIntro.
    iExists [], [], vspace. iFrame. iPureIntro. split_and!; try done.
    exists nil. done. }
  cbn. rewrite bool_decide_decide. destruct decide; first lia.
  wp_pures.
  destruct bin as [|bsnd bin]; cbn; rewrite bool_decide_decide; destruct decide; try lia.
  { iClear "IH". wp_pures. unfold isBuffer in *. subst vin. cbn.
    iDestruct "Hℓin" as "(Hℓin&_)". cbn in Hlength.
    destruct vspace as [|vs1 [|vs2 vsrest]]; cbn in Hlength; try lia.
    cbn. iDestruct "Hℓout" as "(Hℓout1&Hℓout2&Hℓoutr)".
    rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓout1"); iIntros "Hℓout1"; wp_pures.
    wp_pure _. 1: apply ptr_offset_add.
    wp_apply (wp_load with "Hℓin"); iIntros "Hℓin".
    wp_apply (wp_store with "Hℓout2"); iIntros "Hℓout2"; wp_pures.
    iModIntro. iExists [1%Z; bfst], _, vsrest.
    iSplit; first done. cbn. rewrite !loc_add_0. iFrame. iPureIntro.
    split_and!; try done.
    1: by repeat case_match.
    eexists [_; _]. done. }
  wp_pures. unfold isBuffer in HBuffer. subst vin.
  cbn in Hlength. rewrite !Nat.add_succ_r in Hlength. cbn.
  iDestruct "Hℓin" as "(Hℓin0&Hℓin1&HℓinR)". rewrite !loc_add_0.
  destruct (decide (bfst = 0 ∧ bsnd = 0)%Z) as [[-> ->]|Hnn].
  { wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
    wp_pure _; first eapply ptr_offset_add.
    wp_apply (wp_load with "Hℓin1"); iIntros "Hℓin1"; wp_pures.
    destruct vspace as [|vsp1 vspr]; first (cbn in *; lia).
    cbn. iDestruct "Hℓout" as "(Hℓou0&HℓouR)". rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓou0"); iIntros "Hℓou0"; wp_pures.
    wp_pure _; first apply ptr_offset_add.
    wp_pures. replace (Z.of_nat (S (S (length bin))) - 2)%Z with (Z.of_nat (length bin)) by lia.
    wp_pure _; first apply ptr_offset_add.
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
      iIntros (v) "(%bout&%vout&%vrest&->&->&->&(%vov&->)&HℓouR&HℓinR)".
      wp_pures. iModIntro.
      iExists (0%Z :: compress_buffer bin), _, vrest. iSplit; first done. iFrame.
      repeat iSplit; try iPureIntro.
      - done.
      - cbn. do 2 f_equal. lia.
      - cbn. by exists (vsp1 :: vov).
      - unfold array. iApply (big_sepL_wand with "HℓinR").
        iApply big_sepL_intro. iIntros "!> % % % H". rewrite loc_add_assoc.
           replace (Z.of_nat (S (S k))) with (2 + k)%Z by lia. done.
    }
  }
  { wp_bind (if: _ then _ else #0)%CE.
    iApply (wp_wand _ _ _ (λ v, ⌜v = #0⌝ ∗ ℓin ↦C #bfst ∗ (ℓin +ₗ 1) ↦C #bsnd)%I with "[Hℓin0 Hℓin1]").
    { wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
      rewrite bool_decide_decide. destruct decide.
      { wp_pures; wp_pure _; first eapply ptr_offset_add.
        wp_apply (wp_load with "Hℓin1"); iIntros "Hℓin1"; wp_pures.
        rewrite bool_decide_decide. destruct decide; try lia.
        iModIntro. iFrame. done. }
      { wp_pures. iModIntro. iFrame. done. }
    }
    iIntros (?) "(->&Hℓin0&Hℓin1)". wp_pures.
    destruct vspace as [|vsp1 [|vsp2 vspr]]; try (cbn in *; lia).
    cbn. iDestruct "Hℓout" as "(Hℓou0&Hℓou1&HℓouR)". rewrite !loc_add_0.
    wp_apply (wp_store with "Hℓou0"); iIntros "Hℓou0"; wp_pures.
    wp_pure _; first eapply ptr_offset_add.
    wp_apply (wp_load with "Hℓin0"); iIntros "Hℓin0"; wp_pures.
    wp_apply (wp_store with "Hℓou1"); iIntros "Hℓou1"; wp_pures.
    wp_pure _; first apply ptr_offset_add.
    wp_pures. replace (Z.of_nat (S (S (length bin))) - 1)%Z with (Z.of_nat (S (length bin))) by lia.
    wp_pure _; first apply ptr_offset_add.
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
      iIntros (v) "(%bout&%vout&%vrest&->&->&->&(%vov&->)&HℓouR&Hℓin1&HℓinR)".
      wp_pures. iModIntro.
      iExists (1%Z :: bfst :: compress_buffer (bsnd :: bin)), _, vrest. iSplit; first done.
      repeat iSplit; try iPureIntro. 4: cbn; iFrame.
      - do 4 (cbn in *; case_match; try (exfalso; by eapply Hnn); simplify_eq; try congruence).
      - cbn. do 2 f_equal. repeat case_match; cbn in *; lia.
      - cbn. by exists (vsp1 :: vsp2 :: vov).
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

Lemma buffy_compress_spec E ℓin ℓout ℓlen vin bin vspace :
   isBuffer vin bin →
   length vspace ≥ buffer_max_len (length bin) →
(⊢  ℓin  ↦C∗ vin
 -∗ ℓout ↦C∗ vspace
 -∗ ℓlen ↦C  #(length vspace)
 -∗ WP (call: &buffy_compress_name with (Val #ℓin, Val #(length bin), Val #ℓout, Val #ℓlen))%CE @ buffy_prog_env; E
    {{ v', ∃ bout vout vrest,
             ⌜isBuffer vout bout⌝
           ∗ ⌜bout = compress_buffer bin⌝
           ∗ ⌜v' = #0⌝
           ∗ (∃ voverwritten, ⌜vspace = voverwritten ++ vrest⌝)
           ∗ ℓout ↦C∗ (vout ++ vrest)
           ∗ ℓin  ↦C∗ vin 
           ∗ ℓlen ↦C  #(length vout)}})%I.
Proof.
  iIntros (HBuffer Hlength) "Hℓin Hℓout Hℓlen".
  wp_pures.
  wp_apply (wp_load with "Hℓlen"); iIntros "Hℓlen".
  wp_bind (FunCall _ _).
  iApply wp_wand. 1: iApply buffy_max_len_spec; first done. cbn.
  iIntros (?) "->".
  wp_pures. rewrite bool_decide_decide. destruct decide; cbn in *; try lia.
  wp_pure _. wp_bind (FunCall _ _).
  iApply (wp_wand with "[Hℓin Hℓout]").
  1: by iApply (buffy_compress_rec_spec with "[Hℓin]").
  cbn.
  iIntros (v) "(%bout&%vout&%vrest&Hbuf&HH1&->&HH3&HℓouR&HℓinR)".
  wp_apply (wp_store with "Hℓlen"); iIntros "Hℓlen".
  wp_pures. iModIntro.
  iExists bout, vout, vrest. by iFrame.
Qed.


Lemma buffy_compress_spec_too_small E ℓlen (z:Z) (nlen:nat) vv1 vv2 :
    (z < buffer_max_len (nlen))%Z →
(⊢  ℓlen ↦C #z
 -∗ WP (call: &buffy_compress_name with (Val vv1, Val #(nlen), Val vv2, Val #ℓlen))%CE @ buffy_prog_env; E
    {{ v', ℓlen ↦C #z ∗ ⌜v' = #1⌝}})%I.
Proof.
  iIntros (Hlen) "Hℓlen".
  wp_pures.
  wp_apply (wp_load with "Hℓlen"); iIntros "Hℓlen".
  wp_bind (FunCall _ _).
  iApply wp_wand. 1: iApply buffy_max_len_spec; first done. cbn.
  iIntros (?) "->".
  wp_pures. rewrite bool_decide_decide. destruct decide; cbn in *; try lia.
  wp_pures. iModIntro. iFrame. done.
Qed.

End CBuffers.

