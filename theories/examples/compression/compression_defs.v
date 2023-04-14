From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.

Section SemBuffers.
(** Of course, snappy is more complicated than this ..*)
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
