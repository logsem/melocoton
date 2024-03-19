(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.
*)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Export resources.
From melocoton.c_lang Require Export primitive_laws.
From melocoton.c_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context {SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.
Context {p:program}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : gmap loc heap_cell.
Implicit Types v : option val.
Implicit Types vs : list (option val).
Implicit Types l : loc.
Implicit Types sz off : nat.

(** Allocation *)
Lemma wp_Malloc s E n :
  (0 < n)%Z →
  {{{ True }}} Malloc (Val $ LitV $ LitInt $ n) @ s; E
  {{{ l, RET LitV (LitLoc l); l I↦C∗ replicate (Z.to_nat n) None }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply wp_Malloc_seq; [done..|]. iModIntro.
  iIntros (l) "Hlm". iApply "HΦ".
  by iApply mapsto_seq_array.
Qed.

Lemma wp_Malloc_vec s E n :
  (0 < n)%Z →
  {{{ True }}}
    Malloc #n @ s ; E
  {{{ l, RET #l; l I↦C∗ vreplicate (Z.to_nat n) None }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply wp_Malloc; [ lia | done | .. ]. iModIntro.
  iIntros (l) "Hl". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

(** Accessing array elements *)
Lemma wp_load_offset s E l dq off vs (v:val) :
  vs !! off = Some (Some v) →
  {{{ ▷ l I↦C∗{dq} vs }}} * #(l +ₗ off) @ s; E {{{ RET v; l I↦C∗{dq} vs }}}%CE.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_load with "Hl1"). iModIntro. iIntros "Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! (Some v)) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset s E l off vs (v:val) :
  off < length vs →
  {{{ ▷ l I↦C∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #0; l I↦C∗ <[off:=Some v]> vs }}}%CE.
Proof.
  iIntros (Hlength Φ) ">Hl HΦ".
  destruct (lookup_lt_is_Some_2 _ _ Hlength) as [vv Hlookup].
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1"). iModIntro. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec (option val) sz) (v:val) :
  {{{ ▷ l I↦C∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #0; l I↦C∗ vinsert off (Some v) vs }}}%CE.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  rewrite vec_to_list_length. apply fin_to_nat_lt.
Qed.

(** Freeing a region *)
Lemma wp_free_array s E l vs :
  {{{ ▷ l I↦C∗ vs }}} free (#l, #(Z.of_nat (length vs))) @ s; E {{{ RET LitV LitUnit; True }}}%CE.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>".
  iAssert (⌜∀ i : Z, (0 ≤ i)%Z → (i < length vs)%Z → ∃ v0, σ1 !! (l +ₗ i) = Some (Some v0)⌝)%I as "%Halloc".
  1: { iIntros (i H1 H2). destruct (vs !! (Z.to_nat i)) as [vv|] eqn:Heq.
       2: { apply lookup_ge_None_1 in Heq. lia. }
       iPoseProof (big_sepL_lookup_acc with "Hl") as "(Hpto&Hl)". 1: apply Heq.
       iDestruct (gen_heap_valid with "Hσ Hpto") as %?.
       iPureIntro. exists vv. rewrite <- H. do 2 f_equal. lia. }
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  iFrame.
  iSplitL.
  2: { iModIntro. iFrame. iIntros "HΦ". iModIntro. by iApply "HΦ". }
  clear H4 Halloc.
  iInduction vs as [|vh vr] "IH" forall (l σ1).
  - iModIntro. cbn. unfold state_init_heap, state_upd_heap.
    change (Z.to_nat 0%nat) with 0. cbn. rewrite map_empty_union. iFrame.
  - cbn. iDestruct "Hl" as "(Hpto&Hl)". destruct l as [l].
    unfold loc_add. cbn.
    iMod ("IH" $! (Loc (l + 1)) with "[Hl] Hσ") as "Hσ".
    1: { iApply (big_sepL_impl with "Hl").
         iIntros "!> %k %x %H1 H2". unfold loc_add. cbn.
         replace (l + 1 + k)%Z with (l + S k)%Z by lia. done. }
    replace (l + 0%nat)%Z with l by lia.
    iMod (gen_heap_update _ (Loc l) _ Deallocated with "Hσ Hpto") as "[Hσ Hpto]".
    iModIntro. unfold state_init_heap, state_upd_heap.
    rewrite insert_union_l !Nat2Z.id.
    cbn. rewrite insert_union_singleton_l.
    unfold loc_add. cbn. done.
Qed.

Lemma wp_free_array' s E l z vs :
  z = Z.of_nat (length vs) →
  {{{ ▷ l I↦C∗ vs }}} free (#l, #z) @ s; E {{{ RET LitV LitUnit; True }}}%CE.
Proof. iIntros (-> Φ) "H HΦ". by iApply (wp_free_array with "H"). Qed.

End lifting.

#[export] Typeclasses Opaque array.
