From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From stdpp Require Import list.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
From melocoton.interop Require Import lang weakestpre.
From melocoton.language Require Import weakestpre progenv.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.examples.compression Require Import compression_defs buffers_specs.

Section ListUtils.

  (* construction for the list insertion/update syntax:
     list [i := f(i), ... j-1 := f(j-1) ] is defined by
      list_parallel_insert_extending f i j l *)

  Fixpoint tabulate {A:Type} (f : nat → A) (n:nat) : list A := match n with
    0 => nil
  | S n => f 0 :: tabulate (λ n, f (S n)) n end.

  Lemma tabulate_lookup {A} (f : nat → A) n i : i < n → tabulate f n !! i = Some (f i).
  Proof.
    induction n in f,i|-*; first lia.
    destruct i; first done.
    intros Hl; cbn.
    apply (IHn (λ m, f (S m)) i). lia.
  Qed.

  Lemma tabulate_lookup_ge {A} (f : nat → A) n i : i ≥ n → tabulate f n !! i = None.
  Proof.
    induction n in f,i|-*; first done.
    destruct i; first lia.
    intros Hl; cbn. apply IHn. lia.
  Qed.

  Lemma tabulate_ext {A} (f1 f2 : nat → A) n : (∀ i,i < n → f1 i = f2 i) → tabulate f1 n = tabulate f2 n.
  Proof.
    intros Heq. apply list_eq.
    intros i. destruct (decide (i < n)).
    - rewrite !tabulate_lookup; try lia. f_equal. by apply Heq.
    - rewrite !tabulate_lookup_ge; try lia. done.
  Qed.

  Program Fixpoint list_parallel_insert_extending {A:Type} (f : nat → A) (i j : nat) (l : list A) (Hvalid : i ≤ length l) : list A :=
    match l with
      nil => tabulate f j
    | x::lr => match j with 0 => x::lr | _ => (match i with 0 => f 0 | _ => x end) :: list_parallel_insert_extending (λ n, f (S n)) (i-1) (j-1) lr _ end
    end.
  Next Obligation. intros A f i j l Hl x lr <- w Hw <- _ _ n; done. Qed.
  Next Obligation. intros A f i j l Hl x lr <- w Hw <-. cbn in *. lia. Qed.
  Next Obligation. intros HH A f i j l Hl x lr <- _ _ n; done. Qed.

  Lemma list_parallel_insert_extending_ext {A} (f1 f2 : nat → A) i1 i2 j l HH1 HH2 : (∀ k, i1 ≤ k → k < j → f1 k = f2 k) → i1 = i2 →
    list_parallel_insert_extending f1 i1 j l HH1 = list_parallel_insert_extending f2 i2 j l HH2.
  Proof.
    induction l in f1,f2,i1,i2,j,HH1,HH2|-*; cbn in *.
    - intros H1 ->. replace i2 with 0 by lia. apply tabulate_ext.
      intros k Hk; eapply H1; lia.
    - intros Heq ->. destruct j; first done. f_equal.
      + destruct i2; try done. apply Heq; first done. lia.
      + eapply IHl. 2:done. intros k Hk1 Hk2. eapply Heq; lia.
  Qed.

  Lemma list_parallel_insert_extending_j_zero {A} (f : nat → A) i l HH :
    list_parallel_insert_extending f i 0 l HH = l.
  Proof.
    induction l in i,HH|-*; cbn in *; done.
  Qed.

  Lemma list_parallel_insert_extending_befores {A} (f : nat → A) i j l k HH :
      k < i → list_parallel_insert_extending f i j l HH !! k = l !! k.
  Proof.
    induction l in f,i,j,HH,k|-* ; cbn in *. 1:lia.
    destruct k; cbn.
    { intros Hlt; destruct j,i; try lia; done. }
    intros Hk. destruct j; first done.
    destruct i; try lia; cbn.
    eapply IHl. lia.
  Qed.
  Lemma list_parallel_insert_extending_shift {A} (f : nat → A) i j l k HH HH2:
      i ≤ k → list_parallel_insert_extending f i j l HH !! k
            = list_parallel_insert_extending (λ x, f (i+x)) 0 (j-i) (drop i l) HH2 !! (k-i).
  Proof.
    induction l in f,i,j,HH,HH2,k|-*.
    - cbn in *. assert (i=0) as Heq by lia. subst i.
      replace (j-0) with j by lia.
      cbn. replace (k-0) with k by lia. done.
    - destruct j.
      + cbn in *. replace (0-i) with 0 by lia.
        rewrite list_parallel_insert_extending_j_zero lookup_drop.
        intros Hk. f_equal. lia.
      + destruct i.
        * rewrite !Nat.sub_0_r. intros _. change (drop 0 ?a) with a.
          erewrite list_parallel_insert_extending_ext; done.
        * intros Hle. destruct k; first lia. cbn.
          rewrite (Nat.sub_0_r j).
          unshelve erewrite list_parallel_insert_extending_ext. 6: rewrite Nat.sub_0_r //.
          3: eapply (IHl (λ k, (f (S k)))); lia. 2: done. cbn in *; lia.
  Qed.

  Lemma list_parallel_insert_extending_middle {A} (f : nat → A) i j l k HH :
      i ≤ k → k < j → list_parallel_insert_extending f i j l HH !! k = Some (f k).
  Proof.
    induction l in f,i,j,HH,k|-* ; intros HH1 HH2.
    1: cbn; rewrite tabulate_lookup; try done; lia.
    cbn. destruct j.
    1: lia.
    destruct i, k.
    - done.
    - cbn. erewrite IHl; first done; lia.
    - lia.
    - cbn. erewrite IHl; first done; lia.
  Qed.

  Lemma list_parallel_insert_extending_end {A} (f : nat → A) i j l k HH :
      k ≥ j → list_parallel_insert_extending f i j l HH !! k = l !! k.
  Proof.
    induction l in f,i,j,HH,k|-* ; intros HH1.
    1: cbn; rewrite tabulate_lookup_ge; first done; lia.
    cbn. destruct j.
    1: done.
    destruct i, k.
    - lia.
    - cbn. erewrite IHl; first done; lia.
    - done.
    - cbn. erewrite IHl; first done; lia.
  Qed.

  Lemma list_parallel_insert_extending_noop {A} (f : nat → A) i j l HH :
      j ≤ i → list_parallel_insert_extending f i j l HH = l.
  Proof.
    intros H.
    eapply list_eq; intros k.
    destruct (decide (k < i)).
    - rewrite list_parallel_insert_extending_befores; last lia. done.
    - rewrite list_parallel_insert_extending_end; last lia. done.
  Qed.

  Lemma list_parallel_insert_extending_length_1 {A} (f : nat → A) i j l HH :
    length (list_parallel_insert_extending f i j l HH) ≤ max j (length l).
  Proof.
    apply lookup_ge_None.
    rewrite list_parallel_insert_extending_end. 2: lia.
    apply lookup_ge_None. lia.
  Qed.

  Lemma list_parallel_insert_extending_length_2 {A} (f : nat → A) i j l HH :
    length (list_parallel_insert_extending f i j l HH) ≥ max j (length l).
  Proof.
    destruct (decide (max j (length l) = 0)); first lia.
    assert (exists k, S k = max j (length l)) as [k Hk]; first (exists ((max j (length l))-1); lia).
    enough (length (list_parallel_insert_extending f i j l HH) > k) by lia.
    destruct (decide (j < max j (length l)));
    eapply lookup_lt_is_Some.
    - rewrite list_parallel_insert_extending_end; last lia.
      eapply lookup_lt_is_Some. lia.
    - destruct (decide (i ≤ k)).
      + rewrite list_parallel_insert_extending_middle. 2-3: lia. done.
      + rewrite list_parallel_insert_extending_befores. 2: lia.
        eapply lookup_lt_is_Some. lia.
  Qed.

  Lemma list_parallel_insert_extending_length {A} (f : nat → A) i j l HH :
    length (list_parallel_insert_extending f i j l HH) = max j (length l).
  Proof.
    eapply Nat.le_antisymm.
    - apply list_parallel_insert_extending_length_1.
    - apply list_parallel_insert_extending_length_2.
  Qed.

  Lemma list_parallel_insert_extending_extend {A} (f : nat → A) i j l HH : length l ≤ j →
    list_parallel_insert_extending f i (S j) l HH = list_parallel_insert_extending f i j l HH ++ [f j].
  Proof.
    intros Hlen. eapply list_eq.
    intros k. destruct (Nat.lt_trichotomy k j) as [H|[H|H]].
    - destruct (decide (k<i)).
      * rewrite lookup_app_l. 2: rewrite list_parallel_insert_extending_length max_l. 2-3: lia.
        rewrite !list_parallel_insert_extending_befores; first done; lia.
      * rewrite lookup_app_l. 2: rewrite list_parallel_insert_extending_length max_l. 2-3: lia.
        rewrite !list_parallel_insert_extending_middle; first done; lia.
    - subst k. rewrite list_parallel_insert_extending_middle. 2-3: lia.
      rewrite lookup_app_r.
      all: rewrite list_parallel_insert_extending_length max_l. 2-4:lia.
      by rewrite Nat.sub_diag.
    - rewrite lookup_app_r.
      all: rewrite list_parallel_insert_extending_length max_l. 2-4:lia.
      rewrite list_parallel_insert_extending_end; last lia.
      destruct (k-j) eqn:Heq; try lia. cbn. rewrite lookup_nil.
      apply lookup_ge_None. lia.
  Qed.

  Lemma list_parallel_insert_extending_insert {A} (f : nat → A) i j l HH : length l > j → j ≥ i →
    list_parallel_insert_extending f i (S j) l HH = <[j := f j]> (list_parallel_insert_extending f i j l HH).
  Proof.
    intros Hlen Hlen2. eapply list_eq.
    intros k. destruct (Nat.lt_trichotomy k j) as [H|[H|H]].
    - destruct (decide (k<i)).
      * rewrite list_lookup_insert_ne; last lia.
        rewrite !list_parallel_insert_extending_befores; first done; lia.
      * rewrite list_lookup_insert_ne; last lia.
        rewrite !list_parallel_insert_extending_middle; first done; lia.
    - subst k. rewrite list_parallel_insert_extending_middle. 2-3: lia.
      rewrite list_lookup_insert; first done.
      rewrite list_parallel_insert_extending_length max_r; lia.
    - rewrite list_lookup_insert_ne; last lia.
      rewrite !list_parallel_insert_extending_end; try done; lia.
  Qed.

End ListUtils.

Section Specs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition bf (a : Cval) (cap : nat) (arr : list Z) : iProp Σ :=
    ∃ (vcontent:list (option val)) (zcontent zrest : list (option Z)) (ℓ:loc),
    ⌜zcontent = fmap Some arr ++ zrest⌝
  ∗ ⌜vcontent = fmap (option_map (λ (z:Z), #z)) zcontent⌝
  ∗ ⌜length vcontent = cap⌝
  ∗ ⌜a = #ℓ⌝
  ∗ ℓ I↦C∗ vcontent.

  Definition Pb (cap : nat) (arr : list Z) : list (option Z) → iProp Σ := (λ k, ∃ (zrest : list (option Z)), ⌜k = fmap Some arr ++ zrest⌝ ∗ ⌜cap = length k⌝)%I.
  Definition Pbu (arr : list Z) : nat → list (option Z) → iProp Σ := (λ used k, ∃ (zrest : list (option Z)), ⌜k = fmap Some arr ++ zrest⌝ ∗ ⌜used  = length arr⌝)%I.

  Definition bytes (V : MLval) (cap : Z) (arr : list Z) : iProp Σ :=
    ∃ γ ℓbuf (ncap:nat),
      ⌜V = #ML (ML_lang.LitForeign γ)⌝ ∗ ⌜cap = ncap⌝
    ∗ isBufferForeignBlock γ ℓbuf (Pb ncap arr) ncap.

  Definition buf_RT γ (cap : Z) (arr : list Z) : iProp Σ :=
    ∃ ℓ (ncap:nat), ⌜cap = ncap⌝ ∗ isBufferRecord (Lloc γ) ℓ (Pbu arr) ncap .

  Definition buffer_ML_pre ℓ V (cap : Z) (arr : list Z) : iProp Σ :=
    ∃ (ncap:nat), ⌜cap = ncap⌝ ∗ isBufferRecordML V ℓ (Pbu arr) ncap.
  Definition buffer_ML V (cap : Z) (arr : list Z) : iProp Σ :=
    ∃ ℓ, buffer_ML_pre ℓ V cap arr.

  Import melocoton.ml_lang.notation.
  Definition buf_alloc_spec_ML_simple s vv Φ : iProp Σ :=
    ∃ (z:Z),
      "->" ∷ ⌜s = buf_alloc_name⌝
    ∗ "->" ∷ ⌜vv = [ #z ]⌝
    ∗ "%Hb1" ∷ ⌜(0 < z)%Z⌝
    ∗ "HCont" ∷ ▷ (∀ v, buffer_ML v z nil -∗ Φ (OVal v)).

  Lemma buf_alloc_spec_ML_simple_refines :
    buf_alloc_spec_ML_simple ⊑ buf_alloc_spec_ML.
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iExists z. iFrame. repeat (iSplit; first done).
    iNext. iIntros (v ℓbuf) "HBuf". iApply ("HCont" $! v).
    iExists ℓbuf, (Z.to_nat z). iSplit; first (iPureIntro; lia).
    iApply isBufferRecordML_ext; last iFrame.
    iIntros (u lst _) "(->&->)".
    iExists _. cbn. done.
  Qed.

  Definition buf_update_spec_ML_simple Ψcb s vv (Φ:(outcome MLval) → iProp Σ) : iProp Σ :=
    ∃ (i j : nat) b1 b2 F V n m (P : Z → iProp Σ) (f : Z → Z)
      (Hblen : (i ≤ length m)),
      "->" ∷ ⌜s = buf_upd_name⌝
    ∗ "->" ∷ ⌜vv = [ #i; #j; (RecV b1 b2 F); V ]⌝
    ∗ "%Hb1" ∷ ⌜0%Z ≤ i⌝%Z
    ∗ "%Hb2" ∷ ⌜i ≤ j+1⌝%Z
    ∗ "%Hb3" ∷ ⌜j < n⌝%Z
    ∗ "Hbuffer" ∷ buffer_ML V n m
    ∗ "HP" ∷ P i
    ∗ "#Hcallback" ∷ (□ ∀ k, P(k) -∗ WP (RecV b1 b2 F) (#k) at ⟨ ∅, Ψcb ⟩ {{ v, ⌜v = OVal #(f k)⌝ ∗ P (k+1)%Z}})
    ∗ "HCont" ∷ ▷ (buffer_ML V n (list_parallel_insert_extending f i (j+1) m Hblen) -∗ P (j+1) -∗ Φ (OVal #())).

  Lemma buf_update_spec_ML_simple_refines Ψ :
    buf_update_spec_ML_simple Ψ ⊑ buf_update_spec_ML Ψ.
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iDestruct "Hbuffer" as "(%ℓ&%ncap&%Heqn&HBuffer)".
    pose (λ z, P z ∗ buffer_ML_pre ℓ V n (list_parallel_insert_extending f i (Z.to_nat z) m Hblen))%I as Ψupd.
    pose (λ k v, ⌜v = f k⌝ : iProp Σ)%I as Φz.
    pose (λ z, Pbu (list_parallel_insert_extending f i (Z.to_nat z) m Hblen)) as Pbz.
    iExists Ψupd, P, Φz, i, j, ℓ, ncap, Pbz.
    iExists V, _, _, _.
    repeat (iSplit; first (try done; iPureIntro; lia)).
    iFrame "HP".
    iSplit; last iSplit; last iSplitL "HBuffer"; last iSplitR.
    - iIntros (z vnew HH1 HH2) "!> Hp -> HBuffer !>".
      iFrame "Hp". iExists ncap. iSplit; first done.
      iApply isBufferRecordML_ext; last done.
      iIntros (zz lst Heqcap) "H1". unfold buf_alloc1_spec, Pbz, Pbu.
      iDestruct "H1" as (bold capold HHeq1 HHeq2 zrest HHeq3) "%Hcapold". subst lst zz bold capold.
      rewrite insert_length app_length fmap_length list_parallel_insert_extending_length in Heqcap.
        replace (Z.to_nat (z+1)%Z) with (S(Z.to_nat z)) by lia.
      destruct (decide ((Z.of_nat (length m) ≤ z)%Z)).
      + destruct zrest as [|zrest1 zrest]. 1: cbn in *; lia.
        iExists zrest.
        rewrite list_parallel_insert_extending_extend; last lia.
        iPureIntro; split_and!.
        * erewrite insert_app_r_alt.
          all: rewrite fmap_length list_parallel_insert_extending_length. 2: lia.
          rewrite max_l; last lia.
          rewrite Nat.sub_diag fmap_app -app_assoc /=. do 4 f_equal. lia.
        * rewrite app_length list_parallel_insert_extending_length /=. lia.
      + iExists zrest.
        rewrite list_parallel_insert_extending_insert; try lia.
        iPureIntro; split_and!.
        * erewrite insert_app_l.
          2: rewrite fmap_length list_parallel_insert_extending_length; lia.
          rewrite list_fmap_insert. repeat (f_equal; try lia).
        * rewrite insert_length list_parallel_insert_extending_length; lia.
    - iIntros "!> !>" (z Hz1 Hz2) "(HP&(%ncap2&%Hncap2&HBuffer))".
      subst n. apply Nat2Z.inj' in Hncap2. subst ncap2.
      iApply (wp_wand with "(Hcallback HP)").
      iIntros (?) "(->&HP)". iExists (f z). iSplit; first done.
      iSplit; first done. iFrame.
    - iApply isBufferRecordML_ext; last done.
      iIntros (zz lst Heqcap) "H1". unfold Pbz, Pbu.
      rewrite Nat2Z.id list_parallel_insert_extending_noop; last lia. iApply "H1".
    - iIntros "(HP&HH)". iModIntro. iFrame. iExists ncap. iSplit; first done.
      iApply isBufferRecordML_ext; last done.
      iIntros (???) "H". unfold Pbz, Pbu.
      rewrite Nat2Z.id list_parallel_insert_extending_noop; last lia. iApply "H".
    - iNext. iIntros "(HP&HH)". iApply ("HCont" with "[HH] [HP]").
      + iExists ℓ. replace (Z.to_nat (j + 1)) with (j+1) by lia. done.
      + iClear "Hcallback". iStopProof. f_equiv. lia.
  Qed.

End Specs.

