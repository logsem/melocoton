From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import basics basics_resources wrapper_wp.
Import Wrap.

Section BlockSimLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Lemma block_sim_of_ghost_state (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     lloc_own_auth wrapperGS_γχ χvirt
  -∗ lstore_own_auth wrapperGS_γζ ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜is_val χvirt ζfreeze v b⌝
  -∗ block_sim v b.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iDestruct (lstore_own_auth_get_immut_all with "Hζ") as "#Hζimm".
  iInduction H as [] "IH" forall "Hζ Hχ"; cbn; try done.
  1: iExists γ; iSplit; first done.
  1: by iApply (lloc_own_auth_get_pub with "Hχ").
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  1,3,5: iApply (big_sepM_lookup with "Hζimm"); try done.
  4: iSplit.
  4,6,7: by iApply ("IH" with "[] [] [] Hζ Hχ").
  4: by iApply ("IH1" with "[] [] [] Hζ Hχ").
  all: simplify_eq.
  all: apply lstore_immut_blocks_lookup_immut.
  all: match goal with H: (_ ∪ _) !! _ = Some _ |- _ =>
      apply lookup_union_Some in H as [|]; eauto end.
  all: destruct Hstorebl as [_ Hstorebl2].
  all: specialize (Hstorebl2 γ) as [Hstorebl2 _].
  all: destruct Hstorebl2 as (ℓ & Vs & Hχ & Hσml); [by eapply elem_of_dom_2|].
  all: efeed specialize Hstore; eauto; [eapply lookup_union_Some; by eauto|].
  all: inversion Hstore.
Qed.

Lemma block_sim_arr_of_ghost_state (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs b :
     lloc_own_auth wrapperGS_γχ χvirt
  -∗ lstore_own_auth wrapperGS_γζ ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs b⌝
  -∗ block_sim_arr vs b.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iApply big_sepL2_forall; iSplit; first (iPureIntro; by eapply Forall2_length).
  iIntros "%k %v %l %H1 %H2".
  iApply (block_sim_of_ghost_state with "Hχ Hζ"); try done.
  iPureIntro. eapply Forall2_lookup_lr; done.
Qed.

Lemma block_sim_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     lloc_own_auth wrapperGS_γχ χvirt
  -∗ lstore_own_auth wrapperGS_γζ ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗ block_sim v b
  -∗⌜is_val χvirt ζfreeze v b⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iInduction v as [[x|bo| |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & -> & Hsim)". unfold block_sim_raw.
      iPoseProof (lloc_own_pub_of with "Hχ Hsim") as "%HH".
      iPureIntro. econstructor. done. }
  1: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hlv2") as "%Hr2".
  2-3: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hlv") as "%Hr".
  1-3: unshelve iPoseProof (lstore_own_immut_of with "Hζ Hsim") as "[%HH _]".
  all: iPureIntro; econstructor; eauto; by simplify_map_eq.
Qed.

Lemma block_sim_arr_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
     lloc_own_auth wrapperGS_γχ χvirt
  -∗ lstore_own_auth wrapperGS_γζ ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗ block_sim_arr vs bb
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iPoseProof (big_sepL2_forall with "Hsim") as "(%Heq & Hsim)".
  iAssert (⌜(∀ i x y, vs !! i = Some x → bb !! i = Some y → is_val χvirt ζfreeze x y)⌝)%I as "%HF".
  2: iPureIntro; by apply Forall2_same_length_lookup_2.
  iIntros (i v b H1 H2).
  iApply (block_sim_to_ghost_state with "Hχ Hζ"); try done.
  iApply ("Hsim" $! i v b H1 H2).
Qed.

End BlockSimLaws.


