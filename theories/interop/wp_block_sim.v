From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import lang state.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import basics basics_resources weakestpre.
Import Wrap.

Section BlockSimLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Implicit Types P : iProp Σ.

Lemma block_sim_of_ghost_state (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     lloc_own_auth χvirt
  -∗ lstore_own_auth ζvirt
  -∗⌜ζfreeze = ζσ ∪ ζvirt⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζvirt⌝
  -∗⌜is_val χvirt ζfreeze v b⌝
  -∗ b ~~ v.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iDestruct (lstore_own_auth_get_immut_all with "Hζ") as "#Hζimm".
  iInduction H as [] "IH" forall "Hζ Hχ"; cbn; try done.
  1: iExists γ; iSplit; first done.
  1: by iApply (lloc_own_auth_get_pub with "Hχ").
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  7: iExists γ; iSplit; first done.
  1,3,5,7: iApply (big_sepM_lookup with "Hζimm"); try done.
  5: iSplit.
  5,7,8: by iApply ("IH" with "[] [] [] Hζ Hχ").
  5: by iApply ("IH1" with "[] [] [] Hζ Hχ").
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

Lemma block_sim_arr_of_ghost_state (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
     lloc_own_auth χvirt
  -∗ lstore_own_auth ζvirt
  -∗⌜ζfreeze = ζσ ∪ ζvirt⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζvirt⌝
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝
  -∗ bb ~~∗ vs.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iApply big_sepL2_forall; iSplit; first (iPureIntro; by eapply Forall2_length).
  iIntros "%k %v %l %H1 %H2".
  iApply (block_sim_of_ghost_state with "Hχ Hζ"); try done.
  iPureIntro. eapply Forall2_lookup_lr; done.
Qed.

Lemma block_sim_to_ghost_state  (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     lloc_own_auth χvirt
  -∗ lstore_own_auth ζvirt
  -∗⌜ζfreeze = ζσ ∪ ζvirt⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζvirt⌝
  -∗ b ~~ v
  -∗⌜is_val χvirt ζfreeze v b⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iInduction v as [[x|bo| |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & -> & Hsim)".
      iPoseProof (lloc_own_pub_of with "Hχ Hsim") as "%HH".
      iPureIntro. econstructor. done. }
  1: iDestruct "Hsim" as "(%γ & -> & Hsim)".
  2: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hlv2") as "%Hr2".
  3-4: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hlv") as "%Hr".
  1-4: unshelve iPoseProof (lstore_own_immut_of with "Hζ Hsim") as "[%HH _]".
  all: iPureIntro; econstructor; eauto; by simplify_map_eq.
Qed.

Lemma block_sim_arr_to_ghost_state  (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
     lloc_own_auth χvirt
  -∗ lstore_own_auth ζvirt
  -∗⌜ζfreeze = ζσ ∪ ζvirt⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζvirt⌝
  -∗ bb ~~∗ vs
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
