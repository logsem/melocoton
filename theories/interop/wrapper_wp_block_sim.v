From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics wrapper_wp.
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

(* todo: lemmas to help manipulate is_store_blocks? *)
Lemma block_sim_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χvirt)
  -∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜is_val χvirt ζfreeze v b⌝
  -∗ block_sim v b.
Proof.
  iIntros "Hχ #Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iInduction H as [] "IH"; cbn; try done.
  1: iExists γ; iSplit; first done.
  1: iApply (gset_bij_own_elem_get with "Hχ"); by eapply elem_of_map_to_set_pair.
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  1,3,5: iApply (big_sepM_lookup with "Hζ"); try done.
  4: iSplit.
  4,6,7: by iApply "IH". 4: by iApply "IH1".
  all: subst.
  all: pose proof H as H1'.
  all: rewrite lookup_union in H.
  all: destruct (ζσ !! γ) eqn:Heq; rewrite Heq in H; unfold union_with in H; cbn in H.
  all: destruct (ζrest !! γ) eqn:Heq2; rewrite Heq2 in H; try congruence.
  1,4,7: exfalso; eapply map_disjoint_spec; done.
  2,4,6: rewrite Heq2; done.
  all: destruct Hstorebl as [Hstorebl1 Hstorebl2].
  all: unfold block in *.
  all: rewrite <- Heq in H; apply elem_of_dom_2 in Heq; apply Hstorebl2 in Heq.
  all: destruct Heq as (ℓ & Vs & Hχ & Hσml).
  all: unfold is_store in Hstore.
  all: specialize (Hstore _ _ _ _ Hσml Hχ H1').
  all: inversion Hstore.
Qed.

Lemma block_sim_arr_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs b :
     gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χvirt)
  -∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs b⌝
  -∗ block_sim_arr vs b.
Proof.
  iIntros "Hχ #Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iApply big_sepL2_forall; iSplit; first (iPureIntro; by eapply Forall2_length).
  iIntros "%k %v %l %H1 %H2".
  iApply (block_sim_of_ghost_state with "Hχ Hζ"); try done.
  iPureIntro. eapply Forall2_lookup_lr; done.
Qed.

Lemma block_sim_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χvirt)
  -∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗ block_sim v b
  -∗⌜is_val χvirt ζfreeze v b⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & -> & Hsim)". unfold block_sim_raw.
      iPoseProof (gset_bij_elem_of with "Hχ Hsim") as "%HH".
      apply elem_of_map_to_set_pair in HH.
      iPureIntro. econstructor. done. }
  1: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hlv2") as "%Hr2".
  2-3: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hlv") as "%Hr".
  1-3: unshelve iPoseProof (@ghost_map_lookup with "Hζ Hsim") as "%HH";
       iPureIntro; econstructor; eauto; subst;
       rewrite lookup_union; rewrite HH;
       destruct (ζσ !! γ) eqn:Heq; rewrite Heq; try done;
       eapply @map_disjoint_spec in Hdis; done.
Qed.

Lemma block_sim_arr_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
     gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χvirt)
  -∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
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

Lemma is_val_is_safe_on_heap χ ζ σ v l : dom χ ⊆ dom σ → is_val χ ζ v l → val_safe_on_heap σ v.
Proof.
  intros H1; induction 1; cbn; try done.
  2: split.
  1: eapply elem_of_dom_2 in H; set_solver.
  all: eauto.
Qed.





End BlockSimLaws.