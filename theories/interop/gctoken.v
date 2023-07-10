From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props stdpp_extra.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Export defs resources.
From melocoton.ml_lang Require Import lang_instantiation.
From melocoton.ml_lang Require Export lang primitive_laws.
From melocoton.interop Require Import basics_resources.

(** The [GC θ] resource.

   [GC θ] represents the collection of authoritative resources related to the ML
   runtime while running or interoperating with external C-like code. It is used
   e.g. in the points-to update laws that translate between ML and block-level
   pointsto.

   Its definition is best understood side-by-side with the wrapper state
   interpretation (in weakestpre.v), but is in its own separate file to make it
   possible to only import [GC θ] and relevant SL resources without depending on
   the wrapper WP and state interp.
 *)

Class wrapperGCtokGpre `{SI: indexT} Σ := WrapperGCtokGpre {
  wrapperG_locsetG :> ghost_varG Σ (gsetUR loc);
  wrapperG_addrmapG :> ghost_varG Σ (leibnizO addr_map);
  wrapperG_var_lstoreG :> ghost_varG Σ lstore;
  wrapperG_var_lloc_mapG :> ghost_varG Σ lloc_map;
  wrapperG_var_bool :> ghost_varG Σ (leibnizO bool);
}.

Class wrapperGCtokG `{SI: indexT} Σ := WrapperGCtokG {
  wrapperG_basics :> wrapperBasicsG Σ;
  wrapperG_inG :> wrapperGCtokGpre Σ;
  wrapperG_γζ : gname;
  wrapperG_γθ : gname;
  wrapperG_γχ : gname;
  wrapperG_γroots_set : gname;
  wrapperG_γat_init : gname;
}.

Definition wrapperGCtokΣ {SI: indexT} : gFunctors :=
  #[ghost_varΣ (gsetUR loc); ghost_varΣ (leibnizO addr_map);
    ghost_varΣ lstore; ghost_varΣ lloc_map; ghost_varΣ (leibnizO bool)].

Global Instance subG_wrapperGCtokGpre `{SI: indexT} Σ :
  subG wrapperGCtokΣ Σ → wrapperGCtokGpre Σ.
Proof. solve_inG. Qed.

Section GCtoken.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!wrapperGCtokG Σ}.

Definition per_location_invariant (ζ_future : lstore) (σMLvirt : store) (dirty : gset lloc)
     (γ : lloc) (ℓ : loc) : iProp Σ :=
  ∃ (vs : list val) lvs, 
    ( ℓ ↦∗ vs ∗ ⌜ζ_future !! γ = Some (Bvblock (Mut, (TagDefault, lvs)))⌝ ∗ block_canon_arr lvs vs)
  ∨ (⌜σMLvirt !! ℓ = Some vs⌝ ∗ (γ ↦mut (TagDefault, lvs)) ∗ lvs ~~∗ vs ∗ ℓ ↦Mlen (length lvs))
  ∨ (∃ (q r : Qp), ℓ ↦∗{# q} vs ∗ (γ ↦mut{DfracOwn r} (TagDefault, lvs)) ∗ lvs ~~∗ vs ∗ ⌜(q+r=1)%Qp⌝ ∗ ⌜γ ∈ dirty⌝)
  ∨ (⌜σMLvirt !! ℓ = None⌝ ∗ ⌜ζ_future !! γ = None⌝).
(* the last case is "phony" -- it should not exist, but we do not control χ good enough in the op sem *)

Definition SI_block_level (ζ_future : lstore) (χ_future : lloc_map) (dirty : gset lloc) : iProp Σ :=
  ∃ (σMLvirt : store),
    "GCχauth" ∷ lloc_own_auth χ_future
  ∗ "GCζauth" ∷ lstore_own_auth ζ_future
  ∗ "%Hother_blocks" ∷ ⌜dom ζ_future ⊆ dom χ_future⌝
  ∗ "GCσMLv" ∷ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ "GC_per_loc" ∷ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ_future,
      per_location_invariant ζ_future σMLvirt dirty γ ℓ)
  ∗ "%Hstore" ∷ ⌜∀ ℓ, ℓ ∈ dom σMLvirt → ∃ fid γ, χ_future !! γ = Some (LlocPublic fid ℓ)⌝.

Definition SI_GC (ζ_future : lstore) (θ : addr_map) (roots_s : gset addr) (χ : lloc_map) : iProp Σ :=
  ∃ (roots_m : gmap addr lval),
    "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 roots_m
  ∗ "GCrootspto" ∷ ([∗ map] a ↦ v ∈ roots_m, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝)
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝
  ∗ "%HGCOK" ∷ ⌜GC_correct ζ_future θ χ⌝.

Definition GC (θ : addr_map) (dirty : gset lloc) : iProp Σ :=
  ∃ (ζ ζ_future : lstore) (χ χ_future : lloc_map)
    (roots_s : gset addr),
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) roots_s
  ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "HSI_block_level" ∷ SI_block_level ζ_future χ_future dirty
  ∗ "HSI_GC" ∷ SI_GC ζ_future θ roots_s χ_future
  ∗ "%Hζfuture" ∷ ⌜freeze_lstore ζ ζ_future⌝
  ∗ "%Hχfuture" ∷ ⌜expose_llocs χ χ_future⌝.

Definition at_init := ghost_var wrapperG_γat_init (1/2) true.

Section Laws.

Lemma GC_per_loc_modify_σ M ζ σMLvirt dirty γ ℓ' v:
  gmap_inj M →
  M !! γ = Some ℓ' →
(([∗ map] y↦ℓ ∈ delete γ M, per_location_invariant ζ σMLvirt dirty y ℓ)
⊢ [∗ map] y↦ℓ ∈ delete γ M, per_location_invariant ζ (<[ ℓ' := v ]> σMLvirt) dirty y ℓ)%I.
Proof.
  iIntros (Hinj Hlu) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ (Hne&Hlu2)%lookup_delete_Some) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&#Hsim&#Hlen)|[HH|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft. by iFrame.
  - iRight. iLeft. iFrame "Hγ Hsim Hlen". iPureIntro.
    rewrite lookup_insert_ne; first done.
    intros ->. by eapply Hne, Hinj.
  - iRight. iRight. iLeft. done.
  - iRight. iRight. iRight. iPureIntro. split; last done.
    rewrite lookup_insert_ne; try done.
    intros ->. by eapply Hne, Hinj.
Qed.

Lemma GC_per_loc_insert M ζ σMLvirt dirty ℓ' v:
  (∀ γ, M !! γ ≠ Some ℓ') →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant ζ (<[ ℓ' := v ]> σMLvirt) dirty γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&#Hsim&#Hlen)|[HH|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft; by iFrame.
  - iRight. iLeft. iFrame "Hγ Hsim Hlen". iPureIntro.
    rewrite lookup_insert_ne; first done.
    intros ->. eapply Hnℓ, Hne.
  - iRight. iRight. iLeft. done.
  - iRight. iRight. iRight. iSplit; last done. iPureIntro.
    rewrite lookup_insert_ne; try done.
    intros ->. eapply Hnℓ, Hne.
Qed.

Lemma GC_per_loc_modify_ζ M ζ σMLvirt dirty γ v:
  M !! γ = None →
(([∗ map] x↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty x ℓ)
⊢ [∗ map] x↦ℓ ∈ M, per_location_invariant (<[ γ := v ]> ζ) σMLvirt dirty x ℓ)%I.
Proof.
  iIntros (Hne) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hle) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&Hsim&Hlen)|[HH|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft. iFrame. rewrite lookup_insert_ne; first done.
    intros ->; congruence.
  - iRight. iLeft. by iFrame.
  - iRight. iRight. iLeft. done.
  - iRight. iRight. iRight. iPureIntro; split; first done.
    rewrite lookup_insert_ne; try done.
    intros ->. simplify_eq.
Qed.


Lemma GC_per_loc_modify_ζ_in_detail M ζ σMLvirt dirty γ' tg lvs lvs':
  gmap_inj M →
  ζ !! γ' = Some (Bvblock (Mut, (tg, lvs))) →
  (length lvs = length lvs') →
  (∀ vs, block_canon_arr lvs vs -∗ ∃ vs', block_canon_arr lvs' vs') -∗
  lstore_own_elem γ' (DfracOwn 1) (Bvblock (Mut, (tg, lvs'))) -∗
  state_interp σMLvirt -∗
  ([∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty γ ℓ)
  ==∗ ∃ σMLvirt', ⌜dom σMLvirt' = dom σMLvirt⌝ ∗
      lstore_own_elem γ' (DfracOwn 1) (Bvblock (Mut, (tg, lvs')))
    ∗ state_interp σMLvirt'
    ∗([∗ map] γ↦ℓ ∈ M, per_location_invariant (<[ γ' := (Bvblock (Mut, (tg, lvs'))) ]> ζ) σMLvirt' dirty γ ℓ)%I.
Proof.
  iIntros (Hinj Heq Hlen) "Hsafe Hpto HSI Hbig".
  destruct (M !! γ') as [ℓ|] eqn:Hin.
  2: iModIntro; iExists _; iFrame; iSplit; first done; by iApply GC_per_loc_modify_ζ.
  iPoseProof (big_sepM_delete with "Hbig") as "((%vs'&%lvsin&[(Hℓ&%Hzeta&#Hcanon)|[(%Hℓσ&Hγ&Hsim&Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|(%Hnone1&%Hnone2)]]])&Hbig)"; first done.
  2: iDestruct "Hγ" as "(Hγ&_)"; by iDestruct (pgm_elem_ne with "Hpto Hγ") as %H.
  2: iDestruct "Hmapsγ" as "(Hγ&_)"; by iDestruct (pgm_elem_ne with "Hpto Hγ") as %H.
  2: exfalso; congruence.
  simplify_eq.
  iDestruct (big_sepL2_length with "Hcanon") as %Hlen1.
  iDestruct ("Hsafe" with "Hcanon") as "(%vs2&Hcanon2)".
  iDestruct (big_sepL2_length with "Hcanon2") as %Hlen2.
  iDestruct (pgm_lookup with "HSI Hℓ") as %Hinsigma.
  iMod (pgm_update (D:=MLHeapPGMData) vs2 with "HSI Hℓ") as "(HSI&Hℓ)".
  2: done. 1: cbn; rewrite Hlen1 Hlen2 //.
  iModIntro. iExists _.
  iFrame "HSI Hpto".
  iSplit; first by rewrite dom_insert_lookup_L.
  iApply big_sepM_delete; first done.
  iSplitR "Hbig".
  - iExists _,_. iLeft. iFrame. by rewrite lookup_insert.
  - iApply GC_per_loc_modify_ζ; first by rewrite lookup_delete.
    iApply GC_per_loc_modify_σ; done.
Qed.

Lemma GC_per_loc_make_dirty M ζ σMLvirt dirty dirty':
  dirty ⊆ dirty' →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty' γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&#Hsim&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft; iFrame; repeat iSplit; try done; iPureIntro; set_solver.
  - iRight. iLeft. iFrame "Hγ Hsim Hlen". iPureIntro. done.
  - iRight. iRight. iLeft. iExists q,r. iFrame. iFrame "Hsim". iPureIntro; split_and!; try done.
    by eapply elem_of_weaken.
  - iRight. iRight. iRight. iSplit; last done. iPureIntro. done.
Qed.

Lemma GC_per_loc_remove_dirty M ζ σMLvirt dirty γ':
  M !! γ' = None →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt (dirty ∖ {[ γ' ]} ) γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&#Hsim&#Hlen)|[(%q&%r&Hmapsℓ&Hmapsγ&#Hsim&%Hsum&%Hdirty)|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft; iFrame; repeat iSplit; try done.
  - iRight. iLeft. iFrame "Hγ Hsim Hlen". iPureIntro. done.
  - iRight. iRight. iLeft. iExists q,r. iFrame. iFrame "Hsim". iPureIntro; split_and!; try done.
    eapply elem_of_difference; split; first done. eapply not_elem_of_singleton; intros HH; simplify_eq.
  - iRight. iRight. iRight. done.
Qed.

Lemma GC_per_loc_delete_ζ M ζ σMLvirt dirty γ':
  M !! γ' = None →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant ζ σMLvirt dirty γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant (delete γ' ζ) σMLvirt dirty γ ℓ)%I.
Proof.
  iIntros (Hne) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hle) "(%vs'&%lvs&[(Hℓ&%Hzeta&Hcanon)|[(%Hℓσ&Hγ&Hsim&Hlen)|[HH|(%Hnone1&%Hnone2)]]])"; iExists vs', lvs.
  - iLeft. iFrame. rewrite lookup_delete_ne; first done.
    intros ->; congruence.
  - iRight. iLeft. by iFrame.
  - iRight. iRight. iLeft. iFrame.
  - iRight. iRight. iRight. iPureIntro; split; first done.
    rewrite lookup_delete_ne; try done.
    intros ->. simplify_eq.
Qed.

End Laws.

End GCtoken.
