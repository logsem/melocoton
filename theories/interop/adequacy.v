From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props multirelations.
From melocoton.language Require Import language weakestpre.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import state lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import primitive_laws lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation mlang_instantiation.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require Import weakestpre mlanguage adequacy.
From melocoton.linking Require Import lang weakestpre.
From transfinite.base_logic.lib Require Import satisfiable invariants ghost_map ghost_var.
From transfinite.stepindex Require Import ordinals.

Section AllocBasics.
  Existing Instance ordI.
  Context `{Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)

  Record totalGhostStateG : Set := TotalGhostStateG {
    totalG_CG :> heapG_C Σ;
    totalG_MLG :> heapG_ML Σ;
    totalG_wrapperG :> wrapperG Σ;
    totalG_linkG :> linkG Σ;
  }.

  Context `{!heapGpre_ML Σ, !heapGpre_C Σ}. (* everything else still needs ghost names *)
  Context `{!wrapperBasicsGpre Σ, !wrapperGCtokGpre Σ}.
  Context `{!linkGpre Σ}.

  (* TODO do we need the invariant heap *)
  Lemma alloc_heapG_ML : @Alloc _ Σ (heapG_ML Σ) 
      (λ _, state_interp (∅ : language.state ML_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof using heapGpre_ML0.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γheap&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γmeta&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γinv&Halloc).
    - pose (GenHeapG _ (option (list MLval)) _ γheap γmeta) as Hgen_heapG.
      pose (Inv_HeapG _ (option (list MLval)) γinv) as Hinv_heapG.
      pose (HeapG_ML _ _ Hgen_heapG Hinv_heapG) as HheapG_ML.
      exists HheapG_ML. eapply alloc_mono; last exact Halloc.
      iIntros "((($&H1)&H2)&H3)".
      iExists ∅. iSplit; first done. cbn in *. iFrame.
    - unshelve eapply (@gmap_view.gmap_view_auth_valid _ _ _ _ (leibnizO _) (∅ : gmap loc (option (list val)))).
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
    Unshelve. apply _.
  Qed.

  Lemma alloc_heapG_C : @Alloc _ Σ (heapG_C Σ) 
      (λ _, state_interp (∅ : language.state C_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof using heapGpre_C0.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γheap&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γmeta&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γinv&Halloc).
    - pose (GenHeapG _ heap_cell _ γheap γmeta) as Hgen_heapG.
      pose (Inv_HeapG _ heap_cell γinv) as Hinv_heapG.
      pose (HeapG _ _ Hgen_heapG Hinv_heapG) as HheapG_ML.
      exists HheapG_ML. eapply alloc_mono; last exact Halloc.
      iIntros "((($&H1)&H2)&H3)".
      iExists ∅. iSplit; first done. cbn in *. iFrame.
    - unshelve eapply (@gmap_view.gmap_view_auth_valid _ _ _ _ (leibnizO _) (∅ : gmap loc heap_cell)).
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
    Unshelve. apply _.
  Qed.

  Lemma alloc_wrapperBasicsG : @Alloc _ Σ (wrapperBasicsG Σ) 
      (λ _, lstore_own_auth ∅ ∗ lloc_own_auth ∅ ∗ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval) ∗ ⌜basics_resources.wrapperG_inG = _⌝)%I True.
  Proof using heapGpre_C0.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γζvirt&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γχvirt&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γroots_map&Halloc).
    - pose (WrapperBasicsG _ Σ _ γζvirt γχvirt γroots_map) as HWrapperBasicsG.
      exists HWrapperBasicsG. eapply alloc_mono; last exact Halloc.
      iIntros "((($&H1)&H2)&H3)". unfold lstore_own_auth, lloc_own_auth.
      rewrite /named /ghost_map_auth !ghost_map.ghost_map_auth_aux.(seal_eq) /ghost_map.ghost_map_auth_def.
      cbn in *. iFrame. repeat iSplitL.
      + unfold lstore_immut_blocks. rewrite map_filter_empty. by iApply big_sepM_empty.
      + unfold lloc_map_pubs. rewrite omap_empty. by iApply big_sepM_empty.
      + unfold lloc_map_foreign. rewrite omap_empty. by iApply big_sepM_empty.
      + done.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
  Qed.

Definition GCtok_gammas `{!wrapperGCtokG Σ} : iProp Σ :=
    "GCζ" ∷ ghost_var wrapperG_γζ 1 (∅:lstore)
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ 1 (∅:lloc_map)
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ 1 (∅:addr_map)
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set 1 (∅:gset addr)
  ∗ "GCζvirt" ∷ lstore_own_auth (∅:lstore)
  ∗ "GCχvirt" ∷ lloc_own_auth (∅:lloc_map)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval)
  ∗ "HInit" ∷ ghost_var wrapperG_γat_init 1 true.

  Lemma alloc_wrapperGCtokG : @Alloc _ Σ (wrapperGCtokG Σ) 
      (λ H, GCtok_gammas 
          ∗ ⌜wrapperG_inG = _⌝
          ∗ ⌜basics_resources.wrapperG_inG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    eapply alloc_wrapperBasicsG in Halloc as (HwrapperBasicG&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γζ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γχ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γθ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γroots_set&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γat_init&Halloc).
    - pose (WrapperGCtokG _ Σ _ _ γζ γχ γθ γroots_set γat_init) as HWrapperGCtokG.
      exists HWrapperGCtokG. eapply alloc_mono; last exact Halloc.
      unfold GCtok_gammas; cbn.
      rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
      iIntros "(((((($&($&($&($&$))))&$)&$)&$)&$)&$)". done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
  Qed.

  Lemma alloc_wrapperG : @Alloc _ Σ (prod (wrapperG Σ) (heapG_ML Σ))
      (λ '(HW,HML), weakestpre.private_state_interp {| χC := ∅; ζC := ∅; θC := ∅; rootsC := ∅ |} 
               ∗ ghost_var wrapperG_γat_boundary (1 / 2) true ∗ at_init
               ∗ ⌜wrapperG_inG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    eapply alloc_heapG_ML in Halloc as (HheapG_ML&Halloc); last done.
    eapply alloc_wrapperGCtokG in Halloc as (HwrapperGCtokG&Halloc); last done.
    1: eapply alloc_fresh_res in Halloc as (γboundary&Halloc).
    - pose (WrapperG _ Σ HwrapperGCtokG γboundary) as HwrapperG.
      exists (HwrapperG,HheapG_ML). eapply alloc_mono; last exact Halloc. cbn.
      unfold weakestpre.private_state_interp, C_state_interp, at_init.
      iIntros "(((H1&H2)&(H3&(%Heq&%Heq2)))&H4)". iFrame "H1". iNamed "H3". cbn.
      iAssert (ghost_var γboundary (1 / 2) true ∗ ghost_var γboundary (1 / 2) true)%I with "[H4]" as "(H4&H4')".
      { rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
        iApply own_op. iApply "H4". }
      rewrite <- !Heq, <- ! Heq2.
      iDestruct "HInit" as "(HInit1&HInit2)". iFrame. iSplitL; last done.
      iExists true. unfold preGCtok, named. cbn.
      iFrame.
      iDestruct "GCζ" as "($&$)".
      iDestruct "GCχ" as "($&$)".
      iDestruct "GCθ" as "($&$)".
      iDestruct "GCroots" as "($&$)".
    - eapply dfrac_agree.frac_agree_op_valid_L; done.
  Qed.

  Lemma alloc_linkG : @Alloc _ Σ (linkG Σ)
      (λ _, ghost_var linkG_γ 1 Boundary ∗ ⌜linkG_preG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    1: eapply alloc_fresh_res in Halloc as (γlink&Halloc).
    - pose (LinkG _ Σ _ γlink) as HLinkG.
      exists HLinkG. eapply alloc_mono; last exact Halloc. cbn.
      rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
      iIntros "($&$)". done.
    - cbv. done.
  Qed.

End AllocBasics.


Section Alloc.
  Existing Instance ordI.
  Context {Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)
  Context `{!heapGpre_ML Σ, !heapGpre_C Σ}. (* everything else still needs ghost names *)
  Context `{!wrapperBasicsGpre Σ, !wrapperGCtokGpre Σ}.
  Context `{!linkGpre Σ}.
  Local Definition Λ : mlanguage word := link_lang wrap_lang C_mlang.

  Context {Φpure : word → state Λ → Prop}. 
  Context {pe : prog_environ Λ Σ}.
  Context {Φbi : word → iProp Σ}.

  Local Definition σ : state Λ := @Link.St _ _ wrap_lang C_mlang _ _ 
     (∅:c_state) {| χC := ∅; ζC := ∅; θC := ∅; rootsC := ∅ |} ().

  Context (HΦ : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ ∀ (σ:state Λ) v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure v σ⌝).
  Context (Hpeclosed : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ ∀ f s vv, penv_proto pe f s vv -∗ False).
  Context (e : expr Λ).
  Context (HWP : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ at_init -∗ at_boundary wrap_lang -∗ link_state_frag Boundary -∗ WP e @ pe ; ⊤ {{Φbi}}).
(* TODO: change to            ⊢ at_init -∗ link_in_state wrap_lang C_mlang In2 -∗ WP e @ pe ; ⊤ {{Φbi}}). *)

  Lemma allocate_linked_ml_c : @Alloc _ Σ (mlangG _ Λ Σ) 
    (λ H, @sideConds _ Λ Σ Φpure pe Φbi _ _ 
        ∗ state_interp σ ∗ WP e @ pe ; ⊤ {{Φbi}})%I True.
  Proof using All.
    intros P _ Halloc.
    eapply alloc_linkG in Halloc as (HlinkG&Halloc); last done.
    eapply alloc_wrapperG in Halloc as ((HwrapperG&HheapG_ML)&Halloc); last done.
    eapply alloc_heapG_C in Halloc as (HheapG_C&Halloc); last done.
    exists (link_mlangG wrap_lang C_mlang _).
    eapply alloc_mono; last exact Halloc.
    iIntros "((($&(Hb1&Hb2)&%Heq1)&(HσW&Hbound&Hinit&%Heq2))&HσC)". cbn.
    unfold public_state_interp. rewrite <- !Heq1, <- !Heq2.
    iFrame "Hb1 HσC HσW". iSplitR. 1: iSplitL.
    - iIntros "!>". iApply HΦ.
    - iIntros "!>". iApply Hpeclosed.
    - iApply (HWP with "Hinit Hbound Hb2").
  Qed.

End Alloc.
