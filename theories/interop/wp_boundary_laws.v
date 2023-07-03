From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import lang state.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import weakestpre wp_utils update_laws.
Import Wrap.

(** lemmas to switch between the ML<->C state interp at a boundary *)

Section BoundaryLaws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.


Lemma GC_SI_to_C σMLvirt ζ ζplus χ :
    lloc_own_auth χ
  ∗ lstore_own_auth (ζplus ∪ ζ)
  ∗ ([∗ map] γ↦b ∈ ζplus, ghost_map_elem wrapperG_γζvirt γ (DfracOwn 1) b)
  ∗ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ, per_location_invariant ζ σMLvirt ∅ γ ℓ)
  ∗ ⌜∀ ℓ, ℓ ∈ dom σMLvirt → ∃ γ, χ !! γ = Some (LlocPublic ℓ)⌝
 ⊢ ∃ ζσ ζvirt,
    lloc_own_auth χ
  ∗ lstore_own_auth (ζplus ∪ ζ)
  ∗ ([∗ map] γ↦b ∈ ζplus, ghost_map_elem wrapperG_γζvirt γ (DfracOwn 1) b)
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ, per_location_invariant_ML ζvirt ζσ γ ℓ)
  ∗ ⌜ζ = ζσ ∪ ζvirt⌝ ∗ ⌜ζσ ##ₘ ζvirt⌝
  ∗ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ ⌜is_store_blocks χ σMLvirt ζσ⌝
  ∗ ⌜is_store χ ζ σMLvirt⌝.
Proof.
  iIntros "(GCχauth&Hplus&GCζauth&GCσMLv&GC_per_loc&%Hstore)".
  assert (∃ χind, χind ⊆ χ ∧ χ = χind) as (χind&Hsub&Heq).
  1: eexists _; split; last done; done.
  rewrite /is_store /is_store_blocks. rewrite {2 4 6 7} Heq.
  iStopProof. clear Heq. revert ζ ζplus Hsub.
  induction χind as [|γ [ℓ|fid|] χind Hnone IH] using map_ind;
  iIntros (ζ ζplus Hsub) "(GCχauth&GCζauth&Hplus&GCσMLv&GC_per_loc)".
  - iExists ∅, ζ. iFrame.
    repeat iSplit; try iPureIntro.
    + unfold lloc_map_pubs. rewrite omap_empty. done.
    + by rewrite map_empty_union.
    + apply map_disjoint_empty_l.
    + done.
    + intros γ; split.
      * rewrite dom_empty_L. intros []%elem_of_empty.
      * intros (ℓ&Vs&[]%lookup_empty_Some&_).
    + intros ℓ Vs γ blk H1 []%lookup_empty_Some.
  - rewrite lloc_map_pubs_insert_pub.
    iPoseProof (big_sepM_insert with "GC_per_loc") as "((%vs&%tg&%lvs&[(Hℓ&%Hzeta&%Hrepl&%Hdirty&->)|[(%Hℓσ&Hγ&Hrest&->)|[(%q&%r&Hℓ&Hγ&#Hsimm&->&%Hsum&%Hc)|(%Hnone1&%Hnone2)]]])&GC_per_loc)".
    1: apply lloc_map_pubs_lookup_None; left; done.
    + by eapply elem_of_empty in Hdirty. (*
      iDestruct (gen_heap_valid with "GCσMLv Hℓ") as %Hℓσ.
      iDestruct (IH ζ with "[$GCζauth $Hplus $GC_per_loc $GCσMLv $GCχauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hownres&HχNone&->&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
      1: etransitivity; first apply insert_subseteq; done.
      iExists ζσ, ζvirt. iFrame "GCζauth GCσMLv GCχauth Hownres".
      iSplitL; last repeat iSplit; try iPureIntro.
      * iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; left; done).
        iFrame "HχNone". iExists vs, tg, lvs. iLeft. iFrame. iPureIntro.
        apply lookup_union_Some_inv_r in Hγζ; first done.
        destruct (ζσ !! γ) eqn:Heq; last done. exfalso.
        eapply elem_of_dom_2 in Heq. apply Hstore1 in Heq as (ℓ'&Vs'&HH1&HH2); simplify_eq.
      * done.
      * done.
      * done.
      * intros γ'; specialize (Hstore1 γ') as [Hs1L Hs1R]; split.
        -- intros Hdom. destruct (Hs1L Hdom) as (ℓ'&Vs'&HH1&HH2).
           exists ℓ',Vs'. split; last done. rewrite lookup_insert_ne; first done.
           intros ->; congruence.
        -- intros (ℓ'&Vs'&[(HH1a&HH1b)|(HH1a&HH1b)]%lookup_insert_Some&HH2).
           2: apply Hs1R; by repeat eexists.
           simplify_eq.
      * intros ℓ' vs' γ' blk' HH1 [(HH2a&HH2b)|(HH2a&HH2b)]%lookup_insert_Some HH3; first by simplify_eq.
        by eapply Hstore2. *)
    + iPoseProof (lstore_own_vblock_M_as_mut with "Hγ") as "(Hγ&%ℓ'&#Hℓγ)".
      iPoseProof (lstore_own_mut_of with "GCζauth Hγ") as "#(%Hζγ&_)".
      iPoseProof (lstore_own_mut_to_elem with "Hγ") as "Hγ".
      eapply lookup_union_Some_raw in Hζγ as [Hζγ|(Hne&Hζγ)].
      1: { iPoseProof (big_sepM_lookup_acc with "Hplus") as "(Hcontr&_)"; first done.
           rewrite /lstore_own_elem /mutability. cbn. iPoseProof (ghost_map_elem_ne with "Hcontr Hγ") as "%H". done. }
      iPoseProof (GC_per_loc_delete_ζ with "GC_per_loc") as "GC_per_loc".
      1: apply lloc_map_pubs_lookup_None; by left.
      iPoseProof (block_sim_arr_auth_is_val_strong with "GCχauth GCζauth Hplus Hrest") as "%His_val".
      1: by erewrite map_empty_union. 1: apply map_disjoint_empty_l.
      iDestruct (IH (delete γ ζ) (<[ γ := _ ]> ζplus) with "[GCζauth Hplus Hγ $GC_per_loc $GCσMLv $GCχauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hplus&HχNone&%Heqζ&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
      1: etransitivity; first apply insert_subseteq; done.
      { rewrite union_insert_delete; try done. iFrame. iApply big_sepM_insert; try done. iFrame. }
      rewrite union_insert_delete; try done.
      iPoseProof (lloc_own_pub_of with "GCχauth Hℓγ") as "%Hℓ'γχ".
      assert (χ !! γ = Some (LlocPublic ℓ)) as Hℓγχ by (by eapply lookup_weaken; last apply Hsub; eapply lookup_insert).
      assert (ℓ' = ℓ) as -> by congruence.
      iExists (<[ γ := (Bvblock (Mut, (TagDefault, lvs))) ]> ζσ), ζvirt.
      iPoseProof (big_sepM_insert with "Hplus") as "(Hγ&Hplus)"; first done.
      iFrame "GCζauth GCσMLv GCχauth Hplus".
      assert (ζvirt !! γ = None) as HζγvNone.
      { destruct (ζvirt !! γ) eqn:Heq; last done. exfalso.
        eapply elem_of_dom_2, elem_of_union_r, dom_union in Heq.
        erewrite <-Heqζ, dom_delete_L in Heq. set_solver. }
      iSplitL; last repeat iSplit; try iPureIntro.
      * iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; left; done).
        iSplitR "HχNone". 2: (iApply GC_per_loc_ML_insert; try iFrame).
        { iExists vs, TagDefault, lvs. iLeft. iFrame. iSplit; try by iPureIntro.
          iFrame "Hℓγ"; by iExists _. }
        eapply lloc_map_pubs_lookup_None. by left.
      * by rewrite <- insert_union_l, <-Heqζ, insert_delete.
      * apply map_disjoint_insert_l_2; done.
      * done.
      * intros γ'; specialize (Hstore1 γ') as [Hs1L Hs1R]; split.
        -- rewrite dom_insert_L. intros [->%elem_of_singleton|Hdom]%elem_of_union.
           ++ exists ℓ, vs. by rewrite lookup_insert.
           ++ destruct (Hs1L Hdom) as (ℓ'&Vs'&HH1&HH2).
              exists ℓ',Vs'. split; last done. rewrite lookup_insert_ne; first done.
              intros ->; congruence.
        -- rewrite dom_insert_L.
           intros (ℓ'&Vs'&[(HH1a&HH1b)|(HH1a&HH1b)]%lookup_insert_Some&HH2); eapply elem_of_union.
           2: right; apply Hs1R; by repeat eexists.
           left. eapply elem_of_singleton. done.
      * intros ℓ' vs' γ' blk' HH1 [(HH2a&HH2b)|(HH2a&HH2b)]%lookup_insert_Some HH3.
        -- simplify_eq. by econstructor.
        -- eapply (is_heap_elt_weaken χ (delete γ ζ)); [|done|by apply delete_subset].
           eapply Hstore2; try done. by rewrite lookup_delete_ne.
    + exfalso. set_solver. 
    + iDestruct (IH ζ with "[$GCζauth $Hplus $GC_per_loc $GCσMLv $GCχauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hownres&HχNone&->&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
      1: etransitivity; first apply insert_subseteq; done.
      iPoseProof (lloc_own_auth_get_pub with "GCχauth") as "#Hsim".
      1: (eapply lookup_weaken; last apply Hsub); by erewrite lookup_insert.
      iExists ζσ, ζvirt. iFrame "GCζauth GCσMLv GCχauth Hownres".
      iSplitL; last repeat iSplit; try iPureIntro.
      * iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; left; done).
        iFrame "HχNone". iExists vs, tg, lvs. iRight. iFrame "Hsim". iPureIntro.
        eapply lookup_union_None in Hnone2 as [HH1 HH2]; done.
      * done.
      * done.
      * done.
      * intros γ'; specialize (Hstore1 γ') as [Hs1L Hs1R]; split.
        -- intros Hdom. destruct (Hs1L Hdom) as (ℓ'&Vs'&HH1&HH2).
           exists ℓ',Vs'. split; last done. rewrite lookup_insert_ne; first done.
           intros ->; congruence.
        -- intros (ℓ'&Vs'&[(HH1a&HH1b)|(HH1a&HH1b)]%lookup_insert_Some&HH2).
           2: apply Hs1R; by repeat eexists.
           simplify_eq.
      * intros ℓ' vs' γ' blk' HH1 [(HH2a&HH2b)|(HH2a&HH2b)]%lookup_insert_Some HH3; first by simplify_eq.
        by eapply Hstore2.
  - rewrite lloc_map_pubs_insert_foreign -lloc_map_pubs_delete delete_notin. 2: done.
    iDestruct (IH with "[$GCζauth $GC_per_loc $Hplus $GCσMLv $GCχauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hplus&HχNone&%Heqζ&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
    1: etransitivity; first apply insert_subseteq; done.
    iExists ζσ, ζvirt. iFrame.
    iPureIntro; split_and!.
    + done.
    + done.
    + done.
    + intros γ'; destruct (Hstore1 γ') as [HL HR]; split.
      * intros H; destruct (HL H) as (ℓ&Vs&H1&H2). exists ℓ,Vs. split; last done.
        rewrite lookup_insert_ne; first done. intros ->; simplify_eq; done.
      * intros (ℓ&Vs&[(->&H1)|(H1a&H1b)]%lookup_insert_Some&H2).
        1: congruence.
        apply HR; by repeat eexists.
    + intros ℓ vs γ' blk H1 [(->&H2)|(H2a&H2b)]%lookup_insert_Some H3.
      1: congruence.
      eapply Hstore2; done.
  - rewrite lloc_map_pubs_insert_priv -lloc_map_pubs_delete delete_notin. 2: done.
    iDestruct (IH with "[$GCζauth $GC_per_loc $Hplus $GCσMLv $GCχauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hplus&HχNone&%Heqζ&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
    1: etransitivity; first apply insert_subseteq; done.
    iExists ζσ, ζvirt. iFrame.
    iPureIntro; split_and!.
    + done.
    + done.
    + done.
    + intros γ'; destruct (Hstore1 γ') as [HL HR]; split.
      * intros H; destruct (HL H) as (ℓ&Vs&H1&H2). exists ℓ,Vs. split; last done.
        rewrite lookup_insert_ne; first done. intros ->; simplify_eq; done.
      * intros (ℓ&Vs&[(->&H1)|(H1a&H1b)]%lookup_insert_Some&H2).
        1: congruence.
        apply HR; by repeat eexists.
    + intros ℓ vs γ' blk H1 [(->&H2)|(H2a&H2b)]%lookup_insert_Some H3.
      1: congruence.
      eapply Hstore2; done.
Qed.

Lemma wrap_interp_c_to_ml ws ρc mem θ vs lvs :
  Forall2 (repr_lval θ) lvs ws →
  wrap_state_interp (Wrap.CState ρc mem) -∗
  GC θ ∅ -∗
  at_boundary wrap_lang -∗
  lvs ~~∗ vs -∗
  ∃ ρml σ,
  ⌜c_to_ml ws ρc mem vs ρml σ⌝ ∗
  |==> wrap_state_interp (Wrap.MLState ρml σ) ∗ not_at_boundary.
Proof using.
  iIntros (Hlv) "Hσ HGC Hnb #Hblk". 
  iNamed "Hσ". iNamed "SIC". iNamed "HGC". simplify_eq. SI_GC_agree.
  iNamed "HSI_GC". iNamed "HSI_block_level".

  iAssert (⌜Forall2 (is_val χ_future ζ_future) vs lvs⌝)%I as "%Hval".
  1: iApply (block_sim_arr_auth_is_val_simple with "GCχauth GCζauth Hblk").
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  apply map_Forall_lookup_2 in Hroots.
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  iPoseProof (GC_SI_to_C σMLvirt ζ_future ∅ χ_future with "[$GCχauth $GCσMLv $GC_per_loc GCζauth]") as "(%ζσ&%ζvirt&GCχauth&GCζauth&Hownres&HχNone&->&%Hdisj&GCσMLv&(#_&%Hstore1)&%Hstore2)".
  { rewrite map_empty_union. iFrame. by repeat iSplit. }

  iExists (WrapstateML _ _ _ _), _. iSplit.
  { iPureIntro. unfold c_to_ml. cbn.
    eexists σMLvirt, _, _, (ζσ ∪ ζvirt), ζσ. split_and!; eauto.
    1: by rewrite map_union_comm. by split. }

  iMod (ghost_var_update_halves with "Hnb SIbound") as "(Hb & SIbound)".
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ & SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ & SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ & SIθ)".
  iMod (ghost_var_update_halves with "GCroots SIroots") as "(GCroots & SIroots)".
  iMod (set_to_none with "HσC GCrootspto") as "(HσC & GCrootspto)"; first done.

  rewrite !map_empty_union.
  iModIntro. iSplitR "SIbound"; last by iFrame "SIbound".
  rewrite /= /named. iFrame "GCσMLv".
  unfold private_state_interp, ML_state_interp, GC_remnant_ML, SI_block_level_ML, SI_GC_ML, named; cbn.
  iFrame. iSplitL.
  { iExists _, _. iFrame. iSplitR "GCrootspto". 2: iSplit.
    - iExists ζσ. rewrite (map_union_comm ζvirt); last done. iFrame.
      iPureIntro. split_and!; try done.
      + rewrite dom_union_L in Hother_blocks. set_solver.
      + intros γ (ℓ&Vs&HH1&_)%Hstore1. by exists ℓ.
    - by iApply big_sepM_dom.
    - iPureIntro. apply Hχfuture. }
  iPureIntro.
  destruct Hpriv as (mem_r & ->%repr_roots_dom & Hpriv2 & Hpriv3); by apply map_disjoint_dom.
Qed.


Lemma wp_is_None σ χ ζ1 ζ2 : 
  ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ, per_location_invariant_ML ζ1 ζ2 γ ℓ)
 ∗ state_interp σ
 ⊢ ⌜pub_locs_in_lstore χ ζ1 = ∅⌝.
Proof.
  iIntros "(H1&H2)".
  iAssert (⌜_⌝)%I as "%H".
  2: { iPureIntro. eapply map_eq_iff. intros i. destruct (pub_locs_in_lstore χ ζ1 !! i) eqn:Heq.
       2: rewrite lookup_empty; reflexivity. exfalso. revert i l Heq. refine H. }
  iIntros (γ ℓ [Hin [v Hv]%elem_of_dom]%map_filter_lookup_Some).
  iPoseProof (big_sepM_lookup with "H1") as "(%vs&%tg&%lvs&[(%H1&Hζ&Hsim)|(%H1&%H2&Hsim)])"; first done.
  - exfalso; simplify_eq.
  - exfalso; simplify_eq.
Qed.

Lemma gmap_new_elems {A B : Type} `{Countable A} (m1 m2 : gmap A B) : m1 ⊆ m2 → ∃ mr, m2 = m1 ∪ mr ∧ m1 ##ₘ mr.
Proof.
  exists (filter (fun '(k,_) => (m1 !! k) = None) m2). split.
  - eapply map_eq_iff. intros k. rewrite lookup_union. destruct (m1 !! k) eqn:Heq.
    + cbn. rewrite map_filter_lookup_None_2.
      * cbn. by eapply lookup_weaken.
      * right. intros  _ _ Heq2. simplify_eq.
    + rewrite union_with_left_id. rewrite map_filter_lookup. destruct (m2 !! k); cbn; last done.
      by rewrite option_guard_True.
  - apply map_disjoint_spec. intros k v1 v2 HH1 (_&HH2)%map_filter_lookup_Some. simplify_eq.
Qed.

(* Step 1: convert the per_location_invariant for all already known mappings in χ *)
(* Notice that this has no χold and χnew *)
Lemma GC_SI_to_ML_one σMLvirt ζvirt ζσnew ζσold ζnewimm χ χplus:
    ⌜ζvirt ##ₘ ζnewimm⌝ ∗ ⌜ζσnew ##ₘ ζnewimm⌝ ∗ ⌜ζvirt ##ₘ ζσnew⌝∗ ⌜ζvirt ##ₘ ζσold⌝ ∗ ⌜ζσold ##ₘ ζnewimm⌝ 
  ∗ ⌜(∀ γ, γ ∈ dom ζσnew ↔ (∃ ℓ Vs, χ !! γ = Some (LlocPublic ℓ) ∧ σMLvirt !! ℓ = Some Vs))⌝ ∗ ⌜lloc_map_inj χ⌝ ∗ ⌜χ ⊆ χplus⌝
  ∗ ⌜∀ ℓ vs γ blk, σMLvirt !! ℓ = Some vs → χ !! γ = Some (LlocPublic ℓ) → (ζσnew ∪ (ζvirt ∪ ζnewimm)) !! γ = Some blk → is_heap_elt χplus (ζσnew ∪ (ζvirt ∪ ζnewimm)) vs blk⌝
  ∗ ⌜dom ζvirt ⊆ dom χ⌝
  ∗ ⌜∀ γ vs, χ !! γ = Some vs → γ ∈ dom ζnewimm → vs = LlocPrivate⌝
  ∗ ⌜∀ γ, γ ∈ dom ζσold → ∃ ℓ, χ !! γ = Some (LlocPublic ℓ)⌝
  ∗ lloc_own_auth χplus
  ∗ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ lstore_own_auth (ζσold ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ, per_location_invariant_ML ζvirt ζσold γ ℓ)
 ⊢ |==> lstore_own_auth (ζσnew ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ, per_location_invariant (ζσnew ∪ ζvirt) σMLvirt ∅ γ ℓ)
  ∗ lloc_own_auth χplus
  ∗ state_interp (σMLvirt : language.language.state ML_lang).
Proof.
  iIntros "(%Hdisj1&%Hdisj2&%Hdisj3&%Hdisj4&%Hdisj5&%Hbl2&%Hinj&%Hplus&%Hisstore&%Hother_blocks&%Himmut&%Holdblocks&GCχauth&GCζauth&GCσMLv&GC_per_loc)".
  assert (∃ χind, χind ⊆ χ ∧ χ = χind) as (χind&Hsub&Heqind).
  1: eexists _; split; last done; done.
  iStopProof.
  rewrite /named. revert ζσnew ζσold ζnewimm Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5 Hbl2 Hisstore Hother_blocks Himmut Holdblocks Hinj Hplus Hsub.
  rewrite {1 4 5 9 10} Heqind. clear Heqind.
  induction χind as [|γ [ℓ|fid|] χind Hnone IH] using map_ind;
  intros ζσnew ζσold ζnewimm Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5 Hbl2 Hisstore Hother_blocks Himmut Holdblocks Hinj Hplus Hsub;
  iIntros "(GCχauth&GCσMLv&GCζauth&GC_per_loc)".
  - rewrite lloc_map_pubs_empty.
    assert (ζσnew = ∅) as ->.
    1: { apply map_empty. intros γ. eapply not_elem_of_dom. intros Hdom.
         apply Hbl2 in Hdom as (?&?&[]%lookup_empty_Some&_). }
    assert (ζσold = ∅) as ->.
    1: { apply map_empty. intros γ. eapply not_elem_of_dom. intros Hdom.
         destruct (Holdblocks _ Hdom) as (ℓ&[]%lookup_empty_Some). }
    rewrite map_empty_union. iFrame. iModIntro. done.
  - rewrite lloc_map_pubs_insert_pub.
    iPoseProof (big_sepM_insert with "GC_per_loc") as "((%vs&%tg&%lvs&[(%Hne&Hmaps&Hsim)|(%Hne1&%Hne2&Hsim)])&GC_per_loc)".
    + apply lloc_map_pubs_lookup_None. by left. (*
    + assert (ζσold !! γ = None) by by eapply map_disjoint_Some_l.
      assert (ζσnew !! γ = None) by by eapply map_disjoint_Some_l.
      iMod (IH ζσnew ζσold with "[$GCχauth $GCσMLv $GCζauth $GC_per_loc]") as "(GCχauth&GCσMLv&GCζauth&GC_per_loc)"; try done.
      * intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
        -- intros Hg; destruct (HblL Hg) as (ℓ'&Vs&HH1&HH2). repeat eexists; try done.
           rewrite lookup_insert_ne in HH1; try done. intros ->; by eapply not_elem_of_dom in H0.
        -- intros (ℓ'&Vs&HH1&HH2). eapply HblR. repeat eexists; try done.
           rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
      * intros γ' vs' H1 H2. eapply Himmut; try done. rewrite lookup_insert_ne; last intros ->. 1: done. simplify_eq.
      * intros γ' Hγ'. destruct (Holdblocks γ' Hγ') as [ℓ' [(->&_)|(Hne&HH)]%lookup_insert_Some].
        2: by exists ℓ'. eapply not_elem_of_dom in H; exfalso; eapply H,Hγ'.
      * apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
        rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
      * iModIntro. iFrame. iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; by left). iFrame.
        iExists vs, tg, lvs. iLeft. iFrame. iPureIntro. by rewrite lookup_union_r. *)
    + destruct (σMLvirt !! ℓ) as [Vs|] eqn:Heq.
      1: assert (γ ∈ dom ζσnew) as [blk Hblk]%elem_of_dom.
      1: eapply Hbl2; repeat eexists; try done; by rewrite lookup_insert.
      * unshelve epose proof (Hisstore ℓ Vs γ blk Heq _ _) as Helt.
        1: eapply lookup_weaken; last exact Hsub; by rewrite lookup_insert.
        1: by erewrite lookup_union_Some_l.
        assert (ζnewimm !! γ = None). 1: eapply map_disjoint_Some_l; first eapply Hdisj2; done.
        assert (ζvirt !! γ = None). 1: eapply map_disjoint_Some_r; first exact Hdisj3; done.
        iDestruct "Hmaps" as "(Hmaps&Hmaps2)".
        iPoseProof (lstore_own_elem_of with "GCζauth Hmaps") as "%Hlookup".
        apply lookup_union_Some_raw in Hlookup as [Hl|(Hne'&[Hr|(Hne2&Hr)]%lookup_union_Some_raw)].
        2-3: simplify_eq.
        assert ((delete γ ζσnew ∪ (ζvirt ∪ <[γ:=blk]> ζnewimm)) = (ζσnew ∪ (ζvirt ∪ ζnewimm))) as Hzetaeq.
        { do 2 (rewrite -insert_union_r; last try done). 2: by apply lookup_delete.
          rewrite insert_union_l. rewrite insert_delete; done. }
        cbn in Hl.
        eassert ((delete γ ζσold ∪ (ζvirt ∪ <[γ:=_]> ζnewimm)) = (ζσold ∪ (ζvirt ∪ ζnewimm))) as Hzetaeqold.
        { do 2 (rewrite -insert_union_r; last try done). 2: by apply lookup_delete.
          rewrite insert_union_l. rewrite insert_delete; done. }
        iMod (lstore_own_update with "GCζauth [$Hmaps //]") as "(GCζauth&Hmaps)".
        iMod (IH (delete γ ζσnew) (delete γ ζσold) (<[ γ := blk ]> ζnewimm) with "[$GCχauth $GCσMLv GCζauth GC_per_loc]") as "(GCζauth&GC_per_loc&GCχauth&GCσMLv)"; try done.
        1: by apply map_disjoint_insert_r_2.
        1: (apply map_disjoint_insert_r_2; first by rewrite lookup_delete); by apply map_disjoint_delete_l.
        1: by apply map_disjoint_delete_r.
        1: by apply map_disjoint_delete_r.
        1: (apply map_disjoint_insert_r_2; first by rewrite lookup_delete); by apply map_disjoint_delete_l.
        { intros γ'; destruct (Hbl2 γ') as [HHL HHR]; split; rewrite dom_delete_L.
         - intros (He&Hnee%not_elem_of_singleton)%elem_of_difference.
           destruct (HHL He) as (ℓ'&Vs'&HH1&HH2). repeat eexists; try done. by rewrite lookup_insert_ne in HH1.
         - intros (ℓ'&Vs'&HH1&HH2). apply elem_of_difference.
           assert (γ ≠ γ') as Hnee.
           1: intros ->; simplify_eq. split.
           1: eapply HHR; repeat eexists; last done; by rewrite lookup_insert_ne.
           by eapply not_elem_of_singleton. }
        1: erewrite Hzetaeq; apply Hisstore.
        1: { rewrite dom_insert_L; intros γ' vs' H1 [Heqvs%elem_of_singleton|H2]%elem_of_union.
             1: simplify_eq.
             eapply Himmut; try done; rewrite lookup_insert_ne //;intros ->; by simplify_eq. }
        1: { rewrite dom_delete_L; intros γ' (Hγ'&Hnee%not_elem_of_singleton)%elem_of_difference.
             edestruct (Holdblocks _ Hγ') as [ℓ' [(Heqq&_)|(_&Hℓ)]%lookup_insert_Some]. 1: simplify_eq.
             by eexists. }
        1: apply map_subseteq_spec; intros γ' v1 Hv1; eapply lookup_weaken; last exact Hsub;
           rewrite lookup_insert_ne; try done; intros ->; simplify_eq.
        1: { rewrite -Hzetaeqold insert_union_r. 2: apply lookup_delete. rewrite insert_union_r; last done.
             rewrite insert_insert. iFrame "GCζauth".
             iApply (GC_per_loc_ML_delete with "[$]"). apply lloc_map_pubs_lookup_None; by left. }
        rewrite Hzetaeq.
        inversion Helt; simplify_eq.
        iPoseProof (block_sim_arr_of_auth_strong _ _ Vs lvs0 with "GCχauth GCζauth") as "#Hsimvs".
        { eapply Forall2_impl; first eassumption. intros x y HH. eapply is_val_mono; last done; done. }
        iPoseProof (lloc_own_auth_get_pub with "GCχauth") as "#Hsimell".
        1: eapply lookup_weaken; last (etransitivity; try exact Hsub; done); by erewrite lookup_insert.
        cbn in Hl. simplify_eq.
        iModIntro. iFrame. iApply big_sepM_insert.
        1: apply lloc_map_pubs_lookup_None; by left.
        iSplitR "GC_per_loc".
        -- iExists _, TagDefault, _. iRight. iLeft. iFrame. iSplitR; first done.
           iSplit; done.
        -- iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
           1: apply lloc_map_pubs_lookup_None; by left.
           erewrite insert_union_l. by rewrite insert_delete.
      * assert (γ ∉ dom ζσnew) as Hnin%not_elem_of_dom.
        1: intros H; apply Hbl2 in H as (ℓ'&Vs&HH1&HH2); rewrite lookup_insert in HH1; simplify_eq.
        iDestruct "Hmaps" as "(Hmaps&Hmaps2)".
        iPoseProof (lstore_own_elem_of with "GCζauth Hmaps") as "%Hlookup".
        apply lookup_union_Some_raw in Hlookup as [Hl|(Hne'&[Hr|(Hne2&Hr)]%lookup_union_Some_raw)].
        2: simplify_eq.
        2: { eapply elem_of_dom_2 in Hr. unshelve epose proof (Himmut γ _ _ Hr). 2: by rewrite lookup_insert. simplify_eq. }
        assert (ζnewimm !! γ = None). 1: eapply map_disjoint_Some_l; first exact Hdisj5; done.
        iMod (lstore_own_delete with "GCζauth [$Hmaps //]") as "GCζauth".
        assert (delete γ (ζσold ∪ (ζvirt ∪ ζnewimm)) = (delete γ ζσold) ∪ (ζvirt ∪ ζnewimm)) as Heqzeta.
        { rewrite !delete_union. f_equal. rewrite !delete_notin; done. }
        rewrite Heqzeta.
        iPoseProof (GC_per_loc_ML_delete with "GC_per_loc") as "GC_per_loc".
        1: eapply lloc_map_pubs_lookup_None; by left.
        iMod (IH ζσnew (delete γ ζσold) with "[$GCχauth $GCσMLv $GCζauth $GC_per_loc]") as "(GCχauth&GCσMLv&GCζauth&GC_per_loc)"; try done.
        -- by apply map_disjoint_delete_r.
        -- by apply map_disjoint_delete_l.
        -- intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
           ++ intros Hg; destruct (HblL Hg) as (ℓ'&Vs&HH1&HH2). repeat eexists; try done.
              rewrite lookup_insert_ne in HH1; try done. intros ->; eapply not_elem_of_dom in Hnin; done.
           ++ intros (ℓ'&Vs&HH1&HH2). eapply HblR. repeat eexists; try done.
              rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
        -- intros γ' vs' H1 H2. eapply Himmut; try done. rewrite lookup_insert_ne; first done. intros ->. simplify_eq.
        -- rewrite dom_delete_L. intros γ' (H1&Hnee%not_elem_of_singleton)%elem_of_difference.
           destruct (Holdblocks _ H1) as [ℓ' Hℓ']. rewrite lookup_insert_ne in Hℓ'; first by eexists. done.
        -- apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
           rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
        -- iModIntro. iFrame. iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; by left). iFrame.
           iExists vs, tg, lvs. iRight. iRight. iRight. iFrame; iPureIntro; (split; first done).
           all: by apply lookup_union_None_2.
    + destruct (ζnewimm !! γ) as [?|] eqn:Hnewimm.
      { exfalso. apply elem_of_dom_2 in Hnewimm. unshelve epose proof (Himmut _ _ _ Hnewimm) as Hcontr.
        2: by apply lookup_insert. congruence. }
      destruct (ζσnew !! γ) as [blk|] eqn:Heqblk.
      * iMod (lstore_own_insert with "GCζauth") as "(GCζauth&Hmaps)".
        1: repeat (eapply lookup_union_None; split); done.
        do 2 (rewrite insert_union_r; last done).
        assert (delete γ ζσnew ∪ (ζvirt ∪ <[γ:=blk]> ζnewimm) = ζσnew ∪ (ζvirt ∪ ζnewimm)) as Hzetaeq.
        { rewrite -insert_union_r; last done. rewrite -insert_union_r; last by apply lookup_delete.
          rewrite insert_union_l insert_delete; done. }
        iMod (IH (delete γ ζσnew) ζσold ( <[ γ := blk ]> ζnewimm) with "[$GCχauth $GCσMLv $GCζauth $GC_per_loc]") as "(GCζauth&GC_per_loc&GCχauth&GCσMLv)"; try done.
        1: by apply map_disjoint_insert_r_2.
        1: (apply map_disjoint_insert_r_2; first by rewrite lookup_delete); by apply map_disjoint_delete_l.
        1: by apply map_disjoint_delete_r.
        1: apply map_disjoint_insert_r_2; done.
        1: { intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split; rewrite dom_delete_L.
             -- intros (Hg&Hne%not_elem_of_singleton)%elem_of_difference; destruct (HblL Hg) as (ℓ'&Vs&HH1&HH2).
                repeat eexists; try done.
                rewrite lookup_insert_ne in HH1; try done.
             -- intros (ℓ'&Vs&HH1&HH2). eapply elem_of_difference; split.
                1: eapply HblR; repeat eexists; try done; rewrite lookup_insert_ne; try done.
                2: apply not_elem_of_singleton. all: intros ->; simplify_eq. }
        1: { rewrite Hzetaeq. done. }
        1: { rewrite dom_insert_L; intros γ' vs' H1 [Heqvs%elem_of_singleton|H2]%elem_of_union.
             1: simplify_eq.
             eapply Himmut; try done; rewrite lookup_insert_ne //;intros ->; by simplify_eq. }
        1: { intros γ' Hγ'.
             edestruct (Holdblocks _ Hγ') as [ℓ' [(Heqq&_)|(HH&Hℓ)]%lookup_insert_Some].
             2: by eexists. subst γ'. apply not_elem_of_dom in Hne2; tauto. }
        1: { apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
             rewrite lookup_insert_ne; try done. intros ->; simplify_eq. }
        rewrite Hzetaeq.
        eapply elem_of_dom_2 in Heqblk as Hblkdom.
        apply Hbl2 in Hblkdom as (ℓ'&Vs'&HH1&HH2).
        rewrite lookup_insert in HH1. simplify_eq.
        unshelve epose proof (Hisstore ℓ' Vs' γ blk HH2 _ _) as Helt.
        1: { eapply lookup_weaken, Hsub. rewrite lookup_insert; done. }
        1: { eapply lookup_union_Some_l; done. }
        inversion Helt; simplify_eq.
        iPoseProof (block_sim_arr_of_auth_strong _ _ Vs' lvs0 with "GCχauth GCζauth") as "#Hsimvs".
        { eapply Forall2_impl; first eassumption. intros x y HH. eapply is_val_mono; last done; done. }
        iPoseProof (lloc_own_auth_get_pub with "GCχauth") as "#Hsimell".
        1: eapply lookup_weaken; last (etransitivity; try exact Hsub; done); by erewrite lookup_insert.
        simplify_eq.
        iModIntro. iFrame. iApply big_sepM_insert.
        1: apply lloc_map_pubs_lookup_None; by left.
        iSplitR "GC_per_loc".
        -- iExists _, TagDefault, _. iRight. iLeft. iFrame. iSplitR; first done.
           repeat iSplit; try done. by iExists _.
        -- iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
           1: apply lloc_map_pubs_lookup_None; by left.
           erewrite insert_union_l. by rewrite insert_delete.
     * iMod (IH ζσnew ζσold with "[$GCχauth $GCσMLv $GCζauth $GC_per_loc]") as "(GCχauth&GCσMLv&GCζauth&GC_per_loc)"; try done.
       -- intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
          ++ intros Hg; destruct (HblL Hg) as (ℓ'&Vs&HH1&HH2). repeat eexists; try done.
             rewrite lookup_insert_ne in HH1; try done. intros ->; eapply not_elem_of_dom in Heqblk; done.
          ++ intros (ℓ'&Vs&HH1&HH2). eapply HblR. repeat eexists; try done.
             rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
       -- intros γ' vs' H1 H2. eapply Himmut; try done. rewrite lookup_insert_ne; first done. intros ->. simplify_eq.
       -- intros γ' H1.
          destruct (Holdblocks _ H1) as [ℓ' Hℓ']. rewrite lookup_insert_ne in Hℓ'; first by eexists.
          intros ->; eapply not_elem_of_dom in Hne2; done.
       -- apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
          rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
       -- iModIntro. iFrame. iApply big_sepM_insert; first (apply lloc_map_pubs_lookup_None; by left). iFrame.
          iExists vs, tg, lvs. iRight. iRight. iRight. destruct (σMLvirt !! ℓ) as [?|] eqn:Heqsigma.
          1: { exfalso. eapply not_elem_of_dom in Heqblk. apply Heqblk, Hbl2.
               do 2 eexists; rewrite lookup_insert; done. }
          iPureIntro; split_and!; try done.
          by apply lookup_union_None_2.
  - rewrite lloc_map_pubs_insert_foreign -lloc_map_pubs_delete delete_notin; last done.
    iApply (IH); try done.
    + intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
      * intros Hg; destruct (HblL Hg) as (ℓ'&Vs&[(_&HH1)|(HH1L&HH1R)]%lookup_insert_Some&HH2); first simplify_eq.
        by repeat eexists.
      * intros (ℓ'&Vs&HH1&HH2). eapply HblR. repeat eexists; try done.
        rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + intros γ' vs' HH1 HH2. eapply Himmut; last done. rewrite lookup_insert_ne; first done.
      intros ->; simplify_eq.
    + intros γ' H1; edestruct (Holdblocks γ' H1) as [ℓ [(Heq1&Hℓ)|(Hne&Hℓ)]%lookup_insert_Some].
      1: simplify_eq. by eexists.
    + apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
      rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + iFrame.
  - rewrite lloc_map_pubs_insert_priv -lloc_map_pubs_delete delete_notin; last done.
    iApply (IH); try done.
    + intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
      * intros Hg; destruct (HblL Hg) as (ℓ'&Vs&[(_&HH1)|(HH1L&HH1R)]%lookup_insert_Some&HH2); first simplify_eq.
        by repeat eexists.
      * intros (ℓ'&Vs&HH1&HH2). eapply HblR. repeat eexists; try done.
        rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + intros γ' vs' HH1 HH2. eapply Himmut; last done. rewrite lookup_insert_ne; first done.
      intros ->; simplify_eq.
    + intros γ' H1; edestruct (Holdblocks γ' H1) as [ℓ [(Heq1&Hℓ)|(Hne&Hℓ)]%lookup_insert_Some].
      1: simplify_eq. by eexists.
    + apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
      rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + iFrame.
Qed.

(* Step 2: We got χold and χnew, we now add all mappings new in χnew *)
Lemma GC_SI_to_ML_2 σMLvirt ζvirt ζσold ζσnew ζnewimm χold χnew :
    ⌜ζvirt ##ₘ ζnewimm⌝ ∗ ⌜ζσnew ##ₘ ζnewimm⌝ ∗ ⌜ζvirt ##ₘ ζσnew⌝∗ ⌜ζvirt ##ₘ ζσold⌝ ∗ ⌜ζσold ##ₘ ζnewimm⌝ 
  ∗ ⌜is_store_blocks χnew σMLvirt ζσnew⌝
  ∗ ⌜lloc_map_mono χold χnew⌝
  ∗ ⌜is_private_blocks χnew ζnewimm⌝ ∗ ⌜is_store χnew (ζσnew ∪ (ζvirt ∪ ζnewimm)) σMLvirt⌝ ∗ ⌜dom ζvirt ⊆ dom χold⌝
  ∗ ⌜∀ γ, γ ∈ dom ζσold → ∃ ℓ, χold !! γ = Some (LlocPublic ℓ)⌝
  ∗ lloc_own_auth χnew
  ∗ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ lstore_own_auth (ζσold ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χold, per_location_invariant_ML ζvirt ζσold γ ℓ)
 ⊢ |==> lstore_own_auth (ζσnew ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χnew, per_location_invariant (ζσnew ∪ ζvirt) σMLvirt ∅ γ ℓ)
  ∗ lloc_own_auth χnew
  ∗ state_interp (σMLvirt : language.language.state ML_lang).
Proof.
  iIntros "(%Hdisj1&%Hdisj2&%Hdisj3&%Hdisj4&%Hdisj5&%Hbl&%Hmono&%Hpriv&%Hisstore&%Hother_blocks&%Holdblocks&GCχauth&GCζauth&GCσMLv&GC_per_loc)".
  destruct Hmono as [Hmono Hinj].
  destruct Hbl as [Hbl1 Hbl2].
  destruct (gmap_new_elems _ _ Hmono) as (χfresh&Heqfresh&Hχdisj).
  assert (∃ χind, χind ⊆ χfresh ∧ χfresh = χind) as (χind&Hsub&Heqind).
  1: eexists _; split; last done; done.
  iStopProof.
  rewrite /named. revert ζσnew ζnewimm Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5 Hbl1 Hbl2 Hpriv Hisstore Holdblocks Hother_blocks Hmono Hinj Hsub Hχdisj.
  subst χnew.
  rewrite {2 10} Heqind. clear Heqind.
  induction χind as [|γ [ℓ|fid|] χind Hnone IH] using map_ind;
  intros ζσnew ζnewimm Hdisj1 Hdisj2 Hdisj3 Hdisj4 Hdisj5 Hbl1 Hbl2 Hpriv Hisstore Holdblocks Hother_blocks Hmono Hinj Hsub Hχdisj;
  iIntros "(GCχauth&GCσMLv&GCζauth&GC_per_loc)".
  2-4: assert (χold !! γ = None) as Hnold by (eapply map_disjoint_Some_r; first eassumption; eapply lookup_weaken; last eassumption; by erewrite lookup_insert).
  - rewrite map_union_empty in Hbl2|-*.
    iApply (GC_SI_to_ML_one).
    iFrame. iPureIntro. split_and!; try done.
    + intros γ1 γ2 ℓ H1 H2. apply Hinj.
      all: eapply lookup_weaken; done.
    + intros ℓ vs γ blk HH1 HH2 HH3. eapply Hisstore; try done.
      by apply lookup_union_Some_l.
    + intros γ' vs' H1 H2. specialize (Hpriv γ' H2).
      eapply lookup_union_Some_raw in Hpriv as [Heq|(Hne1&Hne2)]; by simplify_eq.
  - rewrite -insert_union_r in Hbl2|-*; last done.
    assert (ζσold !! γ = None) as Hnotold.
    { eapply not_elem_of_dom. intros Hdom. destruct (Holdblocks _ Hdom) as (ℓ'&Hℓ'). simplify_eq. }
    destruct (σMLvirt !! ℓ) as [Vs|] eqn:Heq.
    + assert (γ ∈ dom ζσnew) as [blk Hblk]%elem_of_dom.
      1: eapply Hbl2; repeat eexists; try done; by rewrite lookup_insert.
      assert (ζvirt !! γ = None). 1: eapply map_disjoint_Some_r; first apply Hdisj3; done.
      assert (ζnewimm !! γ = None). 1: eapply map_disjoint_Some_l; first apply Hdisj2; done.
      unshelve epose proof (Hisstore ℓ Vs γ blk Heq _ _) as Helt.
      1: eapply lookup_union_Some_r; first done; eapply lookup_weaken; last exact Hsub; by rewrite lookup_insert.
      1: by erewrite lookup_union_Some_l.
      assert ((delete γ ζσnew ∪ (ζvirt ∪ <[γ:=blk]> ζnewimm)) = (ζσnew ∪ (ζvirt ∪ ζnewimm))) as Hzetaeq.
      { do 2 (rewrite -insert_union_r; last try done). 2: by rewrite lookup_delete.
        rewrite insert_union_l. rewrite insert_delete; done. }
      iMod (IH (delete γ ζσnew) (ζnewimm) with "[$GCχauth $GCσMLv GCζauth GC_per_loc]") as "(GCζauth&GC_per_loc&GCχauth&GCσMLv)"; try done.
      1: by apply map_disjoint_delete_l.
      1: by apply map_disjoint_delete_r.
      1: { intros γ'; destruct (Hbl2 γ') as [HHL HHR]; split; rewrite dom_delete_L.
          - intros (H'&Hnee%not_elem_of_singleton)%elem_of_difference.
            destruct (HHL H') as (ℓ'&Vs'&HH1&HH2). repeat eexists; try done. by rewrite lookup_insert_ne in HH1.
          - intros (ℓ'&Vs'&HH1&HH2); apply elem_of_difference.
            assert (γ ≠ γ') as Hnee.
            1: eapply lookup_union_Some_raw in HH1 as [HH1|(HHr&HH1)]; intros ->; simplify_eq.
            split; last by eapply not_elem_of_singleton.
            eapply HHR; repeat eexists; last done; by rewrite lookup_insert_ne. }
      1: { refine (is_store_blocks_delete_from_sigma _ _ _ _ (χold ∪ χind) _ _ _ _ _ _ _ _ _  Hisstore).
           - by apply map_disjoint_union_r_2.
           - by eapply elem_of_dom_2.
           - by eapply lookup_union_None_2.
           - erewrite insert_union_r; last done. eapply map_union_mono_l. done.
           - eapply Hbl2.
           - done. }
      1: apply map_subseteq_spec; intros γ' v1 Hv1; eapply lookup_weaken; last exact Hsub;
         rewrite lookup_insert_ne; try done; intros ->; simplify_eq.
      1: iFrame.
      assert ((delete γ ζσnew ∪ (ζvirt ∪ ζnewimm)) = delete γ (ζσnew ∪ (ζvirt ∪ ζnewimm))) as Hdel.
      { rewrite ! delete_union. f_equal. rewrite !delete_notin; done. }
      iMod (lstore_own_insert _ _ blk with "GCζauth") as "(GCζauth&GCnew)".
      1: erewrite Hdel, lookup_delete; done.
      inversion Helt; simplify_eq.
      rewrite !Hdel insert_delete.
      2: by apply lookup_union_Some_l.
      iPoseProof (block_sim_arr_of_auth_strong _ _ Vs lvs with "GCχauth GCζauth") as "#Hsimvs".
      { eapply Forall2_impl; first eassumption. intros x y HH. eapply is_val_mono; last done; done. }
      iPoseProof (lloc_own_auth_get_pub with "GCχauth") as "#Hsimell".
      1: eapply lookup_union_Some_r; first done; eapply lookup_weaken; last exact Hsub; by erewrite lookup_insert.
      iModIntro. iFrame. rewrite lloc_map_pubs_insert_pub. iApply big_sepM_insert.
      1: apply lloc_map_pubs_lookup_None; left; eapply lookup_union_None_2; done.
      iSplitR "GC_per_loc".
      * iExists _, _, _. iRight. iLeft. iFrame. iFrame "Hsimvs". iSplit; first done.
        iSplit; last done. by iExists _.
      * iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
        1: apply lloc_map_pubs_lookup_None; left; eapply lookup_union_None_2; done.
        erewrite insert_union_l. by rewrite insert_delete.
    + assert (γ ∉ dom ζσnew) as Hnin%not_elem_of_dom.
      1: intros H; apply Hbl2 in H as (ℓ'&Vs&HH1&HH2); rewrite lookup_insert in HH1; simplify_eq.
      iMod (IH ζσnew with "[$GCχauth $GCσMLv $GCζauth $GC_per_loc]") as "(GCχauth&GCσMLv&GCζauth&GC_per_loc)"; try done.
      * intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
        -- intros Hg; destruct (HblL Hg) as (ℓ'&Vs&HH1&HH2). repeat eexists; try done.
           rewrite lookup_insert_ne in HH1; try done. intros ->; eapply not_elem_of_dom in Hnin; done.
        -- intros (ℓ'&Vs'&HH1&HH2).
           assert (γ ≠ γ') as Hnee.
           1: eapply lookup_union_Some_raw in HH1 as [HH1|(HHr&HH1)]; intros ->; simplify_eq.
           eapply HblR; repeat eexists; try done. by rewrite lookup_insert_ne.
      * apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
        rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
      * iModIntro. iFrame. rewrite lloc_map_pubs_insert_pub. iApply big_sepM_insert.
        1: apply lloc_map_pubs_lookup_None; left; eapply lookup_union_None_2; done. iFrame.
        iExists nil, TagDefault, nil. iRight. iRight. iRight.
        iPureIntro; (split; first done).
        apply lookup_union_None_2; try done; eapply not_elem_of_dom.
        intros HHH%Hother_blocks; by eapply not_elem_of_dom in Hnold.
  - rewrite -insert_union_r in Hbl2|-*; last done.
    rewrite lloc_map_pubs_insert_foreign -lloc_map_pubs_delete delete_notin; last by apply lookup_union_None_2.
    iApply (IH); try done.
    + intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
      * intros Hg; destruct (HblL Hg) as (ℓ'&Vs&[(_&HH1)|(HH1L&HH1R)]%lookup_insert_Some&HH2); first simplify_eq.
        by repeat eexists.
      * intros (ℓ'&Vs&HH1&HH2).
        assert (γ ≠ γ') as Hnee.
        1: eapply lookup_union_Some_raw in HH1 as [HH1|(HHr&HH1)]; intros ->; simplify_eq.
        eapply HblR; repeat eexists; try done. by rewrite lookup_insert_ne.
    + apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
      rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + iFrame.
  - rewrite -insert_union_r in Hbl2|-*; last done.
    rewrite lloc_map_pubs_insert_priv -lloc_map_pubs_delete delete_notin; last by apply lookup_union_None_2.
    iApply (IH); try done.
    + intros γ'; destruct (Hbl2 γ') as [HblL HblR]; split.
      * intros Hg; destruct (HblL Hg) as (ℓ'&Vs&[(_&HH1)|(HH1L&HH1R)]%lookup_insert_Some&HH2); first simplify_eq.
        by repeat eexists.
      * intros (ℓ'&Vs&HH1&HH2).
        assert (γ ≠ γ') as Hnee.
        1: eapply lookup_union_Some_raw in HH1 as [HH1|(HHr&HH1)]; intros ->; simplify_eq.
        eapply HblR; repeat eexists; try done. by rewrite lookup_insert_ne.
    + apply map_subseteq_spec. intros γ' v1 Hv1. eapply lookup_weaken. 2: exact Hsub.
      rewrite lookup_insert_ne; try done. intros ->; simplify_eq.
    + iFrame.
Qed.

(* Final step: Integrate the ζimm *)
Lemma GC_SI_to_ML σMLvirt ζvirt ζσold ζσnew ζnewimm χold χnew :
    ⌜ζvirt ##ₘ ζnewimm⌝ ∗ ⌜ζσnew ##ₘ ζnewimm⌝ ∗ ⌜ζvirt ##ₘ ζσnew⌝∗ ⌜ζvirt ##ₘ ζσold⌝ ∗ ⌜ζσold ##ₘ ζnewimm⌝ 
  ∗ ⌜is_store_blocks χnew σMLvirt ζσnew⌝
  ∗ ⌜lloc_map_mono χold χnew⌝
  ∗ ⌜is_private_blocks χnew ζnewimm⌝ ∗ ⌜is_store χnew (ζσnew ∪ (ζvirt ∪ ζnewimm)) σMLvirt⌝ ∗ ⌜dom ζvirt ⊆ dom χold⌝
  ∗ ⌜∀ γ, γ ∈ dom ζσold → ∃ ℓ, χold !! γ = Some (LlocPublic ℓ)⌝
  ∗ lloc_own_auth χnew
  ∗ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ lstore_own_auth (ζσold ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χold, per_location_invariant_ML ζvirt ζσold γ ℓ)
 ⊢ |==> lstore_own_auth (ζσnew ∪ (ζvirt ∪ ζnewimm))
  ∗ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χnew, per_location_invariant (ζσnew ∪ (ζvirt ∪ ζnewimm)) σMLvirt ∅ γ ℓ)
  ∗ lloc_own_auth χnew
  ∗ state_interp (σMLvirt : language.language.state ML_lang).
Proof.
  iIntros "(%Hdisj1&%Hdisj2&%Hdisj3&%Hdisj4&%Hdisj5&%Hbl&%Hmono&%Hpriv&%Hisstore&%Hother_blocks&%Holdblocks&GCχauth&GCζauth&GCσMLv&GC_per_loc)".
  iMod (GC_SI_to_ML_2 _ _ ζσold ζσnew with "[$GCχauth $GCζauth $GCσMLv $GC_per_loc]") as "(GCχauth&GCζauth&GCσMLv&GC_per_loc)".
  1: iPureIntro; split_and!; try done.
  iFrame.
  iModIntro.
  clear Hbl Holdblocks Hmono Hisstore Hother_blocks χold Hdisj5 Hdisj4.
  rewrite map_union_assoc.
  iStopProof.
  induction ζnewimm as [|γ blk ζnewimm Hnone IH] using map_ind;
  iIntros "GC_per_loc".
  1: by rewrite map_union_empty.
  apply map_disjoint_insert_r in Hdisj1 as [Hd1 Hdisj1].
  apply map_disjoint_insert_r in Hdisj2 as [Hd2 Hdisj2].
  iPoseProof (IH with "GC_per_loc") as "GC_per_loc"; try done.
  - intros γ' Hdom. eapply Hpriv. rewrite dom_insert_L. set_solver.
  - rewrite -insert_union_r.
    + iApply GC_per_loc_modify_ζ; last done.
      apply lloc_map_pubs_lookup_None. right. left.
      eapply Hpriv. by rewrite dom_insert_L; set_solver.
    + by eapply lookup_union_None_2.
Qed.

Lemma wrap_interp_ml_to_c vs ρml σ ws ρc mem :
  ml_to_c_core vs ρml σ ws ρc mem →
  wrap_state_interp (Wrap.MLState ρml σ) -∗
  not_at_boundary
  ==∗
  wrap_state_interp (Wrap.CState ρc mem) ∗
  at_boundary wrap_lang ∗
  GC (θC ρc) ∅ ∗
  (∃ lvs, lvs ~~∗ vs ∗ ⌜Forall2 (repr_lval (θC ρc)) lvs ws⌝).
Proof using.
  iIntros (Hml_to_c) "Hst Hb".
  destruct Hml_to_c as (ζσ & ζnewimm & lvs & HH).
  destruct HH as (Hmono & Hblocks & Hprivblocks & HζC & Hζdisj &
                    Hstore & Hvals & ? & ? & ? & Hroots & ?).

  iNamed "Hst". iNamed "SIML". iNamed "SIGCrem".
  iNamed "HSI_block_level". iNamed "HSI_GC". SI_GC_agree.
  iMod (ghost_var_update_halves with "Hb SIbound") as "(Hnb & SIbound)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ & GCζ)".
  iMod (ghost_var_update_halves with "SIχ GCχ") as "(SIχ & GCχ)".
  iMod (ghost_var_update_halves with "SIθ GCθ") as "(SIθ & GCθ)".
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots & GCroots)".
  apply map_disjoint_union_r in Hζdisj as [Hζdisj1 Hζdisj2].
  assert (ζvirt ##ₘ ζnewimm) as Hζdisj3.
  { apply map_disjoint_spec. intros γ blk1 blk2 HH1%elem_of_dom_2 HH2%elem_of_dom_2.
    destruct (Hvirt _ HH1) as (ℓ' & Hℓ').
    specialize (Hprivblocks γ HH2).
    eapply lookup_weaken in Hℓ'; last apply Hmono. simplify_eq. }
  iMod (lstore_own_insert_many with "GCζauth") as "(GCζauth & SIζnewimm)".
  { apply map_disjoint_union_l_2; first exact Hζdisj2. done. }
  iMod (lloc_own_mono with "GCχauth") as "GCχauth"; first done.
  assert (ζσ ##ₘ ζnewimm) as Hdisj2 by by eapply is_store_blocks_is_private_blocks_disjoint.
  assert (ζC ρc = ζσ ∪ (ζML ρml ∪ ζnewimm)) as H6B.
  1: { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
  rewrite (map_union_comm _ ζvirt); last done. rewrite -(map_union_assoc).
  iMod (GC_SI_to_ML with "[$GCζauth $GCχNone $GCχauth $HσML]") as "(GCζauth&GC_per_loc&GCχauth&GCσMLv)".
  1: iPureIntro; split_and!; try done; by rewrite H6B in Hstore.
  iPoseProof (block_sim_arr_of_auth_strong _ _ vs lvs with "GCχauth GCζauth") as "#Hsim".
  1: by rewrite -H6B.
  iPoseProof (big_sepM_dom with "GCrootspto") as "GCrootspto".
  iMod (set_to_some with "HσCv GCrootspto") as "(HσCv & GCrootspto)"; first done.
  iModIntro. iFrame "Hnb". rewrite /= /named.
  iFrame "HσCv SIζ SIχ SIθ SIroots SIbound".
  iSplitL "SIinit". { iExists false. iFrame. }
  iSplit.
  { rewrite /GC /SI_block_level /SI_GC /named.
    iExists (ζC ρc), (ζC ρc), (χC ρc), (χC ρc), (rootsC ρc). iFrame.
    iSplitR "GCrootsm GCrootspto"; last first.
    { iSplit; first (iExists _; iFrame); iPureIntro; split_and!; try done.
      eapply expose_llocs_refl, Hmono. }
    { iExists σ. rewrite !H6B. iFrame.
      iPureIntro. split; try apply Hblocks.
      rewrite !dom_union_L. repeat apply union_least;
      intros γ Hγ.
      - destruct Hblocks as [Hb1 Hb2]. apply Hb2 in Hγ as (ℓ&Vs&HH1&HH2).
        eapply elem_of_dom_2; done.
      - edestruct Hmono as [Hm1 Hm2]. eapply subseteq_dom; first exact Hm1. by apply Hother_blocks.
      - by eapply elem_of_dom_2, Hprivblocks. } }
  iExists _; iFrame "Hsim". done.
Qed.

End BoundaryLaws.
