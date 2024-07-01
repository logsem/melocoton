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
From melocoton.interop Require Import weakestpre wp_utils hybrid_ghost_heap.
Import Wrap.

(** lemmas to switch between the ML<->C state interp at a boundary *)

Section BoundaryLaws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Lemma wrap_interp_c_to_ml ws ρc mem θ fc vs lvs :
  Forall2 (repr_lval θ) lvs ws →
  wrap_state_interp (Wrap.CState ρc mem) -∗
  GC θ -∗
  current_fc fc -∗
  at_boundary wrap_lang -∗
  lvs ~~∗ vs -∗
  ∃ ρml σ ζ,
  ⌜c_to_ml_heap ρc mem ρml σ ζ⌝ ∗
  ⌜c_to_ml_vals ws ρc vs ρml ζ⌝ ∗
  |==> wrap_state_interp (Wrap.MLState ρml σ) ∗ not_at_boundary.
Proof using.
  iIntros (Hlv) "Hσ HGC Hfc Hnb #Hblk".
  iNamed "Hσ". iNamed "SIC". iNamed "HGC". simplify_eq. SI_GC_agree.

  pose (roots_fm++[roots_gm]) as roots_m.
  iAssert (⌜Forall (λ r,
    ∀ k lv, r !! k = Some lv
    → ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w)
  roots_m⌝)%I as "%Hroots".
  { admit. }

  destruct (make_repr (θC ρc) roots_m roots_fm roots_gm mem) as [privmem Hpriv]; try done.

  iDestruct (hgh_export_ml_heap with "GCHGH")
    as (ζ' χ' ζfreeze) "(GCHGH & Hσ & %Hχ & %Hfrz & %Hζ)".
  iAssert (⌜Forall2 (is_val χ' ζfreeze) vs lvs⌝)%I as %Hval.
  { iDestruct (hgh_block_sim_is_vals with "GCHGH Hblk") as %Hval. iPureIntro.
    eapply Forall2_impl; first done. intros ? ?. eapply is_val_mono; eauto.
    by eapply lstore_hybrid_repr_lstore_sub. }

  (* TODO: refactor opsem to use lstore_hybrid_repr? *)
  destruct Hζ as (ζσ&?&?&?&?).
  iExists (WrapstateML _ _ _ _), _, _. iSplit. 2: iSplit.
  { iPureIntro. unfold c_to_ml_heap. cbn.
    eexists ζσ. split_and!; eauto. by rewrite map_union_comm. }
  { iPureIntro. unfold c_to_ml_vals. cbn. exists lvs. split_and!; eauto. }

  iMod (ghost_var_update_halves with "Hnb SIbound") as "(Hb & SIbound)".
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ & SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ & SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ & SIθ)".
  iMod (ghost_var_update_halves with "GCroots SIroots") as "(GCroots & SIroots)".
  iMod (set_to_none with "HσC GCrootspto") as "(HσC & GCrootspto)"; first done.

  iModIntro. iSplitR "SIbound"; last by iFrame "SIbound".
  rewrite /= /named. iFrame "Hσ".
  unfold private_state_interp, ML_state_interp, GC_remnant, named; cbn.
  iExists fc. iFrame. iSplit. { iExists roots_fm, roots_gm, roots_f. iFrame. done. }
  iPureIntro.
  (* destruct Hpriv as (mem_r & Hpriv1 & Hpriv2 & Hpriv3). by apply map_disjoint_dom. *)
(* Qed. *)
Admitted.

Lemma wrap_interp_c_to_ml_out ow ρc mem θ fc ov olv :
  repr_lval_out θ olv ow →
  wrap_state_interp (Wrap.CState ρc mem) -∗
  GC θ -∗
  current_fc fc -∗
  at_boundary wrap_lang -∗
  olv ~~ₒ ov -∗
  ∃ ρml σ ζ,
  ⌜c_to_ml_heap ρc mem ρml σ ζ⌝ ∗
  ⌜c_to_ml_outcome ow ρc ov ρml ζ⌝ ∗
  |==> wrap_state_interp (Wrap.MLState ρml σ) ∗ not_at_boundary.
Proof using.
  iIntros (Hlv) "Hσ HGC Hfc Hnb Hblk".
  iNamed "Hσ". iNamed "SIC". iNamed "HGC". simplify_eq. SI_GC_agree.

  pose (roots_fm++[roots_gm]) as roots_m.
  iAssert (⌜Forall (λ r,
    ∀ k lv, r !! k = Some lv
    → ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w)
  roots_m⌝)%I as "%Hroots".
  { admit. }

  destruct (make_repr (θC ρc) roots_m roots_fm roots_gm mem) as [privmem Hpriv]; try done.

  iDestruct (hgh_export_ml_heap with "GCHGH")
    as (ζ' χ' ζfreeze) "(GCHGH & Hσ & %Hχ & %Hfrz & %Hζ)".
  iAssert (⌜is_val_out χ' ζfreeze ov olv⌝)%I as %Hval.
  { iDestruct (hgh_block_sim_is_out with "GCHGH Hblk") as %Hval. iPureIntro.
    eapply (is_val_out_mono χ' χ' ζ'); eauto.
    by eapply lstore_hybrid_repr_lstore_sub. }

  destruct Hζ as (ζσ&?&?&?&?).
  (* TODO: refactor opsem to use lstore_hybrid_repr? *)
  iExists (WrapstateML _ _ _ _), _, _. iSplit. 2: iSplit.
  { iPureIntro. unfold c_to_ml_outcome. cbn.
    eexists ζσ. split_and!; eauto;
    first by rewrite map_union_comm. }
  { iPureIntro. unfold c_to_ml_outcome. cbn.
    exists olv. split; eauto. }

  iMod (ghost_var_update_halves with "Hnb SIbound") as "(Hb & SIbound)".
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ & SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ & SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ & SIθ)".
  iMod (ghost_var_update_halves with "GCroots SIroots") as "(GCroots & SIroots)".
  iMod (set_to_none with "HσC GCrootspto") as "(HσC & GCrootspto)"; first done.

  iModIntro. iSplitR "SIbound"; last by iFrame "SIbound".
  rewrite /= /named. iFrame "Hσ".
  unfold private_state_interp, ML_state_interp, GC_remnant, named; cbn.
  iFrame.
  iExists fc. iFrame "Hfc".
  iSplit. { iExists roots_fm, roots_gm, roots_f. iFrame. done. }
  iPureIntro.
  (* destruct Hpriv as (mem_r & Hpriv1 & Hpriv2 & Hpriv3); by apply map_disjoint_dom. *)
Admitted.

Lemma wrap_interp_ml_to_c vs ρml σ ws ρc mem :
  ml_to_c_heap ρml σ ρc mem →
  (∃ lvs, Forall2 (repr_lval (θC ρc)) lvs ws ∧ Forall2 (is_val (χC ρc) (ζC ρc)) vs lvs) →
  wrap_state_interp (Wrap.MLState ρml σ) -∗
  not_at_boundary
  ==∗
  wrap_state_interp (Wrap.CState ρc mem) ∗
  at_boundary wrap_lang ∗
  GC (θC ρc) ∗
  (∃ fc, current_fc fc) ∗
  (∃ lvs, lvs ~~∗ vs ∗ ⌜Forall2 (repr_lval (θC ρc)) lvs ws⌝).
Proof using.
  iIntros (Hml_to_c Hlvs) "Hst Hb".
  destruct Hlvs as (lvs & Hrepre & Hisval).
  destruct Hml_to_c as (ζσ & ζnewimm & HH).
  destruct HH as (Hmono & Hblocks & Hprivblocks & HζC & Hζdisj &
                    Hstore & ? & ? & Hroots & ?).

  iNamed "Hst". iNamed "SIML". iNamed "SIGCrem".
  iDestruct (hgh_dom_lstore_sub with "GCHGH") as %Hζsub.
  iMod (ghost_var_update_halves with "Hb SIbound") as "(Hnb & SIbound)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ & GCζ)".
  iMod (ghost_var_update_halves with "SIχ GCχ") as "(SIχ & GCχ)".
  iMod (ghost_var_update_halves with "SIθ GCθ") as "(SIθ & GCθ)".
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots & GCroots)".
  apply map_disjoint_union_r in Hζdisj as [Hζdisj1 Hζdisj2].
  iMod (hgh_import_ml_interp _ _ _ _ (ζC ρc) with "GCHGH HσML") as "GCHGH"; eauto.
  (* TODO: use lstore_hybrid_repr in the opsem? *)
  { exists ζσ. split_and!; eauto.
    { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
    { apply map_disjoint_union_r; split; eauto.
      by eapply is_store_blocks_is_private_blocks_disjoint. } }
  { rewrite HζC !dom_union_L. repeat apply union_least.
    { destruct Hmono as [?%subseteq_dom ?]. set_solver. }
    { eapply is_store_blocks_lstore_dom_sub; eauto. }
    { eapply is_private_blocks_dom_sub; eauto. } }
  iMod (set_to_some with "HσCv GCrootspto") as "(HσCv & GCrootspto)"; first done.
  iDestruct (hgh_block_sim_of_vals _ _ _ vs lvs with "GCHGH") as "#Hsim"; first eassumption.

  iModIntro. iFrame "Hnb". rewrite /= /named.
  iFrame "HσCv SIζ SIχ SIθ SIroots SIbound".
  iSplitL "SIinit". { iExists false. iFrame. }
  iSplitR "Hfc".
  { rewrite /GC /named. iExists _, _, _, _, roots_fm, roots_gm, roots_f.
    rewrite GCrootsm. iFrame. rewrite <- GCrootsm.
    iPureIntro; split_and!; eauto. }
  iSplit; iExists _.
  { by iFrame "Hfc".  }
  { by iFrame "Hsim". }
Qed.

Lemma wrap_interp_ml_to_c_out ov ρml σ ow ρc mem :
  ml_to_c_heap ρml σ ρc mem →
  ml_to_c_outcome ov ow ρc →
  wrap_state_interp (Wrap.MLState ρml σ) -∗
  not_at_boundary
  ==∗
  wrap_state_interp (Wrap.CState ρc mem) ∗
  at_boundary wrap_lang ∗
  GC (θC ρc) ∗
  (∃ fc, current_fc fc) ∗
  (∃ olv, olv ~~ₒ ov ∗ ⌜repr_lval_out (θC ρc) olv ow⌝).
Proof using.
  iIntros (Hml_to_c H) "Hst Hb".
  destruct H as (lv & Hval & Hrepre).
  destruct Hml_to_c as (ζσ & ζnewimm & HH).
  destruct HH as (Hmono & Hblocks & Hprivblocks & HζC & Hζdisj &
                    Hstore & ? & ? & Hroots & ?).

  iNamed "Hst". iNamed "SIML". iNamed "SIGCrem".
  iDestruct (hgh_dom_lstore_sub with "GCHGH") as %Hζsub.
  iMod (ghost_var_update_halves with "Hb SIbound") as "(Hnb & SIbound)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ & GCζ)".
  iMod (ghost_var_update_halves with "SIχ GCχ") as "(SIχ & GCχ)".
  iMod (ghost_var_update_halves with "SIθ GCθ") as "(SIθ & GCθ)".
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots & GCroots)".
  apply map_disjoint_union_r in Hζdisj as [Hζdisj1 Hζdisj2].
  iMod (hgh_import_ml_interp _ _ _ _ (ζC ρc) with "GCHGH HσML") as "GCHGH"; eauto.
  (* TODO: use lstore_hybrid_repr in the opsem? *)
  { exists ζσ. split_and!; eauto.
    { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
    { apply map_disjoint_union_r; split; eauto.
      by eapply is_store_blocks_is_private_blocks_disjoint. } }
  { rewrite HζC !dom_union_L. repeat apply union_least.
    { destruct Hmono as [?%subseteq_dom ?]. set_solver. }
    { eapply is_store_blocks_lstore_dom_sub; eauto. }
    { eapply is_private_blocks_dom_sub; eauto. } }
  iMod (set_to_some with "HσCv GCrootspto") as "(HσCv & GCrootspto)"; first done.
  iDestruct (hgh_block_sim_of_out _ _ _ ov lv with "GCHGH") as "#Hsim"; first eassumption.

  iModIntro. iFrame "Hnb". rewrite /= /named.
  iFrame "HσCv SIζ SIχ SIθ SIroots SIbound".
  iSplitL "SIinit". { iExists false. iFrame. } iSplitR "Hfc".
  { rewrite /GC /named. iExists _, _, _, _, roots_fm, roots_gm, roots_f.
    rewrite GCrootsm. iFrame. rewrite <- GCrootsm.
    iPureIntro; split_and!; eauto. }
  iSplit; iExists _.
  { iFrame "Hfc". }
  { iSplit; eauto. }
Qed.

End BoundaryLaws.
