From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Import basics wp_utils.
From melocoton.interop Require Export prims weakestpre prims_proto.
From melocoton.interop.wp_prims Require Import common.
From melocoton.mlanguage Require Import weakestpre.
Import Wrap.

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

(* TODO: refactor to share proof with wp_prim_alloc *)
Lemma alloc_foreign_correct E e : |- prims_prog e @ E :: alloc_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  do 2 (iExists _; iSplit; first done). iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ id χC' ζC' θC' (aret:loc) mem',
      χC ρc !! γ = None ∧
      (∀ γ' id', χC ρc !! γ' = Some (LlocForeign id') → id' ≠ id) ∧
      χC' = <[ γ := LlocForeign id ]> (χC ρc) ∧
      ζC' = <[ γ := Bforeign None ]> (ζC ρc) ∧
      GC_correct ζC' θC' ∧
      repr θC' roots_m privmem mem' ∧
      roots_are_live θC' roots_m ∧
      θC' !! γ = Some aret ∧
      e' = WrSE (ExprV (# aret)) ∧
      σ' = CState (WrapstateC χC' ζC' θC' (rootsC ρc)) mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & id & χC' & ζC' & θC' & aret & mem' &
                  HγNone & Hidfresh & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  assert (χvirt !! γ = None) as Hχvirtγ.
  { eapply not_elem_of_dom. destruct Hχvirt as [<- _].
    by eapply not_elem_of_dom. }
  assert (ζσ !! γ = None) as Hζσγ.
  { eapply not_elem_of_dom. destruct Hstore_blocks as [HHL HHR].
    intros (ℓ&Vs&HX1&HX2)%HHR. congruence. }
  assert (ζvirt !! γ = None) as Hζvirtγ.
  { eapply not_elem_of_dom. intros H. eapply not_elem_of_dom in Hχvirtγ.
    apply Hχvirtγ. eapply elem_of_weaken; first done. done. }
  assert (ζC ρc !! γ = None) as HζCγ.
  { destruct Hfreezeρ as [HL HR]. eapply not_elem_of_dom. rewrite HL.
    rewrite dom_union_L.
    intros [HH|HH]%elem_of_union.
    all: eapply elem_of_dom in HH; destruct HH as [v HHv]; congruence. }

  assert (freeze_lstore (<[γ := Bforeign None]> (ζC ρc)) (ζσ ∪ <[γ:=Bforeign None]> ζvirt)) as Hfreezeρ_new.
  { destruct Hfreezeρ as [HfL HfR]; split.
    - rewrite !dom_insert_L HfL dom_union_L. set_solver+.
    - rewrite <- insert_union_r. 2: done.
      intros γ1 b1 b2 ?%lookup_insert_Some ?%lookup_insert_Some.
      destruct_or!; destruct_and!; simplify_eq; eauto. }

  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".

  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".

  iMod (lstore_own_insert _ γ (Bforeign None) with "GCζvirt") as "(GCζvirt & Hbp1)". 1: done.
  iMod (lloc_own_allocate_foreign _ γ id with "[] GCχvirt") as "(GCχvirt&Hbp2)". 1: done.

  do 3 iModIntro. iFrame. cbn -[prims_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" $! θC' γ with "[-Hbp2 Hbp1] [Hbp2 Hbp1] []"); try done.
  3: iPureIntro; by econstructor.
  2: iFrame; by eauto.
  rewrite /GC /named.
  iExists _, _, (ζσ), (<[γ:=Bforeign None]> ζvirt), _, (<[γ:=LlocForeign id]> χvirt).
  iExists σMLvirt, _, _.
  rewrite pub_locs_in_lstore_alloc_foreign //. iFrame.
  iPureIntro; split_and!; eauto.
  2: destruct Hstore_blocks as [HsL HsR]; split.
  - eapply map_disjoint_insert_r. split; done.
  - intros ℓ Hdom. destruct (HsL ℓ Hdom) as (γ1 & Hγ1). exists γ1. rewrite lookup_insert_ne; first done.
    intros ->; congruence.
  - intros γ1; split.
    + intros (ℓ&Vs&HH1&HH2)%HsR. exists ℓ,Vs; split; try done.
      rewrite lookup_insert_ne; first done. intros ->; congruence.
    + intros (ℓ&Vs&[[??]|[??]]%lookup_insert_Some&HH2); try congruence.
      eapply HsR. by exists ℓ,Vs.
  - erewrite !dom_insert_L. clear -Hother_blocks. set_solver.
  - intros ℓ vs γ1 blk1 HH1 [[??]|[? HH2]]%lookup_insert_Some HH3; try congruence.
    rewrite -!insert_union_r in HH3|-*; try done.
    rewrite lookup_insert_ne in HH3; last done.
    specialize (Hstore ℓ vs γ1 blk1 HH1 HH2 HH3).
    inversion Hstore; subst. econstructor.
    eapply Forall2_impl; first eassumption.
    intros vml vl HH4. eapply is_val_mono. 3: apply HH4.
    + eapply insert_subseteq. done.
    + eapply insert_subseteq. eapply lookup_union_None; done.
  - apply expose_llocs_insert_both; eauto. intros γ' ? _ HH1 ->.
    destruct Hχvirt as (Hdom & ? & Hexp).
    assert (is_Some (χC ρc !! γ')) as [? HH2].
    { rewrite -elem_of_dom Hdom elem_of_dom //. }
    specialize (Hexp _ _ _ HH2 HH1). inversion Hexp; simplify_eq.
    naive_solver.
  - cbn. by apply lloc_map_inj_insert_foreign.
  - eapply GC_correct_transport; done.
Qed.

End Laws.
