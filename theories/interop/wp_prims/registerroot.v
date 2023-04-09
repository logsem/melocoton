From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
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

Lemma registerroot_correct e : |- prims_prog e :: registerroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  do 2 (iExists _; iSplit; first done). iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iAssert (⌜¬ l ∈ dom roots_m⌝)%I as "%Hdom".
  1: { iIntros "%H". eapply elem_of_dom in H; destruct H as [k Hk].
       iPoseProof (big_sepM_lookup_acc with "GCrootspto") as "((%ww&Hww&_)&_)".
       1: apply Hk. iPoseProof (resources.mapsto_ne with "Hpto Hww") as "%Hne". congruence. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := {[l]} ∪ rootsC ρc |} mem).
  iSplit. { iPureIntro. econstructor; eauto. congruence. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_insert with "GCrootsm") as "(GCrootsm&Hres)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof (big_sepM_insert) as "(_&HR)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof ("HR" with "[Hpto GCrootspto]") as "GCrootspto"; first iFrame "GCrootspto".
  1: iExists w; iFrame; done.
  iClear "HR".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hres] Hres").
  do 9 iExists _. unfold named. iFrame. iPureIntro; split_and!; eauto.
  - rewrite dom_insert_L. rewrite (_: dom roots_m = rootsC ρc) //.
  - intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply Hrootslive.
    inv_repr_lval. by eapply elem_of_dom_2.
Qed.

End Laws.
