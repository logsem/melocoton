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

Lemma unregisterroot_correct e : |- prims_prog e :: unregisterroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  do 2 (iExists _; iSplit; first done). iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_map_lookup with "GCrootsm Hpto") as "%Helem".

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := rootsC ρc ∖ {[l]} |} mem).
  iSplit. { iPureIntro. econstructor; eauto. rewrite -H2. by eapply elem_of_dom_2. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_delete with "GCrootsm Hpto") as "GCrootsm".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first eapply Helem.
  iPoseProof ("HL" with "GCrootspto") as "((%W&Hpto&%Hw)&GCrootspto)".
  iClear "HL".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" $! W with "[-Hpto] Hpto []"). 2: done.
  do 9 iExists _. iFrame. iPureIntro; split_and!; eauto.
  - rewrite dom_delete_L. rewrite (_: dom roots_m = rootsC ρc) //.
  - intros ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hrootslive.
Qed.

End Laws.
