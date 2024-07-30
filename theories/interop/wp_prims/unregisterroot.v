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

Lemma unregisterroot_correct e : |- wrap_prog e :: unregisterroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_map_lookup with "GCrootsm Hpto") as "%Helem".

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := rootsC ρc ∖ {[l]} |} mem).
  iSplit. { iPureIntro. econstructor; eauto. rewrite -H2. by eapply elem_of_dom_2. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCrootss") as "(SIroots&GCrootss)".
  iMod (ghost_map_delete with "GCrootsm Hpto") as "GCrootsm".
  iDestruct (ROOTS_delete with "GCROOTS") as (w) "(GCROOTS & Hpto & %)"; first done.

  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! w with "[- $Hpto]"). iSplit; last done.
  repeat iExists _. iFrame.
  rewrite /= dom_delete_L (_: dom roots_m = rootsC ρc) //. by iFrame.
Qed.

End Laws.
