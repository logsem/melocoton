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

Lemma registerroot_correct e : |- wrap_prog e :: registerroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct (ROOTS_pto_notin with "GCROOTS Hpto") as %Hdom.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := {[l]} ∪ rootsC ρc |} mem).
  iSplit. { iPureIntro. econstructor; eauto. congruence. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCrootss") as "(SIroots&GCrootss)".
  iMod (ghost_map_insert with "GCrootsm") as "(GCrootsm&Hres)".
  1: by eapply not_elem_of_dom.
  iDestruct (ROOTS_insert with "GCROOTS Hpto") as "GCROOTS"; eauto.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame "Hres".
  repeat iExists _. unfold named. iFrame. iPureIntro; split_and!; eauto.
  rewrite dom_insert_L. rewrite (_: dom roots_m = rootsC ρc) //.
Qed.

End Laws.
