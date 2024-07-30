From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics basics_resources.
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

Lemma write_foreign_correct e : |- wrap_prog e :: write_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ".
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "[Hpto Hγ]".
  iPoseProof (hgh_lookup_block with "GCHGH Hpto") as (b) "(%Hb&%Hγ)".
  inversion Hb; subst; clear Hb.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState (WrapstateC (χC ρc) (<[γ:=Bforeign (Mut, Some w')]> (ζC ρc)) (θC ρc) (rootsC ρc)) mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ&GCζ)".
  iMod (hgh_modify_block with "GCHGH Hpto") as "(GCHGH & Hpto)"; first done.
  do 3 iModIntro. iFrame.
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  change (Z.of_nat 0) with (Z0).
  iApply "Hcont". iFrame.
  iApply ("Cont" with "[- $Hpto]"). iFrame.
  rewrite /GC /named. 
  iExists _, _, _, _. iFrame.
  iPureIntro; eapply GC_correct_modify_foreign; eauto.
Qed.

End Laws.
