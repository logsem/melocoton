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

Lemma length_correct e : |- wrap_prog e :: length_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H". iPoseProof "Hpto" as "#Hpto".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree. iNamed "HSI_block_level".
  iDestruct (lstore_own_head_of with "GCζauth Hpto") as %(blk&Helem&Hagr).
  destruct blk as [(m&tg'&vs)| |]; try (cbn in *; congruence).
  cbn in Hagr. simplify_eq.
  iAssert ⌜∃ m', ζC ρc !! γ = Some (Bvblock (m', (tg, vs)))⌝%I as "%Helem2".
  1: { iPureIntro.
       eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
       inversion Hfrz; simplify_eq; eauto. }
  destruct Helem2 as [m' Helem2].

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #(length vs)) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont"); try done; [].
  rewrite /GC /named.
  do 5 iExists _. iFrame. iSplit; last done.
  iExists _. iFrame. iPureIntro; split_and!; done.
Qed.

End Laws.
