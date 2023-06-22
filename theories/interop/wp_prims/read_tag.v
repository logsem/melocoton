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

Lemma read_tag_correct e : |- wrap_prog e :: read_tag_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree. iNamed "HSI_block_level".
  iPoseProof (lstore_own_elem_of with "GCζauth Hpto") as "%Helem".
  iAssert ⌜∃ bl2, ζC ρc !! γ = Some bl2 ∧ block_tag bl2 = block_tag bl⌝%I as "%Helem2".
  1: { iPureIntro.
       eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
       inversion Hfrz; simplify_eq; eauto. }
  edestruct Helem2 as (bl2&Hlu&Heqtag).
  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #(tag_as_int (block_tag bl2))) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done. rewrite -Heqtag.
  iApply "Hcont". iFrame.
  iApply ("Cont" with "[-Hpto] [$Hpto]"); try done; [].
  rewrite /GC /named.
  do 5 iExists _; iFrame. iSplit; last done.
  iExists _; iFrame; done.
Qed.

End Laws.
