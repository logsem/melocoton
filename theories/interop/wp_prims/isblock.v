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

Lemma isblock_correct e : |- wrap_prog e :: isblock_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #(match lv with  Lint _ => 0 | Lloc _ => 1 end)) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; edestruct lv; try (econstructor; eauto; fail). }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply "Hcont". iFrame.
  destruct lv; iApply ("Cont").
  all: rewrite /GC /named.
  all: iExists _, _, σMLvirt, _; iExists _.
  all: iFrame; iPureIntro; split_and!; eauto; done.
Qed.

End Laws.
