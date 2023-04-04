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

Lemma length_correct E e : |- prims_prog e @ E :: length_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  destruct bl as [tg vs0].
  do 2 (iExists _; iSplit; first done). iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "(Hpto & Hptoacc)".
  iPoseProof (lstore_own_elem_of with "GCζvirt Hpto") as "%Helem".
  iAssert ⌜∃ m', ζC ρc !! γ = Some (Bvblock (m', (tg, vs0)))⌝%I as "%Helem2".
  1: { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
       eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
       inversion Hfrz; simplify_eq; eauto. }
  destruct Helem2 as [m' Helem2].

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #(length vs0)) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hpto Hptoacc] [$Hpto $Hptoacc]"); try done; [].
  rewrite /GC /named.
  iExists _, (ζσ ∪ ζvirt), ζσ, ζvirt, _, χvirt, σMLvirt, _. iExists _.
  iFrame. iPureIntro; split_and!; eauto.
Qed.

End Laws.
