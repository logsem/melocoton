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

Lemma read_foreign_correct e : |- prims_prog e :: read_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  do 2 (iExists _; iSplit; first done). iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "(Hpto & Hsim)".
  iDestruct (lstore_own_mut_of with "GCζvirt Hpto") as %[Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Bforeign (Some w'))⌝%I as "%Helem2".
  { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
    eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
    inversion Hfrz; by simplify_eq. }
  destruct HGCOK as [HGCL HGCR]. inv_repr_lval.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV w') ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hpto Hsim] [$Hpto $Hsim]").
  rewrite /GC /named.
  iExists _, (ζσ ∪ ζvirt), ζσ, ζvirt, _, χvirt, σMLvirt, _. iExists _.
  iFrame. iPureIntro; split_and!; eauto. done.
Qed.

End Laws.
