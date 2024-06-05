From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Import basics wp_utils.
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

Lemma raise_correct e : |- wrap_prog e :: raise_proto.
Proof using.
  iIntros (Hnprim ? ? ?) "Hproto". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "Hb Hcont".
  iApply wp_wrap_call; first done. cbn [snd].

  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hst".
  iDestruct (SI_at_boundary_is_in_C with "Hst Hb") as %(ρc&mem&->). simpl.

  iModIntro.
  iRight; iRight. iSplit; first done.
  iExists (λ '(e2, σ2),
    e2 = WrSE (ExprO (OExn w)) ∧
    σ2 = CState ρc mem).
  iSplit. { iPureIntro. eapply PrimS. eapply RaiseS; eauto. }
  iIntros (? ? (-> & ->)).
  do 3 iModIntro. iFrame "Hst".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hst".
  iModIntro. iLeft. iExists (OExn w). cbn. iFrame. iSplit; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame.
Qed.

End Laws.
