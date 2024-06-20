From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export prims weakestpre prims_proto wp_utils.
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

  iApply wp_pre_cases_c_prim; [done..|].

  iDestruct "GCrootspto" as "(GCrootsptog&GCrootsptol)".
  iAssert (⌜¬ l ∈ dom roots_gm⌝)%I as "%Hdom".
    { iIntros "%H". eapply elem_of_dom in H. destruct H as [k Hk].
    iPoseProof (big_sepM_lookup_acc with "GCrootsptog") as "((%ww&Hww&_)&_)".
    1: apply Hk. iPoseProof (resources.mapsto_ne with "Hpto Hww") as "%Hne". congruence. }

  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {|
      χC := χC ρc;
      ζC := ζC ρc;
      θC := θC ρc;
      rootsC := ({[l]} ∪ (dom roots_gm)) :: (map dom roots_fm)
   |} mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_insert with "GCrootsg") as "(GCrootsg&Hres)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof (big_sepM_insert) as "(_&HR)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof ("HR" with "[Hpto GCrootsptog]") as "GCrootsptog"; first iFrame "GCrootsptog".
  1: iExists w; iFrame; done.
  iClear "HR".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame "Hres".
  repeat iExists _. unfold named. iFrame. iPureIntro; split_and!; eauto.
  - admit. (* rewrite dom_insert_L. rewrite (_: dom roots_m = rootsC ρc) //. *)
  - inversion Hrootslive.
    econstructor; last done.
    intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply H1.
    inv_repr_lval. by eapply elem_of_dom_2.
Admitted.

End Laws.
