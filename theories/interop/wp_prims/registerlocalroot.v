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

Lemma registerlocalroot_correct e : |- wrap_prog e :: registerlocalroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.

  iApply wp_pre_cases_c_prim; [done..|].
  iPoseProof (ghost_var_agree with "GCrootsf Hfc") as "->".
  destruct roots_fm as [| fm roots_fm ]; first by simpl.
  rewrite map_app in H2. simpl in H2.
  iAssert (⌜¬ l ∈ dom fm⌝)%I as "%Hdom".
  { iIntros "%H". eapply elem_of_dom in H. destruct H as [k Hk].
  iDestruct "GCrootspto" as "((GCrootsptof&GCrootsptol)&GCrootsptog)".
  iPoseProof (big_sepM_lookup_acc with "GCrootsptof") as "((%ww&Hww&_)&_)".
  1: apply Hk. iPoseProof (resources.mapsto_ne with "Hpto Hww") as "%Hne". congruence. }

  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {|
      χC := χC ρc;
      ζC := ζC ρc;
      θC := θC ρc;
      rootsC := ({[l]} ∪ (dom fm)) :: (map dom roots_fm) ++ [dom roots_gm]
   |} mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.
  iDestruct "GCrootsm" as "(GCrootsfm&GCrootsm)".
  iDestruct "Hlr" as "(%fm'&(Hlr1&%Hlr2))".
  iPoseProof (ghost_map_auth_agree with "Hlr1 GCrootsfm") as "->".
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".

  iCombine "GCrootsfm Hlr1" as "GCrootsfm".
  iMod (ghost_map_insert l v with "GCrootsfm") as "(GCrootsfm&Hres)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iDestruct "GCrootsfm" as "(GCrootsfm&Hlr1)".

  iDestruct "GCrootspto" as "((GCrootsptof&GCrootsptol)&GCrootsptogg)".
  iPoseProof (big_sepM_insert) as "(_&HR)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof ("HR" with "[Hpto GCrootsptof]") as "GCrootsptof".
  1: iFrame "GCrootsptof"; iExists w; iFrame; done.
  iClear "HR".

  iMod (ghost_var_update_halves with "GCrootsf Hfc") as "(GCrootsf&Hfc)".

  iAssert (([∗ list] y1;y2 ∈ (f::fc);(<[l:=v]>fm::roots_fm), ghost_map_auth y1 (1/2) y2))%I
  with "[GCrootsm GCrootsfm]" as "GCrootsm".
  { simpl. iSplitL "GCrootsfm"; done. }

  iAssert (local_roots f ({[l]} ∪ r)) with "[Hlr1]" as "Hlr".
  { unfold local_roots. iExists (<[l:=v]> fm). iFrame. iPureIntro.
    rewrite dom_insert_L. by rewrite Hlr2. }

  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame "Hres Hfc Hlr".
  iExists _, _, _, _, (<[l:=v]> fm :: roots_fm), roots_gm, _. unfold named. iFrame.
  iPureIntro; split_and!; eauto.
  - rewrite map_app. simpl. f_equal. by rewrite dom_insert_L.
  - apply Forall_app.
    unfold roots_are_live in Hrootslive. rewrite Forall_app in Hrootslive.
    destruct Hrootslive as [Hrootslivel Hrootsliveg].
    split; last done.
    apply Forall_cons_1 in Hrootslivel.
    destruct Hrootslivel as [Hrootslivefm Hrootslivef].
    econstructor; last done.
    intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply Hrootslivefm.
    inv_repr_lval. by eapply elem_of_dom_2.
Qed.

End Laws.
