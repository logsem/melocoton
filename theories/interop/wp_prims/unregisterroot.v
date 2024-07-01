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

Lemma unregisterroot_correct e : |- wrap_prog e :: unregisterroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_map_lookup with "GCrootsg Hpto") as "%Helem".
  rewrite map_app in H2. simpl in H2.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {|
      χC := χC ρc;
      ζC := ζC ρc;
      θC := θC ρc;
      rootsC := (map dom roots_fm) ++ [(dom roots_gm) ∖ {[l]}]
   |} mem).
  iSplit. { iPureIntro. econstructor; eauto. by eapply elem_of_dom_2. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_delete with "GCrootsg Hpto") as "GCrootsg".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first eapply Helem.
  iDestruct "GCrootspto" as "(GCrootsptol&GCrootsptog)". simpl.
  iDestruct "GCrootsptog" as "(GCrootsptog&_)".
  iPoseProof ("HL" with "GCrootsptog") as "((%W&Hpto&%Hw)&GCrootsptog)".
  iClear "HL".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! W with "[- $Hpto]"). iSplit; last done.
  repeat iExists _. iFrame. simpl. iPureIntro; split_and!; eauto.
  - rewrite map_app. simpl. f_equal. by rewrite dom_delete_L.
  - apply Forall_app.
    unfold roots_are_live in Hrootslive. rewrite Forall_app in Hrootslive.
    destruct Hrootslive as [Hrootslivel Hrootsliveg].
    split; first done.
    econstructor; last done. simpl in Hrootsliveg.
    rewrite Forall_singleton in Hrootsliveg.
    intros ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hrootsliveg.
Qed.

End Laws.
