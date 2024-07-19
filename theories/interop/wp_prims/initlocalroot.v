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


Lemma initlocalroot_correct e : |- wrap_prog e :: initlocalroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.

  iApply wp_pre_cases_c_prim; [done..|].
  pose (∅::(rootsC ρc)) as roots_s.

  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {|
      χC := χC ρc;
      ζC := ζC ρc;
      θC := θC ρc;
      rootsC :=  roots_s;
   |} mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.

  (* Alloc local_roots f ∅ *)
  iMod (ghost_map_alloc_strong (frame_fresh roots_f) (∅:roots_map) (frame_fresh_infinite roots_f))
    as "(%f&%ffresh&Hlr&_)".
  iDestruct "Hlr" as "(Hlr&HGCrootsfm)".

  iMod (ghost_map_insert f () with "GCrootslive") as "(GCrootslive&flive)".
  { rewrite <- not_elem_of_dom. rewrite Hlocalrootslive.
    by rewrite not_elem_of_list_to_set. }

  iAssert (local_roots f (dom ∅)) with "[Hlr flive]" as "Hlr".
  { unfold local_roots. iExists ∅. by iFrame. }
  replace (dom (∅:roots_map)) with (∅:gset addr); last by rewrite dom_empty_L.

  iAssert ([∗ list] f0;r ∈ (f::roots_f);(∅::roots_fm), ghost_map_auth f0 (1/2) r)%I
  with "[GCrootsm HGCrootsfm]" as "GCrootsm".
  { simpl. iFrame. }

  iAssert ([∗ list] r ∈ (∅ :: roots_fm ++ [roots_gm]), [∗ map] a↦v ∈ r,
           ∃ w : word, a ↦C{DfracOwn 1} w ∗ ⌜repr_lval (θC ρc) v w⌝)%I
  with "[GCrootspto]" as "GCrootspto".
  { by iFrame. }

  (* Update frame in GC *)
  iMod (ghost_var_update_halves roots_s with "SIroots GCroots") as "(SIroots&GCroots)".

  iPoseProof (ghost_var_agree with "GCrootsf Hfc") as "->".

  (* Update current_fc *)
  iMod (ghost_var_update_halves (f::fc) with "Hfc GCrootsf") as "(Hfc&GCrootsf)".

  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame.
  iExists _, _, _, roots_s, (∅::roots_fm), roots_gm, _, _. iFrame. iPureIntro.
  split_and!; eauto.
  - simpl. rewrite dom_empty_L. by rewrite H2.
  - apply Forall_app. apply Forall_app in Hrootslive.
    destruct Hrootslive as [Hrootslivef Hrootsliveg]. split; last done.
    econstructor; done.
  - rewrite list_to_set_cons. rewrite dom_insert_L. congruence.
  - by apply NoDup_cons_2.
Qed.

End Laws.
