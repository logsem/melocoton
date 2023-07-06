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

Lemma write_foreign_correct e : |- wrap_prog e :: write_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree. iNamed "HSI_block_level".
  iDestruct "Hpto" as "(Hpto & %fid & Hsim)".
  iPoseProof (lloc_own_foreign_of with "GCχauth Hsim") as "%Hχfgn".
  iDestruct (lstore_own_mut_of with "GCζauth Hpto") as %[Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Bforeign wo)⌝%I as "%Helem2".
  1: { iPureIntro.
       destruct Hζfuture as [HL HR].
       assert (γ ∈ dom (ζC ρc)) as [v Hv]%elem_of_dom by by (rewrite HL; eapply elem_of_dom_2).
       specialize (HR _ _ _ Hv Helem) as Hinv. inversion Hinv; subst; done. }

  iApply wp_pre_cases_c_prim; [done..|].

  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := <[γ:=_]> (ζC ρc); θC := θC ρc; rootsC := rootsC ρc |} mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.

  iMod (lstore_own_update _ _ _ (Bforeign (Some w')) with "GCζauth Hpto") as "(GCζvirt&Hpto)".
  1: done. 
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ&GCζ)".
  iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
  { eapply lloc_map_pubs_lookup_None. right. eexists. right. done. }
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  change (Z.of_nat 0) with (Z0).
  iApply "Hcont". iFrame.
  iApply ("Cont" with "[-Hpto Hsim] [$Hpto Hsim]").
  2: { iSplit; first done. by iExists _. } 
  do 5 iExists _. iFrame. iSplitR "HSI_GC"; last iSplitL.
  - iExists _. iFrame. iPureIntro; split_and!; try done.
    rewrite dom_insert_L subseteq_union_1_L; first done.
    by eapply singleton_subseteq_l, elem_of_dom_2.
  - iApply HSI_GC_modify; try done. intros ?; inversion 1.
  - iPureIntro. split_and; last done. cbn. destruct Hζfuture as [Hf1 Hf2]; split.
    1: by rewrite !dom_insert_L Hf1.
    intros γ' b1 b2 [(Heq&H1)|(Hne&H1)]%lookup_insert_Some H2.
    + subst γ' b1. rewrite lookup_insert in H2. by simplify_eq.
    + eapply Hf2; try done. by rewrite lookup_insert_ne in H2.
Qed.

End Laws.
