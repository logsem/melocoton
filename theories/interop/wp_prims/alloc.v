From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics basics_resources.
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

Lemma alloc_correct e : |- wrap_prog e :: alloc_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  pose (tg, repeat (Lint 0) (Z.to_nat sz)) as blk.
  iDestruct (ROOTS_valid with "GCROOTS HσC") as %(privmem & Hrepr).
  iDestruct (ROOTS_live with "GCROOTS") as %Hlive.
  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ χC' ζC' θC' (a:loc) mem',
    χC ρc !! γ = None ∧
    χC' = <[γ := LlocPrivate]> (χC ρc) ∧
    ζC' = <[γ := Bvblock (Mut, (tg, repeat (Lint 0) (Z.to_nat sz)))]> (ζC ρc) ∧
    GC_correct ζC' θC' ∧
    repr_mem θC' roots_m privmem mem' ∧
    roots_are_live θC' roots_m ∧
    θC' !! γ = Some a ∧
    e' = WrSE (ExprO (OVal #a)) ∧
    σ' = CState {| χC := χC'; ζC := ζC'; θC := θC'; rootsC := rootsC ρc |} mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & χC' & ζC' & θC' & a & mem' &
                  HγNone & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  iMod (hgh_alloc_block with "GCHGH") as "(GCHGH & Hpto & Hfresh)"; first eassumption.
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".
  iMod (ROOTS_update_θ _ _ _ _ mem mem' with "GCROOTS HσC") as "[GCROOTS HσC]"; [by eauto..|].

  do 3 iModIntro. iFrame. cbn -[wrap_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! θC' γ with "[-]"); try done.
  iFrame. iSplit; last by eauto.
  rewrite /GC /named.
  iExists _, _, σMLvirt, _. by iFrame.
Qed.

End Laws.
