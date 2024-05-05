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

Lemma alloc_foreign_correct e : |- wrap_prog e :: alloc_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ".
  SI_at_boundary. SI_GC_agree.
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ χC' ζC' θC' (aret:loc) mem',
      χC ρc !! γ = None ∧
      χC' = <[ γ := LlocPrivate ]> (χC ρc) ∧
      ζC' = <[ γ := Bforeign (Mut, None) ]> (ζC ρc) ∧
      GC_correct ζC' θC' ∧
      repr θC' roots_m privmem mem' ∧
      roots_are_live θC' roots_m ∧
      θC' !! γ = Some aret ∧
      e' = WrSE (ExprV (# aret)) ∧
      σ' = CState (WrapstateC χC' ζC' θC' (rootsC ρc)) mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & χC' & ζC' & θC' & aret & mem' &
                  HγNone & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  iMod (hgh_alloc_block with "GCHGH") as "(GCHGH & Hpto & Hfresh)"; first eassumption.
  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".

  do 3 iModIntro. iFrame.
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! θC' γ with "[-]"); try done.
  iFrame. iSplit; last by eauto.
  rewrite /GC /named.
  iExists _, _, σMLvirt, _, _. iFrame; eauto.
Qed.

End Laws.
