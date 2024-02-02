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

Lemma alloc_correct e : |- wrap_prog e :: alloc_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  pose (tg, repeat (Lint 0) (Z.to_nat sz)) as blk.
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ χC' ζC' θC' (a:loc) mem',
    χC ρc !! γ = None ∧
    χC' = <[γ := LlocPrivate]> (χC ρc) ∧
    ζC' = <[γ := Bvblock (Mut, (tg, repeat (Lint 0) (Z.to_nat sz)))]> (ζC ρc) ∧
    GC_correct ζC' θC' ∧
    repr θC' roots_m privmem mem' ∧
    roots_are_live θC' roots_m ∧
    θC' !! γ = Some a ∧
    e' = WrSE (ExprV #a) ∧
    σ' = CState {| χC := χC'; ζC := ζC'; θC := θC'; rootsC := rootsC ρc |} mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & χC' & ζC' & θC' & a & mem' &
                  HγNone & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  iMod (hgh_alloc_block with "GCHGH") as "(GCHGH & Hpto & Hfresh)"; first eassumption.
  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".

  do 3 iModIntro. iFrame. cbn -[wrap_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! θC' γ with "[-Hpto Hfresh] [Hpto Hfresh] []"); try done.
  3: iPureIntro; by econstructor.
  2: iFrame; done.
  rewrite /GC /named.
  iExists _, _, σMLvirt, _, _. iFrame. iPureIntro; split_and!; eauto.
Qed.

End Laws.
