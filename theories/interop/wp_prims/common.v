From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export prims weakestpre.
From melocoton.mlanguage Require Import weakestpre.
Import Wrap.

Ltac SI_at_boundary :=
  iDestruct (SI_at_boundary_is_in_C with "Hσ Hb") as %(ρc & mem & ->);
  iNamed "Hσ"; iNamed "SIC".

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma wp_wrap_call E p Ψ pname prm ws Φ :
  p !! pname = Some prm →
  WP WrSE (RunPrimitive prm ws) @ ⟪p, Ψ⟫; E {{ Φ }} -∗
  WP to_call wrap_lang pname ws @ ⟪p, Ψ⟫; E {{ Φ }}.
Proof.
  iIntros (Hprm) "HWP".
  iApply weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[prims_prog at_boundary].
  iModIntro. iRight. iRight.
  iSplit; first done.
  iExists (λ '(e', σ'), e' = WrSE (RunPrimitive prm ws) ∧
                        σ' = σ).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? (-> & ->)). iModIntro. iNext. iModIntro.
  iFrame "Hσ". done.
Qed.

Lemma wp_pre_cases_c_prim p T wp prm ρc mem E ws Φ :
  prm ≠ Pcallback →
  (∀ e, prm ≠ Pmain e) →
  (∃ X,
    ⌜c_prim_step prm ws ρc mem (λ w ρc' mem', X (WrSE (ExprV w), CState ρc' mem'))⌝ ∗
    (∀ w ρc' mem',
       ⌜X (WrSE (ExprV w), CState ρc' mem')⌝ ={E}▷=∗
       weakestpre.state_interp (CState ρc' mem') ∗
       wp E (WrSE (ExprV w)) Φ)) -∗
  |={E}=> wp_pre_cases p T wp (CState ρc mem) E
    (WrSE (RunPrimitive prm ws))
    Φ.
Proof using.
  iIntros (Hncb Hnmain) "HWP".
  iModIntro. iRight. iRight.
  iSplit; first done.
  iDestruct "HWP" as (X Hpstep) "HWP".
  iExists (λ '(e', σ'), X (e', σ') ∧ ∃ w ρc' mem',
            e' = WrSE (ExprV w) ∧ σ' = CState ρc' mem').
  iSplit.
  { iPureIntro. econstructor.
    eapply c_prim_step_covariant_in_Y; naive_solver. }
  iIntros (? ? (HX & ? & ? & ? & (-> & ->))).
  iMod ("HWP" $! _ _ _ HX) as "HWP". do 2 iModIntro.
  iMod "HWP" as "(Hσ & HWP)". by iFrame.
Qed.

End Laws.
