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
  iIntros "%σ Hσ". cbn -[wrap_prog at_boundary].
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

Lemma HSI_GC_acc ζ θ roots χ γ w m tg vs i vv :
  repr_lval θ (Lloc γ) w
→ ζ !! γ = Some (Bvblock (m, (tg, vs)))
→ vs !! i = Some vv
→ SI_GC ζ θ roots χ
⊢ ⌜∃ ww, repr_lval θ vv ww⌝.
Proof.
  iIntros (H1 H2 H3) "H4". iNamed "H4".
  destruct HGCOK as (HGCL&Hdom&HGCR). inv_repr_lval.
  destruct vv as [vvz|vvl]; first (iExists _; iPureIntro; econstructor).
  eapply elem_of_dom in HGCR as [w' Hw']; first (iExists _; iPureIntro; econstructor).
  1: eapply Hw'. 1: eapply elem_of_dom_2, H4. 1: done.
  constructor; by eapply elem_of_list_lookup_2.
Qed.

Lemma HSI_GC_modify ζ θ χ roots γ blk':
  (∀ γ', lval_in_block blk' (Lloc γ') → γ' ∈ dom θ ∨ ∃ blk, ζ !! γ = Some blk ∧ lval_in_block blk (Lloc γ')) →
  SI_GC ζ θ roots χ
⊢ SI_GC (<[ γ := blk' ]> ζ) θ roots χ.
Proof.
  iIntros (H) "H". iNamed "H".
  iExists roots_m. iFrame. iPureIntro; split_and!; try done.
  destruct HGCOK as (HL&Hdom&HR); split_and!; [done..|].
  intros γ1 blk γ2 Hγ1 [(Heq&Hlu)|(Hne&Hlu)]%lookup_insert_Some H2; simplify_eq.
  2: by eapply HR.
  destruct (H _ H2) as [Hl|(blk1&Hblk&Hr)]; first done.
  apply (HR _ _ _ Hγ1 Hblk Hr).
Qed.


End Laws.
