From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.mlanguage Require Import weakestpre adequacy.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.language Require Import language weakestpre.
From transfinite.base_logic.lib Require Import satisfiable.
From iris.proofmode Require Import proofmode.
Import umrel.
Section BackwardsLiftedAdequacy.
  Existing Instance ordinals.ordI.
  Context {val : Type}.
  Context (Λ : language val).
  Context {Σ : gFunctors}.

  Context (Φpure : state Λ → val → Prop).
  Context (p : lang_prog Λ).
  Context (Ψ : protocol val Σ).
  Context (Φbi : val → iProp Σ).

  Notation step := (@lang.prim_step _ Λ p).
  Notation cfg := (prod (expr Λ) (state Λ)).

  Implicit Types σ : state Λ.
  Implicit Types v : val.
  Implicit Types e : expr Λ.
  Implicit Types X : cfg → Prop.

  Definition sideConds `{!invG Σ, !langG val Λ Σ} : iProp Σ := 
    □ (∀ σ v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure σ v⌝)
  ∗ □ (∀ f s vv, penv_proto ⟨p,Ψ⟩ f s vv -∗ False).
  Context `{!invPreG Σ}.

  Context (e : Λ.(expr)).
  Context (σ : Λ.(state)).

  Context (Halloc : ∀ `{!invG Σ}, Alloc (langG val Λ Σ) (λ H,
    sideConds ∗ state_interp σ ∗ WP e @ ⟨p,Ψ⟩ ; ⊤ {{Φbi}})%I True).

  Lemma mlang_to_lang_safe e' σ' Φ :
    @mlanguage.safe _ (lang_to_mlang Λ) p e' σ' Φ → safe p e' σ' Φ.
  Proof.
    rewrite /safe /mlanguage.safe /mlanguage.to_val; cbn.
    destruct (to_val e') eqn:Heq.
    - done.
    - intros (X&HX). inversion HX; simplify_eq.
      by eapply H2.
  Qed.

  Lemma lang_to_mlang_rtc e1 σ1 e' σ' :
    rtc_step p e1 σ1 e' σ' → star_AD step (e1, σ1) (λ x, x = (e',σ')).
  Proof.
    rewrite /star_AD /= /mrel /=.
    induction 1.
    - by eapply star_refl_AD.
    - eapply star_step_AD. intros Y HY.
      inversion HY; simplify_eq.
      exists (e',σ'). split; first by eapply H6.
      eapply IHrtc_step.
  Qed.

  Lemma mlang_to_lang_adequacy e' σ':
    rtc_step p e σ e' σ' → safe p e' σ' (Φpure σ').
  Proof using All.
    intros H%lang_to_mlang_rtc.
    eapply mlang_to_lang_safe.
    edestruct (@alloc_adequacy_safe _ (lang_to_mlang Λ) _ Φpure p Ψ Φbi _ e σ) as (ex&σx&Heq&HH).
    - intros HinvG. specialize (Halloc HinvG).
      intros Φ HT HΦ.
      destruct (Halloc Φ HT HΦ) as (Hlang&Halloc').
      exists (lang_to_mlang_mlangG Λ).
      eapply alloc_mono. 2: exact Halloc'.
      iIntros "($&($&($&HWP)))".
      by iApply wp_lang_to_mlang.
    - exact H.
    - cbn in Heq. simplify_eq. done.
  Qed.

End BackwardsLiftedAdequacy.