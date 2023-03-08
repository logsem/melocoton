(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From melocoton.mlanguage Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!invGS_gen hlc Σ, !mlangGS val Σ Λ}.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ Λ Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types X : expr Λ * state Λ → Prop.

Lemma wp_lift_step_fupd pe E Φ e1 :
  to_val e1 = None →
  not_is_ext_call (penv_prog pe) e1 →
  (∀ σ1, state_interp σ1 ={E}=∗
    ∃ X, ⌜prim_step (penv_prog pe) (e1, σ1) X⌝ ∗ |={E}▷=>
      ∀ e2 σ2,
        ⌜X (e2, σ2)⌝ -∗ state_interp σ2 ∗ WP e2 @ pe; E {{ Φ }})
  ⊢ WP e1 @ pe; E {{ Φ }}.
Proof. intros Hval Hcall. rewrite wp_unfold /wp_pre.
  iIntros "H %σ Hσ". iMod ("H" $! σ with "Hσ") as (? ?) "H2". iModIntro. do 2 iRight.
  iSplitR; first done. iExists _.
  iSplitR; first done.
  iIntros (? ? HX). iMod "H2". do 2 iModIntro. iMod "H2".
  iModIntro. iSpecialize ("H2" $! _ _ HX). iFrame.
Qed.


(** Derived lifting lemmas. *)


Lemma wp_lift_atomic_step {pe E Φ} e1 :
  to_val e1 = None →
  not_is_ext_call (penv_prog pe) e1 →
  (∀ σ1, state_interp σ1 ={E}=∗
    ∃ X, ⌜prim_step (penv_prog pe) (e1, σ1) X⌝ ∗ |={E}▷=>
      ∀ e2 σ2, ⌜X (e2, σ2)⌝ -∗
        state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (Hnv Hnc) "H".
  iApply (wp_lift_step_fupd pe E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as (X Hstep) ">H". iModIntro.
  iExists _. iSplit; first done. do 2 iModIntro.
  iMod "H". iIntros "!>" (? ? HX).
  iDestruct ("H" $! _ _ HX) as "[? ?]". iFrame.
  destruct (to_val e2) eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {pe E Φ} e1 e2 :
  (to_val e1 = None) →
  (∀ σ1, prim_step (penv_prog pe) (e1, σ1) (λ '(e', σ'), e' = e2 ∧ σ' = σ1)) →
  (|={E}[E]▷=> WP e2 @ pe; E {{ Φ }}) ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_fupd; first done.
  { intros (f&vs&C&H1&H2). specialize (Hstep inhabitant).
    eapply call_prim_step in Hstep as (?&?&?&?&?&?); eauto.
    simplify_eq. }
  iIntros (σ1) "Hσ". iMod "H". iModIntro.
  iExists _. iSplit; first done.
  do 2 iModIntro. iMod "H".
  iModIntro. iIntros (? ? (-> & ->)). iFrame.
Qed.

End lifting.
