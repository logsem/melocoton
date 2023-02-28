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
  (∀ σ1, state_interp σ1 ={E}=∗
    ∀ X, ⌜prim_step (penv_prog pe) (e1, σ1) X⌝ ={E}▷=∗^(1) |={E}=>
      ∃ e2 σ2,
        ⌜X (e2, σ2)⌝ ∗ state_interp σ2 ∗ WP e2 @ pe; E {{ Φ }})
  ⊢ WP e1 @ pe; E {{ Φ }}.
Proof. intros H. rewrite wp_unfold /wp_pre.
  iIntros "H %σ Hσ". iMod ("H" $! σ with "Hσ") as "H2". iModIntro. do 2 iRight.
  iSplitR; first done.
  iIntros (X Hstep). iMod ("H2" $! X Hstep) as "H2". do 2 iModIntro.
  do 2 iMod "H2". iModIntro. iFrame.
Qed.


(** Derived lifting lemmas. *)


Lemma wp_lift_atomic_step {pe E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ▷ ∀ X, ⌜prim_step (penv_prog pe) (e1, σ1) X⌝ ={E}=∗
      ∃ e2 σ2, ⌜X (e2, σ2)⌝ ∗
        state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd pe E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "H". iModIntro.
  iIntros (X Hstep). do 3 iModIntro.
  iMod ("H" $! X Hstep) as (e' σ' HX) "[? ?]". iModIntro.
  iExists _, _. iSplitR; first done. iFrame.
  destruct (to_val e') eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_atomic_head_step {pe E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜(∃ X, head_step (penv_prog pe) (e1, σ1) X)⌝ ∗
    ▷ ∀ X, ⌜head_step (penv_prog pe) (e1, σ1) X⌝ ={E}=∗
      ∃ e2 σ2, ⌜X (e2, σ2)⌝ ∗
        state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd pe E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[(%X'&%HH) H]". iModIntro.
  iIntros (X Hstep). eapply head_reducible_prim_step in Hstep. 2:apply HH. do 3 iModIntro.
  iMod ("H" $! X Hstep) as (e' σ' HX) "[H1 H2]". iModIntro.
  iExists _, _. iSplitR; first done. iFrame.
  destruct (to_val e') eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {pe E Φ} e1 e2 :
  (to_val e1 = None) →
  (∀ σ1 X,
    prim_step (penv_prog pe) (e1, σ1) X →
    X (e2, σ1)) →
  (|={E}[E]▷=> WP e2 @ pe; E {{ Φ }}) ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_fupd; first done.
  iIntros (σ1) "Hσ". iMod "H". iModIntro.
  iIntros (X Hstep'). do 3 iModIntro. iMod "H".
  iModIntro. iExists e2, _. iSplitR.
  { iPureIntro. eapply Hstep; eauto. }
  iFrame.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} pe E e1 e2 φ n Φ :
  PureExec φ n (penv_prog pe) e1 e2 →
  φ →
  (|={E}[E]▷=>^n WP e2 @ pe; E {{ Φ }}) ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { iMod lc_zero as "Hz". by iApply "Hwp". }
  iApply wp_lift_pure_det_step.
  - done.
  - intros. eapply pure_step_det; eauto.
  - iApply (step_fupd_wand with "Hwp"). iApply "IH".
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} pe E e1 e2 φ n Φ :
  PureExec φ n (penv_prog pe) e1 e2 →
  φ →
  ▷^n (WP e2 @ pe; E {{ Φ }}) ⊢ WP e1 @ pe; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by apply Hwp. iIntros (?).
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.

End lifting.
