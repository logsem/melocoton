(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From melocoton.mlanguage Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!invGS_gen hlc Σ, !publicStateInterp pubstate Σ, !mlangGS hlc val pubstate Σ Λ}.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types s : prog_environ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types X : expr Λ * state Λ → Prop.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ∗ ⌜matching_expr_state e1 σ1⌝ ={E}=∗
    ⌜reducible (prog s) e1 σ1⌝ ∗
    ∀ X, ⌜prim_step (prog s) (e1, σ1) X⌝ ={E}▷=∗^(1) |={E}=>
      ∃ e2 σ2,
        ⌜X (e2, σ2)⌝ ∗ state_interp σ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. intros H. rewrite wp_unfold /wp_pre.
  iIntros "H %σ Hσ". iMod ("H" $! σ with "Hσ") as "[H1 H2]". iModIntro. do 2 iRight.
  iFrame. iIntros (X Hstep). iMod ("H2" $! X Hstep) as "H2". do 2 iModIntro.
  do 2 iMod "H2". iModIntro. iFrame.
Qed.


(** Derived lifting lemmas. *)


Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ∗ ⌜matching_expr_state e1 σ1⌝ ={E}=∗
    ⌜reducible (prog s) e1 σ1⌝ ∗
    ▷ ∀ X, ⌜prim_step (prog s) (e1, σ1) X⌝ ={E}=∗
      ∃ e2 σ2, ⌜X (e2, σ2)⌝ ∗
        state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]". iModIntro.
  iIntros (X Hstep). do 3 iModIntro.
  iMod ("H" $! X Hstep) as (e' σ' HX) "[? ?]". iModIntro.
  iExists _, _. iSplitR; first done. iFrame.
  destruct (to_val e') eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ∗ ⌜matching_expr_state e1 σ1⌝ ={E}=∗
    ⌜head_reducible (prog s) e1 σ1⌝ ∗
    ▷ ∀ X, ⌜head_step (prog s) (e1, σ1) X⌝ ={E}=∗
      ∃ e2 σ2, ⌜X (e2, σ2)⌝ ∗
        state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[%HH H]". iModIntro. iSplitR; first (iPureIntro; by eapply head_prim_reducible).
  iIntros (X Hstep%head_reducible_prim_step). 2:easy. do 3 iModIntro.
  iMod ("H" $! X Hstep) as (e' σ' HX) "[H1 H2]". iModIntro.
  iExists _, _. iSplitR; first done. iFrame.
  destruct (to_val e') eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, reducible (prog s) e1 σ1) →
  (∀ σ1 X, matching_expr_state e1 σ1 →
    prim_step (prog s) (e1, σ1) X →
    X (e2, σ1)) →
  (|={E}[E]▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_fupd.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1) "[Hσ %Hmatch]". iMod "H". iModIntro.
  iSplitR; first (iPureIntro; apply Hsafe).
  iIntros (X Hstep'). do 3 iModIntro. iMod "H".
  iModIntro. iExists e2, _. iSplitR.
  { iPureIntro. eapply Hstep; eauto. }
  iFrame.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n (prog s) e1 e2 →
  φ →
  (|={E}[E]▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { iMod lc_zero as "Hz". by iApply "Hwp". }
  iApply wp_lift_pure_det_step.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - intros. eapply pure_step_det; eauto.
  - iApply (step_fupd_wand with "Hwp"). iApply "IH".
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n (prog s) e1 e2 →
  φ →
  ▷^n (WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by apply Hwp. iIntros (?).
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.

End lifting.
