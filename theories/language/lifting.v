(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From melocoton.language Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{SI:indexT, !langG val Λ Σ, !invG Σ}.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types s : prog_environ Λ Σ.
Implicit Types o : outcome val.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : outcome val → iProp Σ.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_outcome e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (penv_prog s) e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜prim_step (penv_prog s) e1 σ1 e2 σ2⌝
      ={E}▷=∗^(1) |={E}=>
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. intros H. rewrite wp_unfold /wp_pre.
  iIntros "H %σ Hσ". iMod ("H" $! σ with "Hσ") as "[%H1 H2]". do 2 iRight.
  iModIntro. iSplitR; first done. iIntros "%σ' %e' %Hstep". iMod ("H2" $! e' σ' Hstep) as "H2". do 2 iModIntro.
  do 2 iMod "H2". iModIntro. iFrame.
Qed.


(** Derived lifting lemmas. *)


Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_outcome e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (penv_prog s) e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step (penv_prog s) e1 σ1 e2 σ2⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_outcome e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]". iModIntro.
  iIntros (e' σ' Hstep). do 3 iModIntro.
  iMod ("H" $! e' σ' Hstep) as "[H1 H2]". iModIntro.
  iFrame.
  destruct (to_outcome e') eqn:?; last by iExFalso.
  iApply wp_outcome; first done. iApply "H2".
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, reducible (penv_prog s) e1 σ1) →
  (∀ σ1 e2' σ2, prim_step (penv_prog s) e1 σ1 e2' σ2 →
    σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E]▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_fupd.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_outcome. }
  iIntros (σ1) "Hσ". iMod "H". iModIntro. iSplitR.
  { iPureIntro. destruct (Hsafe σ1) as (?&?&?Hsafe').
    destruct (Hstep _ _ _ Hsafe') as (->&->).  do 2 eexists. done. }
  iIntros (e' σ2 Hstep'). do 3 iModIntro. iMod "H".
  iModIntro.
  destruct (Hstep σ1 e' σ2 Hstep') as (He1 & He2). subst.
  iFrame.
Qed.

Lemma pure_exec_fill φ n p e1 e2 K : PureExec φ n p e1 e2 -> PureExec φ n p (fill K e1) (fill K e2).
Proof.
  intros H Hφ. specialize (H Hφ). induction H as [|n x y z [Hred Hdet] Hstep IH]; econstructor.
  - econstructor.
    + intros σ1. destruct (Hred σ1) as (e' & σ' & H). do 2 eexists.
      apply prim_step_fill, H.
    + intros σ1 e2 σ2 HH. apply fill_step_inv in HH as (?&?&HH).
      2: { destruct (Hred σ1) as (?&?&?). by eapply outcome_stuck. }
      apply Hdet in HH as (-> & ->). done.
  - apply IH.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n (penv_prog s) e1 e2 →
  φ →
  (|={E}[E]▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { by iApply "Hwp". }
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_outcome.
  - done.
  - iApply (step_fupd_wand with "Hwp").
    iApply "IH".
Qed.


Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n (penv_prog s) e1 e2 →
  φ →
  ▷^n (WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by apply Hwp. iIntros (?).
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
