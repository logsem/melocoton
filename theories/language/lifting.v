(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From melocoton.language Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS_gen hlc val pubstate Λ Σ}.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types s : prog_environ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E}=∗
    ⌜reducible (prog s) e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜prim_step (prog s) e1 σ1 e2 σ2 []⌝
      ={E}▷=∗^(1) |={E}=>
      state_interp σ2 (S ns) ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. intros H. rewrite wp_unfold /wp_pre.
  iIntros "H %σ %ns Hσ". iMod ("H" $! σ ns with "Hσ") as "[H1 H2]". iModIntro. do 2 iRight.
  iFrame. iIntros "%σ' %e' %Hstep". iMod ("H2" $! e' σ' Hstep) as "H2". do 2 iModIntro.
  do 2 iMod "H2". iModIntro. iFrame.
Qed.


(** Derived lifting lemmas. *)


Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E}=∗
    ⌜reducible (prog s) e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step (prog s) e1 σ1 e2 σ2 []⌝ -∗
      state_interp σ2 (S ns) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1 ns) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]". iModIntro.
  iIntros (e' σ' Hstep). do 4 iModIntro.
  iDestruct ("H" $! e' σ' Hstep) as "[H1 H2]".
  iFrame.
  destruct (to_val e') eqn:?; last by iExFalso.
  iApply wp_value; first done. iApply "H2".
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, reducible (prog s) e1 σ1) →
  (∀ σ1 e2' σ2 efs', prim_step (prog s) e1 σ1 e2' σ2 efs' →
    σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E]▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_fupd.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 ns) "Hσ". iMod "H". iModIntro. iSplitR; first (iPureIntro; apply Hsafe).
  iIntros (e' σ2 Hstep'). do 3 iModIntro. iMod "H".
  iMod (state_interp_mono σ1 ns with "Hσ") as "Hs".
  iModIntro.
  destruct (Hstep σ1 e' σ2 [] Hstep') as (He1 & He2 & He3). subst.
  iFrame.
Qed.

  Record pure_step (p : language.prog Λ) (e1 e2 : expr Λ) := {
    pure_step_safe σ1 : reducible p e1 σ1;
    pure_step_det σ1 e2' σ2 efs :
      prim_step p e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

Class PureExec (φ : Prop) (n : nat)  (p : language.prog Λ) (e1 e2 : expr Λ) :=
  pure_exec : φ → relations.nsteps (pure_step p) n e1 e2.


Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n (prog s) e1 e2 →
  φ →
  (|={E}[E]▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { iMod lc_zero as "Hz". by iApply "Hwp". }
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - iApply (step_fupd_wand with "Hwp").
    iApply "IH".
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
