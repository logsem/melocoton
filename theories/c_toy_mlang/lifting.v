(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From melocoton.c_toy_mlang Require Export weakestpre.
From iris.prelude Require Import options.
From melocoton Require Import multirelations.

Section lifting.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types p : gmap string (func Λ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step_fupdN p E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns,
     state_interp σ1 ns ={E,∅}=∗
       ⌜reducible p e1 σ1⌝ ∗
       ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗
         £ (S (num_laters_per_step ns))
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         ∃ e2 σ2,
           ⌜φ (e2, σ2)⌝ ∗
           state_interp σ2 (S ns) ∗
           WP e2 @ p; E {{ Φ }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof. by rewrite wp_unfold /wp_pre=>->. Qed.

Lemma wp_lift_step_fupd p E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns,
     state_interp σ1 ns ={E,∅}=∗
       ⌜reducible p e1 σ1⌝ ∗
       ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗
         £ 1 ={∅}=∗ ▷ |={∅,E}=>
         ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗ state_interp σ2 (S ns) ∗
           WP e2 @ p; E {{ Φ }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "Hwp". rewrite -wp_lift_step_fupdN; [|done].
  iIntros (??) "Hσ". iMod ("Hwp" with "Hσ") as "($ & Hwp)".
  iIntros "!>" (??) "Hcred".
  iPoseProof (lc_weaken 1 with "Hcred") as "Hcred"; first lia.
  simpl. rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro.
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iApply step_fupd_intro; done.
Qed.

(*
Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 ns κ κs nt) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.
*)

(** Derived lifting lemmas. *)

Lemma wp_lift_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns,
     state_interp σ1 ns ={E,∅}=∗
       ⌜reducible p e1 σ1⌝ ∗
       ▷ ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗
         £ 1 ={∅,E}=∗
         ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗ state_interp σ2 (S ns) ∗
           WP e2 @ p; E {{ Φ }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (??) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % Hcred !> !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} p E E' Φ e1 (e2s : _ → Prop) :
  (∀ σ1, reducible p e1 σ1) →
  (∀ σ1 φ, rel (prim_step p) (e1, σ1) φ → ∀ e2, e2s e2 → φ (e2, σ1)) →
  (|={E}[E']▷=> £ 1 -∗ ∃ e2, ⌜e2s e2⌝ ∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
  iIntros (σ1 ns) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. done. }
  iNext. iIntros (φ Hstep') "Hcred".
  specialize (Hstep _ _ Hstep').
  iMod (state_interp_mono with "Hσ") as "Hσ".
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "Hcred") as (??) "Hwp".
  iExists _, _. iFrame. eauto.
Qed.

(*
Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.
*)

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {p E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E1}=∗
    ⌜reducible p e1 σ1⌝ ∗
    ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗ £ 1 ={E1}[E2]▷=∗
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (S ns) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ p; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd p E1 _ e1)=>//; iIntros (σ1 ns) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (φ ?) "Hcred". iMod "Hclose" as "_".
  iMod ("H" $! φ with "[#] Hcred") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as (e2 σ2 ?) "(Hσ & HQ)".
  iModIntro. iExists _, _. iSplit; eauto. iFrame.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E}=∗
    ⌜reducible p e1 σ1⌝ ∗
    ▷ ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗ £ 1 ={E}=∗
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (S ns) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (??) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "Hcred !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {p E E' Φ} e1 e2 :
  (∀ σ1, reducible p e1 σ1) →
  (∀ σ1 φ, rel (prim_step p) (e1, σ1) φ → φ (e2, σ1)) →
  (|={E}[E']▷=> £ 1 -∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step p E E' _ _ (λ e, e = e2)); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H ?".
  iExists e2. iSplit; eauto. by iApply "H".
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} p E E' e1 e2 φ n Φ :
  PureExec φ n p e1 e2 →
  φ →
  (|={E}[E']▷=>^n £ n -∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { iMod lc_zero as "Hz". by iApply "Hwp". }
  iApply (wp_lift_pure_det_step _ e2); eauto.
  iApply (step_fupd_wand with "Hwp").
  iIntros "Hwp Hone". iApply "IH".
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp Hc". iApply ("Hwp" with "[Hone Hc]").
  rewrite (lc_succ n). iFrame.
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} p E e1 e2 φ n Φ :
  PureExec φ n p e1 e2 →
  φ →
  ▷^n (£ n -∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by apply Hwp. iIntros (?).
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.

(***** now: lemmas corresponding to those from ectx_lifting *****)

Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.

Lemma wp_lift_head_step_fupd {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E,∅}=∗
    ⌜head_reducible p e1 σ1⌝ ∗
    ∀ φ, ⌜rel (head_step p) (e1, σ1) φ⌝ -∗
      £ 1 ={∅}=∗ ▷ |={∅,E}=>
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗ state_interp σ2 (S ns) ∗
      WP e2 @ p; E {{ Φ }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iIntros (σ1 ns) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by eauto. iIntros (φ ?).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_head_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E,∅}=∗
    ⌜head_reducible p e1 σ1⌝ ∗
    ▷ ∀ φ, ⌜rel (head_step p) (e1, σ1) φ⌝ -∗
      £ 1 ={∅,E}=∗
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗ state_interp σ2 (S ns) ∗
      WP e2 @ p; E {{ Φ }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_head_step_fupd; [done|]. iIntros (??) "Hσ".
  iMod ("H" with "[$]") as "[$ H]". iIntros "!>" (φ ?) "Hcred !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_atomic_head_step_fupd {p E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E1}=∗
    ⌜head_reducible p e1 σ1⌝ ∗
    ∀ φ, ⌜rel (head_step p) (e1, σ1) φ⌝ -∗ £ 1 ={E1}[E2]▷=∗
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (S ns) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ p; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 ns) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by auto. iIntros (φ Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns, state_interp σ1 ns ={E}=∗
    ⌜head_reducible p e1 σ1⌝ ∗
    ▷ ∀ φ, ⌜rel (head_step p) (e1, σ1) φ⌝ -∗ £ 1 ={E}=∗
      ∃ e2 σ2, ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (S ns) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 ns) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by auto. iNext. iIntros (φ Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_det_head_step `{!Inhabited (state Λ)} {p E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible p e1 σ1) →
  (∀ σ1 φ,
    rel (head_step p) (e1, σ1) φ → φ (e2, σ1)) →
  (|={E}[E']▷=> £ 1 -∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  intros * ? ? HH. rewrite -(wp_lift_pure_det_step e1 e2); eauto.
  intros. eapply HH; eauto.
Qed.

Lemma wp_lift_pure_det_head_step' `{!Inhabited (state Λ)} {p E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible p e1 σ1) →
  (∀ σ1 φ,
    rel (head_step p) (e1, σ1) φ → φ (e2, σ1)) →
  ▷ (£ 1 -∗ WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  intros. rewrite -[(WP e1 @ p; _ {{ _ }})%I]wp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.

End lifting.
