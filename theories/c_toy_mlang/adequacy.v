From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From melocoton.language Require Import mlanguage.
From melocoton.c_toy_mlang Require Import weakestpre.
From melocoton Require Import multirelations.

Section adequacy.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types φ : expr Λ * state Λ → Prop.

Lemma wp_step p e1 σ1 ns φ Φ :
  rel (prim_step p) (e1, σ1) φ →
  state_interp σ1 ns -∗
  £ (S (num_laters_per_step ns)) -∗
  WP e1 @ p; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
    ∃ e2 σ2,
      ⌜φ (e2, σ2)⌝ ∗ state_interp σ2 (S ns) ∗ WP e2 @ p; ⊤ {{ Φ }}.
Proof using.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ Hcred H".
  rewrite (val_stuck p e1 σ1 φ) //.
  iMod ("H" $! σ1 ns with "Hσ") as "(_ & H)". iModIntro.
  iApply (step_fupdN_wand with "(H [//] Hcred)"). iIntros ">H".
  iDestruct "H" as (e2 σ2 Hφ) "(? & ?)". by eauto with iFrame.
Qed.

Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Lemma wp_steps p n e1 σ1 ns φ Φ :
  rel (repeat (prim_step p) n) (e1, σ1) φ →
  state_interp σ1 ns -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  WP e1 @ p; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=>
    ∃ e2 σ2,
      ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (n + ns) ∗
      WP e2 @ p; ⊤ {{ Φ }}.
Proof using.
  revert e1 σ1 ns φ Φ.
  induction n as [|n IH]=> e1 σ1 ns φ Φ /=.
  { unfold id, rel; cbn. iIntros (Hφ) "Hσ ? Hwp".
    iApply fupd_mask_intro. done. iIntros "H"; iMod "H".
    iModIntro. iExists e1, σ1. eauto with iFrame. }
  iIntros (Hsteps) "Hσ Hcred He".
  rewrite unfold_seq in Hsteps.
  destruct Hsteps as (φ' & Hstep1 & Hstep2).
  rewrite Nat.iter_add -{1}plus_Sn_m plus_n_Sm.
  rewrite lc_split. iDestruct "Hcred" as "[Hc1 Hc2]".
  iDestruct (wp_step with "Hσ Hc1 He") as ">H"; first eauto.
  iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "H").
  iIntros ">H". iDestruct "H" as (e2 σ2 Hφ) "(Hσ & He)".
  iMod (IH with "Hσ Hc2 He") as "IH"; first eauto. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as (e3 σ3 Hφ') "[??]".
  by eauto with iFrame.
Qed.

Local Lemma wp_strong_adequacy_internal p n e1 σ1 ns φ Φ :
  rel (repeat (prim_step p) n) (e1, σ1) φ →
  state_interp σ1 ns -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  WP e1 @ p; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=>
    ∃ e2 σ2,
      ⌜φ (e2, σ2)⌝ ∗
      state_interp σ2 (n + ns) ∗
      from_option Φ True (to_val e2).
Proof using.
  iIntros (Hstep) "Hσ Hcred He". iMod (wp_steps with "Hσ Hcred He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (? ? ?) "(Hσ & He)".
  destruct (to_val e2) as [v2|] eqn:He2.
  { apply of_to_val in He2 as <-. simpl. rewrite wp_value_fupd'.
    iMod "He". iModIntro. iExists _, _. iFrame. iSplit; eauto.
    rewrite to_of_val //. }
  { iModIntro. iExists _, _. iFrame. iSplit; eauto. rewrite He2//. }
Qed.
End adequacy.

Lemma wp_strong_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} p e1 σ1 n φ P
        (num_laters_per_step : nat → nat) :
  (∀ `{Hinv : !invGS_gen hlc Σ},
     ⊢ |={⊤}=> ∃
        (stateI : state Λ → nat → iProp Σ)
        (Φ : val Λ → iProp Σ)
        state_interp_mono,
     let _ : irisGS_gen hlc Λ Σ := IrisG Hinv stateI num_laters_per_step state_interp_mono in
     stateI σ1 0 ∗
     WP e1 @ p; ⊤ {{ Φ }} ∗
     (∀ e2 σ2,
        ⌜φ (e2, σ2)⌝ -∗
        stateI σ2 n -∗
        from_option Φ True (to_val e2) -∗
        |={⊤,∅}=> ⌜ P ⌝)) →
  rel (repeat (prim_step p) n) (e1, σ1) φ →
  P.
Proof.
  iIntros (Hwp ?).
  eapply (step_fupdN_soundness_gen _ hlc (steps_sum num_laters_per_step 0 n)
    (steps_sum num_laters_per_step 0 n)).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (stateI Φ state_interp_mono) "(Hσ & Hwp & HP)".
  iMod (@wp_strong_adequacy_internal _ _ _
        (IrisG Hinv stateI num_laters_per_step state_interp_mono)
    with "[Hσ] Hcred Hwp") as "H"; [done|done|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜P⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (e2 σ2 Hφ) "(Hσ & Hval) /=".
  rewrite -plus_n_O.
  by iApply ("HP" with "[//] Hσ").
Qed.

(** Adequacy when using later credits (the default) *)
Definition wp_strong_adequacy := wp_strong_adequacy_gen HasLc.
Global Arguments wp_strong_adequacy _ _ {_}.

Definition adequate {Λ} (p : program Λ) (e1 : expr Λ) (σ1 : state Λ)
    (P : val Λ → state Λ → Prop) :=
  ∀ φ, rel (star (prim_step p)) (e1, σ1) φ →
       ∃ e2 σ2,
         φ (e2, σ2) ∧
         (∀ v2, to_val e2 = Some v2 → P v2 σ2).
(* and recall that [∀ e2 σ2, not_stuck p e2 σ2] *)

Lemma wp_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} p e σ P :
  (∀ `{Hinv : !invGS_gen hlc Σ},
     ⊢ |={⊤}=> ∃ (stateI : state Λ → iProp Σ),
       let _ : irisGS_gen hlc Λ Σ :=
           IrisG Hinv (λ σ _, stateI σ) (λ _, 0)
                 (λ _ _, fupd_intro _ _)
       in
       stateI σ ∗ WP e @ p; ⊤ {{ v, ⌜P v⌝ }}) →
  adequate p e σ (λ v _, P v).
Proof.
  intros Hwp. intros φ. rewrite /rel /star /=.
  intros [n Hsteps].
  eapply (wp_strong_adequacy_gen hlc Σ _); [ | done]=> ?.
  iMod Hwp as (stateI) "[Hσ Hwp]".
  iExists (λ σ _, stateI σ), (λ v, ⌜P v⌝%I), _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 σ2 Hφ) "H Hv".
  iApply fupd_mask_intro_discard; [done|].
  iExists _, _. iSplit; eauto. iIntros (? ->). done.
Qed.

(** Instance for using credits *)
Definition wp_adequacy := wp_adequacy_gen HasLc.
Global Arguments wp_adequacy _ _ {_}.
