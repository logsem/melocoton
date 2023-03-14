From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.mlanguage Require Export mlanguage.
From melocoton Require Import multirelations.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

(* State interpretation for a [mlanguage]:
   - parameterized by the state interpretation for the public state;
   - the data of a state interp predicate for the whole state and a state
     interp for the private state;
   - with the property that splitting/joining the state allows splitting/joining
     the state interpretations accordingly.
*)
Class mlangG {SI:indexT} (val : Type) (Σ : gFunctors) (Λ : mlanguage val) :=
MlangG {
  state_interp : state Λ → iProp Σ;
  at_boundary : iProp Σ;
}.

Arguments at_boundary {_ _ _} Λ {_}.

Definition wp_pre_cases `{SI:indexT, !invG Σ, !mlangG val Σ Λ}
    (p : mixin_prog Λ.(func))
    (T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ)
    (wp : coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ) :
    state Λ -d> coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ := λ σ E e Φ,
  (
      (∃ v, ⌜e = of_val Λ v⌝ ∗ state_interp σ ∗ Φ v)
    ∨ (∃ f vs C, ⌜is_call e f vs C⌝ ∗ ⌜p !! f = None⌝ ∗
       at_boundary Λ ∗ state_interp σ ∗
       ∃ Ξ, T f vs Ξ ∗ ▷ ∀ r, Ξ r ∗ at_boundary Λ -∗ wp E (resume_with C (of_val Λ r)) Φ)
    ∨ (⌜to_val e = None⌝ ∗
       ∃ X, ⌜prim_step p (e, σ) X⌝ ∗
       ∀ e' σ', ⌜X (e', σ')⌝ ={E}▷=∗ state_interp σ' ∗ wp E e' Φ)
  )%I.

Definition wp_pre `{SI:indexT, !invG Σ, !mlangG val Σ Λ}
    (p : mixin_prog Λ.(func))
    (T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ)
    (wp : coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e Φ,
  (∀ σ, state_interp σ ={E}=∗ wp_pre_cases p T wp σ E e Φ)%I.

Local Instance wp_pre_contractive
      `{SI:indexT, !invG Σ, !mlangG val Σ Λ}
      {p:mixin_prog Λ.(func)} T :
  Contractive (wp_pre p T).
Proof.
  rewrite /wp_pre /wp_pre_cases /= => n wp wp' Hwp E e1 Φ. cbn in Hwp.
  repeat (f_contractive || f_equiv || apply Hwp || intros ?).
Qed.

Record prog_environ {SI:indexT} {val} (Λ : mlanguage val) Σ := Penv {
  penv_prog : gmap string Λ.(func);
  penv_proto : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ;
}.
Global Arguments penv_prog {_ _ _ _} _.
Global Arguments penv_proto {_ _ _ _} _.

Local Definition wp_def
      `{SI:indexT, !invG Σ, !mlangG val Σ Λ} :
  Wp (iProp Σ) (expr Λ) (val) (prog_environ Λ Σ) :=
  λ p : (prog_environ Λ Σ), fixpoint (wp_pre p.(penv_prog) p.(penv_proto)).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {SI Σ _ val Λ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{SI:indexT, !invG Σ, !mlangG val Σ Λ} :
  wp = @wp_def SI Σ _ val Λ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{SI:indexT, !invG Σ, !mlangG val Σ Λ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ Λ Σ.
Implicit Types X : expr Λ * state Λ → Prop.

(* Weakest pre *)
Lemma wp_unfold pe E e Φ :
  WP e @ pe; E {{ Φ }} ⊣⊢ wp_pre pe.(penv_prog) pe.(penv_proto) (wp (PROP:=iProp Σ) pe) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre pe.(penv_prog) pe.(penv_proto))). Qed.

Global Instance wp_ne pe E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) pe E e).
Proof.
  revert e. induction (index_lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /wp_pre_cases /=.
  do 16 f_equiv. 1: do 3 f_equiv.
  all: f_contractive.
  1: do 1 f_equiv.
  1: intros r; f_equiv.
  2: do 2 f_equiv.
  all: apply IH; eauto; intros k; eapply dist_le', HΦ; eauto.
  all: by eapply index_lt_le_subrel.
Qed.
Global Instance wp_proper pe E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) pe E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value_fupd' pe E Φ v : (|={E}=> Φ v)%I ⊢ WP ( of_val Λ v) @ pe; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ Hσ". iLeft. iMod "H". iModIntro. iExists _; iFrame; done.
Qed.

Definition prog_environ_mono pe1 pe2 : Prop :=
   penv_prog pe1 = penv_prog pe2 ∧ ∀ f vs Φ, penv_proto pe1 f vs Φ -∗ penv_proto pe2 f vs Φ.

Lemma prog_environ_mono_refl : Reflexive (prog_environ_mono).
Proof. intros s; split; eauto. Qed.
#[local] Hint Resolve prog_environ_mono_refl : core.

Lemma wp_strong_mono pe1 pe2 E1 E2 e Φ Ψ :
  E1 ⊆ E2 → prog_environ_mono pe1 pe2 →
  WP e @ pe1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ pe2; E2 {{ Ψ }}.
Proof.
  iIntros (HE (Hpe1 & Hpe2)) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ Hσ". iSpecialize ("H" $! σ with "Hσ").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "H". iMod "Hclose".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & H3)|H3]]".
  - iLeft. iExists x. iFrame. iSplitR; first done.
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _); first apply HE.
  - iRight; iLeft. iExists s, vv, K. iSplitR; first done. rewrite Hpe1; iFrame.
    iModIntro.
    iDestruct "H3" as "(%Ξ & HT & Hr)".
    iFrame. iExists Ξ. iSplitL "HT"; first iApply (Hpe2 s vv with "HT").
    iNext. iIntros "%r HΞ". iApply ("IH" $! (resume_with K (of_val Λ r)) E1 E2 HE Φ Ψ with "[Hr HΞ] HΦ").
    iApply ("Hr" with "HΞ").
  - do 2 iRight.
    iDestruct "H3" as "(HH & H3)".
    iModIntro. rewrite Hpe1. iFrame.
    iDestruct "H3" as (X) "(HX & H3)". iExists _. iFrame "HX".
    iIntros (e' σ' HX).
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done.
    iMod ("H3" $! _ _ HX) as "H3". iMod "Hclose2". iModIntro. iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose3"; first done.
    iMod "H3" as "[Hσ HWP]". iMod "Hclose3". iModIntro.
    iFrame. iApply ("IH" $! e' E1 E2 HE Φ Ψ with "HWP HΦ").
Qed.

Lemma fupd_wp pe E e Φ : (|={E}=> WP e @ pe; E {{ Φ }}) ⊢ WP e @ pe; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H %σ Hσ".
  iMod "H". iApply ("H" $! σ with "Hσ").
Qed.

Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.


(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here.
 *)
Lemma wp_step_fupdN_strong n pe E e P Φ :
  TCEq (to_val e) None →
  (∀ σ, state_interp σ
       ={E}=∗ ⌜n ≤ 1⌝) ∧
  ((|={E}=> |={E}▷=>^n |={E}=> P) ∗
    WP e @ pe; E {{ v, P ={E}=∗ Φ v }}) -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "H".
  iIntros (σ1) "Hσ".
  destruct (decide (n = 0)) as [->|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" $! σ1 with "Hσ") as "[(%z & -> & Hσ & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & H3)|(%&%&H3)]]".
  + rewrite to_of_val in Heq.
    exfalso. apply TCEq_eq in Heq. congruence.
  + cbn. iRight. iLeft. iMod "HP". iModIntro.
    iExists s, vv, K. iFrame. iSplitR; first done.
    iDestruct "H3" as "(%Ξ & Hvv & HΞ)".
    iExists Ξ. iFrame. iNext. iIntros "%r Hr". iSpecialize ("HΞ" $! r with "Hr").
    iApply (wp_strong_mono pe pe E E with "HΞ [HP]"). 1-2:easy.
    iIntros "%v Hv". iMod "HP". iMod ("Hv" with "HP"). iAssumption.
  + iMod "HP". iModIntro. iRight. iRight. iSplitR; first done.
    iDestruct "H3" as "(Hstep & H3)". iExists _; iFrame "Hstep".
    iIntros (e' σ' HX). iMod ("H3" $! e' σ' HX) as "H3". do 2 iModIntro.
    iMod "H3" as "[Hσ HWP]". do 2 iMod "HP". iModIntro. iFrame.
    iApply (wp_strong_mono pe pe E E with "HWP [HP]"). 1-2:easy.
    iIntros "%v Hv". iMod ("Hv" with "HP"). iAssumption.
Qed.


Lemma wp_step_fupd pe E e P Φ :
  TCEq (to_val e) None →
  ((|={E}=>  ▷ |={E}=> P) ∗
    WP e @ pe; E {{ v, P ={E}=∗ Φ v }}) -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  iIntros (H) "(H1 & H2)".
  iApply (wp_step_fupdN_strong 1). iSplitR.
  - iIntros; iModIntro; done.
  - iSplitR "H2"; last iApply "H2". iMod "H1". do 4 iModIntro. iApply "H1".
Qed.

Lemma wp_step pe E e P Φ :
  TCEq (to_val e) None →
  ( ▷ P) -∗
    WP e @ pe; E {{ v, P ={E}=∗ Φ v }} -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  iIntros (H) "H1 H2".
  iApply (wp_step_fupd). iSplitL "H1".
  - do 3 iModIntro. iApply "H1".
  - iApply "H2".
Qed.



Lemma wp_bind K pe E e Φ :
  WP e @ pe; E {{ v, WP resume_with K (of_val Λ v) @ pe; E {{ Φ }} }} ⊢ WP resume_with K e @ pe; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  iIntros "%σ Hσ".
  iMod ("H" $! σ with "Hσ") as "[(%x & -> & Hσ & H)|[(%s & %vv & %K' & %HH & %H2 & Hb & Hσ & %Ξ & HT & Hr)|(%Hnv&%X&%Hstep&H3)]]".
  - rewrite {1} wp_unfold /wp_pre.
    iMod ("H" $! σ with "Hσ") as "H". iModIntro. iApply "H".
  - iModIntro. iRight. iLeft. iExists s, vv, (compose_cont K K').
    iSplit. 1: (iPureIntro; by eapply is_call_in_cont).
    iSplitR; first done. iFrame.
    iExists Ξ. iFrame. iNext.
    iIntros "%r HΞ". rewrite -resume_compose.
    iApply "IH". iApply ("Hr" with "HΞ").
  - iRight. iRight. iModIntro. iSplit.
    1: iPureIntro; by apply resume_not_val.
    eapply prim_step_resume in Hstep; eauto.
    iExists _. iSplit; first by (iPureIntro; eapply Hstep).
    cbn. iIntros (e' σ' (? & -> & HX)).
    iMod ("H3" $! _ _ HX) as "H3". do 2 iModIntro.
    iMod "H3" as "[Hσ HWP]". iModIntro. iFrame.
    by iApply "IH".
Qed.


(** * Derived rules *)
Lemma wp_mono pe E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ pe; E {{ Φ }} ⊢ WP e @ pe; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_strong_mono_post pe E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) -∗ WP e @ pe; E {{ Φ }} -∗ WP e @ pe; E {{ Ψ }}.
Proof.
  iIntros "HΦ H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply "HΦ".
Qed.
Lemma wp_pe_mono pe1 pe2 E e Φ :
  prog_environ_mono pe1 pe2 → WP e @ pe1; E {{ Φ }} ⊢ WP e @ pe2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val _ v) @ s; E {{ Φ }}.
Proof. iIntros "H". iApply wp_value_fupd'. iAssumption. Qed.

Lemma wp_value s E Φ e v : to_val e = Some v -> Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-%of_to_val. apply wp_value'. Qed.


Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_extern pe e fn vs C E Φ Φ' :
  is_call e fn vs C →
  penv_prog pe !! fn = None →
  penv_proto pe fn vs Φ -∗
  at_boundary Λ -∗
  (▷ ∀ v, Φ v -∗ at_boundary Λ -∗ WP resume_with C (of_val Λ v) @ pe; E {{ Φ' }}) -∗
  WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (Hiscall Hfnext) "H Hb Hcont". rewrite wp_unfold /wp_pre /=.
  iIntros (σ) "Hσ". iModIntro. iRight. iLeft.
  iExists _, _, C. iSplitR; first done.
  iSplitR; first done. iFrame "Hb Hσ". iExists Φ. iFrame "H".
  iIntros "!>" (?) "[? ?]". iApply ("Hcont" with "[$] [$]").
Qed.

Lemma wp_internal_call pe e fn vs C func body E Φ' :
  is_call e fn vs C →
  penv_prog pe !! fn = Some func →
  apply_func func vs = Some body →
  (▷ WP resume_with C body @ pe; E {{ Φ' }}) -∗
  WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (Hcall Hfn Hfunc) "H". iApply wp_unfold. rewrite /wp_pre /=.
  iIntros (σ) "Hσ !>". iRight. iRight.
  iSplitR.
  1: by erewrite is_val_not_call_2.
  iExists (λ '(e2, σ2), e2 = resume_with C body ∧ σ2 = σ). iSplit.
  { iPureIntro. eapply call_prim_step; eauto.
    eexists _, _. repeat split; eauto. }
  iIntros (? ? (-> & ->)). by iFrame.
Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI:indexT, !invG Σ, !mlangG val Σ Λ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.


End proofmode_classes.


Class linkableG
  `{SI:indexT} {val pubstate} (Λ : mlanguage val)
  `{!mlangG val Σ Λ, !linkable Λ pubstate}
  (public_state_interp : pubstate → iProp Σ)
:= LinkableG {
  private_state_interp : private_state → iProp Σ;

  state_interp_split σ pubσ privσ :
    split_state σ pubσ privσ →
    state_interp σ ==∗ public_state_interp pubσ ∗ private_state_interp privσ;

  state_interp_join pubσ privσ :
    public_state_interp pubσ -∗ private_state_interp privσ ==∗
    ∃ σ, state_interp σ ∗ ⌜split_state σ pubσ privσ⌝;

  splittable_at_boundary σ :
    at_boundary Λ -∗ state_interp σ -∗ ⌜∃ pubσ privσ, split_state σ pubσ privσ⌝;
}.
