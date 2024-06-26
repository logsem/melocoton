From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.mlanguage Require Export mlanguage progenv.
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
Class mlangG {SI:indexT} (val : Type) (Λ : mlanguage val) (Σ : gFunctors) :=
MlangG {
  state_interp : state Λ → iProp Σ;
  at_boundary : iProp Σ;
}.

Arguments at_boundary {_ _} Λ {_ _}.

Definition wp_pre_cases `{SI:indexT, !invG Σ, !mlangG val Λ Σ}
    (p : mixin_prog Λ.(func))
    (Ψ : protocol val Σ)
    (wp : coPset -d> expr Λ -d> (outcome val -d> iPropO Σ) -d> iPropO Σ) :
    state Λ -d> coPset -d> expr Λ -d> (outcome val -d> iPropO Σ) -d> iPropO Σ := λ σ E e Φ,
  (
      (∃ o, ⌜e = of_outcome Λ o⌝ ∗ state_interp σ ∗ Φ o)
    ∨ (∃ f vs K, ⌜is_call e f vs K⌝ ∗ ⌜p !! f = None⌝ ∗
       at_boundary Λ ∗ state_interp σ ∗
       ∃ Φ', Ψ f vs Φ' ∗ ▷ ∀ r, Φ' r ∗ at_boundary Λ -∗ wp E (fill K (of_outcome Λ r)) Φ)
    ∨ (⌜to_outcome e = None⌝ ∗
       ∃ X, ⌜prim_step p (e, σ) X⌝ ∗
       ∀ e' σ', ⌜X (e', σ')⌝ ={E}▷=∗ state_interp σ' ∗ wp E e' Φ)
  )%I.

Definition wp_pre `{SI:indexT, !invG Σ, !mlangG val Λ Σ}
    (p : mixin_prog Λ.(func))
    (Ψ : protocol val Σ)
    (wp : coPset -d> expr Λ -d> (outcome val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (outcome val -d> iPropO Σ) -d> iPropO Σ := λ E e Φ,
  (∀ σ, state_interp σ ={E}=∗ wp_pre_cases p Ψ wp σ E e Φ)%I.

Local Instance wp_pre_contractive
      `{SI:indexT, !invG Σ, !mlangG val Λ Σ}
      {p:mixin_prog Λ.(func)} Ψ :
  Contractive (wp_pre p Ψ).
Proof.
  rewrite /wp_pre /wp_pre_cases /= => n wp wp' Hwp E e1 Φ. cbn in Hwp.
  repeat (f_contractive || f_equiv || apply Hwp || intros ?).
Qed.

Local Definition wp_def
      `{SI:indexT, !invG Σ, !mlangG val Λ Σ} :
  Wp (iProp Σ) (expr Λ) (outcome val) (prog_environ Λ Σ) :=
  λ p : (prog_environ Λ Σ), fixpoint (wp_pre p.(penv_prog) p.(penv_proto)).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {SI Σ _ val Λ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{SI:indexT, !invG Σ, !mlangG val Λ Σ} :
  wp = @wp_def SI Σ _ val Λ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Definition mprogwp `{!indexT, !invG Σ, !mlangG val Λ Σ}
  (p : mlang_prog Λ) (Ψ : protocol val Σ) : protocol val Σ
:=
  (λ fname vs Φ, ⌜fname ∈ dom p⌝ ∗ ∀ Φ',
     at_boundary Λ -∗
     ▷ (∀ o, Φ o ∗ at_boundary Λ -∗ Φ' o) -∗
     WP to_call Λ fname vs at ⟪p, Ψ⟫ {{ Φ' }})%I.

Notation "Ψext '|-' p '::' Ψp" := (Ψp ⊑ mprogwp p Ψext)
  (at level 50, p, Ψp at level 51).

Notation "'|-' p '::' Ψp" := (∀ Ψ, Ψ |- p :: Ψp)
  (at level 50, p, Ψp at level 51).

Section wp.
Context `{SI:indexT, !invG Σ, !mlangG val Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : outcome val → iProp Σ.
Implicit Types o : outcome val.
Implicit Types e : expr Λ.
Implicit Types Ψ : protocol val Σ.
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
  revert e. induction (index_lt_wf n) as [n _ IH]=> e Φ Φ' HΦ.
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

Lemma wp_outcome_fupd' pe E Φ o : (|={E}=> Φ o)%I ⊢ WP ( of_outcome Λ o) @ pe; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ Hσ". iLeft. iMod "H". iModIntro. iExists _; iFrame; done.
Qed.


Lemma wp_strong_mono p Ψ1 Ψ2 E1 E2 e Φ Φ' :
  E1 ⊆ E2 → Ψ1 ⊑ Ψ2 →
  WP e @ ⟪p, Ψ1⟫; E1 {{ Φ }} -∗ (∀ o, Φ o ={E2}=∗ Φ' o) -∗ WP e @ ⟪p, Ψ2⟫; E2 {{ Φ' }}.
Proof.
  iIntros (HE HΨ) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Φ').
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ Hσ". iSpecialize ("H" $! σ with "Hσ").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "H". iMod "Hclose".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & H3)|H3]]".
  - iLeft. iExists x. iFrame. iSplitR; first done.
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _); first apply HE.
  - iRight; iLeft. iExists s, vv, K. iSplitR; first done.
    iModIntro.
    iDestruct "H3" as "(%Ξ & HT & Hr)".
    iFrame. iExists Ξ. iSplitL "HT"; first iApply (HΨ s vv with "HT").
    iNext. iIntros "%r HΞ". iApply ("IH" $! (fill K (of_outcome Λ r)) E1 E2 HE Φ Φ' with "[Hr HΞ] HΦ").
    iApply ("Hr" with "HΞ").
  - do 2 iRight.
    iDestruct "H3" as "(HH & H3)".
    iModIntro. iFrame.
    iDestruct "H3" as (X) "(HX & H3)". iExists _. iFrame "HX".
    iIntros (e' σ' HX).
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done.
    iMod ("H3" $! _ _ HX) as "H3". iMod "Hclose2". iModIntro. iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose3"; first done.
    iMod "H3" as "[Hσ HWP]". iMod "Hclose3". iModIntro.
    iFrame. iApply ("IH" $! e' E1 E2 HE Φ Φ' with "HWP HΦ").
Qed.

Lemma wp_post_mono pe E e Φ Φ' :
  WP e @ pe; E {{ Φ }} -∗ (∀ o, Φ o ={E}=∗ Φ' o) -∗ WP e @ pe; E {{ Φ' }}.
Proof. destruct pe as [p Ψ]. by apply wp_strong_mono. Qed.

Lemma fupd_wp pe E e Φ : (|={E}=> WP e @ pe; E {{ Φ }}) ⊢ WP e @ pe; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H %σ Hσ".
  iMod "H". iApply ("H" $! σ with "Hσ").
Qed.

Lemma wp_fupd s E e Φ : WP e @ s; E {{ o, |={E}=> Φ o }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_post_mono with "H"); auto. Qed.


(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here.
 *)
Lemma wp_step_fupdN_strong n pe E e P Φ :
  TCEq (to_outcome e) None →
  (∀ σ, state_interp σ
       ={E}=∗ ⌜n ≤ 1⌝) ∧
  ((|={E}=> |={E}▷=>^n |={E}=> P) ∗
    WP e @ pe; E {{ o, P ={E}=∗ Φ o }}) -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (?) "/= [_ [HP Hwp]]".
    iApply (wp_post_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "H".
  iIntros (σ1) "Hσ".
  destruct (decide (n = 0)) as [->|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" $! σ1 with "Hσ") as "[(%z & -> & Hσ & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & H3)|(%&%&H3)]]".
  + rewrite to_of_outcome in Heq.
    exfalso. apply TCEq_eq in Heq. congruence.
  + cbn. iRight. iLeft. iMod "HP". iModIntro.
    iExists s, vv, K. iFrame. iSplitR; first done.
    iDestruct "H3" as "(%Ξ & Hvv & HΞ)".
    iExists Ξ. iFrame. iNext. iIntros "%r Hr". iSpecialize ("HΞ" $! r with "Hr").
    iApply (wp_post_mono with "HΞ [HP]").
    iIntros "%v Hv". iMod "HP". iMod ("Hv" with "HP"). iAssumption.
  + iMod "HP". iModIntro. iRight. iRight. iSplitR; first done.
    iDestruct "H3" as "(Hstep & H3)". iExists _; iFrame "Hstep".
    iIntros (e' σ' HX). iMod ("H3" $! e' σ' HX) as "H3". do 2 iModIntro.
    iMod "H3" as "[Hσ HWP]". do 2 iMod "HP". iModIntro. iFrame.
    iApply (wp_post_mono with "HWP [HP]").
    iIntros "%v Hv". iMod ("Hv" with "HP"). iAssumption.
Qed.


Lemma wp_step_fupd pe E e P Φ :
  TCEq (to_outcome e) None →
  ((|={E}=>  ▷ |={E}=> P) ∗
    WP e @ pe; E {{ o, P ={E}=∗ Φ o }}) -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  iIntros (H) "(H1 & H2)".
  iApply (wp_step_fupdN_strong 1). iSplitR.
  - iIntros; iModIntro; done.
  - iSplitR "H2"; last iApply "H2". iMod "H1". do 4 iModIntro. iApply "H1".
Qed.

Lemma wp_step pe E e P Φ :
  TCEq (to_outcome e) None →
  ( ▷ P) -∗
    WP e @ pe; E {{ o, P ={E}=∗ Φ o }} -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  iIntros (H) "H1 H2".
  iApply (wp_step_fupd). iSplitL "H1".
  - do 3 iModIntro. iApply "H1".
  - iApply "H2".
Qed.



Lemma wp_bind K pe E e Φ :
  WP e @ pe; E {{ o, WP fill K (of_outcome Λ o) @ pe; E {{ Φ }} }} ⊢ WP fill K e @ pe; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  iIntros "%σ Hσ".
  iMod ("H" $! σ with "Hσ") as "[(%x & -> & Hσ & H)|[(%s & %vv & %K' & %HH & %H2 & Hb & Hσ & %Ξ & HT & Hr)|(%Hnv&%X&%Hstep&H3)]]".
  - rewrite {1} wp_unfold /wp_pre.
    iMod ("H" $! σ with "Hσ") as "H". iModIntro. iApply "H".
  - iModIntro. iRight. iLeft. iExists s, vv, (comp_ectx K K').
    iSplit. 1: (iPureIntro; by eapply is_call_in_ctx).
    iSplitR; first done. iFrame.
    iExists Ξ. iFrame. iNext.
    iIntros "%r HΞ". rewrite -resume_compose.
    iApply "IH". iApply ("Hr" with "HΞ").
  - iRight. iRight. iModIntro. iSplit.
    1: iPureIntro; by apply resume_not_outcome.
    eapply prim_step_resume in Hstep; eauto.
    iExists _. iSplit; first by (iPureIntro; eapply Hstep).
    cbn. iIntros (e' σ' (? & -> & HX)).
    iMod ("H3" $! _ _ HX) as "H3". do 2 iModIntro.
    iMod "H3" as "[Hσ HWP]". iModIntro. iFrame.
    by iApply "IH".
Qed.


(** Derived rules *)
Lemma wp_mono pe E e Φ Φ' : (∀ o, Φ o ⊢ Φ' o) → WP e @ pe; E {{ Φ }} ⊢ WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_post_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
(* FIXME: this is a duplicate of wp_post_mono *)
Lemma wp_strong_mono_post pe E e Φ Φ' :
  (∀ o, Φ o -∗ Φ' o) -∗ WP e @ pe; E {{ Φ }} -∗ WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros "HΦ H"; iApply (wp_post_mono with "H"); auto.
  iIntros (o) "?". by iApply "HΦ".
Qed.
Lemma wp_proto_mono p Ψ1 Ψ2 E e Φ :
  Ψ1 ⊑ Ψ2 → WP e @ ⟪p, Ψ1⟫; E {{ Φ }} ⊢ WP e @ ⟪p, Ψ2⟫; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_mask_mono pe E1 E2 e Φ : E1 ⊆ E2 → WP e @ pe; E1 {{ Φ }} ⊢ WP e @ pe; E2 {{ Φ }}.
Proof.
  destruct pe.
  iIntros (?) "H"; iApply (wp_strong_mono with "H"); by auto.
Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_outcome' s E Φ o : Φ o ⊢ WP (of_outcome _ o) @ s; E {{ Φ }}.
Proof. iIntros "H". iApply wp_outcome_fupd'. iAssumption. Qed.

Lemma wp_outcome s E Φ e o : to_outcome e = Some o -> Φ o ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-%of_to_outcome. apply wp_outcome'. Qed.


Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ o, R ∗ Φ o }}.
Proof. iIntros "[? H]". iApply (wp_post_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ o, Φ o ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_post_mono with "H"); auto with iFrame. Qed.

Lemma wp_internal_call_inv E p Ψ fn vs Φ :
  fn ∈ dom p →
  WP to_call Λ fn vs @ ⟪p, Ψ⟫; E {{ Φ }} -∗
  ∀ σ, state_interp σ ={E}=∗
  ∃ X, ⌜prim_step p (to_call Λ fn vs, σ) X⌝ ∗
    (∀ e' σ',
      ⌜X (e', σ')⌝ ={E}▷=∗ state_interp σ' ∗
      WP e' @ ⟪p,Ψ⟫; E {{ o, Φ o }}).
Proof.
  iIntros (Hfn) "HWP". iIntros (σ) "Hσ".
  rewrite !wp_unfold /wp_pre /=.
  iDestruct ("HWP" with "Hσ") as ">[HWP|[HWP|HWP]]".
  { iExFalso. iDestruct "HWP" as (? HH) "?".
    assert (is_call (of_outcome Λ o) fn vs empty_ectx) as Hv%is_outcome_not_call_2.
    { rewrite -HH. apply to_call_is_call. }
    rewrite to_of_outcome // in Hv. }
  { iExFalso. iDestruct "HWP" as (? ? ? HH Hdom) "_".
    apply not_elem_of_dom in Hdom.
    by apply is_call_to_call_inv in HH as (?&?&?); simplify_eq. }
  iDestruct "HWP" as "[_ HWP]". done.
Qed.

Lemma wp_extern pe e fn vs K E Φ Φ' :
  is_call e fn vs K →
  penv_prog pe !! fn = None →
  penv_proto pe fn vs Φ -∗
  at_boundary Λ -∗
  (▷ ∀ o, Φ o -∗ at_boundary Λ -∗ WP fill K (of_outcome Λ o) @ pe; E {{ Φ' }}) -∗
  WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (Hiscall Hfnext) "H Hb Hcont". rewrite wp_unfold /wp_pre /=.
  iIntros (σ) "Hσ". iModIntro. iRight. iLeft.
  iExists _, _, K. iSplitR; first done.
  iSplitR; first done. iFrame "Hb Hσ". iExists Φ. iFrame "H".
  iIntros "!>" (?) "[? ?]". iApply ("Hcont" with "[$] [$]").
Qed.

Lemma wp_internal_call pe e fn vs K func body E Φ' :
  is_call e fn vs K →
  penv_prog pe !! fn = Some func →
  apply_func func vs = Some body →
  (▷ WP fill K body @ pe; E {{ Φ' }}) -∗
  WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (Hcall Hfn Hfunc) "H". iApply wp_unfold. rewrite /wp_pre /=.
  iIntros (σ) "Hσ !>". iRight. iRight.
  iSplitR.
  1: by erewrite is_outcome_not_call_2.
  iExists (λ '(e2, σ2), e2 = fill K body ∧ σ2 = σ). iSplit.
  { iPureIntro. eapply call_prim_step; eauto.
    eexists _, _. repeat split; eauto. }
  iIntros (? ? (-> & ->)). by iFrame.
Qed.

Lemma wp_internal_call_at_boundary p fn vs Ψ Φ Φ' :
  at_boundary Λ -∗
  mprogwp p Ψ fn vs Φ -∗
  ▷ (∀ o, Φ o ∗ at_boundary Λ -∗ Φ' o) -∗
  WP to_call Λ fn vs at ⟪p, Ψ⟫ {{ Φ' }}.
Proof.
  iIntros "Hb HWP Hcont".
  iDestruct "HWP" as "[%Hin Hwp]".
  iDestruct ("Hwp" with "Hb Hcont") as "Hwp".
  iApply (wp_post_mono with "Hwp"). eauto.
Qed.

Lemma wp_wand s E e Φ Φ' :
  WP e @ s; E {{ Φ }} -∗ (∀ o, Φ o -∗ Φ' o) -∗ WP e @ s; E {{ Φ' }}.
Proof.
  iIntros "Hwp H". iApply (wp_post_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Φ' :
  (∀ o, Φ o -∗ Φ' o) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ' }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Φ' :
  WP e @ s; E {{ Φ }} ∗ (∀ o, Φ o -∗ Φ' o) ⊢ WP e @ s; E {{ Φ' }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ o, R -∗ Φ o }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (o) "HΦ". by iApply "HΦ".
Qed.

Lemma progwp_mono Ψ1 Ψ2 p :
  Ψ1 ⊑ Ψ2 →
  mprogwp p Ψ1 ⊑ mprogwp p Ψ2.
Proof.
  iIntros (HΨ ? ? ?) "[% H]". rewrite /mprogwp.
  iSplit; first done. iIntros (Φ') "Hb HCont".
  iSpecialize ("H" with "[$Hb]"); eauto.
  iApply (wp_strong_mono with "[H HCont]"); [eauto..| |].
  { iApply ("H" with "HCont"). } eauto.
Qed.

Lemma prog_triple_mono Ψ1 Ψ1' Ψ2 Ψ2' p :
  Ψ1 ⊑ Ψ1' → Ψ2' ⊑ Ψ2 →
  Ψ1 |- p :: Ψ2 →
  Ψ1' |- p :: Ψ2'.
Proof. iIntros (H1 H2 HH). rewrite H2 HH. by eapply progwp_mono. Qed.
Lemma prog_triple_mono_l Ψ1 Ψ2 Ψ1' p :
  Ψ1 ⊑ Ψ1' → Ψ1 |- p :: Ψ2 → Ψ1' |- p :: Ψ2.
Proof. intros. by eapply prog_triple_mono. Qed.
Lemma prog_triple_mono_r Ψ1 Ψ2 Ψ2' p :
  Ψ2' ⊑ Ψ2 → Ψ1 |- p :: Ψ2 → Ψ1 |- p :: Ψ2'.
Proof. intros. by eapply prog_triple_mono. Qed.

Lemma mprogwp_except_dom p Ψ : (mprogwp p Ψ) except (dom p) ⊑ ⊥.
Proof.
  iIntros (? ? ?). rewrite /proto_except /=. by iIntros "[% [% H]]".
Qed.

End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI:indexT, !invG Σ, !mlangG val Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : outcome val → iProp Σ.
  Implicit Types o : outcome val.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Φ' :
    (∀ o, Frame p R (Φ o) (Φ' o)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ' }}) | 2.
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
  `{!mlangG val Λ Σ, !linkable Λ pubstate}
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
