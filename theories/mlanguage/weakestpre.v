From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From melocoton.mlanguage Require Export mlanguage.
From melocoton Require Import multirelations.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

Class melocotonGS_gen
  (hlc : has_lc) (val pubstate : Type)
  (Λ : mlanguage val pubstate) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen hlc Σ;
  state_interp : state Λ → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {hlc val pubstate Λ Σ}.

Notation melocotonGS := (melocotonGS_gen HasLc).

Definition wp_pre `{!melocotonGS_gen hlc val pubstate Λ Σ} (p:mixin_prog Λ.(func))
    (T: string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ)
    (wp : coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e Φ,
  (∀ σ, state_interp σ ∗ ⌜matching_expr_state e σ⌝ ={E}=∗
       (∃ v, ⌜e = of_class Λ (ExprVal v)⌝ ∗ state_interp σ ∗ Φ v)
     ∨ (∃ f vs K, ⌜e = fill K (of_class Λ (ExprCall f vs))⌝ ∗ ⌜p !! f = None⌝ ∗
        |={E}=> (state_interp σ ∗ ∃ Ξ, T f vs Ξ ∗ ▷ ∀ r, Ξ r -∗ wp E (fill K (of_class Λ (ExprVal r))) Φ))
     ∨ (⌜reducible p e σ⌝ ∗ ∀ X, ⌜prim_step p (e, σ) X⌝ -∗ |={E}=>▷|={E}=>
        ∃ e' σ', ⌜X (e', σ')⌝ ∗ state_interp σ' ∗ wp E e' Φ))%I.

Local Instance wp_pre_contractive `{!melocotonGS_gen hlc val pubstate Λ Σ} {p:mixin_prog Λ.(func)} T :
  Contractive (wp_pre p T).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ. cbn in Hwp.
  repeat (f_contractive || f_equiv || apply Hwp || intros ?).
Qed.

Record prog_environ `{!melocotonGS_gen hlc val pubstate Λ Σ} := {
  prog : mixin_prog (func Λ);
  T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ
}.

Local Definition wp_def `{!melocotonGS_gen hlc val pubstate Λ Σ} : Wp (iProp Σ) (expr Λ) (val) (prog_environ) :=
  λ p : (prog_environ), fixpoint (wp_pre (p.(prog)) (p.(T))).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {hlc val pubstate Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!melocotonGS_gen hlc val pubstate Λ Σ} : wp = @wp_def hlc val pubstate Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!melocotonGS_gen hlc val pubstate Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ.
Implicit Types X : expr Λ * state Λ → Prop.

(* Weakest pre *)
Lemma wp_unfold pe E e Φ :
  WP e @ pe; E {{ Φ }} ⊣⊢ wp_pre (pe.(prog)) (pe.(T)) (wp (PROP:=iProp Σ) pe) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre (pe.(prog)) (pe.(T)))). Qed.

Global Instance wp_ne pe E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) pe E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 11 f_equiv. 1: do 8 f_equiv.
  all: f_contractive.
  1: do 1 f_equiv. 2: do 2 f_equiv.
  all: intros r; f_equiv.
  2: do 3 f_equiv.
  all: apply IH; eauto; intros k; eapply dist_le', HΦ; lia.
Qed.
Global Instance wp_proper pe E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) pe E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value_fupd' pe E Φ v : (|={E}=> Φ v)%I ⊢ WP (of_class Λ (ExprVal v)) @ pe; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ [Hσ %]". iLeft. iMod "H". iModIntro. iExists _; iFrame; done.
Qed.

Definition prog_environ_mono pe1 pe2 : Prop :=
   prog pe1 = prog pe2 ∧ ∀ f vs Φ, T pe1 f vs Φ -∗ T pe2 f vs Φ.

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
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & -> & H2 & H3)|H3]]".
  - iLeft. iExists x. iFrame. iSplitR; first done.
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _); first apply HE.
  - iRight; iLeft. iExists s, vv, K. iSplitR; first done. rewrite Hpe1; iFrame.
    iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done.
    iMod "H3".
    iMod "Hclose2". iModIntro.
    iDestruct "H3" as "(Hσ & %Ξ & HT & Hr)".
    iFrame. iExists Ξ. iSplitL "HT"; first iApply (Hpe2 s vv with "HT").
    iNext. iIntros "%r HΞ". iApply ("IH" $! (fill K (of_class Λ (ExprVal r))) E1 E2 HE Φ Ψ with "[Hr HΞ] HΦ").
    iApply ("Hr" with "HΞ").
  - do 2 iRight.
    iDestruct "H3" as "(HH & H3)".
    iModIntro. rewrite Hpe1. iFrame. iIntros (X) "Hstep".
    iSpecialize ("H3" $! X with "Hstep").
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done.
    iMod "H3". iMod "Hclose2". iModIntro. iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose3"; first done.
    iMod "H3" as (e' σ' HX) "(Hσ & HWP)". iMod "Hclose3".
    iModIntro. iExists e', σ'. iSplit; [iPureIntro; eauto|].
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
  iIntros (σ1) "[Hσ %]".
  destruct (decide (n = 0)) as [->|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" $! σ1 with "[$Hσ]") as "[(%z & -> & Hσ & H)|[(%s & %vv & %K & -> & H2 & H3)|[% H3]]]"; first done.
  + unfold to_val in Heq. rewrite to_of_class in Heq.
    exfalso. apply TCEq_eq in Heq. congruence.
  + cbn. iRight. iLeft. iMod "HP". iModIntro.
    iExists s, vv, K. iFrame. iSplitR; first done.
    iMod "H3" as "(Hσ & %Ξ & Hvv & HΞ)". iModIntro. iFrame.
    iExists Ξ. iFrame. iNext. iIntros "%r Hr". iSpecialize ("HΞ" $! r with "Hr").
    iApply (wp_strong_mono pe pe E E with "HΞ [HP]"). 1-2:easy.
    iIntros "%v Hv". iMod "HP". iMod ("Hv" with "HP"). iAssumption.
  + iMod "HP". iModIntro. iRight. iRight. iSplitR; first done.
    iIntros (X Hstep). iSpecialize ("H3" $! X Hstep).
    iMod "H3". do 2 iModIntro. iMod "H3" as (e' σ' HX) "(Hσ' & H3)". do 2 iMod "HP".
    iModIntro. iExists e', σ'. iSplitR; first by eauto. iFrame.
    iApply (wp_strong_mono pe pe E E with "H3 [HP]"). 1-2:easy.
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
  WP e @ pe; E {{ v, WP fill K (of_class _ (ExprVal v)) @ pe; E {{ Φ }} }} ⊢ WP fill K e @ pe; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  iIntros "%σ [Hσ %Hmatch]".
  pose proof (proj2 (matching_expr_state_ctx _ _ _) Hmatch) as Hmatch'.
  iMod ("H" $! σ with "[$Hσ]") as "[(%x & -> & Hσ & H)|[(%s & %vv & %K' & -> & H2 & H3)|[%Hred H3]]]"; first done.
  - rewrite {1} wp_unfold /wp_pre.
    iMod ("H" $! σ with "[$Hσ]") as "H"; first done. iApply "H".
  - iRight. iLeft. iExists s, vv, (comp_ectx K K').
    iFrame. iSplitR.
    {iModIntro; iPureIntro. now rewrite fill_comp. }
    do 1 iModIntro. iMod "H3" as "(Hσ & %Ξ & HT & Hr)". iModIntro. iFrame.
    iExists Ξ. iFrame. iNext.
    iIntros "%r HΞ".
    rewrite <- fill_comp.
    iApply "IH". iApply ("Hr" with "HΞ").
  - iRight. iRight. iModIntro. iSplitR; first eauto using reducible_fill.
    iIntros (X Hstep).
    pose proof (reducible_not_val _ _ _ Hred) as Hnone.
    apply fill_step_inv in Hstep; [| done].
    iSpecialize ("H3" $! _ Hstep). iMod "H3". iModIntro. iModIntro.
    iMod "H3" as (e' σ' HX) "(Hσ & H3)". iModIntro. iExists (fill K e'), σ'.
    iSplitR; first done. iFrame. iApply "IH". iApply "H3".
Qed.

(*
Lemma wp_bind_inv K s E e Φ :
  WP fill K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP fill K (of_class _ (ExprVal v)) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). do 2 rewrite {1} wp_unfold /wp_pre /=.
  iIntros "%σ %ns Hσ".
  iMod ("H" $! σ ns with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & H1 & H2 & H3)|H3]]".
  - destruct (fill_class' K e) as [->|(v&<-%of_to_class)].
    + eexists. rewrite H1. now rewrite to_of_class.
    + rewrite ! fill_empty in H1. subst. iLeft.
      iModIntro. iExists _. iSplitR; first done. rewrite fill_empty. iFrame.
      rewrite {1} wp_unfold /wp_pre /=. iIntros "%σ' %ns' Hσ'".
      iModIntro. iLeft. iExists x. iFrame. done.
    + iLeft. iExists v. iModIntro. iSplitR; first done.
      iFrame. rewrite H1.
      rewrite {1} wp_unfold /wp_pre /=. iIntros "%σ' %ns' Hσ'".
      iModIntro. iLeft. iExists x. iFrame. done.
  - *)

(** * Derived rules *)
Lemma wp_mono pe E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ pe; E {{ Φ }} ⊢ WP e @ pe; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
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
Proof. intros H.
  assert (e = of_val _ v) as ->.
  - unfold of_val. unfold to_val in H. destruct (to_class e) as [[]|] eqn:Heq; cbn in H; try congruence.
    apply of_to_class in Heq. congruence.
  - apply wp_value'.
Qed.


Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

(*
Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.
*)
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
  Context `{!melocotonGS_gen hlc val pubstate Λ Σ}.
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
(*
  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.*)
End proofmode_classes.
