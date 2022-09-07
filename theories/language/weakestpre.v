From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From melocoton.language Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

Class irisGS_gen 
  (hlc : has_lc) (val pubstate : Type) 
  (Λ : language val pubstate) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen hlc Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → iProp Σ;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns:
    state_interp σ ns ={∅}=∗ state_interp σ (S ns)
}.
Global Opaque iris_invGS.
Global Arguments IrisG {hlc val pubstate Λ Σ}.

Notation irisGS := (irisGS_gen HasLc).
(** The predicate we take the fixpoint of in order to define the WP. *)
(** In the step case, we both provide [S (num_laters_per_step ns)]
  later credits, as well as an iterated update modality that allows
  stripping as many laters, where [ns] is the number of steps already taken.
  We have both as each of these provides distinct advantages:
  - Later credits do not have to be used right away, but can be kept to
    eliminate laters at a later point.
  - The step-taking update composes well in parallel: we can independently
    compose two clients who want to eliminate their laters for the same
    physical step, which is not possible with later credits, as they
    can only be used by exactly one client.
  - The step-taking update can even be used by clients that opt out of
    later credits, e.g. because they use [BiFUpdPlainly]. *)
Definition wp_pre `{!irisGS_gen hlc val pubstate Λ Σ} 
    (p:mixin_prog Λ.(func))
    (T: string -d> list val -d> (val -d> iPropO Σ) -n> iPropO Σ)
    (wp : coPset -d>
          expr Λ -d>
          (val -d> iPropO Σ) -d>
          iPropO Σ) :
    coPset -d>
    expr Λ -d>
    (val -d> iPropO Σ) -d>
    iPropO Σ := λ E e Φ,
  (  (∃ v, ⌜e = of_class Λ (ExprVal v)⌝ ∗ (|={E}=> Φ v))
   ∨ (∃ s vv K, ⌜e = fill K (of_class Λ (ExprCall s vv))⌝ ∗ ⌜p !! s = None⌝ ∗
        (∀ σ ns, state_interp σ ns ={E}▷=∗ 
                 (state_interp σ ns ∗ T s vv (λ r, wp E (fill K (of_class Λ (ExprVal r))) Φ))))
   ∨ (∀ σ1 ns, state_interp σ1 ns ={E,∅}=∗ ⌜reducible p e σ1⌝ ∗
        ∀ σ2 e', ⌜head_step p e σ1 e' σ2 []⌝ -∗ |={∅}=> ▷ |={∅,E}=> 
            (state_interp σ2 (S ns) ∗ wp E e' Φ)))%I.

Local Instance wp_pre_contractive `{!irisGS_gen hlc val pubstate Λ Σ}
     {p:mixin_prog Λ.(func)} T : Contractive (wp_pre p T).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ. cbn in Hwp.
  repeat (f_contractive || f_equiv || apply Hwp || intros ?).
Qed.

Record prog_environ `{!irisGS_gen hlc val pubstate Λ Σ} := {
  prog : mixin_prog (func Λ);
  T : string -d> list val -d> (val -d> iPropO Σ) -n> iPropO Σ;
  T_weak : ∀ s vv Φ Ψ, (∀ r, Φ r -∗ Ψ r) -∗ T s vv Φ -∗ T s vv Ψ
}.

Local Definition wp_def `{!irisGS_gen hlc val pubstate Λ Σ} : Wp (iProp Σ) (expr Λ) (val) (prog_environ) :=
  λ p : (prog_environ), fixpoint (wp_pre (p.(prog)) (p.(T))).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {hlc val pubstate Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!irisGS_gen hlc val pubstate Λ Σ} : wp = @wp_def hlc val pubstate Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS_gen hlc val pubstate Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -n> iPropO Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ.

(* Weakest pre *)
Lemma wp_unfold pe E e Φ :
  WP e @ pe; E {{ Φ }} ⊣⊢ wp_pre (pe.(prog)) (pe.(T)) (wp (PROP:=iProp Σ) pe) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre (pe.(prog)) (pe.(T)))). Qed.

Global Instance wp_ne pe E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) pe E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 15 f_equiv.
  1: f_equiv.
  all: f_contractive.
  all: f_equiv.
  all: f_equiv. 
  1: f_equiv; intros r. 
  all: apply IH; eauto; intros k; eapply dist_le', HΦ; lia.
Qed.
Global Instance wp_proper pe E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) pe E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance wp_contractive pe E e n :
  (∀ v,e <> of_class Λ (ExprVal v)) ->
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) pe E e).
Proof.
  intros Hne Φ Ψ HΦ. rewrite !wp_unfold /wp_pre /=. f_equiv.
  1: admit. (* TODO: this holds by assumption, if we tie it out of the model? *)
  do 14 f_equiv.
  1: f_equiv.
  all: f_contractive.
  all: f_equiv.
  all: f_equiv.
  1: f_equiv; intros r.
  all: f_equiv.
  all: intros v'; apply dist_later_dist, HΦ.
Admitted.

Lemma wp_value_fupd' pe E Φ v : WP (of_class Λ (ExprVal v)) @ pe; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre. iSplit; first iIntros "[(%x & %Heq & H)|[(%s & %vv & %K & %H1 & _ & H3)|H3]]".
  - assert (v = x) as ->.
    1: {assert (to_class (of_class Λ (ExprVal v)) = Some (ExprVal v)) by apply to_of_class.
        rewrite Heq in H. rewrite to_of_class in H. congruence. }
    iApply "H".
  - exfalso. pose proof (fill_val K (of_class Λ (ExprCall s vv))) as Hnv. unfold to_val in Hnv.
    rewrite to_of_class in Hnv. eapply is_Some_None. apply Hnv.
    rewrite <- H1. rewrite to_of_class. easy.
  - admit. (* Can be shown if the state interpretation is unconditionally true for some state *)
  - iIntros "H". iLeft. iExists v. iSplit; first done. iApply "H".
Admitted.


Definition prog_environ_mono pe1 pe2 : Prop := 
   prog pe1 = prog pe2
/\ ∀ (s:string) vv Φ Ψ, (∀ r, Φ r -∗ Ψ r) -∗ T pe1 s vv Φ -∗ T pe2 s vv Ψ.

Lemma wp_strong_mono pe1 pe2 E1 E2 e Φ Ψ :
  E1 ⊆ E2 → prog_environ_mono pe1 pe2 ->
  WP e @ pe1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ pe2; E2 {{ Ψ }}.
Proof.
  iIntros (HE (Hpe1 & Hpe2)) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  iDestruct "H" as "[(%x & -> & H)|[(%s & %vv & %K & -> & H2 & H3)|H3]]".
  - iLeft. iExists x. iSplitR; first done. 
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _); first apply HE.
  - iRight; iLeft. iExists s, vv, K. iSplitR; first done. rewrite Hpe1; iFrame.
    iIntros "%σ %ns Hσ".
    iSpecialize ("H3" $! σ ns with "Hσ").
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod "H3".
    iMod "Hclose".
    do 2 iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done.
    iMod "H3".
    iMod "Hclose2". iModIntro.
    iDestruct "H3" as "(Hσ & HT)".
    iFrame.
    iApply (Hpe2 s vv with "[HΦ] HT").
    iIntros "%r H1". iApply ("IH" $! (fill K (of_class Λ (ExprVal r))) E1 E2 HE Φ Ψ with "[H1] HΦ").
    done.
  - do 2 iRight. iIntros "%σ1 %ns Hσ".
    iSpecialize ("H3" $! σ1 ns with "Hσ"). 
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod "H3" as "(HH & H3)".
    iModIntro. rewrite Hpe1. iFrame. iIntros "%σ2 %e' Hstep".
    iSpecialize ("H3" $! σ2 e' with "Hstep").
    iMod "H3". iModIntro.
    iModIntro. iMod "H3" as "(Hσ & HWP)". iMod "Hclose".
    iModIntro. iFrame. iApply ("IH" $! e' E1 E2 HE Φ Ψ with "HWP HΦ").
Qed.

Lemma fupd_wp pe E e Φ : (|={E}=> WP e @ pe; E {{ Φ }}) ⊢ WP e @ pe; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". (*destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (e2 σ2 efs Hstep) "Hcred".
  iApply (step_fupdN_wand with "(H [//] Hcred)").
  iIntros ">(Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite wp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". by iApply wp_value_fupd'.
Qed.

(** This lemma gives us access to the later credits that are generated in each step,
  assuming that we have instantiated [num_laters_per_step] with a non-trivial (e.g. linear)
  function.
  This lemma can be used to provide a "regeneration" mechanism for later credits.
  [state_interp] will have to be defined in a way that involves the required regneration
  tokens. TODO: point to an example of how this is used.

  In detail, a client can use this lemma as follows:
  * the client obtains the state interpretation [state_interp _ ns _ _],
  * it uses some ghost state wired up to the interpretation to know that
    [ns = k + m], and update the state interpretation to [state_interp _ m _ _],
  * _after_ [e] has finally stepped, we get [num_laters_per_step k] later credits
    that we can use to prove [P] in the postcondition, and we have to update
    the state interpretation from [state_interp _ (S m) _ _] to
    [state_interp _ (S ns) _ _] again. *)
Lemma wp_credit_access s E e Φ P :
  TCEq (to_val e) None →
  (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ∃ k m, state_interp σ1 m κs nt ∗ ⌜ns = (m + k)%nat⌝ ∗
    (∀ nt σ2 κs, £ (num_laters_per_step k) -∗ state_interp σ2 (S m) κs nt ={E}=∗
      state_interp σ2 (S ns) κs nt ∗ P)) -∗
  WP e @ s; E {{ v, P ={E}=∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> Htri) "Hupd Hwp".
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("Hupd" with "Hσ1") as (k m) "(Hσ1 & -> & Hpost)".
  iMod ("Hwp" with "Hσ1") as "[$ Hwp]". iModIntro.
  iIntros (e2 σ2 efs Hstep) "Hc".
  iDestruct "Hc" as "[Hone Hc]".
  iPoseProof (lc_weaken with "Hc") as "Hc"; first apply Htri.
  iDestruct "Hc" as "[Hm Hk]".
  iCombine "Hone Hm" as "Hm".
  iApply (step_fupd_wand with "(Hwp [//] Hm)"). iIntros "Hwp".
  iApply (step_fupdN_le (num_laters_per_step m)); [ | done | ].
  { etrans; last apply Htri. lia. }
  iApply (step_fupdN_wand with "Hwp"). iIntros ">(SI & Hwp & $)".
  iMod ("Hpost" with "Hk SI") as "[$ HP]". iModIntro.
  iApply (wp_strong_mono with "Hwp"); [by auto..|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". iMod ("H" $! e2 σ2 efs with "[% //] Hcred") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros ">($ & Hwp & $)". iMod "HP".
    iModIntro. iApply (wp_strong_mono with "Hwp"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 step κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//] Hcred") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step.
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the WP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma wp_step_fupdN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
  iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
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
  Context `{!irisGS_gen hlc Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
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
  Qed.
End proofmode_classes.
*)
Admitted.
End wp.
