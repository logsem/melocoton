From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From melocoton.language Require Export mlanguage.
From melocoton Require multirelations.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

Local Notation rel := multirelations.rel.

Class irisGS_gen (hlc : has_lc) (Λ : mlanguage) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen hlc Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → iProp Σ;

  (** The number of additional logical steps (i.e., later modality in the
  definition of WP) and later credits per physical step is
  [S (num_laters_per_step ns)], where [ns] is the number of physical steps
  executed so far. We add one to [num_laters_per_step] to ensure that there
  is always at least one later and later credit for each physical step. *)
  num_laters_per_step : nat → nat;

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
Global Arguments IrisG {hlc Λ Σ}.

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
Definition wp_pre `{!irisGS_gen hlc Λ Σ} (p : program Λ)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns,
     state_interp σ1 ns ={E,∅}=∗
       ⌜reducible p e1 σ1⌝ ∗
       ∀ φ, ⌜rel (prim_step p) (e1, σ1) φ⌝ -∗
         £ (S (num_laters_per_step ns))
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         ∃ e2 σ2,
           ⌜φ (e2, σ2)⌝ ∗
           state_interp σ2 (S ns) ∗
           wp E e2 Φ
  end%I.

Local Instance wp_pre_contractive `{!irisGS_gen hlc Λ Σ} p : Contractive (wp_pre p).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 15 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Local Definition wp_def `{!irisGS_gen hlc Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) (program Λ) :=
  λ p, fixpoint (wp_pre p).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {hlc Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!irisGS_gen hlc Λ Σ} : wp = @wp_def hlc Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types p : program Λ.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold p E e Φ :
  WP e @ p; E {{ Φ }} ⊣⊢ wp_pre p (wp (PROP:=iProp Σ) p) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre p)). Qed.

Global Instance wp_ne p E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) p E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 15 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  do 5 (f_contractive || f_equiv).
  rewrite IH; [done|lia|]. intros v. eapply dist_S, HΦ.
Qed.
Global Instance wp_proper p E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) p E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive p E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) p E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 14 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 8 f_equiv.
Qed.

Lemma wp_value_fupd' p E Φ v : WP of_val v @ p; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

(* TODO: also allow "weakening" the program, and what would that mean? *)
Lemma wp_strong_mono p E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  WP e @ p; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ p; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [done|]. iIntros (φ Hstep) "Hcred".
  iMod ("H" with "[//] Hcred") as "H". iIntros "!> !>".  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros ">H". iDestruct "H" as (e2 σ2 Hφ) "(? & H)".
  iMod "Hclose" as "_". iModIntro. iExists e2, σ2. iSplit; [iPureIntro; eauto|].
  iFrame. iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp p E e Φ : (|={E}=> WP e @ p; E {{ Φ }}) ⊢ WP e @ p; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd p E e Φ : WP e @ p; E {{ v, |={E}=> Φ v }} ⊢ WP e @ p; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono p E with "H"); auto. Qed.

Lemma wp_atomic p E1 E2 e Φ `{!Atomic e} :
  (|={E1,E2}=> WP e @ p; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ p; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (φ Hstep) "Hcred".
  iApply (step_fupdN_wand with "(H [//] Hcred)").
  iIntros ">H". iDestruct "H" as (e2 σ2 Hφ) "(Hσ & H)".
  rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
  + iDestruct "H" as ">> H". iModIntro.
    iExists _, _. iSplit; [by eauto|]. iFrame.
    rewrite wp_unfold /wp_pre He2 //.
  + iMod ("H" $! _ _ with "[$]") as "[H _]".
    iDestruct "H" as %(? & ?).
    eapply (atomic p σ1 _) in Hstep as (? & ? & ? & ?). %not_eq_None_Some).

    apply val_stuck in H.
    unfold irreducible in Hstep. naive_solver.
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
(*
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
*)

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma wp_step_fupdN_strong n p E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns, state_interp σ ns
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    WP e @ p; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ p; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
  iIntros (σ1 ns) "Hσ".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
  iIntros "!>" (φ Hstep) "Hcred". iMod ("H" $! φ with "[% //] Hcred") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros ">H".
    iDestruct "H" as (e2 σ2 Hφ) "(Hσ & Hwp)". iMod "HP".
    iModIntro. iExists e2, σ2. iSplit; [iPureIntro; eauto|]. iFrame.
    iApply (wp_strong_mono with "Hwp"); [done|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma wp_bind K p E e Φ :
  WP e @ p; E {{ v, WP (fill K (of_val v)) @ p; E {{ Φ }} }} ⊢ WP (fill K e) @ p; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 n) "Hσ". iMod ("H" with "[$]") as "[%Hred H]".
  iModIntro; iSplit. { eauto using fill_reducible. }
  iIntros (φ Hstep) "Hcred".
  pose proof (fill_reducible_prim_step _ _ _ _ _ Hred Hstep) as HHH.
  iSpecialize ("H" $! (λ '(e2', σ2), ∀ e2, e2 = fill K e2' → φ (e2, σ2)) with "[//] Hcred").
  iMod "H". iIntros "!>!>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as (? ?) "(% & H & ?)". iModIntro.
  iExists (fill K e2), σ2. iSplit. { iPureIntro; eauto. }
  iFrame. by iApply "IH".
Qed.

Lemma wp_bind_inv K p E e Φ :
  WP (fill K e) @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, WP (fill K (of_val v)) @ p; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 ns) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit. { eauto using fill_reducible_inv. }
  iIntros (φ Hstep) "Hcred".
  iMod ("H" $! (λ '(e2', σ2), ∃ e2, e2' = fill K e2 ∧ φ (e2, σ2)) with "[] Hcred") as "H".
  { eauto using fill_step. }
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H". iDestruct "H" as (e2 σ2 (e2' & -> & ?)) "(? & ?)".
  iModIntro. iExists e2', σ2. iSplit; [by eauto|]. iFrame. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono p E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
(* Lemma wp_stuck_mono s1 s2 E e Φ : *)
(*   s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}. *)
(* Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed. *)
(* Lemma wp_stuck_weaken s E e Φ : *)
(*   WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}. *)
(* Proof. apply wp_stuck_mono. by destruct s. Qed. *)
Lemma wp_mask_mono p E1 E2 e Φ : E1 ⊆ E2 → WP e @ p; E1 {{ Φ }} ⊢ WP e @ p; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' p E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) p E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' p E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) p E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd p E Φ e v : IntoVal e v → WP e @ p; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' p E Φ v : Φ v ⊢ WP (of_val v) @ p; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value p E Φ e v : IntoVal e v → Φ v ⊢ WP e @ p; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l p E e Φ R : R ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r p E e Φ R : WP e @ p; E {{ Φ }} ∗ R ⊢ WP e @ p; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the WP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma wp_step_fupdN n p E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns, state_interp σ ns
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @ p; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ p; E1 {{ Φ }}.
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
Lemma wp_step_fupd p E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ p; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ p; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (??) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma wp_frame_step_l p E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ p; E2 {{ Φ }} ⊢ WP e @ p; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r p E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ p; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ p; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' p E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l p E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' p E e Φ R :
  TCEq (to_val e) None → WP e @ p; E {{ Φ }} ∗ ▷ R ⊢ WP e @ p; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r p E E); try iFrame; eauto. Qed.

Lemma wp_wand p E e Φ Ψ :
  WP e @ p; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ p; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l p E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r p E e Φ Ψ :
  WP e @ p; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ p; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand p E e Φ R :
  R -∗ WP e @ p; E {{ v, R -∗ Φ v }} -∗ WP e @ p; E {{ Φ }}.
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

  Global Instance frame_wp p prog E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ prog; E {{ Φ }}) (WP e @ prog; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp p E e Φ : IsExcept0 (WP e @ p; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p prog E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ prog; E {{ Φ }}) (WP e @ prog; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p prog E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ prog; E {{ Φ }}) (WP e @ prog; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p prog E1 E2 e P Φ :
    ElimModal (Atomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ prog; E1 {{ Φ }}) (WP e @ prog; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp p E e P Φ :
    AddModal (|={E}=> P) P (WP e @ p; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e p Φ :
    ElimAcc (X:=X) (Atomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ p; E1 {{ Φ }})
            (λ x, WP e @ p; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e p Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ p; E {{ Φ }})
            (λ x, WP e @ p; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
