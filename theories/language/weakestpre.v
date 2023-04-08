From stdpp Require Import base.
From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.language Require Export language progenv.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

(* armael: the unbundling of [irisG_gen] here and in mlanguage (a priori
   required to ensure that the same instance is used across different languages)
   might produce large Coq terms and cause performance issues. If this happens
   we may need to revisit this design choice. *)

Class langG
  {SI : indexT}
  (val : Type)
  (Λ : language val) (Σ : gFunctors) := LangG {
  (** The state interpretation is an invariant that should hold in
      between each step of reduction. *)
  state_interp : state Λ → iProp Σ;
}.
Global Arguments LangG {SI val Λ Σ}.

Definition wp_pre `{!indexT, !langG val Λ Σ, !invG Σ}
    (p:mixin_prog Λ.(func))
    (Ψ: string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ)
    (wp : coPset -d>
          expr Λ -d>
          (val -d> iPropO Σ) -d>
          iPropO Σ) :
    coPset -d>
    expr Λ -d>
    (val -d> iPropO Σ) -d>
    iPropO Σ := λ E e Φ,
    (∀ σ, state_interp σ ={E}=∗
      (  (∃ v, ⌜e = of_class Λ (ExprVal v)⌝ ∗ state_interp σ ∗ Φ v)
       ∨ (∃ s vv K, ⌜e = fill K (of_class Λ (ExprCall s vv))⌝ ∗ ⌜p !! s = None⌝ ∗
          |={E}=>
            (∃ Φ', state_interp σ ∗ Ψ s vv Φ' ∗  ▷ ∀ r, Φ' r -∗ wp E (fill K (of_class Λ (ExprVal r))) Φ))
       ∨ ((⌜reducible p e σ⌝ ∗
           ∀ σ' e', ⌜prim_step p e σ e' σ'⌝ -∗  |={E}=> ▷ |={E}=>
                    (state_interp σ' ∗ wp E e' Φ)))))%I.

Local Instance wp_pre_contractive `{!indexT, !langG val Λ Σ, !invG Σ}
     {p:mixin_prog Λ.(func)} T : Contractive (wp_pre p T).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ. cbn in Hwp.
  repeat (f_contractive || f_equiv || apply Hwp || intros ?).
Qed.

Local Definition wp_def `{SI:indexT, !langG val Λ Σ, !invG Σ} : Wp (iProp Σ) (expr Λ) val (prog_environ Λ Σ) :=
  λ p : (prog_environ Λ Σ), fixpoint (wp_pre p.(penv_prog) p.(penv_proto)).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {SI val Λ Σ _ _}.
Global Existing Instance wp'.

Local Lemma wp_unseal `{SI:indexT, !langG val Λ Σ, !invG Σ} : wp = @wp_def SI val Λ Σ _ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.


Definition wp_func `{!indexT, !langG val Λ Σ, !invG Σ} (F:func Λ) (vv : list val) pe E Φ : iProp Σ :=
  match apply_func F vv with
    Some e' => |={E}=> ▷ |={E}=> wp' pe E e' Φ
  | None => ⌜False⌝%I end.

Notation "'WPFun' F 'with' args @ s ; E {{ Φ } }" := (wp_func F args%V s E Φ)
  (at level 20, F, args, Φ at level 200, only parsing) : bi_scope.
Notation "'WPFun' F 'with' args @ s ; E {{ v , Q } }" := (wp_func F args%V s E (λ v, Q))
  (at level 20, F, args, Q at level 200,
   format "'[hv' 'WPFun'  F  'with'  args  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.


Definition wp_for_call `{!indexT, !langG val Λ Σ, !invG Σ} (F:string) (vv : list val) pe E Φ : iProp Σ :=
  match penv_prog pe !! F with
  | Some F => wp_func F vv pe E Φ
  | None => ⌜False⌝%I end.

Notation "'WPCall' F 'with' args @ s ; E {{ Φ } }" := (wp_for_call F args%V s E Φ)
  (at level 20, F, args, Φ at level 200, only parsing) : bi_scope.
Notation "'WPCall' F 'with' args @ s ; E {{ v , Q } }" := (wp_for_call F args%V s E (λ v, Q))
  (at level 20, F, args, Q at level 200,
   format "'[hv' 'WPCall'  F  'with'  args  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Definition progwp `{!indexT, !langG val Λ Σ, !invG Σ}
  E (p : lang_prog Λ) (Ψ : protocol val Σ) : protocol val Σ
:=
  (λ fname vs Φ,
    ∃ fn, ⌜p !! fname = Some fn⌝ ∗
    ∃ e, ⌜apply_func fn vs = Some e⌝ ∗ ▷ WP e @ ⟨p, Ψ⟩; E {{ Φ }})%I.

Notation "Ψext '||-' p @ E '::' Ψp" := (Ψp ⊑ progwp E p Ψext)
  (at level 50, p, E, Ψp at level 51).

Notation "Ψext '||-' p '::' Ψp" := (Ψext ||- p @ ⊤ :: Ψp)
  (at level 50, p, Ψp at level 51).

Notation "'||-' p @ E '::' Ψp" := (∀ Ψext, Ψext ||- p @ E :: Ψp)
  (at level 50, p, E, Ψp at level 51).

Notation "'||-' p '::' Ψp" := (||- p @ ⊤ :: Ψp)
  (at level 50, p, Ψp at level 51).

Section wp.
Context `{SI:indexT, !langG val Λ Σ, !invG Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types Ψ : protocol val Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ Λ Σ.

(* Weakest pre *)
Lemma wp_unfold pe E e Φ :
  WP e @ pe; E {{ Φ }} ⊣⊢ wp_pre pe.(penv_prog) pe.(penv_proto) (wp (PROP:=iProp Σ) pe) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre pe.(penv_prog) pe.(penv_proto))). Qed.
Global Instance wp_ne pe E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) pe E e).
Proof.
  revert e. induction (index_lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 13 f_equiv. 1: do 6 f_equiv.
  all: f_contractive.
  all: f_equiv.
  all: f_equiv.
  1: f_equiv.
  all: apply IH; eauto; intros k; eapply dist_le', HΦ; eauto.
  all: by eapply index_lt_le_subrel.
Qed.
Global Instance wp_proper pe E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) pe E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Lemma wp_ne_proto n prog E e Φ:
  Proper ((dist n) ==> dist n) (λ (x:(string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ)), wp (Penv prog x) E e Φ).
Proof.
  revert E e Φ. induction (index_lt_wf n) as [n _ IH]=> e Φ Ψ.
  intros pp1 pp2 Hpp.
  rewrite !wp_unfold /wp_pre /=.
  do 13 f_equiv. 1: do 6 f_equiv. 1: apply Hpp.
  all: f_contractive.
  all: f_equiv.
  all: f_equiv.
  1: f_equiv.
  all: apply IH; eauto; intros k; eapply dist_le', Hpp; eauto.
  all: by eapply index_lt_le_subrel.
Qed.


(* TODO usually we show the other way around *)

Lemma wp_value_fupd' pe E Φ v : (|={E}=> Φ v)%I ⊢ WP (of_class Λ (ExprVal v)) @ pe; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ Hσ". iLeft. iMod "H". iModIntro. iExists _; iFrame; done.
Qed.

Lemma wp_strong_mono p Ψ1 Ψ2 E1 E2 e Φ Φ' :
  E1 ⊆ E2 → Ψ1 ⊑ Ψ2 →
  WP e @ ⟨p, Ψ1⟩; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Φ' v) -∗ WP e @ ⟨p, Ψ2⟩; E2 {{ Φ' }}.
Proof.
  iIntros (HE HΨ) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Φ').
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ Hσ". iSpecialize ("H" $! σ with "Hσ").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "H".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & -> & %H2 & H3)|H3]]".
  - iMod "Hclose". iLeft. iExists x. iFrame. iSplitR; first done. 
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _); first apply HE.
  - iRight; iLeft. iExists s, vv, K. iMod "H3". iMod "Hclose".
    iModIntro. iSplitR; first done. iSplitR; first (iPureIntro; congruence).
    iModIntro.
    iDestruct "H3" as "(%Ξ & Hσ & HT & Hr)".
    iExists Ξ. iFrame. iSplitL "HT"; first iApply (HΨ s vv with "HT").
    iNext. iIntros "%r HΞ". iApply ("IH" $! (fill K (of_class Λ (ExprVal r))) E1 E2 HE Φ Φ' with "[Hr HΞ] HΦ").
    iApply ("Hr" with "HΞ").
  - do 2 iRight. 
    iDestruct "H3" as "(HH & H3)".
    iMod "Hclose". iFrame. iModIntro. iIntros "%σ2 %e' Hstep".
    iSpecialize ("H3" $! σ2 e' with "Hstep").
    iMod (fupd_mask_subseteq E1) as "Hclose2"; first done. iMod "H3".
    iMod "Hclose2". iModIntro. iModIntro.
    iMod (fupd_mask_subseteq E1) as "Hclose2'"; first done.
    iMod "H3" as "(Hσ & HWP)".
    iMod "Hclose2'". iModIntro.
    iFrame. iApply ("IH" $! e' E1 E2 HE Φ Φ' with "HWP HΦ").
Qed.

Lemma wp_post_mono pe E e Φ Φ' :
  WP e @ pe; E {{ Φ }} -∗ (∀ v, Φ v ={E}=∗ Φ' v) -∗ WP e @ pe; E {{ Φ' }}.
Proof. destruct pe as [p Ψ]. by apply wp_strong_mono. Qed.

Lemma fupd_wp pe E e Φ : (|={E}=> WP e @ pe; E {{ Φ }}) ⊢ WP e @ pe; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H %σ Hσ".
  iMod "H". iApply ("H" $! σ with "Hσ").
Qed.

Lemma wp_fupd pe E e Φ : WP e @ pe; E {{ v, |={E}=> Φ v }} ⊢ WP e @ pe; E {{ Φ }}.
Proof.
  iIntros "H". destruct pe as [p Ψ].
  iApply (wp_strong_mono p Ψ Ψ E with "H"); by auto.
Qed.

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
    iApply (wp_post_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "H".
  iIntros (σ1) "Hσ".
  destruct (decide (n = 0)) as [->|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" $! σ1 with "Hσ") as "[(%z & -> & Hσ & H)|[(%s & %vv & %K & -> & H2 & H3)|(%Hred & H3)]]".
  + unfold to_val in Heq. rewrite to_of_class in Heq.
    exfalso. apply TCEq_eq in Heq. congruence.
  + cbn. iRight. iLeft. iMod "HP". iMod "H3" as "(%Φ' & Hσ & Hvv & HΦ')".
    iExists s, vv, K. iModIntro. iFrame. iSplitR; first done. iModIntro.
    iExists Φ'. iFrame. iNext.
    iIntros "%r Hr". iSpecialize ("HΦ'" $! r with "Hr").
    iApply (wp_post_mono with "HΦ' [HP]").
    iIntros "%v Hv". iMod ("Hv" with "HP") as "HP". do 2 iMod "HP". iModIntro. iAssumption.
  + iMod "HP". iModIntro. iRight. iRight. iSplitR; first done.
    iIntros "%σ' %e' %Hstep". iSpecialize ("H3" $! σ' e' Hstep). iMod "H3". iModIntro. iModIntro.
    iMod "H3" as "(Hσ' & H3)". do 2 iMod "HP". iModIntro.
    iFrame.
    iApply (wp_post_mono with "H3 [HP]").
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
  iIntros "%σ Hσ".
  iMod ("H" $! σ with "Hσ") as "[(%x & -> & Hσ & H)|[(%s & %vv & %K' & -> & H2 & H3)|H3]]".
  - rewrite {1} wp_unfold /wp_pre.
    iMod ("H" $! σ with "Hσ") as "H". iApply "H".
  - iMod "H3" as "(%Ξ & Hσ & HT & Hr)".
    iModIntro. iRight. iLeft. iExists s, vv, (comp_ectx K K'). 
    iFrame. iSplitR.
    {iPureIntro. now rewrite fill_comp. }
    iModIntro. iExists Ξ. iFrame. iNext.
    iIntros "%r HΞ".
    rewrite <- fill_comp.
    iApply "IH". iApply ("Hr" with "HΞ").
  - iRight. iRight. iModIntro. iDestruct "H3" as "(%Hred & H3)".
    iSplitR; first eauto using reducible_fill.
    iIntros "%σ' %e' %Hstep".
    pose proof (reducible_not_val _ _ _ Hred) as  Hnone.
    destruct (fill_step_inv _ _ _ _ _ _ Hnone Hstep) as (e2'' & -> & H4).
    iSpecialize ("H3" $! σ' e2'' H4). iMod "H3". do 2 iModIntro.
    iMod "H3" as "(Hσ & H3)". iModIntro. iFrame.
    iApply "IH". iApply "H3".
Qed.

Lemma wp_bind_inv K s E e Φ :
  WP fill K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP fill K (of_class _ (ExprVal v)) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H".
  iLöb as "IH" forall (E e Φ). do 2 rewrite {1} wp_unfold /wp_pre /=.
  assert ((exists v, e = of_val _ v) \/ (forall v, e <> of_val _ v)) as [[v Hv]|Hnv].
  1: { destruct (to_val e) as [v|] eqn:Heq.
       + left. exists v. now apply of_to_val in Heq.
       + right. intros v ->. rewrite to_of_val in Heq. congruence. }
  1: { rewrite Hv.
       iIntros "%σ Hσ". iModIntro. iLeft. iExists v. iFrame. iSplitR; first done.
       rewrite {1} wp_unfold /wp_pre /=. iApply "H". }
  iIntros "%σ Hσ".
  iMod ("H" $! σ with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]".
  - destruct (fill_class' K e) as [->|[v Hv]].
    + eexists. rewrite H1. now rewrite to_of_class.
    + rewrite fill_empty in H1. exfalso. eapply Hnv. apply H1.
    + apply of_to_class in Hv. exfalso. eapply Hnv. rewrite <- Hv. easy.
  - destruct (call_in_ctx _ _ _ _ _ H1) as [[K'' ->]|[x Hx]].
    + rewrite <- fill_comp in H1. apply fill_inj in H1. subst.
      iMod "H3" as "(%Ξ & Hσ & HT & Hr)".
      iRight. iLeft. iExists s', vv, K''.
      iSplitR; first done. iModIntro. iSplitR; first done.
      iModIntro. iExists Ξ. iFrame. iNext.
      iIntros (r) "HΞr".
      iApply "IH". rewrite fill_comp. by iApply "Hr".
    + unfold to_val in Hx. destruct (to_class e) as [[v|]|] eqn:Heq; try congruence.
      * exfalso. eapply Hnv. apply of_to_class in Heq. rewrite <- Heq. easy.
      * exfalso. rewrite <- Hx in Heq. rewrite to_of_class in Heq. congruence.
      * exfalso. rewrite <- Hx in Heq. rewrite to_of_class in Heq. congruence.
  - iModIntro.
    iRight. iRight. iSplitR. 1: iPureIntro.
    { destruct Hred as (e'&σ'&(e''&->&H2)%fill_step_inv). 1: by eexists e'',σ'.
      destruct (to_val e) eqn:Heq; try congruence. exfalso. apply (Hnv v). apply of_to_val in Heq. done. }
    iIntros (σ' e' Hred').
    iSpecialize ("H3" $! σ' _ (fill_prim_step _ K e _ _ _ Hred')). iMod "H3". do 2 iModIntro.
    iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame.
    iApply "IH". iFrame.
Qed.

(** * Derived rules *)
Lemma wp_mono pe E e Φ Φ' : (∀ v, Φ v ⊢ Φ' v) → WP e @ pe; E {{ Φ }} ⊢ WP e @ pe; E {{ Φ' }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_post_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_proto_mono p Ψ1 Ψ2 E e Φ :
  Ψ1 ⊑ Ψ2 → WP e @ ⟨p, Ψ1⟩; E {{ Φ }} ⊢ WP e @ ⟨p, Ψ2⟩; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_mask_mono pe E1 E2 e Φ : E1 ⊆ E2 → WP e @ pe; E1 {{ Φ }} ⊢ WP e @ pe; E2 {{ Φ }}.
Proof. destruct pe. iIntros (?) "H"; iApply (wp_strong_mono with "H"); by auto. Qed.
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
Proof. iIntros "[? H]". iApply (wp_post_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_post_mono with "H"); auto with iFrame. Qed.

Lemma wp_wand s E e Φ Φ' :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Φ' v) -∗ WP e @ s; E {{ Φ' }}.
Proof.
  iIntros "Hwp H". iApply (wp_post_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Φ' :
  (∀ v, Φ v -∗ Φ' v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ' }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Φ' :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Φ' v) ⊢ WP e @ s; E {{ Φ' }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.


Lemma wp_extern' pe n vv E Φ :
     ⌜penv_prog pe !! n = None⌝
  -∗ (|={E}=> penv_proto pe n vv Φ)
  -∗ WP of_class _ (ExprCall n vv) @ pe ; E {{ Φ }}.
Proof.
  iIntros (Hlookup) "HT".
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ Hσ". iMod "HT". iModIntro. iRight. iLeft.
  iExists _,_,empty_ectx. iSplitR.
  1: by rewrite fill_empty. iSplitR.
  1: done.
  iModIntro. iExists Φ. iFrame. iNext.
  iIntros (r) "Hr". rewrite fill_empty.
  by iApply wp_value'.
Qed.


Lemma wp_extern K pe n vv E Φ :
     ⌜penv_prog pe !! n = None⌝
  -∗ (|={E}=> penv_proto pe n vv (λ v, WP fill K (of_class Λ (ExprVal v)) @ pe; E {{ Φ }}))
  -∗ WP fill K (of_class _ (ExprCall n vv)) @ pe ; E {{ Φ }}.
Proof.
  iIntros (Hlookup) "HT".
  iApply wp_bind.
  iApply (wp_wand with "[HT]").
  1: iApply (wp_extern' with "[] [HT]"). 1: done. 1: iApply "HT".
  iIntros (v) "Hv"; iApply "Hv".
Qed.

Lemma wp_call pe n funn body' vv E Φ :
     ⌜penv_prog pe !! n = Some funn⌝
  -∗ ⌜apply_func funn vv = Some body'⌝
  -∗ (|={E}=> ▷ |={E}=> WP body' @ pe ; E {{ Φ }})
  -∗ WP of_class _ (ExprCall n vv) @ pe ; E {{ Φ }}.
Proof.
  iIntros (Hlookup Happly) "Hcont".
  rewrite (wp_unfold _ _ (of_class Λ (ExprCall n vv))) /wp_pre /=.
  iIntros "%σ Hσ". iMod "Hcont". do 2 iRight.
  iModIntro. iSplitR.
  { iPureIntro. apply head_prim_reducible.
    eexists _,_. apply call_head_step.
    eexists funn. done. }
  iIntros (σ' e' Hstep) "!>!>".
  apply head_reducible_prim_step in Hstep. 2: { eexists _,_. apply call_head_step; eexists funn; done. }
  apply call_head_step in Hstep. destruct Hstep as (fn' & Hfn' & He' & ->).
  iMod "Hcont".
  iModIntro. iFrame. assert (e' = body') as -> by congruence. done.
Qed.

Lemma wp_progwp pe n vv E Ψp Φ K :
     (penv_proto pe ||- penv_prog pe @ E :: Ψp)
  -> (|={E}=> Ψp n vv (λ v, WP fill K (of_class Λ (ExprVal v)) @ pe; E {{ Φ }}))
  -∗ WP fill K (of_class _ (ExprCall n vv)) @ pe ; E {{ Φ }}.
Proof.
  iIntros (Hprogwp) "HT".
  iApply wp_bind.
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ Hσ". iMod "HT".
  iPoseProof (Hprogwp with "HT") as "(%F&%HF&%e&%He&HT)".
  iModIntro. iRight. iRight.
  assert (head_reducible (penv_prog pe) (of_class Λ (ExprCall n vv)) σ) as Hhead.
  { do 2 eexists. eapply call_head_step. exists F; split_and!; done. }
  iSplit.
  1: iPureIntro; by eapply head_prim_reducible.
  iIntros (σ' e' (F2&HF2&He2&->)%head_reducible_prim_step%call_head_step_inv); last done.
  simplify_map_eq. assert (e = e') as <- by congruence.
  do 3 iModIntro. iFrame "Hσ". destruct pe; iApply "HT".
Qed.

Lemma progwp_mono E1 E2 Ψ1 Ψ2 p :
  E1 ⊆ E2 →
  Ψ1 ⊑ Ψ2 →
  progwp E1 p Ψ1 ⊑ progwp E2 p Ψ2.
Proof.
  iIntros (H1 H2 s vv Ψ) "(%F&%HF&%e&%He&HH)".
  iExists F. iSplit; first done.
  iExists e. iSplit; first done.
  iNext. iApply (wp_strong_mono with "HH"). 1: done. 1: done.
  by iIntros (v) "$".
Qed.

End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!indexT, !langG val Λ Σ, !invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Φ' :
    (∀ v, Frame p R (Φ v) (Φ' v)) →
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

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

End proofmode_classes.
