From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.interop Require Import linking.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.mlanguage Require Import weakestpre lifting.
From iris.proofmode Require Import proofmode.

(* FIXME: the proofs in this file need cleanup *)

Class state_interp_for_linking
      {val pubstate : Type} {Σ : gFunctors}
      (public_state_interp : pubstate → iProp Σ)
      (Λ : mlanguage val pubstate) (state_interp : state Λ → iProp Σ)
:= StateInterpForLinking {
  private_state_interp : Λ.(private_state) → iProp Σ;

  state_interp_split σ pubσ privσ :
    split_state σ pubσ privσ →
    state_interp σ ==∗ public_state_interp pubσ ∗ private_state_interp privσ;

  state_interp_join σ pubσ privσ :
    split_state σ pubσ privσ →
    public_state_interp pubσ ∗ private_state_interp privσ ==∗ state_interp σ
}.

Section Linking_logic.
Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context {val pubstate : Type}.
Context (Λ1 Λ2 : mlanguage val pubstate).

Context (public_state_interp : pubstate → iProp Σ).
Context (state_interp1 : state Λ1 → iProp Σ).
Context (state_interp2 : state Λ2 → iProp Σ).
Context (SIL1 : state_interp_for_linking public_state_interp Λ1 state_interp1).
Context (SIL2 : state_interp_for_linking public_state_interp Λ2 state_interp2).

Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.

Definition valid_split (Λ : mlanguage val pubstate)
                       (pubσ : pubstate) (privσ : Λ.(private_state)) : Prop :=
  ∃ σ, Λ.(split_state) σ pubσ privσ.

Class can_link_lang := CanLinkLangs {
  lang1_state_rel : Λ1.(state) → Λ1.(state) → Prop;
  lang2_state_rel : Λ2.(state) → Λ2.(state) → Prop;
  lang1_state_rel_refl :> Reflexive lang1_state_rel;
  lang2_state_rel_refl :> Reflexive lang2_state_rel;
  lang1_state_rel_trans :> Transitive lang1_state_rel;
  lang2_state_rel_trans :> Transitive lang2_state_rel;

  lang1_state_rel_step p e σ X :
    Λ1.(head_step) p (e, σ) X →
    Λ1.(head_step) p (e, σ) (λ '(e', σ'), X (e', σ') ∧ lang1_state_rel σ σ');
  lang2_state_rel_step p e σ X :
    Λ2.(head_step) p (e, σ) X →
    Λ2.(head_step) p (e, σ) (λ '(e', σ'), X (e', σ') ∧ lang2_state_rel σ σ');

  lang1_state_rel_valid_split σ1 pubσ privσ1 σ1' pubσ' privσ1' privσ2 :
    Λ1.(split_state) σ1 pubσ privσ1 →
    valid_split Λ2 pubσ privσ2 →
    lang1_state_rel σ1 σ1' →
    Λ1.(split_state) σ1' pubσ' privσ1' →
    valid_split Λ2 pubσ' privσ2;
  lang2_state_rel_valid_split σ2 pubσ privσ2 σ2' pubσ' privσ2' privσ1 :
    Λ2.(split_state) σ2 pubσ privσ2 →
    valid_split Λ1 pubσ privσ1 →
    lang2_state_rel σ2 σ2' →
    Λ2.(split_state) σ2' pubσ' privσ2' →
    valid_split Λ1 pubσ' privσ1;
}.

Lemma lang1_state_rel_prim_step `{can_link_lang} p e σ X :
  prim_step p (e, σ) X →
  prim_step p (e, σ) (λ '(e', σ'), X (e', σ') ∧ lang1_state_rel σ σ').
Proof using.
  intros (K & e' & -> & Hstep%lang1_state_rel_step). eexists; eauto.
Qed.
Lemma lang2_state_rel_prim_step `{can_link_lang} p e σ X :
  prim_step p (e, σ) X →
  prim_step p (e, σ) (λ '(e', σ'), X (e', σ') ∧ lang2_state_rel σ σ').
Proof using.
  intros (K & e' & -> & Hstep%lang2_state_rel_step). eexists; eauto.
Qed.

Context `{can_link_lang}.

Definition link_state_interp (st : (link_lang Λ1 Λ2).(state)) : iProp Σ :=
  match st with
  | LinkSt pubσ privσ1 privσ2 =>
      public_state_interp pubσ ∗
      private_state_interp privσ1 ∗
      private_state_interp privσ2 ∗
      ⌜valid_split Λ1 pubσ privσ1 ∧ valid_split Λ2 pubσ privσ2⌝
  | LinkSt1 σ1 privσ2 =>
      state_interp1 σ1 ∗ private_state_interp privσ2 ∗
      ⌜∃ σ1_0 pubσ0 privσ1_0,
          lang1_state_rel σ1_0 σ1 ∧
          Λ1.(split_state) σ1_0 pubσ0 privσ1_0 ∧
          valid_split Λ2 pubσ0 privσ2⌝

  | LinkSt2 privσ1 σ2 =>
      private_state_interp privσ1 ∗ state_interp2 σ2 ∗
      ⌜∃ σ2_0 pubσ0 privσ2_0,
          lang2_state_rel σ2_0 σ2 ∧
          Λ2.(split_state) σ2_0 pubσ0 privσ2_0 ∧
          valid_split Λ1 pubσ0 privσ1⌝
  end.

Instance link_melocotonGS {INVG: invGS_gen hlc Σ} :
  melocotonGS_gen hlc val pubstate (link_lang Λ1 Λ2) Σ
:= {
  iris_invGS := INVG;
  state_interp := link_state_interp;
}.

Lemma proj1_prog_union (pe1: mlanguage.prog Λ1) (pe2: mlanguage.prog Λ2) :
  dom pe1 ## dom pe2 →
  proj1_prog _ _ (fmap inl pe1 ∪ fmap inr pe2) = pe1.
Proof using.
  intros Hdisj.
  apply map_eq. intros fname. unfold proj1_prog.
  rewrite map_omap_union.
  2: { apply map_disjoint_dom. rewrite !dom_fmap//. }
  rewrite lookup_union_l.
  { rewrite lookup_omap /= lookup_fmap. by destruct (pe1 !! fname). }
  { rewrite lookup_omap /= lookup_fmap. by destruct (pe2 !! fname). }
Qed.

Lemma proj2_prog_union (pe1: mlanguage.prog Λ1) (pe2: mlanguage.prog Λ2) :
  dom pe1 ## dom pe2 →
  proj2_prog _ _ (fmap inl pe1 ∪ fmap inr pe2) = pe2.
Proof using.
  intros Hdisj.
  apply map_eq. intros fname. unfold proj2_prog.
  rewrite map_omap_union.
  2: { apply map_disjoint_dom. rewrite !dom_fmap//. }
  rewrite lookup_union_r.
  { rewrite lookup_omap /= lookup_fmap. by destruct (pe2 !! fname). }
  { rewrite lookup_omap /= lookup_fmap. by destruct (pe1 !! fname). }
Qed.

Definition link_environ (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
: @prog_environ _ _ _ (link_lang Λ1 Λ2) Σ (IrisG INVG link_state_interp) :=
{|
  prog := fmap inl (prog pe1) ∪ fmap inr (prog pe2);
  T := λ fname vs Φ,
    (⌜prog pe1 !! fname = None ∧ prog pe2 !! fname = None⌝ ∗
     (T pe1 fname vs Φ ∨ T pe2 fname vs Φ))%I;
|}.

Class can_link_prog (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
:= CanLinkProgs {
  can_link_disj :
    dom (prog pe1) ## dom (prog pe2);
  can_link_spec1 fname (func: mlanguage.func Λ2) vs Φ E :
      prog pe2 !! fname = Some func →
      T pe1 fname vs Φ -∗
      ∃ e2, ⌜apply_func func vs = Some e2⌝ ∗ ▷ WP e2 @ pe2; E {{ Φ }};
  can_link_spec2 fname (func: mlanguage.func Λ1) vs Φ E :
      prog pe1 !! fname = Some func →
      T pe2 fname vs Φ -∗
      ∃ e1, ⌜apply_func func vs = Some e1⌝ ∗ ▷ WP e1 @ pe1; E {{ Φ }};
}.

Lemma wp_link_call (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k fn vs (Φ : val → iProp Σ) fname
:
  let pe := link_environ INVG pe1 pe2 in
  prog pe !! fname = Some fn →
  WP LkE (LinkRunFunction Λ1 Λ2 fn vs) k @ pe; E {{ Φ }} -∗
  WP LkE (LinkExprCall Λ1 Λ2 fname vs) k @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe Hfn) "Hwp".
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch]". iModIntro. iRight; iRight.
  inversion Hmatch; subst.
  iSplitR.
  { iPureIntro. eexists (λ _, True). eexists k, (LkE _ []). split; first done.
    eapply CallS; eauto. }
  iIntros (X Hstep'). destruct Hstep' as (K' & [se1' k1'] & ? & Hstep'); simplify_eq.
  inversion Hstep'; simplify_eq; []. simplify_map_eq.
  iModIntro. iNext. iModIntro. iExists _, _. iSplitR; first done. iFrame.
Qed.

Lemma wp_link_run_function_1 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k2 k fn arg fname (Φ : val → iProp Σ) (Ξ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  can_link_prog INVG pe1 pe2 →
  prog pe1 !! fname = Some fn →
  T pe2 fname arg Ξ -∗
  (∀ e1, ⌜apply_func fn arg = Some e1⌝ -∗
         WP e1 @ pe1; E {{ v, Ξ v }} -∗
         WP LkE (LinkExpr1 Λ1 Λ2 e1) (inr k2 :: k) @ pe; E {{ Φ }}) -∗
  WP LkE (LinkRunFunction Λ1 Λ2 (inl fn) arg) (inr k2 :: k) @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe Hcan_link Hfn) "HTΞ Hwp".
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch]". inversion Hmatch; subst.
  iRight; iRight.
  iPoseProof (can_link_spec2 _ _ _ _ E Hfn with "HTΞ") as (? Happlyfunc) "Hwpcall".

  iDestruct "Hσ" as "(Hpubσ & Hprivσ1 & Hprivσ2 & %Hvsplit1 & %Hvsplit2)".
  iModIntro. iSplitR.
  { iPureIntro. destruct Hvsplit1 as (? & ?). exists (λ _, True). eexists _, (LkE _ []). split; [done|].
    eapply RunFunction1S; eauto. }
  iIntros (X Hstep'). destruct Hstep' as (K' & [se1' k1'] & ? & Hstep'). simpl in *; simplify_eq.
  inversion Hstep'; simplify_eq/=; []. iModIntro. iNext.
  iMod (@state_interp_join _ _ _ _ Λ1 with "[$Hprivσ1 $Hpubσ]") as "Hσ1". eassumption.
  iModIntro. iExists _, _. iSplitR; first done. iFrame "Hprivσ2 Hσ1". iSplitR.
  { iPureIntro. do 3 eexists. repeat split; eauto. reflexivity. }
  by iApply "Hwp".
Qed.

Lemma wp_link_run_function_2 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k1 k fn arg fname (Φ : val → iProp Σ) (Ξ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  can_link_prog INVG pe1 pe2 →
  prog pe2 !! fname = Some fn →
  T pe1 fname arg Ξ -∗
  (∀ e2, ⌜apply_func fn arg = Some e2⌝ -∗
         WP e2 @ pe2; E {{ v, Ξ v }} -∗
         WP LkE (LinkExpr2 Λ1 Λ2 e2) (inl k1 :: k) @ pe; E {{ Φ }}) -∗
  WP LkE (LinkRunFunction Λ1 Λ2 (inr fn) arg) (inl k1 :: k) @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe Hcan_link Hfn) "HTΞ Hwp".
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch]". inversion Hmatch; subst.
  iRight; iRight.
  iPoseProof (can_link_spec1 _ _ _ _ E Hfn with "HTΞ") as (? Happlyfunc) "Hwpcall".

  iDestruct "Hσ" as "(Hpubσ & Hprivσ1 & Hprivσ2 & %Hvsplit1 & %Hvsplit2)".
  iModIntro. iSplitR.
  { iPureIntro. destruct Hvsplit2 as (? & ?). exists (λ _, True). eexists _, (LkE _ []). split; [done|].
    eapply RunFunction2S; eauto. }
  iIntros (X Hstep'). destruct Hstep' as (K' & [se2' k2'] & ? & Hstep'). simpl in *; simplify_eq.
  inversion Hstep'; simplify_eq/=; []. iModIntro. iNext.
  iMod (@state_interp_join _ _ _ _ Λ2 with "[$Hprivσ2 $Hpubσ]") as "Hσ2". eassumption.
  iModIntro. iExists _, _. iSplitR; first done. iFrame "Hprivσ1 Hσ2". iSplitR.
  { iPureIntro. do 3 eexists. repeat split; eauto. reflexivity. }
  by iApply "Hwp".
Qed.

Lemma wp_link_retval_1 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k1 v (Φ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  WP LkSE (LinkExpr1 Λ1 Λ2 (fill k1 (of_val Λ1 v))) @ pe; E {{ Φ }} -∗
  WP LkE (LinkExprV Λ1 Λ2 v) [inl k1] @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe) "Hwp".
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch']". inversion Hmatch'; subst. iModIntro. iRight. iRight.
  iDestruct "Hσ" as "(Hpub & Hpriv1 & Hpriv2 & %Hvsplit1 & %Hvsplit2)".
  iSplitR.
  { iPureIntro. apply head_prim_reducible. destruct Hvsplit1 as [? ?].
    exists (λ _, True). eapply Ret1S; eauto. }
  iIntros (X Hstep'). destruct Hstep' as (K' & [se1' k1'] & ? & Hstep'). simplify_eq/=.
  inversion Hstep'; simplify_eq/=; [].
  iModIntro. iNext.
  iMod (@state_interp_join _ _ _ _ Λ1 with "[$Hpriv1 $Hpub]") as "H1". eassumption.
  iModIntro. iExists _, _. iSplitR; first done. iFrame "Hpriv2 H1". iSplitR.
  { iPureIntro. do 3 eexists. repeat split; eauto. reflexivity. }
  by iFrame.
Qed.

Lemma wp_link_retval_2 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k2 v (Φ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  WP LkSE (LinkExpr2 Λ1 Λ2 (fill k2 (of_val Λ2 v))) @ pe; E {{ Φ }} -∗
  WP LkE (LinkExprV Λ1 Λ2 v) [inr k2] @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe) "Hwp".
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch']". inversion Hmatch'; subst. iModIntro. iRight. iRight.
  iDestruct "Hσ" as "(Hpub & Hpriv1 & Hpriv2 & %Hvsplit1 & %Hvsplit2)".
  iSplitR.
  { iPureIntro. apply head_prim_reducible. destruct Hvsplit2 as [? ?].
    eexists (λ _, True). eapply Ret2S; eauto. }
  iIntros (X Hstep'). destruct Hstep' as (K' & [se2' k2'] & ? & Hstep'). simplify_eq/=.
  inversion Hstep'; simplify_eq/=; [].
  iModIntro. iNext.
  iMod (@state_interp_join _ _ _ _ Λ2 with "[$Hpriv2 $Hpub]") as "H2". eassumption.
  iModIntro. iExists _, _. iSplitR; first done. iFrame "Hpriv1 H2". iSplitR.
  { iPureIntro. do 3 eexists. repeat split; eauto. reflexivity. }
  by iFrame.
Qed.

Lemma wp_link_extcall_1 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k1 fn_name arg (Φ : val → iProp Σ) (Ξ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  prog pe1 !! fn_name = None →
  prog pe2 !! fn_name = None →
  T pe1 fn_name arg Ξ -∗
  (▷ ∀ r : val, Ξ r -∗ WP fill (comp_ectx k1 empty_ectx) (of_class Λ1 (ExprVal r)) @ pe1; E {{ Φ }}) -∗
  (▷ ∀ r, WP fill k1 (of_class Λ1 (ExprVal r)) @ pe1; E {{ Φ }} -∗
        WP LkE (LinkExprV Λ1 Λ2 r) [inl k1] @ pe; E {{ Φ }}) -∗
  WP LkE (LinkExprCall Λ1 Λ2 fn_name arg) [inl k1] @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe Hfn1 Hfn2) "HTΞ HΞ Hwp".
  assert (Hpef: prog pe !! fn_name = None).
  { apply lookup_union_None. rewrite !lookup_fmap Hfn1 Hfn2 //. }
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch']". inversion Hmatch'; subst.
  iModIntro. iRight; iLeft. iExists _, _, [inl k1]. iSplitR; [by eauto|].
  iSplitR; first by eauto. iModIntro. iFrame "Hσ". iExists Ξ. iSplitL "HTΞ".
  { rewrite /pe /=. iSplitR; [now iPureIntro; split; eauto|]. iLeft. iApply "HTΞ". }
  iNext. iIntros (r) "Hr". simpl. iSpecialize ("HΞ" with "Hr"). rewrite -fill_comp fill_empty.
  by iApply "Hwp".
Qed.

Lemma wp_link_extcall_2 (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E k2 fn_name arg (Φ : val → iProp Σ) (Ξ : val → iProp Σ)
:
  let pe := link_environ INVG pe1 pe2 in
  prog pe1 !! fn_name = None →
  prog pe2 !! fn_name = None →
  T pe2 fn_name arg Ξ -∗
  (▷ ∀ r : val, Ξ r -∗ WP fill (comp_ectx k2 empty_ectx) (of_class Λ2 (ExprVal r)) @ pe2; E {{ Φ }}) -∗
  (▷ ∀ r, WP fill k2 (of_class Λ2 (ExprVal r)) @ pe2; E {{ Φ }} -∗
        WP LkE (LinkExprV Λ1 Λ2 r) [inr k2] @ pe; E {{ Φ }}) -∗
  WP LkE (LinkExprCall Λ1 Λ2 fn_name arg) [inr k2] @ pe; E {{ Φ }}.
Proof using.
  iIntros (pe Hfn1 Hfn2) "HTΞ HΞ Hwp".
  assert (Hpef: prog pe !! fn_name = None).
  { apply lookup_union_None. rewrite !lookup_fmap Hfn1 Hfn2 //. }
  iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
  iIntros (σ) "[Hσ %Hmatch']". inversion Hmatch'; subst.
  iModIntro. iRight; iLeft. iExists _, _, [inr k2]. iSplitR; [by eauto|].
  iSplitR; first by eauto.
  iModIntro. iFrame "Hσ". iExists Ξ. iSplitL "HTΞ".
  { rewrite /pe /=. iSplitR; [now iPureIntro; split; eauto|]. iRight. iApply "HTΞ". }
  iNext. iIntros (r) "Hr". simpl. iSpecialize ("HΞ" with "Hr"). rewrite -fill_comp fill_empty.
  by iApply "Hwp".
Qed.

Lemma link_head_step_call_ext_1_inv INVG pe1 pe2 K f vs σ1 privσ2 X :
  let pe := link_environ INVG pe1 pe2 in
  can_link_prog INVG pe1 pe2 →
  prog pe1 !! f = None →
  head_step (prog pe) (LkSE (LinkExpr1 Λ1 Λ2 (fill K (of_class Λ1 (ExprCall f vs)))),
                       LinkSt1 σ1 privσ2) X →
  ∃ pubσ privσ1 k,
    K = comp_ectx k empty_ectx ∧
    X (LkE (LinkExprCall Λ1 Λ2 f vs) [inl k], LinkSt pubσ privσ1 privσ2) ∧
    split_state σ1 pubσ privσ1.
Proof using.
  intros pe Hcan_link Hf Hstep. inversion Hstep; subst; simplify_eq.
  { exfalso.
    match goal with H:_|-_ => eapply call_prim_step_fill in H as (?&?&HH&?&_) end.
    rewrite proj1_prog_union in HH; [| apply Hcan_link]. congruence. }
  { exfalso. match goal with H:_|-_ => apply mk_is_Some in H; apply fill_val in H; destruct H as [? HH] end.
    rewrite /to_val to_of_class // in HH. }
  rename H0 into Hfill. rename H4 into Hnofn. rewrite proj1_prog_union in Hnofn;[|apply Hcan_link].
  pose proof (call_in_ctx_to_val _ _ _ _ _ Hfill) as [[K'' ->]|Hval].
  2: { exfalso. unfold to_val in Hval. destruct Hval. by repeat case_match. }
  rewrite -fill_comp in Hfill. apply fill_inj in Hfill. subst e1.
  unshelve epose proof (fill_class' K'' _ _) as HH;[shelve|eexists; eassumption|]. (* XX *)
  destruct HH as [->|[? HH]].
  2: { exfalso. rewrite to_of_class in HH. congruence. }
  do 3 eexists; repeat split; eauto.
  rewrite fill_empty to_of_class in H3. by simplify_eq/=.
Qed.

Lemma link_head_step_call_ext_2_inv INVG pe1 pe2 K f vs σ2 privσ1 X :
  let pe := link_environ INVG pe1 pe2 in
  can_link_prog INVG pe1 pe2 →
  prog pe2 !! f = None →
  head_step (prog pe) (LkSE (LinkExpr2 Λ1 Λ2 (fill K (of_class Λ2 (ExprCall f vs)))),
                       LinkSt2 privσ1 σ2) X →
  ∃ pubσ privσ2 k,
    K = comp_ectx k empty_ectx ∧
    X (LkE (LinkExprCall Λ1 Λ2 f vs) [inr k], LinkSt pubσ privσ1 privσ2) ∧
    split_state σ2 pubσ privσ2.
Proof using.
  intros pe Hcan_link Hf Hstep. inversion Hstep; subst; simplify_eq.
  { exfalso. match goal with H:_|-_ => eapply call_prim_step_fill in H as (?&?&HH&?&_) end.
    rewrite proj2_prog_union in HH; [| apply Hcan_link]. congruence. }
  { exfalso. match goal with H:_|-_ => apply mk_is_Some in H; apply fill_val in H; destruct H as [? HH] end.
    rewrite /to_val to_of_class // in HH. }
  rename H0 into Hfill. rename H4 into Hnofn. rewrite proj2_prog_union in Hnofn;[|apply Hcan_link].
  pose proof (call_in_ctx_to_val _ _ _ _ _ Hfill) as [[K'' ->]|Hval].
  2: { exfalso. unfold to_val in Hval. destruct Hval. by repeat case_match. }
  rewrite -fill_comp in Hfill. apply fill_inj in Hfill. subst e2.
  unshelve epose proof (fill_class' K'' _ _) as HH;[shelve|eexists; eassumption|]. (* XX *)
  destruct HH as [->|[? HH]].
  2: { exfalso. rewrite to_of_class in HH. congruence. }
  do 3 eexists; repeat split; eauto.
  rewrite fill_empty to_of_class in H3. by simplify_eq/=.
Qed.

Lemma wp_link_run (INVG: invGS_gen hlc Σ)
  (pe1 : @prog_environ hlc _ _ Λ1 Σ (IrisG INVG state_interp1))
  (pe2 : @prog_environ hlc _ _ Λ2 Σ (IrisG INVG state_interp2))
  E
:
  let pe := link_environ INVG pe1 pe2 in
  can_link_prog INVG pe1 pe2 →
  ⊢ □ (
    (∀ e1 Φ, WP e1 @ pe1; E {{ Φ }} -∗
             WP (LkSE (LinkExpr1 Λ1 Λ2 e1)) @ pe; E {{ Φ }}) ∗
    (∀ e2 Φ, WP e2 @ pe2; E {{ Φ }} -∗
             WP (LkSE (LinkExpr2 Λ1 Λ2 e2)) @ pe; E {{ Φ }})
  ).
Proof using.
  intros pe Hcan_link. iLöb as "IH". iModIntro. iSplitL.
  (* Case 1: running Λ1 *)
  { iIntros (e1 Φ) "Hwp".
    rewrite wp_unfold. rewrite /wp_pre.
    iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
    iIntros (σ) "[Hσ %Hmatch]".
    inversion Hmatch; subst. iDestruct "Hσ" as "(Hσ1 & Hpriv2 & %Hvsplit)".
    iMod ("Hwp" $! σ1 with "[$Hσ1]") as "[Hwp|[Hwp|Hwp]]"; first done.

    (* WP: value case *)
    { iDestruct "Hwp" as (v ->) "[Hσ HΦ]". iModIntro. iRight; iRight.
      (* administrative step Val1S: LinkExpr1 ~> LinkExprV *)
      assert (Hhred: head_reducible (prog pe) (LkSE (LinkExpr1 Λ1 Λ2 (of_class Λ1 (ExprVal v)))) (LinkSt1 σ1 privσ2)).
      { destruct (val_matching_split _ _ ltac:(eassumption)) as (pubσ&privσ1&Hsplitσ1).
        exists (λ _, True). eapply Val1S; eauto. rewrite /to_val to_of_class //=. }
      iSplitR; [iPureIntro; by apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep; [|done].
      inversion Hstep; simplify_eq/=.
      { exfalso. by match goal with H:_ |- _ => apply val_prim_step in H end. }
      { rewrite /to_val to_of_class in H4; simplify_eq/=.
        iMod (@state_interp_split _ _ _ public_state_interp Λ1 with "Hσ") as "[Hpriv1 Hpub]"; first by eauto.
        iExists _, _. iSplitR; first done. iFrame. do 3 iModIntro.
        iSplitR.
        { iPureIntro. split; first by (eexists; eauto).
          destruct Hvsplit as (σ1_0 & pubσ0 & privσ1_0 & Hrel0 & Hsplit0 & Hvsplit).
          eapply (lang1_state_rel_valid_split σ1_0); eauto. }
        by iApply wp_value. }
      { exfalso.
        assert (is_Some (to_val e1)) as [? ?].
        { eapply fill_val. eexists. unfold to_val. erewrite H0. rewrite to_of_class//. }
        unfold to_val in H1. repeat case_match; congruence. } }

    (* WP: call case *)
    { iDestruct "Hwp" as (f vs K -> Hf) "Hcall". iModIntro. iRight; iRight.
      (* administrative step MakeCall1S: LinkExpr1 ~> LinkExprCall *)
      assert (head_reducible (prog pe) (LkSE (LinkExpr1 Λ1 Λ2 (fill K (of_class Λ1 (ExprCall f vs))))) (LinkSt1 σ1 privσ2)).
      { apply matching_expr_state_ctx in H3.
        destruct (call_matching_split _ _ _ ltac:(eassumption)) as (?&?&?).
        exists (λ _, True). eapply MakeCall1S; eauto. by rewrite to_of_class.
        rewrite proj1_prog_union; [done | apply Hcan_link]. }
      iSplitR; [iPureIntro; by apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep;[|done].
      eapply link_head_step_call_ext_1_inv in Hstep as (pubσ&privσ1&k1&->&?&?); eauto.

      iMod "Hcall" as "[Hσ Hcall]". iDestruct "Hcall" as (Ξ) "[HTΞ HΞ]".
      iMod (@state_interp_split _ _ _ public_state_interp Λ1 with "Hσ") as "[Hpriv1 Hpub]"; eauto.
      iModIntro. iNext. iModIntro. iExists _, _. iSplitR; first done. iFrame. iSplitR.
      { iPureIntro. split; first by (eexists; eauto).
        destruct Hvsplit as (σ1_0 & pubσ0 & privσ1_0 & Hrel0 & Hsplit0 & Hvsplit).
        eapply (lang1_state_rel_valid_split σ1_0); eauto. }

      (* two cases: this is an external call of the linking module itself, or it
         is a call to a function of pe2 *)
      destruct (prog pe2 !! f) as [fn2|] eqn:Hf2.

      { (* call to a function of pe2 *)
        assert (prog pe !! f = Some (inr fn2)) as Hpef.
        { rewrite lookup_union_r lookup_fmap. by rewrite Hf2. by rewrite Hf. }

        (* administrative step CallS: LinkExprCall ~> LinkRunFunction *)
        iApply wp_link_call; first done.
        (* administrative step RunFunction2S: LinkRunFunction ~> LinkExpr2 *)
        iApply (wp_link_run_function_2 with "HTΞ"); first done. iIntros (e2 He2) "Hwpcall".

        progress change (LkE (LinkExpr2 Λ1 Λ2 e2) [inl k1]) with
          (linking.fill _ _ ([inl k1]:ectx (link_lang Λ1 Λ2)) (LkSE (LinkExpr2 Λ1 Λ2 e2))).
        iApply (@wp_bind _ _ _ (link_lang Λ1 Λ2)).
        iApply ((@wp_wand _ _ _ (link_lang Λ1 Λ2)) with "[Hwpcall]").
        { iDestruct "IH" as "#[_ IH2]". iApply "IH2". iApply "Hwpcall". }
        iIntros (r) "Hr". iSpecialize ("HΞ" with "Hr"). rewrite -fill_comp fill_empty. simpl.

        (* administrative step Ret1S: LinkExprV ~> LinkExpr1 *)
        iApply wp_link_retval_1.
        (* continue the execution by induction *)
        iDestruct "IH" as "#[IH1 _]". iApply "IH1". unfold of_val. done. }

      { (* external call *)
        iApply (wp_link_extcall_1 with "HTΞ HΞ"); auto. iNext.
        iIntros (r) "HΞ".
        (* administrative step Ret1S: LinkExprV ~> LinkExpr1 *)
        iApply wp_link_retval_1.
        (* continue the execution by induction *)
        iDestruct "IH" as "#[IH1 _]". iApply "IH1". unfold of_val. done. } }

    { (* WP: step case *)
      iDestruct "Hwp" as (Hred) "Hwp". iModIntro. iRight; iRight.
      assert (head_reducible (prog pe) (LkSE (LinkExpr1 Λ1 Λ2 e1)) (LinkSt1 σ1 privσ2)).
      { destruct Hred as (? & Hstep). exists (λ _, True).
        eapply Step1S. rewrite proj1_prog_union; [| apply Hcan_link]. all: eauto. }
      iSplitR; [by iPureIntro; apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep;[|done].
      inversion Hstep; simplify_eq.
      { (* non-vacuous case: step in Λ1 *)
        clear Hstep. rename H6 into Hstep. apply lang1_state_rel_prim_step in Hstep.
        rewrite proj1_prog_union in Hstep; [|apply Hcan_link].
        iSpecialize ("Hwp" $! _ Hstep). iMod "Hwp". iIntros "!>!>". iMod "Hwp" as (e' σ' [HX HrX]) "[Hσ Hwp]".
        iModIntro. iExists _, _. iSplitR; [iPureIntro; naive_solver|].
        iSplitL "Hσ Hpriv2".
        { simpl. iFrame. iPureIntro. destruct Hvsplit as (σ1_0 & pubσ0 & privσ1_0 & Hrel0 & Hsplit0 & Hvsplit).
          eexists σ1_0, pubσ0, _. repeat split; eauto. etransitivity; eauto. }
        iDestruct "IH" as "[IH1 _]". iApply ("IH1" with "Hwp"). }
      { exfalso. apply reducible_not_val in Hred. congruence. }
      { exfalso. clear Hstep. erewrite <-(of_to_class e0) in Hred; [|eassumption].
        rewrite proj1_prog_union in H6;[|apply Hcan_link].
        destruct Hred as (?&Hred). eapply extcall_ctx_irreducible; eauto. } } }

  (* Case 2: running Λ2 *)
  { iIntros (e2 Φ) "Hwp".
    rewrite wp_unfold. rewrite /wp_pre.
    iApply (@wp_unfold _ _ _ (link_lang Λ1 Λ2)). rewrite /wp_pre.
    iIntros (σ) "[Hσ %Hmatch]".
    inversion Hmatch; subst. iDestruct "Hσ" as "(Hprivσ1 & Hσ2 & %Hvsplit)".
    iMod ("Hwp" $! σ2 with "[$Hσ2]") as "[Hwp|[Hwp|Hwp]]"; first done.

    (* WP: value case *)
    { iDestruct "Hwp" as (v ->) "[Hσ HΦ]". iModIntro. iRight; iRight.
      (* administrative step Val2S: LinkExpr2 ~> LinkExprV *)
      assert (Hhred: head_reducible (prog pe) (LkSE (LinkExpr2 Λ1 Λ2 (of_class Λ2 (ExprVal v)))) (LinkSt2 privσ1 σ2)).
      { destruct (val_matching_split _ _ ltac:(eassumption)) as (?&?&?).
        exists (λ _, True). eapply Val2S; eauto. rewrite /to_val to_of_class //=. }
      iSplitR; [iPureIntro; by apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep; [|done].
      inversion Hstep; simplify_eq/=.
      { exfalso. by match goal with H:_ |- _ => apply val_prim_step in H end. }
      { rewrite /to_val to_of_class in H4; simplify_eq/=.
        iMod (@state_interp_split _ _ _ public_state_interp Λ2 with "Hσ") as "[Hpriv2 Hpub]"; first by eauto.
        iExists _, _. iSplitR; first done. iFrame. iModIntro. iNext. iModIntro.
        iSplitR.
        { iPureIntro. split; last by (eexists; eauto).
          destruct Hvsplit as (σ2_0 & pubσ0 & privσ2_0 & Hrel0 & Hsplit0 & Hvsplit).
          eapply (lang2_state_rel_valid_split σ2_0); eauto. }
        by iApply wp_value. }
      { exfalso.
        assert (is_Some (to_val e2)) as [? ?].
        { eapply fill_val. eexists. unfold to_val. erewrite H0. rewrite to_of_class//. }
        unfold to_val in H1. repeat case_match; congruence. } }

    (* WP: call case *)
    { iDestruct "Hwp" as (f vs K -> Hf) "Hcall". iModIntro. iRight; iRight.
      (* administrative step MakeCall1S: LinkExpr2 ~> LinkExprCall *)
      assert (head_reducible (prog pe) (LkSE (LinkExpr2 Λ1 Λ2 (fill K (of_class Λ2 (ExprCall f vs))))) (LinkSt2 privσ1 σ2)).
      { apply matching_expr_state_ctx in H3.
        destruct (call_matching_split _ _ _ ltac:(eassumption)) as (?&?&?).
        exists (λ _, True). eapply MakeCall2S; eauto. by rewrite to_of_class.
        rewrite proj2_prog_union; [done | apply Hcan_link]. }
      iSplitR; [iPureIntro; by apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep;[|done].
      eapply link_head_step_call_ext_2_inv in Hstep as (pubσ&privσ2&k2&->&?&?); eauto.

      iMod "Hcall" as "[Hσ Hcall]". iDestruct "Hcall" as (Ξ) "[HTΞ HΞ]".
      iMod (@state_interp_split _ _ _ public_state_interp Λ2 with "Hσ") as "[Hpub Hpriv2]"; eauto.
      iModIntro. iNext. iModIntro. iExists _, _. iSplitR; first done. iFrame. iSplitR.
      { iPureIntro. split; last by (eexists; eauto).
        destruct Hvsplit as (σ2_0 & pubσ0 & privσ2_0 & Hrel0 & Hsplit0 & Hvsplit).
        eapply (lang2_state_rel_valid_split σ2_0); eauto. }

      (* two cases: this is an external call of the linking module itself, or it
         is a call to a function of pe2 *)
      destruct (prog pe1 !! f) as [fn1|] eqn:Hf1.

      { (* call to a function of pe1 *)
        assert (prog pe !! f = Some (inl fn1)) as Hpef.
        { rewrite lookup_union_l lookup_fmap. by rewrite Hf1. by rewrite Hf. }

        (* administrative step CallS: LinkExprCall ~> LinkRunFunction *)
        iApply wp_link_call; first done.
        (* administrative step RunFunction1S: LinkRunFunction ~> LinkExpr1 *)
        iApply (wp_link_run_function_1 with "HTΞ"); first done. iIntros (e1 He1) "Hwpcall".

        progress change (LkE (LinkExpr1 Λ1 Λ2 e1) [inr k2]) with
          (linking.fill _ _ ([inr k2]:ectx (link_lang Λ1 Λ2)) (LkSE (LinkExpr1 Λ1 Λ2 e1))).
        iApply (@wp_bind _ _ _ (link_lang Λ1 Λ2)).
        iApply ((@wp_wand _ _ _ (link_lang Λ1 Λ2)) with "[Hwpcall]").
        { iDestruct "IH" as "#[IH1 _]". iApply "IH1". iApply "Hwpcall". }
        iIntros (r) "Hr". iSpecialize ("HΞ" with "Hr"). rewrite -fill_comp fill_empty. simpl.

        (* administrative step Ret2S: LinkExprV ~> LinkExpr2 *)
        iApply wp_link_retval_2.
        (* continue the execution by induction *)
        iDestruct "IH" as "#[_ IH2]". iApply "IH2". unfold of_val. done. }

      { (* external call *)
        iApply (wp_link_extcall_2 with "HTΞ HΞ"); auto. iNext.
        iIntros (r) "HΞ".
        (* administrative step Ret1S: LinkExprV ~> LinkExpr1 *)
        iApply wp_link_retval_2.
        (* continue the execution by induction *)
        iDestruct "IH" as "#[_ IH2]". iApply "IH2". unfold of_val. done. } }

    { (* WP: step case *)
      iDestruct "Hwp" as (Hred) "Hwp". iModIntro. iRight; iRight.
      assert (head_reducible (prog pe) (LkSE (LinkExpr2 Λ1 Λ2 e2)) (LinkSt2 privσ1 σ2)).
      { destruct Hred as (? & Hstep).
        exists (λ _, True). eapply Step2S. rewrite proj2_prog_union; [| apply Hcan_link].
        all: eauto. }
      iSplitR; [by iPureIntro; apply head_prim_reducible|].
      iIntros (X Hstep). apply head_reducible_prim_step in Hstep;[|done].
      inversion Hstep; simplify_eq.
      { (* non-vacuous case: step in Λ2 *)
        clear Hstep. rename H6 into Hstep. apply lang2_state_rel_prim_step in Hstep.
        rewrite proj2_prog_union in Hstep; [|apply Hcan_link].
        iSpecialize ("Hwp" $! _ Hstep). iMod "Hwp". iIntros "!>!>". iMod "Hwp" as (e' σ' [HX HrX]) "[Hσ Hwp]".
        iModIntro. iExists _, _. iSplitR; [iPureIntro; naive_solver|]. iSplitL "Hσ Hprivσ1".
        { simpl. iFrame. iPureIntro. destruct Hvsplit as (σ2_0 & pubσ0 & privσ2_0 & Hrel0 & Hsplit0 & Hvsplit).
          eexists σ2_0, pubσ0, _. repeat split; eauto. etransitivity; eauto. }
        iDestruct "IH" as "[_ IH2]". iApply ("IH2" with "Hwp"). }
      { exfalso. apply reducible_not_val in Hred. congruence. }
      { exfalso. clear Hstep. erewrite <-(of_to_class e0) in Hred; [|eassumption].
        rewrite proj2_prog_union in H6;[|apply Hcan_link].
        destruct Hred as (?&Hred). eapply extcall_ctx_irreducible; eauto. } } }
Qed.

End Linking_logic.
