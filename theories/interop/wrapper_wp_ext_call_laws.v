From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem basics_resources wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws notation.
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim wrapper_wp_utils.
Import Wrap.

Section Laws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Context (p : language.prog C_lang).
Context (Hforbid : Forall (fun k => p !! k = None) forbidden_function_names).

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.
Import mlanguage.


Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ _ Σ).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang Σ).

Notation wrap_return := (fun Φ (a:Cval) => (∃ θ' l v, GC θ' ∗ Φ v ∗ ⌜repr_lval θ' l a⌝ ∗ block_sim v l)%I).
(* TODO move store / load somewhere else *)
Lemma store_to_root E (l:loc) (v v' : lval) w θ :
  {{{GC θ ∗ l ↦roots v' ∗ ⌜repr_lval θ v w⌝}}}
     (#l <- w)%E @ (mkPeC p WP_ext_call_spec); E
  {{{ RET LitV LitUnit; l ↦roots v ∗ GC θ }}}.
Proof.
  iIntros (Φ) "(HGC&Hroots&%Hrepr) HΦ".
  iNamed "HGC".
  iPoseProof (ghost_map_lookup with "HArootsm Hroots") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first apply H.
  iPoseProof ("HL" with "Hrootspto") as "((%w'&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iMod (ghost_map_update with "HArootsm Hroots") as "(HArootsm&Hroots)".
  iApply (wp_store with "Hown").
  iIntros "!> Hown". iApply "HΦ".
  iFrame "Hroots".
  do 2 iExists _.
  iFrame.
  rewrite dom_insert_lookup_L; last done. iSplitR; first done.
  iSplitR.
  - iPureIntro. intros l' γ [[-> ->]|[Hne HH]]%lookup_insert_Some.
    2: by eapply Hrootslive.
    inversion Hrepr; subst. by eapply elem_of_dom_2.
  - iPoseProof (big_sepM_insert_delete) as "(_&HR)"; iApply "HR"; iClear "HR".
    iSplitL "Hown"; last done.
    iExists w. iFrame. done.
Qed.

Lemma load_from_root E (l:loc) (v : lval) dq θ :
  {{{GC θ ∗ l ↦roots{dq} v}}}
     ( * #l)%E @ (mkPeC p WP_ext_call_spec); E
  {{{ w, RET w; l ↦roots{dq} v ∗ GC θ ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iNamed "HGC".
  iPoseProof (ghost_map_lookup with "HArootsm Hroot") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&HR)"; first apply H.
  iPoseProof ("HL" with "Hrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iApply (wp_load with "Hown").
  iIntros "!> Hown". iApply "HΦ".
  iFrame "Hroot". iSplitL; last done.
  iPoseProof ("HR" with "[Hown Hrp]") as "Hrootsm"; iClear "HR".
  - iFrame. iExists w; by iFrame.
  - do 2 iExists _. iFrame. done.
Qed.


Notation fillCCall K s vv := (language.fill K (language.of_class C_lang (ExprCall s (vv:list Cval)))).

Definition ext_call_is_sound (Hspec : string -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ) :=
  forall E T s (vv:list Cval) K Ξ Φ,
    ⌜p !! s = None⌝
 -∗ not_at_boundary
 -∗ Hspec s vv Ξ
 -∗ ▷ (∀ r, Ξ r -∗ not_at_boundary -∗ WP (ExprC (language.fill K (language.of_class C_lang (ExprVal r)))) @ (mkPeW (p : prog wrap_lang) T); E {{v, Φ v }})
 -∗ WP (ExprC (fillCCall K s vv)) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v}}.


Lemma wp_ext_call_int2val : ext_call_is_sound WP_int2val_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. unfold WP_int2val_spec. iNamed "HT". iNamed "HGC".
    iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%H"; subst θ.
    iModIntro. iRight. iRight. iSplitR.
    + iPureIntro. econstructor. eapply head_prim_step.
      eapply (PrimInt2valS _ _ _ _ _ _ _ (fun k => True)).
      2: econstructor. 2: done.
      cbn. done.
    + iIntros (X Hstep).
      destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
      cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
      inversion_call_step Hstep ([ #z]).
      do 3 iModIntro.
      do 2 iExists _. change (Wrap.fill () ?x) with (x) in H5.
      iSplitR; first (iPureIntro; eapply H5).
      iSplitR "Hnb IH HWP HAGCθ HAGCbound HArootss HArootsm Hrootspto".
      * cbn. unfold C_state_interp. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
        repeat iExists _. iFrame. iSplitL; first by iExists _. iPureIntro; done.
      * iApply ("IH" with "[-Hnb] Hnb").
        iApply ("HWP" with "[-]"); last done.
        do 2 iExists _; iFrame. done.
Qed.

Lemma wp_ext_call_val2int : ext_call_is_sound WP_val2int_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. unfold WP_val2int_spec. iNamed "HT". iNamed "HGC".
    iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%H"; subst θ.
    iModIntro. iRight. iRight. iSplitR.
    + iPureIntro. econstructor. eapply head_prim_step.
      eapply (PrimVal2intS _ _ _ _ _ _ _ (fun k => True)). 2: apply Hrepr. all:done.
    + iIntros (X Hstep).
      destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
      cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
      inversion_call_step Hstep ([w]).
      do 3 iModIntro.
      do 2 iExists _. change (Wrap.fill () ?x) with (x) in H5.
      iSplitR; first (iPureIntro; eapply H5).
      iSplitR "Hnb IH HWP HAGCθ HAGCbound HArootss HArootsm Hrootspto".
      * cbn. unfold C_state_interp. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
        repeat iExists _. iFrame. iSplitL; first by iExists _. iPureIntro; done.
      * iApply ("IH" with "[-Hnb] Hnb"). inversion Hrepr; inversion H4; subst; rewrite ! H10.
        iApply ("HWP").
        do 2 iExists _; iFrame. done.
Qed.

Lemma wp_ext_call_registerroot : ext_call_is_sound WP_registerroot_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. unfold WP_registerroot_spec. iNamed "HT". iNamed "HGC".
  iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%H"; subst θ.

  iAssert (⌜l ∈ dom roots_m⌝ → False)%I as "%Hdom".
  1: { iIntros "%H". eapply elem_of_dom in H; destruct H as [k Hk].
       iPoseProof (big_sepM_lookup_acc with "Hrootspto") as "((%ww&Hww&_)&_)".
       1: apply Hk. iPoseProof (mapsto_ne with "Hpto Hww") as "%Hne". congruence. }
  iPoseProof (ghost_var_agree with "HAroots HArootss") as "%Heq"; subst roots_s.

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimRegisterrootS _ _ _ _ _ _ _ (fun k => True)). 1,3,4: done.
    intros H; apply Hdom; congruence.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ #l ]). subst.

    iMod (ghost_var_update_halves with "HAroots HArootss") as "(HAroots&HArootss)".
    iMod (ghost_map_insert with "HArootsm") as "(HArootsm&Hres)". 
    1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
    iPoseProof (big_sepM_insert) as "(_&HR)".
    1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
    iPoseProof ("HR" with "[Hpto Hrootspto]") as "Hrootspto"; first iFrame "Hrootspto".
    iExists w; iFrame; done.
    iClear "HR".
    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in H6.
    iSplitR; first (iPureIntro; eapply H6).
    iSplitR "Hnb IH HWP HAGCθ HAGCbound HArootss HArootsm Hrootspto Hres".
    * cbn. unfold C_state_interp. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
      repeat iExists _. iFrame. iSplitL; first by iExists _. iPureIntro; done.
    * iApply ("IH" with "[-Hnb] Hnb").
      iApply ("HWP" with "[-Hres] Hres").
      iExists _, _. iFrame. iPureIntro; split_and!.
      - rewrite dom_insert_L. rewrite Heq. done.
      - intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply Hrootslive.
        inversion Hrepr; subst. by eapply elem_of_dom_2.
Qed.

Lemma wp_ext_call_unregisterroot : ext_call_is_sound WP_unregisterroot_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. unfold WP_unregisterroot_spec. iNamed "HT". iNamed "HGC".
  iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%H"; subst θ.

  iPoseProof (ghost_map_lookup with "HArootsm Hpto") as "%Helem".
  iPoseProof (ghost_var_agree with "HAroots HArootss") as "%Heq"; subst roots_s.

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimUnregisterrootS _ _ _ _ _ _ _ (fun k => True)). 1,3,4: done.
    rewrite Heq; by eapply elem_of_dom_2.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ #l ]). subst.

    iMod (ghost_var_update_halves with "HAroots HArootss") as "(HAroots&HArootss)".
    iMod (ghost_map_delete with "HArootsm Hpto") as "HArootsm".
    iPoseProof (big_sepM_delete) as "(HL&_)"; first eapply Helem.
    iPoseProof ("HL" with "Hrootspto") as "((%W&Hpto&%Hw)&Hrootspto)".
    iClear "HL".
    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in H6.
    iSplitR; first (iPureIntro; eapply H6).
    iSplitR "Hnb IH HWP HAGCθ HAGCbound HArootss HArootsm Hrootspto Hpto".
    * cbn. unfold C_state_interp. iSplitL "HσC HnC"; first (iExists nCv; iFrame).
      repeat iExists _. iFrame. iSplitL; first by iExists _. iPureIntro; done.
    * iApply ("IH" with "[-Hnb] Hnb").
      iApply ("HWP" $! W with "[-Hpto] Hpto []"). 2: done.
      iExists _, _. iFrame. iPureIntro; split_and!.
      - rewrite dom_delete_L. rewrite Heq. done.
      - intros ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hrootslive.
Qed.

Ltac solve_ext_call H := 
    iPoseProof (H with "[] Hnb H [IH]") as "Hwp"; [done
    | iIntros "!> %r HΞ Hnb"; iApply ("IH" with "HΞ Hnb"); by iApply "Hr"
    | rewrite weakestpre.wp_unfold; rewrite /weakestpre.wp_pre;
      iApply ("Hwp" $! (CState _ _));
      iSplitL "HσC HnC"; first (iExists _; iFrame);
      unfold C_state_interp, named; do 5 iExists _ ;
      iFrame;
      (iSplitL "HAnMLv"; first by iExists _); done ].

Lemma wp_ext_call_collect_all : ext_call_is_sound WP_ext_call_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. iDestruct "HT" as "[H|[H|[H|H]]]".
  - solve_ext_call wp_ext_call_int2val.
  - solve_ext_call wp_ext_call_val2int.
  - solve_ext_call wp_ext_call_registerroot.
  - solve_ext_call wp_ext_call_unregisterroot.
Qed.


End Laws.



