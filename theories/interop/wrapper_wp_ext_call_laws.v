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
  iPoseProof (ghost_map_lookup with "GCrootsm Hroots") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w'&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iMod (ghost_map_update with "GCrootsm Hroots") as "(GCrootsm&Hroots)".
  iApply (wp_store with "Hown").
  iIntros "!> Hown". iApply "HΦ".
  iFrame "Hroots".
  do 10 iExists _. rewrite /named. iFrame.
  rewrite dom_insert_lookup_L; last done.
  iSplit.
  { iPoseProof (big_sepM_insert_delete) as "(_&HR)"; iApply "HR"; iClear "HR".
    iSplitL "Hown"; last done.
    iExists w. iFrame. done. }
  { iPureIntro; split_and!; eauto.
    intros l' γ [[-> ->]|[Hne HH]]%lookup_insert_Some.
    2: by eapply Hrootslive.
    inv_repr_lval. by eapply elem_of_dom_2. }
Qed.

Lemma load_from_root E (l:loc) (v : lval) dq θ :
  {{{GC θ ∗ l ↦roots{dq} v}}}
     ( * #l)%E @ (mkPeC p WP_ext_call_spec); E
  {{{ w, RET w; l ↦roots{dq} v ∗ GC θ ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iNamed "HGC".
  iPoseProof (ghost_map_lookup with "GCrootsm Hroot") as "%H".
  iPoseProof (big_sepM_delete) as "(HL&HR)"; first apply H.
  iPoseProof ("HL" with "GCrootspto") as "((%w&Hown&%Hrepr2) & Hrp)"; iClear "HL".
  iApply (wp_load with "Hown").
  iIntros "!> Hown". iApply "HΦ".
  iFrame "Hroot". iSplit; last done.
  rewrite /GC /named. do 10 iExists _.
  iPoseProof ("HR" with "[Hown Hrp]") as "Hrootsm"; iClear "HR".
  { iFrame. iExists w; by iFrame. }
  iFrame. eauto.
Qed.


Notation fillCCall K s vv := (language.fill K (language.of_class C_lang (ExprCall s (vv:list Cval)))).

Definition ext_call_is_sound (Hspec : string -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ) :=
  forall E T s (vv:list Cval) K Ξ Φ,
    ⌜p !! s = None⌝
 -∗ not_at_boundary
 -∗ Hspec s vv Ξ
 -∗ ▷ (∀ r, Ξ r -∗ not_at_boundary -∗ WP (ExprC (language.fill K (language.of_class C_lang (ExprVal r)))) @ (mkPeW (p : prog wrap_lang) T); E {{v, Φ v }})
 -∗ WP (ExprC (fillCCall K s vv)) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v}}.


Local Ltac SI_not_at_boundary :=
  iDestruct (SI_not_at_boundary_is_in_ML with "Hσ Hnb") as %(ρc & mem & ->);
  iNamed "Hσ"; iNamed "SIC".

Lemma wp_ext_call_int2val : ext_call_is_sound WP_int2val_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ". cbn.
  SI_not_at_boundary. iNamed "HT".
  iNamed "HGC". SI_GC_agree.
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
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    iSplit; first by eauto. simplify_eq.
    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame. eauto. }
    iApply ("IH" with "[-Hnb] Hnb").
    iApply ("HWP" with "[-]"); last done.
    do 10 iExists _; rewrite /named; iFrame. eauto.
Qed.

Lemma wp_ext_call_val2int : ext_call_is_sound WP_val2int_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  SI_not_at_boundary. iNamed "HT". iNamed "HGC". SI_GC_agree.
  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimVal2intS _ _ _ _ _ _ _ (fun k => True)). 2: apply Hrepr. all:done.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([w]).
    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    iSplit; first by eauto. simplify_eq.
    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame; eauto. }
    iApply ("IH" with "[-Hnb] Hnb").
    inv_repr_lval. iApply ("HWP"). do 10 iExists _; unfold named; iFrame. eauto.
Qed.

Lemma wp_ext_call_registerroot : ext_call_is_sound WP_registerroot_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  SI_not_at_boundary. iNamed "HT". iNamed "HGC". SI_GC_agree.

  iAssert (⌜l ∈ dom roots_m⌝ → False)%I as "%Hdom".
  1: { iIntros "%H". eapply elem_of_dom in H; destruct H as [k Hk].
       iPoseProof (big_sepM_lookup_acc with "GCrootspto") as "((%ww&Hww&_)&_)".
       1: apply Hk. iPoseProof (mapsto_ne with "Hpto Hww") as "%Hne". congruence. }

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimRegisterrootS _ _ _ _ _ _ _ (fun k => True)). 1,3,4: done.
    intros H; apply Hdom; congruence.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ #l ]). subst.

    iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
    iMod (ghost_map_insert with "GCrootsm") as "(GCrootsm&Hres)".
    1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
    iPoseProof (big_sepM_insert) as "(_&HR)".
    1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
    iPoseProof ("HR" with "[Hpto GCrootspto]") as "GCrootspto"; first iFrame "GCrootspto".
    iExists w; iFrame; done.
    iClear "HR".
    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    iSplit; first by eauto.
    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame; eauto. }
    iApply ("IH" with "[-Hnb] Hnb").
    iApply ("HWP" with "[-Hres] Hres").
    do 10 iExists _. unfold named. iFrame. iPureIntro; split_and!; eauto.
    - rewrite dom_insert_L. rewrite (_: dom roots_m = rootsC ρc) //.
    - intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply Hrootslive.
      inv_repr_lval. by eapply elem_of_dom_2.
Qed.

Lemma wp_ext_call_unregisterroot : ext_call_is_sound WP_unregisterroot_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  SI_not_at_boundary. iNamed "HT". iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_map_lookup with "GCrootsm Hpto") as "%Helem".

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimUnregisterrootS _ _ _ _ _ _ _ (fun k => True)). 1,3,4: done.
    rewrite (_: rootsC ρc = dom roots_m) //. by eapply elem_of_dom_2.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ #l ]). subst.

    iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
    iMod (ghost_map_delete with "GCrootsm Hpto") as "GCrootsm".
    iPoseProof (big_sepM_delete) as "(HL&_)"; first eapply Helem.
    iPoseProof ("HL" with "GCrootspto") as "((%W&Hpto&%Hw)&GCrootspto)".
    iClear "HL".
    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    iSplit; first by eauto.
    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame; eauto. }
    iApply ("IH" with "[-Hnb] Hnb").
    iApply ("HWP" $! W with "[-Hpto] Hpto []"). 2: done.
    do 10 iExists _. iFrame. iPureIntro; split_and!; eauto.
    - rewrite dom_delete_L. rewrite (_: dom roots_m = rootsC ρc) //.
    - intros ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hrootslive.
Qed.

Lemma wp_ext_call_modify : ext_call_is_sound WP_modify_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  SI_not_at_boundary. iNamed "HT". iNamed "HGC". SI_GC_agree.
  iPoseProof (lstore_own_mut_of with "GCζvirt Hpto") as "%Helem". destruct Helem as [Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Mut, (tg, vs))⌝%I as "%Helem2".
  1: { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
       destruct Hfreezeρ as [HL HR].
       assert (γ ∈ dom (ζC ρc)) as [v Hv]%elem_of_dom by by (rewrite HL; eapply elem_of_dom_2).
       specialize (HR _ _ _ Hv Helem) as Hinv. inversion Hinv; subst; done. }

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimModifyS _ _ _ _ _ _ _ _ _ _ _ _ _ (fun k => True)); try done.
    eapply mk_modify_block. lia.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ w; #i; w' ]). subst.
    iMod (lstore_own_update _ _ _ _ blk' with "GCζvirt Hpto") as "(GCζvirt&Hpto)".
    iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ&GCζ)".
    iPoseProof (interp_ML_discarded_locs_pub with "GCσMLv GCχNone") as "%Hpublocs".

    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    inv_repr_lval.
    destruct HGCOK as [HGCL HGCR]. exploit_gmap_inj. repr_lval_inj.
    iSplit; first by eauto.
    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame; eauto. }

    iApply ("IH" with "[-Hnb] Hnb").
    change (Z.of_nat 0) with (Z0).
    iApply ("HWP" with "[-Hpto] [Hpto]").
    { iExists _, (<[γ:=blk']> (ζσ ∪ ζvirt)), ζσ, (<[γ:=blk']>ζvirt), _, χvirt, σMLvirt.
      iExists _, _, _. unfold named. iFrame.
      erewrite pub_locs_in_lstore_insert_existing; last by eapply elem_of_dom_2. iFrame.
      iPureIntro; split_and!; eauto; cbn. 1: destruct Hfreezeρ as [HL HR]; split.
      - by erewrite !dom_insert_L, HL.
      - intros γ' b1 b2 [[? ?]|[Hne1 H1]]%lookup_insert_Some [[??]|[Hne2 H2']]%lookup_insert_Some; try congruence.
        1: subst; econstructor.
        subst. by eapply HR.
      - rewrite insert_union_r; first done.
        erewrite map_disjoint_Some_l; done.
      - eapply map_disjoint_dom. erewrite dom_insert_lookup; last by eexists. by eapply map_disjoint_dom.
      - rewrite dom_insert_lookup; last by eexists. 
        done.
      - intros ℓ Vs γ1 bb H1 H2' [[<- <-]|[Hne H3']]%lookup_insert_Some.
        -- epose proof (map_Forall_lookup_1 _ _ γ ℓ Hpublocs) as Hpub2. cbn in Hpub2.
           rewrite Hpub2 in H1; first congruence.
           eapply pub_locs_in_lstore_lookup; last apply H2'.
           eapply elem_of_dom_2; done.
        -- specialize (Hstore _ _ _ _ H1 H2' H3'); inversion Hstore; subst.
           econstructor. eapply Forall2_impl; first done.
           intros x' y HH; eapply is_val_insert_immut; last done.
           1: erewrite lookup_union_r; first done.
           1: eapply map_disjoint_Some_l; done. done.
      - split; first apply HGCL.
        intros γ0 m1 tg1 vs1 γ1 Hγ0 [[??]|[Hne1 Hlu]]%lookup_insert_Some Hlloc.
        2: by eapply HGCR. simplify_eq. inv_modify_block.
        apply list_insert_lookup_inv in Hlloc as [HLL|HRR]; simplify_map_eq.
        { inv_repr_lval. by eapply elem_of_dom_2. }
        { eapply HGCR; eauto. rewrite lookup_union_r //.
          eapply map_disjoint_Some_l; eauto. } }
    { iSplit. inv_modify_block; simplify_map_eq. iFrame. eauto. }
Qed.

Lemma wp_ext_call_readfield : ext_call_is_sound WP_readfield_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  SI_not_at_boundary. iNamed "HT". iNamed "HGC". SI_GC_agree.
  iPoseProof (lstore_own_elem_of with "GCζvirt Hpto") as "%Helem".
  iAssert ⌜∃ m', ζC ρc !! γ = Some (m', (tg, vs))⌝%I as "%Helem2".
  1: { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
       destruct Hfreezeρ as [HL HR].
       assert (γ ∈ dom (ζC ρc)) as [v Hv]%elem_of_dom by by (rewrite HL; eapply elem_of_dom_2).
       specialize (HR _ _ _ Hv Helem) as Hinv. inversion Hinv; subst; by eexists. }
  destruct Helem2 as [m' Helem2].
  assert (exists (vv:lval), vs !! (Z.to_nat i) = Some vv) as [vv Hvv].
  1: apply lookup_lt_is_Some; lia.
  destruct HGCOK as [HGCL HGCR]. inv_repr_lval.

  assert (exists w', repr_lval (θC ρc) vv w') as [w' Hw'].
  1: { destruct vv as [vvz|vvl]; first (eexists; econstructor).
       eapply elem_of_dom in HGCR as [w' Hw']; first (eexists; by econstructor).
       1: eapply elem_of_dom_2, H1.
       2: by eapply elem_of_list_lookup_2.
       erewrite lookup_union_r; first done.
       eapply map_disjoint_Some_l; done. }

  iModIntro. iRight. iRight. iSplitR.
  + iPureIntro. econstructor. eapply head_prim_step.
    eapply (PrimReadfieldS _ _ _ _ _ _ _ _ _ _ _ _ _ (fun k => True)); eauto.
  + iIntros (X Hstep).
    destruct Hstep as ([] & x & Hre & Hstep). change (fill () x) with x in Hre. subst x.
    cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
    inversion_call_step Hstep ([ #a ; #i ]). subst.
    inv_repr_lval. exploit_gmap_inj. simplify_map_eq.

    do 3 iModIntro.
    do 2 iExists _. change (Wrap.fill () ?x) with (x) in *.
    iSplit; first by eauto.

    iSplitL "SIζ SIχ SIθ SIroots SIbound HnC HσC".
    { iFrame; eauto. }
    iApply ("IH" with "[-Hnb] Hnb").
    iApply ("HWP" with "[-Hpto] [Hpto] [] []"); try done.
    rewrite /GC /named.
    iExists _, (ζσ ∪ ζvirt), ζσ, ζvirt, _, χvirt, σMLvirt, _. iExists _, _.
    iFrame. iPureIntro; split_and!; eauto. done.
Qed.

Ltac solve_ext_call H := 
    iPoseProof (H with "[] Hnb H [IH]") as "Hwp"; [done
    | iIntros "!> %r HΞ Hnb"; iApply ("IH" with "HΞ Hnb"); by iApply "Hr"
    | rewrite weakestpre.wp_unfold; rewrite /weakestpre.wp_pre;
      iApply ("Hwp" $! (CState _ _));
      iSplitL "HσC HnC"; first (iExists _; iFrame); iFrame ].

Lemma wp_ext_call_collect_all : ext_call_is_sound WP_ext_call_spec.
Proof.
  intros E T s vv K Ξ Φ.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%Hnone Hnb HT IH %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb SIbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  cbn. iDestruct "HT" as "[H|[H|[H|[H|[H|H]]]]]".
  - solve_ext_call wp_ext_call_int2val.
  - solve_ext_call wp_ext_call_val2int.
  - solve_ext_call wp_ext_call_registerroot.
  - solve_ext_call wp_ext_call_unregisterroot.
  - solve_ext_call wp_ext_call_modify.
  - solve_ext_call wp_ext_call_readfield.
  (* - solve_ext_call wp_ext_call_alloc. *)
Qed.


End Laws.
