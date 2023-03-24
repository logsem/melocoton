From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.interop Require Import state lang basics_resources.
From transfinite.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import basics wp_utils.
From melocoton.interop Require Export prims weakestpre prims_proto.
From melocoton.mlanguage Require Import weakestpre.
Import Wrap.

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_intf.val.

Implicit Types P : iProp Σ.
Import mlanguage.

Local Ltac SI_at_boundary :=
  iDestruct (SI_at_boundary_is_in_C with "Hσ Hb") as %(ρc & mem & ->);
  iNamed "Hσ"; iNamed "SIC".

Lemma wp_pre_cases_c_prim p T wp prm ρc mem E ws Φ :
  prm ≠ Pcallback →
  (∀ e, prm ≠ Pmain e) →
  (∃ X,
    ⌜c_prim_step prm ws ρc mem (λ w ρc' mem', X (WrSE (ExprV w), CState ρc' mem'))⌝ ∗
    (∀ w ρc' mem',
       ⌜X (WrSE (ExprV w), CState ρc' mem')⌝ ={E}▷=∗
       weakestpre.state_interp (CState ρc' mem') ∗
       wp E (WrSE (ExprV w)) Φ)) -∗
  |={E}=> wp_pre_cases p T wp (CState ρc mem) E
    (WrSE (RunPrimitive prm ws))
    Φ.
Proof using.
  iIntros (Hncb Hnmain) "HWP".
  iModIntro. iRight. iRight.
  iSplit; first done.
  iDestruct "HWP" as (X Hpstep) "HWP".
  iExists (λ '(e', σ'), X (e', σ') ∧ ∃ w ρc' mem',
            e' = WrSE (ExprV w) ∧ σ' = CState ρc' mem').
  iSplit.
  { iPureIntro. econstructor.
    eapply c_prim_step_covariant_in_Y; naive_solver. }
  iIntros (? ? (HX & ? & ? & ? & (-> & ->))).
  iMod ("HWP" $! _ _ _ HX) as "HWP". do 2 iModIntro.
  iMod "HWP" as "(Hσ & HWP)". by iFrame.
Qed.

Lemma int2val_proto_refines E e Ψ : int2val_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". rewrite /mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #z) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-]"); last done.
  do 9 iExists _; rewrite /named; iFrame. eauto.
Qed.

Lemma val2int_proto_refines E e Ψ : val2int_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". rewrite /mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV #z) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro.
  iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-]").
  do 9 iExists _; rewrite /named; iFrame. eauto.
Qed.

Lemma registerroot_proto_refines E e Ψ : registerroot_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iAssert (⌜¬ l ∈ dom roots_m⌝)%I as "%Hdom".
  1: { iIntros "%H". eapply elem_of_dom in H; destruct H as [k Hk].
       iPoseProof (big_sepM_lookup_acc with "GCrootspto") as "((%ww&Hww&_)&_)".
       1: apply Hk. iPoseProof (resources.mapsto_ne with "Hpto Hww") as "%Hne". congruence. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := {[l]} ∪ rootsC ρc |} mem).
  iSplit. { iPureIntro. econstructor; eauto. congruence. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_insert with "GCrootsm") as "(GCrootsm&Hres)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof (big_sepM_insert) as "(_&HR)".
  1: eapply not_elem_of_dom; intros Hc; eapply Hdom; done.
  iPoseProof ("HR" with "[Hpto GCrootspto]") as "GCrootspto"; first iFrame "GCrootspto".
  1: iExists w; iFrame; done.
  iClear "HR".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hres] Hres").
  do 9 iExists _. unfold named. iFrame. iPureIntro; split_and!; eauto.
  - rewrite dom_insert_L. rewrite (_: dom roots_m = rootsC ρc) //.
  - intros ℓ γ [[-> ->]|[Hne HH]]%lookup_insert_Some; last by eapply Hrootslive.
    inv_repr_lval. by eapply elem_of_dom_2.
Qed.

Lemma unregisterroot_proto_refines E e Ψ : unregisterroot_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_map_lookup with "GCrootsm Hpto") as "%Helem".

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := ζC ρc; θC := θC ρc; rootsC := rootsC ρc ∖ {[l]} |} mem).
  iSplit. { iPureIntro. econstructor; eauto. rewrite -H2. by eapply elem_of_dom_2. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_map_delete with "GCrootsm Hpto") as "GCrootsm".
  iPoseProof (big_sepM_delete) as "(HL&_)"; first eapply Helem.
  iPoseProof ("HL" with "GCrootspto") as "((%W&Hpto&%Hw)&GCrootspto)".
  iClear "HL".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" $! W with "[-Hpto] Hpto []"). 2: done.
  do 9 iExists _. iFrame. iPureIntro; split_and!; eauto.
  - rewrite dom_delete_L. rewrite (_: dom roots_m = rootsC ρc) //.
  - intros ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hrootslive.
Qed.

Lemma modify_proto_refines E e Ψ : modify_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct (lstore_own_vblock_mutable_as_mut with "Hpto") as "(Hpto & Hptoacc)";
    first done.
  iPoseProof (lstore_own_mut_of with "GCζvirt Hpto") as "%Helem". destruct Helem as [Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Bvblock (Mut, (tg, vs0)))⌝%I as "%Helem2".
  1: { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
       destruct Hfreezeρ as [HL HR].
       assert (γ ∈ dom (ζC ρc)) as [v Hv]%elem_of_dom by by (rewrite HL; eapply elem_of_dom_2).
       specialize (HR _ _ _ Hv Helem) as Hinv. inversion Hinv; subst; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  assert (∃ blk', modify_block (Bvblock (Mut, (tg, vs0))) (Z.to_nat i) v' blk')
    as (blk'&Hblk').
  { eexists. eapply mk_modify_block. lia. }

  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState {| χC := χC ρc; ζC := <[γ:=blk']> (ζC ρc); θC := θC ρc; rootsC := rootsC ρc |} mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.

  destruct HGCOK as [HGCL HGCR].
  iMod (lstore_own_update _ _ _ blk' with "GCζvirt Hpto") as "(GCζvirt&Hpto)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ&GCζ)".
  iPoseProof (interp_ML_discarded_locs_pub with "GCσMLv GCχNone") as "%Hpublocs".
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  change (Z.of_nat 0) with (Z0).
  iApply ("Cont" with "[-Hpto Hptoacc] [Hpto Hptoacc]").
  { iExists _, (<[γ:=blk']> (ζσ ∪ ζvirt)), ζσ, (<[γ:=blk']>ζvirt), _, χvirt, σMLvirt.
    iExists _, _. unfold named. iFrame.
    erewrite pub_locs_in_lstore_insert_existing; last by eapply elem_of_dom_2. iFrame.
    iPureIntro; split_and!; eauto; cbn. 1: destruct Hfreezeρ as [HL HR]; split.
    - by erewrite !dom_insert_L, HL.
    - intros γ' b1 b2 [[? ?]|[Hne1 H1']]%lookup_insert_Some [[??]|[Hne2 H2']]%lookup_insert_Some; try congruence.
      1: subst; econstructor.
      subst. by eapply HR.
    - rewrite insert_union_r; first done.
      erewrite map_disjoint_Some_l; done.
    - eapply map_disjoint_dom. erewrite dom_insert_lookup; last by eexists. by eapply map_disjoint_dom.
    - rewrite dom_insert_lookup; last by eexists.
      done.
    - intros ℓ Vs γ1 bb H1' H2' [[<- <-]|[Hne H3']]%lookup_insert_Some.
      -- epose proof (map_Forall_lookup_1 _ _ γ ℓ Hpublocs) as Hpub2. cbn in Hpub2.
         rewrite Hpub2 in H1'; first congruence.
         eapply pub_locs_in_lstore_lookup; last apply H2'.
         eapply elem_of_dom_2; done.
      -- specialize (Hstore _ _ _ _ H1' H2' H3'); inversion Hstore; subst.
         econstructor. eapply Forall2_impl; first done.
         intros x' y HH; eapply is_val_insert_immut; last done.
         1: erewrite lookup_union_r; first done.
         1: eapply map_disjoint_Some_l; done. done.
    - split; first apply HGCL.
      intros γ0 blk1 γ1 Hγ0 [[??]|[Hne1 Hlu]]%lookup_insert_Some Hlloc.
      2: by eapply HGCR. simplify_eq. inv_modify_block.
      apply lval_in_vblock, list_insert_lookup_inv in Hlloc as [HLL|HRR];
        simplify_map_eq.
      { inv_repr_lval. by eapply elem_of_dom_2. }
      { eapply HGCR; eauto. 1: rewrite lookup_union_r //.
        1: eapply map_disjoint_Some_l; eauto. by constructor. } }
  {  iApply lstore_own_vblock_mutable_as_mut; eauto. iFrame.
     iSplit. 1: inv_modify_block; simplify_map_eq. 1: iFrame. eauto. }
Qed.

Lemma readfield_proto_refines E e Ψ : readfield_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "(Hpto & Hptoacc)".
  iPoseProof (lstore_own_elem_of with "GCζvirt Hpto") as "%Helem".
  iAssert ⌜∃ m', ζC ρc !! γ = Some (Bvblock (m', (tg, vs0)))⌝%I as "%Helem2".
  1: { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
       eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
       inversion Hfrz; simplify_eq; eauto. }
  destruct Helem2 as [m' Helem2].
  assert (exists (vv:lval), vs0 !! (Z.to_nat i) = Some vv) as [vv Hvv].
  1: apply lookup_lt_is_Some; lia.
  destruct HGCOK as [HGCL HGCR]. inv_repr_lval.

  assert (exists w', repr_lval (θC ρc) vv w') as [w' Hw'].
  1: { destruct vv as [vvz|vvl]; first (eexists; econstructor).
       eapply elem_of_dom in HGCR as [w' Hw']; first (eexists; by econstructor).
       1: eapply elem_of_dom_2, H1.
       2: constructor; by eapply elem_of_list_lookup_2.
       erewrite lookup_union_r; first done.
       eapply map_disjoint_Some_l; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV w') ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hpto Hptoacc] [$Hpto $Hptoacc] [] []"); try done; [].
  rewrite /GC /named.
  iExists _, (ζσ ∪ ζvirt), ζσ, ζvirt, _, χvirt, σMLvirt, _. iExists _.
  iFrame. iPureIntro; split_and!; eauto. done.
Qed.


Lemma alloc_proto_refines E e Ψ : alloc_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  pose (tg, repeat (Lint 0) (Z.to_nat sz)) as blk.
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ χC' ζC' θC' (a:loc) mem',
    χC ρc !! γ = None ∧
    χC' = <[γ := LlocPrivate]> (χC ρc) ∧
    ζC' = <[γ := Bvblock (Mut, (tg, repeat (Lint 0) (Z.to_nat sz)))]> (ζC ρc) ∧
    GC_correct ζC' θC' ∧
    repr θC' roots_m privmem mem' ∧
    roots_are_live θC' roots_m ∧
    θC' !! γ = Some a ∧
    e' = WrSE (ExprV #a) ∧
    σ' = CState {| χC := χC'; ζC := ζC'; θC := θC'; rootsC := rootsC ρc |} mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & χC' & ζC' & θC' & a & mem' &
                  HγNone & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  assert (χvirt !! γ = None) as Hχvirtγ.
  { eapply not_elem_of_dom. destruct Hχvirt as [<- _].
    by eapply not_elem_of_dom. }
  assert (ζσ !! γ = None) as Hζσγ.
  { eapply not_elem_of_dom. destruct Hstore_blocks as [HHL HHR].
    intros (ℓ&Vs&HX1&HX2)%HHR. congruence. }
  assert (ζvirt !! γ = None) as Hζvirtγ.
  { eapply not_elem_of_dom. intros H. eapply not_elem_of_dom in Hχvirtγ.
    apply Hχvirtγ. eapply elem_of_weaken; first done. done. }
  assert (ζC ρc !! γ = None) as HζCγ.
  { destruct Hfreezeρ as [HL HR]. eapply not_elem_of_dom. rewrite HL.
    rewrite dom_union_L.
    intros [HH|HH]%elem_of_union.
    all: eapply elem_of_dom in HH; destruct HH as [v HHv]; congruence. }

  assert (freeze_lstore (<[γ := Bvblock (Mut, blk)]> (ζC ρc)) (ζσ ∪ <[γ:=Bvblock (Mut, blk)]> ζvirt)) as Hfreezeρ_new.
  { destruct Hfreezeρ as [HfL HfR]; split.
    - rewrite !dom_insert_L. rewrite dom_union_L in HfL. set_solver+ HfL.
    - rewrite <- insert_union_r. 2: done.
      intros γ1 b1 b2 ?%lookup_insert_Some ?%lookup_insert_Some.
      destruct_or!; destruct_and!; simplify_eq; eauto. }

  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".

  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".
  
  iMod (lstore_own_insert _ γ (Bvblock (Mut, blk)) with "GCζvirt") as "(GCζvirt & Hbp1)". 1: done.
  iMod (lloc_own_allocate _ γ with "[] GCχvirt") as "(GCχvirt&Hbp2)". 1: done.

  do 3 iModIntro. iFrame. cbn -[prims_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" $! θC' γ with "[-Hbp2 Hbp1] [Hbp2 Hbp1] []"); try done.
  3: iPureIntro; by econstructor.
  2: iFrame; done.
  rewrite /GC /named.
  iExists _, _, (ζσ), (<[γ:=Bvblock (Mut, blk)]> ζvirt), _, (<[γ:=LlocPrivate]> χvirt).
  iExists σMLvirt, _, _.
  rewrite pub_locs_in_lstore_alloc_priv. 2: done. iFrame.
  cbn. iPureIntro; split_and!; eauto.
  2: destruct Hstore_blocks as [HsL HsR]; split.
  - eapply map_disjoint_insert_r. split; done.
  - intros ℓ Hdom. destruct (HsL ℓ Hdom) as (γ1 & Hγ1). exists γ1. rewrite lookup_insert_ne; first done.
    intros ->; congruence.
  - intros γ1; split.
    + intros (ℓ&Vs&HH1&HH2)%HsR. exists ℓ,Vs; split; try done.
      rewrite lookup_insert_ne; first done. intros ->; congruence.
    + intros (ℓ&Vs&[[??]|[??]]%lookup_insert_Some&HH2); try congruence.
      eapply HsR. by exists ℓ,Vs.
  - erewrite !dom_insert_L. clear -Hother_blocks. set_solver.
  - intros ℓ vs γ1 blk1 HH1 [[??]|[? HH2]]%lookup_insert_Some HH3; try congruence.
    rewrite -!insert_union_r in HH3|-*; try done.
    rewrite lookup_insert_ne in HH3; last done.
    specialize (Hstore ℓ vs γ1 blk1 HH1 HH2 HH3).
    inversion Hstore; subst. econstructor.
    eapply Forall2_impl; first apply H1.
    intros vml vl HH4. eapply is_val_mono. 3: apply HH4.
    + eapply insert_subseteq. done.
    + eapply insert_subseteq. eapply lookup_union_None; done.
  - apply expose_llocs_insert_both; eauto.
  - by apply lloc_map_inj_insert_priv.
  - eapply GC_correct_transport; done.
Qed.

(* TODO: refactor to share proof with wp_prim_alloc *)
Lemma alloc_foreign_proto_refines E e Ψ : alloc_foreign_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ id χC' ζC' θC' (aret:loc) mem',
      χC ρc !! γ = None ∧
      (∀ γ' id', χC ρc !! γ' = Some (LlocForeign id') → id' ≠ id) ∧
      χC' = <[ γ := LlocForeign id ]> (χC ρc) ∧
      ζC' = <[ γ := Bforeign a ]> (ζC ρc) ∧
      GC_correct ζC' θC' ∧
      repr θC' roots_m privmem mem' ∧
      roots_are_live θC' roots_m ∧
      θC' !! γ = Some aret ∧
      e' = WrSE (ExprV (# aret)) ∧
      σ' = CState (WrapstateC χC' ζC' θC' (rootsC ρc)) mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & id & χC' & ζC' & θC' & aret & mem' &
                  HγNone & Hidfresh & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  assert (χvirt !! γ = None) as Hχvirtγ.
  { eapply not_elem_of_dom. destruct Hχvirt as [<- _].
    by eapply not_elem_of_dom. }
  assert (ζσ !! γ = None) as Hζσγ.
  { eapply not_elem_of_dom. destruct Hstore_blocks as [HHL HHR].
    intros (ℓ&Vs&HX1&HX2)%HHR. congruence. }
  assert (ζvirt !! γ = None) as Hζvirtγ.
  { eapply not_elem_of_dom. intros H. eapply not_elem_of_dom in Hχvirtγ.
    apply Hχvirtγ. eapply elem_of_weaken; first done. done. }
  assert (ζC ρc !! γ = None) as HζCγ.
  { destruct Hfreezeρ as [HL HR]. eapply not_elem_of_dom. rewrite HL.
    rewrite dom_union_L.
    intros [HH|HH]%elem_of_union.
    all: eapply elem_of_dom in HH; destruct HH as [v HHv]; congruence. }

  assert (freeze_lstore (<[γ := Bforeign a]> (ζC ρc)) (ζσ ∪ <[γ:=Bforeign a]> ζvirt)) as Hfreezeρ_new.
  { destruct Hfreezeρ as [HfL HfR]; split.
    - rewrite !dom_insert_L HfL dom_union_L. set_solver+.
    - rewrite <- insert_union_r. 2: done.
      intros γ1 b1 b2 ?%lookup_insert_Some ?%lookup_insert_Some.
      destruct_or!; destruct_and!; simplify_eq; eauto. }

  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".

  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".

  iMod (lstore_own_insert _ γ (Bforeign a) with "GCζvirt") as "(GCζvirt & Hbp1)". 1: done.
  iMod (lloc_own_allocate_foreign _ γ id with "[] GCχvirt") as "(GCχvirt&Hbp2)". 1: done.

  do 3 iModIntro. iFrame. cbn -[prims_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" $! θC' γ with "[-Hbp2 Hbp1] [Hbp2 Hbp1] []"); try done.
  3: iPureIntro; by econstructor.
  2: iFrame; by eauto.
  rewrite /GC /named.
  iExists _, _, (ζσ), (<[γ:=Bforeign a]> ζvirt), _, (<[γ:=LlocForeign id]> χvirt).
  iExists σMLvirt, _, _.
  rewrite pub_locs_in_lstore_alloc_foreign //. iFrame.
  iPureIntro; split_and!; eauto.
  2: destruct Hstore_blocks as [HsL HsR]; split.
  - eapply map_disjoint_insert_r. split; done.
  - intros ℓ Hdom. destruct (HsL ℓ Hdom) as (γ1 & Hγ1). exists γ1. rewrite lookup_insert_ne; first done.
    intros ->; congruence.
  - intros γ1; split.
    + intros (ℓ&Vs&HH1&HH2)%HsR. exists ℓ,Vs; split; try done.
      rewrite lookup_insert_ne; first done. intros ->; congruence.
    + intros (ℓ&Vs&[[??]|[??]]%lookup_insert_Some&HH2); try congruence.
      eapply HsR. by exists ℓ,Vs.
  - erewrite !dom_insert_L. clear -Hother_blocks. set_solver.
  - intros ℓ vs γ1 blk1 HH1 [[??]|[? HH2]]%lookup_insert_Some HH3; try congruence.
    rewrite -!insert_union_r in HH3|-*; try done.
    rewrite lookup_insert_ne in HH3; last done.
    specialize (Hstore ℓ vs γ1 blk1 HH1 HH2 HH3).
    inversion Hstore; subst. econstructor.
    eapply Forall2_impl; first eassumption.
    intros vml vl HH4. eapply is_val_mono. 3: apply HH4.
    + eapply insert_subseteq. done.
    + eapply insert_subseteq. eapply lookup_union_None; done.
  - apply expose_llocs_insert_both; eauto. intros γ' ? _ HH1 ->.
    destruct Hχvirt as (Hdom & ? & Hexp).
    assert (is_Some (χC ρc !! γ')) as [? HH2].
    { rewrite -elem_of_dom Hdom elem_of_dom //. }
    specialize (Hexp _ _ _ HH2 HH1). inversion Hexp; simplify_eq.
    naive_solver.
  - cbn. by apply lloc_map_inj_insert_foreign.
  - eapply GC_correct_transport; done.
Qed.

Lemma read_foreign_proto_refines E e Ψ : read_foreign_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "(Hpto & Hsim)".
  iDestruct (lstore_own_mut_of with "GCζvirt Hpto") as %[Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Bforeign a)⌝%I as "%Helem2".
  { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
    eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
    inversion Hfrz; by simplify_eq. }
  destruct HGCOK as [HGCL HGCR]. inv_repr_lval.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV (#a)) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply ("Cont" with "[-Hpto Hsim] [$Hpto $Hsim]").
  rewrite /GC /named.
  iExists _, (ζσ ∪ ζvirt), ζσ, ζvirt, _, χvirt, σMLvirt, _. iExists _.
  iFrame. iPureIntro; split_and!; eauto. done.
Qed.

Lemma write_foreign_proto_refines E e Ψ : write_foreign_proto ⊑ mprog_proto E (prims_prog e) Ψ.
Proof using.
  (* TODO: refactor to share lemmas with prim_modify *)
  iIntros (? ? ?) "H". unfold mprog_proto. iNamed "H".
  iExists _. iSplit; first done. iNext.
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "Hb %σ Hσ". cbn -[prims_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iDestruct "Hpto" as "(Hpto & Hsim)".
  iDestruct (lstore_own_mut_of with "GCζvirt Hpto") as %[Helem _].
  iAssert ⌜ζC ρc !! γ = Some (Bforeign a)⌝%I as "%Helem2".
  { iPureIntro. eapply lookup_union_Some_r in Helem; last apply Hfreezedj.
    eapply freeze_lstore_lookup_backwards in Helem as (?&Hfrz&?); eauto.
    inversion Hfrz; by simplify_eq. }
  destruct HGCOK as [HGCL HGCR]. inv_repr_lval.

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'),
    e' = WrSE (ExprV #0) ∧
    σ' = CState (WrapstateC (χC ρc) (<[γ:=Bforeign a']> (ζC ρc)) (θC ρc) (rootsC ρc)) mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.

  iMod (lstore_own_update _ _ _ (Bforeign a') with "GCζvirt Hpto") as "(GCζvirt&Hpto)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ&GCζ)".
  iPoseProof (interp_ML_discarded_locs_pub with "GCσMLv GCχNone") as "%Hpublocs".
  do 3 iModIntro. iFrame. cbn -[prims_prog] in *.
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  change (Z.of_nat 0) with (Z0).
  iApply ("Cont" with "[-Hpto Hsim] [$Hpto $Hsim]").
  { iExists _, (<[γ:=Bforeign a']> (ζσ ∪ ζvirt)), ζσ, (<[γ:=Bforeign a']>ζvirt), _, χvirt, σMLvirt.
    iExists _, _. unfold named. iFrame.
    erewrite pub_locs_in_lstore_insert_existing; last by eapply elem_of_dom_2. iFrame.
    iPureIntro; split_and!; eauto; cbn. 1: destruct Hfreezeρ as [HL HR]; split.
    - by erewrite !dom_insert_L, HL.
    - intros γ' b1 b2 [[? ?]|[Hne1 H1']]%lookup_insert_Some [[??]|[Hne2 H2']]%lookup_insert_Some; try congruence.
      1: subst; econstructor.
      subst. by eapply HR.
    - rewrite insert_union_r; first done.
      erewrite map_disjoint_Some_l; done.
    - eapply map_disjoint_dom. erewrite dom_insert_lookup; last by eexists. by eapply map_disjoint_dom.
    - rewrite dom_insert_lookup; last by eexists.
      done.
    - intros ℓ Vs γ1 bb H1' H2' [[<- <-]|[Hne H3']]%lookup_insert_Some.
      -- epose proof (map_Forall_lookup_1 _ _ γ ℓ Hpublocs) as Hpub2. cbn in Hpub2.
         rewrite Hpub2 in H1'; first congruence.
         eapply pub_locs_in_lstore_lookup; last apply H2'.
         eapply elem_of_dom_2; done.
      -- specialize (Hstore _ _ _ _ H1' H2' H3'); inversion Hstore; subst.
         econstructor. eapply Forall2_impl; first done.
         intros x' y HH; eapply is_val_insert_immut; last done.
         1: erewrite lookup_union_r; first done.
         1: eapply map_disjoint_Some_l; done. done.
    - split; first apply HGCL.
      intros γ0 blk1 γ1 Hγ0 [[??]|[Hne1 Hlu]]%lookup_insert_Some Hlloc.
      2: by eapply HGCR. simplify_eq. inversion Hlloc. }
  { done. }
Qed.

Lemma base_prim_proto_refines (p : prim) E e Ψ Ψ' :
  p ≠ Pcallback →
  (∀ e, p ≠ Pmain e) →
  prim_proto p E Ψ ⊑ mprog_proto E (prims_prog e) Ψ'.
Proof using.
  intros Hncb Hnmain.
  (destruct p; try by congruence); unfold prim_proto.
  - apply alloc_proto_refines.
  - apply registerroot_proto_refines.
  - apply unregisterroot_proto_refines.
  - apply modify_proto_refines.
  - apply readfield_proto_refines.
  - apply val2int_proto_refines.
  - apply int2val_proto_refines.
  - apply alloc_foreign_proto_refines.
  - apply write_foreign_proto_refines.
  - apply read_foreign_proto_refines.
Qed.

End Laws.
