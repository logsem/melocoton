From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Import basics wp_utils.
From melocoton.interop Require Export prims weakestpre prims_proto.
From melocoton.interop.wp_prims Require Import common.
From melocoton.mlanguage Require Import weakestpre.
Import Wrap.

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma modify_correct e : |- prims_prog e :: modify_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  do 2 (iExists _; iSplit; first done). iNext.
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

End Laws.
