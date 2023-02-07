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
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim wrapper_wp_utils wrapper_wp_ext_call_laws.
Import Wrap.

Section Simulation.

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

Lemma wp_to_val E T a Φ: 
    wrap_return Φ a (* Basically, a WP (Val a) {{a, wrap_return a}} *)
 -∗ not_at_boundary
 -∗ WP (ExprC (C_lang.Val a)) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "(%θ & %l & %v & HGC & Hv & %Hrepr & #Hblock) Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "HGC". iNamed "SIC".
  iModIntro. iRight. iRight. iSplit.
  1: iPureIntro; cbn; exists (fun _ => True); eexists (), _; repeat split; by eapply RetS.
  cbn. iIntros (X Hstep).
  destruct Hstep as ([] & e1 & Heq & Hstep).
  cbv in Heq; subst e1.
  inversion Hstep.
  1: exfalso; apply language.language.val_stuck in H3; cbn in H3; done.
  2-8: exfalso; unfold language.to_call in H2; destruct language.to_class as [[]|] eqn:Heq; try congruence;
       destruct (language.fill_class' K ec) as [?|[vv ?]];
       [exists (ExprVal a); cbn; by rewrite H
       |subst K; cbn in *; subst ec; cbn in Heq; congruence| congruence].
  cbn in H3; injection H3; intros <-.
  cbv in H1. subst mem0 ρc0 X0.

  iAssert (⌜is_val χvirt ζfreeze v l⌝)%I as "%Hval".
  1: iApply (block_sim_to_ghost_state with "HAχvirt HAζrest"); done.
  iAssert (⌜∀ k v, roots_m !! k = Some v → ∃ w, mem !! k = Some (Storing w) ∧ repr_lval θ v w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots). iPoseProof (big_sepM_lookup with "Hrootspto") as "(%w & Hw & %Hw2)"; first done.
       iExists w. iSplit; last done. iApply (gen_heap_valid with "HσC Hw"). }
  apply map_Forall_lookup_2 in Hroots.
  iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%Hagree1"; subst θ.
  iPoseProof (ghost_var_agree with "HArootss HAroots") as "%Hagree2"; subst roots_s.
  iMod (ghost_var_update_halves with "Hnb [HAGCbound HAbound]") as "(Hnb & Hbound)".
  (* Coq fails to infer ghost_var_fractional in time *)
  1: iPoseProof (@fractional.fractional_merge _ _ _ _ _ _ (ghost_var_fractional _ _) with "HAGCbound HAbound") as "HH".
  1: by assert ((1 / 4 + 1 / 4 = 1 / 2)%Qp) as -> by compute_done.
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.
  iMod (ghost_var_update_halves with "HAGCθ HAθ") as "(HAGCθ & HAθ)".
  iMod (set_to_none with "HσC Hrootspto") as "(HσC & Hrootspto)".
  1: done.

  do 3 iModIntro. do 2 iExists _.  iSplit.
  1: iPureIntro; eapply (H4 σMLvirt l v ζfreeze ζσ χvirt ζrest roots_m privmem).
  all: try done.
  1: rewrite map_union_comm; done.

  iSplitR "Hv Hnb"; last first.
  1: { iApply weakestpre.wp_value'. iFrame. }
  cbn. iSplitL "HAσMLv HAnMLv HAσdom".
  1: iExists nMLv; iFrame.
  unfold private_state_interp, ML_state_interp, GC_token_remnant, named; cbn.
  iFrame. iSplitL "HnC"; first by iExists _.
  rewrite <- Hagree2.
  iFrame "HAroots".
  iPureIntro; split_and!.
  1: destruct Hχvirt as (_ & HHH); apply HHH.
  1: apply Hother_blocks.
  1: destruct Hpriv as (mem_r & ->%repr_roots_dom & Hpriv2 & Hpriv3); by apply map_disjoint_dom.
Qed.

Lemma wp_simulates E T ec Φ: 
    not_at_boundary
 -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }}
 -∗ WP (ExprC ec) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iLöb as "IH" forall (ec).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb HWP %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iClear "HWP"; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  iMod ("HWP" $! mem nCv with "[HσC HnC]") as 
  "[(%x & -> & Hσ & Hret)
  |[(%s' & %vv & %K' & -> & %H2 & >(%Ξ & Hσ & HT & Hr))
  |(%Hred & H3)]]".
  + cbn. iFrame.
  + iPoseProof (wp_to_val with "Hret") as "Hret".
    iSpecialize ("Hret" with "Hnb").
    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iApply ("Hret" $! (CState ρc mem)).
    iSplitL "Hσ". 1: by iExists _.
    unfold C_state_interp, named.
    iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
    iFrame.
    iSplitL "HAnMLv"; first by iExists nMLv.
    iPureIntro. split_and!; done.
  + iPoseProof (wp_ext_call_collect_all with "[] Hnb HT [Hr]") as "Hwp"; first done.
    1: iIntros "!> %r HΞ Hnb"; iApply ("IH" with "Hnb");
       by iApply "Hr".
    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iApply ("Hwp" $! (CState ρc mem)).
    iSplitL "Hσ". 1: by iExists _.
    unfold C_state_interp, named.
    iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
    iFrame.
    iSplitL "HAnMLv"; first by iExists nMLv.
    iPureIntro. split_and!; done.
  + cbn in Hred. iModIntro. iRight. iRight. iSplit.
    * iPureIntro. exists (fun _ => True). eapply head_prim_step.
      destruct Hred as (e' & σ' & Hprim). econstructor; last done. cbn. eapply Hprim.
    * iIntros (X Hstep).
      destruct Hstep as ([] & x & Hre & Hstep). cbv in Hre; subst x.
      cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
      inversion Hstep. 2-9: exfalso.
      2: { apply C_lang.of_to_val in H3; subst ec.
           apply language.language.reducible_no_threads_reducible in Hred.
           apply language.language.reducible_not_val in Hred. cbn in Hred; congruence. }
      2-8: subst ec; eapply reducible_call_is_in_prog; 
           [ by eapply language.language.reducible_no_threads_reducible
           | done
           | eapply @List.Forall_forall in Hforbid; [apply Hforbid | cbv; eauto 20]].
      cbv in H1,H4.
      subst ec0 ρc0 mem0 X0. cbn.
      iMod ("H3" $! _ _ H3) as "H3".
      do 2 iModIntro. iMod "H3" as "(HσC & HWP')".
      iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H4).
      iSplitR "HWP' Hnb".
      2: iApply ("IH" with "Hnb HWP'").
      cbn. iSplitL "HσC"; first by iExists _.
      unfold C_state_interp, named. iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
      iFrame. iSplitL; first by iExists _.
      iPureIntro; split_and!; done.
Qed.




Lemma run_function_correct F (vv : list ML_lang.val) T E Φ: 
    ⌜arity F = length vv⌝
 -∗ at_boundary _
 -∗ (∀ θ ll aa ec, 
       GC θ 
    -∗ ⌜C_lang.apply_function F aa = Some ec⌝
    -∗ ⌜Forall2 (repr_lval θ) ll aa⌝
    -∗ block_sim_arr vv ll
    -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }})
 -∗ WP RunFunction F vv @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "%Harity Hb Hwp".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hσ".
  unfold at_boundary; cbn. destruct σ as [ρml σ | ? ?].
  2: {iExFalso. iNamed "Hσ"; iNamed "SIC". iPoseProof (ghost_var_agree with "Hb HAbound") as "%Heq". congruence. }
  iModIntro. iRight. iRight.
  iNamed "Hσ". iNamed "SIML". iNamed "HAGCrem".

  iPoseProof (sigma_None_extract with "HσML HAχNone") as "%Hpublocs".

  iSplitR.
  + iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn.

    destruct (deserialize_ML_heap_extra (ζML ρml) (χML ρml) σ) as (χ1 & ζσ & ζσimm & Hext & Hstorebl & Hdisj & Hstore).
    1: done.
    1: done.
    1: done.
    destruct (deserialize_ML_values χ1 vv) as (χ2 & ζimm & lvs & Hext2 & Hvs).
    1: apply Hext.

    assert (ζML ρml ∪ ζσ ∪ ζσimm ##ₘ ζimm) as Hdis1.
    1: { eapply map_disjoint_dom. eapply disjoint_weaken. 1: eapply Hext2. 2: done.
         rewrite dom_union_L. eapply union_subseteq. split. 2: by eapply extended_to_dom_subset.
         rewrite dom_union_L. eapply union_subseteq; split.
         1: etransitivity; first by eapply elem_of_subseteq. 1: eapply subseteq_dom, Hext.
         intros γ Hγ. destruct Hstorebl as [_ HR]. apply HR in Hγ. destruct Hγ as (ℓ & ? & HH & _); by eapply elem_of_dom_2. }

    pose (ζML ρml ∪ ζσ ∪ (ζσimm ∪ ζimm)) as ζC.

    destruct (collect_dom_θ_ζ ∅ ζC) as (θdom1 & Hθdom1).
    destruct (collect_dom_θ_vs θdom1 lvs) as (θdom2 & Hθdom2).
    destruct (collect_dom_θ_roots θdom2 (rootsML ρml)) as (θdom3 & Hθdom3).
    destruct (injectivify_map θdom3) as (θC & Hdom & Hinj).
    destruct (find_repr_lval_vs θC lvs) as (ws & Hws).
    1: intros γ Hγ; subst θdom3; apply Hθdom3; right; apply Hθdom2; left; done.
    destruct (apply_function_arity F ws) as (HL&_); destruct HL as (ec&Hec).
    1: rewrite Harity; etransitivity; eapply Forall2_length; done.
    assert (roots_are_live θC (rootsML ρml)) as Hrootslive.
    1: { intros a γ H1. subst θdom3. apply Hθdom3. left. by eexists. }
    destruct (find_repr_roots θC (rootsML ρml) (privmemML ρml)) as (mem & Hrepr); try done.

    eapply (RunFunctionS p F vv ρml σ ζσ (ζσimm ∪ ζimm) lvs ws ec mem χ2 ζC θC (fun _ => True)).
    1: eapply extended_to_trans; done.
    1: destruct Hstorebl as [HL HR]; split.
    1: { intros ℓ  Hℓ. destruct (HL ℓ Hℓ) as (γ & Hγ). exists γ. eapply lookup_weaken; first done. apply Hext2. }
    1: { intros γ; destruct (HR γ) as [HRL HRH]; split.
         1: intros H; destruct (HRL H) as (ℓ & Vs & H1 & H2); exists ℓ, Vs; split; try done; eapply lookup_weaken; first done; apply Hext2.
         intros (ℓ & Vs & H1 & H2). apply HRH. exists ℓ, Vs. split; try done. eapply elem_of_dom_2 in H2. destruct (HL _ H2) as (γ2 & Hγ2).
         enough (γ2 = γ) as -> by done. eapply Hext2. 2: done. eapply lookup_weaken; first done; eapply Hext2. }
    1: { intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; eapply lookup_weaken.
         1: by eapply Hext. 2: by eapply Hext2. 2: done. 1: apply Hext2. }
    1: { reflexivity. }
    1: { rewrite map_union_assoc. apply map_disjoint_union_r_2. 1: done.
         eapply map_disjoint_dom, disjoint_weaken; first eapply map_disjoint_dom, Hdis1; try done.
         erewrite ! dom_union_L; set_solver. }
    1: { intros ℓ vs γ b H1 H2 H3. unfold ζC in *. rewrite ! map_union_assoc. rewrite ! map_union_assoc in H3.
         apply lookup_union_Some_inv_l in H3.
         2: apply not_elem_of_dom; intros Hc; apply Hext2 in Hc; congruence.
         eapply is_heap_elt_weaken. 1: eapply Hstore; try done.
         2: apply Hext2.
         + destruct Hstorebl as [HL HR]; destruct (HL ℓ) as [v Hv]; first by eapply elem_of_dom_2.
           rewrite <- Hv; f_equal; eapply Hext2; try done; eapply lookup_weaken, Hext2; try done.
         + eapply map_union_subseteq_l. }
    1: { eapply Forall2_impl; first done. intros ? ? H; eapply is_val_mono; last done; first done.
         unfold ζC. rewrite ! map_union_assoc. eapply map_union_subseteq_r. done. }
    1: { split; first done. subst θdom3. intros γ m tg vs γ' _ H2 H3.
         apply Hθdom3. right. apply Hθdom2. right. apply Hθdom1. right. left. do 4 eexists; done. }
    1: { done. }
    1: { done. }
    1: { done. }
    1: { done. }
    1: { done. }
  + iIntros (X Hstep).
    destruct Hstep as ([] & e1 & Heq & Hstep).
    cbv in Heq; subst e1.
    inversion Hstep.
    cbv in H1. subst fn vs ρml0 σ0 X0.

    iMod (ghost_var_update_halves with "Hb HAbound") as "(Hnb & Hnb2)".
    1: iPoseProof (@fractional.fractional _ _ (ghost_var_fractional _ _)) as "[HH _]".
    iDestruct ("HH" with "[Hnb2]") as "(HAGCbound & HAbound)".
    1: by assert ((1 / 4 + 1 / 4 = 1 / 2)%Qp) as <- by compute_done.
    iClear "HH".
    iMod (ghost_var_update_halves with "HAθ HAGCθ") as "(HAθ & HAGCθ)".
    iMod (lstore_own_insert_many with "HAζrest") as "(HAζrest & Hζnewimm)".
    1: apply map_disjoint_union_r in H7 as [H71 H72]; apply H72.
    iMod (lloc_own_mono with "HAχ") as "HAχ"; first done.
    assert (ζσ ##ₘ ζnewimm) as Hdisj2 by by eapply is_store_blocks_is_private_blocks_disjoint.
    apply map_disjoint_union_r in H7 as [H71 H72].
    assert (ζC = ζσ ∪ (ζML ρml ∪ ζnewimm)) as H6B.
    1: { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
    iPoseProof (block_sim_arr_of_ghost_state _ _ _ _ _ vv lvs with "HAχ HAζrest [] [] [] [] []") as "#Hsim".
    1-5: iPureIntro. 5: exact H9. 1-3:done. 1: by apply map_disjoint_union_r.
    iMod (set_to_some with "HAσCv Hrootspto") as "(HAσCv & Hrootspto)"; first done.

    do 3 iModIntro.
    do 2 iExists _.
    iSplitR; first (iPureIntro; exact H16).

    iSpecialize ("Hwp" $! θC lvs ws ec).
    iSplitR "Hnb Hwp HAGCθ HAGCbound HArootss HArootsm Hrootspto".
    * unfold wrap_state_interp, C_state_interp; cbn.
      iSplitL "HAσCv HAnCv"; first (iExists nCv; iFrame).
      iExists ζC, ζσ, (ζML ρml ∪ ζnewimm), χC, σ.
      iFrame.
      iSplitL "HvML"; first by iExists _.
      rewrite pub_locs_in_lstore_insert_priv_store; last done.
      erewrite pub_locs_in_lstore_mono at 1; last apply H3; last done.
      iFrame "HAχNone".
      iPureIntro. split_and!.
      1: reflexivity.
      1: done.
      1: apply map_disjoint_union_r; done.
      1: done.
      1: { rewrite dom_union_L. intros γ [H|H]%elem_of_union.
           - eapply elem_of_weaken; first by eapply Hother_blocks.
             eapply subseteq_dom, H3.
           - by eapply elem_of_dom_2, H5. }
      1: done.
      1: { split; first done.
           split; first apply H3.
           intros γ v1 v2 H1 H2. rewrite H1 in H2. injection H2; intros ->. econstructor. }
      1: apply H3.
      1: done.
    * iApply (wp_simulates with "Hnb").
      iApply ("Hwp" with "[-] [] [] Hsim"); try done.
      unfold GC; cbn.
      iExists (dom (rootsML ρml)), (rootsML ρml).
      iFrame. done.
Qed.

End Simulation.



