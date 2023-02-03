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
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim wrapper_wp_update_laws.
Import Wrap.

Section Simulation.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.
Import mlanguage.


Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ _ Σ).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang Σ).


Definition WP_ext_call_spec : string -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ := λ n vl wp,
  ⌜False⌝%I.

Definition forbidden_function_names : list string := ["alloc"; "registerroot"; "unregisterroot"; "modify"; "readfield"; "int2val"; "val2int"].

Notation wrap_return := (fun Φ (a:Cval) => (∃ θ' l v, GC θ' ∗ Φ v ∗ ⌜repr_lval θ' l a⌝ ∗ block_sim v l)%I).

Lemma repr_roots_dom θ a b : repr_roots θ a b -> dom a = dom b.
Proof.
  induction 1.
  + by do 2 rewrite dom_empty_L.
  + by do 2 rewrite dom_insert_L; rewrite IHrepr_roots.
Qed.

(* We can decompose mem, the C heap, into a privmem, which is everything but the roots, and a memr, which are just the rooted cells *)
Lemma make_repr θ roots_m mem : 
    roots_are_live θ roots_m
 -> map_Forall (λ k v, ∃ w , mem !! k = Some (Storing w) ∧ repr_lval θ v w) roots_m
 -> ∃ privmem, repr θ roots_m privmem mem.
Proof.
  revert mem.
  induction roots_m as [|l a roots_m Hin IH] using map_ind; intros mem Hlive Hforall.
  + exists mem, ∅. split_and!.
    * econstructor.
    * eapply map_disjoint_empty_r.
    * by rewrite map_empty_union.
  + apply map_Forall_insert_1_1 in Hforall as Hforall2.
    destruct Hforall2 as (w & Hw & Hrep).
    specialize (IH (delete l mem)).
    destruct IH as (privmem & memr & IH & Hdisj & Hunion).
    1: intros l' g Hg; eapply Hlive; rewrite lookup_insert_ne; first done; intros ->; rewrite Hg in Hin; congruence.
    1: apply map_Forall_lookup; intros i x Hinix;
       eapply map_Forall_lookup_1 in Hforall.
    1: destruct Hforall as (w' & H1 & H2); exists w'; repeat split; try done.
    1: rewrite lookup_delete_ne; first done.
    2: rewrite lookup_insert_ne; first done.
    1-2: intros ->; rewrite Hin in Hinix; congruence.
    assert (memr !! l = None) as HNone1.
    1: apply not_elem_of_dom; erewrite <- repr_roots_dom; last done; by eapply not_elem_of_dom.
    assert (privmem !! l = None) as Hnone2.
    rewrite <- (lookup_union_r memr privmem); try done; rewrite <- Hunion; by apply lookup_delete.
    eexists privmem, (<[l:=Storing w]> memr). split_and!.
    * econstructor; try done; by eapply not_elem_of_dom.
    * by apply map_disjoint_insert_r.
    * erewrite <- insert_union_l. rewrite <- Hunion. rewrite insert_delete_insert.
      apply map_eq_iff. intros i. destruct (decide (i = l)) as [-> |]; (try by rewrite lookup_insert); by rewrite lookup_insert_ne.
Qed.

Lemma repr_lval_inj θ v w w' : repr_lval θ v w -> repr_lval θ v w' -> w = w'.
Proof.
  induction 1; inversion 1.
  + done.
  + rewrite H in H3. injection H3; intros ->; done.
Qed.

Lemma set_to_none θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp mem
 -∗ ([∗ map] a0↦v0 ∈ roots_m, ∃ w, a0 ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v0 w⌝)
==∗ (gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
    ∗[∗ set] a0 ∈ dom roots_m, a0 O↦ None).
Proof.
  intros (mm & Hrepr1 & Hrepr2 & Hrepr3).
  induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*.
  + iIntros "Hheap Hmap !>".
    rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty.
    rewrite map_empty_union in Hrepr3. subst mem. iFrame.
    iApply big_sepS_empty. done.
  + eapply not_elem_of_dom in H0,H1. iIntros "Hheap Hmap".
    iPoseProof (big_sepM_insert) as "(Hb1 & _)"; first apply H0.
    iPoseProof ("Hb1" with "Hmap") as "((%w' & Hw & %Hrepr4) & Hmap)".
    pose proof (repr_lval_inj _ _ _ _ Hrepr4 H) as Heq; subst w'.
    iMod (gen_heap_update with "Hheap Hw") as "(Hheap & Hw)".
    specialize (IHHrepr1 (<[a:=None]> mem) (<[a:=None]> privmem)).
    iMod (IHHrepr1 with "Hheap Hmap") as "(Hheap & Hmap)".
    * eapply map_disjoint_insert_l_2; first done.
      erewrite <- (delete_insert mem0); last done.
      by eapply map_disjoint_delete_r.
    * subst mem. erewrite <- insert_union_l.
      rewrite insert_insert. by rewrite insert_union_r.
    * iModIntro. iSplitL "Hheap".
      - erewrite <- insert_union_l. rewrite insert_union_r.
        2: eapply map_disjoint_Some_r; try done; by rewrite lookup_insert.
        rewrite fmap_insert. iFrame.
      - rewrite dom_insert_L. iApply big_sepS_insert; first by eapply not_elem_of_dom. iFrame.
Qed.

Lemma wp_to_val E p T a Φ: 
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
(*
  iAssert (⌜gmap_inj χvirt⌝)%I as "%Hinj".
  1: { iPoseProof (gset_bij_own_valid with "HAχbij") as "%Hbij". iPureIntro.
       destruct Hbij as (_ & Hbij). intros l1 l2 vv Hl1 Hl2.
       eapply gset_bijective_eq_iff. 1: apply Hbij.
       1-2: eapply elem_of_map_to_set_pair. all: done. } *)
  iMod (set_to_none with "HσC Hrootspto") as "(HσC & Hrootspto)".
  1: done.
(*
  assert (val_safe_on_heap σMLvirt v) as Hsafe.
  1: { eapply is_val_is_safe_on_heap; last done. destruct Hstore_blocks; set_solver. }
  iMod (val_safe_to_ghost_state with "[] HAσdom") as "(HAσdom & #Hsafe)"; first done.
*)
  do 3 iModIntro. do 2 iExists _.  iSplit.
  1: iPureIntro; eapply (H4 σMLvirt l v ζfreeze ζσ χvirt ζrest roots_m privmem).
  all: try done.
  1: rewrite map_union_comm; done.

  iSplitR "Hv Hnb"; last first.
  1: { iApply weakestpre.wp_value'. iFrame. }
  cbn. iSplitL "HAσMLv HAnMLv HAσdom".
  1: iExists nMLv; iFrame.
  unfold private_state_interp, ML_state_interp, GC_token_remnant, named; cbn.
  iFrame "HArootss".
  iFrame "HArootsm".
  iFrame "HAGCθ".
  iFrame "HAζrest".
  iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  iFrame "HAχvirt".
  iFrame "HAχNone".
  iFrame "Hbound".
  iFrame "HAθ".
  rewrite <- Hagree2.
  iFrame "Hrootspto".
  iFrame "HAroots".
  iPureIntro; split_and!.
  1: destruct Hχvirt as (_ & HHH); apply HHH.
  1: apply Hother_blocks.
Qed.

Context (p : language.prog C_lang).
Context (Hforbid : Forall (fun k => p !! k = None) forbidden_function_names).

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
  + cbn. iExFalso. iApply "HT". (* TODO: add more calls here *)
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

Definition lookup_reversed (χ : lloc_map) ℓ := {γ | χ !! γ = Some (LlocPublic ℓ)}.

Definition find_in_χ (χ:lloc_map) ℓ : sum (lookup_reversed χ ℓ) (lookup_reversed χ ℓ -> False).
Proof.
  pose (map_to_set (fun γ ll => match ll with LlocPrivate => None | LlocPublic ℓ' => if decide (ℓ' = ℓ) then Some γ else None end) χ : gset _) as Hset.
  epose (filter (fun k => is_Some (k)) Hset) as Hset2.
  destruct (elements Hset2) as [|[γ|] ?] eqn:Heq.
  - right. intros (γ & Hγ).
    apply elements_empty_inv in Heq. apply gset_leibniz in Heq.
    eapply filter_empty_not_elem_of_L. 2: apply Heq. 1: apply _.
    2: eapply elem_of_map_to_set.
    2: exists γ, (LlocPublic ℓ); split; done.
    rewrite decide_True; done. Unshelve. all: apply _.
  - left. exists γ.
    assert (Some γ ∈ Hset2).
    1: eapply elem_of_elements; rewrite Heq; left.
    eapply elem_of_filter in H. destruct H as [_ H].
    eapply elem_of_map_to_set in H.
    destruct H as (i & ll & H1 & H2).
    destruct ll; try congruence.
    destruct decide; try congruence.
  - exfalso. assert (None ∈ Hset2).
    + eapply elem_of_elements. rewrite Heq. left.
    + apply elem_of_filter in H. destruct H as [[? Hc]?]. congruence.
Defined.

Lemma allocate_in_χ_pub χ ℓ : lloc_map_inj χ → exists χ' γ, lloc_map_mono χ χ' ∧ χ' !! γ = Some (LlocPublic ℓ) ∧ ∀ γ' r, γ' ≠ γ → χ' !! γ' = r → χ !! γ' = r.
Proof.
  intros Hinj.
  destruct (find_in_χ χ ℓ) as [[γ Hgam]|Hnot].
  1: exists χ, γ; done.
  eexists (<[fresh (dom χ) := LlocPublic ℓ]> χ), _.
  erewrite lookup_insert; split_and!. 2: done.
  2: intros γ' r Hne H1; by rewrite lookup_insert_ne in H1.
  split.
  1: eapply insert_subseteq, not_elem_of_dom, is_fresh.
  intros γ1 γ2 ℓ' [[? ?]|[? ?]]%lookup_insert_Some [[? ?]|[? ?]]%lookup_insert_Some; subst.
  1: done.
  3: by eapply Hinj.
  all: exfalso; eapply Hnot; eexists _; erewrite H0, H2; done.
Qed.

Lemma allocate_in_χ_priv χ : lloc_map_inj χ → exists χ' γ, lloc_map_mono χ χ' ∧ χ' !! γ = Some (LlocPrivate) ∧ γ ∉ dom χ.
Proof.
  intros Hinj.
  eexists (<[fresh (dom χ) := LlocPrivate]> χ), _.
  erewrite lookup_insert; split_and!; last apply is_fresh; last done.
  split.
  1: eapply insert_subseteq, not_elem_of_dom, is_fresh.
  intros γ1 γ2 ℓ' [[? ?]|[? ?]]%lookup_insert_Some [[? ?]|[? ?]]%lookup_insert_Some; subst; try congruence.
  by eapply Hinj.
Qed.

Lemma deserialize_ML_value χMLold v :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lv,
    lloc_map_mono χMLold χC 
  ∧ is_private_blocks χC ζimm
  ∧ dom χMLold ## dom ζimm
  ∧ is_val χC ζimm v lv.
Proof.
  induction v as [[x|bo| |ℓ]| |v1 IHv1 v2 IHv2|v IHv|v IHv] in χMLold|-*; intros Hinj.
  1-3,5: eexists χMLold, ∅, _; split_and!;
       [ done | done | rewrite dom_empty_L; set_solver | econstructor].
  Unshelve. 5: exact (Lloc 0). (* what happens for functions *)
  1: destruct (allocate_in_χ_pub χMLold ℓ) as (χ' & γ & Hχ' & Hγ & _); first done;
     exists χ', ∅, (Lloc γ); (split_and!; last by econstructor); done.
  1: { destruct (IHv1 χMLold) as (χ1 & ζ1 & lv1 & (Hχ1&Hχ1inj) & Hζ1 & Hd1 & Hlv1); first done.
       destruct (IHv2 χ1) as (χ2 & ζ2 & lv2 & (Hχ2&Hχ2inj) & Hζ2 & Hd2 & Hlv2); first done.
       destruct (allocate_in_χ_priv χ2) as (χ3 & γ & (Hχ3&Hχ3inj) & Hγ & Hγne); first done.
       assert (dom ζ1 ## dom ζ2) as Hdis.
       1: eapply elem_of_disjoint; intros γ' H1 H2; edestruct (@elem_of_disjoint) as [HL _]; 
          eapply HL; [exact Hd2 | |exact H2]; eapply elem_of_dom_2; eapply Hζ1; done.
       assert ( {[ γ ]} ## dom ζ1 ∪ dom ζ2) as Hdis2.
       1: eapply disjoint_singleton_l; intros [H|H]%elem_of_union; apply Hγne; eapply elem_of_weaken.
       1: by eapply elem_of_dom_2, Hζ1. 1: by eapply subseteq_dom.
       1: by eapply elem_of_dom_2, Hζ2. 1: done.
       eexists χ3, (<[γ := _]> (ζ1 ∪ ζ2)), _; split_and!.
       4: econstructor; first by erewrite lookup_insert.
       4-5: eapply is_val_mono; last done; first by repeat (etransitivity; first done).
       1: repeat (eapply lloc_map_mono_trans; first done); split; try done; apply Hχ3.
       1: intros γ'; rewrite ! dom_insert_L  ! dom_union_L;
          intros [H%elem_of_singleton|[H|H]%elem_of_union]%elem_of_union.
       - congruence.
       - eapply lookup_weaken; first by eapply Hζ1.
         by repeat (etransitivity; first done).
       - eapply lookup_weaken; first by eapply Hζ2. done.
       - rewrite ! dom_insert_L  ! dom_union_L. repeat (apply disjoint_union_r; split).
         + eapply disjoint_singleton_r. intros Hc. apply Hγne. eapply elem_of_weaken; first done.
           apply subseteq_dom. by repeat (etransitivity; last done).
         + done.
         + eapply elem_of_disjoint. intros γ' H1 H2.
           edestruct (@elem_of_disjoint) as [HL _]. eapply HL. 1: apply Hd2. 2: apply H2.
           eapply elem_of_weaken; first apply H1. apply subseteq_dom; done.
       - etransitivity; last eapply insert_subseteq. 2: eapply not_elem_of_dom; rewrite dom_union_L; set_solver.
         eapply map_union_subseteq_l.
       - etransitivity; last eapply insert_subseteq. 2: eapply not_elem_of_dom; rewrite dom_union_L; set_solver.
         eapply map_union_subseteq_r. eapply map_disjoint_dom; done. }
  all: destruct (IHv χMLold) as (χ1 & ζ1 & lv1 & (Hχ1&Hχ1inj) & Hζ1 & Hd1 & Hlv1); first done;
       destruct (allocate_in_χ_priv χ1) as (χ3 & γ & (Hχ3&Hχ3inj) & Hγ & Hγne); first done;
       assert ( {[ γ ]} ## dom ζ1) as Hdis2 by
       (eapply disjoint_singleton_l; intros H; apply Hγne; eapply elem_of_weaken; [ by eapply elem_of_dom_2, Hζ1 | done ]);
       eexists χ3, (<[γ := _]> (ζ1)), _; split_and!.
  1,5: repeat (eapply lloc_map_mono_trans; first done); split; try done; apply Hχ3.
  3,6: econstructor; first by erewrite lookup_insert.
  3,4: eapply is_val_mono; last done; first by repeat (etransitivity; first done).
  3,4: eapply insert_subseteq; eapply not_elem_of_dom; set_solver.
  1,3: intros γ'; rewrite ! dom_insert_L; intros [H%elem_of_singleton|H]%elem_of_union; try congruence. 
  1-2: (eapply lookup_weaken; first by apply Hζ1); done.
  1-2: rewrite ! dom_insert_L; eapply disjoint_union_r; split; try done.
  1-2: eapply disjoint_singleton_r; intros Hc; apply Hγne; eapply elem_of_weaken; first done;
       apply subseteq_dom; by repeat (etransitivity; last done).
Qed.

Lemma deserialize_ML_values χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lvs,
    lloc_map_mono χMLold χC 
  ∧ is_private_blocks χC ζimm
  ∧ dom χMLold ## dom ζimm
  ∧ Forall2 (is_val χC ζimm) vs lvs.
Proof.
  induction vs as [|v vs IH] in χMLold|-*; intros Hinj.
  - eexists χMLold, ∅, _; split_and!;
    [ done | done | rewrite dom_empty_L; set_solver | econstructor].
  - destruct (deserialize_ML_value χMLold v Hinj) as (χ1 & ζ1 & lv & (Hχ1&Hχ1inj) & Hζ1 & Hd1 & Hlv1).
    destruct (IH χ1 Hχ1inj) as (χ2 & ζ2 & lvs & (Hχ2&Hχ2inj) & Hζ2 & Hd2 & Hlv2).
    exists χ2, (ζ1 ∪ ζ2), (lv::lvs). split_and!.
    + split; last done. by etransitivity.
    + intros γ. rewrite ! dom_union_L. intros [H|H]%elem_of_union.
      1: (eapply lookup_weaken; first by apply Hζ1); done.
      1: by eapply Hζ2.
    + rewrite dom_union_L. eapply disjoint_union_r. split; first done.
      eapply elem_of_disjoint. intros γ' H1 H2.
      edestruct (@elem_of_disjoint) as [HL _]. eapply HL. 1: apply Hd2. 2: apply H2.
      eapply elem_of_weaken; first apply H1. apply subseteq_dom; done.
    + econstructor. 1: eapply is_val_mono; last done; try done; eapply map_union_subseteq_l.
      eapply Forall2_impl; first done. 
      intros ? ? Hv. eapply is_val_mono; last done; try done.
      eapply map_union_subseteq_r. eapply map_disjoint_dom.
      eapply elem_of_disjoint. intros γ' H1 H2.
      edestruct (@elem_of_disjoint) as [HL _]. eapply HL. 1: apply Hd2. 2: apply H2.
      eapply elem_of_dom_2. apply Hζ1. done.
Qed.

Lemma deserialize_ML_block χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm blk,
    lloc_map_mono χMLold χC 
  ∧ is_private_blocks χC ζimm
  ∧ dom χMLold ## dom ζimm
  ∧ is_heap_elt χC ζimm vs blk.
Proof.
  intros H.
  destruct (deserialize_ML_values χMLold vs H) as (χC & ζimm & lvs & H1 & H2 & H3 & H4).
  exists χC, ζimm, (Mut,(TagDefault,lvs)). split_and!; done.
Qed.

Lemma deserialize_ML_heap ζMLold χMLold σ : 
  lloc_map_inj χMLold
→ dom ζMLold ⊆ dom χMLold
→ (map_Forall (fun _ ℓ => σ !! ℓ = Some None \/ σ !! ℓ = None) (pub_locs_in_lstore χMLold ζMLold))
→ ∃ χC ζσ ζnewimm,
    lloc_map_mono χMLold χC 
  ∧ is_store_blocks χC σ ζσ
  ∧ is_private_blocks χC ζnewimm
  ∧ ζMLold ##ₘ (ζσ ∪ ζnewimm)
  ∧ is_store χC (ζMLold ∪ ζσ ∪ ζnewimm) σ.
Proof.
  revert ζMLold χMLold.
  induction σ as [|ℓ [vv|] σ Hin IH] using map_ind; intros ζMLold χMLold HχMLold Hsubset Hnone.
  - exists χMLold, ∅, ∅; split_and!.
    + done.
    + split; rewrite dom_empty_L. 1: done. split. 1: done.
      intros (ℓ & Vs & H1 & H2). exfalso. rewrite lookup_empty in H2. done.
    + intros γ; rewrite dom_empty_L; done.
    + apply map_disjoint_dom. rewrite ! dom_union_L dom_empty_L union_empty_r_L. apply disjoint_empty_r.
    + intros ℓ Vs γ blk Hc. exfalso. rewrite lookup_empty in Hc. done.
  - destruct (IH ζMLold χMLold) as (χ0 & ζσ & ζi0 & Hχ0 & (HζσL & HζσR) & Hζi0 & Hd0 & Hstore). 1-2: done.
    1: { eapply map_Forall_impl. 1: apply Hnone.
         intros i k [[[? ?]|[Hne H]]%lookup_insert_Some|[H Hne]%lookup_insert_None]; try congruence.
         1: by left. by right. }
    destruct (allocate_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first apply Hχ0.
    destruct (deserialize_ML_block χ1 vv) as (χ2 & ζi2 & lvs & Hχ2 & Hζi2 & Hdom & Helt); first apply Hχ1.
    assert (γ ∉ dom ζMLold) as HγML.
    1: { intros Hc. assert (χMLold !! γ = Some (LlocPublic ℓ)).
         1: assert (γ ∈ dom χMLold) as [k Hk]%elem_of_dom by set_solver.
         1: enough (k = LlocPublic ℓ) by now subst.
         1: eapply lookup_weaken_inv; first done; last done.
         1: etransitivity; last eapply Hχ1; eapply Hχ0.
         assert (pub_locs_in_lstore χMLold ζMLold !! γ = Some ℓ) as Hpl.
         1: eapply pub_locs_in_lstore_lookup; done.
         pose proof (map_Forall_lookup_1 _ _ _ _ Hnone Hpl) as HHH. cbn in HHH.
         rewrite ! lookup_insert in HHH. destruct HHH; congruence. }
    assert (ζi0 ##ₘ ζi2) as Hdisji0i2.
    1: { apply map_disjoint_spec. intros ? ? ? H1%elem_of_dom_2 H2%elem_of_dom_2.
         edestruct @elem_of_disjoint as [HL HR]; eapply HL. 1: apply Hdom. 2: done.
         eapply elem_of_dom_2. eapply lookup_weaken. 2: apply Hχ1. by apply Hζi0. }
    exists χ2, (<[γ := lvs]> ζσ), (ζi0 ∪ ζi2). split_and!. 1-2: split.
    + etransitivity; first apply Hχ0. etransitivity; first apply Hχ1. apply Hχ2.
    + apply Hχ2.
    + intros ℓ' Hℓ'. rewrite dom_insert_L in Hℓ'. apply elem_of_union in Hℓ'. destruct Hℓ' as [->%elem_of_singleton|H].
      1: eexists; eapply lookup_weaken; first done; eapply Hχ2.
      destruct (HζσL ℓ' H) as (γ' & Hγ'). exists γ'. eapply lookup_weaken; first apply Hγ'.
      etransitivity; first apply Hχ1. eapply Hχ2.
    + intros γ'; destruct (HζσR γ') as [HL HR]; rewrite ! dom_insert_L; split. 
      2: intros (ℓ' & Vs & HH1 & [[? ?]|[Hne HH]]%lookup_insert_Some).
      1: intros [->%elem_of_singleton|H]%elem_of_union.
      * exists ℓ, vv. split. 1: eapply lookup_weaken; first done; eapply Hχ2.
        rewrite lookup_insert; done.
      * destruct (HL H) as (ℓ' & Vs & HH1 & HH2). exists ℓ', Vs; split.
        1: eapply lookup_weaken; first eapply HH1. etransitivity; first apply Hχ1. apply Hχ2.
        rewrite lookup_insert_ne; try done. intros ->; rewrite Hin in HH2; congruence.
      * subst. injection H0; intros ->. eapply elem_of_union; left. eapply elem_of_singleton.
        destruct Hχ2 as [HHL HHR]; eapply HHR. 1: done. 1: eapply lookup_weaken; first done. apply HHL.
      * eapply elem_of_union. right.
        destruct (HζσL ℓ') as (γ2 & HH2); first by eapply elem_of_dom_2.
        apply HR. exists ℓ', Vs. split_and!. 2: done.
        enough (γ' = γ2) as -> by done.
        destruct Hχ2 as [HHL HHR]; eapply HHR; try done. eapply lookup_weaken; first done.
        etransitivity; first eapply Hχ1. eapply HHL.
    + intros γ' H. rewrite dom_union_L in H. apply elem_of_union in H. destruct H as [H|H].
      * destruct Hχ2 as [HHL _]; eapply lookup_weaken. 1: by apply Hζi0.
        etransitivity; first eapply Hχ1. eapply HHL.
      * destruct Hχ2 as [HHL _]; by apply Hζi2.
    + apply map_disjoint_dom. rewrite ! dom_union_L. rewrite dom_insert_L.
      rewrite <- union_assoc_L.
      apply disjoint_union_r. split.
      1: eapply elem_of_disjoint; intros ? Hζ ->%elem_of_singleton; apply HγML; done. 
      rewrite union_assoc_L. apply disjoint_union_r; split.
      1: apply map_disjoint_dom in Hd0; rewrite dom_union_L in Hd0; done.
      eapply elem_of_disjoint. intros x H1 H2. edestruct @elem_of_disjoint as [HL]; eapply HL. 1: apply Hdom. 2: done.
      eapply elem_of_weaken. 1: apply H1.
      etransitivity; last apply subseteq_dom, Hχ1.
      etransitivity; last apply subseteq_dom, Hχ0.
      eapply Hsubset.
    + intros ℓ' vs γ' blk H1 H2 H3.
      apply lookup_insert_Some in H1. destruct H1 as [[? ?]|[Hne H1]].
      * subst ℓ'. injection H0; intros ->.
        assert (γ' = γ) as ->.
        1: destruct Hχ2 as [HHL HHR]; eapply HHR; first done; eapply lookup_weaken; last apply HHL; done.
        rewrite lookup_union_l in H3.
        2: { eapply not_elem_of_dom. rewrite dom_union_L. intros [H|H]%elem_of_union.
             1: apply Hζi0 in H. 2: apply Hζi2 in H; congruence.
             eapply lookup_weaken in H. 1: erewrite H2 in H; congruence.
             etransitivity. 1: apply Hχ1. apply Hχ2. }
        rewrite lookup_union_r in H3.
        2: { eapply not_elem_of_dom. done. }
        rewrite lookup_insert in H3. injection H3; intros ->.
        inversion Helt; subst. econstructor.
        eapply Forall2_impl. 1: apply H.
        intros x y Hc. eapply is_val_mono. 3: apply Hc. 1: done.
        rewrite ! map_union_assoc.
        apply map_union_subseteq_r.
        eapply map_disjoint_dom. eapply elem_of_disjoint.
        intros γ'. rewrite ! dom_union_L. rewrite dom_insert_L.
        intros [[H1|[H1|H1]%elem_of_union]%elem_of_union|H1]%elem_of_union Ho.
        all: edestruct @elem_of_disjoint as [HL HR]; last eapply HL; first apply Hdom; last done.
        -- eapply elem_of_weaken. 2: etransitivity; first apply Hsubset. 2: eapply subseteq_dom. 2: etransitivity; last eapply Hχ1. 2: etransitivity; last eapply Hχ0.
           2: reflexivity. done.
        -- apply elem_of_singleton in H1; subst; eapply elem_of_dom_2; done.
        -- eapply elem_of_weaken. 2: eapply subseteq_dom; eapply Hχ1. apply HζσR in H1. destruct H1 as (l & _ & HH & _).
           eapply elem_of_dom_2. done.
        -- eapply elem_of_dom_2. eapply lookup_weaken. 1: by eapply Hζi0. eapply Hχ1.
      * assert (χ0 !! γ' = χ2 !! γ') as Hass.
        1: { apply elem_of_dom_2 in H1. apply HζσL in H1.
             destruct H1 as (γA & HγA). rewrite H2. rewrite <- HγA. f_equal. destruct Hχ2 as [HHHL HHH]; eapply HHH. 1: done.
             eapply lookup_weaken; first done. etransitivity; first eapply Hχ1; apply HHHL. }
        rewrite <- Hass in H2.
        assert ((ζMLold ∪ ζσ ∪ ζi0) !! γ' = Some blk) as H3'.
        1: { assert (γ' ∈ dom ζσ) as HH1. 
             1: eapply HζσR; exists ℓ', vs; repeat split; done.
             apply elem_of_dom in HH1. destruct HH1 as [bb Hbb].
             assert (ζi0 !! γ' = None) as HH3.
             1: { eapply not_elem_of_dom. intros H. pose proof (Hζi0 _ H) as HH2. rewrite HH2 in H2; congruence. }
             assert (ζMLold !! γ' = None) as HH.
             1: { eapply map_disjoint_Some_r. 1: done. rewrite lookup_union_l. all: done. }
             rewrite lookup_union_l. 2: done.
             rewrite lookup_union_r. 2: done.
             apply lookup_union_Some_inv_l in H3.
             2: apply lookup_union_None; split; try done.
             2: eapply not_elem_of_dom; intros H; pose proof (Hζi2 _ H) as HH2; rewrite <- Hass in HH2;  rewrite HH2 in H2; congruence.
             apply lookup_union_Some_inv_r in H3. 2: done.
             apply lookup_insert_Some in H3. destruct H3 as [[? ?]|[? ?]]; last done.
             subst γ'. eapply lookup_weaken in H2. 2: apply Hχ1. rewrite H2 in Hγ. congruence. }
        specialize (Hstore ℓ' vs γ' blk H1 H2 H3') as Hstore1.
        inversion Hstore1; subst. econstructor.
        eapply Forall2_impl; first done. intros x y He; eapply is_val_mono.
        3:done. 1: etransitivity; first eapply Hχ1; eapply Hχ2.
        rewrite <- ! map_union_assoc.
        eapply map_union_mono_l. etransitivity.
        1: eapply map_union_mono_l. 2: eapply map_union_mono_r.
        1: apply map_union_subseteq_l.
        1: { apply map_disjoint_spec. intros γ3 b1 b2.
             intros [[Heq1 Heq2]|[Hne1 HH1]]%lookup_insert_Some;
             intros [HH2|HH2]%lookup_union_Some. 3,6:done.
             - subst γ3. eapply elem_of_dom_2 in HH2. apply Hζi0 in HH2. eapply lookup_weaken in HH2. 1: erewrite HH2 in Hγ; done. eapply Hχ1.
             - subst γ3. eapply elem_of_dom_2 in HH2. apply Hζi2 in HH2. eapply lookup_weaken_inv in HH2. 2: eapply Hγ. 2: eapply Hχ2. congruence.
             - eapply elem_of_dom_2 in HH2. apply Hζi0 in HH2. eapply elem_of_dom_2 in HH1. eapply HζσR in HH1. destruct HH1 as (?&?&H0&?). rewrite HH2 in H0; congruence.
             - eapply elem_of_dom_2 in HH2. apply Hζi2 in HH2. eapply elem_of_dom_2 in HH1. eapply HζσR in HH1. destruct HH1 as (?&?&H0&?).
               eapply lookup_weaken in H0. 2: etransitivity; first apply Hχ1; apply Hχ2. rewrite HH2 in H0; congruence. }
        eapply insert_subseteq. eapply not_elem_of_dom. intros Hcc. apply HζσR in Hcc.
        destruct Hcc as (ll&bb&HH1&HH2). eapply lookup_weaken in HH1. 2: apply Hχ1. rewrite Hγ in HH1.
        injection HH1; intros ->. rewrite HH2 in Hin; congruence.
  - destruct (IH ζMLold χMLold) as (χ0 & ζσ & ζi0 & Hχ0 & (HζσL & HζσR) & Hζi0 & Hd0 & Hstore). 1-2: done.
    1: { eapply map_Forall_impl. 1: apply Hnone.
         intros i k [[[? ?]|[Hne H]]%lookup_insert_Some|[H Hne]%lookup_insert_None]; try congruence.
         1: right; subst; done. 1: by left. by right. }
    destruct (allocate_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first apply Hχ0.
    exists χ1, ζσ, ζi0. split_and!. 1-2: split.
    + etransitivity; first apply Hχ0. apply Hχ1.
    + apply Hχ1.
    + intros ℓ' Hℓ'. rewrite dom_insert_L in Hℓ'. apply elem_of_union in Hℓ'. destruct Hℓ' as [->%elem_of_singleton|H].
      1: eexists; done.
      destruct (HζσL ℓ' H) as (γ' & Hγ'). exists γ'. eapply lookup_weaken; first apply Hγ'.
      apply Hχ1.
    + intros γ'; destruct (HζσR γ') as [HL HR]; split.
      * intros H. destruct (HL H) as (ℓ' & Vs & HH1 & HH2). exists ℓ', Vs; split.
        1: eapply lookup_weaken; first eapply HH1; apply Hχ1.
        rewrite lookup_insert_ne; try done. intros ->; rewrite Hin in HH2; congruence.
      * intros (ℓ' & Vs & HH1 & HH2). eapply HR. exists ℓ', Vs.
        apply lookup_insert_Some in HH2. destruct HH2 as [[? Hc]|[Hne HH]]; first congruence.
        split; last done.
        destruct (HζσL ℓ') as (γ2 & HH2); first by eapply elem_of_dom_2.
        enough (γ' = γ2) as -> by done.
        destruct Hχ1 as [HHL HHR]; eapply HHR; try done. by eapply lookup_weaken.
    + intros γ' H. destruct Hχ1 as [HHL _]; eapply lookup_weaken. 2: apply HHL. by apply Hζi0.
    + done.
    + intros ℓ' vs γ' blk H1 H2 H3.
      apply lookup_insert_Some in H1. destruct H1 as [[? Hc]|[Hne H1]]; first congruence.
      assert (χ0 !! γ' = χ1 !! γ') as Hass. 1: eapply Hold; last done. intros ->; exfalso; destruct Hχ1 as [_ HHR]; congruence.
      rewrite <- Hass in H2.
      specialize (Hstore ℓ' vs γ' blk H1 H2 H3) as Hstore1.
      inversion Hstore1; subst. econstructor.
      eapply Forall2_impl; first done. intros x y He; eapply is_val_mono. 1: apply Hχ1. done. done.
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

  iAssert (⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) (pub_locs_in_lstore (χML ρml) (ζML ρml))⌝)%I with "[HσML HAχNone]" as "%Hpublocs".
  1: { generalize (pub_locs_in_lstore (χML ρml) (ζML ρml)) as mm. intros mm. iStopProof.
       induction mm as [|k l mm Hin IH] using map_ind; iIntros "(HH & HK)".
       - iPureIntro. apply map_Forall_empty.
       - iPoseProof (big_sepM_insert) as "[HL _]". 1: apply Hin.
         iPoseProof ("HL" with "HK") as "[H1 H2]".
         iPoseProof (IH with "[HH H2]") as "%HIH". 1: iFrame.
         iPoseProof (gen_heap_valid with "HH H1") as "%Hv".
         iPureIntro. apply map_Forall_insert. 1: done. split; done. }

  destruct (deserialize_ML_heap (ζML ρml) (χML ρml) σ) as (χ1 & ζσ & ζσimm & Hχ1 & Hζσ & Hζσimm & Hdisj1 & Hstore).
  1: done.
  1: eapply elem_of_subseteq; done.
  1: eapply map_Forall_impl; first exact Hpublocs; intros ? ? ? ; by left.
  destruct (deserialize_ML_values χ1 vv) as (χ2 & ζimm & lvs & Hχ2 & Hζimm & Hdisj2 & Hlvs).
  1: apply Hχ1.
  


  iSplitR.
  + iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn.
    eapply (RunFunctionS p F vv ρml σ ζσ (ζσimm ∪ ζimm) _ _ _ _ χ2 _ _ (fun _ => True)). 7-13: admit.
    1: {split; try apply Hχ2. etransitivity; last apply Hχ2; apply Hχ1. }
    1: { admit. }
    1: { admit. }
    1: { reflexivity. }
    1: { admit. }
    1: { admit. }

Admitted.

End Simulation.
